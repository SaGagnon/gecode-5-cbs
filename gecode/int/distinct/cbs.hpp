/* -*- mode: C++; c-basic-offset: 2; indent-tabs-mode: nil -*- */
/*
 *  This file is part of Gecode, the generic constraint
 *  development environment:
 *     http://www.gecode.org
 *
 *  Permission is hereby granted, free of charge, to any person obtaining
 *  a copy of this software and associated documentation files (the
 *  "Software"), to deal in the Software without restriction, including
 *  without limitation the rights to use, copy, modify, merge, publish,
 *  distribute, sublicense, and/or sell copies of the Software, and to
 *  permit persons to whom the Software is furnished to do so, subject to
 *  the following conditions:
 *
 *  The above copyright notice and this permission notice shall be
 *  included in all copies or substantial portions of the Software.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 *  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 *  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 *  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 *  LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 *  OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 *  WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 */

#include <set>
#include <vector>
#include <limits>
#include <algorithm>


//#define VAL_TO_VAR
//#define BACKUP

namespace Gecode { namespace Int { namespace Distinct {

  /**
   * \brief Minc and Brégman factors
   *
   * Factors precomputed for every value in the domain of x. Thoses factors are
   * used to compute the Minc and Brégman upper bound for the permanent in
   * counting base search
   */

  // The maximum factor that can be calculated with a double is the 170th,
  // else we have an overflow
  const int MAX_MINC_FACTOR = 1000;
  extern const double mincFactors[MAX_MINC_FACTOR];

  static double getMincfactor(int domSize) {
    assert(domSize > 0);
    if (domSize-1 >= MAX_MINC_FACTOR)
      throw Int::OutOfLimits(
        "Int::Distinct::getMincfactor & Int::Distinct::getLiangBaiFactor");
    return mincFactors[domSize-1];
  }


  /**
   * \brief Liang and Bai factors
   *
   * Factors precomputed for every index and domain size in x. Thoses factors
   * are used to compute the Liang and Bai upper bound for the permanent in
   * counting base search
   */

  const int WIDTH_LIANG_BAI_FACTOR = 1000;
  extern const double liangBaiFactors[WIDTH_LIANG_BAI_FACTOR
                                      *WIDTH_LIANG_BAI_FACTOR];

  static double getLiangBaiFactor(int index, int domSize) {
    assert(index >= 0 && domSize > 0);
    assert(index < WIDTH_LIANG_BAI_FACTOR);
    assert(domSize-1 < WIDTH_LIANG_BAI_FACTOR);
    return liangBaiFactors[index*WIDTH_LIANG_BAI_FACTOR + domSize-1];
  }


  struct UB {
    double minc;
    double liangBai;
  };

#ifdef VAL_TO_VAR
  /**
   * \Brief Function for updating upper bounds given a domain change
   */
  forceinline
  void upperBoundUpdate(UB& ub, int index, int oldDomSize, int newDomSize) {
    ub.minc *= getMincfactor(newDomSize) / getMincfactor(oldDomSize);
    ub.liangBai *= getLiangBaiFactor(index,newDomSize) /
                   getLiangBaiFactor(index,oldDomSize);
  }

  /**
   * \brief Maps values to variables
   *
   * Used for a faster update of the upper bounds. When we assign a value, we
   * need to know each variable that is affected by the assignment.
   */
  class ValToVar {
  public:
    template<class View>
    ValToVar(const ViewArray<View>& x, int minDomVal, int maxDomVal);
    ~ValToVar();

    int getNbVarForVal(int val) const;
    int get(int val, int ith_var) const;

  private:
    int nbVal() const;
  private:
    int *nbVarForVal; // Number of variable for each value
    int *valVar; // Value to variables

    int minVal;
    int maxVal;
    int nb_var;
  };

  template<class View>
  ValToVar::ValToVar(const ViewArray<View>& x, int minDomVal, int maxDomVal)
    : minVal(minDomVal), maxVal(maxDomVal), nb_var(x.size()) {

    nbVarForVal = heap.alloc<int>(nbVal());;
    for (int i=0; i<nbVal(); i++) nbVarForVal[i] = 0;

    valVar = heap.alloc<int>(nbVal() * nb_var);

    for (int var=0; var<x.size(); var++) {
      if (x[var].assigned()) continue;
      for (ViewValues<View> val(x[var]); val(); ++val) {
        // Current value
        int v = val.val();
        // Number of variables for current value
        int *nbVar = &nbVarForVal[v-minVal];

        int row=(v-minVal); int width=nb_var; int col=*nbVar;
        valVar[row*width + col] = var;

        (*nbVar)++;
      }
    }
  }

  forceinline
  ValToVar::~ValToVar() {
    heap.free<int>(nbVarForVal, nbVal());
    heap.free<int>(valVar, nb_var*nbVal());
  }

  forceinline
  int ValToVar::getNbVarForVal(int val) const {
    return nbVarForVal[val-minVal];
  }

  forceinline
  int ValToVar::get(int val, int ith_var) const {
    assert(ith_var < getNbVarForVal(val));
    assert(val - minVal >= 0 && val - minVal <= maxVal);
    int row=(val-minVal); int width=nb_var; int col=ith_var;
    return valVar[row*width + col];
  }

  forceinline
  int ValToVar::nbVal() const {
    return maxVal - minVal + 1;
  }
#endif

  class ValToUpdate {
  private:
    template<typename T>
    class Arr {
    private:
      int minVal;
      int maxVal;
      T *x;
    public:
      Arr(int minDomVal, int maxDomVal)
        : minVal(minDomVal), maxVal(maxDomVal) {
        x = heap.alloc<T>(size());
      }
      ~Arr() { heap.free(x, size()); }
      T& operator[](int val) {
        assert(val >= minVal && val <= maxVal);
        return x[val-minVal];
      }
      T operator[](int val) const {
        return const_cast<Arr*>(this)->operator[](val);
      }
      unsigned int size() const { return (unsigned int)(maxVal-minVal+1); }
      int getMin() const { return minVal; }
      int getMax() const { return maxVal; }
    };

    Arr<double> mincUpdate;
    Arr<double> liangUpdate;
    // TODO: changer ce nom... et explication...
    struct BestVarForVal { int pos; unsigned int domsize; };
    Arr<BestVarForVal> best;
  public:
    template<class View>
    ValToUpdate(const ViewArray<View>& x, int minDomVal, int maxDomVal)
      : mincUpdate(minDomVal, maxDomVal), liangUpdate(minDomVal, maxDomVal),
        best(minDomVal, maxDomVal) {
      assert(mincUpdate.size() == liangUpdate.size()
             && mincUpdate.size() == best.size());
      for (int val=best.getMin(); val<=best.getMax(); val++) {
        mincUpdate[val] = 1;
        liangUpdate[val] = 1;
        BestVarForVal b;
        b.pos = -1;
        b.domsize = std::numeric_limits<unsigned int>::max();
        best[val] = b;
      }
      for (int i=0; i<x.size(); i++) {
        if (x[i].assigned()) continue;
        unsigned int s = x[i].size();
        for (ViewValues<View> val(x[i]); val(); ++val) {
          int v = val.val();
          mincUpdate[v] *= getMincfactor(s-1) / getMincfactor(s);
          liangUpdate[v] *= getLiangBaiFactor(i, s-1) / getLiangBaiFactor(i, s);
          if (s < best[v].domsize) {
            BestVarForVal b;
            b.pos = (unsigned int)i;
            b.domsize = s;
            best[v] = b;
          }
        }
      }
    }

    double getMincUpdate(int val, unsigned int varSize) const {
      return mincUpdate[val] / getMincfactor(varSize-1);
    }
    double getLiangUpdate(int val, unsigned int idx,
                          unsigned int varSize) const {
      return liangUpdate[val] / getLiangBaiFactor(idx, varSize-1);
    }
    // TODO: Renaming et commentaire
    template<class View>
    void TransmitBestPosValDens(Propagator::SendMarginal send,
                                unsigned int prop_id,
                                const ViewArray<View>& x ) const {
      for (int v=best.getMin(); v<=best.getMax(); v++) {
        if (best[v].pos != -1) {
          double mU = getMincUpdate(v, best[v].domsize);
          double lU = ::sqrt(
            getLiangUpdate(v, (unsigned int)best[v].pos, best[v].domsize));
          double _dens = std::min(mU,lU);
          send(prop_id, x[best[v].pos].id(), v, _dens);
        }
      }
    }
  };


  /**
   * \Brief Structure used for storing counts prior to normalization
   */
  class SolCounts {
  public:
    SolCounts(int domSize, int minDomVal);
    double& operator ()(int val);
  private:
    int minVal;
    int maxVal;
    std::vector<double> solcounts;
  };

  forceinline
  SolCounts::SolCounts(int minDomVal, int maxDomVal)
    : minVal(minDomVal), maxVal(maxDomVal),
      solcounts((unsigned long)(maxDomVal-minDomVal+1)) {}

  forceinline
  double& SolCounts::operator()(int val) {
    assert(minVal <= val && val <= maxVal);
    return solcounts[val-minVal];
  }

  template<class View>
  class QSComparator {
  public:
    bool operator ()(const View& a, const View& b, bool eq=false) {
      // This comparison makes it easier to debug and compare solutions
      if (a.size() != b.size()) return eq ? false : a.size() > b.size();
      if (a.min() != b.min()) return eq ? false : a.min() > b.min();
      if (a.max() != b.max()) return eq ? false : a.max() > b.max();

      // If there's no hole and all the above conditions are true, a and b
      // have the same domain
      if (a.max() - a.min() + 1 == (int)a.size())
        return eq ? true : a.varimp()->id() > b.varimp()->id();

      ViewRanges<View> aR(a), bR(b);

      while (aR() && bR() && aR.min() == bR.min() && aR.max() == bR.max())
        ++aR, ++bR;

      if (!aR() && !bR())
        return eq ? true : a.varimp()->id() > b.varimp()->id();
      else {
        if (eq) return false;
        if (aR.min() != bR.min()) return aR.min() > bR.min();
        return aR.max() > bR.max();
      }
    }
  };

  struct Record { int val; double dens; };

  template<class View>
  bool computation_to_do(const ViewArray<View>& x) {
    auto it = std::find_if(x.begin(), x.end(),
                           [&](const View& v) {
                             return !v.assigned();
                           });
    return it != x.end();
  }

  template<class View>
  void min_max_dom(const ViewArray<View>& x, int& min, int& max) {
    min = std::numeric_limits<int>::max();
    max = std::numeric_limits<int>::min();
    for (const auto& v : x) {
      if (v.assigned()) continue;
      min = std::min(v.min(), min);
      max = std::max(v.max(), max);
    }
  }

  forceinline
  void throw_if_inf(double n) {
    double inf = std::numeric_limits<double>::infinity();
    if (n == -inf || n == inf)
      throw Int::OutOfLimits("Int::Distinct::cbsdistinct");
  }

  template<class View>
  void cbsdistinct(Space& home, unsigned int prop_id, const ViewArray<View>& x,
                   Propagator::SendMarginal send,
                   Propagator::SolnDistribCalc sdc) {
    if(!computation_to_do(x))
      return;

    int minVal, maxVal;
    min_max_dom(x, minVal, maxVal);

    if (sdc == Propagator::MAX_PER_PROP) {
      ValToUpdate valToUpdate(x, minVal, maxVal);
      valToUpdate.TransmitBestPosValDens(send, prop_id, x);
    } else if (sdc == Propagator::ALL) {
      assert(!x.assigned());

      Region r(home);
      ViewArray<View> viewArray(r,x);

      // We sort the variables by their domain size. Liang & Bai gives a tighter
      // bound this way
      QSComparator<View> comp;
      Support::quicksort(&viewArray[0],viewArray.size(),comp);

      // Minc and Brégman and Liang and Bai upper bound.
      UB ub{1,1};
      for (int i=0; i<viewArray.size(); i++) {
        ub.minc *= getMincfactor(viewArray[i].size());
        ub.liangBai *= getLiangBaiFactor(i,viewArray[i].size());
      }

//      dist->supportsize(prop_id, std::min(ub.minc, ::sqrt(ub.liangBai)));

#ifdef VAL_TO_VAR
      ValToVar valToVar(viewArray,minVal,maxVal);
#else
      ValToUpdate valToUpdate(viewArray, minVal, maxVal);
#endif
      SolCounts solcounts(minVal,maxVal);

#ifdef BACKUP
      std::vector<Record> backup;
      backup.reserve(maxVal-minVal+1);
#endif
      for (int i = 0; i < viewArray.size(); i++) {
        if (viewArray[i].assigned()) continue;
//        if (!dist->compute(viewArray[i].id())) continue;

#ifdef VAL_TO_VAR
        UB varUB = ub;
        upperBoundUpdate(varUB,i,viewArray[i].size(), 1);
#endif

#ifdef BACKUP
        auto cant_use_backup = [&]() {
          return i == 0 || !comp(viewArray[i], viewArray[i - 1], true);
        };

        if (cant_use_backup()) {
          backup.resize(0);
#endif
          // Normalization constant for keeping densities values between 0 and 1
          double normalization = 0;
          // We calculate the density for every value assignment for the variable
          for (ViewValues<View> val(viewArray[i]); val(); ++val) {
#ifdef VAL_TO_VAR
            UB localUB = varUB;
            int nbVarAffectedByVal = valToVar.getNbVarForVal(val.val());
            for (int j=0; j<nbVarAffectedByVal; j++) {
              int affectedVar = valToVar.get(val.val(), j);
              if (affectedVar != i)
                upperBoundUpdate(localUB,affectedVar,viewArray[affectedVar].size(),
                                 viewArray[affectedVar].size()-1);
            }
#else
            UB localUB = ub;
            int v = val.val(); unsigned int s = viewArray[i].size();
            localUB.minc *= valToUpdate.getMincUpdate(v,s);
            localUB.liangBai *= valToUpdate.getLiangUpdate(v,i,s);
#endif
            double lowerUB = std::min(localUB.minc, ::sqrt(localUB.liangBai));
            solcounts(val.val()) = lowerUB;
            normalization += lowerUB;
          }

          // Normalization
          for (ViewValues<View> val(viewArray[i]); val(); ++val) {
            assert(normalization != 0);
            Record rec{
              viewArray[i].baseval(val.val()),
              solcounts(val.val()) / normalization
            };
            throw_if_inf(rec.dens);
            send(prop_id, viewArray[i].id(), rec.val,
                                          rec.dens);
#ifdef BACKUP
            backup.push_back(rec);
#endif
          }
#ifdef BACKUP
        } else {
          for (auto v : backup) {
            dist->marginaldistrib(prop_id, viewArray[i].id(), v.val,
                                          v.dens);
          }
        }
#endif
      }
    }

  }

  template<class View>
  void cbssize(const ViewArray<View>& x, Propagator::InDecision in,
               unsigned int& size, unsigned int& size_b) {
    size = 0;
    size_b = 0;
    for (const auto& v : x) {
      if (!v.assigned()) {
        size += v.size();
        if (in(v.id()))
          size_b += v.size();
      }
    }
  }

  template<class View>
  void cbsmindom(const ViewArray<View>& x, Propagator::InDecision in,
                 unsigned int& min) {
    min = 0;
    for (const auto& v : x) {
      if (!v.assigned() && in(v.id())) {
        if (v.size() < min || min == 0) {
          min = v.size();
        }
      }
    }
  }

}}}
