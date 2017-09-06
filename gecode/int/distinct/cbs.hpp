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
    assert(index < WIDTH_LIANG_BAI_FACTOR);
    assert(domSize-1 < WIDTH_LIANG_BAI_FACTOR);
    return liangBaiFactors[index*WIDTH_LIANG_BAI_FACTOR + domSize-1];
  }


  struct UB {
    double minc;
    double liangBai;
  };

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
//  class ValToVar {
//  public:
//    template<class View>
//    ValToVar(const ViewArray<View>& x, int minDomVal, int maxDomVal);
//    ~ValToVar();
//
//    int getNbVarForVal(int val) const;
//    int get(int val, int ith_var) const;
//
//  private:
//    int nbVal() const;
//  private:
//    int *nbVarForVal; // Number of variable for each value
//    int *valVar; // Value to variables
//
//    int minVal;
//    int maxVal;
//    int nb_var;
//  };
//
//  template<class View>
//  ValToVar::ValToVar(const ViewArray<View>& x, int minDomVal, int maxDomVal)
//    : minVal(minDomVal), maxVal(maxDomVal), nb_var(x.size()) {
//
//    nbVarForVal = heap.alloc<int>(nbVal());;
//    for (int i=0; i<nbVal(); i++) nbVarForVal[i] = 0;
//
//    valVar = heap.alloc<int>(nbVal() * nb_var);
//
//    for (int var=0; var<x.size(); var++) {
//      for (ViewValues<View> val(x[var]); val(); ++val) {
//        // Current value
//        int v = val.val();
//        // Number of variables for current value
//        int *nbVar = &nbVarForVal[v-minVal];
//
//        int row=(v-minVal); int width=nb_var; int col=*nbVar;
//        valVar[row*width + col] = var;
//
//        (*nbVar)++;
//      }
//    }
//  }
//
//  forceinline
//  ValToVar::~ValToVar() {
//    heap.free<int>(nbVarForVal, nbVal());
//    heap.free<int>(valVar, nb_var*nbVal());
//  }
//
//  forceinline
//  int ValToVar::getNbVarForVal(int val) const {
//    return nbVarForVal[val-minVal];
//  }
//
//  forceinline
//  int ValToVar::get(int val, int ith_var) const {
//    assert(ith_var < getNbVarForVal(val));
//    assert(val - minVal >= 0 && val - minVal <= maxVal);
//    int row=(val-minVal); int width=nb_var; int col=ith_var;
//    return valVar[row*width + col];
//  }
//
//  forceinline
//  int ValToVar::nbVal() const {
//    return maxVal - minVal + 1;
//  }

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
    void getBestPosValDens(int& pos, int& val, double& dens) const {
      pos = -1;
      dens = 0;
      for (int v=best.getMin(); v<=best.getMax(); v++) {
        if (best[v].pos != -1) {
          double mU = getMincUpdate(v, best[v].domsize);
          double lU = ::sqrt(
            getLiangUpdate(v, (unsigned int)best[v].pos, best[v].domsize));
          double _dens = std::min(mU,lU);
          if (_dens > dens) {
            pos = best[v].pos;
            val = v;
            dens = _dens;
          }
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
  void cbsdistinct(Space& home, unsigned int prop_id, const ViewArray<View>& x,
                  SolnDistribution* dist, SolnDistribution::Type type) {
    if (type == SolnDistribution::MAX_PER_PROP) {
      int minVal = x[0].min();
      int maxVal = x[0].max();
      for (int i = 1; i < x.size(); i++) {
        if (x[i].assigned()) continue;
        minVal = std::min(x[i].min(), minVal);
        maxVal = std::max(x[i].max(), maxVal);
      }

      ValToUpdate valToUpdate(x, minVal, maxVal);
      int pos;
      int val;
      double dens;
      valToUpdate.getBestPosValDens(pos, val, dens);
      assert(pos != -1 && dens != 0);
      dist->setMarginalDistribution(prop_id, x[pos].id(), val, dens);
    } else if (type == SolnDistribution::ALL) {
      assert(!x.assigned());
      {
        bool compute = false;
        for (int i=0; i<x.size(); i++) {
          if (!x[i].assigned() && dist->compute(x[i].id())) {
            compute = true;
            break;
          }
        }
        if (!compute) return;
      }

      Region r(home);
      ViewArray<View> viewArray(r,x);

      // We sort the variables by their domain size. Liang & Bai gives a tighter
      // bound this way
      QSComparator<View> comp;
      Support::quicksort(&viewArray[0],viewArray.size(),comp);

      // Minc and Brégman and Liang and Bai upper bound.
      UB ub; ub.minc=1; ub.liangBai=1;
      for (int i=0; i<viewArray.size(); i++) {
        ub.minc *= getMincfactor(viewArray[i].size());
        ub.liangBai *= getLiangBaiFactor(i,viewArray[i].size());
      }

      dist->setSupportSize(prop_id, std::min(ub.minc, ::sqrt(ub.liangBai)));

      // Span from the minimum to the maximum value of the union of all
      // variable domains
      int minVal = viewArray[0].min();
      int maxVal = viewArray[0].max();
      for (int i=1; i<viewArray.size(); i++) {
        if (viewArray[i].assigned()) continue;
        minVal = std::min(viewArray[i].min(), minVal);
        maxVal = std::max(viewArray[i].max(), maxVal);
      }

  //    ValToVar valToVar(viewArray,minVal,maxVal);
      ValToUpdate valToUpdate(viewArray, minVal, maxVal);
      SolCounts solcounts(minVal,maxVal);

      std::vector<Record> backup;
      backup.reserve((size_t)(maxVal-minVal+1));
      for (int i = 0; i < viewArray.size(); i++) {
        if (viewArray[i].assigned()) continue;
        if (!dist->compute(viewArray[i].id())) continue;

        if (i == 0 || !comp(viewArray[i], viewArray[i - 1], true)) {
          backup.resize(0);
          // Normalization constant for keeping densities values between 0 and 1
          double normalization = 0;
          // We calculate the density for every value assignment for the variable
          for (ViewValues<View> val(viewArray[i]); val(); ++val) {
            UB localUB = ub;
            int v = val.val(); unsigned int s = viewArray[i].size();
            localUB.minc *= valToUpdate.getMincUpdate(v,s);
            localUB.liangBai *= valToUpdate.getLiangUpdate(v,i,s);
            double lowerUB = std::min(localUB.minc, ::sqrt(localUB.liangBai));
            solcounts(val.val()) = lowerUB;
            normalization += lowerUB;
          }

          // Normalization
          for (ViewValues<View> val(viewArray[i]); val(); ++val) {
            Record r;
            r.val = viewArray[i].baseval(val.val());
            r.dens = solcounts(val.val()) / normalization;
            double inf = std::numeric_limits<double>::infinity();
            if (r.dens == -inf || r.dens == inf)
              throw Int::OutOfLimits("Int::Distinct::cbsdistinct");
            dist->setMarginalDistribution(prop_id, viewArray[i].id(), r.val,
                                          r.dens);
            backup.push_back(r);
          }
        } else {
          for (int j=0; j<(int)backup.size(); j++) {
            dist->setMarginalDistribution(prop_id,
                                          viewArray[i].id(),
                                          backup[j].val,
                                          backup[j].dens);
          }
        }
      }
    }

  }

  template<class View>
  void cbssize(const ViewArray<View>& x, SolnDistributionSize* s,
              unsigned int& domAggr, unsigned int& domAggrB) {
    domAggr = 0;
    domAggrB = 0;
    for (int i=0; i<x.size(); i++) {
      if (!x[i].assigned()) {
        domAggr += x[i].size();
        if (s->varInBrancher(x[i].id()))
          domAggrB += x[i].size();
      }
    }
  }

}}}
