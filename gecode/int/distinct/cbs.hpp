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
      if (a.max() - a.min() + 1 == a.size())
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
                  SolnDistribution* dist) {
    assert(!x.assigned());
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
    int minVal = viewArray[0].min(); int maxVal = viewArray[0].max();
    for (int i=1; i<viewArray.size(); i++) {
      if (viewArray[i].min() < minVal) minVal = viewArray[i].min();
      if (viewArray[i].max() > maxVal) maxVal = viewArray[i].max();
    }

    ValToVar valToVar(viewArray,minVal,maxVal);
    SolCounts solcounts(minVal,maxVal);

    std::vector<Record> backup;
    backup.reserve((size_t)(maxVal-minVal+1));
    for (int i = 0; i < viewArray.size(); i++) {
      if (viewArray[i].assigned()) continue;

      if (i == 0 || !comp(viewArray[i], viewArray[i - 1], true)) {
        backup.resize(0);
        UB varUB = ub;
        upperBoundUpdate(varUB, i, viewArray[i].size(), 1);
        // Normalization constant for keeping densities values between 0 and 1
        double normalization = 0;
        // We calculate the density for every value assignment for the variable
        for (ViewValues<View> val(viewArray[i]); val(); ++val) {
          UB localUB = varUB;
          // Upper bound for every variable affected by the assignation
          int nbVarAffectedByVal = valToVar.getNbVarForVal(val.val());
          for (int j = 0; j < nbVarAffectedByVal; j++) {
            int affectedVar = valToVar.get(val.val(), j);
            if (affectedVar != i)
              upperBoundUpdate(localUB, i, viewArray[affectedVar].size(),
                               viewArray[affectedVar].size() - 1);
          }

          double lowerUB = std::min(localUB.minc, ::sqrt(localUB.liangBai));
          solcounts(val.val()) = lowerUB;
          normalization += lowerUB;
        }

        // Normalization
        for (ViewValues<View> val(viewArray[i]); val(); ++val) {
          Record r;
          r.val = viewArray[i].baseval(val.val());
          r.dens = solcounts(val.val()) / normalization;;
          dist->setMarginalDistribution(prop_id, viewArray[i].id(), r.val,
                                        r.dens);
          backup.push_back(r);
        }
      } else {
        for (int j=0; j<backup.size(); j++) {
          dist->setMarginalDistribution(prop_id,
                                        viewArray[i].id(),
                                        backup[j].val,
                                        backup[j].dens);
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
