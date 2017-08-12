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

namespace Gecode { namespace Int { namespace Distinct {

  /**
   * \brief Minc and Brégman factors
   *
   * Factors precomputed for every value in the domain of x. Thoses factors are
   * used to compute the Minc and Brégman upper bound for the permanent in
   * counting base search
   */
  class MincFactors {
  public:
    MincFactors();
    double get(int domSize);
  private:
    void precompute(void);
  private:
    // The maximum factor that can be calculated with a double is the 170th,
    // else we have an overflow
    static const int MAX_FACTOR = 170;
    double mincFactors[MAX_FACTOR];
    bool computed;
  };

  forceinline
  MincFactors::MincFactors() :
    computed(false) {}

  forceinline
  void MincFactors::precompute(void) {
    double fac = 1;
    mincFactors[0] = 1;
    for (int i=2; i<MAX_FACTOR+1; i++) {
      fac *= i;
      mincFactors[i-1] = ::pow(fac,1.0/i);
    }
    computed = true;
  }

  forceinline
  double MincFactors::get(int domSize) {
    // If the requested domSize is greater than MAX_FACTOR, we return INFINITY.
    // This way, the Liang&Bai bound will be used instead
    if (domSize >= MAX_FACTOR) return INFINITY;
    // We only compute the factors if we need it
    if (!computed) precompute();
    return mincFactors[domSize-1];
  }


  /**
   * \brief Liang and Bai factors
   *
   * Factors precomputed for every index and domain size in x. Thoses factors
   * are used to compute the Liang and Bai upper bound for the permanent in
   * counting base search
   */
  class LiangBaiFactors {
  public:
    LiangBaiFactors();
    double get(int index, int domSize);
  private:
    void precompute(int newNbVar, int newLargestDomSize);
  private:
    int nbVar;
    int largestDomSize;
    double **liangBaiFactors;
  };

  forceinline
  double LiangBaiFactors::get(int index, int domSize) {
    // We only compute the factors if we need it
    bool compute = false;
    int a = index+1>nbVar?compute=true,index+1:nbVar;
    int b = domSize>largestDomSize?compute=true,domSize:largestDomSize;
    // The minimum factor matrix we compute is 128x128
    if (compute) precompute(std::max(a,128),std::max(b,128));
    return liangBaiFactors[index][domSize-1];
  }

  forceinline
  void LiangBaiFactors::precompute(int newNbVar, int newLargestDomSize) {
    // If we need bigger factors, we reuse our latest precomputation
    liangBaiFactors = heap.realloc(liangBaiFactors,nbVar,newNbVar);
    for (int i=0; i<newNbVar; i++)
      liangBaiFactors[i] = heap.realloc(liangBaiFactors[i], largestDomSize,
                                        newLargestDomSize);

    for (int i = 1; i <= newNbVar; i++) {
      double b = std::ceil(i/2.0);
      int j;
      // if i<=nb_var, we already computed 1..largest_domain_size for j
      if ( i <= nbVar) j = largestDomSize+1; else j = 1;
      for (; j <= newLargestDomSize; j++) {
        double a = std::ceil((j+1)/2.0);
        double q = std::min(a,b);
        liangBaiFactors[i-1][j-1] = q*(j-q+1);
      }
    }

    nbVar = newNbVar;
    largestDomSize = newLargestDomSize;
  }

  forceinline
  LiangBaiFactors::LiangBaiFactors() :
    nbVar(0), largestDomSize(0) {
  }

  /**
   * \brief Shared factors used by all instances of cbs distinct branchers
   */
  extern MincFactors mincFactors;
  extern LiangBaiFactors liangBaiFactors;

  struct UB {
    double minc;
    double liangBai;
  };

  /**
   * \Brief Function for updating upper bounds given a domain change
   */
  forceinline
  void upperBoundUpdate(UB& ub, int index, int oldDomSize, int newDomSize) {
    ub.minc *= mincFactors.get(newDomSize) / mincFactors.get(oldDomSize);
    ub.liangBai *= liangBaiFactors.get(index,newDomSize) /
                   liangBaiFactors.get(index,oldDomSize);
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
    bool operator ()(const View& a, const View& b) {
      // This comparison makes it easier to debug and compare solutions
      if (a.size() == b.size())
        return a.varimp()->id() > b.varimp()->id();
      return a.size() > b.size();
    }
  };

  template<class View>
  int cbsdistinct(Space& home, const ViewArray<View>& x,
                  SolnDistribution* dist) {
    if (dist == NULL) {
      int d = 0;
      for (int i=0; i<x.size(); i++) if (!x[i].assigned()) d += x[i].size();
      return d;
    }

    assert(!x.assigned());
    Region r(home);
    ViewArray<View> viewArray(r,x);

    // We sort the variables by their domain size. Liang & Bai gives a tighter
    // bound this way
    QSComparator<View> descendingDomSize;
    Support::quicksort(&viewArray[0],viewArray.size(),descendingDomSize);

    // Minc and Brégman and Liang and Bai upper bound.
    UB ub; ub.minc=1; ub.liangBai=1;
    for (int i=0; i<viewArray.size(); i++) {
      ub.minc *= mincFactors.get(viewArray[i].size());
      ub.liangBai *= liangBaiFactors.get(i,viewArray[i].size());
    }

    dist->setSupportSize(std::min(ub.minc, ::sqrt(ub.liangBai)));

    // Span from the minimum to the maximum value of the union of all
    // variable domains
    int minVal = viewArray[0].min(); int maxVal = viewArray[0].max();
    for (int i=1; i<viewArray.size(); i++) {
      if (viewArray[i].min() < minVal) minVal = viewArray[i].min();
      if (viewArray[i].max() > maxVal) maxVal = viewArray[i].max();
    }

    ValToVar valToVar(viewArray,minVal,maxVal);
    SolCounts solcounts(minVal,maxVal);

    for (int i = 0; i < viewArray.size(); i++) {
      if (viewArray[i].assigned()) continue;

      UB varUB = ub;
      upperBoundUpdate(varUB,i,viewArray[i].size(), 1);
      // Normalization constant for keeping densities values between 0 and 1
      double normalization = 0;
      // We calculate the density for every value assignment for the variable
      for (ViewValues<View> val(viewArray[i]); val(); ++val) {
        UB localUB = varUB;
        // Upper bound for every variable affected by the assignation
        int nbVarAffectedByVal = valToVar.getNbVarForVal(val.val());
        for (int j=0; j<nbVarAffectedByVal; j++) {
          int affectedVar = valToVar.get(val.val(), j);
          if (affectedVar != i)
            upperBoundUpdate(localUB,i,viewArray[affectedVar].size(),
                             viewArray[affectedVar].size()-1);
        }

        double lowerUB = std::min(localUB.minc,::sqrt(localUB.liangBai));
        solcounts(val.val()) = lowerUB;
        normalization += lowerUB;
      }

      // Normalization
      for (ViewValues<View> val(viewArray[i]); val(); ++val) {
        double d = solcounts(val.val()) / normalization;
        dist->setMarginalDistribution(
          viewArray[i].id(),viewArray[i].baseval(val.val()),d);
      }
    }

    return 0;
  }

}}}
