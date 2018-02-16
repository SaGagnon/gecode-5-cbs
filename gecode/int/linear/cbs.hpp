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


namespace Gecode { namespace Int { namespace Linear {

  class NoView;

  template<class P, class N>
  forceinline void
  nonAssignedSize(Propagator::InDecision in,
                  const ViewArray<P>& x, const ViewArray<N>& y,
                  unsigned int& size, unsigned int& size_b) {
    size = 0;
    size_b = 0;
    for (int i=0; i<x.size(); i++) {
      if (!x[i].assigned()) {
        size += x[i].size();
        if (in(x[i].id()))
          size_b += x[i].size();
      }
    }
    for (int i=0; i<y.size(); i++) {
      if (!y[i].assigned()) {
        size += y[i].size();
        if (in(y[i].id()))
          size_b += y[i].size();
      }
    }
  }

  template<class P, class N>
  forceinline void
  cbsmindom(Propagator::InDecision in,
                  const ViewArray<P>& x, const ViewArray<N>& y,
                  unsigned int& min) {
    min = 0;
    for (int i=0; i<x.size(); i++) {
      if (!x[i].assigned() && in(x[i].id())) {
        if (x[i].size() < min || min == 0) {
          min = x[i].size();
        }
      }
    }
    for (int i=0; i<y.size(); i++) {
      if (!y[i].assigned() && in(y[i].id())) {
        if (y[i].size() < min || min == 0) {
          min = y[i].size();
        }
      }
    }
  };

template<class View>
  forceinline double
  boundsMean(const View& x) {
    return (x.min() + x.max())/2;
  }

  template<>
  forceinline double
  boundsMean(const NoView&) {
    return 0;
  }

  template<class View>
  forceinline double
  domainMean(const View& x) {
    double mean = 0;
    for (ViewValues<View> val(x); val(); ++val)
      mean += val.val();
    return mean / x.size();
  }

  template<>
  forceinline double
  domainMean(const NoView&) {
    return 0;
  }

  template<class View>
  forceinline double
  domainVariance(const View& x, double mean) {
    double variance = 0;
    for (ViewValues<View> val(x); val(); ++val)
      variance += std::pow(val.val()-mean, 2);
    return variance / x.size();
  }

  template<>
  forceinline double
  domainVariance(const NoView&, double) {
    return 0;
  }

  template<class P, class N>
  void
  MV_dist(int lb, int ub, const ViewArray<P>& x, const ViewArray<N>& y,
          double& mean, double &variance) {
    mean = (lb+ub)/2;
    variance = (std::pow(ub-lb+1,2)-1)/12;

    for (int i=0; i<x.size(); i++) {
      if (x[i].assigned()) {
        mean -= x[i].val();
      } else {
        double _mean = domainMean(x[i]);
        mean -= _mean;
        variance += domainVariance(x[i], _mean);
      }
    }

    for (int i=0; i<y.size(); i++) {
      if (y[i].assigned()) {
        mean += y[i].val();
      } else {
        double _mean = domainMean(y[i]);
        mean += _mean;
        variance += domainVariance(y[i], _mean);
      }
    }
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
  forceinline void
  approx_dens_for_array(Space& home, unsigned int prop_id,
                        const ViewArray<View>& a, bool P,
                        Propagator::SendMarginal send,
                        double mean, double variance) {
    // For every variable in the domain of ViewArray viewArray
    Region r(home);
    ViewArray<View> viewArray(r,a);

    QSComparator<View> comp;
    Support::quicksort(&viewArray[0],viewArray.size(),comp);

    std::vector<Record> backup;
    {
      unsigned int maxDomSize = 0;
      for (int i = 0; i < viewArray.size(); i++)
        if (viewArray[i].size() > maxDomSize)
          maxDomSize = viewArray[i].size();
      backup.reserve(maxDomSize);
    }

//    unsigned int _reuse_count = 0;
    for (int i = 0; i < viewArray.size(); i++) {
      if (viewArray[i].assigned()) continue;
//      if(!dist->compute(viewArray[i].id())) continue;

      if (i == 0 || !comp(viewArray[i], viewArray[i - 1], true)) {
        backup.resize(0);
        double mean_i, variance_i;
        {
          double _mean = domainMean(viewArray[i]);
          double _variance = domainVariance(viewArray[i], _mean);
          mean_i = P ? mean + _mean : mean - _mean;
          variance_i = variance - _variance;
        }

        // Probability mass for each value in viewArray[i]
//      Region r(home);
        double *approx_dens_a = r.alloc<double>((int) viewArray[i].size());
        double approx_sum = 0;
        {
          int j = 0;
          for (ViewValues<View> val(viewArray[i]); val(); ++val) {
            int v = P ? val.val() : -val.val();
            if (variance_i == 0)
              approx_dens_a[j] = 1;
            else
              approx_dens_a[j] = exp(
                -std::pow(v - mean_i, 2) / (2 * variance_i));
            approx_sum += approx_dens_a[j];
            j++;
          }
        }

        // Normalization and assignation
        {
          int j = 0;
          for (ViewValues<View> val(viewArray[i]); val(); ++val) {
            Record r;
            r.val = viewArray[i].baseval(val.val());
            r.dens = approx_dens_a[j] / approx_sum;
            send(prop_id, viewArray[i].id(), r.val, r.dens);
            backup.push_back(r);
            j++;
          }
        }
      } else {
//        _reuse_count++;
        for (int j=0; j<backup.size(); j++) {
          send(prop_id, viewArray[i].id(), backup[j].val,
                             backup[j].dens);
        }
      }
    }
//    std::cout << (double)_reuse_count / viewArray.size() << std::endl;
  }

  template<> forceinline void
  approx_dens_for_array(Space&, unsigned int, const ViewArray<NoView>&, bool,
                        Propagator::SendMarginal, double, double) {}

  template<class P, class N>
  void
  cbslinear(Space& home, unsigned int prop_id, Propagator::SendMarginal send,
            const ViewArray<P>& x, const ViewArray<N>& y, int lb, int ub) {
//    {
//      bool compute = false;
//      for (int i=0; i<x.size(); i++) {
//        if (x[i].assigned() && dist->compute(x[i].id())) {
//          compute = true;
//          break;
//        }
//      }
//      if (!compute) {
//        for (int i=0; i<y.size(); i++) {
//          if (y[i].assigned() && dist->compute(y[i].id())) {
//            compute = true;
//            break;
//          }
//        }
//      }
//      if (!compute) return;
//    }

    // Mean and variance of the distribution
    double mean, variance;
    MV_dist(lb, ub, x, y, mean, variance);

    approx_dens_for_array(home,prop_id,x,true,send,mean,variance);
    approx_dens_for_array(home,prop_id,y,false,send,mean,variance);
  }

}}}
