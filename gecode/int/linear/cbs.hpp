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
  forceinline int
  nonAssignedSize(SolnDistributionSize* size,
                  const ViewArray<P>& x, const ViewArray<N>& y) {
    int d = 0;
    for (int i=0; i<x.size(); i++)
      if (!x[i].assigned() && size->varInBrancher(x[i].id()))
        d += x[i].size();
    for (int i=0; i<y.size(); i++)
      if (!y[i].assigned() && size->varInBrancher(x[i].id()))
        d += y[i].size();
    return d;
  }

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
  forceinline void
  approx_dens_for_array(Space& home, unsigned int prop_id,
                        const ViewArray<View>& a, bool P,
                        SolnDistribution* dist,
                        double mean, double variance) {
    // For every variable in the domain of ViewArray a
    for (int i = 0; i < a.size(); i++) {
      if (a[i].assigned()) continue;

      double mean_i, variance_i;
      {
        double _mean = domainMean(a[i]);
        double _variance = domainVariance(a[i], _mean);
        mean_i = P? mean+_mean : mean-_mean;
        variance_i = variance - _variance;
      }

      // Probability mass for each value in a[i]
      Region r(home);
      double *approx_dens_a = r.alloc<double>((int)a[i].size());
      double approx_sum = 0;
      {
        int j = 0;
        for (ViewValues<View> val(a[i]); val(); ++val) {
          int v = P? val.val() : -val.val();
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
        for (ViewValues<View> val(a[i]); val(); ++val) {
          dist->setMarginalDistribution(
            prop_id,
            a[i].id(),
            a[i].baseval(val.val()),
            approx_dens_a[j] / approx_sum
          );
          j++;
        }
      }
    }
  }

  template<> forceinline void
  approx_dens_for_array(Space&, unsigned int, const ViewArray<NoView>&, bool,
                        SolnDistribution*, double, double) {}

  template<class P, class N>
  void
  cbslinear(Space& home, unsigned int prop_id, SolnDistribution* dist,
            const ViewArray<P>& x, const ViewArray<N>& y,
            int lb, int ub) {
    // Mean and variance of the distribution
    double mean, variance;
    MV_dist(lb, ub, x, y, mean, variance);

    approx_dens_for_array(home,prop_id,x,true,dist,mean,variance);
    approx_dens_for_array(home,prop_id,y,false,dist,mean,variance);
  }

}}}
