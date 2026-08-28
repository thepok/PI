#include <algorithm>
#include <array>
#include <atomic>
#include <cassert>
#include <cfloat>
#include <cfenv>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#pragma STDC FENV_ACCESS ON

static_assert(FLT_RADIX == 2, "binary floating point required");
static_assert(LDBL_MANT_DIG >= 64, "at least IEEE binary80 precision required");

namespace iv {
constexpr long double INF = std::numeric_limits<long double>::infinity();
struct I { long double lo, hi; };

inline long double dn(long double x) {
  return std::nextafterl(std::nextafterl(x, -INF), -INF);
}
inline long double up(long double x) {
  return std::nextafterl(std::nextafterl(x, INF), INF);
}
inline I point(long double x) { return {dn(x), up(x)}; }
inline I exact(long double x) { return {x, x}; }
inline I add(I a, I b) { return {dn(a.lo + b.lo), up(a.hi + b.hi)}; }
inline I neg(I a) { return {dn(-a.hi), up(-a.lo)}; }
inline I sub(I a, I b) { return add(a, neg(b)); }
inline I mul(I a, I b) {
  long double p1 = a.lo*b.lo, p2 = a.lo*b.hi, p3 = a.hi*b.lo, p4 = a.hi*b.hi;
  return {dn(std::min(std::min(p1,p2),std::min(p3,p4))),
          up(std::max(std::max(p1,p2),std::max(p3,p4)))};
}
inline I reciprocal(I b) {
  if (b.lo <= 0 && 0 <= b.hi) throw std::runtime_error("interval division by zero");
  return {dn(1.0L/b.hi), up(1.0L/b.lo)};
}
inline I div(I a, I b) { return mul(a, reciprocal(b)); }
inline I sqr(I a) {
  if (a.lo >= 0) return {dn(a.lo*a.lo), up(a.hi*a.hi)};
  if (a.hi <= 0) return {dn(a.hi*a.hi), up(a.lo*a.lo)};
  long double m = std::max(a.lo*a.lo, a.hi*a.hi);
  return {0.0L, up(m)};
}
inline I scale(I a, long double k) { return mul(a, exact(k)); }
inline I hull(I a, I b) { return {std::min(a.lo,b.lo), std::max(a.hi,b.hi)}; }
inline long double mid(I a) { return (a.lo/2.0L)+(a.hi/2.0L); }
inline long double width(I a) { return a.hi-a.lo; }

// Every integer passed here is < 2^64 and hence exact in the required
// long-double format (including the 10^15 decimal chunks).
inline I uint_exact(std::uint64_t x) { return exact(static_cast<long double>(x)); }
inline I int_exact(std::int64_t x) { return exact(static_cast<long double>(x)); }

} // namespace iv
using iv::I;

static std::string PI_INT_DIGITS;
static std::string PI_FRAC_DIGITS;
static I PI_INTERVAL;
static std::vector<I> ORBITS;
static constexpr int SUFFIX_DIGITS = 30;
static constexpr long double TRIG_PAD = 1.0e-12L;
static std::atomic<std::uint64_t> reduction_fallbacks{0};

I decimal30_fraction(const std::string& s30) {
  if (s30.size() != 30) throw std::runtime_error("decimal30 length");
  std::uint64_t hi = 0, lo = 0;
  for (int i=0;i<15;i++) hi = hi*10 + static_cast<unsigned>(s30[i]-'0');
  for (int i=15;i<30;i++) lo = lo*10 + static_cast<unsigned>(s30[i]-'0');
  constexpr std::uint64_t E15 = 1000000000000000ULL;
  I num = iv::add(iv::mul(iv::uint_exact(hi), iv::uint_exact(E15)), iv::uint_exact(lo));
  I den = iv::mul(iv::uint_exact(E15), iv::uint_exact(E15));
  return iv::div(num, den);
}

I make_orbit_interval(std::size_t n) {
  if (n + SUFFIX_DIGITS > PI_FRAC_DIGITS.size())
    throw std::runtime_error("insufficient certified suffix digits");
  std::string s = PI_FRAC_DIGITS.substr(n, SUFFIX_DIGITS);
  I lo = decimal30_fraction(s);
  // [first 30 digits, first 30 digits + 10^-30] contains every suffix of
  // every alpha in the certified D-digit decimal cylinder.
  constexpr std::uint64_t E15 = 1000000000000000ULL;
  I den = iv::mul(iv::uint_exact(E15), iv::uint_exact(E15));
  I eps = iv::div(iv::exact(1.0L), den);
  return {lo.lo, iv::add(lo, eps).hi};
}
I orbit_interval(std::size_t n) {
  if (n >= ORBITS.size()) throw std::runtime_error("orbit cache exhausted");
  return ORBITS[n];
}

I reduce_centered(I x) {
  long double m = iv::mid(x);
  long double kld = std::floor(m + 0.5L);
  if (std::fabs(kld) > 9.0e15L) throw std::runtime_error("reduction integer too large");
  I r = iv::sub(x, iv::exact(kld));
  if (r.lo < -0.5000000001L || r.hi > 0.5000000001L) {
    reduction_fallbacks.fetch_add(1,std::memory_order_relaxed);
    // This branch is deliberately conservative.  It did not trigger in the
    // printed certificate runs.
    return {-0.5L,0.5L};
  }
  return r;
}

I add_trig_pad(I a) {
  return {iv::dn(a.lo - TRIG_PAD), iv::up(a.hi + TRIG_PAD)};
}

// Taylor polynomials with interval coefficients.  On |x|<=4, omitted
// remainders are < 4^51/51! < 4e-36; the explicit 1e-12 output padding is
// vastly larger and also makes the certificate insensitive to scalar
// polynomial-evaluation details.
const std::array<I,26>& sin_coeffs() {
  static const std::array<I,26> c=[] {
    std::array<I,26> z;
    z[0]=iv::exact(1.0L);
    for (int k=0;k<25;k++) {
      I den=iv::exact(static_cast<long double>((2*k+2)*(2*k+3)));
      z[k+1]=iv::neg(iv::div(z[k],den));
    }
    return z;
  }();
  return c;
}
const std::array<I,26>& cos_coeffs() {
  static const std::array<I,26> c=[] {
    std::array<I,26> z;
    z[0]=iv::exact(1.0L);
    for (int k=0;k<25;k++) {
      I den=iv::exact(static_cast<long double>((2*k+1)*(2*k+2)));
      z[k+1]=iv::neg(iv::div(z[k],den));
    }
    return z;
  }();
  return c;
}
I sin_taylor(I x) {
  I y=iv::sqr(x);
  const auto& c=sin_coeffs();
  I p=c[25];
  for (int k=24;k>=0;k--) p=iv::add(c[k],iv::mul(y,p));
  return add_trig_pad(iv::mul(x,p));
}
I cos_taylor(I x) {
  I y=iv::sqr(x);
  const auto& c=cos_coeffs();
  I p=c[25];
  for (int k=24;k>=0;k--) p=iv::add(c[k],iv::mul(y,p));
  return add_trig_pad(p);
}

I sin_pi_times(I cycle) { return sin_taylor(iv::mul(PI_INTERVAL,cycle)); }
I cos_two_pi_times_centered(I cycle) {
  I u=reduce_centered(cycle);
  return cos_taylor(iv::mul(iv::scale(PI_INTERVAL,2.0L),u));
}

struct Params { I one_minus_beta, alpha_zero; };
Params parameters(std::uint64_t q) {
  I qI=iv::uint_exact(q);
  I u=iv::div(iv::exact(1.0L),iv::scale(qI,2.0L));
  I s=sin_pi_times(u);
  I a=iv::scale(iv::sqr(s),2.0L);
  I q2=iv::sqr(qI);
  I numerator=iv::add(iv::scale(q2,2.0L),iv::exact(1.0L));
  I alpha=iv::sub(iv::mul(a,iv::div(numerator,iv::scale(qI,3.0L))),
                  iv::div(iv::exact(1.0L),qI));
  return {a,alpha};
}

I coefficient(std::uint64_t q,std::uint64_t h,I one_minus_beta) {
  I qI=iv::uint_exact(q), hI=iv::uint_exact(h), q2=iv::sqr(qI);
  I fejer,edge;
  if (h<=q) {
    // (4q^3+2q-6qh^2+3h^3-3h)/(6q^2)
    I q3=iv::mul(q2,qI), h2=iv::sqr(hI), h3=iv::mul(h2,hI);
    I num=iv::add(iv::scale(q3,4.0L),iv::scale(qI,2.0L));
    num=iv::sub(num,iv::scale(iv::mul(qI,h2),6.0L));
    num=iv::add(num,iv::scale(h3,3.0L));
    num=iv::sub(num,iv::scale(hI,3.0L));
    fejer=iv::div(num,iv::scale(q2,6.0L));
    edge=iv::div(iv::sub(iv::scale(hI,3.0L),iv::scale(qI,2.0L)),iv::scale(q2,2.0L));
  } else {
    I a=iv::sub(iv::sub(iv::scale(qI,2.0L),hI),iv::exact(1.0L));
    I b=iv::sub(iv::scale(qI,2.0L),hI);
    I c=iv::add(b,iv::exact(1.0L));
    fejer=iv::div(iv::mul(iv::mul(a,b),c),iv::scale(q2,6.0L));
    edge=iv::div(b,iv::scale(q2,2.0L));
  }
  return iv::add(iv::mul(one_minus_beta,fejer),edge);
}

I center_interval(std::uint64_t q,std::uint64_t label) {
  return iv::div(iv::uint_exact(2*label+1),iv::uint_exact(2*q));
}

I boundary_kernel(std::uint64_t q,I center,std::size_t n) {
  I t=reduce_centered(iv::sub(orbit_interval(n),center));
  I shift=iv::div(iv::exact(1.0L),iv::scale(iv::uint_exact(q),2.0L));
  I splus=sin_pi_times(iv::add(t,shift));
  I sminus=sin_pi_times(iv::sub(t,shift));
  I cosdiff=iv::scale(iv::mul(splus,sminus),-2.0L);

  I qt=reduce_centered(iv::scale(t,static_cast<long double>(q)));
  I sqt=sin_pi_times(qt);
  I st=sin_pi_times(t);
  I st2=iv::sqr(st);
  if (st2.lo<=0) throw std::runtime_error("removable singularity encountered; closed-form branch required");
  I fejer=iv::div(iv::sqr(sqt),iv::scale(st2,static_cast<long double>(q)));
  return iv::mul(cosdiff,iv::sqr(fejer));
}

std::pair<unsigned,unsigned> primitive_part(unsigned h) {
  unsigned v=0;
  while (h%10==0) {++v;h/=10;}
  return {v,h};
}

I endpoint(std::uint64_t q,std::uint64_t label,std::uint64_t horizon,I one_minus_beta) {
  I center=center_interval(q,label);
  I total=iv::exact(0.0L);
  for (std::uint64_t h=10;h<2*q;h+=10) {
    auto [v,prim]=primitive_part(static_cast<unsigned>(h));
    I block=iv::exact(0.0L);
    for (unsigned j=0;j<v;j++) {
      I ch=iv::sub(iv::scale(orbit_interval(horizon+j),static_cast<long double>(prim)),
                   iv::scale(center,static_cast<long double>(h)));
      I c0=iv::sub(iv::scale(orbit_interval(j),static_cast<long double>(prim)),
                   iv::scale(center,static_cast<long double>(h)));
      block=iv::add(block,iv::sub(cos_two_pi_times_centered(ch),cos_two_pi_times_centered(c0)));
    }
    total=iv::add(total,iv::mul(coefficient(q,h,one_minus_beta),block));
  }
  return total;
}

struct ScorePair { I first, final; };
ScorePair score(std::uint64_t q,std::uint64_t label,std::uint64_t firstN,std::uint64_t finalN) {
  Params p=parameters(q);
  I center=center_interval(q,label);
  I sum=iv::exact(0.0L),first=iv::exact(0.0L);
  for (std::uint64_t n=0;n<finalN;n++) {
    sum=iv::add(sum,boundary_kernel(q,center,n));
    if (n+1==firstN) first=sum;
  }
  I firstReal=iv::sub(iv::scale(iv::sub(first,iv::scale(p.alpha_zero,static_cast<long double>(firstN))),0.5L),
                      endpoint(q,label,firstN,p.one_minus_beta));
  I finalReal=iv::sub(iv::scale(iv::sub(sum,iv::scale(p.alpha_zero,static_cast<long double>(finalN))),0.5L),
                      endpoint(q,label,finalN,p.one_minus_beta));
  return {firstReal,finalReal};
}

I surplus(std::uint64_t q,I realScore,std::uint64_t horizon) {
  I potential=iv::div(iv::uint_exact(7*horizon),iv::uint_exact(3*q));
  return iv::sub(iv::scale(realScore,static_cast<long double>(q)),potential);
}

I positive_part_of_negative(I g) {
  // h=(-g)_+ with exact interval extension.
  if (g.lo>=0) return iv::exact(0.0L);
  if (g.hi<=0) return {-g.hi,-g.lo};
  return {0.0L,-g.lo};
}

void printI(const char* name,I x) {
  std::cout<<name<<"=["<<std::setprecision(21)<<x.lo<<", "<<x.hi<<"]\n";
}
void printRow(int d,I G,I D,I h,I Y) {
  std::cout<<d
           <<" G=["<<std::setprecision(21)<<G.lo<<", "<<G.hi<<"]"
           <<" D=["<<D.lo<<", "<<D.hi<<"]"
           <<" Hdef=["<<h.lo<<", "<<h.hi<<"]"
           <<" Y=["<<Y.lo<<", "<<Y.hi<<"]\n";
}

void load_digits(const char* path) {
  std::ifstream f(path);
  f>>PI_INT_DIGITS;
  if (PI_INT_DIGITS.size()<100051 || PI_INT_DIGITS[0]!='3')
    throw std::runtime_error("bad pi digit certificate");
  PI_FRAC_DIGITS=PI_INT_DIGITS.substr(1);
  I frac=decimal30_fraction(PI_FRAC_DIGITS.substr(0,30));
  constexpr std::uint64_t E15=1000000000000000ULL;
  I eps=iv::div(iv::exact(1.0L),iv::mul(iv::uint_exact(E15),iv::uint_exact(E15)));
  PI_INTERVAL={iv::add(iv::exact(3.0L),frac).lo,iv::add(iv::add(iv::exact(3.0L),frac),eps).hi};
  ORBITS.resize(100010);
  for (std::size_t n=0;n<ORBITS.size();++n) ORBITS[n]=make_orbit_interval(n);
}

int main(int argc,char**argv) {
  if (argc<3) {
    std::cerr<<"usage: t189_interval_cert pi_digits_cert.txt root|rootall|node\n";
    return 2;
  }
  load_digits(argv[1]);
  std::string mode=argv[2];
  std::cout<<"claim=outward_interval_certificate\n";
  std::cout<<"binary_radix="<<FLT_RADIX<<" long_double_mantissa_bits="<<LDBL_MANT_DIG<<"\n";
  std::cout<<"decimal_suffix_enclosure_digits="<<SUFFIX_DIGITS<<" trig_output_pad="<<std::setprecision(4)<<TRIG_PAD<<"\n";
  printI("pi_interval_used",PI_INTERVAL);

  if (mode=="root" || mode=="rootall") {
    ScorePair parentS=score(1000,334,1000,1000);
    I parent=surplus(1000,parentS.final,1000);
    printI("B_parent_q1000_A334_N1000",parent);
    int d0=(mode=="root" ? 1 : 0), d1=(mode=="root" ? 2 : 10);
    for (int d=d0;d<d1;d++) {
      std::uint64_t label=334ULL+static_cast<std::uint64_t>(d)*1000ULL;
      ScorePair childS=score(10000,label,1000,10000);
      I oldChild=surplus(10000,childS.first,1000);
      I newChild=surplus(10000,childS.final,10000);
      I G=iv::sub(oldChild,parent);
      I D=iv::sub(newChild,oldChild);
      I h=positive_part_of_negative(G);
      I Y=iv::sub(D,h);
      if (mode=="root") {
        printI("B_child_q10000_A1334_N1000",oldChild);
        printI("B_child_q10000_A1334_H10000",newChild);
        printI("G_d1",G); printI("D_d1",D); printI("G_plus_D_d1",Y);
      } else printRow(d,G,D,h,Y);
    }
  } else if (mode=="node") {
    std::uint64_t parentA = argc > 3 ? std::strtoull(argv[3],nullptr,10) : 1334ULL;
    ScorePair parentS=score(10000,parentA,10000,10000);
    I parent=surplus(10000,parentS.final,10000);
    std::cout << "parent_A=" << parentA << "\n";
    printI("B_parent_q10000_N10000",parent);
    std::array<I,10> G,D,h,Y;
    #pragma omp parallel for schedule(static)
    for (int d=0;d<10;d++) {
      std::uint64_t label=parentA+static_cast<std::uint64_t>(d)*10000ULL;
      ScorePair ss=score(100000,label,10000,100000);
      I oldB=surplus(100000,ss.first,10000);
      I newB=surplus(100000,ss.final,100000);
      G[d]=iv::sub(oldB,parent);
      D[d]=iv::sub(newB,oldB);
      h[d]=positive_part_of_negative(G[d]);
      Y[d]=iv::sub(D[d],h[d]);
    }
    for (int d=0;d<10;d++) printRow(d,G[d],D[d],h[d],Y[d]);
    I M0=iv::exact(0),M1=iv::exact(0),Db0=iv::exact(0),Db1=iv::exact(0),H0=iv::exact(0),H1=iv::exact(0);
    for (int d=0;d<10;d++) {
      if ((d&1)==0) {M0=iv::add(M0,Y[d]);Db0=iv::add(Db0,D[d]);H0=iv::add(H0,h[d]);}
      else {M1=iv::add(M1,Y[d]);Db1=iv::add(Db1,D[d]);H1=iv::add(H1,h[d]);}
    }
    I five=iv::exact(5.0L);
    M0=iv::div(M0,five); M1=iv::div(M1,five);
    Db0=iv::div(Db0,five); Db1=iv::div(Db1,five);
    H0=iv::div(H0,five); H1=iv::div(H1,five);
    printI("Dbar_even",Db0);printI("Dbar_odd",Db1);
    printI("H_even",H0);printI("H_odd",H1);
    printI("M_even",M0);printI("M_odd",M1);
    I Z=iv::scale(iv::add(Db0,Db1),0.5L);
    I qR5=iv::scale(iv::sub(Db0,Db1),0.5L);
    I Havg=iv::scale(iv::add(H0,H1),0.5L);
    I deltaH=iv::scale(iv::sub(H0,H1),0.5L);
    I C=iv::sub(Z,Havg);
    I V=iv::sub(qR5,deltaH);
    printI("Z_common_zero_minus_potential",Z);
    printI("qR5",qR5);
    printI("H_average",Havg);
    printI("deltaH",deltaH);
    printI("C_common_including_deficit",C);
    printI("qR5_minus_deltaH",V);
  } else {
    throw std::runtime_error("unknown mode");
  }
  std::cout<<"reduction_fallbacks="<<reduction_fallbacks.load()<<"\n";
}
