// Exact-integer certificate for the two-digit Parry row-norm obstruction.
// Build: g++ -O3 -std=c++17 -fno-fast-math certify.cpp -o certify
// Run:   ./certify > certificate.csv
// Every decision in the proof uses integer arithmetic. Floating sqrt only
// proposes an integer square root; exact integer inequalities correct it.
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <string>
#include <unordered_map>
#include <vector>
using I = __int128_t;
using U = __uint128_t;
using Z = int64_t;
static constexpr Z S = Z(1) << 48;
static constexpr Z EPS500 = (I(500)*S + 999999)/1000000; // 500*S*10^-6, rounded up
static Z PI;
struct C { Z r, i; };
static Z mul(Z a, Z b) { return Z(I(a)*b/S); }
static Z absz(Z a) { return a < 0 ? -a : a; }
static std::string istr(I v) {
    if (!v) return "0";
    bool neg=v<0; if(neg)v=-v;
    std::string s;
    while(v){s.push_back(char('0'+v%10));v/=10;}
    if(neg)s.push_back('-'); std::reverse(s.begin(),s.end());return s;
}
static Z hyp(Z a, Z b) {
    U n=U(I(a)*a+I(b)*b);
    // The estimate is NOT trusted. The two following tests are exact.
    uint64_t r=uint64_t(std::sqrt((long double)n));
    while (U(r)*r>n) --r;
    while (U(r+1)*(r+1)<=n) ++r;
    return Z(r);
}
static Z atan_fixed(Z d) {
    Z p=S/d, out=0; int k=0, sign=1;
    while(p){out+=sign*(p/(2*k+1));p/=d*d;sign=-sign;++k;}
    return out;
}
static C phase(int ell, Z x, int j) {
    // exp(-2*pi*i*ell*(x/S+j)/10).
    Z rem=Z((-I(ell)*(x+Z(j)*S))%(I(10)*S));
    if(rem>5*S)rem-=10*S;
    if(rem<-5*S)rem+=10*S;
    Z t=Z(I(2)*PI*rem/(I(10)*S));
    Z t2=mul(t,t), tc=S, ts=t, co=S, si=t;
    for(int k=1;k<=20;++k){
        tc=-(mul(tc,t2)/((2*k-1)*(2*k))); co+=tc;
        ts=-(mul(ts,t2)/((2*k)*(2*k+1))); si+=ts;
    }
    return {co,si};
}
struct AllPhases { std::array<std::array<C,10>,9> e; };
static std::unordered_map<Z,AllPhases> phase_cache;
static const AllPhases& phases(Z x) {
    auto it=phase_cache.find(x);if(it!=phase_cache.end())return it->second;
    AllPhases p;
    for(int ell=1;ell<=9;++ell)for(int j=0;j<10;++j)p.e[ell-1][j]=phase(ell,x,j);
    return phase_cache.emplace(x,p).first->second;
}
static C getphase(const AllPhases& p,int ell,int j){
    if(ell==0)return {S,0};
    C z=p.e[std::abs(ell)-1][j];if(ell<0)z.i=-z.i;return z;
}
struct Data { std::array<C,10> k,e; Z lk; };
static std::unordered_map<Z,Data> data_cache;
static const Data& data(Z x,int a,int b){
    auto it=data_cache.find(x);if(it!=data_cache.end())return it->second;
    const auto& p=phases(x);Data d;d.lk=0;
    for(int j=0;j<10;++j){
        C k{0,0};
        for(int z=0;z<10;++z)if(z!=a){C e=getphase(p,z-a,j);k.r+=e.r;k.i+=e.i;}
        d.k[j]=k;d.e[j]=getphase(p,b-a,j);d.lk+=hyp(k.r,k.i);
    }
    return data_cache.emplace(x,d).first->second;
}
// Returns a proven lower bound for 500*S*G at the box center.
static I center_lower(Z x,Z qr,Z qi,int a,int b){
    const auto& d=data(x,a,b);
    Z nq=hyp(qr,qi)+1, n1=hyp(qr-S,qi)+1;
    I out=0;
    if(a==b){
        I sum=0;for(int j=0;j<10;++j)sum+=hyp(d.k[j].r+qr,d.k[j].i+qi);
        out=500*sum+I(180)*d.lk-I(819)*nq-I(2619)*n1-I(7275)*S;
    } else {
        I s0=0,s1=0;
        for(int j=0;j<10;++j){
            C e=d.e[j], k=d.k[j];
            Z vr=k.r+mul(qr-S,e.r)-mul(qi,e.i);
            Z vi=k.i+mul(qr-S,e.i)+mul(qi,e.r);
            s0+=hyp(vr,vi);s1+=hyp(vr+S,vi);
        }
        out=500*s1+180*s0-I(5475)*S-I(2619)*(nq+n1);
    }
    return out-EPS500;
}
struct Box{Z x,qr,qi,hx,hr,hi;int depth;};
struct Stats{uint64_t nodes=0,leaves=0,tail=0;int maxdepth=0;I minmargin=I(1)<<120;};
static Stats certify(int a,int b){
    data_cache.clear();std::vector<Box> st;
    st.push_back({S/2,0,0,S/2,6*S,6*S,0});Stats out;
    while(!st.empty()){
        Box z=st.back();st.pop_back();++out.nodes;
        Z mr=std::max(Z(0),absz(z.qr)-z.hr), mi=std::max(Z(0),absz(z.qi)-z.hi);
        if(I(mr)*mr+I(mi)*mi>=I(36)*S*S){
            ++out.leaves;++out.tail;out.maxdepth=std::max(out.maxdepth,z.depth);continue;
        }
        I ax;Z lq;
        if(a==b){ax=I(146)*z.hx*S;lq=17;}
        else {ax=I(9)*(17*S+Z(std::abs(b-a))*(absz(z.qr-S)+absz(z.qi)+z.hr+z.hi))*z.hx;lq=25;}
        I ar=I(lq)*z.hr*S, ai=I(lq)*z.hi*S;
        I variation=(500*ax+S-1)/S+I(500)*lq*(z.hr+z.hi);
        I margin=center_lower(z.x,z.qr,z.qi,a,b)-variation;
        if(margin>0){
            ++out.leaves;out.minmargin=std::min(out.minmargin,margin);
            out.maxdepth=std::max(out.maxdepth,z.depth);continue;
        }
        if(z.depth>=100 || z.hx==0 || z.hr==0 || z.hi==0){
            std::cerr<<"FAILED "<<a<<b<<" at depth "<<z.depth<<"\n";std::exit(2);
        }
        ++z.depth;
        if(ax>=ar && ax>=ai){if(z.hx%2){std::cerr<<"Non-dyadic split\n";std::exit(4);}z.hx/=2;Box l=z,r=z;l.x-=z.hx;r.x+=z.hx;st.push_back(l);st.push_back(r);}
        else if(ar>=ai){if(z.hr%2){std::cerr<<"Non-dyadic split\n";std::exit(4);}z.hr/=2;Box l=z,r=z;l.qr-=z.hr;r.qr+=z.hr;st.push_back(l);st.push_back(r);}
        else {if(z.hi%2){std::cerr<<"Non-dyadic split\n";std::exit(4);}z.hi/=2;Box l=z,r=z;l.qi-=z.hi;r.qi+=z.hi;st.push_back(l);st.push_back(r);}
    }
    return out;
}
int main(int argc,char** argv){
    PI=16*atan_fixed(5)-4*atan_fixed(239);
    if(PI!=884279719003552LL){std::cerr<<"Unexpected pi enclosure\n";return 3;}
    int lo=0,hi=99;if(argc>=2)lo=std::atoi(argv[1]);if(argc>=3)hi=std::atoi(argv[2]);else if(argc>=2)hi=lo;
    if(lo<0 || hi>99 || lo>hi){std::cerr<<"Require 0 <= lo <= hi <= 99\n";return 5;}
    std::cout<<"word,nodes,leaves,tail_leaves,max_depth,min_margin_numerator,margin_denominator,status\n";
    uint64_t nodes=0,leaves=0;
    for(int w=lo;w<=hi;++w){
        Stats z=certify(w/10,w%10);nodes+=z.nodes;leaves+=z.leaves;
        std::cout<<w/10<<w%10<<","<<z.nodes<<","<<z.leaves<<","<<z.tail<<","<<z.maxdepth<<","<<istr(z.minmargin)<<","<<istr(I(500)*S)<<",PASS\n"<<std::flush;
        std::cerr<<"PASS "<<w/10<<w%10<<" nodes="<<z.nodes<<" cached_x="<<phase_cache.size()<<"\n";
    }
    std::cerr<<"TOTAL nodes="<<nodes<<" leaves="<<leaves<<"\n";
}
