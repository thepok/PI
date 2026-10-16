#!/usr/bin/env python3
"""Prime-power Cartier evaluation with denominator exponent O(precision).

Uses the symmetric degree-six denominator Q0 and the exact Frobenius defect
R=(Q0**5-Q0(z**5,w**5))/5. Every operation is over integers modulo 5**a.
"""
from math import comb
from prime_power import baseline_directory, mul, trim


def bm(A, B, p):
    out = [[0] for _ in range(len(A)+len(B)-1)]
    for i, a in enumerate(A):
        if not any(a): continue
        for j, b in enumerate(B):
            if not any(b): continue
            v=mul(a,b,p)
            if len(out[i+j])<len(v):out[i+j]+=[0]*(len(v)-len(out[i+j]))
            for k,x in enumerate(v):out[i+j][k]=(out[i+j][k]+x)%p
    return [trim(row) for row in out]


def bp(A, n, p):
    out=[[1]]
    for _ in range(n):out=bm(out,A,p)
    return out


def qpower(F,D,n,p):
    ff=[[1]];dd=[[1]]
    for _ in range(n):ff.append(mul(ff[-1],F,p));dd.append(mul(dd[-1],D,p))
    out=[]
    for j in range(n+1):
        fac=comb(n,j)*(-1)**j%p
        out.append(trim([fac*x%p for x in mul(ff[j],dd[n-j],p)]))
    return out


def add(A,B,p,scale=1,offset=0):
    if len(A)<len(B)+offset:A += [[0] for _ in range(len(B)+offset-len(A))]
    for j,row in enumerate(B):
        target=A[j+offset]
        if len(target)<len(row):target += [0]*(len(row)-len(target))
        for k,x in enumerate(row):target[k]=(target[k]+scale*x)%p
        trim(target)


class BoundedCartier:
    def __init__(self,precision=3):
        assert precision>=2
        self.precision=a=precision
        self.modulus=p=5**a
        self.m=m=5
        self.h=h=1
        while 4*m//5<a-1:m*=5;h+=1
        self.m,self.h=m,h
        self.s=s=m//5
        D=[x%(5*p) for x in [8,-12,6,-1]]
        S0=[4,p-4,1]
        H0=[x%(5*p) for x in [32,-112,56]]
        H=[x%(5*p) for x in [32,-112,156,-100,25]]
        left=[1,5*p-2,1]
        F0=mul(left,mul(H0,H0,5*p),5*p)
        F=mul(left,mul(H,H,5*p),5*p)
        diff=[((F[j] if j<len(F) else 0)-(F0[j] if j<len(F0) else 0))%p
              for j in range(max(len(F),len(F0)))]
        assert all(x%25==0 for x in diff)
        q5=qpower(F0,D,5,5*p)
        for row,poly,sign in ((0,D,1),(5,F0,-1)):
            for j,x in enumerate(poly):
                if len(q5[row])<=5*j:q5[row]+=[0]*(5*j+1-len(q5[row]))
                q5[row][5*j]=(q5[row][5*j]-sign*x)%(5*p)
        assert all(x%5==0 for row in q5 for x in row)
        R=[trim([x//5 for x in row]) for row in q5]
        self.Rpowers=[[[1]]]
        for j in range(1,a):self.Rpowers.append(bm(self.Rpowers[-1],R,p))
        F0=[x%p for x in F0];D=[x%p for x in D]
        self.Qpowers=[qpower(F0,D,j,p) for j in range(m)]
        initial=[[0] for _ in range(m)]
        diffpow=[1]
        for j in range((a-1)//2+1):
            if j:diffpow=mul(diffpow,diff,p)
            piece=bm([mul(S0,diffpow,p)],self.Qpowers[m-j-1],p)
            add(initial,piece,p,offset=j)
        self.initial=initial
        self.invconstant=pow(pow(8,m,p),-1,p)

    def step(self,S,a,b):
        p,m=self.modulus,self.m
        out=[[0] for _ in range(m)]
        for j in range(self.precision):
            fac=(-5)**j*comb(self.s+j-1,j)%p
            if not fac:continue
            P=bm(S,self.Rpowers[j],p)
            section=[trim(row[b::5] or [0]) for row in P[a::5]]
            piece=bm(section,self.Qpowers[m-self.s-j],p)
            add(out,piece,p,fac)
        while len(out)>m:
            assert out[-1]==[0];out.pop()
        return out

    def coefficient(self,n,w):
        if min(n,w)<0:return 0
        S=self.initial
        while n or w:
            S=self.step(S,n%5,w%5);n//=5;w//=5
        return S[0][0]*self.invconstant%self.modulus

    def q(self,n):
        factor=(-1)**n*pow(2,(1-5*n//2)%(4*5**(self.precision-1)),self.modulus)
        return factor*self.coefficient(n,3*n)%self.modulus


if __name__=='__main__':
    import argparse,sys,time
    parser=argparse.ArgumentParser()
    parser.add_argument('--precision',type=int,default=3)
    parser.add_argument('--check',type=int,default=30)
    args=parser.parse_args()
    sys.path.insert(0,str(baseline_directory()))
    from full_pair import recurrence_sequences,p2
    now=time.monotonic();E=BoundedCartier(args.precision)
    A,B=recurrence_sequences(args.check)
    for n in range(args.check+1):
        q=p2(2-5*n//2)*B[n]
        assert q.denominator==1 and E.q(n)==q.numerator%E.modulus,n
    print('Exact comparison passed:',args.check,'precision',args.precision,'denominator exponent',E.m,'seconds',time.monotonic()-now,flush=True)
    S=E.initial;c=0
    for copies in range(1,args.precision+2):
        for a in [0,3]:
            b,c=(3*a+c)%5,(3*a+c)//5;S=E.step(S,a,b)
        vals=[x for row in S for x in row if x]
        print('copies03',copies,'nonzero numerator coefficients',len(vals),'sample',vals[:4],flush=True)
        if not vals:break
