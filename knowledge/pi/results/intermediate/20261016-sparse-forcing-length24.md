# Sparse forcing for every forbidden word of length at least 24

Status: proof sketch. Date: 2026-10-16.

This note gives a sharper finite-block Fourier estimate and uses the
[independent-bridge sparse-corridor construction](20261016-sparse-forcing-arbitrary-corridors.md)
to replace the threshold 49 by 24. It also records an independent audit of the inherited
complete-cylinder Fourier estimate. No Lean verification, novelty claim,
or pi-digit consequence is asserted.

## Result and precise quantifiers

Let w be a decimal word of length m>=24, and let d_w=log_10(lambda) be
the dimension of its avoidance shift. For every fixed set F of positive
digit positions with |F intersect [1,N]|=o(N), and every 0<s<d_w, there
exists kappa=kappa(w,F,s)>0 such that **every compatible assignment** a
on F satisfies

    dim_H(pi_10((Sigma_w)_a) intersect BA(kappa)) > s.

Consequently the intersection with BA has full dimension d_w. Kappa is
uniform over assignments on F and over all digit depths. Entropy
neutrality need not be separately assumed. This is the same quantified
conclusion as the October 16 arbitrary-corridor result, with a strictly
larger class of forbidden words.

The new input is a uniform shifted row-l1 bound for the unweighted
m-digit prefix-automaton matrix. Everything below is uniform over the
actual digits and overlap pattern of w.

## 1. A shifted Dirichlet bound that charges only the free digits

Let N,Q be positive integers with N<=Q and

    S_N(x)=sum_(j=0)^(N-1) exp(-2*pi*i*j*x).

Then

    (1/Q) sum_(ell=0)^(Q-1)|S_N(x+ell/Q)|
       <= 3 + (2/3) log N                                  (1)

for every real x, where log is natural. For N=1 the exact left side is 1.

Here is an elementary proof with explicit constants. For 0<d<=1/2,

    1/sin(pi*d) <= 1 + 1/(3d).                             (2)

If d<=1/6, concavity between 0 and pi/6 gives sin(pi*d)>=3d.
If d>=1/6, concavity between 0 and pi/2 gives sin(pi*d)>=2d,
and 1/(2d)<=1+1/(3d). Thus

    |S_N(y)| <= 1 + min(N, 1/(3||y||)).

Sort the Q distances from x+ell/Q to the nearest integer. The j-th is
at least (j-1)/(2Q) for j>=2. With theta=N/Q and c=2/3, the normalized
sum is at most

    1+theta+sum_(j=1)^(Q-1) min(theta,c/j)
    <= 1+theta+integral_0^Q min(theta,c/t) dt
    = 1+theta+c+c log(N/c)
    <= 3+c log N.

The last inequality uses theta<=1 and
c+c log(1/c)<1, which follows from log(3/2)<1/2.

Now fix a prefix of length r and a suffix of length t in an m-digit
decimal block. If r+t<m, their intersection consists of an arithmetic
progression of step 10^t with exactly N=10^(m-r-t) terms. On the full
10^m-point frequency grid its normalized Fourier l1 sum is the left side
of (1) with Q=10^(m-t). Therefore this cylinder intersection costs at most

    3+(2/3)(m-r-t)log10.

If r+t>=m, the intersection is empty or a singleton, so its cost is at
most 1. The bound charges the number of free middle digits, not m.

## 2. The terminal-suffix exclusions form a failure tree

Write p_t=w_1...w_t for 0<=t<m, with p_0 empty. Define f(t), for
1<=t<m, to be the length of the longest proper suffix of p_t that is also
a prefix of w. These edges t->f(t) form the usual prefix failure tree.

For every m-digit block z, let C_t(z) say that z ends in p_t, and define
its terminal suffix label to be the length of its longest suffix that is
a proper prefix of w. This label is defined even when z contains the
forbidden word. On a block that survives from the incoming state, it
agrees with the terminal state of the avoidance automaton. The label is
v exactly when

    1_(suffix_label=v)(z)
       = 1_C_v(z) - sum_(t: f(t)=v) 1_C_t(z).              (3)

Indeed the suffixes of z which are prefixes of w form one ancestor chain
in the failure tree. Equivalently, as a vector over suffix labels,

    suffix_label_vector(z)
       = 1_C_0(z)e_0
         +sum_(t=1)^(m-1)1_C_t(z)(e_t-e_(f(t))).            (4)

Thus p_0 appears with coefficient-vector l1 norm 1 and each p_t with
t>=1 appears with norm 2. The total number of signed suffix contributions
is exactly 2m-1, independent of how large individual failure-tree
branches are. Summing separate worst-case bounds for all terminal states
loses this fact.

## 3. Prefix survival and the sharpened row bound

From any incoming state u, a forbidden occurrence ending at new digit r
prescribes at most one prefix of length r, for each 1<=r<=m. Delete
prefix cylinders contained in others; the remaining cylinders are
disjoint. Their union is exactly the set of blocks that fail to survive
from u. Hence survival is one unrestricted prefix term minus at most
one prescribed-prefix term of each length r=1,...,m.

Multiply this signed prefix decomposition by (4). On surviving blocks,
the suffix label is precisely the actual terminal automaton state; on
rejected blocks the survival factor is zero. Put weights
a_0=1 and a_t=2 for 1<=t<m. The exact matrix K_m(x) is normalized by
10^(-m), and the triangle inequality plus (1) gives the row bound

    sup_x max_u sum_(ell=0)^(10^m-1) sum_v
         |K_(m;u,v)(x+ell/10^m)|
       <= L_m,                                             (5)

where

    L_m = 4m^2+m-1
          +(2/3)log(10) * m(m+1)(2m+1)/6.                  (6)

To verify the count, over r=0,...,m and t=0,...,m-1,

    sum a_t = (m+1)(2m-1),
    sum_(r+t<m) a_t = m^2,
    sum a_t (m-r-t)_+ = m(m+1)(2m+1)/6.

A singleton costs 1, a positive free length adds at most
2+(2/3)log(10)*(m-r-t). These three identities give (6).
Terms that do not actually occur, or whose prescriptions conflict, are
simply overcounted. No assumption on the border structure of w is made.

## 4. Perron conjugation is paid once

Let D be the digit-counting automaton matrix, Dh=lambda h, H=diag(h),
B_0=10^m, and P=lambda^(-m)H^(-1)D^mH. The earlier uniform automaton
estimates, together with the spectral refinement proved immediately below,
give

    max h/min h<=2,     B_0/lambda^m<10001/10000,
    (P^r)_(u,v)>=p_*=(1/4)10^(-(m-1)) for every r>=2.        (7)

### The autocorrelation identity gives a smaller spectral loss

Let a_n count length-n words avoiding w, with a_0=1, and let b_n count
length-n words whose first occurrence of w ends at their last digit.
Extending each avoiding word by one digit gives

    b_n=10a_(n-1)-a_n,     n>=1.

Let c_d be one when w overlaps itself at shift d, meaning its suffix of
length m-d equals its prefix of that length, and zero otherwise. Here
0<=d<m and c_0=1. Append w to any avoiding word of length n. Its first
occurrence ends at position n+m-d for exactly one such overlap shift d.
Conversely, a word with its first occurrence ending there has a unique
extension by the last d digits of w. Thus

    a_n=sum_(d=0)^(m-1)c_d b_(n+m-d),     n>=0.

Writing A(z)=sum a_n z^n, B(z)=sum b_n z^n, and
C_*(z)=sum_(d=0)^(m-1)c_d z^d, these two exact counts give

    (1-10z)A(z)+B(z)=1,       z^m A(z)=C_*(z)B(z),
    A(z)=C_*(z)/[(1-10z)C_*(z)+z^m].

The avoidance matrix is primitive by the preceding positive two-block
estimate. Perron counting makes A(z) diverge at z=1/lambda, so its
denominator vanishes there. Equivalently, with
C(X)=sum_(d=0)^(m-1)c_d X^(m-1-d),

    (10-lambda)C(lambda)=1,       C(lambda)>=lambda^(m-1).

Words over any nine-digit alphabet excluding a digit of w avoid w, so
lambda>=9. Consequently

    lambda>=10-9^(-(m-1)).

Put epsilon_m=1/(10*9^(m-1)). For m>=24,
10001m<10*9^(m-1): check m=24 by integers, then use that
m/9^(m-1) is decreasing. Bernoulli's inequality gives

    (lambda/10)^m >= (1-epsilon_m)^m
       >=1-m epsilon_m >10000/10001.

This proves the spectral bound in (7), uniformly over all words of the
given length. No approximation to a Perron root is used.

### The product estimate

For L=rm, the entire free Parry Fourier matrix is

    R_L(x)=(B_0/lambda^m)^r H^(-1)
           [K_m(B_0^(r-1)x)...K_m(x)] H.

Apply the shifted row-norm induction to the unweighted product first.
Then perform the two outside diagonal multiplications. Equation (5)
therefore yields

    shifted row-l1 norm of R_L <= 2 gamma_m^r,
    gamma_m := (10001/10000)L_m.                            (8)

The factor 2 is an outside prefactor. Charging it once per m-digit block
would create an unnecessary exponential loss.

For the uniform u->v bridge, divide the entry of R_L by
(P^r)_(u,v)>=p_*. Thus its shifted scalar Fourier l1 norm is at most

    (2/p_*) gamma_m^r.                                    (9)

Each bridge word has probability at most (2/p_*)lambda^(-L), as in the
existing independent-bridge construction.

## 5. Exact threshold and parameter order

The elementary bound log(10)<7/3 gives

    gamma_m < G_m
       := (10001/10000)(14m^3+129m^2+34m-27)/27.            (10)

For m=24,

    G_24=895519543/90000 < 10^4.                           (11)

The inequality is an exact integer comparison; no sampled Fourier
operator estimate or decimal logarithm is used.

The function log(G_m)/m decreases for m>=24. Indeed
mG'_m<3G_m, while log(G_m)>3, so its derivative is negative.
Consequently gamma_m<10^(m/6) for every m>=24.

An explicit uniform macroblock choice is r=20000. At m=24,

    [8*10^23*(895519543/90000)^20000]^6 < 10^480000.        (12)

An elementary integer certificate avoids evaluating these large powers:

    G_24/10^4 < 249/250,
    (249/250)^250 < 1/2,
    8*10^23 < 2^80.

For the middle inequality, Bernoulli gives
(250/249)^250>=1+250/249>2. Raising its reciprocal bound to the
80th power proves (12). The base-10 exponent per digit is approximately
0.1666261547<1/6.
The same choice works for every m>=24: adding
log(8*10^(m-1))/(rm) to log(G_m)/m still gives a decreasing function of m.
For example, after multiplying its derivative by m^2 and using natural
logs, its numerator is at most
3-log(G_m)+(log10-log8)/r<0.
The clean bound also dominates 2+log(10^L), the uniform-tail block bound:
G_m>m, log10<3, and m^r>2+3rm for m>=24 and r>=2, the last inequality
following from the r=2 case by induction.
The entropy loss is smaller than 1/r because 2/p_*=8*10^(m-1)<10^m.

Given 0<s<d_w, choose r>=20000 with 1/r<d_w-s. Then

    beta_L := log_10((2/p_*)G_m^r)/L < 1/6,
    d_L := d_w-log_10(2/p_*)/L > s.

Choose an auxiliary complete-cylinder BA measure of dimension delta close
enough to one that e(delta)>beta_L and d_L+delta-1>s. Choose
beta_L<alpha<eta<e(delta), and a positive epsilon with
d_L+delta-1-2epsilon>s. All choices precede assigning a rational slice
and taking a weak limit.

The independent-bridge sparse-corridor proof applies with these constants:
freeze macroblocks meeting F to a compatible reference, fix boundary
states to the reference, and choose clean bridges independently. Dirty
blocks have zero density; cylinder masses have exponent d_L-epsilon and
rescaled tails obey the same all-scale Fourier estimate with exponent
alpha and depth cost 10^(epsilon N). Complete-cylinder slicing gives a
Frostman exponent d_L+delta-1-2epsilon>s. One rational denominator Q is
uniform over assignments, so kappa=kappa_mu/Q^2 is uniform as well.

This proves the displayed result at the stated proof-sketch status.
Lengths below 24 and arbitrary finite-type subshifts remain unresolved.
The September 6 two-digit obstruction is respected: the present bound
does not assert contraction at m=2.

## 6. Independent audit of the complete-cylinder analytic input

The required input is

    |widehat(mu restricted to J)(xi)|
       <= C_Gamma mu(J)(1+|J||xi|)^(-e(delta)),
    e(delta)=delta(2delta-1)/((2delta+1)(3-delta)),           (13)

uniformly over complete Schottky cylinders J of a fixed group.

I checked the existing adaptation against the primary source,
Lequen–Sahlsten (2026), especially §§2.4–2.8 and Lemmas 3.1–3.5:
https://arxiv.org/html/2607.18010v1 .
The paper's theorem is global; (13) requires the adaptation and is not
being attributed to the paper as a stated theorem.

The following possible uniformity failures were checked:

* Outer-cylinder normalization: for J=gamma_p(I_b), division of the
  spherical conformal weight by mu(J) has a uniform C1 bound because
  mu(J) is comparable to |J|^delta and gamma_p''/gamma_p' is uniformly
  bounded on the fixed enlargement U_b.
* The pole q_J=gamma_p^(-1)(infinity) lies outside U_b, in the inverse
  last-letter interval. For empty p it is infinity. Composing with the
  stopped map gamma_(v') sends this pole into
  I_(overline(v')), after deleting the last letter before reversal.
  These containers are independent of p and have size comparable to
  the stopping scale tau.
* Reversed, deleted cylinders have bounded overlap by comparable
  sizes and uniform contraction. Each has mass comparable to tau^delta.
  Therefore the pole-counting bound uses the original fixed Frostman
  constant and is uniform in p; it does not assume the poles themselves
  lie in the limit set.
* A determinant-one lift of the normalized composed map has bottom
  row sqrt(|J|)(c_(pv'),d_(pv')). Its derivative is comparable to tau.
  After choosing the sign so C_v x+D_v>0 on U_i, the derivative
  difference factors as tau W(x)(A x+B), with W positive and uniformly
  C1. The primary Lemma 3.5 applies uniformly to these amplitudes.
* The resulting bound
  ||f_i||_2^2<=C[tau^delta+(R tau)^(-1/2)]
  uses only the uniformly bounded coefficient-pair counts. Smoothing
  the unnormalized fixed measure mu restricted to I_i gives
  r^((delta-1)/2)||f_i||_2+r||f_i'||_infinity.
  At tau=R^(-1/(2delta+1)) and
  r=R^(-5delta/((3-delta)(2delta+1))), both powers equal -e(delta).

These checks found no failure of depth uniformity.

### A normalization point that should be explicit

Bowen supplies free convex-cocompact modular groups with dimensions
approaching one. The cited Schottky setup allows a real conjugation to
obtain its separated bounded disk presentation. An arbitrary real
Möbius change of coordinates must not be assumed to preserve BA.

One can arrange a **rational** conjugation. Start with any conjugator
giving the desired finite strict disk separations and exclusion of
infinity (and of zero if using that normalization). These properties
persist in a neighborhood of the conjugator. PSL_2(Q) is dense in
PSL_2(R), so a rational conjugator in that neighborhood retains all of
them. Its pole is outside the original compact limit set.

Rational Möbius transformations preserve BA uniformly on compact
subsets avoiding their pole. Here is a direct check. Write
g(x)=(Ax+B)/(Cx+D) with integer coefficients and nonzero determinant.
For a rational p/q within distance one of the compact image g(K),

    g(x)-p/q = [(Aq-Cp)x+(Bq-Dp)]/[q(Cx+D)].

If Aq-Cp is nonzero, its absolute value is at most a constant times q;
the original BA bound applied at denominator |Aq-Cp| yields a lower
bound kappa'/q^2. If Aq-Cp=0, the determinant gives a fixed positive
distance between g(K) and A/C. Rational points farther from g(K) are
trivial. All constants are uniform on K.

Thus rational normalization retains one positive BA constant. Take the
Patterson–Sullivan measure of the normalized group directly; no Fourier
decay is transferred merely from equivalence to another measure.
The later rational affine placement inside (0,1) is also harmless.
This supplies a missing normalization justification if the original
geometric presentation was obtained only up to real conjugacy.

## 7. Falsification audit

The [checker](../../../../workflows/experiments/sparse_fourier_length24_20261016/audit.py)
uses only the Python standard library and writes no files. Run
`python3 workflows/experiments/sparse_fourier_length24_20261016/audit.py`.

The completed run checked all binary words of lengths 2–8, all ternary
words of lengths 2–5, and all decimal words of lengths 2 and 3:
1,968 words; 1,163,796 exact suffix-vector identities; 4,013,758 exact
incoming-state survival and terminal-state comparisons. It checked 18,812
exact first-occurrence/autocorrelation identities against independent
automaton counts. It also checked the three weighted-term identities for
2<=m<=99, the exact spectral comparison in (7), the small-integer
certificates for (11)–(12), and log(10)<7/3 using a positive Taylor
partial sum for exp(7/3).

Forty-two shifted Dirichlet samples passed. Those samples are floating
point and are only experiments; the analytic proof of (1) supplies the
universal shift bound. None of these finite checks verifies the infinite
Hausdorff-dimension or complete-cylinder Fourier assertion in Lean.

