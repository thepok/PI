# T47: all injective one-block decimal codings of the Fibonacci word

Status: `proof sketch` (rigorous prose note; not machine-checked)

Scope: **non-pi sibling classification only**. This note makes no claim about
pi, C1, Fourier amplification, or cancellation for the fixed orbit of pi.
The T45 note was motivation only; none of its conclusions is used as a
premise below.

## 1. Provenance and normalized question

- Canonical local problem file:
  `knowledge/pi/statements/pi-positive-decimal-factor-entropy.txt`.
- Original source URL: none; the canonical question was formulated locally.
- Required and verified SHA-256:
  `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`.
- Hash checked: 2026-08-01.
- This is a sibling calculation. The canonical question about pi remains
  open.

Put

```text
phi = (1+sqrt(5))/2,          alpha = 1/phi^2 = (3-sqrt(5))/2.
```

Thus `0<alpha<1`, and `alpha` is irrational. We use the zero-indexed
characteristic Fibonacci word

```text
f_n = floor((n+2)alpha)-floor((n+1)alpha),    n>=0.        (1.1)
```

It begins `010010100100101...`. The next lemma verifies, rather than assumes,
that this is the usual fixed point beginning in `0` of `0 -> 01, 1 -> 0`.
Formula (1.1) then fixes the convention used throughout.

### Lemma 1.1 (mechanical word equals the morphic Fibonacci word)

Let `sigma(0)=01` and `sigma(1)=0`. The word defined by (1.1) satisfies
`sigma(f)=f`; since it begins in `0`, it is the limit of `sigma^k(0)`.

Proof. Telescoping (1.1) shows that the number of `1`s among
`f_0,...,f_n` is `floor((n+2)alpha)`. Consequently the zero-indexed position
of the `k`-th `1`, for `k>=1`, is

```text
p_k = floor(k/alpha)-1 = floor(k phi^2)-1.                 (1.2)
```

Put `beta=1-alpha=1/phi`. Because no positive multiple of `alpha` is an
integer,

```text
1-f_n
 = floor((n+2)beta)-floor((n+1)beta).
```

The same telescoping argument says that the position of the `k`-th `0` in
`f` is

```text
m_k = floor(k/beta)-1 = floor(k phi)-1.                    (1.3)
```

In `sigma(f)`, each input letter contributes one initial `0`, and precisely
the input zeroes contribute a following `1`. Before the image of the `k`-th
zero there are `m_k` input letters and `k-1` earlier zeroes. Its output `1`
is therefore at position

```text
m_k+(k-1)+1
 = floor(k phi)-1+k
 = floor(k(phi+1))-1
 = floor(k phi^2)-1
 = p_k.                                                     (1.4)
```

Thus `sigma(f)` and `f` have exactly the same positions occupied by `1`, so
they are equal. Since `sigma(0)` begins in `0`, every `sigma^k(0)` is a prefix
of the next iterate. The fixed word `f`, which begins in `0`, has each of
these iterates as a prefix by induction, proving the limit assertion. QED.

Let `X` be the closure, in `{0,1}^N` with the product topology, of the suffixes

```text
shift^j(f) = f_j f_(j+1) f_(j+2) ...,    j>=0.
```

For `u in X`, define

```text
V(u) = sum_(n>=0) u_n / 10^(n+1).                         (1.5)
```

For ordered distinct digits `a,b in {0,...,9}`, let `c_(a,b)(0)=a` and
`c_(a,b)(1)=b`, and define its decimal suffix closure

```text
C_(a,b) = { sum_(n>=0) c_(a,b)(u_n)/10^(n+1) : u in X }
          subset R/Z.                                     (1.6)
```

Continuity of the decimal evaluation map and compactness of `X` show that
(1.6) is exactly the closure in the circle of the decimal values of all coded
suffixes. Thus no symbolic/numeric closure interchange is being assumed.

We call the image of a closed real interval of length at most `1/2` a
**closed semicircle**. Endpoints are included.

### Quantifier and convention audit

1. The 90 maps are ordered maps: `(a,b)` and `(b,a)` are different.
2. Injective means exactly `a != b`; leading zeroes are retained.
3. The closure uses every suffix, not only morphism-block boundaries.
4. The topology is the circle topology after decimal evaluation.
5. The assertion is existential separately for each coding: its containing
   semicircle may depend on `(a,b)`.
6. The boundary length `1/2` is allowed; this matters when `|a-b|=5`.

## 2. The classification theorem

### Theorem T47

For every ordered pair of distinct decimal digits `(a,b)`, put
`d=|b-a|`. Then `C_(a,b)` lies in a closed semicircle. More precisely, the
largest component of `(R/Z) \ C_(a,b)` has length

```text
G(d) = max(1-d/10, 9d/100)
     = 1-d/10       for 1<=d<=5,
       9d/100       for 6<=d<=9.                           (2.1)
```

Consequently `G(d)>=1/2` for every `d=1,...,9`. For `d<=5` the ordinary
convex hull of the coded set has length `d/10<=1/2`. For `d>=6`, the
complement of the central vacant interval has length
`1-9d/100<=46/100<1/2` and is a containing closed arc.

There are exactly `2(10-d)` ordered codings with digit gap `d`, so these nine
classes contain all

```text
sum_(d=1)^9 2(10-d) = 90
```

injective one-block codings.

The proof occupies Sections 3-7.

## 3. Irrational-rotation model and lexicographic monotonicity

For `0<=t<1`, define the lower mechanical word

```text
W(t)_n = floor(t+(n+1)alpha)-floor(t+n alpha),    n>=0.    (3.1)
```

Every digit is `0` or `1`. Equation (1.1) says

```text
f = W(alpha).                                               (3.2)
```

Integer parts cancel in (3.1), so

```text
shift^j(f) = W({(j+1)alpha}),                               (3.3)
```

where braces denote fractional part.

We use the elementary irrational-rotation fact that
`{{n alpha}:n>=1}` is dense in `[0,1]`. One short proof is as follows. The
closure in `R/Z` of all integer multiples of `alpha` is a closed subgroup.
A proper closed subgroup of the circle is finite: if it had positive elements
arbitrarily close to zero, their integer multiples would form arbitrarily
fine nets; otherwise its least positive element generates it. Finiteness
would make an integer multiple of `alpha` integral, contradicting
irrationality. The forward orbit has the same closure, since compactness
supplies positive multiples converging to zero and hence approximating the
negative multiples.

### Lemma 3.1 (monotonicity in the intercept)

If `0<=s<t<1`, then

```text
W(s) <_lex W(t).                                            (3.4)
```

Proof. The number of `1`s in the first `m` digits telescopes to

```text
A_m(t) = sum_(n=0)^(m-1) W(t)_n = floor(t+m alpha).         (3.5)
```

For `s<t`, each difference `A_m(t)-A_m(s)` is `0` or `1`. The two infinite
words cannot be equal: density of `{m alpha}` supplies an `m` for which an
integer lies strictly between `s+m alpha` and `t+m alpha`. At the first `m`
where the prefix sums differ, all earlier digit sums agree and the new digit
is `0` for `W(s)` and `1` for `W(t)`. This is (3.4). QED.

For a fixed word `v`, each order interval
`{u:u<=_lex v}` and `{u:v<=_lex u}` is closed in the product topology: its
complement is the union of cylinders whose first difference from `v` has the
wrong sign. Combining this fact, (3.3), density, and Lemma 3.1 reduces all
extremal questions for `X` to one-sided intercept limits. More explicitly,
density supplies orbit intercepts converging from the required side. For each
fixed coordinate the two floors in (3.1) are eventually constant at their
indicated one-sided values. The words therefore converge coordinatewise, and
their limit belongs to the closed set `X`.

## 4. Exact symbolic extrema

Concatenation is denoted without a separator; thus `0f` means a leading `0`
followed by all of `f`.

### Lemma 4.1 (global extrema)

The lexicographically least and greatest elements of `X` are respectively

```text
min X = 0f,              max X = 1f.                        (4.1)
```

Proof. At `t=0`, (3.1) gives `W(0)_0=0`, and for `n>=1`,

```text
W(0)_n = floor((n+1)alpha)-floor(n alpha) = f_(n-1).
```

Hence `W(0)=0f`. As `t` tends to `1` from below, the zeroth digit tends to
`1`. For every `n>=1`, irrationality of `n alpha` and `(n+1)alpha` gives

```text
lim_(t->1-) W(t)_n
 = floor((n+1)alpha)-floor(n alpha)
 = f_(n-1).
```

Thus the right endpoint word is `1f`. Density shows both one-sided limits
belong to `X`, and monotonicity places every suffix, hence every point of its
closure, between them. QED.

### Lemma 4.2 (the two central cylinder extrema)

Among elements of `X` beginning in `0`, the greatest is `01f`. Among elements
beginning in `1`, the least is `10f`:

```text
max {u in X:u_0=0} = 01f,
min {u in X:u_0=1} = 10f.                                  (4.2)
```

Proof. The zeroth digit of `W(t)` is `0` for `t<1-alpha` and `1` for
`t>=1-alpha`. Direct substitution in (3.1) gives the two coordinatewise
limits

```text
lim_(t->(1-alpha)-) W(t) = 01f,
lim_(t->(1-alpha)+) W(t) = 10f.                             (4.3)
```

For completeness, at the left limit the first two digits are `01`; for
`n>=2` the digit is

```text
floor(n alpha)-floor((n-1)alpha)=f_(n-2).
```

At the right limit the first two digits are `10`, followed by the same tail.
Density puts both limits in `X`. Lemma 3.1 makes them the indicated one-sided
extrema. QED.

There is also a useful check not depending on intercept order. If `u=0v` is
in `X`, shift-invariance gives `v in X`, so Lemma 4.1 gives
`u<=0(1f)=01f`. Similarly, `u=1v` implies `u>=1(0f)=10f`.

These four identities include all endpoint claims used below.

## 5. Exact decimal extrema and gaps

Put

```text
xi = V(f).                                                  (5.1)
```

The map `V` is strictly lexicographically increasing on `{0,1}^N`: at the
first differing digit, the leading contribution is `10^(-(m+1))`, whereas
the absolute value of the entire binary tail is at most
`1/(9*10^(m+1))`, which is strictly smaller.

Applying `V` to Lemmas 4.1 and 4.2 gives the exact identities

```text
V(0f)  = xi/10,
V(1f)  = (1+xi)/10,
V(01f) = (1+xi)/100,
V(10f) = (10+xi)/100.                                      (5.2)
```

Therefore

```text
diam V(X) = V(1f)-V(0f) = 1/10,                            (5.3)
V(10f)-V(01f) = 9/100.                                     (5.4)
```

Equation (5.4) is an actual vacant interval, not merely a distance between
two selected points: every binary sequence begins in `0` or `1`, and (4.2)
places the entire zero-cylinder at or below `01f` and the entire one-cylinder
at or above `10f`.

The remaining bounded complementary gaps have length at most `1/100`.
Indeed, two points in the same first-digit cylinder have the form
`epsilon/10+V(v)/10`, with `v in X`; (5.3) bounds that whole cylinder's
diameter by `1/100`. This exhausts the possibilities inside the real convex
hull: a complementary component either separates the zero-cylinder from the
one-cylinder, in which case it is the central gap (5.4), or lies in the convex
hull of one cylinder, in which case its length is at most `1/100`. On the
circle, the only additional component is the exterior gap from the global
maximum back to the global minimum, of length

```text
1-diam V(X) = 9/10                                         (5.5)
```

for the binary set itself. Thus (5.3)-(5.5) identify, with endpoints, every
possible location of a largest circle gap.

## 6. Reduction of all 90 codings to the digit gap

For every `u in X`, summing the coded digits gives the exact affine identity

```text
sum_(n>=0) c_(a,b)(u_n)/10^(n+1)
 = a/9 + (b-a)V(u).                                        (6.1)
```

Let `d=|b-a|`. If `b>a`, (6.1) is translation followed by multiplication by
`d`. If `b<a`, it is the same operation followed by reflection. Translation
and reflection preserve all circle-gap lengths. The real convex hull has
length `d/10<=9/10<1`. Therefore the quotient map to `R/Z` is injective on
this hull: two of its points cannot differ by a nonzero integer. No internal
gaps merge under circle projection; projection adds only the exterior
component joining the real maximum back to the real minimum.

Scaling (5.3)-(5.5) now gives:

1. the exterior circle gap has exact length `1-d/10`;
2. the central cylinder gap has exact length `9d/100`;
3. every other gap has length at most `d/100`.

Because `d/100` is smaller than `9d/100`, the largest gap is exactly

```text
G(d)=max(1-d/10,9d/100).                                   (6.2)
```

This proves the reduction to `d`, including both orientations. Explicitly,
when `b>a`, the central open gap is

```text
( a/9+d(1+xi)/100,  a/9+d(10+xi)/100 ),                    (6.3)
```

and when `b<a`, it is

```text
( a/9-d(10+xi)/100,  a/9-d(1+xi)/100 ).                    (6.4)
```

The endpoints belong to the coded closure by Lemma 4.2.

For a fixed `d`, choose the smaller digit in `10-d` ways and choose which of
`0,1` receives it in two ways. Hence there are `2(10-d)` ordered codings.

## 7. Semicircle criterion and complete boundary table

For a nonempty compact subset of the circle, a complementary open arc of
length at least `1/2` is equivalent to containment in the complementary
closed arc of length at most `1/2`. This is endpoint-safe: equality gives a
closed semicircle containing both boundary points.

The exact comparison

```text
1-d/10 >= 9d/100  iff  100>=19d
```

selects the exterior gap for integer `d<=5` and the central gap for integer
`d>=6`. All cases are displayed here.

| `d` | ordered codings `2(10-d)` | exterior gap `1-d/10` | central gap `9d/100` | chosen containing closed-arc length |
|---:|---:|---:|---:|---:|
| 1 | 18 | `0.90` | `0.09` | `0.10` |
| 2 | 16 | `0.80` | `0.18` | `0.20` |
| 3 | 14 | `0.70` | `0.27` | `0.30` |
| 4 | 12 | `0.60` | `0.36` | `0.40` |
| 5 | 10 | `0.50` | `0.45` | `0.50` |
| 6 | 8  | `0.40` | `0.54` | `0.46` |
| 7 | 6  | `0.30` | `0.63` | `0.37` |
| 8 | 4  | `0.20` | `0.72` | `0.28` |
| 9 | 2  | `0.10` | `0.81` | `0.19` |

For `d<=5`, the containing arc is simply the real interval between the coded
global minimum and maximum; its length is `d/10`. At the boundary `d=5`, it
has length exactly `1/2`, which is permitted because the target is a
**closed** semicircle.

For `d>=6`, delete the central open gap (6.3) or (6.4); its complementary
closed arc contains the entire coded set and has length `1-9d/100`. At the
first case `d=6`, the vacant gap is already `0.54`, leaving a closed arc of
length `0.46`. There is no unexamined integer gap between the two mechanisms.

The multiplicities sum to

```text
18+16+14+12+10+8+6+4+2 = 90.
```

This completes the universal closed-semicircle classification.

## 8. Scope and review status

What has been established in this note is an exact classification of a
Fibonacci-word sibling family. It shows that no injective context-free coding
of the two letters by two single decimal digits escapes closed-semicircle
geometry. It does **not** show that every two-symbol or every morphic decimal
construction has this property: longer blocks, three or more output digits,
and context-dependent codings are outside the theorem.

The proof is elementary once the mechanical convention (1.1) is fixed. No
finite computation is used as evidence, and no claim from the unverified T45
note is imported. Independent skeptical review is still required; this note
is not a `candidate resolution` or a `verified resolution`.
