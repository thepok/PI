# Critical-shell laws: iid failures and a normal separator

Claim status: `proof sketch`. Date: 2026-09-05.
The critical-shell schedule admits infinitely many empty and successful shells
almost surely under iid decimal digits, for each orientation. A decimal-normal
number can nevertheless fail both margin tests in every shell.
Neither statement proves or disproves M5CS0/M5CS9 for pi, CW0, CW9, or V1.

This is a compact, independently reviewed consequence of a Pro-assisted
investigation. It is not machine-checked, carries no novelty claim, and is not
an unformalized paper theorem. The elementary arguments below suffice; more
detailed proposed compound-Poisson asymptotics are not needed or retained here.

## Exact schedule

Use the exact width and tests of the
[cycle-2 source](20260904-pro-conjecture-mining-cycle2.md). Put

```
t = 4m+3, M_e = 5^e, a = log_10(3), ell = log_10(5),
W_m = 8/(t 3^t) + 4/(t 7^t),
H(t) = log_10(1/W_m), k_e = floor(e ell),
S_e = {m : M_e <= 4m+3 < 5 M_e},
n_(e,m) = floor(H(4m+3)) - k_e - 1,
r_e = 10^(-k_e), c_m = 10^(-1-fract(H(4m+3))).
```

Here e >= 4, |S_e| = M_e, 1 <= M_e r_e < 10, and
0.01 < c_m <= 0.1. A zero hit for a real x is
`c_m r_e < fract(10^n x) < (1-c_m) r_e`; the nine target is its
reflection about 1/2. Let Z_e^d(x) count hits for d in {0,9}.

Factoring W gives
`H(t)=a t+log_10(t)-log_10(8)-epsilon(t)`, where
`epsilon(t)=log_10(1+(3/7)^t/2)` is positive and decreasing. Direct bounds
for t >= 627 give `a t-3 < n_(e,m) < a t` and

```
1 < H(t+4)-H(t)
  = 4a + log_10(1+4/t) + epsilon(t)-epsilon(t+4) < 2.
```

Thus candidate starts are distinct, with increments 1 or 2. Their range in
shell e runs from `a 5^e+O(1)` to `a 5^(e+1)+O(1)`, while k_e=O(e).
Consequently finite tests of length k_e+1 in shells of one fixed parity
depend on disjoint digit blocks for all sufficiently large e. Adjacent
shells need not be independent.

## Infinitely many empty shells under iid digits

Fix d in {0,9}. At each candidate start consider the bare prescribed word
`d^k_e`. Its probability is r_e. The event that it is absent is decreasing
in the independent Bernoulli coordinates `1_{digit=d}`. Positive association
of decreasing events therefore gives

```
P(no bare d^k_e at any scheduled start)
  >= (1-r_e)^M_e
  >= exp(-M_e r_e/(1-r_e))
  >= exp(-1000/99) > 0.
```

We used k_e >= 2, hence r_e <= 0.01. For completeness, positive association
here follows by induction on the number of independent binary coordinates:
conditional covariance is nonnegative by induction, and the covariance of
the two conditional means is nonnegative because both means are monotone in
the final binary coordinate. Applying the two-function inequality repeatedly
to indicator products proves the displayed product bound. No independence of
overlapping word events is assumed.

Bare-word absence implies Z_e^d=0. Along a sufficiently late fixed parity of
shells the bare-absence events are independent, with a uniform positive
probability. The probability that none occurs after any specified shell is
zero, by the bound `(1-c)^j -> 0`. Taking the countable union over onsets
proves infinitely many empty shells almost surely.

## Infinitely many successful shells under iid digits

At each candidate start use the finite sufficient pattern `d^k_e 5`. The
tail after the constant word lies in [0.5,0.6), strictly within every margin
because c_m <= 0.1. Let Y_e count these patterns. Its mean satisfies
`mu_e=M_e r_e/10` and `0.1 <= mu_e < 1`.

For two distinct starts whose length-(k_e+1) windows overlap, these patterns
are incompatible: the earlier terminal 5 would have to be a d in the later
constant block. For disjoint windows the events are independent. Therefore
`Var(Y_e) <= mu_e` and Cauchy-Schwarz gives

```
P(Y_e > 0) >= (E Y_e)^2/E(Y_e^2)
           >= mu_e/(1+mu_e) >= 1/11.
```

Again the finite tests are independent along a sufficiently late fixed
parity of shells. Thus infinitely many successful shells occur almost surely.
Intersecting the four probability-one conclusions gives infinitely many
empty and successful shells for each of d=0 and d=9, jointly almost surely.
This does not assert simultaneous emptiness or success in the same shell.
In particular, each every-shell law has probability zero, even if its onset
is allowed to be any finite integer.

## A normal number with no successful shell

Start with any decimal-normal digit sequence. For each e >= 4 define
`s_e^- = min_m(n_(e,m)+1)` and `s_e^+ = max_m(n_(e,m)+1)`.
Replace by 5 every digit at a position j satisfying

```
s_e^- <= j <= s_e^+ + k_e - 1,    j = 0 mod k_e.
```

Every scheduled length-k_e window contains such a forced 5. All zero and
nine margin tests therefore fail, in every shell. These edits are compatible
where shells overlap because all write the same digit.

Shell e contributes O(5^e/e) edited positions. The geometric growth of the
shell ranges gives O(N/log N)=o(N) edited positions among the first N digits,
including partial shells. For each fixed word length q, the change in its
occurrence count through N is at most q times the number of edits through
N+q. This is o(N), so every fixed-word limiting frequency is preserved and
the resulting number is still normal.

The construction can begin with any fixed finite prefix, followed by a
normal continuation; only sufficiently late shells are then edited if that
prefix must be preserved. The all-shell version above does not promise to
preserve an arbitrary prescribed prefix.

## Consequence for the pi conjectures

M5CS0/M5CS9 remain `conjecture`, not disproved: pi has not been shown to
satisfy the iid model, and no probability-one statement singles it out.
Normality, even if proved for pi, would not alone imply the every-shell or
unbounded-success laws for this schedule. The normal separator does not
satisfy the exact Machin identities characterizing pi.
Unbounded successful shells would still suffice for the corresponding CW0
or CW9 milestone because k_e tends to infinity. Establishing them for pi
requires actual oriented numerator information; neither the null-model
calculation nor the denominator valuation law supplies it.
