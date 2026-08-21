# T88: Bernoulli Measure Audit Against the Literal T67 Statistics

Claim label: **proof sketch**. This is a source-pinned rigorous prose note with
a deterministic replay, not a Lean theorem. The T55, T61, and T67 files quoted
below are byte-exact copies of previously kernel-checked library inputs; this
note makes no new machine-checked claim.

## 1. Scope and immutable statement

1. The vendored `canonical_statement.txt` has SHA-256
   `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`,
   matching the required immutable file.
2. The canonical question concerns the one fixed orbit of `pi`, strict circle
   distance, ordered pairs including the diagonal, and the quantifiers
   `for every A, eventually every n, there exists N=N(A,n)`.
3. The construction below instead chooses an artificial non-Lebesgue
   invariant probability measure and a generic point for it. It is therefore
   an A13/A14 sibling test. It proves no estimate for `Q_pi`, C1, C2,
   normality of pi, or any other property of pi.

## 2. Pinned external theorems and substitutions

4. Cuny--Eisner--Farkas, *Wiener's lemma along primes and other
   subsequences*, Advances in Mathematics 347 (2019), 340--383,
   DOI `10.1016/j.aim.2019.02.005`, states at Theorem 1.1 (published page
   340; author-version printed page 1; extracted text lines 41--52) that for a
   finite complex Borel measure `mu` on the circle,

   ```text
   lim_(H->infinity) (1/H) sum_(h=1)^H |mu_hat(h)|^2
     = sum_(a an atom) |mu({a})|^2.
   ```

   Its parenthetical sentence permits the symmetric normalization
   `(2H+1)^(-1) sum_(-H)^H`. We use the displayed positive-frequency version
   exactly. The vendored source is author version arXiv:1701.00101v6; it is a
   post-publication revision and records an unrelated gap in a page-13 return
   times example. Theorem 1.1 itself is present verbatim at the locator above.
5. Birkhoff, *Proof of the Ergodic Theorem*, PNAS 17 (1931), 656--660,
   DOI recorded by PMC/Crossref as `10.1073/pnas.17.2.656` (the issue is 12),
   proves almost-everywhere existence of time frequencies. Page 656, formula
   (1), states the almost-everywhere limit of crossing-time frequencies;
   pages 659--660 pass to time spent in a measurable region, and page 660
   states that the resulting time-probability exists for almost every moving
   point and that the abstract lemma extends to function space under suitable
   restrictions.
6. Because the 1931 paper is written for an invertible differential flow, the
   exact modern statement used here is separately pinned. Hagelstein--Herden--
   Stokolos, arXiv:1910.09054v1, Theorem 2 on printed page 3, states almost-
   everywhere convergence of the averages `n^(-1) sum_(k<n) f(T^k x)` for an
   invertible measure-preserving transformation of a standard probability
   space whenever its ergodic maximal function is finite; lines immediately
   after the theorem note that integrability gives this by Birkhoff. Apply it
   to the invertible two-sided iid Bernoulli shift `D^Z`, for which the real and
   imaginary parts of every character pulled back through the future-decimal
   factor are bounded and hence have finite maximal function. The shift is
   ergodic. The almost-everywhere limit is invariant, hence constant; bounded
   convergence and invariance of the measure identify that constant with the
   integral. Projecting a two-sided point to its future coordinates supplies a
   point for the one-sided decimal orbit below. Applying this to the countable
   family `f_h(x)=exp(2*pi*i*h*x)` and intersecting their full-measure sets
   gives one point on which every fixed integer frequency converges. Density
   of trigonometric polynomials in the continuous circle functions then makes
   that point generic for `mu`. Thus neither a noninvertible extension of the
   cited theorem, an uncountable intersection, nor a generic point is assumed.
7. The original PNAS scan is image-only in the available PMC interface. The
   five vendored PNG files are the exact official PMC page scans 656--660 and
   were visually checked. The direct PNAS and PMC PDF endpoints returned HTTP
   403 or a 1,817-byte anti-bot HTML response in this sandbox; no fake PDF is
   presented as a source.

## 3. The explicit Bernoulli circle measure

8. Let `D={0,...,9}` and set

   ```text
   p_0 = 2/11,       p_d = 1/11 for 1 <= d <= 9.
   ```

   Let `Omega=D^N`, let `P` be the iid product probability with digit law
   `p`, let `sigma` be the left shift, and define

   ```text
   q(omega) = sum_(n>=1) omega_n / 10^n mod 1,
   T(x) = 10*x mod 1,
   mu = q_* P.
   ```

9. **Full support.** Every finite digit cylinder `[a_1...a_m]` has mass
   `product_(j<=m) p_(a_j)>0`. Decimal intervals of arbitrarily small length
   occur inside every nonempty circle arc. Such an interval contains the image
   of a finite cylinder, up to endpoints, so every nonempty open arc has
   positive `mu`-mass. Hence `supp(mu)` is the whole circle.
10. **Atomless.** A single sequence has product mass at most
    `(2/11)^m` after its first `m` coordinates are fixed, which tends to zero.
    Every circle point has at most two decimal codings (including the
    terminating/recurring-9 ambiguity). Therefore its inverse image under `q`
    is the union of at most two null singletons, and `mu({x})=0`.
11. **Non-Lebesgue.** Apart from the null ambiguous endpoint coding,
    `q^(-1)([0,1/10))` is the first-digit-0 cylinder. Consequently
    `mu([0,1/10))=2/11`, whereas Lebesgue measure gives `1/10`.
12. **Times-10 invariant.** The identity `q(sigma omega)=T(q(omega))` holds
    modulo one even at ambiguous decimal expansions. Since `sigma_*P=P`,
    `T_*mu=T_*q_*P=q_*sigma_*P=mu`.
13. **Ergodic.** Cylinder events separated by more than their lengths are
    independent, so the iid one-sided Bernoulli shift is mixing first on the
    cylinder algebra and then, by the monotone-class approximation, on all
    measurable sets. It is therefore ergodic. A measurable factor of an
    ergodic system is ergodic: the inverse image under `q` of a `T`-invariant
    set is `sigma`-invariant. Thus `(circle,mu,T)` is ergodic.

## 4. A nonzero persistent Fourier ray

14. Use `e(t)=exp(2*pi*i*t)` and the positive convention
    `mu_hat(h)=integral e(hx) dmu(x)`. Put

    ```text
    Phi(t) = sum_(d=0)^9 p_d e(d*t).
    ```

    Independence and bounded convergence for the decimal partial sums give

    ```text
    c := mu_hat(1) = product_(n>=1) Phi(10^(-n)).                 (4.1)
    ```

15. Every factor in (4.1) is nonzero. With `z=e(t)`, the numerator is
    `P(z)=2+z+...+z^9=1+sum_(d=0)^9 z^d`. If `|z|=1`, `z!=1`, and `P(z)=0`,
    multiplication by `1-z` gives `2=z+z^10`. Equality in the triangle
    inequality forces `z=z^10=1`, a contradiction. At `z=1`, `P(1)=11`.
16. The product is nonzero, not merely termwise nonzero. Indeed,

    ```text
    |Phi(10^(-n))-1|
      <= 2*pi*(sum_d p_d*d)*10^(-n)
      = (90*pi/11)*10^(-n),
    ```

    whose sum converges. The standard nonzero infinite-product criterion
    applies to the nonzero tail factors. The finitely many initial factors are
    nonzero by step 15. In particular the first factor is exactly
    `Phi(1/10)=1/11`, because the ten tenth roots sum to zero. Hence `c!=0`.
17. Invariance supplies the whole ray without an additional hypothesis:

    ```text
    mu_hat(10*h) = integral e(h*T(x)) dmu(x) = mu_hat(h),
    mu_hat(10^r) = c != 0 for every r >= 0.                    (4.2)
    ```

## 5. Literal T67 cutoffs, weights, rays, and bulk statistics

18. The following statements are read from the vendored kernel-checked source,
    not from an unverified prose predecessor.
19. `T67TerminalRayStrength.lean:53-61` defines

    ```text
    A_N(h,beta) = N^(-1) sum_(j=0)^(N-1) e(h*10^j*beta),
    d_(beta,N)(m) = A_N(10*m,beta)-A_N(m,beta).
    ```

    Its endpoint theorem at lines 90--132 assumes `1<=N` and retains both
    endpoints:

    ```text
    N*d_(beta,N)(m) = e(10^N*m*beta)-e(m*beta).                (5.1)
    ```

20. `T67TerminalRayStrength.lean:138-155` defines primitive bases by
    `1<=v<=H` and `not (10 divides v)`, not by coprimality. Its ray shell is

    ```text
    H/10 < u <= H,       u=10^a*v for some a>=0.              (5.2)
    ```

    The ray-shell definition itself does not impose primitivity; `v` must also
    be chosen from `primitiveDecimalBases H`.
21. `T55SignedMultiplierTenPairing.lean:187-188,229-230` defines

    ```text
    w_R(u)=1-u/R,
    terminalShell(R)=Ioc((R-1)/10,R-1).
    ```

    T67 lines 157--160 prove that at `R=H+1` this is exactly `(H/10,H]`.
22. For an unconstrained cutoff array `a:{1,...,H}->C`, T67 lines 497--509
    define the unweighted terminal mean square and the full positive-cutoff
    triangular mean square

    ```text
    U_H(a) = (1/|terminalShell(H+1)|)
             sum_(u in terminalShell(H+1)) |a(u)|^2,

    B_H(a) = [sum_(u=1)^H w_(H+1)(u)|a(u)|^2]
             /[sum_(u=1)^H w_(H+1)(u)].                       (5.3)
    ```

    Lines 522--525 prove the exact denominator
    `sum_(u=1)^H w_(H+1)(u)=H/2`.
23. T67's named exact separator theorems at lines 581--645 have the literal
    quantifier order `for every H, if 1<=H and not (10 divides H)`, then apply
    to the special array which is one at the top frequency `H` and zero
    elsewhere. They conclude exact values
    `U_H=1/(H-H/10)` and `B_H=2/(H(H+1))`. They assert neither realizability by
    a measure nor realizability by an orbit.
24. Apply Cuny--Eisner--Farkas Theorem 1.1 to the atomless `mu`. It gives

    ```text
    (1/H) sum_(h=1)^H |mu_hat(h)|^2 -> 0.                     (5.4)
    ```

    Since `0<=w_(H+1)(h)<=1`, the exact denominator in step 22 gives

    ```text
    0 <= B_H(mu_hat) <= (2/H) sum_(h=1)^H |mu_hat(h)|^2 -> 0. (5.5)
    ```

    The terminal shell has `H-H/10` elements and that quantity is at least
    `9H/10`; hence (5.4) also gives `U_H(mu_hat)->0`.
25. For `r>=1`, choose the actual schedule

    ```text
    H_r=2*10^r+1,       R_r=H_r+1,       u_r=10^r.            (5.6)
    ```

    Then `10` does not divide `H_r`. The base `v=1` satisfies every clause of
    `primitiveDecimalBases H_r`: `1<=1`, `1<=H_r`, and `10` does not divide
    `1`. The frequency `u_r` satisfies every ray-shell clause:
    `H_r/10=2*10^(r-1)<u_r<=H_r` and `u_r=10^r*1`. Its exact T55 weight is

    ```text
    w_(R_r)(u_r)=1-10^r/(2*10^r+2)
                 =(10^r+2)/(2*10^r+2) > 1/2.                (5.7)
    ```

    Equations (4.2), (5.5), and step 24 now give a measure-realizable
    same-functional separator:

    ```text
    U_(H_r)(mu_hat)->0,  B_(H_r)(mu_hat)->0,
    sup_(u in terminalShell(R_r)) |mu_hat(u)| >= |c| > 0.     (5.8)
    ```

    This is not T67's special top-spike array: the witness is `u_r`, not `H_r`,
    and other coefficients need not vanish. It does instantiate the literal
    functionals (5.3) because T67's cutoff-array type accepts any complex
    array on `{1,...,H}`.

## 6. Birkhoff transfer and the 2r/J bound

26. Fix one Birkhoff-generic point `x` supplied by step 6 and write

    ```text
    A_J(h,x)=J^(-1) sum_(j=0)^(J-1) e(h*10^j*x),    J>=1.
    ```

    For every fixed integer `h`, `A_J(h,x)->mu_hat(h)`.
27. For every `J>=1`, `r>=0`, and every `x`, shifting indices gives

    ```text
    A_J(10^r,x)=J^(-1) sum_(k=r)^(J+r-1) e(10^k*x).
    ```

    Subtract the range `0<=k<J`. The identity between the two interval sums
    leaves a terminal block of `r` terms minus an initial block of `r` terms,
    even when `r>J`. Every term has modulus one, so

    ```text
    |A_J(10^r,x)-A_J(1,x)| <= 2r/J.                           (6.1)
    ```

28. No growing-frequency Birkhoff theorem is assumed. For each `r>=1`, fixed
    frequency convergence on the finite set `1<=h<=H_r` supplies an integer
    `N_r(x)` such that

    ```text
    J>=N_r(x), 1<=h<=H_r  implies
    |A_J(h,x)-mu_hat(h)| <= 1/r.                              (6.2)
    ```

    Recursively define the strictly increasing, generally ineffective schedule

    ```text
    J_r=max(J_(r-1)+1, N_r(x), r^2),                          (6.3)
    ```

    beginning with `J_0=0`. This derives one joint diagonal after choosing
    `x`; it does not assume genericity uniformly in growing `h`.
29. Since both empirical and measure Fourier coefficients have modulus at most
    one, (6.2) implies

    ```text
    ||A_(J_r)(h,x)|^2-|mu_hat(h)|^2| <= 2/r
    ```

    simultaneously through the cutoff. Averaging with either normalized
    functional in (5.3), and using (5.8), yields

    ```text
    U_(H_r)(A_(J_r))->0,       B_(H_r)(A_(J_r))->0.           (6.4)
    ```

30. The requested finite-orbit ray transfer uses (6.1), not (6.2) at the
    moving frequency:

    ```text
    |A_(J_r)(10^r,x)-c|
      <= 2r/J_r + |A_(J_r)(1,x)-c|
      <= 3/r -> 0.                                           (6.5)
    ```

    Thus the shell supremum in (6.4) is eventually at least `|c|/2`. The
    result is a genuine existential joint schedule

    ```text
    there exists x, there exists strictly increasing J_r:
      bulk_(H_r,J_r)->0 and shellSup_(H_r,J_r) not->0,
    ```

    not only `lim_H lim_J`. Neither `x` nor `J_r` is prescribed or effective.

## 7. Clause-complete comparison with qualified UPRID

31. The separator just proved concerns Fourier coefficient magnitudes in the
    two literal T67 cutoff functionals. T67 also contains a distinct
    chain-indexed predicate, `T61QualifiedUPRID`, which must not be merged with
    that separator.
32. `T61DirectLabelAdjacentPhaseVariance.lean:35-36,57-58` defines the labeled
    frequencies and mass

    ```text
    m_(u,j)=u*(10^ell-10^j),
    A_0=sum_(u in terminalShell(R)) sum_(j<ell) w_R(u).
    ```

    Labels are retained even when numerical frequencies collide.
33. `T67TerminalRayStrength.lean:167-175` defines the exact margin

    ```text
    Lambda = ell + 2*A_0
             - 2*predecessorRemainderBudget(beta_(k+1),ell,R)
             - 2*endpointBudget(beta_(k+1),ell,R)
             - ell/(4*R*delta^2).                             (7.1)
    ```

    This is the exact T61 remainder, not the valuation-expanded quantity from
    the unverified T60 note.
34. For already supplied `chain,k,ell,R,delta`, T67 lines 181--192 have the
    literal quantifier order

    ```text
    exists eta, 0<=eta and A_0*eta^2 < Lambda and
      for every u in terminalShell(R), for every j in range(ell),
        s*|d_(beta_k,s)(m_(u,j))| <= eta,                     (7.2)
    ```

    where `s=incomingShift(chain,k)`. T67 lines 227--284 then quantify over
    `chain,k,ell,R,delta`, assume `1<=R`, `1<=s`, and (7.2), and conclude the
    strict threshold

    ```text
    ell/(4*R*delta^2)
      < sum_(j<ell) fejerKernel(R-1,
          beta_(k+1)*(10^ell-10^j)).                          (7.3)
    ```

    This retains `R-1`, every label `j<ell`, the adjacent coefficient `k+1`,
    all predecessor and endpoint budgets, and strict `<`.
35. The Bernoulli argument does **not** prove (7.2) or (7.3). Its persistent
    coefficients concern `1` and `10^r`, not all moving `m_(u,j)`. Equation
    (5.1) only gives the universal scaled estimate

    ```text
    s*|d_(beta,s)(m)| <= 2,
    ```

    with no reason for it to fit the strict budget `A_0*eta^2<Lambda`.
    Wiener gives an average of coefficient magnitudes, not a simultaneous
    chain-dependent bound on scaled invariance defects. Genericity gives no
    `o(1/s)` endpoint rate. Finally, the constructed generic point is not shown
    to equal any `chain.nodeCoefficient(k)`.
36. Therefore the proved separator repairs only this precise boundary:
    cardinality- or triangularly-normalized Fourier bulk decay does not control
    the terminal-shell supremum, even for actual empirical decimal orbits along
    one derived diagonal. It neither supplies nor refutes qualified UPRID and
    does not trigger T67's strict Fejer conclusion.

## 8. Remaining limitations

37. This is a `proof sketch`, not a new machine-checked theorem.
38. The source-pinned Birkhoff invocation is qualitative. The schedule `J_r`
    depends on the selected generic point and has no effective growth bound.
39. No assertion is made for every schedule `H(J)`, for `J_r` comparable with
    `H_r`, or for all generic points with one common schedule.
40. The named exact T67 top-spike theorem is not instantiated; only its literal
    cutoff functionals are instantiated by actual Fourier arrays.
41. Qualified UPRID, its exact margin, canonical chain legality, and the strict
    Fejer threshold remain unproved.
42. No fixed-pi statement, canonical near-return estimate, C1, C2, normality,
    pair correlation, or digit theorem follows.

Scope of terminal verdict: for the artificial Bernoulli factor constructed
above, there exist a point `x` and a strictly increasing schedule `J_r`, with
`H_r=2*10^r+1`, such that the literal T67 terminal-shell and triangular
mean-square functionals of `h |-> A_(J_r)(h,x)` tend to zero while the literal
terminal-shell supremum stays bounded away from zero. This does not instantiate
T67's abstract top-spike theorem, prove `T61QualifiedUPRID` or its strict Fejer
threshold, or assert anything about the fixed orbit of pi.

SEPARATOR PROVED
