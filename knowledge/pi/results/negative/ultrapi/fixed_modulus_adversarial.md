# Adversarial audit of the fixed-modulus Machin separator

Audit date: **2026-08-12 UTC**  
Artifact audited: [`fixed_modulus_attack.md`](fixed_modulus_attack.md)  
Artifact SHA-256 at audit: `2cc89a692b291894257ec6b90c7aa6c38a0d65cc27c100f062774a67b0c4a699`  
Experiment script SHA-256: `e9e006d3f92881be9b144551a6183f89a4ced0db7d1ed355bf838e9464706906`

## Finding

The separator is a sound `proof sketch`. I found no counterexample or fatal
gap in the exact seed indexing, upper-half prime survival, CRT reduction,
Jacobsthal step, decimal-cylinder argument, or asymptotic constants. It does
not constrain the actual Machin numerator's complementary component and
therefore does not prove V1; the report states that scope correctly.

Two amendments should be made before treating the note as a clean research
handoff:

1. replace the vague endpoint sentence by the exact argument below; and
2. correct the finite-audit bullet that says the script checks recurrence
   (3), because the script constructs the reverse quantities directly but
   does not compare successive quantities using (3).

There is also one important wording restriction: “every T45 fresh-prime
component” in this note means only the at-most-three primes in
\(\mathcal F_N\) born from \(\Delta_N\). It does not mean all older T45
primes whose pulses overlap the seed. The latter stronger freezing statement
belongs to [`multiprime_pulse_attack.md`](multiprime_pulse_attack.md) and is
also only a `proof sketch`.

## Exact arithmetic checks

### Seed and endpoints

With \(n=N+1\), `machinLowerRat (3*n)` contains

- base-5 indices \(0\le j\le6n+1\), hence final odd exponent
  \(12n+3=d\); and
- base-239 indices \(0\le j\le6n+2\), hence final exponent \(d+2\).

Thus equations (1) and (2), including the sign of the lone
\(-4/((d+2)239^{d+2})\) term, have the correct indices. The reverse-sum
identity is also exact:

\[
 R_q(m)=1-q^2\frac{2m+1}{2m-1}R_q(m-1).
\]

Here \(R_q(m)\) is generally rational; the valuation formulas correctly use
rational valuations.

### Upper-half uniqueness and noncancellation

Let \(d=12n+3\), \(n\ge1\), and let \(d/2<\ell\le d\) be prime with
\(\ell\notin\{239,317\}\). Then \(\ell\) is odd and exceeds 5. Among the
common odd linear denominators \(u\le d\), only \(u=\ell\) is divisible by
\(\ell\). The extra endpoint cannot introduce a second singular term:

- \(d+2<3\ell\), since \(d\ge15\) and \(\ell>d/2\);
- \(d+2\ne\ell\), since \(d+2>d\ge\ell\); and
- \(d+2\ne2\ell\), since \(d+2\) is odd.

Therefore \(\ell\nmid d+2\) for **every** relevant \(n\), with no finite
exception check needed. This should replace “for all sufficiently large
\(d\)” in the audited note.

After multiplying the unique singular pair by \(\ell\), Fermat gives

\[
 4(-1)^{(\ell-1)/2}
 \frac{4\,239^\ell-5^\ell}{5^\ell239^\ell}
 \equiv
 4(-1)^{(\ell-1)/2}\frac{951}{5\cdot239}\not\equiv0\pmod\ell.
\]

The exclusions are exact because \(951=3\cdot317\), while all other terms
are \(\ell\)-integral. Multiplication by \(10^n\) is a unit at \(\ell\).
Hence the unequal-valuation sum gives
\(v_\ell(Y_N)=-1\), so \(\ell\) occurs exactly once in the reduced
denominator. No ordinary cancellation argument is being substituted for the
needed nonarchimedean one.

### Controlled factor

For \(p\in\mathcal F_N\), the preceding sample \(y_N\) has all of its odd
linear denominator factors below \(p\); also \(p\notin\{2,5,239\}\).
Therefore it is \(p\)-integral. T45's `machine-checked` statement
\(v_p(\Delta_N)=-1\), applied to
\(Y_N=y_{N+1}=10y_N+\Delta_N\), gives \(v_p(Y_N)=-1\) at `proof sketch`
status. Consequently every such \(p\) occurs once in \(Q_N\).

Since \(s_N=v_5(Q_N)\) and \(r_N=v_{239}(Q_N)\) are the *full* exponents,
and the fresh primes are distinct from 5 and 239 and occur to exponent one,

\[
 F_N=5^{s_N}239^{r_N}\prod_{p\in\mathcal F_N}p,
 \qquad D_N=Q_N/F_N
\]

is an integer factorization with \(\gcd(F_N,D_N)=1\). The conjectural
closed formulas (6) for \(s_N,r_N\) are not used.

## Jacobsthal and CRT audit

Kanold's primary paper defines \(g(m)\) as the least length for which every
run of consecutive integers contains an integer coprime to \(m\), notes that
one may pass to squarefree arguments, and proves in Satz 4 (printed p. 324)

\[
 g(m)\le2^k\quad\text{when }k=\omega(m).
\]

Primary scan:
[Kanold, *Über eine zahlentheoretische Funktion von Jacobsthal*](https://gdz.sub.uni-goettingen.de/download/pdf/PPN235181684_0170/LOG_0054.pdf),
SHA-256 `dd75cd1ff949feff49b0e7ca9ca2379518e8f65e075ee99a7df4f247c80c97cb`.
This supports (15). For maximum precision, the note should state explicitly
that \(g(D)=g(\operatorname{rad}D)\), since coprimality depends only on the
prime support.

The note's progression version is equivalent to Kanold's consecutive
version. Indeed, for

\[
 a_j=a_N+F_Nj\pmod{Q_N},\qquad Q_N=F_ND_N,
\]

multiplication modulo \(D_N\) by the unit \(F_N^{-1}\) sends the index run to
the consecutive residues \(F_N^{-1}a_N+j\). Coprimality is periodic modulo
\(D_N\), so the same bound applies across the cyclic wrap. Also
\(a_j\equiv a_N\pmod{F_N}\), and reducedness of \(a_N/Q_N\) implies
\(\gcd(a_j,F_N)=1\). The selected fractions are therefore reduced and have
cyclic gaps at most \(g(D_N)/D_N\).

## Asymptotic and cylinder audit

Upper-half survivors outside 239, 317, and the at-most-three members of
\(\mathcal F_N\) give

\[
 \log D_N\ge\vartheta(d)-\vartheta(d/2)-O(\log d)
             =d/2+o(d)=6N+o(N).
\]

Every denominator prime is among 5, 239, or the primes dividing an odd
linear denominator at most \(d+2\), so
\(\omega(D_N)\le\pi(d+2)=o(d)\). Thus

\[
 \log\frac{D_N}{2^{\omega(D_N)}}\ge6N+o(N).
\]

For \(L_N=2N+2\), the required grid scale has logarithm
\(L_N\log10=2N\log10+O(1)\). The strict numerical margin is genuine:
\(6-2\log10\approx1.39483>0\). The cited unconditional bounds for
\(\vartheta(x)-x\) are more than sufficient for this PNT input.

If the maximum cyclic gap is strictly below \(10^{-L_N}\), every half-open
base-ten cylinder of that length contains a selected reduced fraction. In
the all-5 cylinder, multiplication by \(10^t\) shifts the prescribed prefix,
so

\[
 \{10^t a'_N/Q_N\}\in[0.5,0.6),\qquad0\le t<L_N.
\]

Projection onto the direction \(e(0.55)\) then gives the claimed lower
bound \(L_N\cos(\pi/10)\). The strict mesh inequality avoids any ambiguity
at the right cylinder endpoint; the left endpoint has the intended
terminating decimal expansion.

## Experiment audit and requested amendments

The script uses exact `Fraction` arithmetic and has the correct loop bounds,
fresh-prime indices, upper-half test, cofactor support bound, and sufficient
inequality. Its retained SHA-256 matches the report. The computation remains
an `experiment` and was not used to justify the asymptotic proof.
An independent rerun of `--max-n 300` during this audit reproduced all 300
rows, zero failures, and the stated first and last summaries.

Amend the Section 5 checklist as follows:

- change “both reverse recurrences and the component equalities (6)” to
  “both directly constructed reverse quantities and the component
  equalities (6)”; alternatively add an explicit successive-recurrence
  assertion to the script;
- say explicitly that the script checks the **sufficient inequality**, not
  construction of the avoiding numerator or its digits; and
- retain the existing qualification that finite success has no proof force.

Amend the opening and interpretation paragraphs to say “all primes in the
at-most-three-element set \(\mathcal F_N\)” wherever “every T45 fresh-prime
component” could be read as including overlapping pulses from older forcing
indices. Also say “the fractional part has an all-5 prefix” rather than
speaking loosely of the large rational seed's first digits.

## Smallest valuable formal theorem next

The next compact formal target is the full-seed upper-half survival lemma:

> For \(n\ge1\), prime \(\ell\) with
> \(2\ell>12n+3\), \(\ell\le12n+3\), and
> \(\ell\notin\{239,317\}\), prove
> \[
> \operatorname{padicValRat}_\ell
>   (\operatorname{sampledMachinValueRat}(n))=-1.
> \]

This isolates the only route-specific unformalized arithmetic input behind
the exponential cofactor bound. It should be split into (i) endpoint
nondivisibility, (ii) the shared-term residue \(951\), (iii) integrality of
the remaining finite sums, and (iv) the unequal-valuation conclusion. The
PNT and Kanold layers can remain a separately sourced `proof sketch` until
this exact local theorem is `machine-checked`.
