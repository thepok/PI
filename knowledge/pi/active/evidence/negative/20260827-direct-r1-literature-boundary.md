# Direct R1 literature boundary

Claim status: `literature-checked` for the cited source hypotheses and the
bounded PaperSearch comparison below.  No theorem for actual pi is claimed.

Search date: 2026-08-27 UTC.  The local PaperSearch database at
`/home/Marcel/dev/AllMath/paper-search.sqlite3` contained `776632` records,
including `187052` with extracted full text.  The
search targeted the live natural-diagonal fresh contribution

```text
D_d = q*(Delta_0+Xi_d)-21/10
```

and the same-digit R2 condition `D_d>0` and `G_d+D_d>0`.  It looked for
pointwise lacunary theorems at explicit constants, Mahler or special-value
mechanisms with ordered real sign, and results stated specifically for pi.

## Closest source families

1. Aistleitner, [Metric number theory, lacunary series and systems of dilated
   functions](https://arxiv.org/abs/1306.3315), records discrepancy and LIL
   theorems for Hadamard-gap sequences.  Their strong fluctuation conclusions
   are explicitly for almost every `x`.  They do not select `x=pi`, handle the
   target-dependent growing T179 kernel, or align a fresh digit with `G_d`.

2. Moshchevitin, [A version of the proof for Peres--Schlag's theorem on
   lacunary sequences](https://arxiv.org/abs/0708.2087), Theorem 1, constructs
   an `alpha` satisfying a uniform lacunary avoidance bound.  Specializing to
   `d=1`, `M=8`, and `t_j=10^j` gives

   ```text
   exists alpha, forall j>=1:
     ||10^j*alpha|| >= 1/(2^14*log 8).
   ```

   The quantifier constructs a favorable number; it supplies no information
   for the prescribed number `alpha=pi` and only avoids integers rather than
   signing R1.

3. Costin--Huang, [Behavior of lacunary series at the natural
   boundary](https://arxiv.org/abs/0810.3027), gives Abel-regularized
   magnitude and boundary expansions, with exact finite decompositions at
   rational/root-of-unity angles.  It does not give a sign for a finite block
   at `exp(2*pi*i*pi)` or for the complete target-dependent primitive score.

4. Zorin, [Algebraic independence and normality of the values of Mahler's
   functions](https://arxiv.org/abs/1309.0105), proves quantitative
   nonvanishing for algebraic-coefficient Mahler systems evaluated along
   contracting interior orbits.  The actual decimal pi phase is an expanding
   unit-circle orbit, and algebraic nonvanishing supplies no order on a real
   part.

5. Barral--Loiseau, [Large deviations for the local fluctuations of random
   walks and new insights into the "randomness" of
   Pi](https://arxiv.org/abs/1004.3713), proves large-deviation properties for
   almost every path of suitable stochastic systems.  Its statement that the
   base-`m` digits of pi satisfy property `(P)` is explicitly labeled a
   conjecture supported by numerical experiments.  Even that conjecture does
   not state the same-witness R2 alignment.

6. Lagarias, [On the Normality of Arithmetical
   Constants](https://arxiv.org/abs/math/0101055), Theorem 3.1a, gives an
   exact asymptotic bridge between ordinary radix and perturbed BBP remainder
   orbits. Its distribution conclusion depends on the explicitly unproved
   Hypothesis A. The proved bridge is only `o(1)` in torus distance and gives
   neither a one-sided local gauge bound, a `1/q` rate, nor decimal
   same-digit alignment for DC1. More precisely, if
   `E_q=sup_(m>=q+1)|epsilon_m|`, direct use of the two literal T179 residue
   classes gives

   ```text
   |P_1(pi)-P_1(shadow)| < 200*pi*q^2*E_q,
   |DC1_pi-DC1_hybrid| < 100*pi*sec(pi/10)*q^3*E_q.
   ```

   Thus even a constant-margin hybrid DC1 transfer needs `E_q=o(q^-3)` plus
   an independent positive signed carrier margin. A degree-gap-one rational
   perturbation has only `E_q=O(q^-1)`. The familiar pi BBP formula is also
   power-of-two based, not a literal decimal rational-function expansion.

7. Beukers--Tijdeman, [A one-sided power sum
   inequality](https://arxiv.org/abs/1107.5495), proves signed pointwise lower
   excursions for fixed conjugate unit-circle exponential polynomials after
   selecting an unrestricted exponent. This is the closest inspected
   deterministic one-sided theorem. DC1 changes both coefficients and
   inherited deficit with the node and needs the prescribed natural-scale
   block; the theorem has no effective hitting time, fixed-node selector, or
   coupling to actual pi.

   A proof-level specialization sharpens this mismatch. Every fixed literal
   T179 paired-sector Laurent polynomial satisfies the source hypotheses, so
   in every complex direction it has syndetic positive excursions under
   integer dilation `z -> z^m`; at natural scales the directional amplitude
   is `>1/(450q)`. But the theorem selects an unrestricted integer `m`. A
   syndetic set can avoid every `10^s`, and `m` changes the constant from pi
   to `m*pi`; even `m=10^s` shifts the fresh block without transporting the
   same node's inherited DC1 deficit. The right-size excursion therefore
   occurs at the wrong quantifier.

## Boundary

The inspected literature splits at the wrong quantifier:

- signed lacunary fluctuation theorems hold almost everywhere in `alpha`;
- pointwise avoidance theorems construct some favorable `alpha`;
- Mahler and natural-boundary identities apply at contracting algebraic or
  rational boundary points;
- the direct pi stochastic statement is conjectural;
- the strongest one-sided power-sum result selects a free exponent for fixed
  coefficients, not the moving literal T179 polynomial at the required node.

None of these results proves R1 on an unbounded coherently reached actual-pi
path, and none couples the same digit to R2.  This is a dated bounded
literature boundary, not a proof that no relevant theorem exists outside the
searched corpus or can be developed later.
