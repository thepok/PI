# Exact carry-language target

Define

```text
a(k)=(120*k^2+151*k+47)/((2*k+1)*(4*k+3)*(8*k+1)*(8*k+5))
b_k=a(k)/16^k
B_n=sum_(k=0)^n b_k
R_n=(10^n-16)*B_n
e_n=R_n-floor(R_n+1/2) in [-1/2,1/2)
kappa_n=floor(R_(n+2)+1/2)-11*floor(R_(n+1)+1/2)
        +10*floor(R_n+1/2)
```

The exact numerator-eliminated recurrence is

```text
e_(n+2)-11*e_(n+1)+10*e_n = h_n-kappa_n,
h_n=(10^(n+2)-16)*b_(n+2)+(160-10^(n+1))*b_(n+1).
```

The actual four-pole values satisfy `h_n<0` for `n>=2`. The audited scalar
bound also gives

```text
max(|e_n|,|e_(n+1)|)>0.0349 for every n>=4.
```

Thus returns tending to zero, if they exist, are isolated. Under the recorded
Furstenberg source input, the remaining target is

```text
liminf_(n->infinity) |e_n| = 0.
```

Determine whether the exact sequence `h_n` forces the canonical carry
trajectory to leave every survivor strip `|e|>=eta` infinitely often through a
genuinely arithmetic restriction on finite carry blocks. For a compatible
block `kappa_N,...,kappa_(N+L-2)`, eliminate `e_N,e_(N+1)` and seek an exact
congruence, divisibility, or interval condition involving the actual rational
block `h_N,...,h_(N+L-2)`. Prove violation for a specified family `eta->0` and
growing `L`, or rule out an explicit infinite family of carry words by a
product-scale cross-index argument. If such a restriction is false, give an
exact compatible block or trajectory for the actual `h_n` and identify the
failure.

Hard exclusions: qualitative use of `h_n<0`, summability or monotonicity alone;
denominator growth; isolated prime residues; generic DFT or energy; T119/T120;
modified-forcing countermodels; merely rewriting the recurrence; or restoring
the full numerator as hidden state. Every positive lemma must use cross-index
arithmetic of the displayed four-pole numerators and denominators and state
exact quantifiers. V1 remains open.
