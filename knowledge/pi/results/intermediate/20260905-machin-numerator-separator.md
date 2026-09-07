# Machin numerator information and its remaining real carry

Claim status: `proof sketch`; finite reproduction: `experiment`.
Date: 2026-09-05. No novelty or Lean-formalization claim.
The exact Machin recurrence remains available, but its positive increment,
a sharper one-sided enclosure, and a sparse numerator congruence do not
together force a prescribed decimal hit.

Use the actual [T198 brackets](../../entries/T198.md). Write N=4m+3,
`T_j=8/(j 3^j)+4/(j 7^j)` and W_m=T_N. Adding two Taylor terms gives
`L_(m+1)=L_m+T_(N+2)-T_(N+4)` and
`U_(m+1)=U_m-T_N+T_(N+2)`.
For `ell_N=lcm(1,3,...,N)`, let `H_m=21^N ell_N`, `B_m=H_m L_m`,
`b_m=H_(m+1)/H_m` and `K_m=H_(m+1)(T_(N+2)-T_(N+4))`.
These are integers, K_m>0, B_0=87112, H_0=27783, and

```
B_(m+1) = b_m B_m + K_m,
[10^(n+d) B_(m+1)]_(H_(m+1))
  = [10^d b_m [10^n B_m]_(H_m) + 10^(n+d) K_m]_(H_(m+1)).
```

The brackets in the last display denote least nonnegative residues; n,d>=0.
The positive increment does not determine the integer carry of this reduction.

## Sharper enclosure

Put `C_m=8/(10 N 3^N)+4/(50 N 7^N)`. Then

```
L_m + N C_m/(N+2) < pi < L_m + C_m,
width of this enclosure = 2 C_m/(N+2) < W_m/(5(N+2)).
```

For q=3,7 with coefficient c_q=8,4, the exact lower Taylor remainder is
`c_q integral_0^(1/q) u^(N+1)/(1+u^2) du`. Dividing by
`W_(q,m)=c_q/(N q^N)` gives
`N integral_0^1 t^(N-1) t^2/(q^2+t^2) dt`.
Bounding its final factor strictly between `t^2/(q^2+1)` and
`1/(q^2+1)` proves the enclosure. Its endpoint denominators change;
T214's exact valuation law cannot automatically be assigned to them.

## Sparse numerator congruence and inadequate orbit length

If N=3^r with r>=1 odd, then, in rationals with denominator prime to 3,

```
3^(N+r) L_m = -8 mod 3^(r+2),
v_3(den(L_m)) = N+r.
```

The normalized last 3-term is -8. Each earlier odd j=N-d contributes
3-adic valuation `r+d-v_3(d)>=r+2`; normalized 7-terms have valuation
at least N>=r+2. This proves the congruence and denominator equality.
For the common endpoint denominator D_m the same 3-adic exponent holds,
since U_m lacks that last term and has smaller exponent. Removing its
5-part therefore leaves a decimal residue period at least `3^(N+r-2)`:
`v_3(10^T-1)=2+v_3(T)`.
The original enclosure, however, can fit a length-10^(-k) cylinder only if
`10^(n+k) W_m<=1`, so n is at most `floor(log_10(1/W_m))-k=O(N)`.
A full-period argument lies far outside this accuracy window.

## One replacement retaining these derived properties

Take alpha=1/9, retaining H_m,W_m,C_m. Choose integer B_m^* in

```
H_m(alpha-C_m) < B_m^* < H_m(alpha-N C_m/(N+2)),
5 does not divide B_m^*,
B_m^* = -8 H_m/3^(N+r) mod 3^(r+2) when N=3^r, r odd.
```

The open interval has length `2 H_m C_m/(N+2)>18N`. At a sparse index
the required congruence has modulus 9N, so at least two consecutive
representatives lie inside, and at least one is prime to 5. The size bound
follows from `ell_N/N>=1` and `8*7^N/(5(N+2))>18N` for N>=3.
Elsewhere the mod-5 restriction alone is possible. Let
`L_m^*=B_m^*/H_m`, `U_m^*=L_m^*+W_m`.
They retain the sharper enclosure about alpha, the lower-endpoint 5-adic
denominator law, and the sparse 3-adic congruence and exponent above.
They are nested: both C_(m+1)<C_m/81 and W_(m+1)<W_m/81, while the
lower error is between N C_m/(N+2) and C_m and the upper error is
between W_m-C_m and W_m. Yet alpha's orbit is constantly 1/9, so it
has no zero or nine cylinder hit for any k>=1.

The replacement does not retain the literal increment K_m and seed B_0
together, nor necessarily the original reduced D_m. It does not refute an
argument that actually uses those exact data to control the real carry.

## Finite reproduction and retained boundary

The [standard-library exact-arithmetic script](../../../../workflows/experiments/machin_orientation_audit_20260905.py)
was inspected and rerun locally; its complete JSON output matched the
Pro-generated output exactly: 551 adjacent and 2,204 joint residue checks,
547 refined enclosures certified using deeper original brackets, and 552
rational replacement brackets. These finite checks are `experiment` only.
At m=6, N=27, k=1 the entire admissible range n=0,...,12 contains no zero
certificate. This refutes the corresponding per-truncation forcing rule,
not CW0 and not existence after arbitrarily long waiting.

First fatal inference: positive increment or a 3-adic numerator congruence
is treated as a favorable real carry before the accuracy window closes.
Strongest retained: the exact recurrence, sharper enclosure, sparse
congruence, and a replacement retaining their stated coarse consequences.
Reopen only with a carry estimate using the literal seed and increments.
