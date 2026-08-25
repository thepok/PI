# Canonical BBP singleton-core prefix no-go

Status: `experiment`

Date: 2026-08-24 UTC

This is a finite, target-labelled obstruction to two stronger ways of trying
to bound the rational singleton core left open by T139. It is not a
cancellation estimate and is not a theorem in `TheoryLib/`.

Use the canonical inclusive T112 convention

```text
P_M = sum_(m=0)^M bbpTerm(m),
y_n = fract(10^n P_(7n)),
f_n = 10^(n+1) (P_(7n+7) - P_(7n)),
b_n = floor(10 y_n + f_n).
```

Thus `f_n` contains precisely the seven terms with indices `7n+1` through
`7n+7`. For `q=100`, `k=2`, `A=16`, and `N=50`, evaluate the 45
endpoint-free singleton frequencies `h=100+j`, where `1 <= j <= 49` and
`10` does not divide `j`, in the nine-channel rational core `R_(q,A)(N)`
defined in the
[singleton-ray note](20260824-endpoint-free-singleton-ray-barrier.md). Directed
interval arithmetic certifies

```text
Re R_(100,16)(50) in
[-0.677629649371418980600869768283705728604287172808882488071642779128145550151663590812742993,
 -0.677629649371418980600869768283705728604287172808882488071642779128145550151663590811524549]

-100 Re(R)/50 in
[1.35525929874283796120173953656741145720857434561776497614328555825629110030332718162304909,
 1.35525929874283796120173953656741145720857434561776497614328555825629110030332718162548599]
```

The exact T139 zero mode and full endpoint budget give

```text
100 alpha_100(0) / 2 < 1.144881020833854739,
(-2 Re(R)/50) - alpha_100(0) > 0.004207565558179664,
(-2 Re(R)/50 + 4 E/50) - alpha_100(0) > 0.024087099832656988.
```

Consequently, if

```text
U(C) := for every k>=2, A<10^k, and N>=1,
        Re R_(10^k,A)(N) >= -C N / 10^k,
```

then `U(C)` forces `C > 1.355259298742837961`, whereas even endpoint-free
T139 compatibility at `q=100` requires
`2C/100 < alpha_100(0)`, hence `C < 1.144881020833854739`. This retires the
T139-compatible, horizon-uniform **all-prefix** bound.

The actual `n=39` summand separately satisfies

```text
Re r_39 in
[-0.313807762365723917416046751668161070851984605785776063432903433499261671693668021126081306,
 -0.313807762365723917416046751668161070851984605785776063432903433499261671693668021126060266].
```

Therefore a uniform termwise bound `Re r_n >= -C/q` needs
`C > 31.3807762365723917416` and cannot provide a T139-compatible constant.
All phases here come from the actual reduced selected BBP rationals and
carries; in particular `b_39=1` and `floor(100 y_39)=16`.

## Provenance repair and replay

The originating Pro artifact used the exclusive partial sum
`sum_(m=0)^(M-1) bbpTerm(m)` while claiming to use T112. Its forcing therefore
used indices `7n` through `7n+6`, and its `b_0=31`, selected-rational digest,
and printed prefix interval were noncanonical. The corrected inclusive replay
has `b_0=1`, the same carry residues modulo ten, and selected-rational digest

```text
7afe5ab16b7dee048a39d83911809ecce7161363bc93afc56361f907c4129882
```

Reproduce the corrected certificate with

```text
python3 workflows/experiments/bbp_core_q100_A16_N50_canonical_certificate.py
```

Checker SHA-256:
`73f2655f44d860b684570d6df6f67a1315a42b0e0a7443419b5f6b9c519482b4`.

## Limits

The target was selected after inspecting the finite data and is already hit
at `n=39`. Later times can compensate for the negative prefix, and other
primitive rays can compensate in the full T139 sum. This finite experiment by
itself does not exclude a later or cofinal bound, obstruct the full primitive
sum, falsify T139, prove a strict pi-level predicate separation, or resolve
V1. The later `proof sketch` in the
[singleton-ray note](20260824-endpoint-free-singleton-ray-barrier.md#cofinal-fixed-target-termwise-no-go-proof-sketch)
does exclude eventual termwise rehabilitation at `q=100`, while retaining all
of the prefix, full-sum, T139, and V1 limitations just listed.
