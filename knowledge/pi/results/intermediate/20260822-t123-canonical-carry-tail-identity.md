# T123 canonical carry-tail identity

Date: 2026-08-22 UTC

Status: `proof sketch`

For the canonical BBP rational diagonal, write

```text
R_n=(10^n-16)*A_n=a_n+e_n,
a_n=floor(R_n+1/2),
e_n in [-1/2,1/2),
b_n=a_(n+1)-10*a_n in Z.
```

Iterating the last recurrence gives, for every `N>=0` and `L>=1`,

```text
a_(N+L)/10^L
  =a_N+sum_(r=0)^(L-1) b_(N+r)/10^(r+1).
```

Since `a_n=R_n-e_n` and `|e_n|<=1/2`, the centered term divided by `10^L`
tends to zero.  Also

```text
R_(N+L)/10^L
  =(10^N-16*10^(-L))*A_(N+L) -> 10^N*pi,
```

because the BBP partial sums `A_n` converge to `pi`.  Passing to the limit
yields the exact identity

```text
10^N*pi=a_N+sum_(r>=0) b_(N+r)/10^(r+1)       (N>=0).
```

The integer sequence `b_n` is bounded: from

```text
C_n=R_(n+1)-10*R_n=b_n+e_(n+1)-10*e_n,
```

the centered errors are bounded and `C_n` converges to `144*pi` (with only
finitely many earlier values).  Thus the displayed sum is a convergent
base-ten weighted integer series; `b_n` is not being identified with an
ordinary decimal digit.

If the canonical carry tail were eventually periodic, choose `N` beyond its
periodic onset.  Its base-ten weighted integer series would then be rational,
so the identity would make `10^N*pi`, and hence `pi`, rational.  Therefore

```text
the canonical first-carry sequence (b_n) is not eventually periodic.
```

This is only the contradiction endpoint for T123.  It does not prove that
eventual avoidance of a centered hole forces periodicity or even a rational
carry tail; those are the open `(AR_eta)` and `(CTR_eta)` implications.  It
uses no Furstenberg premise and proves neither `(D)` nor V1.  V1 remains open.
