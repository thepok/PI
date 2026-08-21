# T17 source-pinned decimal-prefix certification

Status: `literature-checked` digit certification plus exact computation.

## Normalized scope and ambiguities

T17 certifies one byte string: `1048596` fractional decimal digits of pi,
with no leading `3`, no decimal point or wrapping, and one final LF. It proves
that the file is forced by a rational interval derived from a published
identity and that its SHA-256 is the input hash retained for T16.

The canonical statement has quantifier ambiguities A1-A16 recorded in the
immutable statement. None is selected or weakened here. In particular, T17
does not evaluate `Q_pi`, successor splitting, T14, C2, or canonical A1. It
makes no normality, factor-complexity, or local block-occurrence claim.

## Published analytic input

The retained proof source is Milla, arXiv:1809.00533v6, Theorem 10.12,
PDF/printed p. 44. Exact source hashes, the general theorem's hypothesis, the
CM specialization, and the original Chudnovsky equation locators are recorded
in `SOURCE_PINS.md`.

Put `C=640320`, `A=13591409`, `B=545140134`, and

```text
u_k = (-1)^k (6k)! (A+B*k) / ((3k)! (k!)^3 C^(3k)),
S   = sum_(k>=0) u_k.
```

Theorem 10.12 states

```text
sqrt(C^3)/(12*pi) = S.
```

The exact integer identity

```text
C^3 = (12*426880)^2 * 10005
```

therefore gives the identity used by the verifier:

```text
pi = 426880*sqrt(10005)/S.                         (I)
```

The source's only explicit analytic hypothesis inherited from Main Theorem
9.7 is `Im(tau)>1.25`; for `tau=(1+i*sqrt(163))/2`, it is immediate from
`163>(5/2)^2`. All radicals in (I) are positive real roots.

## Truncation and tail inequalities

Let `L_k=A+B*k`. For every integer `k>=0`,

```text
L_(k+1)/L_k = 1 + B/L_k <= 1 + B/A < 42,
```

because `B < 41*A`. Direct cancellation gives

```text
 |u_(k+1)|   (6k+1)...(6k+6)             L_(k+1)
 ---------- = ------------------------- * ---------
    |u_k|     (3k+1)(3k+2)(3k+3)(k+1)^3  L_k*C^3

              6^6*42        1959552
          < --------- = ------------------ < 1.    (T)
               C^3      262537412640768000
```

Indeed each numerator factor is at most `6(k+1)`, while every one of the six
denominator factors preceding `C^3` is at least `k+1`. Thus the absolute terms
strictly decrease to zero (also `|u_k| <= |u_0|*rho^k` for the displayed
`rho<1`). The alternating-series theorem yields, for
`S_N=sum_(0<=k<N) u_k`,

```text
min(S_N,S_(N+1)) < S < max(S_N,S_(N+1)),            (A)
|S-S_N| < |u_N|.                                    (R)
```

Here `N=74919` is odd, so the exact computed order is

```text
S_(N+1) < S < S_N,
0 < S_N-S < |u_N|,
0 < S-S_(N+1) < |u_(N+1)|.
```

These are strict mathematical tail bounds, not a floating-point estimate.
`certify_pi.py` computes both adjacent partial sums as exact integer ratios by
binary splitting and verifies their cross-product order.

## Rational pi interval

Set `D=1048596`, `M=10^D`, and

```text
R = floor(sqrt(10005)*M) = isqrt(10005*M^2).
```

Exact integer squaring checks

```text
R^2 <= 10005*M^2 < (R+1)^2,                         (Q)
```

and `10005` is not a square, so `R < sqrt(10005)*M < R+1`.
Write the lower and upper adjacent sum bounds from (A) as
`S_lo=t_lo/q_lo` and `S_hi=t_hi/q_hi`. Positivity, (I), (A), and (Q) give

```text
  426880*R*q_hi                 426880*(R+1)*q_lo
  ---------------- < pi*M < ----------------------. (P)
        t_hi                            t_lo
```

The left and right fractions in (P) are the declared rational endpoints.
`interval_endpoints.hex` retains their four integers exactly as canonical
lowercase hexadecimal lines. Its SHA-256 is
`30e7186d43de56ceba645ef7170fed40ddc22bd50f6eb2bf6a39b1fcb170a0f9`.
Component checks are:

| component | bits | SHA-256 of canonical `0x...` integer |
|---|---:|---|
| lower numerator | 10790267 | `90cf426e6781cfe7f169517339e8b864f480f9f1707f040749defff527951897` |
| lower denominator | 7306904 | `52a0914ea591cd565263b99ed7e763eaeedb436caa9a77dd815c1f7aa9749338` |
| upper numerator | 10790368 | `253baaaf0cda9fe886163964fcbca37544b596bfee0f46f330a111f65ecc80e2` |
| upper denominator | 7307006 | `ad30c5a78cf6e25c75716c74dd38104bf5c75876f0bf682b78f8917cdb340318` |

If `L_num/L_den` and `U_num/U_den` denote these endpoints, the verifier checks

```text
floor(L_num/L_den) = (U_num-1)//U_den.               (F)
```

The right side is the greatest integer strictly below the upper endpoint, so
(P) and (F) force one value of `floor(pi*10^D)`.

## Certified bytes and hashes

The forced integer has `D+1` decimal digits and begins with `3`. Removing that
leading `3` and appending LF gives `pi_digits.txt`, exactly `1048597` bytes.

```text
payload without LF:
677e20e8d4e416051786d608ba29f6c56b9c84d8bd48132e33f83e8663818989

complete pi_digits.txt including LF:
77eeccb0067283e14c460b33dc230de54ef15c2e825fc2a35c984fb6984bf684
```

Retained `t16-reproduce.sh` shows that T16 generated exactly `1048596` digits
and byte-compared that file before using it. The exact retained T16 writer is
`t16-pi_certify.py`; the replay runs it and byte-compares its result with the
independently enclosed T17 file. Line 10 of
`t15-predecessor-SHA256SUMS.txt` independently records the same complete-file
hash for the predecessor experiment; it is not presented as a T16 manifest.

## One-command replay

From this directory run:

```bash
bash reproduce.sh
```

Requirements are Python 3 with arbitrary-size integers and standard
`bash`, `sha256sum`, `cmp`, and `mktemp`; no network or third-party package is
used. The command first verifies every retained artifact hash, then regenerates
the rational endpoints, certificate, and digit file in a temporary directory,
byte-compares all three, and independently runs the exact retained T16 writer
and compares its output bytes. Observed certification time in the managed run:
`41.442` wall-clock seconds, exit code 0. Declared budget: 300 wall-clock
seconds and 4 GiB RAM.

## Conclusion

This package certifies only the exact decimal-prefix input bytes and their
provenance. It does not repeat T16's experiment and makes no T14, C2, canonical
A1, or universal mathematical claim.
