# Digit file verification

Date: 2026-09-03 (public opening).

`pi_digits_1048596.txt` (1,048,596 digits after the decimal point,
SHA-256 `77eeccb0067283e14c460b33dc230de54ef15c2e825fc2a35c984fb6984bf684`)
was compared digit by digit against `mpmath.mp.pi` evaluated at working
precision 1,048,616 decimal digits (`mpmath` 1.x, CPython 3):

```
file digits 1048596
match True first mismatch None
```

Script: read the file, set `mpmath.mp.dps = n + 20`, take the fractional
part of `mpmath.nstr(mpmath.mp.pi, n + 10, strip_zeros=False)`, compare the
first `n` digits.
