# Versioned input data

## `pi_digits_1048596.txt`

- Content: the first 1,048,596 decimal digits of π **after** the decimal
  point, as one line of ASCII digits without the leading `3.`. The digit at
  0-based offset `n` is `piDigit n` in
  `TheoryLib/PiDigits/T7Statements.lean` (both indexed from zero after the
  point).
- SHA-256: `77eeccb0067283e14c460b33dc230de54ef15c2e825fc2a35c984fb6984bf684`
- Verification: at the public opening the whole file was compared digit by
  digit against an independent computation with `mpmath` at working
  precision 1,048,616 digits; the result is recorded in
  `VERIFICATION.md` next to this file.
- Reuse: the digits of π are a mathematical fact and carry no copyright. The
  file is provided as is; recompute it from any trusted source if you do not
  trust this one.
