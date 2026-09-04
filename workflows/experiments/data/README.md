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

## `pi_digits_4700000.txt`

- Content: the first 4,700,000 decimal digits of π after the decimal point, one line,
  zero-based like the file above; its first 1,048,596 digits are byte-identical to
  `pi_digits_1048596.txt` (checked with `cmp`).
- Generated 2026-09-04 with `mpmath` (`mp.dps = 4700030`, `nstr(mp.pi, 4700020)`), 3.7 s.
- SHA-256: `0a14c71c5e0f093b25707c907bf416edc553153ff7c57c89bff31513889c0a93`
- Purpose: complete Machin critical shell e = 9 for the cycle-2 conjectures M5CS0/M5CS9.
