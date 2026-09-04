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

## `pi_digits_24000000.txt` (not tracked; regenerate)

- 24,000,000 digits after the point, generated 2026-09-04 with `mpmath` (`mp.dps = 24000040`,
  `nstr(mp.pi, 24000030)`, 25 s); prefix byte-identical to the 4,700,000-digit file.
- SHA-256: `7f97a5a03dc2745cae1c1b3f9c889ee4bc068fdbb93e28baa82512e93b528482` (the mining
  script checks it by file name).
- Not tracked because it exceeds the repository's 20 MB blob rule; the output
  `t198_mining_cycle2_machin_critical_shells.24000000.out.md` is tracked.

## `pi_digits_120000000.txt` (not tracked; regenerate)

- 120,000,000 digits after the point, generated 2026-09-04 with `mpmath` (`mp.dps = 120000050`,
  `nstr(mp.pi, 120000040)`, 181 s); prefix byte-identical to the 24,000,000-digit file.
- SHA-256: `f4ab163bc7562217a3f32bc48a2d88ff958bae1c4c986a3d6eedc73a2d1d45cf`.
- Output tracked: `t198_mining_cycle2_machin_critical_shells.120000000.out.md` (shell e = 11).
