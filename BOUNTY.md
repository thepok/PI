# The V1 bounty

**USD 10,000** for a machine-checked proof that every finite decimal digit
string occurs in the decimal expansion of π.

## Why I am doing this

I am not a professional mathematician. Pi Lab is a hobby, and it is not a
cheap one: every month a few hundred dollars go into compute and AI models
that grind through Lean proofs, falsification experiments, and route audits
for this one question. Measured against that, USD 10,000 for the actual
answer is a bargain, and I would pay it with a smile.

I do not expect a claim next week. Every road that has been tried ends at the
same wall, and this repository documents that wall in detail. But somebody,
someday, will have the idea that the digit-avoiding numbers do not share, and
I want that person to have a reason to write it down in Lean and to send it
here first.

## The statement

The prize is for a proof of the proposition `Theory.PiDigits.V1` exactly as
defined in
[`TheoryLib/PiDigits/T7Statements.lean`](TheoryLib/PiDigits/T7Statements.lean):

```lean
noncomputable def piDigit (n : ℕ) : Fin 10 :=
  ⟨⌊Real.pi * (10 : ℝ) ^ (n + 1)⌋₊ % 10, Nat.mod_lt _ (by norm_num)⟩

def V1 : Prop :=
  ∀ s : List (Fin 10), ∃ n : ℕ, ∀ i : ℕ, ∀ hi : i < s.length,
    piDigit (n + i) = s.get ⟨i, hi⟩
```

`Real.pi` is Mathlib's π. The definition file is frozen; a proof of a
different statement, however similar, does not qualify.

## What qualifies

A pull request against this repository that

1. contains a Lean 4 term `theorem v1_holds : Theory.PiDigits.V1 := ...`
   (any name, any file under `TheoryLib/`), imported by `TheoryLib.lean`;
2. builds green with the toolchain in `lean-toolchain` and the Mathlib
   revision pinned in `lake-manifest.json` at the time of submission
   (`pwsh workflows/verification/check.ps1` passes);
3. contains no `sorry`, `admit`, `native_decide`, `unsafe`, `opaque` tricks,
   `implemented_by`, `extern`, or new `axiom` declarations, and whose
   `#print axioms` output lists nothing beyond `propext`, `Classical.choice`,
   and `Quot.sound`;
4. is submitted under this repository's license so that it can be merged.

Nothing else is required. No paper, no referee, no waiting period: the proof
checker is the referee.

## Verification and payment

The maintainer rebuilds the pull request from a clean checkout on the pinned
toolchain within 30 days of submission and publishes the build log in the
pull request. If the build is green and the axiom audit is clean, the pull
request is merged with the author's name and the prize is paid to the author
within 30 further days by bank transfer.

If several qualifying pull requests are open at the same time, the earliest
submission timestamp on GitHub wins. Co-authors share the single prize as
they agree among themselves; failing agreement, in equal parts. The prize is
paid once.

AI assistance is allowed and must be disclosed in the pull request
description. The author must be a natural person or a group of natural
persons; the prize is not paid to organisations.

## Fine print

- Sponsor: the owner of this repository, a private individual in Germany.
- This is a public promise of a reward. It is binding on the sponsor under
  German law (§ 657 BGB) from the date it was first published in this
  repository, and it remains open for ten years from that date unless
  revoked earlier by a notice in this file, which cannot affect a pull
  request already submitted.
- The prize is a fixed gross amount in US dollars. Taxes, if any, are the
  recipient's responsibility.
- Smaller named problems on the way to V1 are listed in
  [`knowledge/pi/workstreams/OPEN_PROBLEMS.md`](knowledge/pi/workstreams/OPEN_PROBLEMS.md).
  They carry no prize; a solution earns a named entry in the ledger and the
  maintainer's gratitude.
- Questions go into a GitHub issue, not e-mail.

Published: *(date to be set when the repository goes public)*.
