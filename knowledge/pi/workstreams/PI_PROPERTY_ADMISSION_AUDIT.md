# Finite π-property admission audit

Status: `literature-checked` where a source is linked; logical route judgments
are `proof sketch`. Last audited: 2026-09-02 UTC.

This is a finite audit of the named inputs used by the current program, not a
claim to classify every theorem about π. Admission requires both a property
that suitable word-avoiding replacement constants cannot share and a credible
translation to a directed decimal statement.

| Input | Can a word avoider share the property? | Directed decimal output | Decision |
|---|---|---|---|
| Irrationality | Yes. | None; it only prevents eventual exact periodicity. | Closed. |
| Transcendence | Yes; the avoidance Cantor families contain transcendental points. | None. | Closed. |
| Finite, or even exact `mu=2`, irrationality exponent | Yes; the active Kleinbock--Weiss/Kristensen--Thorn--Velani and BFKRW separators supply badly approximable, hence exact-`mu=2`, avoiders. | Ridout-type control limits very long boundary runs but does not force recurrence to either endpoint. | Closed as a sign source. |
| Published irrationality measure for π | Yes at the qualitative property level. [Zeilberger--Zudilin](https://arxiv.org/abs/1912.06345) give an exponent below `8`; [Hata](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6344.pdf) gives about `8.016045`, not below `8`. | The former discharges T194's timed premise in ordinary mathematics. It does not prescribe the cell or sign the fresh horizon. | Retain for T194; full Lean formalization is a separate large milestone. |
| Euler/Wallis products and `zeta(2n)` identities | No when stated as exact identities uniquely fixing π. | Known positive products and scalar order do not survive target rotation; extracting a digit restores the unknown integer lift. | Closed absent a new non-scalar order law. |
| Machin identities and rational/Padé brackets | No as exact-value identities. | Approximation length is controlled; target-side orientation is not. | Closed by the mirror/derivative and scalar-tail separators. |
| BBP-type formulas | No as exact-value identities. Binary BBP leads to the Bailey--Crandall perturbed-orbit problem; [Lagarias](https://arxiv.org/abs/math/0101055) records the open Hypothesis A context. | No proved distinguished-orbit sign. The decimal unknown-lift obstruction is analogous to, not literally identical with, Hypothesis A. | Binary route remains open but conditional; decimal route paused. |
| Base-10 Machin-type BBP formulas | The proposed source itself is unavailable in the studied class: [Borwein--Borwein--Galway](https://geodesic.mathdoc.fr/articles/10.4153/CJM-2004-041-2/) exclude nonbinary Machin-type BBP arctangent formulas for π. | This does **not** prove that every conceivable base-10 BBP formula or digit algorithm is impossible. | Do not overstate the no-go. |
| Chudnovsky/hypergeometric and modular/CM representations | No as exact-value characterizations. | Extremely strong scalar approximation and algebraic structure, but no target-rotated half-plane order has survived audit. | Paused; reopen only with a literal signed translation theorem. |

## Exact benchmark below V1

For `x_n={10^n*pi}`, all `0^k` occur iff `liminf x_n=0`, and all `9^k`
occur iff `limsup x_n=1` (`proof sketch`). Therefore
`liminf ||10^n*pi||=0` is the disjunction of these endpoint recurrences, not
their conjunction. Both directed endpoint statements remain open in this
repository.

## Program decision

The audit found no missed admitted property among these named inputs.
Exact-value representations are the only entries in the table that word
avoiders cannot simply share,
but every audited translation loses the distinguished real sign. The current
exactifier cycle is therefore paused. It reopens only when a candidate passes
the three admission tests in `FRONTIER.md`.

A base-2 or base-16 pivot would be a scope change, not a deduction from this
audit. The BBP dynamical problem is native there, but disjunctivity remains
open and would not prove decimal V1.
