# Finite three-adic BBP fibers do not constrain the real phase

Claim label: `proof sketch`.

Reviewed: 2026-08-21 UTC.

Source lineage: GPT Pro commit
`719631185e6003491ab64fd0cf3e796c58c587f7` and its immutable external
[handoff](../../handoffs/external/20260821-1922Z-archimedean-three-adic-fiber-separator.md).

## Accepted negative finding

Fix an epoch `t` and one residue of `3^(2*t) * q` modulo
`3^(2*t+2)`. Rational numbers with that exact scaled residue can be chosen on
a real lattice of mesh `9 / 10^K`; letting `K` grow makes every such finite
fiber dense in the real line. The construction can be iterated so that a
sequence of rational shadows preserves the actual registered BBP residue
system, its finite-precision coherence, and any prescribed one-sided error
schedule while converging to an arbitrary real target.

Consequently, no implication to decimal phase distribution can use only:

- the selected finite three-adic residues and their coherence;
- arbitrary positive rational shadows with a geometric one-sided tail; and
- generic algebraic or summable coboundary identities of the T106 form.

The handoff supplies a source-backed adversarial target whose decimal digits
use only `1` and `2`, yet which has irrationality exponent `2`. Thus adding a
source-style `IrrationalityMeasureBelow · 8` premise does not repair this
abstract route.

## Surviving BBP information

A viable continuation must use data destroyed by same-fiber replacement: the
specific full reduced numerator and denominator, the four-pole coefficient
structure, the exact seven-term BBP forcing, or another genuinely joint
invariant. More finite three-adic lifting without such coupling is closed as a
research direction.

## Scope firewall

This record is not a Lean theorem and does not close all BBP approaches. The
separator does not preserve the exact BBP partial-sum identity, full reduced
numerator or denominator, four-pole decomposition, or exact seven-term
forcing. It proves nothing about π, V1, normality, or digit occurrence.
