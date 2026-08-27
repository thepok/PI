# Thue–Morse–Mahler adversarial target

Claim label: `literature-checked`.

Checked: 2026-08-21 UTC.

## Primary source

Yann Bugeaud, “On the rational approximation to the Thue--Morse--Mahler
numbers,” *Annales de l'Institut Fourier* 61 (2011), no. 5, 2065--2076,
[DOI 10.5802/aif.2666](https://www.numdam.org/item/AIF_2011__61_5_2065_0/).
The relevant locator is the unnumbered theorem in Section 2; Remark 2.1 records
effectivity.

For the Thue--Morse sequence `τ`, the source proves that
`Σ k, τ k * b^(-k)` has irrationality exponent exactly `2` for every integer
base `b >= 2`.

## Repository use

At `b = 10`, rational translation by `1/9` preserves irrationality exponent
and, because the summands introduce no decimal carries, produces an irrational
target whose decimal digits are only `1` and `2`. It is therefore not decimal
disjunctive. The effective exponent-two bound yields the quantifiers in the
repository predicate `IrrationalityMeasureBelow · 8` by choosing an exponent
strictly below `8` and absorbing finitely many denominators into the onset.

The source theorem is used only to build an adversarial target for the finite
three-adic-fiber route. It is not evidence about π. The translation, digit
description, and conversion to the repository predicate are elementary
derivations, not claims quoted from Bugeaud.
