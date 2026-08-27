# Locked prior evidence

This T5 package references the following accepted, content-addressed audits.
It did not rerun their searches, theorem transcription, or replay scripts.
The paths are relative to the workspace root. Each basename equals the file's
SHA-256 and can therefore be checked directly.

| Prior item | Role imported into T5 | Accepted audit | Source manifest | Acceptance evidence |
|---|---|---|---|---|
| pi-digits T28 | Lacunary exponential sums and discrepancy against the earlier T27 certificate; source of the Philipp and Fukuyama rows | `.research/proof-ledger-artifacts/sha256/48/4845c8661303b873bc4bb38dc8ee1005695fdd62b1fe4d16b36eaee61244abbd` | `.research/proof-ledger-artifacts/sha256/33/33c0ccc0cba5f8aaa12783e5201da41ffa002d0ea01cdd21621791b8b28e6544` | `.research/proof-ledger-artifacts/sha256/59/5984f0dacb05f4bfc3e612836edc4560a6965c02ccce18ddc9e18b043d4ab401` |
| pi-quantitative-block-hitting T4 | Bailey-Crandall, Lagarias, BBP, base transfer, and finite-computation separation | `.research/proof-ledger-artifacts/sha256/43/432500da9cd3e29470cfba78ab1fd0f5f5362c20bf6038fccdfede8987e3d5a0` | `.research/proof-ledger-artifacts/sha256/67/673d31125cb1776ceff7dec5c72f9ba48ab46f12dd20f1c7369745838f6be913` | `.research/proof-ledger-artifacts/sha256/c3/c383d9d70dfebed6e9a2fc778ee935258b2308dcf23496daf9c25508e408b223` |
| pi-quantitative-block-hitting T9 | Deterministic fixed-orbit and irrationality-measure results beyond T4 | `.research/proof-ledger-artifacts/sha256/97/9734cd424f252b6f166a601c1d6f6bd1297645b6d39d6a276d2ba2b90118c350` | `.research/proof-ledger-artifacts/sha256/27/27ecb1ef8221d1e5bb5903d004b192caa86288415b518eaa993e7d05eb38e870` | `.research/proof-ledger-artifacts/sha256/c1/c139f6f8ce2cd95f44936fde22131e922871c8b693c93197a5163119daa52128` |
| pi-decimal-factor-complexity T11 retry r1 | Fixed-pi weighted Fourier applicability matrix; confirms that metric and mean-square inputs remain non-pointwise | `.research/proof-ledger-artifacts/sha256/19/19842fdad9fae9ea19abadeaf21121946558b181ab8eb49c57668e8823107016` | `.research/proof-ledger-artifacts/sha256/bb/bb2b0c4ed44a6e77b800ca6aef3fc1a635828890e080dce9ccd60d82c7a4d328` | `.research/proof-ledger-artifacts/sha256/da/dafd9dadcac2279f02d3d2d2930405e59955f2379da13f84f2a30cc6abb2af58` |

## Scope discipline

- T28 already inspected Erdos-Gal, Philipp, and Fukuyama. T5 imports the
  exact source pins and fixed-pi obstruction; it does not perform that audit
  again.
- T4 and T9 target the stronger quantitative block-hitting problem. T5 uses
  their source and separation findings only where they compare directly with
  decimal pi; it does not import their stronger deadline as the present T3.
- T11 targets a different weighted Fourier hypothesis. T5 imports only its
  classification of metric versus fixed-point evidence.
- Same-number Lean modules such as positive-lower-density T4, pi-digits T9,
  and pi-digits T11 are not silently substituted for these literature audits.
  They are distinct accepted formal artifacts.
- The acceptance JSON files use generic workflow telemetry labels. The
  accepted audits themselves are explicitly `literature-checked`; T5 relies
  on their content and `verdict: done`, not on the telemetry suggestion.

`reproduce.sh verify` checks every path above without executing any prior
audit or prior replay script.
