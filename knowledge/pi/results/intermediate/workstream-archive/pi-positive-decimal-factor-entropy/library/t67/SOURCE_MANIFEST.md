# T67 source manifest

The canonical problem was formulated locally; no original source URL is
recorded. The delivered byte-exact copy is replay-verified.

| Source | Role | SHA-256 or persistent identifier |
|---|---|---|
| `pi-positive-decimal-factor-entropy.txt` | Canonical statement | `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6` |
| T36 `T36DecimalPeriodicWindowGap.lean` | Kernel-checked periodic-window estimate | `900e9fdeefbaea73236435b3845cd9dcc3c3b07b93d2e244b94dc39f4c109781` |
| T56 `T56LagSectorAudit.lean` | Kernel-checked exact lag ranges and conditional aggregation | `41e8ec69c4a113592b8f1de1dc5e02e815726c5a7e541ac7fd57afc6b181f1cc` |
| `T2NormalOrbitNearReturns.lean` | Kernel-checked cyclic-adjacency endpoint theorem | `1f0a50bc5286e997b897d03d49cc2613370c4cea0a20e41340f099b6278ff174` |
| `T8PiLacunaryNearReturns.lean` | Kernel-checked equality-to-strict-return direction | `324478887e8504d8086a9cedc6e640fe415491849e6391b63d1ec3fb10f596d8` |
| `T7FiniteCylinderEnergy.lean` | Kernel-checked three-code-graph comparison | `cac7b8da11c9369510e2e6e76b8bc74820b50ffe0285310475c7cf8ee1cfe91c` |
| `T25T25ResidualPairReduction.lean` | Kernel-checked arithmetic mask | `86639d8f8adbb5cf54a474fe89760cbeecd243e9f0bcb3768a16a23dab3ee88c` |
| `T26T26LongLagResidualReduction.lean` | Kernel-checked short residual definition | `744731fcaa2e252a8f63b0a0bbaf09ea86bdc72f379616437cc5b570f282e6b0` |
| Fine and Wilf (1965), *Uniqueness Theorems for Periodic Functions* | Attribution for finite periodicity lemma; the note gives its own graph proof | DOI `10.1090/S0002-9939-1965-0174934-9` |

The internal Lean files are cited accepted knowledge-library inputs, not replay
dependencies and not duplicated in this artifact package. `verify.sh` checks
the new counterfamily package; it does not independently recompile those
accepted modules.
