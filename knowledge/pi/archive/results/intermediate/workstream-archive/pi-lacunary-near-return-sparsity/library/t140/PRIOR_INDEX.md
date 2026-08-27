# T140 prior-evidence index

`prior_evidence.tar.gz` contains the readable comparator reports and Lean
modules from the refreshed T140 knowledge snapshot. Reports under `notes/` and
all recovered reports remain unverified proof-sketch comparison memory.

## Named machine-checked comparators

| item | archive member | SHA-256 | named declaration and locator | T140 boundary |
|---|---|---|---|---|
| T7 | `t7/FiniteCylinderEnergy.lean` | `cac7b8da11c9369510e2e6e76b8bc74820b50ffe0285310475c7cf8ee1cfe91c` | machine-checked equal-cylinder/near-return comparison at source lines 292--318 and exact finite-energy frontier at lines 346--386 | T140 uses its collision convention only; assuming decay would restate T7 |
| T92 | `t92/T92ConstantRunDiscriminator.lean` | `d912120e6ebc122d82f889f1731be56eb756b312b66244ff22ee451317e7cd12` | named machine-checked constant-run discriminator accompanying the unverified T92 report | one-family charging, not census |
| T100 | `t100/T100UniversalCharging.lean` | `8fa767cf17deb3ff7b17f94d2d57679122c7cc46e1d9d7a2286846e12ae51787` | named machine-checked universal exact-word charging theorem accompanying the unverified T100 report | overlap-period charging, not census |
| T106 | `t106/FiniteBranchingResonanceTree.lean` | `824971b102f33b41f6c2f79ad616cc03b1ce83d59aec5edafa836f2cafa89f61` | `DecimalFactorComplexity.FiniteBranchingResonanceTreeT106.literal_not_canonical_C1_implies_finite_branching_resonanceTree`, lines 299--368; axiom print line 375 | conditional Fourier resonance branching, not a word census |
| T107 | `t107/T107AveragedTriangularFejer.lean` | `45cb809d65c38b866ad7c46c913d617c61f8e97e777ccdec8ed9645e4982ae28` | `DecimalFactorComplexity.AveragedTriangularFejerT107.explicit_averaged_triangular_t64_implies_coherent_splitting_at`, lines 300--328; axiom print line 368 | same triangular depth geometry, but low analytic defect rather than inverse high-collision enumeration |
| T108 | `t108/T108LiteralTransport.lean` | `97f6333ee777b45b842530876ac5e6d29309cfe0987a1ce669690c86c8e5caee` | `DecimalFactorComplexity.T108LiteralTransport.literal_deterministic_transport`, lines 695--733; axiom print line 750 | exact-word-to-metric transport, not container census |

## Recovered comparison artifacts

| item | archive member | SHA-256 | status and boundary |
|---|---|---|---|
| T109 | `t117/prior-t109-REPORT.md` | `6b4f27464b76c67ea6fe41990f9ed6d3242c8c763b880fb4862fbac16f3ffcdf` | rejected robustness report; records why failure of a sufficient certificate is not a necessary obstruction |
| T119 | `t130/prior-t119-REPORT.md` | `72b10e921761874158893bb9cbb7454094bcbc59bbdfc787f33bbf355b63f23a` | revised report with incomplete source package; predictive/Hankel/Prony rank separators are proof sketches |
| T122 | `t125/prior-t122-REJECTED-REPORT.md` | `6ea3b7798ff4b211c0f6c3b514d062fbce8e518208c570231a1f2c32417845b7` | rejected constructive discrepancy report; comparison memory only |
| T123 | `t125/prior-t123-R0-REPORT.md` | `3eed848437e5ade5cfc0ac5c8f8fabf5968ff156262b74ea2d947413b74fecb2` | parked effective specification report; accepted recovery is readable T128 |

## Accepted report map

Each entry below is source-audited prose with local deductions remaining proof
sketches (`LC/PS`).

```text
T89  t89/REPORT.md   ad90a5a5084f7ef19f4fce052ae99330f0cab9103f2942ee164d713de2a8b5b9
T90  t90/REPORT.md   730c5cdaf154bd375084a243fc82ebf6ab4ce2c1e234baf43515d4aaea34cfc0
T103 t103/REPORT.md  ed690a31fbc19d08c817bcb2558ec259788e37d4f8243261ece1b9eafbbb5df0
T104 t104/REPORT.md  2dee0c91ce8480785a851df4aad06e0ab65f92e647fa7f67605b868129fc16d5
T105 t105/REPORT.md  ff63d5a956765beda402cc36e953a6f678ad1bf900254e6e2e8a20326842ed9f
T110 t110/REPORT.md  4eaa088ecb7ea8936d5c35d1eefb66027b376a020c8e76f4a2b91c012a3cb668
T111 t111/REPORT.md  89eae292ac15699fd7175b879189d6eb5560fd692029f8a9dbdc1093583156d8
T112 t112/REPORT.md  72884fc7d8d594cfd2f380cafde121c541c1aa316badf054ac143bb102abcefa
T114 t114/REPORT.md  db21ac7d0a7845264c727132293db149a06a832d6f67700fd9ceb0f69a142cca
T115 t115/REPORT.md  29cd0707df354aef8f50e4dfa4b9a780b863d93aef26cebdc4cbb8488ee27a36
T116 t116/REPORT.md  573011bda281022483a113829138112494b73d667323c30aa2a0ef03bba32cd1
T117 t117/REPORT.md  ee6974209f7e6064f30ec3ae83240cb1e7994e66566e920417dbf361da0ff30b
T118 t118/REPORT.md  2ed7a176bedb2f3a1627dffd4002f6b6141f078fe5c73798041b4fba90c7410e
T120 t120/REPORT.md  8b375d1c06cbf9549e5f1919d25b227a9479be7bc3a5ed70955f5718a996dad5
T121 t121/REPORT.md  01b97953941608b41b0fcd12cc5be0047f447be28d7cd26f8bae6506717e6cf2
T125 t125/REPORT.md  1ce372d3a99323eae9460a4dbc25b329b93b66e0a356aa3284f1fc9c543f461a
T127 t127/REPORT.md  19bdf7a7e44be685c4c994c64d28bdf9f1787b77e8999f6c9a10a496b27ed379
T128 t128/REPORT.md  7e9520d7a0191df6f988d7f4f4920cfb954ac5162efa7fae43c1851de5863ffc
T130 t130/REPORT.md  c130b2c8790dce80080367201e56efb3847f8262189af57f2ce756aacb6a893c
T131 t131/REPORT.md  ed2229ceedcff357f80121fbdc31ffbb8e3582717f487a3a85368eabe64790db
T132 t132/REPORT.md  1d1aa950f21bb35697a5301cd3dbcacb27fec50a70d98009f1bb9f6179fe23bd
T133 t133/REPORT.md  53a1c70ff1fe9d91cc21f9044372a0ecca96567654ae1b6e3e04955be69c9d40
T134 t134/REPORT.md  a403e69db9d30d82bbc669cac02efd4476d71ad19ae5d6fac62016aa6334db14
T135 t135/REPORT.md  4439850a49ee2fa7351d85daf366eba4b2b4a55e756a15bf7c431d92fb195e21
T136 t136/REPORT.md  b15cb995dfc5e1983d0056987c0371b3b7f85469c7dd175e2eb13a719465dc5f
```

## Unverified note map

Every row below is `PS` (some have source pins or experiments, but no note
claim is treated as discharged).

```text
T91  notes/t91/REPORT.md   a684f15960a176f37ee2e8e853313e05e0e2f8de9674be2fcd744f59fe62573e
T92  notes/t92/REPORT.md   155f1a4652f125bcf48e668315b05199a6077a943bf19f714e1e1ad02d9e19c1
T93  notes/t93/REPORT.md   2ff685b20920f5a2d71db2b8a300ce8c2762152c3d4b2c59236b160ed812f8ae
T94  notes/t94/REPORT.md   f399dfac1990b3cc4a6c9e69127a1ceff22356c6b656ec2e3a1b9045be6efa10
T95  notes/t95/REPORT.md   08baad91851c1d25ceaa82f86cbe8b728ca2c063f31f01f83c5fa96aea45d8cb
T96  notes/t96/REPORT.md   de8940fd7927a20d88626cec7ae8b411cd2788c1fdecb762496a72c8f18019aa
T97  notes/t97/REPORT.md   fb3c58a436d173902ccf3577dc02d1702403f681d6cc08a39481e1c73cd31a8e
T98  notes/t98/REPORT.md   b6b8d30499543fadf5be200b85afe3929dcba5b7a7d96061476965060c589f57
T99  notes/t99/REPORT.md   9778fd0fdc3151b0e3f8888afdb1d1049347e926d266f2981e7daa3bc44af2b4
T100 notes/t100/REPORT.md  7328d1730a68b820441f4e6c1eb9c4bbb99abb34193dbcc1270f6990a8c905fb
T101 notes/t101/REPORT.md  ddd24794d6e6795a4aa466819782aa63a6578d70746ce4d592bb18ef644c243e
T102 notes/t102/REPORT.md  49a63d0003102728766a41e026400f3bc69e9baeb42e66338510bcbecc1d6304
T113 notes/t113/REPORT.md  30ff535624185d37981311d2f1e2a072d300221bec3f049351e5cae1026ed445
T124 notes/t124/REPORT.md  461df40595e9d59852b7d86f8df8800b0e5fafaf6803843cb2ea1e29d737dd86
T126 notes/t126/REPORT.md  afa4bf0c5ef48042c68f4b938c94ecb0890c5722bc97d72e08bb9ef616e39ed8
T137 notes/t137/REPORT.md  84cbe349ea52137d2bd8bbf90e1eab389a599271f9d404b2e12255d3188d29f5
```

There is no direct T129 report or declaration in the refreshed snapshot. T138
is present only as a rejected recent-result record whose listed files are
absent. T139 has no knowledge entry, report, declaration, or recent result.
These are explicit comparison-availability failures, not novelty claims.
