# T133 prior-evidence archive index

`prior_evidence.tar.gz` vendors byte-exact comparison evidence. Extract with
`tar -xzf prior_evidence.tar.gz`. Notes and reports are comparison memory only;
their status is stated in `REPORT.md`.

| Archive member | SHA-256 | Exact inspected region |
|---|---|---|
| `T91-REPORT.md` | `a684f15960a176f37ee2e8e853313e05e0e2f8de9674be2fcd744f59fe62573e` | lines 34--51 and Sections 3--6, lines 53--357 |
| `T94-REPORT.md` | `f399dfac1990b3cc4a6c9e69127a1ceff22356c6b656ec2e3a1b9045be6efa10` | automata/recurrence lines 47--378; transfer boundary lines 472--498 |
| `T97-REPORT.md` | `fb3c58a436d173902ccf3577dc02d1702403f681d6cc08a39481e1c73cd31a8e` | result/recurrence lines 58--389; transfer boundary lines 408--424 |
| `T101-REPORT.md` | `ddd24794d6e6795a4aa466819782aa63a6578d70746ce4d592bb18ef644c243e` | splitting/energy lines 13--359; fingerprint and tests lines 364--434 |
| `T112-REPORT.md` | `72884fc7d8d594cfd2f380cafde121c541c1aa316badf054ac143bb102abcefa` | carry models lines 217--543; proposed operator/boundary lines 602--819 |
| `T115-REPORT.md` | `29cd0707df354aef8f50e4dfa4b9a780b863d93aef26cebdc4cbb8488ee27a36` | recursion lines 86--193; comparisons and rejection lines 208--342 |
| `T118-REPORT.md` | `2ed7a176bedb2f3a1627dffd4002f6b6141f078fe5c73798041b4fba90c7410e` | private component/order lines 46--167; transfer and candidate tests lines 169--604; fingerprint lines 647--687 |
| `T124-REPORT.md` | `461df40595e9d59852b7d86f8df8800b0e5fafaf6803843cb2ea1e29d737dd86` | branching/H1 lines 127--313; transfer lines 643--668; U_n successor lines 687--690 |
| `T126-REPORT.md` | `afa4bf0c5ef48042c68f4b938c94ecb0890c5722bc97d72e08bb9ef616e39ed8` | recurrence/valuation lines 50--188; denominator/orbit lines 190--364; PI-H1-COLL lines 386--405 |
| `T7-FiniteCylinderEnergy.lean` | `cac7b8da11c9369510e2e6e76b8bc74820b50ffe0285310475c7cf8ee1cfe91c` | machine-checked comparisons lines 292--318; canonical energy frontier lines 346--386 |
| `T107-AveragedTriangularFejer.lean` | `45cb809d65c38b866ad7c46c913d617c61f8e97e777ccdec8ed9645e4982ae28` | definitions/budgets lines 31--69; criterion lines 150--199 |
| `T133-binding-prompt.txt` | `969089188470d713ae3f7d9c9a31a4fcaa07c4506894d9c280319122b45bfefc` | line 38 identifies active T131--T132 and states the binding comparison requirement |
| `T133-orchestrator-snapshot.json` | `64dd3a8dbfe1e665f0c409d1979e795a12b6ceb69a4afd99d505d34e485cc78d` | supplied snapshot inventory; no T131/T132 artifact entry is present |

The replay checks every member name and hash after extraction in memory.
