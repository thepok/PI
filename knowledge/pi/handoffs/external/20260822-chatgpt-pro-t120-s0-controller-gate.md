# ChatGPT Pro T120 S0 controller-gate handoff

Date: 2026-08-22 UTC

Status: `experiment` workflow implementation candidate; no Pi computation or
mathematical result

ChatGPT Pro was given repository `https://github.com/thepok/PI`, branch
`pi-core-consolidation`, and the bounded task of implementing only the frozen
T120 S0 strict-byte/schema/statistic/CAS/receipt validation gate and
controller-owned mutation tests. The single Pro call completed successfully,
required no re-login, and closed its browser session.

The response correctly reported that GitHub access was read-only and delivered
a patch rather than claiming a commit. It re-read the advancing branch and
targeted head `2d65e2535fc1d92dbd121dacbc31070b009f10cf`, including the later
hardened contract and immutable-controller-image prerequisite.

Downloaded artifact SHA-256 values:

- unified patch: `c84250cdac1c52463f78f21f040a60f8b3e96395e29f7a399b86eff02a8ff8a2`
- source archive: `b1028050aa14642dbdba2fe2fd31471dcec350841e296fde4af3bdf4a789b52c`
- audit summary: `415b2afc05b50d59af507cd1b06f3d117be8a96c1a80920ed4556fc375a4f32f`
- focused transcript: `bb44e991b76832d4c81ea7d93c53f308127d022865f50af836a0fab3b66be5be`
- supplied digest manifest: `f2c6fa8fa00b8bbc628c8b51a34ef6a87937bc5b780a3614a9f6c68301b713e3`

The patch adds a trusted oracle, isolated candidate harness, fixed controller
gate, focused tests, and the runner dispatch for gate ID
`t120_s0_schema_v1`. It changes no frozen contract, activates no task, runs no
provider/model wave, computes no BBP production point, writes no CAS object,
and mints no receipt.

Pro reported 47 passing tests and two environment-dependent skips. After
application on the real PI checkout, all 49 original focused tests passed,
including the real runner-dispatch and Podman checks. Independent audits then
confirmed the exact cell, determinant, lag, ratio, statistic, and decision
formulas, but found two acceptance-blocking trust gaps: a single public
deterministic fixture family and missing provenance for the live trusted
gate/harness/oracle bytes.

Both gaps were repaired before acceptance. The controller now creates four
unpredictable, replayable hidden fixture families from per-run entropy that is
unavailable to candidate code and disclosed only after execution. The hashed
runner binds the exact gate, harness, and oracle bytes; the gate rehashes,
copies, and rechecks them before using the copied harness. The resulting
controller bundle SHA-256 is
`9ceb6d0fcb754cbebe42067694694f0f69d8e8daf5d731bfa8177d38611abb88`.
After hardening, 53 T120 tests and 71 runner tests passed (124 total), including
real Podman execution. The independent integration verdict is to accept the
S0 implementation as trusted workflow infrastructure. No S0 candidate task or
production experiment is activated by this handoff.

Nothing in this handoff is evidence for decimal distribution, occupancy,
normality, V1, or a resolution of the Pi problem.
