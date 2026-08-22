# T120 S0 controller schema integration

Status: `experiment`.

The bounded T120 S0 pure validation library is now integrated at
`workflows/modelbench/tasks/pi/planned/t120-q10-exact-diagnostic/stages/s0-controller-gate/implementation/`.
It originated from free OpenCode/Oxzen run `t120-s0-wave-a-oxzen-r2` and was
repaired under independent integration review. The original model artifact is
preserved unchanged in ignored run state.

The repair replaced every unbounded decimal-to-integer conversion with a
correct fixed-chunk parser, connected that parser to JSON integer decoding,
enforced the frozen encoded-byte limit, and applied the existing frozen
experiment/window/bundle and receipt-authority checks to candidate-supplied
CAS and receipt bindings. It did not modify the trusted gate, harness, oracle,
task contract, immutable image, or frozen specification bundle.

The integrated source SHA-256 is
`15d9409494963ba7087c55dd33b181e53516eb6f358333a6d336c975fe9ebf66`.
The unchanged `t120_s0_schema_v1` controller accepted it three times with independent
hidden fixtures under controller bundle
`9ceb6d0fcb754cbebe42067694694f0f69d8e8daf5d731bfa8177d38611abb88`
and immutable image
`458e58fafe9c54b5a93f3d03ee57047cbdeb8c69b8884eb0ff543ed07a1bf400`.
The accepted fixture seeds are recorded in
`stages/s0-controller-gate/IMPLEMENTATION_PROVENANCE.json`.

This establishes only a controller-accepted S0 implementation. It does not
authenticate that supplied `r,w` values came from T118, authorize generator or
verifier execution, create a CAS object or receipt, report a finite PI window,
or support any theorem about PI digits. Those remain later disjoint stages.
