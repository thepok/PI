# T150: bounded P21 fixed-rho energy review

Status: `experiment`  
Last audited: 2026-08-22

## Endpoint

P21 is `OPEN/HOLD`.  The frozen statement

```text
b_0,...,b_(D_p-1) nonzero modulo p  =>  E_p^4<=p^3
```

was neither proved nor refuted.  T149 found no finite counterexample and in
fact observed `E_p=0` through `p<65536`, but finite evidence is not a proof.

## Bounded worker review

The direction gate precommitted to at most six substantive P21 memos, with at
least two substantive outputs across each provider.  A route-positive memo
had to provide an independently checkable aggregate fixed-`i` transfer
content/resultant factorization into explicit short convolution factors, or
an equivalent quantitative Toeplitz rank/minor inequality.  Generic pair
counting, a stronger zero-count conjecture, and finite `E=0` evidence did not
qualify.

All six substantive memos were rejected:

| provider/run | memo SHA-256 | principal fatal gap |
|---|---|---|
| `ox-6` | `5975b14e692ee26024fa7789f2b638aa7a330cb6df46739ea75a3c0680ac1a2f` | only `E<=binom(|Z|,2)`; replaces P21 by a stronger zero-count target |
| `oxzen-20` | `9b90934ae9f77f8ce9621b15fee02ae4a467260d542fdaceb9209a85e1995de5` | no aggregate inequality; misclassifies the short-convolution antecedent |
| `oxzen-14` | `5ed7232ed17ae60699cda533a9beed0a5fc9d9654322f72d2fdcf7fb50ca6e97` | assumes the decisive residue-class cover and order lower bound |
| `oxzen-19` | `bf7c490d3c039a14eaed781ec7b73c81fbfa084d77453c89aebf50a0bb5e2e7b` | generic pair counting plus a false quantitative sufficiency claim |
| `oxzen-16` | `de017f5968fdaf3940b35e5d54e21eb8e1d0209f23c99f53e423b6891e5cfa0e` | confuses the fixed sequence `a_n` with its convolution `b_n` |
| `ox-5` | `a3fe959503606ef3efc2e934c2b4584469d2ef694f9895a7322748d861e18e02` | tautological multi-`h` bound and unproved zero-count replacement |

Several memos also repeated incorrect decimal cutoff arguments or contained
algebraic errors.  No result from these memos was promoted.  Empty provider
responses were treated as stubs and were not counted.

## Scope and pivot

This bounded failure is not a mathematical STOP: it proves neither that the
fixed-rho energy statement is false nor that no aggregate transfer method can
work.  It does establish that the present weak-model prompt has exhausted its
useful sample without discovering the required mechanism.  Repeating the
same P21 wave would be an operational rabbit hole.

The next active task therefore returns to T143's logically independent
off-diagonal term and freezes one four-form affine divisor-switch inequality.
Any future proof of that inequality supplies only the off-diagonal power
saving; the diagonal remains open because P21 is on hold.

No diagonal saving, `(D)`, or V1 result is claimed.

V1 remains open.
