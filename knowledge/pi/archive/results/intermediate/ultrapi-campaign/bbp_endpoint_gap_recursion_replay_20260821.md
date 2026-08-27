# Exact replay audit (2026-08-21 UTC)

Claim status: `experiment` for the exact computation; the accompanying informal
countermodel interpretation remains a `proof sketch`.

Two independently generated OxZen replay artifacts reproduced the canonical
checker stdout byte-for-byte. A trusted-host rerun of
`bbp_endpoint_gap_recursion_20260813_check.py` also exited successfully and
produced the same stdout SHA-256:

`3490c218eeef3e1d572b5ce198298f214bde4f69592c411db948bd78b8c97f8a`

The reproduced facts were:

```text
complete_subwindow_pairs=41924
exact_subwindow_distance_checks=38772
countermodel_checks=33
countermodel_primary_points=1092
countermodel_gap_lower_bound=99/100
countermodel_is_bbp_or_pi=false
asserts_endpoint_gap_law=false
asserts_fixed_return=false
asserts_v1=false
status=PASS
```

The copied checker, canonical problem source, and seven frozen inputs matched
their canonical bytes. Static inspection found no checker mutation or output
spoofing in either independent replay implementation.

This replay confirms only that the finite exact computation is reproducible.
It does not supply an endpoint-gap theorem for the BBP sequence, a fixed-return
theorem, a statement about pi, SP1, or V1. No claim-status upgrade follows.
