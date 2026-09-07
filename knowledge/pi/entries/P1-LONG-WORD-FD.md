---
id: P1-LONG-WORD-FD
title: Localized full BA-ALA dimension for every fixed word of length at least 49
label: proof sketch
lean: []
file: knowledge/pi/results/intermediate/20260905-fixed-word-full-dimension.md
statement: "Every fixed decimal word w of length m>=49, every omitted digit d occurring in w, A=D10 except d, every c in A intersect {1,...,8}, and every finite w-avoiding prefix P satisfy dim_H(C_w intersect I(P) intersect ALA_(A,c) intersect BA)=d_w. More precisely, for each 0<s<d_w some scale-uniform kappa>0 gives dimension >s. The word stays fixed as s approaches d_w."
does_not_show: "Not-proved:universal-P1-FD/FD-loc/PD/NE;P1-prime;word-lengths-below-49;one-kappa-attaining-full-dimension;pi-CW0/CW9/V1;no-Lean-or-novelty-claim."
source: knowledge/pi/results/intermediate/20260905-fixed-word-full-dimension.md
---
> Every fixed decimal word w of length m>=49,
> every digit d occurring in w, A={0,...,9}\{d}, every c in A intersect
> {1,...,8}, every finite prefix P avoiding w, and every 0<s<d_w admit
> kappa>0 with dim_H(C_w intersect I(P) intersect ALA_(A,c) intersect BA(kappa))>s.
> Consequently the same intersection with BA has dimension d_w for each such
> fixed word and prefix. The explicit threshold 49 is justified below.
