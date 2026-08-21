# T116 exact sampled-BBP gcd census

This reproducible workflow computes the canonical synchronized sampled-BBP
normalization gcd with exact Python integers and `Fraction` values. It keeps
the canonical inclusive convention
`bbpPartial(M) = sum_{k=0}^{M} bbpCombinedTerm(k)`; therefore
`Q_0 = bbpPartial(0) = 47/15`.

Run in a disposable directory because the generated `census.json` is about
24 MB and is intentionally not tracked:

```sh
cp census.py verify_census.py /tmp/t116-census/
cd /tmp/t116-census
python3 census.py
python3 verify_census.py
```

Validated 2026-08-21 output hashes:

- `census.py`: `55e4d5b2307205be8ef1c7b56bc45e90122cd9b626d0c8722b433157c1e94f2b`
- `verify_census.py`: `26bf4b60e859c0bde3c8ba41937ea81fdc0164fcc581743b2467039415c31280`
- generated `census.json`: `08e798cede42ae4c9de9ff01df39d4c0929938b188dd68ea7b114fc21a870847`
- records payload: `d3af4c9b9170068fc40e81070b4754fef62a8728ed70a4e0f18707871bc3f413`

The verifier enforces exact ordered unique coverage `N=0..511`, replays the
source equations by a separate four-pole route, checks the T116 prime-support
invariant, and recomputes every stored field and preregistered verdict. Its
successful finite replay is an `experiment`, not a proof of a surviving law.
