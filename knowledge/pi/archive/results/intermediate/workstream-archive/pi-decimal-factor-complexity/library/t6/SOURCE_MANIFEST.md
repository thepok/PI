# T6 pi digit source manifest

## Canonical statement

- File: `knowledge/pi/statements/pi-decimal-factor-complexity.txt`
- Required and verified SHA-256: `e2b6c9375936a97fe6cdd10c3f014613267f3c491935b536c6ec016c5f501e43`
- Relevant convention: contiguous factors beginning at arbitrary fractional-digit positions; the integer digit `3` is excluded.

## Primary digit source

- URL: <https://files.pilookup.com/pi/2000000.txt>
- Retrieved: 2026-07-22 UTC
- Retrieved byte count: `2000002`
- Retrieved-file SHA-256: `f533022c5d2a21db137b158345c6276355e89b301d76d1531c1ca26f9a026612`
- Format verified by code: exactly `3.` followed by 2,000,000 ASCII fractional digits, with no trailing newline.

## Second-host overlap source

- URL: <https://www.angio.net/pi/digits/pi1000000.txt>
- Retrieved: 2026-07-22 UTC
- Retrieved byte count: `1000003`
- Retrieved-file SHA-256: `b50ea720602439dcb8a56265b75fadfa4d0a0fbd46d9705693dde14b8a053fb0`
- Format verified by code: exactly `3.` followed by 1,000,000 ASCII fractional digits and one trailing newline.
- Cross-check: after removing the trailing newline, all one million fractional digits agree byte-for-byte with the primary source. The final 11 required digits are pinned by the complete primary-source hash rather than covered by this overlap.
- Independence boundary: the different hosts and matching bytes provide a useful corruption cross-check, but no claim is made that the hosts generated their digits independently or lack a common upstream source. The complete primary download is the pinned source required by this experiment.

## Delivered extraction

- File: `pi_fractional_1000011.txt`
- Contents: exactly the first 1,000,011 fractional digits, without `3.`, whitespace, or trailing newline.
- Byte count: `1000011`
- SHA-256: `3d11a0e07b0fe7fbc6cb78dbc99afbeec8cfb277c64a559463822da236aff779`
- Why 1,000,011: the largest grid point uses `N=1,000,000`, `n=12`, and therefore ends at fractional digit `N+n-1=1,000,011`.

`python3 run_experiment.py prepare --output pi_fractional_1000011.txt` downloads both pinned files, verifies their hashes and formats, checks their complete overlap, extracts the delivered prefix, and verifies its hash.
