# GP-0002 CI verification

- Commit under test: `27669ba9ae5123c24033a440a7639d2e3262a9b9`
- Run ID: `32524669644`
- Run attempt: `1`
- Runner: `ubuntu-latest`
- Lean setup outcome: `success`
- Isolated T110 build exit: `1`
- Deterministic promotion exit: `125`
- Promotion changed canonical files: `false`
- Strict repository gate exit: `125`

## Isolated T110 build output (last 400 lines)

```text
✖ [2/2] Running TheoryLib.PiQuantitativeBlockHitting.T110T110PostT17CancellationCriterion
error: no such file or directory (error code: 4294967294)
  file: /home/runner/work/PI/PI/TheoryLib/PiQuantitativeBlockHitting/T110T110PostT17CancellationCriterion.lean
Some required targets logged failures:
- TheoryLib.PiQuantitativeBlockHitting.T110T110PostT17CancellationCriterion
error: build failed
```

## Deterministic promotion output

```text
not run: isolated T110 build failed
```

## Strict repository gate output (last 400 lines)

```text
not run: isolated T110 build failed
```

RESULT: FAIL
