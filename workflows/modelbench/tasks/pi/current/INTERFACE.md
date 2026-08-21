# Wave AI pinned BBP forced-orbit interface

Use namespace `Theory.PiDigits.T106BBPForcedOrbit` and these definitions
verbatim.  Do not change the sampling factor, indexing, codomain, or scaling.

```lean
def sampledBBPValue (N : ℕ) : ℝ :=
  T100BBPRealBridge.bbpRealPartial (7 * N)

def sampledBBPOrbit (N : ℕ) : ℝ :=
  Int.fract ((10 : ℝ) ^ N * sampledBBPValue N)

def sampledBBPError (N : ℕ) : ℝ :=
  (10 : ℝ) ^ N * (Real.pi - sampledBBPValue N)

def sampledBBPForcing (N : ℕ) : ℝ :=
  (10 : ℝ) ^ (N + 1) *
    (sampledBBPValue (N + 1) - sampledBBPValue N)

def sampledBBPForcingRat (N : ℕ) : ℚ :=
  (10 : ℚ) ^ (N + 1) *
    (T77SelectedPadicDefectShell.bbpPartial (7 * (N + 1)) -
      T77SelectedPadicDefectShell.bbpPartial (7 * N))

def bbpErrorRatio : ℝ := 10 / 16 ^ 7
```

`bbpPartial K` is inclusive.  Advancing from `7*N` to `7*(N+1)` adds exactly
the seven terms indexed `7*N+1` through `7*N+7`, represented by
`sum j in Finset.range 7, bbpCombinedTerm (7*N+j+1)`.  Any `range 8`, index
`7*N`, altered numerator, or altered sampling convention is a specification
failure even if Lean compiles.

T104 proves the BBP series identity.  Instantiate T100 tail bounds with
`T104BBPSeriesIdentity.bbpRealTerm_hasSum_pi`.  No task may claim mixing,
density, normality, SP1, or V1 without retaining its explicit cancellation
or coverage hypothesis.
