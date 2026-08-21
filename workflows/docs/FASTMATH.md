# FastMath production path

Use Python for orchestration, decoding, small falsification tests, and reference
implementations. Move a production computation to C++ or Rust when it will
visit roughly `10^7` states, hold roughly `10^6` structured objects, emit a
large CNF/certificate, or has already exceeded one minute or one GiB in Python.

The research image includes:

- C++23 (`g++`, CMake, Ninja) with GMP, FLINT, NTL, Eigen, Boost Graph, and
  OpenBLAS development libraries;
- Rust and Cargo;
- Lean/mathlib;
- Kissat plus `drat-trim`;
- nauty/Traces (`geng`);
- Python/PySAT for reference encoders and independent artifact checkers.

The pod keeps the repository's cached Lean 4.30 toolchain and also installs
Lean 4.31 for source artifacts that pin it. Project-local `lean-toolchain`
files select the compiler; proof audits run directly inside the pod and must
not depend on launching a nested Docker or Podman container. OpenCode is pinned
to 1.18.3 in the current image definition and refresh layer.

Run the toolchain check:

```bash
workflows/runtime/fastmath.sh doctor
```

Create a tested starting point instead of writing build plumbing from scratch:

```bash
workflows/runtime/fastmath.sh new cpp knowledge/pi/results/intermediate/scratch/my_search.cpp
workflows/runtime/fastmath.sh new rust knowledge/pi/results/intermediate/scratch/my_search
workflows/runtime/fastmath.sh new milp knowledge/pi/results/intermediate/scratch/my_model.py
```

The templates under `templates/fastmath/` include known-answer self-tests,
streaming compiled loops, structured `experiment` output, and an independent
MILP witness checker. The same commands work in the AllMath pod.

For a Python-dependency-only update, preserve the large cached Lean/mathlib
base and create a small refreshed image:

```bash
scripts/refresh-allmath-research-image.sh \
  localhost/allmath-research:latest localhost/allmath-research:refreshed
scripts/smoke-allmath-research-image.sh localhost/allmath-research:refreshed
```

Promote the refreshed tag only after the smoke test passes. OpenCode
configuration and auth remain runtime mounts; they are not baked into either
image.

Compile, cache, and run one C++ source:

```bash
workflows/runtime/fastmath.sh cpp attacks/617/example.cpp -- --limit 100
FASTMATH_LIBS="flint gmp" workflows/runtime/fastmath.sh cpp exploration/example.cpp
```

`fastmath.sh` supplies Debian linker fallbacks for `flint`, `gmp`, `ntl`,
`openblas`, and the `eigen3` include path when a package has no `pkg-config`
file. The full math-library set is guaranteed in the AllMath pod; a local
`doctor` result reports exactly what is missing on the host.

Run a locked Rust crate with a shared release cache:

```bash
workflows/runtime/fastmath.sh rust fastmath/example/Cargo.toml -- --limit 100
```

Production generators should stream records or DIMACS clauses rather than
holding them as language-level objects. Keep a small Python/reference
implementation and cross-check both implementations on tractable cases.
For sparse binary optimization, start with `sparse_milp.py`: Python constructs
an inspectable sparse matrix while SciPy delegates the search to compiled
HiGHS.
Solver `SAT` needs an independently decoded witness; solver `UNSAT` needs a
retained proof stream checked by an independent proof checker. Neither result
is promoted beyond `experiment` merely because the compiled program is fast.
