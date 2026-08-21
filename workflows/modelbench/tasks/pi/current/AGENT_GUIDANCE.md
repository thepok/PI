# Pi BBP transfer wave

Work only in the isolated task directory. Create `Contribution.lean` immediately and compile it against the copied Lean project. Use the exact theorem name and proposition in the task; do not rename, weaken, strengthen, or replace it with an imported result.

Reuse the canonical T104, T106, T26, T75, and T37 interfaces. Do not re-prove T106 or alter its sevenfold sampling. No `sorry`, `admit`, `native_decide`, new axiom, `opaque`, `constant`, metaprogramming, syntax extension, unsafe declaration, or compiler-trusting shortcut is allowed. Comments do not satisfy contracts.

Every cancellation, density, irrationality-measure, or V1 premise must remain explicit. Never claim unconditional cancellation, density, mixing, normality, digit occurrence, or V1. Circle-density work must stay in `UnitAddCircle`; ordinary real distance is unsafe at zero/one.

Write a short `REPORT.md` stating what compiled and what remains conditional. Compiler failure is not a mathematical negative result.
