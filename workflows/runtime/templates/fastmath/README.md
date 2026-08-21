# FastMath worker templates

Create a problem-local starting point without overwriting existing work:

```bash
workflows/runtime/fastmath.sh new cpp work/my_search.cpp
workflows/runtime/fastmath.sh new rust work/my_search
workflows/runtime/fastmath.sh new milp work/my_model.py
```

Immediately run the included known-answer test:

```bash
workflows/runtime/fastmath.sh cpp work/my_search.cpp -- --self-test
workflows/runtime/fastmath.sh rust work/my_search/Cargo.toml -- --self-test
.venv/bin/python work/my_model.py --self-test
```

The C++ and Rust templates keep enumeration in a compiled streaming loop. The
MILP template keeps model construction inspectable in Python while delegating
the solve to compiled HiGHS through SciPy. Replace the toy kernel only after
pinning at least two known-answer cases, including one adversarial mutation.

Keep outputs labeled `experiment`. A decoded SAT/MILP witness needs an
independent checker; an UNSAT/infeasible result needs a retained, independently
checked certificate before it can support a proof claim.
