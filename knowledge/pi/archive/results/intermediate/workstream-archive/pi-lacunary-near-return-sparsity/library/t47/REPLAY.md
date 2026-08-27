# T47 replay

This artifact is a rigorous `proof sketch` note about an artificial-stream
A13/A14 sibling. The vendored T14 and T37 files are byte-identical copies of
the accumulated kernel-checked inputs. No new Lean theorem is claimed.

From a directory containing only these delivered artifacts, run:

```sh
python3 verify_note.py
sha256sum -c DEPENDENCIES.sha256
```

The first command checks the immutable statement, kernel-source locators,
finite algebra used in the report, and the terminal quantified-clause
contract. The second checks all pinned inputs. `SHA256SUMS` pins the report,
verifier, replay instructions, and dependency manifest.
