# MathlibExt

`MathlibExt` contains reusable, fully proved mathematics that is not yet in
Mathlib.

Follow Mathlib's subject taxonomy, naming, namespace, documentation, and
import style. Keep imports narrow and put tests, benchmarks, negative examples,
and diagnostics in `MathlibExtTest`.

Every module must be free of `sorry`, `sorryAx`, `admit`, custom axioms, and
`native_decide`. It may use only Lean's standard logical axioms and must not
import `WantedExt` or `MathlibExtTest`.
