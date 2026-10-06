# CSLibExt

`CSLibExt` contains reusable, fully proved computer-science developments built
on Mathlib and `MathlibExt`.

Keep imports narrow and put tests and diagnostics in `CSLibExtTest`. Every
module must be free of `sorry`, `sorryAx`, `admit`, custom axioms, and
`native_decide`. It may import `MathlibExt`, but not `WantedExt` or either test
library.
