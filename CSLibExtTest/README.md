# CSLibExtTest

`CSLibExtTest` contains tests and diagnostics for public `CSLibExt` APIs. It
may import `CSLibExt` and `MathlibExt`, but production libraries must not import
it.

Tests should exercise meaningful public behavior, including boundary values,
simplification, decoding failures, and expected elaboration failures when
those protect against plausible regressions.
