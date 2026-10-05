## Summary

<!-- Describe the mathematical or infrastructure change and its scope. -->

## Validation

- [ ] I ran `scripts/check.sh` from the repository root.

## MathlibExt

- [ ] New reusable mathematics is in `MathlibExt`, with tests or diagnostics in
      `MathlibExtTest`.
- [ ] Changed `MathlibExt` code contains no proof holes, custom axioms,
      `native_decide`, or imports from `WantedExt` or `MathlibExtTest`.
- [ ] This pull request does not change `MathlibExt`, or the items above are
      complete.

## WantedExt

- [ ] Deferred results use direct `theorem_wanted` or `def_wanted`
      declarations and directly import `Batteries.Util.ProofWanted`.
- [ ] Changed `WantedExt` code contains no proof holes, custom axioms, or
      `native_decide`.
- [ ] This pull request does not change `WantedExt`, or the items above are
      complete.

## MathlibExtTest

- [ ] Changed tests and diagnostics contain no proof holes or custom axioms.
- [ ] This pull request does not change `MathlibExtTest`, or the item above is
      complete.
