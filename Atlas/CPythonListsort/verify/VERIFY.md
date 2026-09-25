# Verification

Run all commands from the ATLAS repository root.  The excerpt check requires
network access to the pinned CPython commit; the trust-boundary check and Lean
build are local after Lake has fetched the pinned dependencies.

```sh
cd Atlas/CPythonListsort
python3 verify/verify_excerpts.py
python3 verify/verify_trust_boundary.py
lake build
```

Expected excerpt-check output:

```text
verified sources/listobject-excerpts.md
verified sources/listsort.md
```

Expected trust-boundary output:

```text
verified native_decide trust boundary: 12 named compiler-checked regressions, no Lean consumers
```

`lake build` compiles the `Code` library, including all five layers imported
by `Code.lean`.  It should exit successfully with no `sorry` declarations.

To inspect the axioms of the five headline theorems, run this additional
temporary-file check:

```sh
check_dir="$(mktemp -d /tmp/cpython-listsort-axioms.XXXXXX)"
check_file="$check_dir/CheckAxioms.lean"
trap 'rm -rf "$check_dir"' EXIT
cat >"$check_file" <<'EOF'
import Code
#print axioms CPythonListsort.listsort_safe
#print axioms CPythonListsort.listsort_correct_keyed
#print axioms CPythonListsort.listsort_correct
#print axioms CPythonListsort.listSort_mergeMemory_safe
#print axioms CPythonListsort.listsort_mergeCost_bound
EOF
lake env lean "$check_file"
rm -rf "$check_dir"
trap - EXIT
```

The principal theorems may report Lean/Mathlib's standard logical axioms; none
may report `Lean.ofReduceBool`.  The twelve declarations allowed by
`verify_trust_boundary.py` are compiler-checked regression leaves and cannot
be dependencies of another Lean declaration.
