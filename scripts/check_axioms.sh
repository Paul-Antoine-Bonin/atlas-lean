#!/usr/bin/env bash
# Inspect parsed sources and compiled declarations for repository-policy violations.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

CHECK_FILE="$(mktemp "${TMPDIR:-/tmp}/atlas-axioms.XXXXXX.lean")"
trap 'rm -f "$CHECK_FILE"' EXIT

for library in MathlibExt MathlibExtTest WantedExt; do
  while IFS= read -r path; do
    module="${path%.lean}"
    module="${module//\//.}"
    printf 'import %s\n' "$module" >>"$CHECK_FILE"
  done < <(find "$library" -type f -name '*.lean' -print | LC_ALL=C sort)
done

cat >>"$CHECK_FILE" <<'LEAN'
import Batteries.Util.ProofWanted
import Lean.Compiler.ImplementedByAttr
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean.Elab.Command

private def trustedAxioms : Array Lean.Name :=
  #[``propext, ``Quot.sound, ``Classical.choice]

private def libraryRoots : Array Lean.Name :=
  #[`MathlibExt, `MathlibExtTest, `WantedExt]

private def libraryOf? (name : Lean.Name) : Option Lean.Name :=
  libraryRoots.find? (·.isPrefixOf name)

private def mayImport (source target : Lean.Name) : Bool :=
  (source == `MathlibExtTest && target == `MathlibExt) ||
    (source == `WantedExt && target == `MathlibExt)

private def containsWantedWrapper (type : Lean.Expr) : Bool :=
  (type.find? fun
    | .const name _ =>
      name == ``ProofWanted || name == ``DefWanted || name == ``DerivedWanted
    | _ => false).isSome

private def normalizeAuditedType
    (auditedConstants : Lean.NameHashSet) (type : Lean.Expr) : Lean.Meta.MetaM Lean.Expr :=
  Lean.Meta.transform type (pre := fun expression => do
    let reduced ← Lean.Meta.withTransparency .reducible <| Lean.Meta.whnf expression
    if reduced != expression then
      return .visit reduced

    if let .const name _ := expression.getAppFn then
      if auditedConstants.contains name then
        let unfolded ← Lean.Meta.withTransparency .all <| Lean.Meta.whnf expression
        if unfolded != expression then
          return .visit unfolded

    pure .continue)

run_cmd do
  let env ← Lean.getEnv
  let mut failed := false
  let mut auditedConstants := Lean.NameHashSet.empty

  for i in [0:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[i]!
    if (libraryOf? moduleName).isSome then
      for name in env.header.moduleData[i]!.constNames do
        auditedConstants := auditedConstants.insert name

  for i in [0:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[i]!
    let some library := libraryOf? moduleName | continue
    let moduleData := env.header.moduleData[i]!

    for imported in moduleData.imports do
      let some importedLibrary := libraryOf? imported.module | continue
      if importedLibrary != library && !mayImport library importedLibrary then
        Lean.logError m!"{moduleName} must not import {imported.module}"
        failed := true

    let mut hasWantedDeclaration := false
    for name in moduleData.constNames do
      let some info := env.find? name | continue
      if info.isUnsafe then
        Lean.logError m!"{name} is an unsafe declaration"
        failed := true
      if (Lean.Compiler.getImplementedBy? env name).isSome then
        Lean.logError m!"{name} uses implemented_by"
        failed := true
      let normalizedType ← liftTermElabM do normalizeAuditedType auditedConstants info.type
      if containsWantedWrapper normalizedType then
        hasWantedDeclaration := true

      let axioms ← Lean.collectAxioms name
      let forbidden :=
        (axioms.filter fun ax => !trustedAxioms.contains ax).qsort Lean.Name.quickLt
      unless forbidden.isEmpty do
        Lean.logError m!"{name} depends on forbidden axioms: {forbidden}"
        failed := true

    if hasWantedDeclaration then
      if library != `WantedExt then
        Lean.logError m!"{moduleName} contains a wanted declaration outside WantedExt"
        failed := true
      unless moduleData.imports.any (·.module == `Batteries.Util.ProofWanted) do
        Lean.logError m!"{moduleName} must directly import Batteries.Util.ProofWanted"
        failed := true

  if failed then
    throwError
      "audited libraries violate the axiom, safety, wanted-declaration, or import policy"
LEAN

lake env lean "$CHECK_FILE"
echo "ok [environment]: compiled libraries satisfy trust and dependency policies."
