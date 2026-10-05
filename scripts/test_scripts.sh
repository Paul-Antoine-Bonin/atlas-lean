#!/usr/bin/env bash
# Regression tests for repository-maintenance scripts. These tests need only
# Bash and standard Unix tools; they intentionally do not invoke Lean.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/atlas-scripts.XXXXXX")"
trap 'rm -rf "$TMP_ROOT"' EXIT

fail() {
  echo "FAIL [scripts]: $*" >&2
  exit 1
}

reset_fixture() {
  rm -rf "$TMP_ROOT/repo"
  mkdir -p "$TMP_ROOT/repo"/{MathlibExt,MathlibExtTest,WantedExt,scripts}
  cp "$REPO_ROOT/lakefile.toml" "$TMP_ROOT/repo/"
  cp "$REPO_ROOT/scripts/check_health.sh" "$TMP_ROOT/repo/scripts/"
}

expect_pass() {
  local description="$1"
  if ! "$TMP_ROOT/repo/scripts/check_health.sh" >"$TMP_ROOT/output.log" 2>&1; then
    cat "$TMP_ROOT/output.log" >&2
    fail "$description failed"
  fi
}

expect_failure() {
  local description="$1" pattern="$2"
  if "$TMP_ROOT/repo/scripts/check_health.sh" >"$TMP_ROOT/output.log" 2>&1; then
    fail "$description unexpectedly passed"
  fi
  grep -q -- "$pattern" "$TMP_ROOT/output.log" || {
    cat "$TMP_ROOT/output.log" >&2
    fail "$description produced the wrong diagnostic"
  }
}

reset_fixture
expect_pass "empty scaffold"

reset_fixture
printf '%s\n' '[[lean_lib]]' 'name = "Undocumented"' >>"$TMP_ROOT/repo/lakefile.toml"
expect_failure "library without policy" 'do not match policy'

reset_fixture
printf '%s\n' 'axiom hidden : Prop' >"$TMP_ROOT/linked.lean"
ln -s "$TMP_ROOT/linked.lean" "$TMP_ROOT/repo/MathlibExt/Linked.lean"
expect_failure "symlinked Lean source" 'symlinked paths'

FAKE_BIN="$TMP_ROOT/bin"
FAKE_LAKE_LOG="$TMP_ROOT/lake.log"
mkdir -p "$FAKE_BIN"
cat >"$FAKE_BIN/lake" <<'SH'
#!/usr/bin/env bash
printf '%s\n' "$*" >>"$FAKE_LAKE_LOG"
printf '%s\n' "${FAKE_LAKE_OUTPUT:-Build completed successfully.}"
SH
chmod +x "$FAKE_BIN/lake"
export FAKE_LAKE_LOG

if ! PATH="$FAKE_BIN:$PATH" "$REPO_ROOT/scripts/check_diagnostics.sh" \
  >"$TMP_ROOT/output.log" 2>&1; then
  cat "$TMP_ROOT/output.log" >&2
  fail "clean compiler diagnostics failed"
fi
grep -qx 'build MathlibExt WantedExt MathlibExtTest' "$FAKE_LAKE_LOG" ||
  fail "compiler diagnostics built the wrong targets"

if env PATH="$FAKE_BIN:$PATH" \
  FAKE_LAKE_OUTPUT="warning: MathlibExt/Bad.lean:1:1: declaration uses 'sorry'" \
  "$REPO_ROOT/scripts/check_diagnostics.sh" >"$TMP_ROOT/output.log" 2>&1; then
  fail "sorry diagnostic unexpectedly passed"
fi
grep -q 'forbidden compiler diagnostic' "$TMP_ROOT/output.log" ||
  fail "sorry diagnostic produced the wrong failure"

if env PATH="$FAKE_BIN:$PATH" \
  FAKE_LAKE_OUTPUT='warning: Using `native_decide` is not allowed in mathlib' \
  "$REPO_ROOT/scripts/check_diagnostics.sh" >"$TMP_ROOT/output.log" 2>&1; then
  fail "native_decide diagnostic unexpectedly passed"
fi
grep -q 'forbidden compiler diagnostic' "$TMP_ROOT/output.log" ||
  fail "native_decide diagnostic produced the wrong failure"

echo "ok [scripts]: repository policy regression tests passed."
