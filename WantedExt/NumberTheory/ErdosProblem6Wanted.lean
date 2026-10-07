/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 6
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Range
public import MathlibExt.NumberTheory.PrimeGap

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem6Wanted

/-! Source record `FC-ErdosProblem6`, ported from FormalConjectures
`ErdosProblems/6.lean` (`theorem erdos_6`) and checked against
erdosproblems.com/6. -/

def conjecture : Prop :=
  {n | primeGap n < primeGap (n + 1) ∧ primeGap (n + 1) < primeGap (n + 2)}.Infinite

/--
Resolved true: Solved: Banks-Freiberg-Turnage-Butterbaugh via Maynard-Tao machinery. Source:
William D. Banks, Tristan Freiberg, and Caroline L. Turnage-Butterbaugh, Consecutive primes in
tuples, Acta Arith. 167 (2015), 261-266; arXiv:1311.7003, https://arxiv.org/abs/1311.7003. Moved
from `OpenConjectures/NumberTheory/ErdosProblem6`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.ErdosProblem6Wanted
