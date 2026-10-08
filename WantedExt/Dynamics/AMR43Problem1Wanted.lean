/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# AMR 43, Problem 1: Hochman aperiodic conjugacy question
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Dynamics.SymbolicDynamics.FullShift

@[expose] public section

namespace MathlibExt.Dynamics.AMR43Problem1Wanted

open SymbolicDynamics.FullShift

/-! Source record `AMR-043-0001__4400001`. -/

/-- [AMR-043-0001] Full two-shift space `X = {0,1}^Z`. -/
abbrev X : Type := FullShiftSpace 2

/-- [AMR-043-0001] Ambient space for `Y`: all `Z`-indexed sequences over
three symbols. -/
abbrev YAmb : Type := FullShiftSpace 3

/-- [AMR-043-0001] The mixing shift of finite type `Y`: sequences with no
equal adjacents. -/
def Y : Set YAmb := { y | ∀ i : ℤ, y i ≠ y (i + 1) }

/-- [AMR-043-0001] Aperiodic part of `X`: `X \ Per(X)`. -/
def AperiodicX : Set X := (Function.periodicPts (unitShift 2))ᶜ

/-- [AMR-043-0001] Aperiodic part of `Y`: admissible sequences that are not
periodic. -/
def AperiodicY : Set YAmb := Y \ Function.periodicPts (unitShift 3)

private theorem unitShift_mem_periodicPts_iff {N : ℕ} (x : FullShiftSpace N) :
    unitShift N x ∈ Function.periodicPts (unitShift N) ↔
      x ∈ Function.periodicPts (unitShift N) := by
  constructor
  · rintro ⟨n, hn, hper⟩
    refine ⟨n, hn, ?_⟩
    apply (shiftHomeomorph N).injective
    change unitShift N ((unitShift N)^[n] x) = unitShift N x
    rw [(Function.Commute.self_iterate (unitShift N) n).eq]
    exact hper
  · rintro ⟨n, hn, hper⟩
    exact ⟨n, hn, hper.apply⟩

/-- [AMR-043-0001] Shift restricted to the aperiodic part of `X`. -/
def shiftXRes (a : ↥AperiodicX) : ↥AperiodicX :=
  ⟨unitShift 2 a, by
    exact fun h ↦ a.property
      ((unitShift_mem_periodicPts_iff (N := 2) (a : X)).mp h)⟩

/-- [AMR-043-0001] Shift restricted to the aperiodic part of `Y`. -/
def shiftYRes (a : ↥AperiodicY) : ↥AperiodicY :=
  ⟨unitShift 3 a, by
    have ha : (a : YAmb) ∈ Y ∧ (a : YAmb) ∉ Function.periodicPts (unitShift 3) :=
      a.property
    constructor
    · change ∀ i : ℤ, unitShift 3 (a : YAmb) i ≠ unitShift 3 (a : YAmb) (i + 1)
      intro i
      simpa [unitShift_apply, add_assoc, add_comm, add_left_comm] using ha.1 (1 + i)
    · exact fun h ↦ ha.2
        ((unitShift_mem_periodicPts_iff (N := 3) (a : YAmb)).mp h)⟩

/-- [AMR-043-0001] Hochman problem 1: are `X \ Per(X)` and `Y \ Per(Y)`
topologically conjugate, i.e. is there a homeomorphism intertwining the
shifts? -/
def conjecture : Prop :=
  ∃ e : Homeomorph ↥AperiodicX ↥AperiodicY,
    ∀ a : ↥AperiodicX, e (shiftXRes a) = shiftYRes (e a)

/--
Resolved false: Salo (arXiv:2104.09860, accepted in Proc. London Math. Soc.) proves every
conjugacy between infinite transitive SFTs minus periodic points extends to a conjugacy of the
SFTs; since the full 2-shift has fixed points and the proper 3-colouring shift has none, the
aperiodic parts are not conjugate. Source: Ville Salo, Conjugacy of transitive SFTs minus
periodic points, Proc. London Math. Soc. (accepted; arXiv v3 2023), arXiv:2104.09860,
https://arxiv.org/abs/2104.09860. Moved from `OpenConjectures/Dynamics/AMR43Problem1`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Dynamics.AMR43Problem1Wanted
