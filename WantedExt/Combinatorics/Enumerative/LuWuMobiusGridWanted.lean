/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false

@[expose] public section

namespace MetaMathlibExt

open scoped BigOperators

/- Primary source: Wentao T. Lu and F. Y. Wu, "Close-packed dimers on
nonorientable surfaces", arXiv:cond-mat/0110035v3
(<https://arxiv.org/abs/cond-mat/0110035>).
Grid/generating-function display (gen), lines 145-163;
odd-column Mobius-grid formula (Mob-2), lines 184-188;
M-even Mobius-strip setup with grid dimensions (2M, N) and the twisted
adjacency matrix, lines 264-311.
Only the unweighted odd-column Mobius-grid formula is formalized here;
the Klein-bottle and even-N variants are not encoded. -/

/-- Vertices of the `2 * M`-by-`N` Mobius grid. -/
def MobiusGridVertex (M N : ℕ) : Type :=
  Fin (2 * M) × Fin N

/-- Labeled edges of the Mobius grid. The three labeled constructors preserve
the primary source's edge-labeled dimer multiplicities: distinct labels stay
distinct even when small dimensions make endpoint pairs coincide. -/
inductive MobiusGridEdge (M N : ℕ) where
  | horizontal (row : Fin (2 * M)) (col : Fin (N - 1)) : MobiusGridEdge M N
  | vertical (row : Fin (2 * M - 1)) (col : Fin N) : MobiusGridEdge M N
  | seam (row : Fin (2 * M)) : MobiusGridEdge M N
deriving DecidableEq, Fintype

/-- Incidence by natural-coordinate equations. -/
def MobiusGridIncident {M N : ℕ} (e : MobiusGridEdge M N)
    (v : MobiusGridVertex M N) : Prop :=
  match e with
  | .horizontal row col =>
      v.1.val = row.val ∧ (v.2.val = col.val ∨ v.2.val = col.val + 1)
  | .vertical row col =>
      v.2.val = col.val ∧ (v.1.val = row.val ∨ v.1.val = row.val + 1)
  | .seam row =>
      (v.1.val = row.val ∧ v.2.val = N - 1) ∨
        (v.1.val = 2 * M - 1 - row.val ∧ v.2.val = 0)

/-- A perfect matching is a finset of labeled edges incident to every vertex
exactly once. -/
def IsMobiusGridPerfectMatching {M N : ℕ}
    (S : Finset (MobiusGridEdge M N)) : Prop :=
  ∀ v : MobiusGridVertex M N, ∃! e, e ∈ S ∧ MobiusGridIncident e v

/-- Number of perfect matchings of the `2 * M`-by-`N` Mobius grid. -/
noncomputable def mobiusGridPerfectMatchingCount (M N : ℕ) : ℕ :=
  by
    classical
    exact Fintype.card
      {S : Finset (MobiusGridEdge M N) //
        IsMobiusGridPerfectMatching (M := M) (N := N) S}

/-- Unweighted odd-column Lu-Wu perfect-matching formula for the Mobius grid. -/
theorem_wanted lu_wu_mobius_grid_perfect_matching_count {M N : ℕ}
    (hM : 0 < M) (hN : 0 < N) (hNodd : Odd N) :
    (mobiusGridPerfectMatchingCount M N : ℝ) =
      Complex.re
        ((1 - Complex.I) *
          ∏ s ∈ Finset.Icc 1 M, ∏ r ∈ Finset.Icc 1 N,
            (2 * Complex.I * (-1 : ℂ) ^ (M + s + 1) *
                ↑(Real.sin ((((4 * r - 1 : ℕ) : ℝ)) * Real.pi / (2 * (N : ℝ)))) +
              2 * ↑(Real.cos ((s : ℝ) * Real.pi / (2 * (M : ℝ) + 1)))))

end MetaMathlibExt
