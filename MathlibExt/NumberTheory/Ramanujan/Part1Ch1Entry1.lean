/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch1

namespace Entry1Magicsquare3

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 1, Entry 1. -/
theorem ramanujan_part1_ch1_entry1_magicsquare3
    {n : ℕ} (_hn : 0 < n)
    (a b : Fin n → ℕ)
    (L R : Fin n → Fin n → Fin n)
    (hL_row : ∀ i : Fin n, Function.Bijective (L i))
    (hL_col : ∀ j : Fin n, Function.Bijective (fun i : Fin n => L i j))
    (hL_diag : Function.Bijective (fun i : Fin n => L i i))
    (hL_anti : Function.Bijective (fun i : Fin n => L i ⟨n - 1 - i.val, by omega⟩))
    (hR_row : ∀ i : Fin n, Function.Bijective (R i))
    (hR_col : ∀ j : Fin n, Function.Bijective (fun i : Fin n => R i j))
    (hR_diag : Function.Bijective (fun i : Fin n => R i i))
    (hR_anti : Function.Bijective (fun i : Fin n => R i ⟨n - 1 - i.val, by omega⟩))
    (_hPair : Function.Bijective (fun p : Fin n × Fin n => (L p.1 p.2, R p.1 p.2))) :
    ∃ S : ℕ,
      (∀ i : Fin n, (∑ j : Fin n, (a (L i j) + b (R i j))) = S)
      ∧ (∀ j : Fin n, (∑ i : Fin n, (a (L i j) + b (R i j))) = S)
      ∧ ((∑ i : Fin n, (a (L i i) + b (R i i))) = S)
      ∧ ((∑ i : Fin n,
          (a (L i ⟨n - 1 - i.val, by omega⟩) + b (R i ⟨n - 1 - i.val, by omega⟩))) = S) := by
  refine ⟨(∑ k : Fin n, a k) + (∑ k : Fin n, b k), ?_, ?_, ?_, ?_⟩
  · intro i
    simp only [Finset.sum_add_distrib, (hL_row i).sum_comp a, (hR_row i).sum_comp b]
  · intro j
    simp only [Finset.sum_add_distrib, (hL_col j).sum_comp a, (hR_col j).sum_comp b]
  · simp only [Finset.sum_add_distrib, hL_diag.sum_comp a, hR_diag.sum_comp b]
  · simp only [Finset.sum_add_distrib, hL_anti.sum_comp a, hR_anti.sum_comp b]

end Entry1Magicsquare3

end MathlibExt.NumberTheory.Ramanujan.Part1Ch1
