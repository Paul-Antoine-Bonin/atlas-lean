/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
AMR-022-2035: if `Γ` is a continuum receding to infinity, then
`limsup_{z → ∞ on Γ} log |f z| / log M(|z|) ≥ -A` for an absolute
constant `A`. Is `A = 1`?

Here `f` is entire (ambient context from Hayman) and `M(r)` is the
maximum modulus on the circle of radius `r`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.EReal.Basic
public import MathlibExt.Analysis.Complex.Wiman

@[expose] public section

namespace MathlibExt.Analysis.ContinuumLimsupConstantWanted

/-! Source record `AMR-022-2035`. -/
open Filter

/-- An entire function: complex-differentiable everywhere.
Interpretation gap: the record gives `f` entire only as ambient
context from Hayman; we take it as an explicit hypothesis. -/
def Entire (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f Set.univ

/- Maximum modulus `M(r)` is MathlibExt's `Complex.wimanMaximumModulus`,
the supremum of `‖f‖` on the sphere of radius `|r|`. -/
/-- A continuum receding to infinity: closed, connected, and unbounded.
Continuum is read as closed connected; receding to infinity is read as
unbounded. Compactness at finite scales is not required, since an
unbounded set is never compact. -/
def RecedesToInf (Γ : Set ℂ) : Prop :=
  IsClosed Γ ∧ IsConnected Γ ∧ ¬Bornology.IsBounded Γ

/-- The ratio `log |f z| / log M(|z|)` in `EReal`, with zeros of `f`
mapped to `⊥` (the genuine logarithm of a zero modulus is `-∞`).
This avoids the conditionally complete `Filter.limsup` on `ℝ` collapsing
the `-∞` case to `0`. Division by `log M(|z|) = 0` retains the real
division-by-zero junk value `0`; that convention is recorded in the
metadata gaps. -/
noncomputable def Ratio (f : ℂ → ℂ) (z : ℂ) : EReal :=
  if f z = 0 then (⊥ : EReal)
  else ((Real.log ‖f z‖ / Real.log (Complex.wimanMaximumModulus f ‖z‖) : ℝ) : EReal)

/-- [AMR-022-2035] Along every continuum receding to infinity, the
limsup at infinity of `log |f z| / log M(|z|)` is at least `-1`,
i.e. the absolute constant is `A = 1`. The limit is taken along the
filter `cocompact ⊓ 𝓟 Γ` (at infinity on `Γ`), in `EReal` so that a
ratio tending to `-∞` is not collapsed to `0`. The function is required
to be transcendental (`Complex.IsTranscendental`, the standing Hayman
hypothesis): the identically zero function is an immediate
counterexample, since its ratio is constantly `⊥`. -/
noncomputable def conjecture : Prop :=
  ∀ f : ℂ → ℂ, Entire f → Complex.IsTranscendental f →
    ∀ Γ : Set ℂ, RecedesToInf Γ →
    (-1 : EReal) ≤ Filter.limsup (Ratio f) (Filter.cocompact ℂ ⊓ 𝓟 Γ)

/--
Resolved true: Hayman and Kjellberg (Studies in Pure Mathematics, Birkhauser 1983) proved that
for entire f and every K > 1 all components of {ln|f| + K ln M(|z|,f) < 0} are bounded, so A =
1: the limsup along any unbounded continuum is >= -1 (Hayman-Lingham Update 2.35;
arXiv:0801.0692). Source: A. Eremenko and J. K. Langley, Meromorphic functions of one complex
variable. A survey, arXiv:0801.0692 (2008), https://arxiv.org/abs/0801.0692; Walter K. Hayman
and Eleanor F. Lingham, Research Problems in Function Theory (New Edition), arXiv:1809.07200v2
(2018), https://arxiv.org/abs/1809.07200. Moved from
`OpenConjectures/Analysis/ContinuumLimsupConstant`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.ContinuumLimsupConstantWanted
