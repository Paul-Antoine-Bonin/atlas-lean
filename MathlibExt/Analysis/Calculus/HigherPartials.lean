/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Higher partial derivatives

This file relates coordinate partial derivatives to Fréchet derivatives and proves that mixed
second partial derivatives of a twice continuously differentiable real function commute.
-/

@[expose] public section

namespace MetaMathlibExt

/-- Coordinate partial derivative of `f` along the `i`-th axis.
Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Differential calculus`, entries `partial derivatives` and
`k-th order partial derivatives` (unmapped);
W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9;
stable ref https://en.wikipedia.org/wiki/Partial_derivative. -/
noncomputable def partialDeriv {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i : Fin n) :
    (Fin n → ℝ) → ℝ :=
  fun x => deriv (fun t : ℝ => f (x + t • Pi.single i (1 : ℝ))) 0

/-- Characteristic spec: the partial is the single-variable derivative of the
axis slice.
Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Differential calculus`, entry `partial derivatives` (unmapped);
W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9. -/
theorem partialDeriv_spec {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i : Fin n)
    (x : Fin n → ℝ) :
    partialDeriv f i x =
      deriv (fun t : ℝ => f (x + t • Pi.single i (1 : ℝ))) 0 := rfl

private theorem partialDeriv_hasDerivAt_axis {n : ℕ} (i : Fin n) (x : Fin n → ℝ) :
    HasDerivAt (fun t : ℝ => x + t • Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ)) 0 := by
  simpa only [id_eq, one_smul] using
    ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const (Pi.single i (1 : ℝ))).const_add x

/-- A partial derivative is the Frechet derivative applied to the axis vector.
Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Differential calculus`, entry `partial derivatives` (unmapped);
W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9.

Proves `Wanted` entry `partialDeriv_eq_fderiv_apply`.

Proof: Differentiate the affine coordinate line `t ↦ x + t • Pi.single i 1` and compose with `f`
by the chain rule `HasFDerivAt.comp_hasDerivAt`.
-/
theorem partialDeriv_eq_fderiv_apply {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (i : Fin n) (x : Fin n → ℝ) (hf : DifferentiableAt ℝ f x) :
    partialDeriv f i x = fderiv ℝ f x (Pi.single i (1 : ℝ)) := by
  have hf' : HasFDerivAt f (fderiv ℝ f x)
      (x + (0 : ℝ) • Pi.single i (1 : ℝ)) := by
    simpa using hf.hasFDerivAt
  simpa only [partialDeriv, Function.comp_def] using
    (hf'.comp_hasDerivAt 0 (partialDeriv_hasDerivAt_axis i x)).deriv

/-- For a differentiable function, the coordinate partial derivative is its Fréchet derivative
applied pointwise to the coordinate vector. -/
theorem partialDeriv_eq_fderiv_apply_of_differentiable {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (i : Fin n) (hf : Differentiable ℝ f) :
    partialDeriv f i = fun x => fderiv ℝ f x (Pi.single i (1 : ℝ)) := by
  funext x
  exact partialDeriv_eq_fderiv_apply f i x (hf x)

private theorem partialDeriv_fderiv_apply_differentiable {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (i : Fin n) (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (fun x => fderiv ℝ f x (Pi.single i (1 : ℝ))) := by
  apply Differentiable.clm_apply
  · exact (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  · exact differentiable_const _

private theorem partialDeriv_fderiv_apply_eq {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (i j : Fin n) (x : Fin n → ℝ) (hf : ContDiff ℝ 2 f) :
    fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i (1 : ℝ))) x
        (Pi.single j (1 : ℝ)) =
      fderiv ℝ (fderiv ℝ f) x (Pi.single j (1 : ℝ)) (Pi.single i (1 : ℝ)) := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) x
  have hderiv :=
    ((ContinuousLinearMap.apply ℝ ℝ (Pi.single i (1 : ℝ))).hasFDerivAt.comp
      x hfd.hasFDerivAt).fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply] using
      congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single j (1 : ℝ))) hderiv

/-- An iterated coordinate partial derivative is the second Fréchet derivative applied to the
corresponding pair of coordinate vectors. -/
theorem partialDeriv_partialDeriv_eq_fderiv_fderiv {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (i j : Fin n) (x : Fin n → ℝ) (hf : ContDiff ℝ 2 f) :
    partialDeriv (partialDeriv f i) j x =
      fderiv ℝ (fderiv ℝ f) x (Pi.single j (1 : ℝ)) (Pi.single i (1 : ℝ)) := by
  calc
    partialDeriv (partialDeriv f i) j x =
        partialDeriv (fun y => fderiv ℝ f y (Pi.single i (1 : ℝ))) j x := by
      rw [partialDeriv_eq_fderiv_apply_of_differentiable f i
        (hf.differentiable (by norm_num))]
    _ = fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i (1 : ℝ))) x
        (Pi.single j (1 : ℝ)) :=
      partialDeriv_eq_fderiv_apply _ j x (partialDeriv_fderiv_apply_differentiable f i hf x)
    _ = fderiv ℝ (fderiv ℝ f) x (Pi.single j (1 : ℝ)) (Pi.single i (1 : ℝ)) :=
      partialDeriv_fderiv_apply_eq f i j x hf

/-- Iterated partials commute for `C^2` functions (Clairaut's theorem).
Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Differential calculus`, entry `k-th order partial derivatives` (unmapped);
W. Rudin, Principles of Mathematical Analysis, 3rd ed., Theorem 9.41 (pp. 235–236).

Proves `Wanted` entry `iterated_partialDeriv_commute`.

Proof: Rewrite both iterated partials through the Fréchet bridge above, then apply Mathlib's
`ContDiffAt.isSymmSndFDerivAt`, Schwarz's theorem as stated in Wikipedia, "Symmetry of second
derivatives".
-/
theorem iterated_partialDeriv_commute {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (i j : Fin n) (x : Fin n → ℝ) (hf : ContDiff ℝ 2 f) :
    partialDeriv (partialDeriv f i) j x =
      partialDeriv (partialDeriv f j) i x := by
  rw [partialDeriv_partialDeriv_eq_fderiv_fderiv f i j x hf,
    partialDeriv_partialDeriv_eq_fderiv_fderiv f j i x hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

end MetaMathlibExt
