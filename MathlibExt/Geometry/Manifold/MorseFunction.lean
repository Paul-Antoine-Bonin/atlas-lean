/-
Authors: @toskua, Avocado, Adam Kiezun, Muse Spark 1.3
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import MathlibExt.Geometry.Manifold.MorseTheory

@[expose] public section

open scoped Manifold ContDiff

namespace MathlibExt.Geometry.Manifold.ReebSphereWanted

open MathlibExt.Geometry.Manifold.MorseTheoryWanted

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- `f : M → ℝ` is Morse when it is `C^∞` and every critical point admits a local
`C^∞` diffeomorphism to the normal form `f p + morseQuadratic k n`. -/
def IsMorseFunction (f : M → ℝ) : Prop :=
  ContMDiff I (𝓘(ℝ, ℝ)) (⊤ : ℕ∞) f ∧
    ∀ p : M, mfderiv I (𝓘(ℝ, ℝ)) f p = 0 →
      ∃ (k : ℕ) (_ : k ≤ Module.finrank ℝ E)
        (φ : M → EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
        IsLocalDiffeomorphAt I (𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
            (⊤ : ℕ∞) φ p ∧
          φ p = 0 ∧
            ∃ (U : Set M) (_ : IsOpen U) (_ : p ∈ U),
              ∀ q ∈ U, f q = f p + morseQuadratic k (Module.finrank ℝ E) (φ q)

end MathlibExt.Geometry.Manifold.ReebSphereWanted
