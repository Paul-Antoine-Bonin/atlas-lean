import MathlibExt.NumberTheory.NumberField.RayClass.FrobeniusGenerators

/-!
# Tests for unramified Frobenius generators (ATLAS N402, Stage B1)
-/

@[expose] public noncomputable section

open NumberField

namespace N402FrobeniusGeneratorsTest

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- A generic consumer of `frobeniusAtCoprimePrime_spec`: the exhibited prime
lies above `p`, is unramified, and the chosen value is an arithmetic Frobenius
there. -/
example (m : Modulus K) (h : m.IsUnramifiedOutside L) (p : m.CoprimePrimes) :
    ∃ Q : Ideal (𝓞 L), ∃ _ : Q.IsPrime,
      Q.LiesOver p.val.asIdeal ∧ Algebra.IsUnramifiedAt (𝓞 K) Q ∧
        IsArithFrobAt (𝓞 K) (m.frobeniusAtCoprimePrime (L := L) h p) Q := by
  obtain ⟨Q, -, hover, hunramm, hfrob⟩ :=
    m.frobeniusAtCoprimePrime_spec (L := L) h p
  exact ⟨Q.1, Q.property.1, hover, hunramm, hfrob⟩

/-- The free-group map computes on generators (`freeGroupToGal_of` is `simp`). -/
example (m : Modulus K) (h : m.IsUnramifiedOutside L) (p : m.CoprimePrimes) :
    m.freeGroupToGal (L := L) h (FreeGroup.of p) =
      m.frobeniusAtCoprimePrime (L := L) h p := by
  simp

end N402FrobeniusGeneratorsTest
