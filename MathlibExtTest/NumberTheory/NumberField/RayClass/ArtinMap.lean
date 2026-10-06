import MathlibExt.NumberTheory.NumberField.RayClass.ArtinMap

/-!
# Tests for the Artin map by descent (ATLAS N402, Stage B2)
-/

@[expose] public noncomputable section

open NumberField

namespace N402ArtinMapTest

variable {K : Type*} [Field K] [NumberField K]
variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]

/-- The kernel containment applies to kernel elements. -/
example (m : Modulus K) (h : m.IsUnramifiedOutside L)
    (x : FreeGroup m.CoprimePrimes) (hx : x ∈ MonoidHom.ker m.freeGroupToCoprime) :
    x ∈ MonoidHom.ker (m.freeGroupToGal (L := L) h) :=
  m.freeGroupToCoprime_ker_le_freeGroupToGal_ker (L := L) h hx

/-- The exact factorization identity is consumed as stated. -/
example (m : Modulus K) (h : m.IsUnramifiedOutside L) :
    (m.artinMap (L := L) h).comp m.freeGroupToCoprime =
      m.freeGroupToGal (L := L) h :=
  m.artinMap_comp_freeGroupToCoprime (L := L) h

/-- Evaluation at a prime generator computes the unramified Frobenius by `simp`. -/
example (m : Modulus K) (h : m.IsUnramifiedOutside L)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hvm : ¬ m.finiteSupported v) :
    m.artinMap (L := L) h (m.primeCoprimeUnit v hvm) =
      m.frobeniusAtCoprimePrime (L := L) h ⟨v, hvm⟩ := by
  simp

end N402ArtinMapTest
