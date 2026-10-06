import MathlibExt.NumberTheory.NumberField.RayClass.ArtinMapRestriction

/-!
# Tests for Artin map restriction (ATLAS N402, C3 and final)
-/

@[expose] public noncomputable section

open NumberField

namespace N402ArtinMapRestrictionTest

variable {K L M : Type*} [Field K] [Field L] [Field M]
  [NumberField K] [NumberField L] [NumberField M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [IsAbelianGalois K L] [IsAbelianGalois K M]

/-- Restriction of the `M`-Artin map at a prime generator is the `L`-Artin map. -/
example (m : Modulus K) (hL : m.IsUnramifiedOutside L)
    (hM : m.IsUnramifiedOutside M)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hvm : ¬ m.finiteSupported v) :
    AlgEquiv.restrictNormalHom L
        (m.artinMap (L := M) hM (m.primeCoprimeUnit v hvm)) =
      m.artinMap (L := L) hL (m.primeCoprimeUnit v hvm) := by
  simpa only using
    m.restrictNormalHom_artinMap_primeCoprimeUnit (L := L) (M := M) hL hM v hvm

/-- Pointwise restriction of the `M`-Artin map is the `L`-Artin map. -/
example (m : Modulus K) (hL : m.IsUnramifiedOutside L)
    (hM : m.IsUnramifiedOutside M) (I : m.coprimeFractionalIdeals) :
    AlgEquiv.restrictNormalHom L (m.artinMap (L := M) hM I) =
      m.artinMap (L := L) hL I :=
  DFunLike.congr_fun
    (m.restrictNormalHom_comp_artinMap (L := L) (M := M) hL hM) I

end N402ArtinMapRestrictionTest
