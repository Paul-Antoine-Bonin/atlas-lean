import MathlibExt.NumberTheory.NumberField.RayClass.PrimeGeneration
import MathlibExt.NumberTheory.NumberField.RayClass.FrobeniusGenerators
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Artin map by descent (ATLAS NumberTheoryI:402, Stage B2)

This file is a partial prerequisite for canonical ATLAS item `NumberTheoryI:402`
(Proposition 21.1 of Sutherland, MIT 18.785 Lecture 21), not the full N402 theorem.
Its exact ATLAS source is one slice of
[`v1/Atlas/NumberTheoryI/code/RayClassFields.lean`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
at frozen revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`:
lines `489--542`.

## ATLAS source-to-API map

| Source lines | Source name | API in this file |
| --- | --- | --- |
| 489--507 | `artinMap_ker_condition` | `Modulus.freeGroupToCoprime_ker_le_freeGroupToGal_ker` |
| 509--535 | Artin map construction | Artin map API (see below) |
| 537--542 | `artinMap_at_prime_eq_frobenius` | `Modulus.artinMap_primeCoprimeUnit` |

Row 509--535 maps source declarations `artinMapExists` and `ArtinMap` to
`Modulus.artinMap` and `Modulus.artinMap_comp_freeGroupToCoprime`.

The source proves a redundant existential theorem (`artinMapExists`) and then
applies another classical choice (`ArtinMap`). This file collapses that layer:
`Modulus.artinMap` is defined directly with Mathlib's quotient universal
property `MonoidHom.liftOfSurjective`, and the factorization identity
`Modulus.artinMap_comp_freeGroupToCoprime` is the observable contract for the
internal right-inverse choice.

## Repaired public scope

The source works under a custom abelian-extension class and an unconditional
Frobenius choice. Here the Artin map requires `h : m.IsUnramifiedOutside L`,
repairing the ramified-prime choice, and `[IsAbelianGalois K L]`, the native
replacement for the custom class. Abelianity is used to kill the free-group
commutator in the Galois target.

This stage stops before choice independence at arbitrary primes, ray-group
kernel statements, any `IsRayClassField` structure, restriction compatibility,
and Proposition 21.1. Those are separate DAG nodes.
-/

@[expose] public noncomputable section

namespace NumberField

namespace Modulus

variable {K : Type*} [Field K] [NumberField K]
variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
variable (m : Modulus K)

open scoped IsMulCommutative in
/-- Kernel containment descending the free-group Frobenius map to coprime
fractional ideals: the B0 presentation kernel lies in the commutator subgroup,
which dies in the abelian Galois target. -/
theorem freeGroupToCoprime_ker_le_freeGroupToGal_ker (h : m.IsUnramifiedOutside L) :
    MonoidHom.ker m.freeGroupToCoprime ≤
      MonoidHom.ker (m.freeGroupToGal (L := L) h) :=
  le_trans m.freeGroupToCoprime_ker_le_commutator
    (Abelianization.commutator_subset_ker _)

/-- The Artin map on fractional ideals coprime to `m`, descended directly with
Mathlib's quotient universal property `MonoidHom.liftOfSurjective`. -/
noncomputable def artinMap (h : m.IsUnramifiedOutside L) :
    m.coprimeFractionalIdeals →* (L ≃ₐ[K] L) :=
  (m.freeGroupToCoprime.liftOfSurjective m.freeGroupToCoprime_surjective)
    ⟨m.freeGroupToGal (L := L) h,
      m.freeGroupToCoprime_ker_le_freeGroupToGal_ker (L := L) h⟩

/-- Exact factorization identity: the Artin map composed with the free-group
presentation is the free-group Frobenius map. Proved through the public
`liftOfRightInverse` simp API, keeping `Function.surjInv` opaque. -/
@[simp]
theorem artinMap_comp_freeGroupToCoprime (h : m.IsUnramifiedOutside L) :
    (m.artinMap (L := L) h).comp m.freeGroupToCoprime =
      m.freeGroupToGal (L := L) h := by
  simp only [artinMap, MonoidHom.liftOfRightInverse_comp]

/-- The Artin map evaluates on a prime generator as the unramified Frobenius. -/
@[simp]
theorem artinMap_primeCoprimeUnit (h : m.IsUnramifiedOutside L)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hvm : ¬ m.finiteSupported v) :
    m.artinMap (L := L) h (m.primeCoprimeUnit v hvm) =
      m.frobeniusAtCoprimePrime (L := L) h ⟨v, hvm⟩ := by
  have hgen : m.primeCoprimeUnit v hvm =
      m.freeGroupToCoprime (FreeGroup.of (⟨v, hvm⟩ : m.CoprimePrimes)) :=
    (m.freeGroupToCoprime_of ⟨v, hvm⟩).symm
  rw [hgen, ← MonoidHom.comp_apply, m.artinMap_comp_freeGroupToCoprime,
    m.freeGroupToGal_of]

end Modulus

end NumberField
