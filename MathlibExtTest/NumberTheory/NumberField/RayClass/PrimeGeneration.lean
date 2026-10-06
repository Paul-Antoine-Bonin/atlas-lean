import MathlibExt.NumberTheory.NumberField.RayClass.PrimeGeneration

/-!
# Tests for prime generation of coprime fractional ideals (ATLAS N402, Stages A2+B0)
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors
open NumberField

namespace N402PrimeGenerationTest

variable {K : Type*} [Field K] [NumberField K]

/-- Generator membership unfolds to an existential over coprime primes. -/
example (m : Modulus K) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hvm : ¬ m.finiteSupported v) :
    m.primeCoprimeUnit v hvm ∈ m.coprimePrimeUnits :=
  (m.mem_coprimePrimeUnits _).mpr ⟨v, hvm, rfl⟩

/-- Closure of the prime generators is the whole coprime group. -/
example (m : Modulus K) :
    Subgroup.closure m.coprimePrimeUnits = ⊤ :=
  m.closure_coprimePrimeUnits_eq_top

/-- The free-group map computes on generators (`freeGroupToCoprime_of` is `simp`). -/
example (m : Modulus K) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hvm : ¬ m.finiteSupported v) :
    m.freeGroupToCoprime (FreeGroup.of ⟨v, hvm⟩) = m.primeCoprimeUnit v hvm := by
  simp

/-- Membership in the generator range is membership in the prime coprime units. -/
example (m : Modulus K) (I : m.coprimeFractionalIdeals) :
    I ∈ Set.range
        (fun p : m.CoprimePrimes => m.primeCoprimeUnit p.val p.property) ↔
      I ∈ m.coprimePrimeUnits := by
  rw [← m.coprimePrimeUnits_eq_range]

/-- Generic surjectivity of the free-group map. -/
example (m : Modulus K) :
    Function.Surjective m.freeGroupToCoprime :=
  m.freeGroupToCoprime_surjective

/-- Every coprime ideal is hit by the free-group map. -/
example (m : Modulus K) (x : m.coprimeFractionalIdeals) :
    ∃ w, m.freeGroupToCoprime w = x :=
  m.freeGroupToCoprime_surjective x

/-- Concrete consumer over `ℚ` at the trivial modulus. -/
example (x : (1 : Modulus ℚ).coprimeFractionalIdeals) :
    ∃ w, (Modulus.freeGroupToCoprime (1 : Modulus ℚ)) w = x :=
  (Modulus.freeGroupToCoprime_surjective (1 : Modulus ℚ)) x

/-- The kernel inclusion: kernel elements lie in the commutator subgroup. -/
example (m : Modulus K) (x : FreeGroup m.CoprimePrimes)
    (hx : x ∈ MonoidHom.ker m.freeGroupToCoprime) :
    x ∈ commutator (FreeGroup m.CoprimePrimes) :=
  m.freeGroupToCoprime_ker_le_commutator hx

/-- The simp kernel equality fires under `simp`. -/
example (m : Modulus K) (x : FreeGroup m.CoprimePrimes) :
    x ∈ MonoidHom.ker m.freeGroupToCoprime ↔
      x ∈ commutator (FreeGroup m.CoprimePrimes) := by
  simp

/-- Concrete `K := ℚ`, `m := 1`: kernel elements lie in the commutator. -/
example (x : FreeGroup (Modulus.CoprimePrimes (1 : Modulus ℚ)))
    (hx : x ∈ MonoidHom.ker (Modulus.freeGroupToCoprime (1 : Modulus ℚ))) :
    x ∈ commutator (FreeGroup (Modulus.CoprimePrimes (1 : Modulus ℚ))) :=
  (Modulus.freeGroupToCoprime_ker_le_commutator (1 : Modulus ℚ)) hx

end N402PrimeGenerationTest
