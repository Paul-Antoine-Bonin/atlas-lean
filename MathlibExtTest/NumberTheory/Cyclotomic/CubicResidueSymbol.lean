module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
public import MathlibExt.NumberTheory.Cyclotomic.CubicResidueSymbol

@[expose] public section

namespace MetaMathlibExtTest

open MetaMathlibExt Ideal NumberField

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]
variable {zeta : K} (hZeta : IsPrimitiveRoot zeta 3)

-- Zero branch: cubicResidueSymbolRaw a 0 = 0
public lemma test_zero (a : NumberField.RingOfIntegers K) :
    cubicResidueSymbolRaw hZeta a 0 = 0 := by
  unfold MetaMathlibExt.cubicResidueSymbolRaw
  simp

-- Unit law via associate invariance.
public lemma test_unit_mul_invariance
    (a n : NumberField.RingOfIntegers K)
    (u : NumberField.RingOfIntegers K) (hu : IsUnit u) (hn : n ≠ 0) :
    cubicResidueSymbolRaw hZeta a (u * n) =
      cubicResidueSymbolRaw hZeta a n := by
  have hu0 : u ≠ 0 := IsUnit.ne_zero hu
  have h1 := MetaMathlibExt.cubicResidueSymbolRaw_mul hZeta a u n hu0 hn
  have h2 := MetaMathlibExt.cubicResidueSymbolRaw_unit hZeta a u hu
  rw [h2, one_mul] at h1
  exact h1

public lemma test_associate_invariance
    (a n : NumberField.RingOfIntegers K)
    (u : NumberField.RingOfIntegers K) (hu : IsUnit u) (hn : n ≠ 0) :
    cubicResidueSymbolRaw hZeta a n =
      cubicResidueSymbolRaw hZeta a (u * n) := by
  rw [test_unit_mul_invariance hZeta a n u hu hn]

public lemma test_unit_via_mul
    (a : NumberField.RingOfIntegers K)
    (u : NumberField.RingOfIntegers K) (hu : IsUnit u) :
    cubicResidueSymbolRaw hZeta a u = 1 := by
  have hOneNe : (1 : NumberField.RingOfIntegers K) ≠ 0 := one_ne_zero
  have hInv :=
    test_unit_mul_invariance hZeta a (1 : NumberField.RingOfIntegers K) u hu hOneNe
  have hOne :
      cubicResidueSymbolRaw hZeta a (1 : NumberField.RingOfIntegers K) = 1 :=
    MetaMathlibExt.cubicResidueSymbolRaw_unit hZeta a 1 isUnit_one
  rw [mul_one] at hInv
  rw [hOne] at hInv
  exact hInv

-- Prime root membership and congruence (not dividing case) — forwarded.
public lemma test_prime_not_dvd (a p : NumberField.RingOfIntegers K)
    (hp : Prime p) (hp0 : p ≠ 0)
    (hCop : Nat.Coprime
      (Ideal.absNorm (Ideal.span ({p} : Set (NumberField.RingOfIntegers K)))) 3)
    (hndvd : ¬ p ∣ a) :
    MetaMathlibExt.cubicResidueSymbolRaw hZeta a p ∈
      ({(1 : NumberField.RingOfIntegers K),
        MetaMathlibExt.omega hZeta,
        MetaMathlibExt.omega hZeta ^ 2} : Set _) ∧
    Ideal.Quotient.mk
        (Ideal.span ({p} : Set (NumberField.RingOfIntegers K)))
        (MetaMathlibExt.cubicResidueSymbolRaw hZeta a p) =
      Ideal.Quotient.mk (Ideal.span ({p} : Set _)) a ^
        ((Ideal.absNorm (Ideal.span ({p} : Set _)) - 1) / 3) :=
  MetaMathlibExt.cubicResidueSymbolRaw_prime_not_dvd hZeta a p hp hp0 hCop hndvd

-- Prime zero when dividing — forwarded.
public lemma test_prime_dvd (a p : NumberField.RingOfIntegers K)
    (hp : Prime p) (hp0 : p ≠ 0)
    (hCop : Nat.Coprime
      (Ideal.absNorm (Ideal.span ({p} : Set (NumberField.RingOfIntegers K)))) 3)
    (hdvd : p ∣ a) :
    MetaMathlibExt.cubicResidueSymbolRaw hZeta a p = 0 :=
  MetaMathlibExt.cubicResidueSymbolRaw_prime_dvd hZeta a p hp hp0 hCop hdvd

-- Multiplicativity: repeated factor and nontrivial composite — forwarded.
public lemma test_mul_repeated (a n : NumberField.RingOfIntegers K)
    (hn : n ≠ 0) :
    MetaMathlibExt.cubicResidueSymbolRaw hZeta a (n * n) =
      MetaMathlibExt.cubicResidueSymbolRaw hZeta a n *
        MetaMathlibExt.cubicResidueSymbolRaw hZeta a n :=
  MetaMathlibExt.cubicResidueSymbolRaw_mul hZeta a n n hn hn

public lemma test_mul_composite_three
    (a m n k : NumberField.RingOfIntegers K)
    (hm : m ≠ 0) (hn : n ≠ 0) (hk : k ≠ 0) :
    MetaMathlibExt.cubicResidueSymbolRaw hZeta a (m * n * k) =
      MetaMathlibExt.cubicResidueSymbolRaw hZeta a m *
        MetaMathlibExt.cubicResidueSymbolRaw hZeta a n *
          MetaMathlibExt.cubicResidueSymbolRaw hZeta a k := by
  have hmn : m * n ≠ 0 := mul_ne_zero hm hn
  have h1 := MetaMathlibExt.cubicResidueSymbolRaw_mul hZeta a (m * n) k hmn hk
  have h2 := MetaMathlibExt.cubicResidueSymbolRaw_mul hZeta a m n hm hn
  rw [h2] at h1
  exact h1

public lemma test_mul_with_unit
    (a m n : NumberField.RingOfIntegers K)
    (u : NumberField.RingOfIntegers K) (hu : IsUnit u)
    (hm : m ≠ 0) (hn : n ≠ 0) :
    MetaMathlibExt.cubicResidueSymbolRaw hZeta a (u * m * n) =
      MetaMathlibExt.cubicResidueSymbolRaw hZeta a m *
        MetaMathlibExt.cubicResidueSymbolRaw hZeta a n := by
  have hu0 : u ≠ 0 := IsUnit.ne_zero hu
  have hm0 : m ≠ 0 := hm
  have humn : u * m ≠ 0 := mul_ne_zero hu0 hm0
  have h1 := MetaMathlibExt.cubicResidueSymbolRaw_mul hZeta a (u * m) n humn hn
  have h2 := MetaMathlibExt.cubicResidueSymbolRaw_mul hZeta a u m hu0 hm0
  have h3 := MetaMathlibExt.cubicResidueSymbolRaw_unit hZeta a u hu
  rw [h2, h3, one_mul] at h1
  exact h1

-- Totalization: every default branch of the prime-ideal factor — forwarded.

public lemma test_factor_notPrime
    (P : Ideal (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K)
    (hNotPrime : ¬ P.IsPrime) :
    MetaMathlibExt.primeIdealCubicSymbolFactorRaw hZeta P a = 1 :=
  MetaMathlibExt.primeIdealCubicSymbolFactorRaw_of_not_isPrime hZeta P a hNotPrime

public lemma test_factor_bot
    (a : NumberField.RingOfIntegers K) :
    MetaMathlibExt.primeIdealCubicSymbolFactorRaw hZeta
        (⊥ : Ideal (NumberField.RingOfIntegers K)) a = 1 :=
  MetaMathlibExt.primeIdealCubicSymbolFactorRaw_bot hZeta a

public lemma test_factor_notCoprime
    (P : Ideal (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K)
    (hPprime : P.IsPrime) (hPbot : P ≠ ⊥)
    (hNotCop : ¬ Nat.Coprime (Ideal.absNorm P) 3) :
    MetaMathlibExt.primeIdealCubicSymbolFactorRaw hZeta P a = 1 :=
  MetaMathlibExt.primeIdealCubicSymbolFactorRaw_of_not_coprime
    hZeta P a hPprime hPbot hNotCop

public lemma test_factor_isPrime_bot
    (P : Ideal (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K)
    (hPprime : P.IsPrime) (hBot : P = ⊥) :
    MetaMathlibExt.primeIdealCubicSymbolFactorRaw hZeta P a = 1 :=
  MetaMathlibExt.primeIdealCubicSymbolFactorRaw_eq_one_of_isPrime_of_bot
    hZeta P a hPprime hBot

-- Independent definition-unfolding probes for prime-ideal factor branches.

public lemma test_factor_valid_branch_via_definition
    (P : Ideal (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K)
    (hPprime : P.IsPrime) (hPbot : P ≠ ⊥)
    (hCop : Nat.Coprime (Ideal.absNorm P) 3) (ha : a ∉ P) :
    MetaMathlibExt.primeIdealCubicSymbolFactorRaw hZeta P a =
      MetaMathlibExt.primeIdealValidCubicSymbol hZeta P a hPprime hPbot hCop ha := by
  simp only [MetaMathlibExt.primeIdealCubicSymbolFactorRaw,
    dite_eq_left hPprime, dite_eq_left hPbot, dite_eq_left hCop, dite_eq_right ha]

public lemma test_factor_dvd_branch_via_definition
    (P : Ideal (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K)
    (hPprime : P.IsPrime) (hPbot : P ≠ ⊥)
    (hCop : Nat.Coprime (Ideal.absNorm P) 3) (ha : a ∈ P) :
    MetaMathlibExt.primeIdealCubicSymbolFactorRaw hZeta P a = 0 := by
  simp only [MetaMathlibExt.primeIdealCubicSymbolFactorRaw,
    dite_eq_left hPprime, dite_eq_left hPbot, dite_eq_left hCop, dite_eq_left ha]

public lemma test_factor_notPrime_via_definition
    (P : Ideal (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K)
    (hNotPrime : ¬ P.IsPrime) :
    MetaMathlibExt.primeIdealCubicSymbolFactorRaw hZeta P a = 1 := by
  simp only [MetaMathlibExt.primeIdealCubicSymbolFactorRaw, dite_eq_right hNotPrime]

public lemma test_factor_bot_via_definition
    (a : NumberField.RingOfIntegers K) :
    MetaMathlibExt.primeIdealCubicSymbolFactorRaw hZeta
        (⊥ : Ideal (NumberField.RingOfIntegers K)) a = 1 := by
  have hPprime : (⊥ : Ideal (NumberField.RingOfIntegers K)).IsPrime := by
    constructor
    · intro h
      have : (1 : NumberField.RingOfIntegers K) ∈ (⊥ : Ideal _) := by
        rw [h]; trivial
      simp at this
    · intro x y hxy
      rw [Ideal.mem_bot] at hxy
      rcases mul_eq_zero.mp hxy with hx | hy
      · left; rw [Ideal.mem_bot, hx]
      · right; rw [Ideal.mem_bot, hy]
  have hNotBot : ¬ ((⊥ : Ideal (NumberField.RingOfIntegers K)) ≠ ⊥) := by
    intro h
    exact h rfl
  simp only [MetaMathlibExt.primeIdealCubicSymbolFactorRaw, dite_eq_left hPprime, dite_eq_right hNotBot]

public lemma test_factor_notCoprime_via_definition
    (P : Ideal (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K)
    (hPprime : P.IsPrime) (hPbot : P ≠ ⊥)
    (hNotCop : ¬ Nat.Coprime (Ideal.absNorm P) 3) :
    MetaMathlibExt.primeIdealCubicSymbolFactorRaw hZeta P a = 1 := by
  simp only [MetaMathlibExt.primeIdealCubicSymbolFactorRaw,
    dite_eq_left hPprime, dite_eq_left hPbot, dite_eq_right hNotCop]

-- Independent definition-unfolding probe for prime denominator via normalizedFactors.

public lemma test_prime_not_dvd_via_definition
    (a p : NumberField.RingOfIntegers K)
    (hp : Prime p) (hp0 : p ≠ 0)
    (hCop : Nat.Coprime
      (Ideal.absNorm (Ideal.span ({p} : Set (NumberField.RingOfIntegers K)))) 3)
    (hndvd : ¬ p ∣ a) :
    MetaMathlibExt.cubicResidueSymbolRaw hZeta a p ∈
        ({(1 : NumberField.RingOfIntegers K),
          MetaMathlibExt.omega hZeta,
          MetaMathlibExt.omega hZeta ^ 2} : Set _) ∧
    Ideal.Quotient.mk (Ideal.span ({p} : Set (NumberField.RingOfIntegers K)))
        (MetaMathlibExt.cubicResidueSymbolRaw hZeta a p) =
      Ideal.Quotient.mk (Ideal.span ({p} : Set _)) a ^
        ((Ideal.absNorm (Ideal.span ({p} : Set _)) - 1) / 3) := by
  have hNotMem : a ∉ Ideal.span ({p} : Set (NumberField.RingOfIntegers K)) := by
    rwa [Ideal.mem_span_singleton]
  have hSpanPrime : (Ideal.span ({p} : Set (NumberField.RingOfIntegers K))).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime hp
  have hSpanNeBot : Ideal.span ({p} : Set (NumberField.RingOfIntegers K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hp0
  have hPrimeIdeal : Prime (Ideal.span ({p} : Set (NumberField.RingOfIntegers K))) :=
    Ideal.prime_of_isPrime hSpanNeBot hSpanPrime
  have hIrred : Irreducible (Ideal.span ({p} : Set (NumberField.RingOfIntegers K))) :=
    hPrimeIdeal.irreducible
  have hFac : UniqueFactorizationMonoid.normalizedFactors
      (Ideal.span ({p} : Set _)) = {Ideal.span {p}} := by
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hIrred, normalize_eq]
  have hSymEq : MetaMathlibExt.cubicResidueSymbolRaw hZeta a p =
      MetaMathlibExt.primeIdealValidCubicSymbol hZeta
        (Ideal.span ({p} : Set _)) a hSpanPrime hSpanNeBot hCop hNotMem := by
    unfold MetaMathlibExt.cubicResidueSymbolRaw
    simp only [hp0, ↓reduceIte]
    rw [hFac]
    simp only [Multiset.map_singleton, Multiset.prod_singleton]
    simp only [MetaMathlibExt.primeIdealCubicSymbolFactorRaw,
      dite_eq_left hSpanPrime, dite_eq_left hSpanNeBot, dite_eq_left hCop, dite_eq_right hNotMem]
  rw [hSymEq]
  exact ⟨MetaMathlibExt.primeIdealValidCubicSymbol_mem hZeta _ _
      hSpanPrime hSpanNeBot hCop hNotMem,
    MetaMathlibExt.primeIdealValidCubicSymbol_spec hZeta _ _
      hSpanPrime hSpanNeBot hCop hNotMem⟩

public lemma test_prime_dvd_via_definition
    (a p : NumberField.RingOfIntegers K)
    (hp : Prime p) (hp0 : p ≠ 0)
    (hCop : Nat.Coprime
      (Ideal.absNorm (Ideal.span ({p} : Set (NumberField.RingOfIntegers K)))) 3)
    (hdvd : p ∣ a) :
    MetaMathlibExt.cubicResidueSymbolRaw hZeta a p = 0 := by
  have hMem : a ∈ Ideal.span ({p} : Set (NumberField.RingOfIntegers K)) :=
    Ideal.mem_span_singleton.mpr hdvd
  have hSpanPrime : (Ideal.span ({p} : Set (NumberField.RingOfIntegers K))).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime hp
  have hSpanNeBot : Ideal.span ({p} : Set (NumberField.RingOfIntegers K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hp0
  have hPrimeIdeal : Prime (Ideal.span ({p} : Set (NumberField.RingOfIntegers K))) :=
    Ideal.prime_of_isPrime hSpanNeBot hSpanPrime
  have hIrred : Irreducible (Ideal.span ({p} : Set (NumberField.RingOfIntegers K))) :=
    hPrimeIdeal.irreducible
  have hFac : UniqueFactorizationMonoid.normalizedFactors
      (Ideal.span ({p} : Set _)) = {Ideal.span {p}} := by
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hIrred, normalize_eq]
  unfold MetaMathlibExt.cubicResidueSymbolRaw
  simp only [hp0, ↓reduceIte]
  rw [hFac]
  simp only [Multiset.map_singleton, Multiset.prod_singleton]
  simp only [MetaMathlibExt.primeIdealCubicSymbolFactorRaw,
    dite_eq_left hSpanPrime, dite_eq_left hSpanNeBot, dite_eq_left hCop, dite_eq_left hMem]

-- Independent direct-definition multiplicativity probes that unfold normalizedFactors.

public lemma test_mul_via_definition
    (a m n : NumberField.RingOfIntegers K)
    (hm : m ≠ 0) (hn : n ≠ 0) :
    MetaMathlibExt.cubicResidueSymbolRaw hZeta a (m * n) =
      MetaMathlibExt.cubicResidueSymbolRaw hZeta a m *
        MetaMathlibExt.cubicResidueSymbolRaw hZeta a n := by
  unfold MetaMathlibExt.cubicResidueSymbolRaw
  have hmn : m * n ≠ 0 := mul_ne_zero hm hn
  simp only [hm, hn, hmn, ↓reduceIte]
  have hSpanMul : Ideal.span ({m * n} : Set (NumberField.RingOfIntegers K)) =
      Ideal.span ({m} : Set _) * Ideal.span ({n} : Set _) := by
    rw [Ideal.span_singleton_mul_span_singleton]
  have hmBot : Ideal.span ({m} : Set (NumberField.RingOfIntegers K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hm
  have hnBot : Ideal.span ({n} : Set (NumberField.RingOfIntegers K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hn
  have hFacMul : UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({m * n} : Set _)) =
      UniqueFactorizationMonoid.normalizedFactors (Ideal.span ({m} : Set _)) +
        UniqueFactorizationMonoid.normalizedFactors (Ideal.span ({n} : Set _)) := by
    rw [hSpanMul]
    exact UniqueFactorizationMonoid.normalizedFactors_mul hmBot hnBot
  simp only [hFacMul, Multiset.map_add, Multiset.prod_add]

public lemma test_mul_repeated_via_definition
    (a n : NumberField.RingOfIntegers K) (hn : n ≠ 0) :
    MetaMathlibExt.cubicResidueSymbolRaw hZeta a (n * n) =
      MetaMathlibExt.cubicResidueSymbolRaw hZeta a n *
        MetaMathlibExt.cubicResidueSymbolRaw hZeta a n := by
  have h := test_mul_via_definition hZeta a n n hn hn
  simpa using h

public lemma test_mul_composite_three_via_definition
    (a m n k : NumberField.RingOfIntegers K)
    (hm : m ≠ 0) (hn : n ≠ 0) (hk : k ≠ 0) :
    MetaMathlibExt.cubicResidueSymbolRaw hZeta a (m * n * k) =
      MetaMathlibExt.cubicResidueSymbolRaw hZeta a m *
        MetaMathlibExt.cubicResidueSymbolRaw hZeta a n *
          MetaMathlibExt.cubicResidueSymbolRaw hZeta a k := by
  have hmn : m * n ≠ 0 := mul_ne_zero hm hn
  have h1 := test_mul_via_definition hZeta a (m * n) k hmn hk
  have h2 := test_mul_via_definition hZeta a m n hm hn
  rw [h2] at h1
  exact h1

instance : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
  @CyclotomicField.isCyclotomicExtension 3 ⟨by decide⟩ ℚ _ ⟨by norm_num⟩

-- Concrete third cyclotomic instantiation
public lemma concrete_cyclotomic_inhabited :
    IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
  inferInstance

public noncomputable def concreteZeta : CyclotomicField 3 ℚ :=
  IsCyclotomicExtension.zeta 3 ℚ (CyclotomicField 3 ℚ)

public lemma concrete_zeta_isPrimitive :
    IsPrimitiveRoot concreteZeta 3 :=
  IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ)

public lemma concrete_omega_mem :
    MetaMathlibExt.omega (K := CyclotomicField 3 ℚ)
        concrete_zeta_isPrimitive ∈
      ({(1 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)),
        MetaMathlibExt.omega concrete_zeta_isPrimitive,
        MetaMathlibExt.omega concrete_zeta_isPrimitive ^ 2} : Set _) := by
  simp

public lemma concrete_symbol_at_one :
    MetaMathlibExt.cubicResidueSymbolRaw
        (K := CyclotomicField 3 ℚ) concrete_zeta_isPrimitive 0 1 = 1 :=
  MetaMathlibExt.cubicResidueSymbolRaw_unit
    concrete_zeta_isPrimitive 0 1 isUnit_one

public lemma concrete_symbol_zero_branch :
    MetaMathlibExt.cubicResidueSymbolRaw
        (K := CyclotomicField 3 ℚ) concrete_zeta_isPrimitive 0 0 = 0 := by
  unfold MetaMathlibExt.cubicResidueSymbolRaw
  simp

public lemma concrete_symbol_unit_direct :
    MetaMathlibExt.cubicResidueSymbolRaw
        (K := CyclotomicField 3 ℚ) concrete_zeta_isPrimitive 0 (-1) = 1 := by
  have h : IsUnit (-1 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) :=
    isUnit_one.neg
  exact MetaMathlibExt.cubicResidueSymbolRaw_unit concrete_zeta_isPrimitive 0 (-1) h

-- Concrete composite and repeated-factor probes via direct definition
public lemma concrete_composite_mul_via_definition
    (a : NumberField.RingOfIntegers (CyclotomicField 3 ℚ))
    (m n : NumberField.RingOfIntegers (CyclotomicField 3 ℚ))
    (hm : m ≠ 0) (hn : n ≠ 0) :
    MetaMathlibExt.cubicResidueSymbolRaw (K := CyclotomicField 3 ℚ)
        concrete_zeta_isPrimitive a (m * n) =
      MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive a m *
        MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive a n :=
  test_mul_via_definition concrete_zeta_isPrimitive a m n hm hn

public lemma concrete_repeated_factor_via_definition
    (a n : NumberField.RingOfIntegers (CyclotomicField 3 ℚ))
    (hn : n ≠ 0) :
    MetaMathlibExt.cubicResidueSymbolRaw (K := CyclotomicField 3 ℚ)
        concrete_zeta_isPrimitive a (n * n) =
      MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive a n *
        MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive a n :=
  test_mul_repeated_via_definition concrete_zeta_isPrimitive a n hn

-- Concrete composite with explicit nonzero numerals (exercises normalization multiplicity)
public lemma concrete_composite_explicit_two_three
    (a : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) :
    MetaMathlibExt.cubicResidueSymbolRaw (K := CyclotomicField 3 ℚ)
        concrete_zeta_isPrimitive a ((2 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) * 3) =
      MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive a 2 *
        MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive a 3 := by
  have h2 : (2 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by decide : (2 : ℕ) ≠ 0)
  have h3 : (3 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by decide : (3 : ℕ) ≠ 0)
  exact test_mul_via_definition concrete_zeta_isPrimitive a 2 3 h2 h3

public lemma concrete_repeated_explicit_two
    (a : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) :
    MetaMathlibExt.cubicResidueSymbolRaw (K := CyclotomicField 3 ℚ)
        concrete_zeta_isPrimitive a ((2 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) * 2) =
      MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive a 2 *
        MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive a 2 := by
  have h2 : (2 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by decide : (2 : ℕ) ≠ 0)
  exact test_mul_via_definition concrete_zeta_isPrimitive a 2 2 h2 h2

-- Closed concrete prime over rational prime 2
instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

instance span_two_isPrime :
    (Ideal.span ({(2 : ℤ)} : Set ℤ)).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime Int.prime_two

noncomputable def concretePrimeIdealSubtype :
    ↥(Ideal.primesOver (Ideal.span ({(2 : ℤ)} : Set ℤ))
        (NumberField.RingOfIntegers (CyclotomicField 3 ℚ))) :=
  Classical.choice inferInstance

noncomputable def concretePrimeIdeal :
    Ideal (NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) :=
  concretePrimeIdealSubtype.val

public lemma concretePrimeIdeal_isPrime :
    concretePrimeIdeal.IsPrime :=
  concretePrimeIdealSubtype.prop.1

public lemma concretePrimeIdeal_liesOver :
    concretePrimeIdeal.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) :=
  concretePrimeIdealSubtype.prop.2

public lemma concretePrimeIdeal_mem :
    concretePrimeIdeal ∈
      Ideal.primesOver (Ideal.span ({(2 : ℤ)} : Set ℤ))
        (NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) :=
  concretePrimeIdealSubtype.prop

public lemma concretePrimeIdeal_ne_bot :
    concretePrimeIdeal ≠ ⊥ :=
  Ideal.ne_bot_of_mem_primesOver
    (p := Ideal.span ({(2 : ℤ)} : Set ℤ))
    (by
      intro h
      have hMem : (2 : ℤ) ∈ (⊥ : Ideal ℤ) :=
        h ▸ Ideal.mem_span_singleton_self (2 : ℤ)
      simp at hMem)
    concretePrimeIdeal_mem

public lemma concretePrimeIdeal_inertiaDeg :
    Ideal.inertiaDeg concretePrimeIdeal ℤ = 2 := by
  have hm : ¬ (2 : ℕ) ∣ 3 := by decide
  have hEq :
      Ideal.inertiaDeg concretePrimeIdeal ℤ =
        orderOf ((2 : ℕ) : ZMod 3) :=
    @IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
      (m := 3) (p := 2) _ (CyclotomicField 3 ℚ) _ _
      concretePrimeIdeal concretePrimeIdeal_isPrime
      concretePrimeIdeal_liesOver _ _ hm
  have hOrder : orderOf ((2 : ℕ) : ZMod 3) = 2 := by
    apply orderOf_eq_prime
    · decide
    · decide
  rw [hOrder] at hEq
  exact hEq

public lemma concretePrimeIdeal_absNorm :
    Ideal.absNorm concretePrimeIdeal = 4 := by
  have hInertia := concretePrimeIdeal_inertiaDeg
  have hPow :
      (2 : ℕ) ^ Ideal.inertiaDeg concretePrimeIdeal ℤ =
        Ideal.absNorm concretePrimeIdeal :=
    @Ideal.pow_inertiaDeg _ _ _ _ _ 2 concretePrimeIdeal
      concretePrimeIdeal_isPrime concretePrimeIdeal_liesOver
  rw [hInertia] at hPow
  have : (2 : ℕ) ^ 2 = 4 := by decide
  rw [this] at hPow
  exact hPow.symm

public lemma concretePrimeIdeal_norm_coprime :
    Nat.Coprime (Ideal.absNorm concretePrimeIdeal) 3 := by
  rw [concretePrimeIdeal_absNorm]
  decide

instance instThreePID :
    IsPrincipalIdealRing
      (NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) :=
  IsCyclotomicExtension.Rat.three_pid (K := CyclotomicField 3 ℚ)

noncomputable def concretePrime :
    NumberField.RingOfIntegers (CyclotomicField 3 ℚ) :=
  Submodule.IsPrincipal.generator concretePrimeIdeal

public lemma concretePrime_span :
    Ideal.span ({concretePrime} : Set _) = concretePrimeIdeal :=
  Submodule.IsPrincipal.span_singleton_generator concretePrimeIdeal

public lemma concretePrime_prime : Prime concretePrime :=
  @Submodule.IsPrincipal.prime_generator_of_isPrime _ _
    concretePrimeIdeal _ concretePrimeIdeal_isPrime
    concretePrimeIdeal_ne_bot

public lemma concretePrime_ne_zero : concretePrime ≠ 0 :=
  concretePrime_prime.ne_zero

public lemma concretePrime_absNorm :
    Ideal.absNorm (Ideal.span ({concretePrime} : Set _)) = 4 := by
  rw [concretePrime_span, concretePrimeIdeal_absNorm]

public lemma concretePrime_norm_coprime :
    Nat.Coprime
      (Ideal.absNorm (Ideal.span ({concretePrime} : Set _))) 3 := by
  rw [concretePrime_absNorm]
  decide

public lemma concretePrime_not_dvd_one :
    ¬ concretePrime ∣ (1 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) := by
  intro h
  have hUnit : IsUnit concretePrime := isUnit_of_dvd_one h
  exact concretePrime_prime.not_isUnit hUnit

public lemma concretePrime_not_mem_span_one :
    (1 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) ∉
      Ideal.span ({concretePrime} : Set _) := by
  rw [Ideal.mem_span_singleton]
  exact concretePrime_not_dvd_one

public lemma concretePrime_one_not_mem_ideal :
    (1 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) ∉
      concretePrimeIdeal := by
  rw [← concretePrime_span]
  exact concretePrime_not_mem_span_one

-- Closed concrete valid-branch probe at prime denominator
public lemma concrete_prime_symbol_valid_closed :
    MetaMathlibExt.cubicResidueSymbolRaw
        (K := CyclotomicField 3 ℚ) concrete_zeta_isPrimitive
        1 concretePrime ∈
      ({(1 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)),
        MetaMathlibExt.omega concrete_zeta_isPrimitive,
        MetaMathlibExt.omega concrete_zeta_isPrimitive ^ 2} : Set _) ∧
    Ideal.Quotient.mk (Ideal.span {concretePrime})
        (MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive
          1 concretePrime) =
      Ideal.Quotient.mk (Ideal.span {concretePrime})
          (1 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) ^
        ((Ideal.absNorm (Ideal.span {concretePrime}) - 1) / 3) :=
  MetaMathlibExt.cubicResidueSymbolRaw_prime_not_dvd
    (K := CyclotomicField 3 ℚ) concrete_zeta_isPrimitive 1 concretePrime
    concretePrime_prime concretePrime_ne_zero concretePrime_norm_coprime
    concretePrime_not_dvd_one

-- Valid branch via direct definition unfolding (closed)
public lemma concrete_prime_symbol_valid_via_definition :
    MetaMathlibExt.cubicResidueSymbolRaw
        (K := CyclotomicField 3 ℚ) concrete_zeta_isPrimitive
        1 concretePrime ∈
      ({(1 : _), MetaMathlibExt.omega concrete_zeta_isPrimitive,
        MetaMathlibExt.omega concrete_zeta_isPrimitive ^ 2} : Set _) ∧
    Ideal.Quotient.mk (Ideal.span {concretePrime})
        (MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive
          1 concretePrime) =
      Ideal.Quotient.mk (Ideal.span {concretePrime}) (1 : _) ^
        ((Ideal.absNorm (Ideal.span {concretePrime}) - 1) / 3) := by
  have hNotMem : (1 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) ∉
      Ideal.span ({concretePrime} : Set _) := concretePrime_not_mem_span_one
  have hSpanPrime :
      (Ideal.span ({concretePrime} : Set _)).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime concretePrime_prime
  have hSpanNeBot :
      Ideal.span ({concretePrime} : Set _) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact concretePrime_ne_zero
  have hCop := concretePrime_norm_coprime
  have hFac :
      UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({concretePrime} : Set _)) =
        {Ideal.span {concretePrime}} := by
    have hPrimeIdeal :
        Prime (Ideal.span ({concretePrime} : Set _)) :=
      Ideal.prime_of_isPrime hSpanNeBot hSpanPrime
    have hIrr :
        Irreducible (Ideal.span ({concretePrime} : Set _)) :=
      hPrimeIdeal.irreducible
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hIrr,
      normalize_eq]
  have hSymEq :
      MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive 1
          concretePrime =
        MetaMathlibExt.primeIdealValidCubicSymbol
          (K := CyclotomicField 3 ℚ) concrete_zeta_isPrimitive
          (Ideal.span {concretePrime}) 1 hSpanPrime hSpanNeBot
          hCop hNotMem := by
    unfold MetaMathlibExt.cubicResidueSymbolRaw
    simp only [concretePrime_ne_zero, ↓reduceIte]
    rw [hFac]
    simp only [Multiset.map_singleton, Multiset.prod_singleton]
    simp only [MetaMathlibExt.primeIdealCubicSymbolFactorRaw,
      dite_eq_left hSpanPrime, dite_eq_left hSpanNeBot, dite_eq_left hCop,
      dite_eq_right hNotMem]
  rw [hSymEq]
  exact ⟨MetaMathlibExt.primeIdealValidCubicSymbol_mem _ _ _
      hSpanPrime hSpanNeBot hCop hNotMem,
    MetaMathlibExt.primeIdealValidCubicSymbol_spec _ _ _
      hSpanPrime hSpanNeBot hCop hNotMem⟩

-- NormalizedFactors factorization for the concrete prime
public lemma concretePrime_normalizedFactors_single :
    UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({concretePrime} :
          Set (NumberField.RingOfIntegers (CyclotomicField 3 ℚ)))) =
      {Ideal.span {concretePrime}} := by
  have hSpanNeBot :
      Ideal.span ({concretePrime} :
          Set (NumberField.RingOfIntegers (CyclotomicField 3 ℚ))) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact concretePrime_ne_zero
  have hSpanPrime :
      (Ideal.span ({concretePrime} : Set _)).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime concretePrime_prime
  have hPrimeIdeal :
      Prime (Ideal.span ({concretePrime} : Set _)) :=
    Ideal.prime_of_isPrime hSpanNeBot hSpanPrime
  have hIrr :
      Irreducible (Ideal.span ({concretePrime} : Set _)) :=
    hPrimeIdeal.irreducible
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hIrr,
    normalize_eq]

public lemma concretePrime_normalizedFactors_sq :
    UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({concretePrime * concretePrime} :
          Set (NumberField.RingOfIntegers (CyclotomicField 3 ℚ)))) =
      {Ideal.span {concretePrime}, Ideal.span {concretePrime}} := by
  have hPiNeZero := concretePrime_ne_zero
  have hBot :
      Ideal.span ({concretePrime} :
          Set (NumberField.RingOfIntegers (CyclotomicField 3 ℚ))) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hPiNeZero
  have hFacSingle := concretePrime_normalizedFactors_single
  have hFacMul :
      UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({concretePrime * concretePrime} : Set _)) =
        UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({concretePrime} : Set _)) +
          UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({concretePrime} : Set _)) := by
    rw [show Ideal.span ({concretePrime * concretePrime} : Set _) =
        Ideal.span ({concretePrime} : Set _) *
          Ideal.span ({concretePrime} : Set _) from by
      rw [Ideal.span_singleton_mul_span_singleton]]
    exact UniqueFactorizationMonoid.normalizedFactors_mul hBot hBot
  rw [hFacMul, hFacSingle]
  rfl

-- Closed repeated-factor probe using the concrete prime twice,
-- unfolding normalizedFactors (nontrivial factorization)
public lemma concrete_prime_repeated_closed (a :
    NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) :
    MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive a
        (concretePrime * concretePrime) =
      MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive a
          concretePrime *
        MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive a
          concretePrime := by
  have hPiNeZero : concretePrime ≠ 0 := concretePrime_ne_zero
  have hPiSqNeZero : concretePrime * concretePrime ≠ 0 :=
    mul_ne_zero hPiNeZero hPiNeZero
  unfold MetaMathlibExt.cubicResidueSymbolRaw
  simp only [hPiNeZero, hPiSqNeZero, ↓reduceIte]
  have hSpanMul :
      Ideal.span ({concretePrime * concretePrime} :
          Set (NumberField.RingOfIntegers (CyclotomicField 3 ℚ))) =
        Ideal.span ({concretePrime} : Set _) *
          Ideal.span ({concretePrime} : Set _) := by
    rw [Ideal.span_singleton_mul_span_singleton]
  have hBot :
      Ideal.span ({concretePrime} :
          Set (NumberField.RingOfIntegers (CyclotomicField 3 ℚ))) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hPiNeZero
  have hFacMul :
      UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({concretePrime * concretePrime} : Set _)) =
        UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({concretePrime} : Set _)) +
          UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({concretePrime} : Set _)) := by
    rw [hSpanMul]
    exact UniqueFactorizationMonoid.normalizedFactors_mul hBot hBot
  simp only [hFacMul, Multiset.map_add, Multiset.prod_add]

public lemma concrete_prime_repeated_zero_a_closed :
    MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive
        (0 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ))
        (concretePrime * concretePrime) =
      MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive 0
          concretePrime *
        MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive 0
          concretePrime :=
  concrete_prime_repeated_closed 0

omit [IsCyclotomicExtension {3} ℚ K] in
public lemma test_valid_ne_zero (n : NumberField.RingOfIntegers K) :
    MetaMathlibExt.IsCubicResidueDenominator n → n ≠ 0 := fun h => h.1

omit [IsCyclotomicExtension {3} ℚ K] in
public lemma test_valid_norm_coprime (n : NumberField.RingOfIntegers K) :
    MetaMathlibExt.IsCubicResidueDenominator n →
    Nat.Coprime (Ideal.absNorm (Ideal.span {n})) 3 := fun h => h.2

public lemma test_canonical_eq_raw (a n : NumberField.RingOfIntegers K) :
    ∀ (hValid : MetaMathlibExt.IsCubicResidueDenominator n),
    MetaMathlibExt.cubicResidueSymbol hZeta a n hValid =
    MetaMathlibExt.cubicResidueSymbolRaw hZeta a n := fun _ => rfl

public lemma test_canonical_prime_dvd (a p : NumberField.RingOfIntegers K) :
    ∀ (_hp : Prime p) (hpValid : MetaMathlibExt.IsCubicResidueDenominator p),
    p ∣ a → MetaMathlibExt.cubicResidueSymbol hZeta a p hpValid = 0 :=
    fun _hp hpValid hdvd =>
      MetaMathlibExt.cubicResidueSymbol_prime_dvd hZeta a p _hp hpValid hdvd

public lemma test_canonical_prime_not_dvd (a p : NumberField.RingOfIntegers K) :
    ∀ (_hp : Prime p) (hpValid : MetaMathlibExt.IsCubicResidueDenominator p),
    ¬ p ∣ a →
    MetaMathlibExt.cubicResidueSymbol hZeta a p hpValid ∈
    ({(1 : NumberField.RingOfIntegers K), MetaMathlibExt.omega hZeta,
    MetaMathlibExt.omega hZeta ^ 2} : Set _) ∧
    Ideal.Quotient.mk (Ideal.span {p})
    (MetaMathlibExt.cubicResidueSymbol hZeta a p hpValid) =
    Ideal.Quotient.mk (Ideal.span {p}) a ^
    ((Ideal.absNorm (Ideal.span {p}) - 1) / 3) :=
    fun _hp hpValid hndvd =>
      MetaMathlibExt.cubicResidueSymbol_prime_not_dvd hZeta a p _hp hpValid hndvd

end MetaMathlibExtTest
