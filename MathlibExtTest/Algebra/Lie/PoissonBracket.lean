module

public import MathlibExt.Algebra.Lie.PoissonBracket

@[expose] public section

namespace MathlibExtTest.Algebra.Lie.PoissonBracket

open MathlibExt.Algebra.Lie.PoissonBracket

/-- The trivial (zero) Poisson bracket: every bracket vanishes. -/
def trivialBracket (A : Type) [CommRing A] [Algebra ℂ A] :
    PoissonBracket A where
  bracket := fun _ _ => 0
  add_left _ _ _ := by simp
  add_right _ _ _ := by simp
  skew _ _ := by simp
  leibniz _ _ _ := by simp
  jacobi _ _ _ := by simp
  smul_left _ _ _ := by simp
  smul_right _ _ _ := by simp

/-- With the trivial bracket, every ideal is Poisson. -/
theorem trivial_poisson (A : Type) [CommRing A] [Algebra ℂ A]
    (P : Ideal A) : IsPoissonIdeal A (trivialBracket A) P :=
  fun a p _ => P.zero_mem

/-- The Poisson core of `⊤` under the trivial bracket is `⊤`. -/
theorem trivial_core_top (A : Type) [CommRing A] [Algebra ℂ A] :
    poissonCore A (trivialBracket A) ⊤ = ⊤ := by
  apply le_antisymm (poissonCore_le A (trivialBracket A) ⊤)
  exact le_poissonCore A (trivialBracket A)
    ⟨le_rfl, trivial_poisson A ⊤⟩

/-- The universal property is usable: the core is the greatest Poisson
ideal below `J`. -/
example (A : Type) [CommRing A] [Algebra ℂ A]
    (br : PoissonBracket A) (J : Ideal A) :
    IsGreatest {P : Ideal A | P ≤ J ∧ IsPoissonIdeal A br P}
      (poissonCore A br J) :=
  poissonCore_isGreatest A br J

end MathlibExtTest.Algebra.Lie.PoissonBracket
