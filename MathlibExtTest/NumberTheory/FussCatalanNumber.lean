module

public import MathlibExt.NumberTheory.FussCatalanNumber

open MetaMathlibExt

private theorem t10 : fussCatalanNumber 1 0 (by decide) = 1 := rfl
private theorem t13 : fussCatalanNumber 1 3 (by decide) = 1 := rfl
private theorem t20 : fussCatalanNumber 2 0 (by decide) = 1 := rfl
private theorem t21 : fussCatalanNumber 2 1 (by decide) = 1 := rfl
private theorem t22 : fussCatalanNumber 2 2 (by decide) = 2 := rfl
private theorem t23 : fussCatalanNumber 2 3 (by decide) = 5 := rfl
private theorem t32 : fussCatalanNumber 3 2 (by decide) = 3 := rfl

private theorem fussCatalanNumber_proof_irrel (h₁ h₂ : 1 ≤ 2) :
    fussCatalanNumber 2 3 h₁ = fussCatalanNumber 2 3 h₂ :=
  rfl
