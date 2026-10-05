module

public import MathlibExt.Combinatorics.InfiniteWord.RPRelation

namespace MetaMathlibExt.ReversePermute

example (k : ℕ) (s : KString k) : rpRelation k s s :=
  ⟨Equiv.refl _, Or.inl (by simp)⟩

example (k : ℕ) (s : KString k) : rpRelation k s s.reverse :=
  ⟨Equiv.refl _, Or.inr (by simp)⟩

example : rpRelation 2 ([0, 0] : KString 2) ([1, 1] : KString 2) := by
  refine ⟨Equiv.swap 0 1, Or.inl ?_⟩
  decide

end MetaMathlibExt.ReversePermute
