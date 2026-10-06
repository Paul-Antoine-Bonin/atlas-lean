module

public import CSLibExt.Computability.CookLevin

@[expose] public section

set_option autoImplicit false

open Cslib.CookLevin

#check PolyManyOneRed
#check CNF
#check CNFSat
#check encodeCNF
#check decodeCNF
#check decodeCNF_eq_some_iff
#check encodeCNF_injective
#check encodeCNF_length
#check SATLang
#check satDec

example : CNFSat [[(0, true)]] := by
  refine ⟨fun _ => true, fun C h => ?_⟩
  have hC : C = [(0, true)] := by
    simpa only [List.mem_singleton] using h
  subst C
  exact ⟨0, true, by simp, rfl⟩

example : ¬ CNFSat [[(0, true)], [(0, false)]] := by
  rintro ⟨v, hv⟩
  obtain ⟨x1, b1, m1, e1⟩ := hv [(0, true)] (by simp)
  obtain ⟨x2, b2, m2, e2⟩ := hv [(0, false)] (by simp)
  have hm1 : x1 = 0 ∧ b1 = true := by
    simpa only [List.mem_singleton, Prod.mk.injEq] using m1
  have hm2 : x2 = 0 ∧ b2 = false := by
    simpa only [List.mem_singleton, Prod.mk.injEq] using m2
  obtain ⟨rfl, rfl⟩ := hm1
  obtain ⟨rfl, rfl⟩ := hm2
  rw [e1] at e2
  exact Bool.noConfusion e2

example : decodeCNF (encodeCNF []) = some [] := by simp

example : decodeCNF
    (encodeCNF [[(0, true), (5, false)], [], [(2, true)]]) =
      some [[(0, true), (5, false)], [], [(2, true)]] := by simp

example : decodeCNF [] = none := rfl
example : decodeCNF [true] = none := rfl
example : decodeCNF [false, true] = none := rfl
example : decodeNatPrefix [true, false, false] = none := rfl
example : decodeLit (encodeNatPrefix 3) = none := by
  unfold decodeLit
  rw [show decodeNatPrefix (encodeNatPrefix 3) =
      some (3, []) by
    simpa using decodeNatPrefix_encodeNatPrefix_append 3 []]
  rfl

example : encodeClause [] = [false] := rfl

example (n : Nat) (b : Bool) : encodeLit (n, b) =
    encodeNatPrefix n ++ [b] := rfl

example (φ ψ : CNF) (h : encodeCNF φ =
    encodeCNF ψ) : φ = ψ :=
  encodeCNF_injective h

example (input : List Bool) (φ : CNF) :
    decodeCNF input = some φ ↔ input = encodeCNF φ :=
  decodeCNF_eq_some_iff input φ

example : decodeClause
    (encodeClause [(2, false)] ++ [true]) =
      some ([(2, false)], [true]) := by simp
