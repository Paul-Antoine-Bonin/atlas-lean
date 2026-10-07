module

public import Cslib.Computability.Languages.RegularLanguage
public import Mathlib.Computability.Language
public import Mathlib.Computability.RegularExpressions

open scoped Computability

/-!
# Generalized regular expressions

Mathlib's ordinary regular expressions extended with complement, with
concrete denotation into `Language`, star height, and regularity /
bounded-height predicates for the generalized star height problem.

## Main definitions

* `Cslib.Language.GenRegExp`: generalized regular expressions over an alphabet.
* `Cslib.Language.GenRegExp.denote`: denotation as a `Language`.
* `Cslib.Language.GenRegExp.starHeight`: generalized star height.
* `Cslib.Language.HasGenHeightLe`: bounded generalized star height.
Regularity is Mathlib's `Language.IsRegular`, shared with the rest of
`Cslib.Language`.
-/

@[expose] public section

namespace Cslib.Language

universe u

variable {α : Type u}

/-- Star height of an ordinary regular expression: the nesting depth of
`star` (`zero`, `epsilon`, and `char` have height zero). -/
def regularStarHeight : RegularExpression α → ℕ
  | .zero => 0
  | .epsilon => 0
  | .char _ => 0
  | .plus e₁ e₂ => max (regularStarHeight e₁) (regularStarHeight e₂)
  | .comp e₁ e₂ => max (regularStarHeight e₁) (regularStarHeight e₂)
  | .star e => regularStarHeight e + 1

/-- Generalized regular expressions: Mathlib's ordinary regular
expressions extended with complement. -/
inductive GenRegExp (α : Type u) : Type u
  | ofReg : RegularExpression α → GenRegExp α
  | compl : GenRegExp α → GenRegExp α
  | plus : GenRegExp α → GenRegExp α → GenRegExp α
  | comp : GenRegExp α → GenRegExp α → GenRegExp α
  | star : GenRegExp α → GenRegExp α

namespace GenRegExp

/-- Denotation of a generalized regular expression as a language. -/
def denote : GenRegExp α → Language α
  | .ofReg e => e.matches'
  | .compl e => (denote e)ᶜ
  | .plus e₁ e₂ => denote e₁ + denote e₂
  | .comp e₁ e₂ => denote e₁ * denote e₂
  | .star e => (denote e)∗

/-- Generalized star height: the nesting depth of `star`, counting stars
in the ordinary base expression as well. -/
def starHeight : GenRegExp α → ℕ
  | .ofReg e => regularStarHeight e
  | .compl e => starHeight e
  | .plus e₁ e₂ => max (starHeight e₁) (starHeight e₂)
  | .comp e₁ e₂ => max (starHeight e₁) (starHeight e₂)
  | .star e => starHeight e + 1

end GenRegExp

/-- A language has generalized star height at most `n`. -/
def HasGenHeightLe (L : Set (List α)) (n : ℕ) : Prop :=
  ∃ e : GenRegExp α, e.denote = L ∧ e.starHeight ≤ n

end Cslib.Language
