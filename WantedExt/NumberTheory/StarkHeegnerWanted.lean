module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MetaMathlibExt

/-- Stark-Heegner theorem (statement `stark-heegner-s1`): an imaginary quadratic field
`ℚ(√(-d))` with `d` positive squarefree has class number one iff `d` is one of the nine
Heegner numbers.

Source: K. Heegner, *Diophantische Analysis und Modulfunktionen*,
Mathematische Zeitschrift 56 (1952), 227–253; A. Baker, *Linear forms in the
logarithms of algebraic numbers*, Mathematika 13–15 (1966–1968); H. M. Stark,
*A complete determination of the complex quadratic fields of class-number one*,
Michigan Mathematical Journal 14 (1967), 1–27; see also
https://en.wikipedia.org/wiki/Stark%E2%80%93Heegner_theorem. -/
theorem_wanted stark_heegner_theorem (d : ℕ) (hd_pos : 0 < d) (hd_sf : Squarefree d)
    (K : Type*) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 2)
    (hsqrt : ∃ x : K, x ^ 2 = algebraMap ℚ K (-(d : ℚ))) :
    NumberField.classNumber K = 1 ↔
    d ∈ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ)

end MetaMathlibExt

end
