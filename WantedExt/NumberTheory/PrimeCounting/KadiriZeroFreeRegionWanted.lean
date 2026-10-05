module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Batteries.Util.ProofWanted

@[expose] public section

namespace MetaMathlibExt

/-!
## Kadiri zero-free region

`ζ(s) ≠ 0` for `Re s ≥ 1 - 1/(R_0 log|Im s|)` with `|Im s| ≥ 2` and
`R_0 = 5.70176`. This is the zero-free-region input to Dusart 2016
(whose tail theorem is filed alongside); Dusart cites the constant
`5.69693` from Kadiri's published version, a refinement of the
`5.70176` proved in the arXiv preprint sourced here.

Source: Habiba Kadiri, *Une région sans zéros pour la fonction zêta
de Riemann* (preprint), arXiv:math.NT/0401238, Théorème Principal,
TeX lines 142–148, <https://arxiv.org/html/math.NT/0401238>.
-/

/-- Kadiri's explicit zero-free region with `R_0 = 5.70176`. -/
public theorem_wanted kadiri_zero_free_region (s : ℂ)
    (ht : 2 ≤ |s.im|)
    (hσ : 1 - 1 / (5.70176 * Real.log |s.im|) ≤ s.re) :
    riemannZeta s ≠ 0

/-- Kadiri's refined zero-free region with `R_0 = 5.69693`, as cited in Dusart
2016: the region required by `dusart2016_tail_theorem`. -/
public theorem_wanted kadiri_zero_free_region_refined (s : ℂ)
    (ht : 2 ≤ |s.im|)
    (hσ : 1 - 1 / (5.69693 * Real.log |s.im|) ≤ s.re) :
    riemannZeta s ≠ 0

end MetaMathlibExt
