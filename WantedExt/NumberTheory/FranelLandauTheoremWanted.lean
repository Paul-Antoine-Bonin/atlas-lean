module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import MathlibExt.NumberTheory.Farey

namespace MetaMathlibExt

open scoped BigOperators Asymptotics

@[expose] public section

/-- Franel-Landau theorem (statement_id `franel-landau-s1`, canonical name
"Franel-Landau theorem"): with `F_N = Farey.fareySeq N` and zero-based list
index `k`, let `δ_k = F_N[k] - k / (F_N.length - 1)`. The Riemann hypothesis
holds iff for every
`ε > 0`, `∑_k δ_k ^ 2 = O(N ^ (-1 + ε))` as `N → ∞`.
Source: https://en.wikipedia.org/wiki/Farey_sequence. -/
theorem_wanted franel_landau :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε →
        (fun N : ℕ => ∑ k : Fin (Farey.fareySeq N).length,
          ((((Farey.fareySeq N).get k : ℚ) : ℝ) -
            ((k : ℕ) : ℝ) / (((Farey.fareySeq N).length - 1 : ℕ) : ℝ)) ^ 2)
            =O[Filter.atTop]
        (fun N : ℕ => (N : ℝ) ^ (-1 + ε))

end

end MetaMathlibExt
