module

public import MathlibExt.NumberTheory.LSeries.RiemannZeta

@[expose] public section

/-!
# Tests for meromorphicity of the Riemann zeta function
-/

namespace RiemannZetaTest

example : MeromorphicOn riemannZeta Set.univ :=
  meromorphicOn_riemannZeta

/-- Meromorphic at the pole `s = 1`. -/
example : MeromorphicAt riemannZeta 1 :=
  meromorphicOn_riemannZeta 1 (Set.mem_univ _)

end RiemannZetaTest
