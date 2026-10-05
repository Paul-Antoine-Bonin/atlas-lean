module

public import Mathlib.Data.Nat.Totient
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MetaMathlibExt

/-- Ford's totient multiplicity theorem (statement `ford-totient-s1`): every `k ≥ 2`
is the multiplicity of the totient function, i.e. some `m` has exactly `k` preimages
under `Nat.totient` (Ford 1999).
Primary source: Kevin Ford, *The Number of Solutions of phi(x) = m*,
Annals of Mathematics 150 (1999), DOI 10.2307/121103.
Also: https://en.wikipedia.org/wiki/Euler%27s_totient_function -/
theorem_wanted ford_totient_multiplicity :
    ∀ k : ℕ, 1 < k → ∃ m : ℕ, Set.ncard {x : ℕ | Nat.totient x = m} = k

end MetaMathlibExt
