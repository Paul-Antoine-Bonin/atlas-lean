module

import MathlibExt.Combinatorics.Words.KolakoskiSequence

namespace MetaMathlibExt

example (K : ℕ → ℕ) (h : IsKolakoski K) :
    K 1 = 1 ∧ K 2 = 2 ∧ K 3 = 2 ∧ K 4 = 1 :=
  ⟨h.one, h.two, h.three, h.four⟩

#print axioms kolakoskiBlockStart
#print axioms IsKolakoski
#print axioms IsKolakoski.two
#print axioms IsKolakoski.three
#print axioms IsKolakoski.four

end MetaMathlibExt
