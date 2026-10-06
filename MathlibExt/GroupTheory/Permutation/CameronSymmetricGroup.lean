module

public import MathlibExt.GroupTheory.Permutation.HighlyHomogeneous
public import MathlibExt.GroupTheory.Permutation.PointwiseTopology

namespace MetaMathlibExt

@[expose] public section

/-- Cameron representative `S`: the full symmetric group is closed and highly homogeneous.

Scope: this proves only the representative `S`, not Cameron's exhaustive classification,
uniqueness, conjugacy, Parker-sequence claims, or the other four representatives.

References:
- Daniele A. Gewurz and Francesca Merola, *Sequences realized as Parker vectors of
  oligomorphic permutation groups*, Journal of Integer Sequences 6, source lines 331--359 at
  https://cs.uwaterloo.ca/journals/JIS/VOL6/Gewurz/gewurz22.tex; source SHA-256
  `aa62fa83a5a0944c6903374ab69e7ab8d597622de49c86684e44b75f76baca21`, span SHA-256
  `81f32b07c6496d97cbe329c5facf9480104f4afa49b8dfc347b1fd6b1e4f93c4`.
- Peter J. Cameron, "Transitivity of permutation groups on unordered sets,"
  *Mathematische Zeitschrift* 148(2) (1976), 127--139, DOI 10.1007/BF01214702.

Representation choice: `S` is the full symmetric group on the countably infinite set `ℚ`,
written `(⊤ : Subgroup (Equiv.Perm ℚ))`, with `ℚ` serving as a canonical countably
infinite carrier. The topology on `Equiv.Perm ℚ` is `Equiv.Perm.pointwiseTopology`
(pointwise convergence); the ordinary topology on `ℚ` itself is untouched. -/
public theorem cameron_symmetricGroup_closed_highlyHomogeneous :
    @IsClosed (Equiv.Perm ℚ) (Equiv.Perm.pointwiseTopology (α := ℚ))
        (↑(⊤ : Subgroup (Equiv.Perm ℚ)) : Set (Equiv.Perm ℚ)) ∧
      IsHighlyHomogeneous (⊤ : Subgroup (Equiv.Perm ℚ)) := by
  constructor
  · rw [Subgroup.coe_top]
    exact @isClosed_univ _ (Equiv.Perm.pointwiseTopology (α := ℚ))
  · exact isHighlyHomogeneous_top

end

end MetaMathlibExt
