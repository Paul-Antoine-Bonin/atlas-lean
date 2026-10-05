module

public import MathlibExt.Analysis.SpecialFunctions.Elliptic.Order

/-!
# Tests for pole sets and elliptic order

Compile-time examples exercising `PeriodPair.poleMultiplicity`,
`PeriodPair.poleSetInFundamentalParallelogram`,
`PeriodPair.ellipticOrderInFundamentalParallelogram`, and `PeriodPair.ellipticOrder`.
It also contains an honest far-away failure witness: a function with pole
multiplicity one at `0` that is nonmeromorphic on every neighborhood of the
remote point `1`, hence not globally meromorphic.
-/

@[expose] public section

open scoped Topology

namespace PeriodPair

/-- The order of the local inverse pole, computed from public `meromorphicOrderAt`
lemmas. Only the behavior near `a` is used. -/
private lemma order_inv_sub_self (a : ℂ) :
    meromorphicOrderAt (fun z : ℂ => (z - a)⁻¹) a = -1 := by
  have h1 : meromorphicOrderAt (fun z : ℂ => z - a) a = 1 :=
    meromorphicOrderAt_id_sub_const
  have hinv : (fun z : ℂ => (z - a)⁻¹) = (fun z : ℂ => z - a)⁻¹ := rfl
  rw [hinv, meromorphicOrderAt_inv, h1]

/-- The multiplicity of the local inverse pole. -/
private lemma mult_inv_sub_self (a : ℂ) :
    poleMultiplicity (fun z : ℂ => (z - a)⁻¹) a = 1 := by
  unfold poleMultiplicity
  rw [order_inv_sub_self a]
  rfl

/-- A constant function has canonical elliptic order zero. -/
example (L : PeriodPair) (c : ℂ) :
    L.ellipticOrder (fun _ => c) (IsEllipticFunction.const L c) = 0 := by
  unfold ellipticOrder ellipticOrderInFundamentalParallelogram
  exact Finset.sum_eq_zero fun z _ => poleMultiplicity_const c z

/-- A constant function has arbitrary-vertex elliptic order zero. -/
example (L : PeriodPair) (c α : ℂ) :
    L.ellipticOrderInFundamentalParallelogram (fun _ => c) α
        (IsEllipticFunction.const L c) = 0 := by
  unfold ellipticOrderInFundamentalParallelogram
  exact Finset.sum_eq_zero fun z _ => poleMultiplicity_const c z

/-- Canonical and arbitrary-vertex orders agree on constants. -/
example (L : PeriodPair) (c α : ℂ) :
    L.ellipticOrder (fun _ => c) (IsEllipticFunction.const L c)
      = L.ellipticOrderInFundamentalParallelogram (fun _ => c) α
        (IsEllipticFunction.const L c) := by
  have hzero : ∀ (β : ℂ) (hβ : L.IsEllipticFunction (fun _ => c)),
      L.ellipticOrderInFundamentalParallelogram (fun _ => c) β hβ = 0 := by
    intro β hβ
    unfold ellipticOrderInFundamentalParallelogram
    exact Finset.sum_eq_zero fun z _ => poleMultiplicity_const c z
  unfold ellipticOrder
  rw [hzero, hzero]

/-- The genuinely local inverse pole has multiplicity one. The statement and proof
mention no global meromorphicity hypothesis: only the local order at `a` is used,
so the value cannot depend on the behavior of the function far from `a`. -/
example (a : ℂ) : poleMultiplicity (fun z : ℂ => (z - a)⁻¹) a = 1 :=
  mult_inv_sub_self a

/-- Locality under far-away modification: changing the function value at a point
`b ≠ a` does not affect the multiplicity at `a`, since the two functions agree on a
punctured neighborhood of `a`. -/
example (a b : ℂ) (hab : a ≠ b) :
    poleMultiplicity (fun z : ℂ => if z = b then (0 : ℂ) else (z - a)⁻¹) a
      = 1 := by
  have heq : (fun z : ℂ => if z = b then (0 : ℂ) else (z - a)⁻¹)
      =ᶠ[𝓝[≠] a] (fun z : ℂ => (z - a)⁻¹) := by
    have hb : {b}ᶜ ∈ 𝓝[≠] a :=
      mem_nhdsWithin_of_mem_nhds ((compl_singleton_mem_nhds_iff).mpr hab)
    filter_upwards [self_mem_nhdsWithin, hb] with z _ hzb
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hzb
    rw [ite_eq_right hzb]
  have hcongr : meromorphicOrderAt
      (fun z : ℂ => if z = b then (0 : ℂ) else (z - a)⁻¹) a
      = meromorphicOrderAt (fun z : ℂ => (z - a)⁻¹) a :=
    meromorphicOrderAt_congr heq
  unfold poleMultiplicity
  rw [hcongr, order_inv_sub_self a]
  rfl

/-- Complex conjugation is nowhere complex-differentiable. The complex derivative,
if it existed, would have to agree (as a real-linear map) with `conjCLE`, which
is not complex-linear: it fixes `1` but negates `Complex.I`. -/
private lemma not_differentiableAt_conj (b : ℂ) :
    ¬ DifferentiableAt ℂ (⇑(starRingEnd ℂ)) b := by
  intro h
  have hR := h.hasFDerivAt.restrictScalars ℝ
  have hconj : HasFDerivAt (⇑(starRingEnd ℂ))
      (Complex.conjCLE.toContinuousLinearMap) b :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt
  have heq : (fderiv ℂ (⇑(starRingEnd ℂ)) b).restrictScalars ℝ =
      Complex.conjCLE.toContinuousLinearMap := hR.unique hconj
  have h1 : fderiv ℂ (⇑(starRingEnd ℂ)) b 1 = (starRingEnd ℂ) (1 : ℂ) := by
    have hcon := DFunLike.congr_fun heq (1 : ℂ)
    simpa using hcon
  have hI : fderiv ℂ (⇑(starRingEnd ℂ)) b Complex.I = (starRingEnd ℂ) Complex.I := by
    have hcon := DFunLike.congr_fun heq Complex.I
    simpa using hcon
  have hlin : fderiv ℂ (⇑(starRingEnd ℂ)) b Complex.I
      = Complex.I • fderiv ℂ (⇑(starRingEnd ℂ)) b 1 := by
    have hIb : Complex.I • (1 : ℂ) = Complex.I := by simp
    conv_lhs => rw [← hIb]
    rw [map_smul]
  have hcon : (starRingEnd ℂ) Complex.I
      = Complex.I • (starRingEnd ℂ) (1 : ℂ) := by
    rw [← hI, ← h1]
    exact hlin
  have hneg : -Complex.I = Complex.I := by simpa using hcon
  have hsum : Complex.I + Complex.I = 0 := by linear_combination -hneg
  have hI0 : Complex.I = 0 := by
    have h2 : (2 : ℂ) * Complex.I = 0 := by linear_combination hsum
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  exact Complex.I_ne_zero hI0

/-- Complex conjugation is nowhere analytic. -/
private lemma not_analyticAt_conj (y : ℂ) : ¬ AnalyticAt ℂ (⇑(starRingEnd ℂ)) y :=
  fun hy => not_differentiableAt_conj y hy.differentiableAt

open Classical in
/-- A function with a genuine pole at `0` but no global meromorphicity: it agrees
with the inverse pole `z ↦ (z - 0)⁻¹` away from a small ball around the remote
point `1`, and equals complex conjugation on that ball. Unlike a single-point
value change (which preserves `MeromorphicAt` by punctured-locality, see above),
conjugation is nonmeromorphic on every neighborhood of `1`. -/
private noncomputable def poleWithConjBranch : ℂ → ℂ := fun z =>
  if z ∈ Metric.ball (1 : ℂ) (1 / 2 : ℝ) then (starRingEnd ℂ) z else (z - 0)⁻¹

/-- The test function agrees with the inverse pole near `0`, since `0` stays a
positive distance away from the conjugation ball around `1`. -/
private lemma poleWithConjBranch_eq_near_zero :
    poleWithConjBranch =ᶠ[𝓝 (0 : ℂ)] (fun z : ℂ => (z - 0)⁻¹) := by
  have h01 : dist (0 : ℂ) 1 = 1 := by rw [dist_comm, dist_zero_right, norm_one]
  have hnbhd : Metric.ball (0 : ℂ) (1 / 2 : ℝ) ∈ 𝓝 (0 : ℂ) :=
    Metric.ball_mem_nhds _ (by norm_num)
  filter_upwards [hnbhd] with z hz
  have hz_out : z ∉ Metric.ball (1 : ℂ) (1 / 2 : ℝ) := by
    rw [Metric.mem_ball] at hz ⊢
    have htri := dist_triangle (0 : ℂ) z (1 : ℂ)
    rw [h01, dist_comm (0 : ℂ) z] at htri
    linarith
  change poleWithConjBranch z = (z - 0)⁻¹
  unfold poleWithConjBranch
  exact ite_eq_right hz_out

/-- The test function has pole multiplicity one at `0`, by transport of the order
along the local equality above. Only the behavior near `0` is used. -/
example : poleMultiplicity poleWithConjBranch 0 = 1 := by
  have hne : poleWithConjBranch =ᶠ[𝓝[≠] (0 : ℂ)] (fun z : ℂ => (z - 0)⁻¹) :=
    poleWithConjBranch_eq_near_zero.filter_mono nhdsWithin_le_nhds
  have hcongr : meromorphicOrderAt poleWithConjBranch 0
      = meromorphicOrderAt (fun z : ℂ => (z - 0)⁻¹) 0 :=
    meromorphicOrderAt_congr hne
  unfold poleMultiplicity
  rw [hcongr, order_inv_sub_self 0]
  rfl

/-- The test function is not meromorphic at the remote point `1`: meromorphicity
there would force analyticity at some point of the conjugation ball, where the
function locally equals conjugation, contradicting nowhere-analyticity of
conjugation. The contradiction uses the whole ball, not a single value. -/
private lemma poleWithConjBranch_not_meromorphicAt :
    ¬ MeromorphicAt poleWithConjBranch 1 := by
  intro hf
  have hana := hf.eventually_analyticAt
  have hball_nhds : Metric.ball (1 : ℂ) (1 / 2 : ℝ) ∈ 𝓝 (1 : ℂ) :=
    Metric.ball_mem_nhds _ (by norm_num)
  have hmem : ∀ᶠ y in 𝓝[≠] (1 : ℂ), y ∈ Metric.ball (1 : ℂ) (1 / 2 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds hball_nhds
  obtain ⟨y, hy_ana, hy_ball⟩ := (hana.and hmem).exists
  have heq : poleWithConjBranch =ᶠ[𝓝 y] (⇑(starRingEnd ℂ)) := by
    filter_upwards [IsOpen.mem_nhds Metric.isOpen_ball hy_ball] with z hz
    unfold poleWithConjBranch
    rw [ite_eq_left hz]
  exact not_analyticAt_conj y (hy_ana.congr heq)

/-- Pointwise failure at the remote point. -/
example : ¬ MeromorphicAt poleWithConjBranch 1 :=
  poleWithConjBranch_not_meromorphicAt

/-- Hence the test function is not globally meromorphic. -/
example : ¬ Meromorphic poleWithConjBranch :=
  fun h => poleWithConjBranch_not_meromorphicAt (h 1)

/-- The Weierstrass function is elliptic, using the public Mathlib API. -/
example (L : PeriodPair) : L.IsEllipticFunction L.weierstrassP :=
  ⟨L.meromorphic_weierstrassP, L.periodic_weierstrassP⟩

/-- The Weierstrass function has a double pole at the origin, by the public order
computation `PeriodPair.order_weierstrassP`. -/
example (L : PeriodPair) : poleMultiplicity L.weierstrassP 0 = 2 := by
  have horder : meromorphicOrderAt L.weierstrassP 0 = -2 :=
    L.order_weierstrassP 0 (Submodule.zero_mem _)
  unfold poleMultiplicity
  rw [horder]
  rfl

/-- The origin lies in the pole set of the Weierstrass function at vertex `0`. -/
example (L : PeriodPair) :
    0 ∈ L.poleSetInFundamentalParallelogram L.weierstrassP 0 := by
  have h2 : poleMultiplicity L.weierstrassP 0 = 2 := by
    have horder : meromorphicOrderAt L.weierstrassP 0 = -2 :=
      L.order_weierstrassP 0 (Submodule.zero_mem _)
    unfold poleMultiplicity
    rw [horder]
    rfl
  rw [mem_poleSetInFundamentalParallelogram_iff]
  refine ⟨?_, by rw [h2]; decide⟩
  rw [fundamentalParallelogram_zero, ZSpan.mem_fundamentalDomain]
  intro i
  simp only [map_zero]
  exact Set.mem_Ico.mpr ⟨le_rfl, zero_lt_one⟩

/-- The vertex belongs to its own fundamental parallelogram (half-open convention:
`0 ≤ tᵢ` includes the lower boundary). -/
example (L : PeriodPair) (α : ℂ) : α ∈ L.fundamentalParallelogram α := by
  rw [mem_fundamentalParallelogram_iff]
  exact ⟨0, 0, le_rfl, one_pos, le_rfl, one_pos, by simp⟩

/-- The period translate `α + ω₁` lies outside the parallelogram (half-open
convention: `tᵢ < 1` excludes the upper boundary). -/
example (L : PeriodPair) (α : ℂ) :
    α + L.ω₁ ∉ L.fundamentalParallelogram α := by
  rw [mem_fundamentalParallelogram_iff]
  rintro ⟨t₁, t₂, _, h1, _, _, h⟩
  have hω : L.ω₁ = t₁ • L.ω₁ + t₂ • L.ω₂ := by
    have hcancel : α + L.ω₁ = α + (t₁ • L.ω₁ + t₂ • L.ω₂) := by
      calc α + L.ω₁ = α + t₁ • L.ω₁ + t₂ • L.ω₂ := h
        _ = α + (t₁ • L.ω₁ + t₂ • L.ω₂) := add_assoc _ _ _
    exact add_left_cancel_iff.mp hcancel
  have hr := congrArg (fun w => L.basis.repr w 0) hω
  rw [basis_repr_omega] at hr
  have hLHS : L.basis.repr L.ω₁ 0 = 1 := by
    have hrepr := L.basis_repr_omega 1 0 0
    simpa using hrepr
  rw [hLHS] at hr
  have ht1 : t₁ = 1 := by simpa using hr.symm
  linarith

/-- The transparent bridge between canonical and arbitrary-vertex order. -/
example (L : PeriodPair) {f : ℂ → ℂ} (hf : L.IsEllipticFunction f) :
    L.ellipticOrder f hf = L.ellipticOrderInFundamentalParallelogram f 0 hf :=
  ellipticOrder_eq_orderInFundamentalParallelogram_zero L hf

end PeriodPair

