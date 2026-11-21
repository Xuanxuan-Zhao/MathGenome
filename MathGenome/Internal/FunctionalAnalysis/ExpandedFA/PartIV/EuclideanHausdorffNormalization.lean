import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.EuclideanHausdorffNormalization
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

namespace ExpandedFA.EuclideanHausdorff

open MeasureTheory Measure Set Filter Metric Module
open scoped ENNReal Topology BigOperators

/-- The fixed scalar in the target, with the Euclidean (not supremum) metric. -/
def ballConstant (n : ℕ) : ℝ≥0∞ :=
  volume (ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2 : ℝ))

theorem ballConstant_pos (n : ℕ) : 0 < ballConstant n :=
  measure_ball_pos volume _ (by norm_num)

theorem ballConstant_ne_top (n : ℕ) : ballConstant n ≠ ⊤ :=
  measure_ball_lt_top.ne

/-- Ball scaling with exactly the coefficient appearing in the target.
All dimensions and nonnegative radii are allowed. -/
theorem volume_closedBall (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) {r : ℝ}
    (hr : 0 ≤ r) :
    volume (closedBall x r) = ballConstant n * ENNReal.ofReal (2 * r) ^ n := by
  have hh : volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2 : ℝ)) =
      ballConstant n := by
    change volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2 : ℝ)) =
      volume (ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2 : ℝ))
    rw [addHaar_closedBall volume _ (by norm_num)]
    conv_rhs => rw [addHaar_ball_of_pos volume _ (by norm_num)]
  have h := addHaar_closedBall_mul volume x (by positivity : 0 ≤ 2 * r)
    (by norm_num : 0 ≤ (1 / 2 : ℝ))
  rw [show 2 * r * (1 / 2) = r by ring, hh] at h
  rw [finrank_euclideanSpace, Fintype.card_fin,
    ENNReal.ofReal_pow (by positivity : 0 ≤ 2 * r)] at h
  exact h.trans (mul_comm _ _)

/-- The cost of a closed ball is no larger than its volume, with the exact scalar. -/
theorem ballConstant_mul_ediam_closedBall_pow_le (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    ballConstant n * ediam (closedBall x r) ^ n ≤ volume (closedBall x r) := by
  rw [volume_closedBall n x hr.le]
  gcongr
  exact ediam_le_of_forall_dist_le fun a ha b hb =>
    calc dist a b ≤ dist a x + dist b x := dist_triangle_right a b x
         _ ≤ r + r := add_le_add ha hb
         _ = 2 * r := by ring

/-- Arbitrarily small ball coverings have total volume at most `volume s + ε`.
No measurability or boundedness of `s` is imposed. -/
theorem small_ball_cover (n : ℕ) (s : Set (EuclideanSpace ℝ (Fin n)))
    {δ : ℝ} (hδ : 0 < δ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ (t : Set (EuclideanSpace ℝ (Fin n))) (r : EuclideanSpace ℝ (Fin n) → ℝ),
      t.Countable ∧ (∀ x ∈ t, 0 < r x ∧ 2 * r x < δ) ∧
      s ⊆ ⋃ x ∈ t, closedBall x (r x) ∧
      (∑' x : t, volume (closedBall (x : EuclideanSpace ℝ (Fin n)) (r x))) ≤ volume s + ε := by
  obtain ⟨t, r, ht, _, hr, hcover, hsum⟩ :=
    Besicovitch.exists_closedBall_covering_tsum_measure_le volume hε
      (fun _ : EuclideanSpace ℝ (Fin n) => Ioo 0 (δ / 2)) s
      (by
        intro x hx η hη
        refine ⟨min (δ / 2) η / 2, ?_, ?_⟩
        · constructor
          · positivity
          · have := min_le_left (δ / 2) η
            have := lt_min (by linarith : 0 < δ / 2) hη
            linarith
        · constructor
          · positivity
          · have := min_le_right (δ / 2) η
            have := lt_min (by linarith : 0 < δ / 2) hη
            linarith)
  exact ⟨t, r, ht, fun x hx => ⟨(hr x hx).1, by linarith [(hr x hx).2]⟩,
    hcover, hsum⟩

/-- The covering half of exact Euclidean normalization. -/
theorem scaled_hausdorffMeasure_le_volume (n : ℕ) :
    ballConstant n • (hausdorffMeasure (n : ℝ) : Measure (EuclideanSpace ℝ (Fin n))) ≤
      volume := by
  apply Measure.le_iff'.mpr
  intro s
  change ballConstant n * hausdorffMeasure (n : ℝ) s ≤ volume s
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hC0 := (ballConstant_pos n).ne'
  have hCt := ballConstant_ne_top n
  have hcover (k : ℕ) := small_ball_cover n s
    (δ := 1 / (k + 1 : ℝ)) (by positivity) (ε := (ε : ℝ≥0∞)) (by positivity)
  choose t r ht hr hcov hsum using hcover
  let (k : ℕ) : Countable (t k) := (ht k).to_subtype
  have hdiam (k : ℕ) (x : t k) :
      ediam (closedBall (x : EuclideanSpace ℝ (Fin n)) (r k x)) ≤
        ENNReal.ofReal (1 / (k + 1 : ℝ)) := by
    apply ediam_le_of_forall_dist_le
    intro a ha b hb
    calc dist a b ≤ dist a x + dist b x := dist_triangle_right a b x
         _ ≤ r k x + r k x := add_le_add ha hb
         _ ≤ 1 / (k + 1 : ℝ) := by linarith [(hr k x x.2).2]
  have hcost (k : ℕ) :
      (∑' x : t k, ediam (closedBall (x : EuclideanSpace ℝ (Fin n)) (r k x)) ^ (n : ℝ)) ≤
        (volume s + ε) / ballConstant n := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hC0) (Or.inl hCt)).mpr
    rw [mul_comm, ← ENNReal.tsum_mul_left]
    calc
      (∑' x : t k, ballConstant n *
          ediam (closedBall (x : EuclideanSpace ℝ (Fin n)) (r k x)) ^ (n : ℝ)) ≤
          ∑' x : t k, volume (closedBall (x : EuclideanSpace ℝ (Fin n)) (r k x)) := by
        apply ENNReal.tsum_le_tsum
        intro x
        rw [ENNReal.rpow_natCast]
        exact ballConstant_mul_ediam_closedBall_pow_le n x (hr k x x.2).1
      _ ≤ volume s + ε := hsum k
  have hH : hausdorffMeasure (n : ℝ) s ≤ (volume s + ε) / ballConstant n := by
    apply le_trans (hausdorffMeasure_le_liminf_tsum (n : ℝ) s
      (fun k : ℕ => ENNReal.ofReal (1 / (k + 1 : ℝ)))
      (by simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat)
      (fun k (x : t k) => closedBall (x : EuclideanSpace ℝ (Fin n)) (r k x))
      (Eventually.of_forall hdiam) (Eventually.of_forall (by simpa using hcov)))
    exact liminf_le_of_frequently_le (Frequently.of_forall hcost)
  simpa only [mul_comm] using
    (ENNReal.le_div_iff_mul_le (Or.inl hC0) (Or.inl hCt)).mp hH

/-- Dimension zero has unit point mass for the existing Euclidean volume. -/
theorem volume_singleton_zero : volume ({0} : Set (EuclideanSpace ℝ (Fin 0))) = 1 := by
  simpa [parallelepiped] using
    (EuclideanSpace.basisFun (Fin 0) ℝ).volume_parallelepiped

@[simp] theorem ballConstant_zero : ballConstant 0 = 1 := by
  have hb : ball (0 : EuclideanSpace ℝ (Fin 0)) (1 / 2 : ℝ) = {0} :=
    (nonempty_ball.mpr (by norm_num)).eq_zero
  change volume (ball (0 : EuclideanSpace ℝ (Fin 0)) (1 / 2 : ℝ)) = 1
  rw [hb, volume_singleton_zero]

/-- The complete target in dimension zero. -/
theorem normalization_zero :
    ballConstant 0 • (hausdorffMeasure (0 : ℝ) : Measure (EuclideanSpace ℝ (Fin 0))) =
      volume := by
  rw [ballConstant_zero, one_smul]
  ext s
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · rw [hs.eq_zero, hausdorffMeasure_zero_singleton, volume_singleton_zero]

/-- The sharp geometric estimate is sufficient for the other measure inequality.
This is a reduction lemma, not a certificate assumed by the target. -/
theorem volume_le_scaled_hausdorffMeasure_of_isodiametric (n : ℕ)
    (hiso : ∀ s : Set (EuclideanSpace ℝ (Fin n)),
      volume s ≤ ballConstant n * ediam s ^ n) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))) ≤
      ballConstant n • hausdorffMeasure (n : ℝ) := by
  have hC0 := (ballConstant_pos n).ne'
  have hCt := ballConstant_ne_top n
  have hH : (ballConstant n)⁻¹ • (volume : Measure (EuclideanSpace ℝ (Fin n))) ≤
      hausdorffMeasure (n : ℝ) := by
    apply le_hausdorffMeasure (n : ℝ) _ ⊤ (by simp)
    intro s _
    change (ballConstant n)⁻¹ * volume s ≤ ediam s ^ (n : ℝ)
    calc
      (ballConstant n)⁻¹ * volume s ≤
          (ballConstant n)⁻¹ * (ballConstant n * ediam s ^ n) := by gcongr; exact hiso s
      _ = ediam s ^ (n : ℝ) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hC0 hCt, one_mul, ENNReal.rpow_natCast]
  apply Measure.le_iff'.mpr
  intro s
  have hs := Measure.le_iff'.mp hH s
  change (ballConstant n)⁻¹ * volume s ≤ hausdorffMeasure (n : ℝ) s at hs
  change volume s ≤ ballConstant n * hausdorffMeasure (n : ℝ) s
  calc
    volume s = ballConstant n * ((ballConstant n)⁻¹ * volume s) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hC0 hCt, one_mul]
    _ ≤ ballConstant n * hausdorffMeasure (n : ℝ) s := by gcongr

/-- Assembly after a proof of the sharp isodiametric inequality. -/
theorem normalization_of_isodiametric (n : ℕ)
    (hiso : ∀ s : Set (EuclideanSpace ℝ (Fin n)),
      volume s ≤ ballConstant n * ediam s ^ n) :
    ballConstant n • (hausdorffMeasure (n : ℝ) : Measure (EuclideanSpace ℝ (Fin n))) =
      volume :=
  le_antisymm (scaled_hausdorffMeasure_le_volume n)
    (volume_le_scaled_hausdorffMeasure_of_isodiametric n hiso)

/-- The one-dimensional Euclidean metric has the usual real Hausdorff normalization. -/
theorem hausdorffMeasure_one_eq_volume :
    (hausdorffMeasure (1 : ℝ) : Measure (EuclideanSpace ℝ (Fin 1))) = volume := by
  let e : EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] ℝ :=
    (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm
  apply e.toHomeomorph.measurableEmbedding.map_injective
  exact (e.toIsometryEquiv.map_hausdorffMeasure 1).trans
    (hausdorffMeasure_real.trans e.measurePreserving.map_eq.symm)

@[simp] theorem ballConstant_one : ballConstant 1 = 1 := by
  let e : EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] ℝ :=
    (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm
  have h := e.measurePreserving.measure_preimage
    (s := ball (0 : ℝ) (1 / 2 : ℝ)) measurableSet_ball.nullMeasurableSet
  have he : e ⁻¹' ball (0 : ℝ) (1 / 2 : ℝ) =
      ball (0 : EuclideanSpace ℝ (Fin 1)) (1 / 2 : ℝ) := by
    simp
  change volume (ball (0 : EuclideanSpace ℝ (Fin 1)) (1 / 2 : ℝ)) = 1
  rw [← he, h, Real.ball_eq_Ioo, Real.volume_Ioo]
  norm_num

/-- The complete target in dimension one. -/
theorem normalization_one :
    ballConstant 1 • (hausdorffMeasure (1 : ℝ) : Measure (EuclideanSpace ℝ (Fin 1))) =
      volume := by
  rw [ballConstant_one, one_smul, hausdorffMeasure_one_eq_volume]

/-- A set symmetric about the origin lies in a ball of half its diameter.
This is the geometric endpoint of the finite Steiner symmetrization argument. -/
theorem subset_closedBall_half_diam_of_neg_mem {n : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : Bornology.IsBounded s)
    (hsymm : ∀ x ∈ s, -x ∈ s) : s ⊆ closedBall 0 (diam s / 2) := by
  intro x hx
  have h := dist_le_diam_of_mem hs hx (hsymm x hx)
  have hd : dist x (-x) = 2 * ‖x‖ := by
    rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ x, norm_smul]
    norm_num
  rw [hd] at h
  rw [mem_closedBall, dist_zero_right]
  linarith

/-- The sharp isodiametric bound for centrally symmetric bounded sets. -/
theorem volume_le_ball_half_diam_of_neg_mem {n : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : Bornology.IsBounded s)
    (hsymm : ∀ x ∈ s, -x ∈ s) :
    volume s ≤ volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (diam s / 2)) :=
  measure_mono (subset_closedBall_half_diam_of_neg_mem hs hsymm)

/-- A sharp compact-set isodiametric theorem implies the estimate for every set,
including nonmeasurable and unbounded sets. -/
theorem isodiametric_of_compact (n : ℕ)
    (hcompact : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      volume K ≤ volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (diam K / 2))) :
    ∀ s : Set (EuclideanSpace ℝ (Fin n)),
      volume s ≤ ballConstant n * ediam s ^ n := by
  intro s
  by_cases hn : n = 0
  · subst n
    rw [ballConstant_zero, pow_zero, mul_one]
    have hs : s ⊆ ({0} : Set (EuclideanSpace ℝ (Fin 0))) :=
      fun x _ => mem_singleton_iff.mpr (Subsingleton.elim _ _)
    exact (measure_mono hs).trans_eq volume_singleton_zero
  by_cases hb : Bornology.IsBounded s
  · calc
      volume s ≤ volume (closure s) := measure_mono subset_closure
      _ ≤ volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (diam (closure s) / 2)) :=
        hcompact _ hb.isCompact_closure
      _ = ballConstant n * ediam s ^ n := by
        rw [diam_closure, volume_closedBall n _ (by positivity), show 2 * (diam s / 2) = diam s by ring]
        rw [diam, ENNReal.ofReal_toReal hb.ediam_ne_top]
  · rw [ediam_of_unbounded hb, ENNReal.top_pow hn, ENNReal.mul_top (ballConstant_pos n).ne']
    exact le_top

/-- Reduction of exact normalization to compact sharp isodiametry. -/
theorem normalization_of_compact_isodiametric (n : ℕ)
    (hcompact : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      volume K ≤ volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (diam K / 2))) :
    ballConstant n • (hausdorffMeasure (n : ℝ) : Measure (EuclideanSpace ℝ (Fin n))) =
      volume :=
  normalization_of_isodiametric n (isodiametric_of_compact n hcompact)

set_option backward.isDefEq.respectTransparency false in
/-- The geometric input can be restricted to dimensions at least two;
the point and line cases above are already unconditional. -/
theorem normalization_of_compact_isodiametric_ge_two
    (hcompact : ∀ n : ℕ, 2 ≤ n →
      ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
        volume K ≤ volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (diam K / 2))) :
    Specs.ExpandedFA.PartIV.EuclideanHausdorffNormalization := by
  intro n
  change ballConstant n • (hausdorffMeasure (n : ℝ) : Measure (EuclideanSpace ℝ (Fin n))) = volume
  rcases n with _ | n
  · rw [Nat.cast_zero]
    exact normalization_zero
  rcases n with _ | n
  · rw [Nat.cast_one]
    exact normalization_one
  exact normalization_of_compact_isodiametric (n + 1 + 1) (hcompact (n + 1 + 1) (by omega))

namespace CoordinateSymmetrization
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Reflection in a coordinate hyperplane, on ordinary product coordinates. -/
def flip (i : ι) (x : ι → ℝ) : ι → ℝ := Function.update x i (-x i)

/-- Compact parameters for pairs on one coordinate fiber and a centered interval. -/
def source (i : ι) (K : Set (ι → ℝ)) : Set (((ι → ℝ) × (ι → ℝ)) × ℝ) :=
  {p | p.1.1 ∈ K ∧ p.1.2 ∈ K ∧
    (∀ j, j ≠ i → p.1.1 j = p.1.2 j) ∧ p.2 ∈ Icc (-1/2 : ℝ) (1/2)}

def centerMap (i : ι) (p : ((ι → ℝ) × (ι → ℝ)) × ℝ) : ι → ℝ :=
  Function.update p.1.1 i (p.2 * (p.1.1 i - p.1.2 i))

/-- Replace each nonempty coordinate fiber by the centered interval of its full span.
Unlike length-based Steiner symmetrization, this operation can increase volume;
that is sufficient for the sharp isodiametric inequality. -/
def hull (i : ι) (K : Set (ι → ℝ)) : Set (ι → ℝ) := centerMap i '' source i K

omit [Fintype ι] in
lemma continuous_centerMap (i : ι) : Continuous (centerMap (ι := ι) i) := by
  apply continuous_pi
  intro j
  by_cases h : j = i
  · subst j
    simp only [centerMap, Function.update_self]
    fun_prop
  · simpa [centerMap, h, Function.comp_def] using
      (continuous_apply j).comp (continuous_fst.comp continuous_fst)

omit [Fintype ι] in
lemma isCompact_hull (i : ι) {K : Set (ι → ℝ)} (hK : IsCompact K) :
    IsCompact (hull i K) := by
  apply IsCompact.image _ (continuous_centerMap i)
  have hc : IsClosed {p : ((ι → ℝ) × (ι → ℝ)) × ℝ |
      ∀ j, j ≠ i → p.1.1 j = p.1.2 j} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro j
    apply isClosed_iInter
    intro _
    exact isClosed_eq ((continuous_apply j).comp (continuous_fst.comp continuous_fst))
      ((continuous_apply j).comp (continuous_snd.comp continuous_fst))
  convert ((hK.prod hK).prod (isCompact_Icc (a := (-1/2 : ℝ)) (b := 1/2))).inter_right hc using 1
  ext p
  simp only [source, mem_ofPred_eq, mem_inter_iff, mem_prod]
  tauto

omit [Fintype ι] in
lemma mem_hull_iff {i : ι} {K : Set (ι → ℝ)} {x : ι → ℝ} :
    x ∈ hull i K ↔ ∃ a ∈ K, ∃ b ∈ K,
      (∀ j, j ≠ i → a j = x j ∧ b j = x j) ∧
        |x i| ≤ |a i - b i| / 2 := by
  constructor
  · rintro ⟨⟨⟨a,b⟩,t⟩, ⟨ha,hb,hab,ht⟩,rfl⟩
    refine ⟨a,ha,b,hb,?_,?_⟩
    · intro j hj
      simp only [centerMap, Function.update_of_ne hj]
      exact ⟨trivial, (hab j hj).symm⟩
    · simp only [centerMap, Function.update_self, abs_mul]
      have : |t| ≤ (1/2 : ℝ) := abs_le.mpr (by constructor <;> linarith [ht.1, ht.2])
      nlinarith [abs_nonneg (a i-b i)]
  · rintro ⟨a,ha,b,hb,hab,hx⟩
    by_cases hz : a i - b i = 0
    · have hxi : x i = 0 := by simpa [hz] using hx
      refine ⟨((a,b),0), ⟨ha,hb,?_,by norm_num⟩,?_⟩
      · intro j hj; exact (hab j hj).1.trans (hab j hj).2.symm
      · ext j
        by_cases hj : j=i
        · subst j; simp [centerMap, hxi]
        · simp [centerMap, hj, (hab j hj).1]
    · refine ⟨((a,b),x i / (a i-b i)), ⟨ha,hb,?_,?_⟩,?_⟩
      · intro j hj; exact (hab j hj).1.trans (hab j hj).2.symm
      · have ht : |x i / (a i-b i)| ≤ (1/2 : ℝ) := by
          rw [abs_div, div_le_iff₀ (abs_pos.mpr hz)]
          linarith
        constructor <;> linarith [(abs_le.mp ht).1, (abs_le.mp ht).2]
      · ext j
        by_cases hj : j=i
        · subst j; simp [centerMap, div_mul_cancel₀ _ hz]
        · simp [centerMap, hj, (hab j hj).1]

omit [Fintype ι] in
lemma flip_mem_hull {i : ι} {K : Set (ι → ℝ)} {x : ι → ℝ}
    (hx : x ∈ hull i K) : flip i x ∈ hull i K := by
  obtain ⟨a,ha,b,hb,hab,hbound⟩ := mem_hull_iff.mp hx
  apply mem_hull_iff.mpr
  refine ⟨a,ha,b,hb,?_,?_⟩
  · intro j hj; simpa [flip, hj] using hab j hj
  · simpa [flip] using hbound

omit [Fintype ι] in
lemma flip_mem_hull_of_flip_mem {i j : ι} (hij : i ≠ j)
    {K : Set (ι → ℝ)} (hK : ∀ x ∈ K, flip j x ∈ K)
    {x : ι → ℝ} (hx : x ∈ hull i K) : flip j x ∈ hull i K := by
  obtain ⟨a,ha,b,hb,hab,hbound⟩ := mem_hull_iff.mp hx
  apply mem_hull_iff.mpr
  refine ⟨flip j a,hK a ha,flip j b,hK b hb,?_,?_⟩
  · intro k hk
    by_cases hkj : k=j
    · subst k; simpa [flip] using And.intro
        (congrArg Neg.neg (hab j hij.symm).1) (congrArg Neg.neg (hab j hij.symm).2)
    · simpa [flip, hkj] using hab k hk
  · simpa [flip, hij] using hbound

omit [Fintype ι] in
lemma mem_hull_ordered {i : ι} {K : Set (ι → ℝ)} {x : ι → ℝ}
    (hx : x ∈ hull i K) : ∃ a ∈ K, ∃ b ∈ K,
      (∀ j, j ≠ i → a j = x j ∧ b j = x j) ∧
        b i ≤ a i ∧ |x i| ≤ (a i - b i) / 2 := by
  obtain ⟨a,ha,b,hb,hab,hbound⟩ := mem_hull_iff.mp hx
  rcases le_total (b i) (a i) with h | h
  · exact ⟨a,ha,b,hb,hab,h,by simpa [abs_of_nonneg (sub_nonneg.mpr h)] using hbound⟩
  · refine ⟨b,hb,a,ha,fun j hj => (hab j hj).symm,h,?_⟩
    rw [abs_of_nonpos (sub_nonpos.mpr h)] at hbound
    linarith

/-- Squared Euclidean distance, expressed in product coordinates. -/
def sqDist (x y : ι → ℝ) : ℝ := ∑ j, (x j-y j)^2

lemma sqDist_eq_erase (i : ι) (x y : ι → ℝ) :
    sqDist x y = (∑ j ∈ Finset.univ.erase i, (x j-y j)^2) + (x i-y i)^2 := by
  exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm

/-- Centering full fiber spans does not increase the Euclidean diameter bound. -/
lemma sqDist_hull_le (i : ι) {K : Set (ι → ℝ)} {D : ℝ}
    (hD : ∀ a ∈ K, ∀ b ∈ K, sqDist a b ≤ D)
    {x y : ι → ℝ} (hx : x ∈ hull i K) (hy : y ∈ hull i K) :
    sqDist x y ≤ D := by
  obtain ⟨a,ha,b,hb,hab,hab',hxi⟩ := mem_hull_ordered hx
  obtain ⟨c,hc,d,hd,hcd,hcd',hyi⟩ := mem_hull_ordered hy
  have hscalar : |x i-y i| ≤ max |a i-d i| |b i-c i| := by
    have hxy := abs_sub (x i) (y i)
    have h1 := le_abs_self (a i-d i)
    have h2 := neg_le_abs (b i-c i)
    have h3 := le_max_left |a i-d i| |b i-c i|
    have h4 := le_max_right |a i-d i| |b i-c i|
    linarith
  have had : (∑ j ∈ Finset.univ.erase i, (a j-d j)^2) =
      ∑ j ∈ Finset.univ.erase i, (x j-y j)^2 := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    rw [(hab j hji).1, (hcd j hji).2]
  have hbc : (∑ j ∈ Finset.univ.erase i, (b j-c j)^2) =
      ∑ j ∈ Finset.univ.erase i, (x j-y j)^2 := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    rw [(hab j hji).2, (hcd j hji).1]
  have h1 := hD a ha d hd
  have h2 := hD b hb c hc
  rw [sqDist_eq_erase i, had] at h1
  rw [sqDist_eq_erase i, hbc] at h2
  rw [sqDist_eq_erase i]
  rcases le_total |a i-d i| |b i-c i| with h | h
  · rw [max_eq_right h] at hscalar
    have := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hscalar
    rw [sq_abs, sq_abs] at this
    linarith
  · rw [max_eq_left h] at hscalar
    have := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hscalar
    rw [sq_abs, sq_abs] at this
    linarith


omit [Fintype ι] in
/-- Each compact one-dimensional section gains or preserves length. -/
lemma volume_fiber_le (i : ι) {K : Set (ι → ℝ)} (hK : IsCompact K) (p : ι → ℝ) :
    volume {t : ℝ | Function.update p i t ∈ K} ≤
      volume {t : ℝ | Function.update p i t ∈ hull i K} := by
  let F : Set ℝ := {t | Function.update p i t ∈ K}
  have hF : IsCompact F := (isClosedEmbedding_update p i).isCompact_preimage hK
  rcases F.eq_empty_or_nonempty with he | hne
  · change volume F ≤ _
    rw [he, measure_empty]
    exact bot_le
  obtain ⟨a,ha,hmin⟩ := hF.exists_isMinOn hne continuous_id.continuousOn
  obtain ⟨b,hb,hmax⟩ := hF.exists_isMaxOn hne continuous_id.continuousOn
  calc
    volume F ≤ volume (Icc a b) := measure_mono fun t ht => ⟨hmin ht, hmax ht⟩
    _ = volume (Icc (-(b-a)/2) ((b-a)/2)) := by
      simp only [Real.volume_Icc]
      congr 1
      ring
    _ ≤ volume {t : ℝ | Function.update p i t ∈ hull i K} := by
      apply measure_mono
      intro t ht
      apply mem_hull_iff.mpr
      refine ⟨Function.update p i b,hb,Function.update p i a,ha,?_,?_⟩
      · intro j hj; simp [hj]
      · simp only [Function.update_self]
        have ht' : |t| ≤ (b-a)/2 := abs_le.mpr (by constructor <;> linarith [ht.1,ht.2])
        exact ht'.trans (div_le_div_of_nonneg_right (le_abs_self _) (by norm_num))

/-- Cavalieri's principle gives the required nondecrease of volume. -/
lemma volume_le_hull {n : ℕ} (i : Fin (n+1)) {K : Set (Fin (n+1) → ℝ)}
    (hK : IsCompact K) : volume K ≤ volume (hull i K) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  have hmp : MeasurePreserving e.symm :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm
  rw [← hmp.measure_preimage hK.measurableSet.nullMeasurableSet,
    ← hmp.measure_preimage (isCompact_hull i hK).measurableSet.nullMeasurableSet]
  change (volume : Measure ℝ).prod volume (e.symm ⁻¹' K) ≤
    (volume : Measure ℝ).prod volume (e.symm ⁻¹' hull i K)
  rw [Measure.prod_apply_symm (e.symm.measurable hK.measurableSet),
    Measure.prod_apply_symm (e.symm.measurable (isCompact_hull i hK).measurableSet)]
  apply lintegral_mono
  intro p
  simpa [e, Fin.update_insertNth, Fin.insertNthEquiv, Set.preimage, Function.comp_def] using volume_fiber_le i hK (i.insertNth 0 p)


/-- Iterating finitely many coordinate operations preserves the diameter bound. -/
lemma finite_symmetrization {n : ℕ} {K : Set (Fin (n+1) → ℝ)}
    (hK : IsCompact K) {D : ℝ}
    (hD : ∀ x ∈ K, ∀ y ∈ K, sqDist x y ≤ D) (s : Finset (Fin (n+1))) :
    ∃ T : Set (Fin (n+1) → ℝ), IsCompact T ∧ volume K ≤ volume T ∧
      (∀ x ∈ T, ∀ y ∈ T, sqDist x y ≤ D) ∧
      (∀ i ∈ s, ∀ x ∈ T, flip i x ∈ T) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨K,hK,le_rfl,hD,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨T,hT,hvol,hdiam,hsymm⟩ := ih
    refine ⟨hull i T,isCompact_hull i hT,hvol.trans (volume_le_hull i hT),
      fun x hx y hy => sqDist_hull_le i hdiam hx hy,?_⟩
    intro j hj x hx
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact flip_mem_hull hx
    · exact flip_mem_hull_of_flip_mem (by intro h; subst j; exact hi hj) (hsymm j hj) hx

lemma neg_mem_of_flip_mem {T : Set (ι → ℝ)}
    (hT : ∀ i, ∀ x ∈ T, flip i x ∈ T) {x : ι → ℝ} (hx : x ∈ T) : -x ∈ T := by
  have h (s : Finset ι) : (fun j => if j ∈ s then -x j else x j) ∈ T := by
    induction s using Finset.induction_on with
    | empty => simpa using hx
    | @insert i s hi ih =>
      convert hT i _ ih using 1
      ext j
      by_cases hji : j=i
      · subst j; simp [flip, hi]
      · simp [flip, hji]
  change (fun j => -x j) ∈ T
  simpa using h Finset.univ


/-- Sharp compact Euclidean isodiametry, using only finitely many fiber hulls. -/
lemma compact_isodiametric_succ (n : ℕ)
    {K : Set (EuclideanSpace ℝ (Fin (n+1)))} (hK : IsCompact K) :
    volume K ≤ volume (closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) (diam K / 2)) := by
  let P : Set (Fin (n+1) → ℝ) := WithLp.toLp 2 ⁻¹' K
  have hP : IsCompact P :=
    (PiLp.homeomorph 2 (fun _ : Fin (n+1) => ℝ)).symm.isClosedEmbedding.isCompact_preimage hK
  have hvolP : volume P = volume K :=
    (PiLp.volume_preserving_toLp (Fin (n+1))).measure_preimage hK.measurableSet.nullMeasurableSet
  have hD : ∀ a ∈ P, ∀ b ∈ P, sqDist a b ≤ (diam K)^2 := by
    intro a ha b hb
    have hab := dist_le_diam_of_mem hK.isBounded ha hb
    have he : sqDist a b = dist (WithLp.toLp 2 a) (WithLp.toLp 2 b)^2 := by
      rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
      rfl
    rw [he]
    exact (sq_le_sq₀ dist_nonneg diam_nonneg).mpr hab
  obtain ⟨T,hT,hvolT,hdiamT,hsymmT⟩ := finite_symmetrization hP hD Finset.univ
  have hneg : ∀ x ∈ T, -x ∈ T :=
    fun x hx => neg_mem_of_flip_mem (fun i => hsymmT i (Finset.mem_univ i)) hx
  have hsub : WithLp.ofLp ⁻¹' T ⊆
      closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) (diam K / 2) := by
    intro x hx
    have hb := hdiamT (WithLp.ofLp x) hx (-WithLp.ofLp x) (hneg _ hx)
    have he : sqDist (WithLp.ofLp x) (-WithLp.ofLp x) = 4 * ‖x‖^2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      change (x j - -x j)^2 = 4*(x j)^2
      ring
    rw [he] at hb
    rw [mem_closedBall, dist_zero_right]
    nlinarith [norm_nonneg x, diam_nonneg (s := K)]
  calc
    volume K = volume P := hvolP.symm
    _ ≤ volume T := hvolT
    _ = volume (WithLp.ofLp ⁻¹' T : Set (EuclideanSpace ℝ (Fin (n+1)))) :=
      ((PiLp.volume_preserving_ofLp (Fin (n+1))).measure_preimage hT.measurableSet.nullMeasurableSet).symm
    _ ≤ _ := measure_mono hsub

end CoordinateSymmetrization

/-- Exact normalization of the raw Hausdorff measure, in every dimension.
The sharp constant follows from the compact fiber-hull isodiametric proof above. -/
theorem normalization : Specs.ExpandedFA.PartIV.EuclideanHausdorffNormalization := by
  apply normalization_of_compact_isodiametric_ge_two
  intro n hn K hK
  cases n with
  | zero => omega
  | succ n => exact CoordinateSymmetrization.compact_isodiametric_succ n hK

end ExpandedFA.EuclideanHausdorff
