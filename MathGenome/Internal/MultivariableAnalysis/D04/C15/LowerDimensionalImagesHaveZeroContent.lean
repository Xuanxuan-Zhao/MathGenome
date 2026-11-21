import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.LowerDimensionalImagesHaveZeroContent
import MathGenome.Internal.MultivariableAnalysis.D04.C06.ExceptionalSets
import MathGenome.Internal.MultivariableAnalysis.D04.C14.GraphTransitionsAndIntrinsicBoundary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

noncomputable section
open Set Filter Topology
open scoped BigOperators ContDiff NNReal
namespace D04.LowerDimensionalImages
open Darboux NullCovers DiscontinuityCriterion

/-- A coordinate width bound gives a Euclidean diameter bound, including
empty coordinate sets. -/
lemma box_dist_le {d : ℕ} (Q : Box d) {δ : ℝ} (hδ : 0 ≤ δ)
    (hw : ∀ i, Q.upper i - Q.lower i ≤ δ)
    {x y : E d} (hx : x ∈ carrier Q) (hy : y ∈ carrier Q) :
    dist x y ≤ Real.sqrt (d : ℝ) * δ := by
  rw [dist_eq_norm]
  apply (norm_le_sqrt_mul_maxNorm (x - y)).trans
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  rw [maxNorm_eq_coordinate_norm]
  apply (pi_norm_le_iff_of_nonneg hδ).mpr
  intro i
  change |x i - y i| ≤ δ
  exact abs_le.mpr ⟨by linarith [(hx i).1, (hy i).2, hw i],
    by linarith [(hx i).2, (hy i).1, hw i]⟩

private def span {d : ℕ} (Q : Box d) : ℝ :=
  1 + ∑ i, (Q.upper i - Q.lower i)

private lemma span_pos {d : ℕ} (Q : Box d) : 0 < span Q := by
  have := Finset.sum_nonneg (s := Finset.univ) (fun i _ => sub_nonneg.mpr (Q.ordered i))
  unfold span
  linarith

private lemma width_le_span {d : ℕ} (Q : Box d) (i : Fin d) :
    Q.upper i - Q.lower i ≤ span Q := by
  have := Finset.single_le_sum (s := Finset.univ)
    (fun j _ => sub_nonneg.mpr (Q.ordered j)) (Finset.mem_univ i)
  unfold span
  linarith

private def corner {d : ℕ} (Q : Box d) (δ : ℝ) (v : Fin d → ℕ) : E d :=
  WithLp.toLp 2 (fun i => min (Q.upper i) (Q.lower i + (v i : ℝ) * δ))

private lemma corner_mem {d : ℕ} (Q : Box d) {δ : ℝ} (hδ : 0 ≤ δ)
    (v : Fin d → ℕ) : corner Q δ v ∈ carrier Q := by
  intro i
  change Q.lower i ≤ min _ _ ∧ min _ _ ≤ Q.upper i
  exact ⟨le_min (Q.ordered i) (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hδ)), min_le_left _ _⟩

private def gridBox {d : ℕ} (Q : Box d) (δ : ℝ) (hδ : 0 ≤ δ)
    (v : Fin d → ℕ) : Box d where
  lower := corner Q δ v
  upper := WithLp.toLp 2 (fun i => min (Q.upper i) (corner Q δ v i + δ))
  ordered i := le_min (corner_mem Q hδ v i).2 (le_add_of_nonneg_right hδ)

private lemma gridBox_subset {d : ℕ} (Q : Box d) {δ : ℝ} (hδ : 0 ≤ δ)
    (v : Fin d → ℕ) : carrier (gridBox Q δ hδ v) ⊆ carrier Q := by
  intro x hx i
  exact ⟨(corner_mem Q hδ v i).1.trans (hx i).1,
    (hx i).2.trans (min_le_left _ _)⟩

private lemma gridBox_width {d : ℕ} (Q : Box d) {δ : ℝ} (hδ : 0 ≤ δ)
    (v : Fin d → ℕ) (i : Fin d) :
    (gridBox Q δ hδ v).upper i - (gridBox Q δ hδ v).lower i ≤ δ := by
  change min (Q.upper i) (corner Q δ v i + δ) - corner Q δ v i ≤ δ
  have := min_le_right (Q.upper i) (corner Q δ v i + δ)
  linarith

private lemma gridBox_cover {d : ℕ} (Q : Box d) {δ : ℝ} (hδ : 0 < δ) :
    carrier Q = ⋃ v : Fin d → Fin (⌈span Q / δ⌉₊ + 1),
      carrier (gridBox Q δ hδ.le (fun i => (v i).val)) := by
  apply Subset.antisymm
  · intro x hx
    let v : Fin d → Fin (⌈span Q / δ⌉₊ + 1) := fun i =>
      ⟨⌊(x i - Q.lower i) / δ⌋₊, Nat.lt_succ_of_le
        ((Nat.floor_le_floor ((div_le_div_iff_of_pos_right hδ).mpr
          ((sub_le_sub_right (hx i).2 _).trans (width_le_span Q i)))).trans
            (Nat.floor_le_ceil _))⟩
    refine mem_iUnion.mpr ⟨v, fun i => ?_⟩
    have hl := Nat.floor_le (div_nonneg (sub_nonneg.mpr (hx i).1) hδ.le)
    have hu := Nat.lt_floor_add_one ((x i - Q.lower i) / δ)
    have hl' : Q.lower i + (v i : ℝ) * δ ≤ x i := by
      have := (le_div_iff₀ hδ).mp hl
      change Q.lower i + (⌊(x i - Q.lower i) / δ⌋₊ : ℝ) * δ ≤ x i
      linarith
    have hu' : x i ≤ Q.lower i + (v i : ℝ) * δ + δ := by
      have := (div_lt_iff₀ hδ).mp hu
      change x i ≤ Q.lower i + (⌊(x i - Q.lower i) / δ⌋₊ : ℝ) * δ + δ
      nlinarith
    have hc : corner Q δ (fun i => (v i).val) i = Q.lower i + (v i : ℝ) * δ :=
      min_eq_right (hl'.trans (hx i).2)
    change corner Q δ (fun i => (v i).val) i ≤ x i ∧
      x i ≤ min (Q.upper i) (corner Q δ (fun i => (v i).val) i + δ)
    rw [hc]
    exact ⟨hl', le_min (hx i).2 hu'⟩
  · exact iUnion_subset fun v => gridBox_subset Q hδ.le _

private def cube {k : ℕ} (c : E k) (r : ℝ) (hr : 0 ≤ r) : Box k where
  lower := WithLp.toLp 2 (fun i => c i - r)
  upper := WithLp.toLp 2 (fun i => c i + r)
  ordered i := by change c i - r ≤ c i + r; linarith

private lemma cube_content {k : ℕ} (c : E k) (r : ℝ) (hr : 0 ≤ r) :
    content (cube c r hr) = (2 * r) ^ k := by
  simp [content, Specs.D04.C06.DarbouxIntegral.Model.content, cube,
    show ∀ i : Fin k, c i + r - (c i - r) = 2 * r by intro i; ring]

private lemma image_in_cube {d k : ℕ} (S : Set (E d)) (f : E d → E k)
    (L : ℝ≥0) (hL : LipschitzOnWith L f S) (A : Box d)
    {δ : ℝ} (hδ : 0 ≤ δ) (hw : ∀ i, A.upper i - A.lower i ≤ δ) :
    ∃ c : E k, f '' (S ∩ carrier A) ⊆
      carrier (cube c (((L : ℝ) * Real.sqrt d + 1) * δ) (by positivity)) := by
  by_cases he : (S ∩ carrier A).Nonempty
  · obtain ⟨x, hx⟩ := he
    refine ⟨f x, ?_⟩
    rintro z ⟨y, hy, rfl⟩ i
    have hn : ‖f y - f x‖ ≤ ((L : ℝ) * Real.sqrt d + 1) * δ := by
      have hdist := (hL.dist_le_mul y hy.1 x hx.1).trans
        (mul_le_mul_of_nonneg_left (box_dist_le A hδ hw hy.2 hx.2) L.coe_nonneg)
      rw [dist_eq_norm] at hdist
      nlinarith
    have hc := (PiLp.norm_apply_le (f y - f x) i).trans hn
    change |f y i - f x i| ≤ _ at hc
    change f x i - _ ≤ f y i ∧ f y i ≤ f x i + _
    exact ⟨by linarith [(abs_le.mp hc).1], by linarith [(abs_le.mp hc).2]⟩
  · exact ⟨0, by simp [Set.not_nonempty_iff_eq_empty.mp he]⟩

/-- The grid has at most ((span Q + 2) / δ)^d cells. -/
private lemma grid_count_bound {d : ℕ} (Q : Box d) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ((⌈span Q / δ⌉₊ + 1 : ℕ) : ℝ) ^ d ≤ ((span Q + 2) / δ) ^ d := by
  apply pow_le_pow_left₀ (by positivity)
  have hc := Nat.ceil_lt_add_one (div_nonneg (span_pos Q).le hδ.le)
  push_cast
  apply (le_div_iff₀ hδ).mpr
  have hc' : (⌈span Q / δ⌉₊ : ℝ) * δ < span Q + δ := by
    have := (mul_lt_mul_iff_left₀ hδ).mpr hc
    field_simp at this
    nlinarith
  nlinarith

/-- Quantitative finite-box covering estimate, uniform over 0 < δ ≤ 1. -/
theorem quantitative_cover :
    Specs.D04.C15.LowerDimensionalImagesHaveZeroContent.quantitative_coverType := by
  classical
  intro d k hdk Q S f L hS hL
  let B : ℝ := span Q + 2
  let H : ℝ := 2 * ((L : ℝ) * Real.sqrt d + 1)
  have hB : 0 < B := by dsimp [B]; linarith [span_pos Q]
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨B ^ d * H ^ k, mul_pos (pow_pos hB _) (pow_pos hH _), ?_⟩
  intro δ hδ hδ1
  let ι := Fin d → Fin (⌈span Q / δ⌉₊ + 1)
  let A : ι → Box d := fun v => gridBox Q δ hδ.le (fun i => (v i).val)
  have hc : ∀ v : ι, ∃ c : E k, f '' (S ∩ carrier (A v)) ⊆
      carrier (cube c (((L : ℝ) * Real.sqrt d + 1) * δ) (by positivity)) :=
    fun v => image_in_cube S f L hL (A v) hδ.le (gridBox_width Q hδ.le _)
  choose c hc using hc
  let R : ι → Box k := fun v =>
    cube (c v) (((L : ℝ) * Real.sqrt d + 1) * δ) (by positivity)
  refine ⟨ι, inferInstance, A, R, gridBox_cover Q hδ,
    (fun v => gridBox_subset Q hδ.le _), (fun v => gridBox_width Q hδ.le _), hc, ?_⟩
  have hR (v : ι) : content (R v) = (H * δ) ^ k := by
    rw [cube_content]
    congr 1
    dsimp [H]
    ring
  calc
    (∑ v : ι, content (R v)) = ((⌈span Q / δ⌉₊ + 1 : ℕ) : ℝ) ^ d * (H * δ) ^ k := by
      simp only [hR, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp [ι, Fintype.card_fin, Nat.cast_pow]
    _ ≤ (B / δ) ^ d * (H * δ) ^ k :=
      mul_le_mul_of_nonneg_right (grid_count_bound Q hδ hδ1) (by positivity)
    _ = (B ^ d * H ^ k) * δ ^ (k - d) := by
      rw [div_pow, mul_pow, show k = d + (k - d) from (Nat.add_sub_of_le hdk.le).symm,
        pow_add]
      simp only [Nat.add_sub_cancel_left]
      field_simp
      ring

/-- A finite box containing any bounded Euclidean set. -/
lemma bounded_subset_box {d : ℕ} {S : Set (E d)} (hS : Bornology.IsBounded S) :
    ∃ Q : Box d, S ⊆ carrier Q := by
  obtain ⟨r, hr, hSr⟩ := hS.subset_closedBall_lt 0 0
  refine ⟨cube (0 : E d) r hr.le, ?_⟩
  intro x hx i
  have hn : ‖x‖ ≤ r := by simpa using hSr hx
  have hc := (PiLp.norm_apply_le x i).trans hn
  change |x i| ≤ r at hc
  change 0 - r ≤ x i ∧ x i ≤ 0 + r
  simpa using abs_le.mp hc

/-- Small-scale coverings give content zero for the image of every bounded
subset on which the map is Lipschitz. -/
theorem lipschitz_image_contentZero :
    Specs.D04.C15.LowerDimensionalImagesHaveZeroContent.lipschitz_image_contentZeroType := by
  intro d k hdk S f L hS hL
  obtain ⟨Q, hSQ⟩ := bounded_subset_box hS
  obtain ⟨C, hC, hcover⟩ := quantitative_cover hdk Q S f L hSQ hL
  intro ε hε
  have hpow : k - d ≠ 0 := (Nat.sub_pos_of_lt hdk).ne'
  have hsmall : ∀ᶠ δ : ℝ in 𝓝 0, C * δ ^ (k - d) < ε := by
    have hc : Continuous (fun δ : ℝ => C * δ ^ (k - d)) := by fun_prop
    exact (hc.continuousAt (x := 0)).eventually
      (gt_mem_nhds (by simpa [hpow] using hε))
  obtain ⟨r, hr, hsmall⟩ := Metric.eventually_nhds_iff.mp hsmall
  let δ : ℝ := min (r / 2) 1
  have hδ : 0 < δ := lt_min (half_pos hr) zero_lt_one
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : C * δ ^ (k - d) < ε := hsmall (by
    change |δ - 0| < r
    rw [sub_zero, abs_of_pos hδ]
    exact (min_le_left (r / 2) 1).trans_lt (half_lt_self hr))
  obtain ⟨ι, hι, A, R, hA, hAQ, hw, hfR, hsum⟩ := hcover δ hδ hδ1
  let := hι
  refine ⟨ι, inferInstance, R, ?_, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    have hxA : x ∈ ⋃ i, carrier (A i) := by rw [← hA]; exact hSQ hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxA
    exact mem_iUnion.mpr ⟨i, hfR i ⟨x, ⟨hx, hxi⟩, rfl⟩⟩
  · rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => content_nonneg _)]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr (hsum.trans_lt hδε)

/-- Compactness of the image is obtained from Lipschitz continuity, not
inserted as an assumption. -/
theorem lipschitz_rectangle :
    Specs.D04.C15.LowerDimensionalImagesHaveZeroContent.lipschitz_rectangleType := by
  intro d k hdk Q f L hL
  exact ⟨(carrier_compact Q).image_of_continuousOn hL.continuousOn,
    lipschitz_image_contentZero hdk (carrier Q) f L (carrier_isBounded Q) hL⟩

/-- Local C¹ extensions on a compact parameter set give Lipschitz control
there. The conclusion says nothing about a noncompact chart domain. -/
theorem compact_C1_image :
    Specs.D04.C15.LowerDimensionalImagesHaveZeroContent.compact_C1_imageType := by
  intro d k hdk K f hK hf
  have hloc : LocallyLipschitzOn K f := by
    intro x hx
    obtain ⟨L, t, ht, hL⟩ := (hf x hx).exists_lipschitzOnWith
    exact ⟨L, t, mem_nhdsWithin_of_mem_nhds ht, hL⟩
  obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact hK
  exact ⟨hK.image_of_continuousOn hL.continuousOn,
    lipschitz_image_contentZero hdk K f L hK.isBounded hL⟩

/-- Local extensions only have to agree on the actual parameter set. -/
theorem compact_local_C1_image :
    Specs.D04.C15.LowerDimensionalImagesHaveZeroContent.compact_local_C1_imageType := by
  intro d k hdk K f hK hf
  have hloc : LocallyLipschitzOn K f := by
    intro x hx
    obtain ⟨U, g, hU, hg, heq⟩ := hf x hx
    obtain ⟨L, t, ht, hL⟩ := hg.exists_lipschitzOnWith
    refine ⟨L, K ∩ (U ∩ t), inter_mem_nhdsWithin K (inter_mem hU ht), ?_⟩
    intro y hy z hz
    rw [← heq ⟨hy.1, hy.2.1⟩, ← heq ⟨hz.1, hz.2.1⟩]
    exact hL hy.2.2 hz.2.2
  obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact hK
  exact ⟨hK.image_of_continuousOn hL.continuousOn,
    lipschitz_image_contentZero hdk K f L hK.isBounded hL⟩

/-- The dimensions of the finitely many pieces may differ. In particular,
zero-dimensional pieces are permitted. -/
theorem finite_C1_images :
    Specs.D04.C15.LowerDimensionalImagesHaveZeroContent.finite_C1_imagesType := by
  intro ι hι k d K f hdk hK hf
  have hh := fun i => compact_C1_image (hdk i) (K i) (f i) (hK i) (hf i)
  have hc : IsCompact (⋃ i, f i '' K i) := isCompact_iUnion (fun i => (hh i).1)
  exact ⟨hc, compact_null_contentZero _ hc
    (null_iUnion_countable _ (fun i => contentZero_null (hh i).2))⟩

theorem finite_local_C1_images :
    Specs.D04.C15.LowerDimensionalImagesHaveZeroContent.finite_local_C1_imagesType := by
  intro ι hι k d K f hdk hK hf
  have hh := fun i => compact_local_C1_image (hdk i) (K i) (f i) (hK i) (hf i)
  have hc : IsCompact (⋃ i, f i '' K i) := isCompact_iUnion (fun i => (hh i).1)
  exact ⟨hc, compact_null_contentZero _ hc
    (null_iUnion_countable _ (fun i => contentZero_null (hh i).2))⟩

/-- In positive target dimension every finite point image has content zero. -/
theorem finite_points :
    Specs.D04.C15.LowerDimensionalImagesHaveZeroContent.finite_pointsType := by
  intro k hk S hS
  exact compact_null_contentZero S hS.isCompact (countable_null hk hS.countable)

/-- Compact lower-dimensional pieces remain negligible in actual embedded
chart coordinates, including boundary charts. -/
theorem chart_overlap :
    Specs.D04.C15.LowerDimensionalImagesHaveZeroContent.chart_overlapType := by
  intro d k n M c hdk hkn K f hK hf htarget
  have hloc : LocallyLipschitzOn K (c.invFun ∘ f) := by
    intro x hx
    have hfx : f x ∈ M ∩ c.ambient := htarget ⟨x, hx, rfl⟩
    have hu := c.map_target hfx
    obtain ⟨O, J, hO, hcenter, hJ, heq⟩ :=
      chart_inverse_extension c (by constructor <;> norm_num [ManifoldRegularity,
        Specs.D04.C14.EmbeddedManifoldCharts.Model.ManifoldRegularity]) hkn (c.invFun (f x)) hu
    rw [c.right_inv _ hfx] at hcenter
    have hcomp : ContDiffAt ℝ 1 (J ∘ f) x :=
      (hJ.contDiffAt (hO.mem_nhds hcenter)).comp x (hf x hx)
    obtain ⟨L, t, ht, hL⟩ := hcomp.exists_lipschitzOnWith
    have hpre : f ⁻¹' O ∈ 𝓝 x :=
      (hf x hx).continuousAt.preimage_mem_nhds (hO.mem_nhds hcenter)
    refine ⟨L, K ∩ (t ∩ f ⁻¹' O), inter_mem_nhdsWithin K (inter_mem ht hpre), ?_⟩
    intro y hy z hz
    change edist (c.invFun (f y)) (c.invFun (f z)) ≤ _
    rw [← heq ⟨htarget ⟨y, hy.1, rfl⟩, hy.2.2⟩,
      ← heq ⟨htarget ⟨z, hz.1, rfl⟩, hz.2.2⟩]
    exact hL hy.2.1 hz.2.1
  obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact hK
  have hi : c.invFun '' (f '' K) = (c.invFun ∘ f) '' K := image_image _ _ _
  rw [hi]
  exact ⟨hK.image_of_continuousOn hL.continuousOn,
    lipschitz_image_contentZero hdk K (c.invFun ∘ f) L hK.isBounded hL⟩

/-- The same coordinate conclusion for pieces defined only by local C¹
extensions, as in the paper's boundary regularity convention. -/
theorem chart_local_overlap :
    Specs.D04.C15.LowerDimensionalImagesHaveZeroContent.chart_local_overlapType := by
  intro d k n M c hdk hkn K f hK hf htarget
  rw [image_image]
  apply compact_local_C1_image hdk K (c.invFun ∘ f) hK
  intro x hx
  obtain ⟨U, g, hU, hg, heqg⟩ := hf x hx
  have hfx : f x ∈ M ∩ c.ambient := htarget ⟨x, hx, rfl⟩
  obtain ⟨O, J, hO, hcenter, hJ, heqJ⟩ :=
    chart_inverse_extension c (by constructor <;> norm_num [ManifoldRegularity,
      Specs.D04.C14.EmbeddedManifoldCharts.Model.ManifoldRegularity])
      hkn (c.invFun (f x)) (c.map_target hfx)
  rw [c.right_inv _ hfx] at hcenter
  have hgx : g x = f x := heqg ⟨hx, mem_of_mem_nhds hU⟩
  have hgO : g x ∈ O := hgx.symm ▸ hcenter
  have hcomp : ContDiffAt ℝ 1 (J ∘ g) x :=
    (hJ.contDiffAt (hO.mem_nhds hgO)).comp x hg
  refine ⟨U ∩ g ⁻¹' O, J ∘ g,
    inter_mem hU (hg.continuousAt.preimage_mem_nhds (hO.mem_nhds hgO)), hcomp, ?_⟩
  intro y hy
  change J (g y) = c.invFun (f y)
  rw [heqg ⟨hy.1, hy.2.1⟩]
  exact heqJ ⟨htarget ⟨y, hy.1, rfl⟩, by
    rw [← heqg ⟨hy.1, hy.2.1⟩]; exact hy.2.2⟩

/-- Application to the established Darboux integral. -/
theorem coefficient_integral_zero :
    Specs.D04.C15.LowerDimensionalImagesHaveZeroContent.coefficient_integral_zeroType := by
  intro k hk S hS Q a ha hz
  exact ExceptionalSets.zero_off_contentZero hk ha hS hz

theorem coefficient_integral_unchanged :
    Specs.D04.C15.LowerDimensionalImagesHaveZeroContent.coefficient_integral_unchangedType := by
  intro k hk S hS Q a b ha hb heq
  exact ExceptionalSets.modification_contentZero hk ha hb hS heq

end D04.LowerDimensionalImages
