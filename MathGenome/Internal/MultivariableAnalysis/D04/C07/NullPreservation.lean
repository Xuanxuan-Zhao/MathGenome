import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.NullPreservation
import MathGenome.Internal.MultivariableAnalysis.D04.C06.JordanRegions
import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeInterfaces
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Topology.Bases

noncomputable section
open Set Filter Topology MeasureTheory
open scoped BigOperators ENNReal NNReal MeasureTheory
namespace D04.NullPreservation
open NullCovers Darboux JordanRegions

variable {n : ℕ}

/-- Box-cover nullity implies zero coordinate Lebesgue outer measure, using
only box volumes and countable subadditivity. -/
lemma coordinate_volume_zero_of_null {S : Set (E n)} (hS : Null S) :
    MeasureTheory.volume (WithLp.ofLp '' S) = 0 := by
  apply le_antisymm _ zero_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨ι, hι, Q, hQ, hsum⟩ := hS ε hε
  let := hι
  have hle : MeasureTheory.volume (WithLp.ofLp '' S) ≤
      ∑' i, ENNReal.ofReal (content (Q i)) := by
    calc
      _ ≤ MeasureTheory.volume (WithLp.ofLp '' (⋃ i, carrier (Q i))) := measure_mono (image_mono hQ)
      _ = MeasureTheory.volume (⋃ i, WithLp.ofLp '' carrier (Q i)) := by rw [image_iUnion]
      _ ≤ ∑' i, MeasureTheory.volume (WithLp.ofLp '' carrier (Q i)) := measure_iUnion_le _
      _ = _ := tsum_congr fun i => coordinate_volume (Q i)
  simpa using hle.trans hsum.le

/-- A bounded set in coordinate sup norm fits in the cube centered at any
one of its points with radius its diameter. -/
lemma exists_box_of_ediam {T : Set (Fin n → ℝ)} (hne : T.Nonempty)
    (hfin : Metric.ediam T ≠ ∞) :
    ∃ Q : Box n, T ⊆ WithLp.ofLp '' carrier Q ∧
      ENNReal.ofReal (content Q) = (2 : ℝ≥0∞)^n * Metric.ediam T ^ n := by
  let p := hne.choose
  let r := (Metric.ediam T).toReal
  have hr : 0 ≤ r := ENNReal.toReal_nonneg
  let Q : Box n := ⟨WithLp.toLp 2 (fun i => p i - r),
    WithLp.toLp 2 (fun i => p i + r), fun i => by change p i - r ≤ p i + r; linarith⟩
  refine ⟨Q, ?_, ?_⟩
  · intro x hx
    refine ⟨WithLp.toLp 2 x, ?_, rfl⟩
    have hd : dist x p ≤ r := Metric.dist_le_diam_of_mem (Metric.isBounded_iff_ediam_ne_top.mpr hfin)
      hx hne.choose_spec
    intro i
    have hi := (dist_pi_le_iff hr).mp hd i
    rw [Real.dist_eq] at hi
    change p i - r ≤ x i ∧ x i ≤ p i + r
    constructor <;> linarith [(abs_le.mp hi).1, (abs_le.mp hi).2]
  · have he : content Q = (2*r)^n := by
      simp [content, Specs.D04.C06.DarbouxIntegral.Model.content, Q,
        show ∀ i, p i + r - (p i - r) = 2*r from fun i => by ring]
    rw [he, ENNReal.ofReal_pow (mul_nonneg (by norm_num) hr),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hfin, mul_pow]
    norm_num

/-- Converse box-cover bridge, via the elementary diameter-cover formula
for Hausdorff measure in coordinate sup norm. No integral comparison or
change-of-variables theorem is used. -/
lemma null_of_coordinate_volume_zero (hn : 0 < n) {S : Set (E n)}
    (hS : MeasureTheory.volume (WithLp.ofLp '' S) = 0) : Null S := by
  classical
  intro ε hε
  let C : ℝ≥0∞ := (2 : ℝ≥0∞)^n
  have hC : C ≠ 0 := by simp [C]
  have hCt : C ≠ ∞ := by simp [C]
  have hδ : 0 < ENNReal.ofReal ε / C := ENNReal.div_pos (ENNReal.ofReal_pos.mpr hε).ne' hCt
  have hh : Measure.hausdorffMeasure (n : ℝ) (WithLp.ofLp '' S) = 0 := by
    simpa only [Fintype.card_fin] using (congrArg (fun μ : Measure (Fin n → ℝ) => μ (WithLp.ofLp '' S))
      (hausdorffMeasure_pi_real (ι := Fin n))).trans hS
  have hi :
    (⨅ (t : ℕ → Set (Fin n → ℝ)) (_ : WithLp.ofLp '' S ⊆ ⋃ k, t k)
      (_ : ∀ k, Metric.ediam (t k) ≤ 1),
        ∑' k, ⨆ _ : (t k).Nonempty, Metric.ediam (t k) ^ (n : ℝ)) ≤
      Measure.hausdorffMeasure (n : ℝ) (WithLp.ofLp '' S) := by
    rw [Measure.hausdorffMeasure_apply]
    refine le_iSup_of_le (1 : ℝ≥0∞) ?_
    exact le_iSup_of_le (by norm_num : (0 : ℝ≥0∞) < 1) le_rfl
  rw [hh] at hi
  have hlt := hi.trans_lt hδ
  simp only [iInf_lt_iff] at hlt
  obtain ⟨t, ht, hd, hsum⟩ := hlt
  let κ := {k : ℕ // (t k).Nonempty}
  have hfinite (k : κ) : Metric.ediam (t k) ≠ ∞ := ne_top_of_le_ne_top (by norm_num) (hd k)
  choose Q hQ hvol using fun k : κ => exists_box_of_ediam k.property (hfinite k)
  refine ⟨κ, inferInstance, Q, ?_, ?_⟩
  · intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp (ht (mem_image_of_mem WithLp.ofLp hx))
    obtain ⟨y, hy, he⟩ := hQ ⟨k, ⟨_, hk⟩⟩ hk
    have hyx : y = x := WithLp.ofLp_injective 2 he
    subst y
    exact mem_iUnion.mpr ⟨⟨k, ⟨_, hk⟩⟩, hy⟩
  · calc
      _ = C * ∑' k : κ, Metric.ediam (t k) ^ n := by
        simp_rw [hvol]; rw [ENNReal.tsum_mul_left]
      _ ≤ C * ∑' k, ⨆ _ : (t k).Nonempty, Metric.ediam (t k) ^ (n : ℝ) := by
        gcongr
        calc
          _ = ∑' k : κ, ⨆ _ : (t k).Nonempty, Metric.ediam (t k) ^ (n : ℝ) := by
            apply tsum_congr; intro k
            simp [k.property, ENNReal.rpow_natCast]
          _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective
            (f := fun k : κ => k.val) Subtype.coe_injective
            (fun k : ℕ => ⨆ _ : (t k).Nonempty, Metric.ediam (t k) ^ (n : ℝ))
      _ < C * (ENNReal.ofReal ε / C) := by
        simpa only [mul_comm] using ENNReal.mul_lt_mul_left hC hCt hsum
      _ = ENNReal.ofReal ε := ENNReal.mul_div_cancel hC hCt

/-- Lipschitz maps preserve Hausdorff-null sets in the same dimension. -/
lemma hausdorff_null_image {X Y : Type} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {L : ℝ≥0} {f : X → Y} {S : Set X} (hL : LipschitzOnWith L f S)
    {d : ℝ} (hd : 0 ≤ d) (hS : Measure.hausdorffMeasure d S = 0) :
    Measure.hausdorffMeasure d (f '' S) = 0 := by
  apply le_antisymm _ zero_le
  simpa [hS] using hL.hausdorffMeasure_image_le hd

/-- The coordinate and Euclidean metrics have the same null sets. -/
lemma null_iff_hausdorff_zero (hn : 0 < n) (S : Set (E n)) :
    Null S ↔ Measure.hausdorffMeasure (n : ℝ) S = 0 := by
  constructor
  · intro h
    have hz : Measure.hausdorffMeasure (n : ℝ) (WithLp.ofLp '' S) = 0 := by
      simpa only [Fintype.card_fin] using (congrArg (fun μ : Measure (Fin n → ℝ) => μ (WithLp.ofLp '' S))
        (hausdorffMeasure_pi_real (ι := Fin n))).trans (coordinate_volume_zero_of_null h)
    have hmap := hausdorff_null_image
      (PiLp.lipschitzWith_toLp 2 (fun _ : Fin n => ℝ)).lipschitzOnWith
      (Nat.cast_nonneg n) hz
    simpa only [image_image, Function.comp_def, WithLp.toLp_ofLp, image_id'] using hmap
  · intro h
    have hz := hausdorff_null_image
      (PiLp.lipschitzWith_ofLp 2 (fun _ : Fin n => ℝ)).lipschitzOnWith
      (Nat.cast_nonneg n) h
    apply null_of_coordinate_volume_zero hn
    have heq : (Measure.hausdorffMeasure (n : ℝ) : Measure (Fin n → ℝ)) =
        MeasureTheory.volume := by
      simpa only [Fintype.card_fin] using hausdorffMeasure_pi_real (ι := Fin n)
    rwa [heq] at hz

lemma lipschitzOn_null_image (hn : 0 < n) {F : E n → E n} {S : Set (E n)}
    {L : ℝ≥0} (hL : LipschitzOnWith L F S) (hS : Null S) : Null (F '' S) :=
  (null_iff_hausdorff_zero hn _).mpr
    (hausdorff_null_image hL (Nat.cast_nonneg n) ((null_iff_hausdorff_zero hn _).mp hS))

theorem c1_locally_lipschitz (U : Set (E n)) (F : E n → E n)
    (hU : IsOpen U) (hF : CrOn 1 U F) (x : E n) (hx : x ∈ U) :
    ∃ (L : ℝ≥0) (W : Set (E n)), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ LipschitzOnWith L F W := by
  have hc := (crOn_iff_contDiffOn 1 U F hU).mp hF
  obtain ⟨L, T, hT, hL⟩ := (hc.contDiffAt (hU.mem_nhds hx)).exists_lipschitzOnWith
  obtain ⟨W, hWT, hW, hxW⟩ := mem_nhds_iff.mp (inter_mem hT (hU.mem_nhds hx))
  exact ⟨L, W, hW, hxW, fun y hy => (hWT hy).2, hL.mono fun y hy => (hWT hy).1⟩

theorem c1_null_image (hn : 0 < n) (U : Set (E n)) (F : E n → E n)
    (hU : IsOpen U) (hF : CrOn 1 U F) (S : Set (E n)) (hSU : S ⊆ U) (hS : Null S) :
    Null (F '' S) := by
  classical
  choose L W hWo hxW hWU hL using fun x : U => c1_locally_lipschitz U F hU hF x x.property
  obtain ⟨A, hA, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  have hSA : S ⊆ ⋃ x : A, W x := by
    intro x hx
    have hmem : x ∈ ⋃ y : U, W y := mem_iUnion.mpr ⟨⟨x, hSU hx⟩, hxW ⟨x, hSU hx⟩⟩
    rw [← hcover] at hmem
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp hmem
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, hxy⟩
  let := hA.to_subtype
  apply null_mono (T := ⋃ x : A, F '' (S ∩ W x))
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hSA hx)
    exact mem_iUnion.mpr ⟨i, mem_image_of_mem F ⟨hx, hi⟩⟩
  · apply null_iUnion_countable
    intro x
    exact lipschitzOn_null_image hn ((hL x).mono inter_subset_right)
      (null_mono inter_subset_left hS)

theorem c1_contentZero_image (hn : 0 < n) (U : Set (E n)) (F : E n → E n)
    (hU : IsOpen U) (hF : CrOn 1 U F) (K : Set (E n)) (hKU : K ⊆ U)
    (hK : IsCompact K) (hz : ContentZero K) : ContentZero (F '' K) := by
  have hc : ContinuousOn F U := ((crOn_iff_contDiffOn 1 U F hU).mp hF).continuousOn
  exact compact_null_contentZero _ (hK.image_of_continuousOn (hc.mono hKU))
    (c1_null_image hn U F hU hF K hKU (contentZero_null hz))

/-- Compact containment excludes new ambient boundary points at the edge
of the source or target of a partial homeomorphism. -/
theorem diffeomorph_frontier (e : OpenPartialHomeomorph (E n) (E n))
    (S : Set (E n)) (hK : IsCompact (closure S)) (hU : closure S ⊆ e.source) :
    frontier (e '' S) = e '' frontier S := by
  have hSU : S ⊆ e.source := subset_closure.trans hU
  have htarget : e '' closure S ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hU hx)
  have hclosed : IsClosed (e '' closure S) :=
    (hK.image_of_continuousOn (e.continuousOn.mono hU)).isClosed
  have hcl : closure (e '' S) ⊆ e '' closure S :=
    closure_minimal (image_mono subset_closure) hclosed
  have hST : e '' S ⊆ e.target := (image_mono subset_closure).trans htarget
  have hi : e.IsImage S (e '' S) := OpenPartialHomeomorph.IsImage.of_image_eq (by
    rw [inter_eq_right.mpr hSU, inter_eq_right.mpr hST])
  have heq := hi.frontier.image_eq
  rw [inter_eq_right.mpr (frontier_subset_closure.trans hU),
    inter_eq_right.mpr (frontier_subset_closure.trans (hcl.trans htarget))] at heq
  exact heq.symm

theorem diffeomorph_jordan (hn : 0 < n)
    (e : OpenPartialHomeomorph (E n) (E n))
    (hF : CrOn 1 e.source e) (_hInv : CrOn 1 e.target e.symm)
    (S : Set (E n)) (hS : Jordan S) (hK : IsCompact (closure S))
    (hU : closure S ⊆ e.source) :
    Bornology.IsBounded (e '' S) ∧ Jordan (e '' S) ∧ frontier (e '' S) = e '' frontier S := by
  have hb : Bornology.IsBounded (e '' S) :=
    (hK.image_of_continuousOn (e.continuousOn.mono hU)).isBounded.subset (image_mono subset_closure)
  have heq := diffeomorph_frontier e S hK hU
  refine ⟨hb, (jordan_iff_boundary hn _ hb).mpr ?_, heq⟩
  rw [heq]
  exact c1_contentZero_image hn e.source e e.open_source hF (frontier S)
    (frontier_subset_closure.trans hU) (frontier_compact (jordan_bounded hS))
    ((jordan_iff_boundary hn _ (jordan_bounded hS)).mp hS)

end D04.NullPreservation
