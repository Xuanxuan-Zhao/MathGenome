import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.MeasureBridge
import MathGenome.Internal.MultivariableAnalysis.D04.C06.AbsoluteConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
open Set Filter MeasureTheory Topology
open scoped BigOperators ENNReal
namespace D04.MeasureBridge
open Darboux NullCovers DiscontinuityCriterion

variable {n : ℕ}

lemma volume_carrier (Q : Box n) :
    MeasureTheory.volume (carrier Q) = ENNReal.ofReal (content Q) := by
  rw [← coordinate_volume Q]
  have hp := (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
    (isClosed_carrier Q).measurableSet.nullMeasurableSet
  convert hp.symm using 2
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro hx; exact ⟨WithLp.toLp 2 x, hx, rfl⟩

lemma measurableSet_carrier (Q : Box n) : MeasurableSet (carrier Q) :=
  (isClosed_carrier Q).measurableSet

lemma null_measure_zero {S : Set (E n)} (hS : Null S) : MeasureTheory.volume S = 0 := by
  apply le_antisymm _ (zero_le)
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨ι, hι, Q, hcover, hsum⟩ := hS ε hε
  letI := hι
  calc
    MeasureTheory.volume S ≤ MeasureTheory.volume (⋃ i, carrier (Q i)) := measure_mono hcover
    _ ≤ ∑' i, MeasureTheory.volume (carrier (Q i)) := measure_iUnion_le _
    _ = ∑' i, ENNReal.ofReal (content (Q i)) := tsum_congr fun i => volume_carrier _
    _ ≤ 0 + (ε : ℝ≥0∞) := by simpa only [ENNReal.ofReal_coe_nnreal, zero_add] using hsum.le

lemma box_aemeasurable (f : E n → ℝ) (Q : Box n) (hf : Darboux.Integrable f Q) :
    AEMeasurable f (MeasureTheory.volume.restrict (carrier Q)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have he : f = fun _ => f 0 := funext fun x => congrArg f (Subsingleton.elim x 0)
    rw [he]
    exact measurable_const.aemeasurable
  · let D := discontinuitySet f Q
    let N := toMeasurable MeasureTheory.volume D
    have hD : MeasureTheory.volume D = 0 :=
      null_measure_zero ((integrable_iff_null_discontinuitySet hn f Q hf.1).mp hf)
    have hN : MeasureTheory.volume N = 0 := by
      dsimp [N]; rw [measure_toMeasurable, hD]
    have hs : MeasurableSet (carrier Q \ N) :=
      (measurableSet_carrier Q).diff (measurableSet_toMeasurable _ _)
    have hc : ContinuousOn f (carrier Q \ N) := by
      intro x hx
      have hcont : ContinuousWithinAt f (carrier Q) x := by
        by_contra h
        exact hx.2 (subset_toMeasurable _ _ (show x ∈ D from ⟨hx.1, h⟩))
      exact hcont.mono sdiff_subset
    have hm := hc.aemeasurable (μ := MeasureTheory.volume) hs
    rwa [Measure.restrict_congr_set (sdiff_null_ae_eq_self hN)] at hm

lemma box_integrableOn (f : E n → ℝ) (Q : Box n) (hf : Darboux.Integrable f Q) :
    IntegrableOn f (carrier Q) := by
  letI : IsFiniteMeasure (MeasureTheory.volume.restrict (carrier Q)) :=
    ⟨by simp [Measure.restrict_apply_univ, volume_carrier]⟩
  obtain ⟨M, hM, hb⟩ := exists_abs_bound hf.1
  exact (MeasureTheory.integrable_const M).mono' (box_aemeasurable f Q hf).aestronglyMeasurable
    ((ae_restrict_mem (measurableSet_carrier Q)).mono fun x hx => by simpa using hb x hx)

/-- Open parameter cells, transported to the actual Euclidean space. -/
def openCell {Q : Box n} (P : Grid Q) (c : CellIndex P) : Set (E n) :=
  openCarrier (cellBox P c)

lemma measurableSet_openCell {Q : Box n} (P : Grid Q) (c : CellIndex P) :
    MeasurableSet (openCell P c) := (isOpen_openCarrier _).measurableSet

lemma openCell_subset {Q : Box n} (P : Grid Q) (c : CellIndex P) :
    openCell P c ⊆ cell P c := openCarrier_subset _

lemma volume_openCell {Q : Box n} (P : Grid Q) (c : CellIndex P) :
    MeasureTheory.volume (openCell P c) = ENNReal.ofReal (cellContent P c) := by
  have hp := (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
    (measurableSet_openCell P c).nullMeasurableSet
  rw [← hp]
  convert openCoordinateCell_volume P c using 2
  ext x
  exact ⟨fun hx i _ => hx i, fun hx i => hx i (mem_univ _)⟩

lemma openCell_disjoint {Q : Box n} (P : Grid Q) :
    Pairwise (fun c d => Disjoint (openCell P c) (openCell P d)) := by
  intro c d hcd
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact Set.disjoint_left.mp (openCoordinateCell_disjoint P hcd)
    (show (fun i => x i) ∈ openCoordinateCell P c from fun i _ => hx i)
    (show (fun i => x i) ∈ openCoordinateCell P d from fun i _ => hy i)

lemma openCells_ae_carrier {Q : Box n} (P : Grid Q) :
    (⋃ c, openCell P c) =ᵐ[MeasureTheory.volume] carrier Q := by
  have hvol : MeasureTheory.volume (⋃ c, openCell P c) = MeasureTheory.volume (carrier Q) := by
    rw [measure_iUnion (openCell_disjoint P) (measurableSet_openCell P), tsum_fintype,
      volume_carrier]
    simp_rw [volume_openCell]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => cellContent_nonneg P c), content_partition]
  exact ae_eq_of_subset_of_measure_ge
    (iUnion_subset fun c => (openCell_subset P c).trans (cell_subset P c))
    hvol.ge (MeasurableSet.iUnion (measurableSet_openCell P)).nullMeasurableSet
    (by rw [volume_carrier]; exact ENNReal.ofReal_ne_top)

lemma setIntegral_grid {Q : Box n} (P : Grid Q) {f : E n → ℝ}
    (hf : IntegrableOn f (carrier Q)) :
    ∫ x in carrier Q, f x = ∑ c, ∫ x in openCell P c, f x := by
  rw [← Measure.restrict_congr_set (openCells_ae_carrier P), integral_iUnion_fintype]
  · exact measurableSet_openCell P
  · exact openCell_disjoint P
  · intro c; exact hf.mono_set ((openCell_subset P c).trans (cell_subset P c))

lemma lebesgue_darboux_bounds (f : E n → ℝ) (Q : Box n)
    (hf : Darboux.Integrable f Q) (P : Grid Q) :
    lowerSum f P ≤ ∫ x in carrier Q, f x ∧
      (∫ x in carrier Q, f x) ≤ upperSum f P := by
  have hi := box_integrableOn f Q hf
  rw [setIntegral_grid P hi]
  have hb (c : CellIndex P) :
      cellInfimum f P c * cellContent P c ≤ ∫ x in openCell P c, f x ∧
      (∫ x in openCell P c, f x) ≤ cellSupremum f P c * cellContent P c := by
    letI : IsFiniteMeasure (MeasureTheory.volume.restrict (openCell P c)) :=
      ⟨by simp [volume_openCell]⟩
    have hci := hi.mono_set ((openCell_subset P c).trans (cell_subset P c))
    have hconst (a : ℝ) : (∫ _ in openCell P c, a) = a * cellContent P c := by
      rw [setIntegral_const, measureReal_def, volume_openCell,
        ENNReal.toReal_ofReal (cellContent_nonneg P c), smul_eq_mul, mul_comm]
    constructor
    · rw [← hconst]
      exact MeasureTheory.integral_mono_ae (MeasureTheory.integrable_const _) hci
        ((ae_restrict_mem (measurableSet_openCell P c)).mono fun x hx =>
          cellInfimum_le f hf.1 P c (openCell_subset P c hx))
    · rw [← hconst]
      exact MeasureTheory.integral_mono_ae hci (MeasureTheory.integrable_const _)
        ((ae_restrict_mem (measurableSet_openCell P c)).mono fun x hx =>
          le_cellSupremum f hf.1 P c (openCell_subset P c hx))
  exact ⟨Finset.sum_le_sum (fun c _ => (hb c).1),
    Finset.sum_le_sum (fun c _ => (hb c).2)⟩

lemma box_integral_eq (f : E n → ℝ) (Q : Box n) (hf : Darboux.Integrable f Q) :
    Darboux.integral f Q hf = ∫ x in carrier Q, f x := by
  have hl : lowerIntegral f Q ≤ ∫ x in carrier Q, f x := by
    apply (lowerIntegral_isLUB f Q hf.1).2
    rintro _ ⟨P, rfl⟩
    exact (lebesgue_darboux_bounds f Q hf P).1
  have hu : (∫ x in carrier Q, f x) ≤ upperIntegral f Q := by
    apply (upperIntegral_isGLB f Q hf.1).2
    rintro _ ⟨P, rfl⟩
    exact (lebesgue_darboux_bounds f Q hf P).2
  exact le_antisymm hl (hu.trans_eq hf.2.symm)

lemma box_bridge (f : E n → ℝ) (Q : Box n) (hf : Darboux.Integrable f Q) :
    NullMeasurable ((carrier Q).indicator f) MeasureTheory.volume ∧
    MeasureTheory.Integrable ((carrier Q).indicator f) MeasureTheory.volume ∧
    Darboux.integral f Q hf = ∫ x in carrier Q, f x := by
  have hi := (integrable_indicator_iff (measurableSet_carrier Q)).mpr (box_integrableOn f Q hf)
  exact ⟨hi.aestronglyMeasurable.aemeasurable.nullMeasurable, hi, box_integral_eq f Q hf⟩

lemma region_bridge {S : Set (E n)} (f : S → ℝ) (hf : JordanRegions.RegionIntegrable f) :
    NullMeasurable (JordanRegions.zeroExtension f) MeasureTheory.volume ∧
    MeasureTheory.Integrable (JordanRegions.zeroExtension f) MeasureTheory.volume ∧
    JordanRegions.regionIntegral f = ∫ x, JordanRegions.zeroExtension f x := by
  obtain ⟨Q, hQ, hi⟩ := hf.2
  have he : (carrier Q).indicator (JordanRegions.zeroExtension f) = JordanRegions.zeroExtension f := by
    funext x
    by_cases hx : x ∈ carrier Q
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx, JordanRegions.zeroExtension_of_not_mem f
        (fun h => hx (JordanRegions.encloses_subset hQ h))]
  obtain ⟨hm, hL, heq⟩ := box_bridge (JordanRegions.zeroExtension f) Q hi
  rw [he] at hm hL
  refine ⟨hm, hL, ?_⟩
  rw [JordanRegions.integral_eq_on_enclosing_box f hf hQ hi, heq,
    ← integral_indicator (measurableSet_carrier Q), he]

lemma jordan_measure {S : Set (E n)} (hS : JordanRegions.Jordan S) :
    NullMeasurableSet S MeasureTheory.volume ∧
    MeasureTheory.volume S = ENNReal.ofReal (JordanRegions.volume S) := by
  have hr : JordanRegions.RegionIntegrable (fun _ : S => (1 : ℝ)) := by
    refine ⟨⟨1, fun _ => by norm_num⟩, ?_⟩
    obtain ⟨Q, hQ, hi⟩ := hS
    exact ⟨Q, hQ, hi⟩
  obtain ⟨hm, hi, heq⟩ := region_bridge (fun _ : S => (1 : ℝ)) hr
  have hfun : JordanRegions.zeroExtension (fun _ : S => (1 : ℝ)) = S.indicator (fun _ => 1) := by
    funext x
    by_cases hx : x ∈ S
    · simp [hx, Specs.D04.C06.JordanRegions.Model.zeroExtension]
    · simp [hx, Specs.D04.C06.JordanRegions.Model.zeroExtension]
  rw [hfun] at hm hi heq
  have hpre : (S.indicator (fun _ => (1 : ℝ))) ⁻¹' Ioi (1 / 2 : ℝ) = S := by
    ext x; by_cases hx : x ∈ S <;> norm_num [hx]
  have hs : NullMeasurableSet S MeasureTheory.volume :=
    hpre ▸ hm measurableSet_Ioi
  refine ⟨hs, ?_⟩
  rw [JordanRegions.regionIntegral_one, integral_indicator₀ hs, setIntegral_const,
    smul_eq_mul, mul_one] at heq
  have hfin : MeasureTheory.volume S ≠ ⊤ := by
    obtain ⟨Q, hQ, _⟩ := hS
    exact ne_top_of_le_ne_top (by rw [volume_carrier]; exact ENNReal.ofReal_ne_top)
      (measure_mono (JordanRegions.encloses_subset hQ))
  rw [heq, ofReal_measureReal hfin]

lemma zeroExtension_restrict {S : Set (E n)} (f : E n → ℝ) :
    JordanRegions.zeroExtension (fun x : S => f x) = S.indicator f := by
  funext x
  by_cases hx : x ∈ S
  · simp [hx, Specs.D04.C06.JordanRegions.Model.zeroExtension]
  · simp [hx, Specs.D04.C06.JordanRegions.Model.zeroExtension]

lemma region_bridge_ambient {S : Set (E n)} (f : E n → ℝ) (hS : MeasurableSet S)
    (hf : JordanRegions.RegionIntegrable (fun x : S => f x)) :
    IntegrableOn f S ∧ JordanRegions.regionIntegral (fun x : S => f x) = ∫ x in S, f x := by
  obtain ⟨_, hi, heq⟩ := region_bridge (fun x : S => f x) hf
  rw [zeroExtension_restrict] at hi heq
  refine ⟨(integrable_indicator_iff hS).mp hi, ?_⟩
  rw [integral_indicator hS] at heq
  exact heq

lemma improper_bridge {Ω : Set (E n)} {f : E n → ℝ} (hΩ : IsOpen Ω)
    (hf : ImproperExhaustions.AbsolutelyConvergent Ω f) :
    NullMeasurable (Ω.indicator f) MeasureTheory.volume ∧
    MeasureTheory.Integrable (Ω.indicator f) MeasureTheory.volume ∧
    AbsoluteConvergence.improperIntegral Ω f = ∫ x, Ω.indicator f x := by
  obtain ⟨K, hK⟩ := ImproperExhaustions.regular_exhaustion_exists Ω hΩ
  have hmono := ImproperExhaustions.regular_exhaustion_mono hK
  have hcover : AECover (MeasureTheory.volume.restrict Ω) atTop K := by
    refine ⟨?_, fun j => (hK.1 j).1.measurableSet⟩
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hK.2.2.symm ▸ hx)
    exact eventually_atTop.mpr ⟨j, fun k hk => hmono hk (interior_subset hj)⟩
  have hproper (j : ℕ) : IntegrableOn f (K j) ∧
      JordanRegions.regionIntegral (fun x : K j => f x) = ∫ x in K j, f x :=
    region_bridge_ambient f (hK.1 j).1.measurableSet
      (ImproperExhaustions.locally_integrable_on_compact_jordan hΩ hf.1 (hK.1 j))
  have hproperΩ (j : ℕ) : IntegrableOn f (K j) (MeasureTheory.volume.restrict Ω) := by
    rw [IntegrableOn, Measure.restrict_restrict_of_subset (hK.1 j).2.2]
    exact (hproper j).1
  have hnorm (j : ℕ) : (∫ x in K j, ‖f x‖) =
      JordanRegions.regionIntegral (fun x : K j => |f x|) := by
    simpa only [Real.norm_eq_abs] using
      (region_bridge_ambient (fun x => |f x|) (hK.1 j).1.measurableSet
        (ImproperExhaustions.locally_integrable_on_compact_jordan hΩ
          (AbsoluteConvergence.locally_integrable_abs hf.1) (hK.1 j))).2.symm
  have hiΩ : IntegrableOn f Ω :=
    hcover.integrable_of_integral_norm_bounded (ImproperExhaustions.absoluteMass Ω f).toReal
      hproperΩ (Eventually.of_forall fun j => by
        rw [Measure.restrict_restrict_of_subset (hK.1 j).2.2, hnorm]
        exact AbsoluteConvergence.integral_abs_le_mass hf.2 (hK.1 j))
  have hglobal := (integrable_indicator_iff hΩ.measurableSet).mpr hiΩ
  refine ⟨hglobal.aestronglyMeasurable.aemeasurable.nullMeasurable, hglobal, ?_⟩
  rw [integral_indicator hΩ.measurableSet]
  have hlim := hcover.integral_tendsto_of_countably_generated hiΩ
  have hR := (AbsoluteConvergence.absolute_exhaustion hΩ hf).1 K hK
  have heq : (fun j => ∫ x in K j, f x ∂MeasureTheory.volume.restrict Ω) =
      (fun j => JordanRegions.regionIntegral (fun x : K j => f x)) := by
    funext j
    rw [Measure.restrict_restrict_of_subset (hK.1 j).2.2, (hproper j).2]
  rw [heq] at hlim
  exact tendsto_nhds_unique hR hlim

end D04.MeasureBridge
