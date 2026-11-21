import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.VitaliHahnSaks
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.VitaliHahnSaksUniformity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarRieszMarkov
import Mathlib.Analysis.SpecificLimits.Normed

/-! The countable-additivity stage and the compact weak-convergence application
 of Vitali--Hahn--Saks (paper.tex:9734--9814). -/

open Set Filter MeasureTheory
open scoped Topology ENNReal ZeroAtInfty Function
universe u

namespace ExpandedFA.Compactness.VitaliHahnSaks

open Specs.ExpandedFA.Compactness.VitaliHahnSaks
open VitaliHahnSaksUniformity
open FunctionSpaces.ScalarRieszMarkovSpec

section Limit
variable {α : Type u} [MeasurableSpace α]
variable {E : Type*} [NormedAddCommGroup E]

/-- Finite additivity and small-set continuity suffice for countable additivity.
 The proof uses the actual finite-subset filter in `HasSum`. -/
lemma hasSum_of_additive_of_small_sets
    (ρ : Measure α) [IsFiniteMeasure ρ] (m : Set α → E)
    (hadd : ∀ s t, MeasurableSet s → MeasurableSet t → Disjoint s t →
      m (s ∪ t) = m s + m t)
    (hzero : m ∅ = 0)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s, MeasurableSet s →
      ρ s < ENNReal.ofReal δ → ‖m s‖ < ε)
    {f : ℕ → Set α} (hf : ∀ n, MeasurableSet (f n))
    (hd : Pairwise (Disjoint on f)) : HasSum (fun n => m (f n)) (m (⋃ n, f n)) := by
  classical
  have hfin (F : Finset ℕ) : m (⋃ i ∈ F, f i) = ∑ i ∈ F, m (f i) := by
    induction F using Finset.induction with
    | empty => simpa using hzero
    | @insert a F ha ih =>
      simp only [Finset.set_biUnion_insert, Finset.sum_insert ha]
      rw [hadd _ _ (hf a) (Finset.measurableSet_biUnion _ (fun i _ => hf i)), ih]
      simp only [Set.disjoint_iUnion_right]
      intro i hi
      exact hd (by intro h; subst i; exact ha hi)
  change Tendsto (fun F : Finset ℕ => ∑ i ∈ F, m (f i)) atTop _
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hsmallδ⟩ := hsmall ε hε
  have htail := tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
    (μ := ρ) (fun i => (hf i).nullMeasurableSet) hd
  have hevent : ∀ᶠ n in atTop, ρ (⋃ i ∈ Set.Ici n, f i) < ENNReal.ofReal δ :=
    (tendsto_order.1 htail).2 _ (ENNReal.ofReal_pos.mpr hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  filter_upwards [eventually_ge_atTop (Finset.range N)] with F hF
  let A := ⋃ i ∈ F, f i
  have hA : MeasurableSet A := Finset.measurableSet_biUnion _ (fun i _ => hf i)
  have hU : MeasurableSet (⋃ i, f i) := MeasurableSet.iUnion hf
  have hAU : A ⊆ ⋃ i, f i := by
    intro x hx; simp only [A, mem_iUnion] at hx ⊢
    obtain ⟨i, _, hxi⟩ := hx; exact ⟨i, hxi⟩
  have hsub : (⋃ i, f i) \ A ⊆ ⋃ i ∈ Set.Ici N, f i := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx.1
    have hNi : N ≤ i := by
      by_contra h
      have hiF : i ∈ F := hF (Finset.mem_range.2 (lt_of_not_ge h))
      exact hx.2 (by simp only [A, mem_iUnion]; exact ⟨i, hiF, hi⟩)
    exact mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨hNi, hi⟩⟩
  have heq : m (⋃ i, f i) = m A + m ((⋃ i, f i) \ A) := by
    rw [← hadd A _ hA (hU.diff hA) disjoint_sdiff_right, union_sdiff_cancel hAU]
  rw [← hfin F, dist_eq_norm, norm_sub_rev, heq, add_sub_cancel_left]
  exact hsmallδ _ (hU.diff hA) ((measure_mono hsub).trans_lt (hN N le_rfl))

/-- Construct the countably additive limit from setwise convergence and uniform
 small-set control of the original scalar values. -/
lemma exists_vectorMeasure_limit
    (ρ : Measure α) [IsFiniteMeasure ρ] (μ : ℕ → VectorMeasure α E)
    (hconv : ∀ s, MeasurableSet s → ∃ l : E,
      Tendsto (fun n => μ n s) atTop (𝓝 l))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s, MeasurableSet s →
      ρ s < ENNReal.ofReal δ → ∀ n, ‖μ n s‖ < ε) :
    ∃ ν : VectorMeasure α E,
      (∀ s, MeasurableSet s → Tendsto (fun n => μ n s) atTop (𝓝 (ν s))) ∧
      (∀ s, MeasurableSet s → ρ s = 0 → ν s = 0) := by
  classical
  let m : Set α → E := fun s => if hs : MeasurableSet s then (hconv s hs).choose else 0
  have hm s : Tendsto (fun n => μ n s) atTop (𝓝 (m s)) := by
    by_cases hs : MeasurableSet s
    · simpa only [m, dite_eq_left hs] using (hconv s hs).choose_spec
    · simp [m, hs, VectorMeasure.not_measurable]
  have hadd s t (hs : MeasurableSet s) (ht : MeasurableSet t) (hd : Disjoint s t) :
      m (s ∪ t) = m s + m t := by
    apply tendsto_nhds_unique (hm (s ∪ t))
    simpa only [VectorMeasure.of_union hd hs ht] using (hm s).add (hm t)
  have hzero : m ∅ = 0 := by
    exact tendsto_nhds_unique (hm ∅) (by simp)
  have hmsmall : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s, MeasurableSet s →
      ρ s < ENNReal.ofReal δ → ‖m s‖ < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδsmall⟩ := hsmall (ε / 2) (by positivity)
    refine ⟨δ, hδ, fun s hs hρ => ?_⟩
    have hle : ‖m s‖ ≤ ε / 2 := le_of_tendsto (hm s).norm
      (Eventually.of_forall fun n => (hδsmall s hs hρ n).le)
    exact hle.trans_lt (by linarith)
  let ν : VectorMeasure α E :=
    { measureOf' := m
      empty' := hzero
      not_measurable' := fun s hs => by simp [m, hs]
      m_iUnion' := fun f hf hd => hasSum_of_additive_of_small_sets ρ m hadd hzero hmsmall hf hd }
  refine ⟨ν, fun s _ => hm s, fun s hs hρ => ?_⟩
  change m s = 0
  apply norm_eq_zero.1
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_gt
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hmsmall ε hε
  exact h s hs (by rw [hρ]; exact ENNReal.ofReal_pos.mpr hδ)

end Limit

/-- Native signed measures have finite total variation. -/
lemma signed_variation_finite {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α) :
    IsFiniteMeasure ν.variation := by
  rw [← ν.totalVariation_eq_variation]
  infer_instance

/-- Finiteness in the complex case follows from the real and imaginary parts. -/
lemma complex_variation_finite {α : Type u} [MeasurableSpace α] (ν : ComplexMeasure α) :
    IsFiniteMeasure ν.variation :=
  isFiniteMeasure_of_le (ν.re.totalVariation + ν.im.totalVariation) (complex_variation_le ν)

lemma limit_conclusion_of_uniform {α : Type u} [MeasurableSpace α]
    {𝕜 : Type*} [RCLike 𝕜] (ρ : Measure α) [IsFiniteMeasure ρ]
    (μ : ℕ → VectorMeasure α 𝕜)
    (hfinite : ∀ ν : VectorMeasure α 𝕜, IsFiniteMeasure ν.variation)
    (hconv : ∀ s, MeasurableSet s → ∃ l : 𝕜,
      Tendsto (fun n => μ n s) atTop (𝓝 l))
    (huniform : UniformVariation ρ μ) : LimitConclusion ρ μ := by
  have hsmall : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s, MeasurableSet s →
      ρ s < ENNReal.ofReal δ → ∀ n, ‖μ n s‖ < ε := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := huniform ε hε
    refine ⟨δ, hδ, fun s hs hρ n => ?_⟩
    have hvar := (le_iSup (fun n => (μ n).variation s) n).trans_lt (h s hs hρ)
    have : IsFiniteMeasure (μ n).variation := hfinite _
    exact (VectorMeasure.norm_measure_le_variation (μ := μ n)).trans_lt
      (ENNReal.toReal_lt_of_lt_ofReal hvar)
  obtain ⟨ν, hνconv, hνac⟩ := exists_vectorMeasure_limit ρ μ hconv hsmall
  refine ⟨ν, ⟨hfinite ν, hνconv, hνac⟩, ?_⟩
  intro η hη
  ext s hs
  exact tendsto_nhds_unique (hη.2.1 s hs) (hνconv s hs)

/-- Full finite-control-measure theorem for signed measures. -/
theorem vitali_hahn_saks_signed : SignedTheorem.{u} := by
  intro α _ ρ _ μ hac hconv
  have hu : UniformVariation ρ μ := by
    simpa only [UniformVariation, ← SignedMeasure.totalVariation_eq_variation] using
      uniform_variation_signed ρ μ hac hconv
  exact ⟨hu, limit_conclusion_of_uniform ρ μ signed_variation_finite hconv hu⟩

/-- Full finite-control-measure theorem for complex measures. -/
theorem vitali_hahn_saks_complex : ComplexTheorem.{u} := by
  intro α _ ρ _ μ hac hconv
  have hu : UniformVariation ρ μ := uniform_variation_complex ρ μ hac hconv
  exact ⟨hu, limit_conclusion_of_uniform ρ μ complex_variation_finite hconv hu⟩

section Control
variable {X : Type u} [MeasurableSpace X] {𝕜 : Type*} [RCLike 𝕜]

/-- Each summand has mass at most its geometric coefficient. -/
lemma control_summand_mass_le (μ : ℕ → VectorMeasure X 𝕜)
    (hfinite : ∀ n, IsFiniteMeasure (μ n).variation) (n : ℕ) :
    (ENNReal.ofReal ((1 / 2 : ℝ)^n / (1 + (μ n).variation.real univ)) •
      (μ n).variation) univ ≤ ENNReal.ofReal ((1 / 2 : ℝ)^n) := by
  have : IsFiniteMeasure (μ n).variation := hfinite n
  let b := (μ n).variation.real univ
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  have hb1 : 0 < 1 + b := by positivity
  rw [Measure.smul_apply, smul_eq_mul]
  have heq : (μ n).variation univ = ENNReal.ofReal b := by
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  rw [heq, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  change (1 / 2 : ℝ)^n / (1 + b) * b ≤ (1 / 2 : ℝ)^n
  calc
    _ ≤ (1 / 2 : ℝ)^n / (1 + b) * (1 + b) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := div_mul_cancel₀ _ hb1.ne'

lemma control_measure_finite (μ : ℕ → VectorMeasure X 𝕜)
    (hfinite : ∀ n, IsFiniteMeasure (μ n).variation) :
    IsFiniteMeasure (controlMeasure μ) := by
  constructor
  rw [controlMeasure, Measure.sum_apply _ MeasurableSet.univ]
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (control_summand_mass_le μ hfinite))
  exact (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).tsum_ofReal_lt_top

lemma control_measure_dominates (μ : ℕ → VectorMeasure X 𝕜) (n : ℕ) :
    (μ n).variation ≪ controlMeasure μ := by
  apply Measure.absolutelyContinuous_sum_right n
  apply Measure.absolutelyContinuous_smul
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  exact div_pos (pow_pos (by norm_num) _) (by positivity)

/-- The control measure is finite Radon and dominates every variation.
 Inner regularity passes to the positive series; finiteness then gives
 outer regularity, including on nonmetrizable compact spaces. -/
theorem control_measure_theorem (𝕜 : Type) [RCLike 𝕜] : ControlMeasureTheorem.{u} 𝕜 := by
  intro X _ _ _ _ _ μ hμ
  have hf n : IsFiniteMeasure (μ n).variation := ⟨(hμ n).1⟩
  have hr n : (μ n).variation.Regular :=
    (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mp (hμ n).2
  have : IsFiniteMeasure (controlMeasure μ) := control_measure_finite μ hf
  have : (controlMeasure μ).InnerRegular := by
    unfold controlMeasure
    infer_instance
  have hregular : (controlMeasure μ).Regular := inferInstance
  exact ⟨inferInstance,
    (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mpr hregular,
    control_measure_dominates μ⟩

end Control

section Evaluation
variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {𝕜 : Type} [RCLike 𝕜]

open FunctionSpaces.ScalarRieszMarkov

omit [LocallyCompactSpace X] in
lemma finiteScalarRadon_add (μ ν : VectorMeasure X 𝕜)
    (hμ : FiniteScalarRadon μ) (hν : FiniteScalarRadon ν) : FiniteScalarRadon (μ + ν) := by
  have : IsFiniteMeasure μ.variation := ⟨hμ.1⟩
  have : IsFiniteMeasure ν.variation := ⟨hν.1⟩
  have : μ.variation.Regular :=
    (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mp hμ.2
  have : ν.variation.Regular :=
    (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mp hν.2
  have : (μ.variation + ν.variation).Regular := regular_add _ _
  have : IsFiniteMeasure (μ + ν).variation :=
    isFiniteMeasure_of_le _ VectorMeasure.variation_add_le
  exact ⟨measure_lt_top _ _,
    (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mpr
      (regular_of_le VectorMeasure.variation_add_le)⟩

omit [T2Space X] [LocallyCompactSpace X] [BorelSpace X] in
lemma finiteScalarRadon_smul (c : 𝕜) (μ : VectorMeasure X 𝕜)
    (hμ : FiniteScalarRadon μ) : FiniteScalarRadon (c • μ) := by
  have : IsFiniteMeasure μ.variation := ⟨hμ.1⟩
  have : μ.variation.Regular :=
    (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mp hμ.2
  rw [FiniteScalarRadon, VectorMeasure.variation_smul]
  exact ⟨measure_lt_top _ _,
    (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mpr inferInstance⟩

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [BorelSpace X] in
/-- Scalar multiplication of the measure preserves the ordinary bilinear
 multiplication pairing. This is valid for complex scalars as well. -/
lemma scalarIntegral_smul_measure (c : 𝕜) (μ : VectorMeasure X 𝕜) (f : X → 𝕜) :
    scalarIntegral (c • μ) f = c * scalarIntegral μ f := by
  let B := ContinuousLinearMap.mul ℝ 𝕜
  have heq : (c • μ).transpose B = μ.transpose (c • B) := by
    ext s hs z
    change z * (c * μ s) = c * (z * μ s)
    ring
  have hU : DominatedFinMeasAdditive μ.variation ((c • μ).transpose B) ‖c • B‖ := by
    rw [heq]
    exact dominatedFinMeasAdditive_cbmApplyMeasure μ (c • B)
  unfold scalarIntegral VectorMeasure.integral
  simp only [VectorMeasure.variation_smul]
  rw! [← setToFun_congr_smul_measure' ‖c‖₊ hU]
  apply setToFun_postcompose _ _ (B c)
  intro s hs hsf
  ext z
  change z * (c * μ s) = c * (z * μ s)
  ring

/-- Borel set evaluation is a bounded scalar-linear functional on the entire
 norm dual. Its norm is at most one. The construction uses Riesz--Markov
 uniqueness, so it is independent of the chosen representing measure. -/
lemma exists_set_evaluation (hrmk : ScalarRepresentation.{u} 𝕜) (s : Set X) :
    ∃ T : (C₀(X, 𝕜) →L[𝕜] 𝕜) →L[𝕜] 𝕜, (∀ L, ‖T L‖ ≤ ‖L‖) ∧
      ∀ (μ : VectorMeasure X 𝕜), FiniteScalarRadon μ →
        ∀ L : C₀(X, 𝕜) →L[𝕜] 𝕜,
          (∀ f, L f = scalarIntegral μ f) → T L = μ s := by
  classical
  let : NormedAddCommGroup (C₀(X, 𝕜) →L[𝕜] 𝕜) := inferInstance
  let : NormedSpace 𝕜 (C₀(X, 𝕜) →L[𝕜] 𝕜) := inferInstance
  choose ν hν hrep hnorm huniq using (hrmk X)
  have hfinite L : IsFiniteMeasure (ν L).variation := ⟨(hν L).1⟩
  have hadd (L M : C₀(X, 𝕜) →L[𝕜] 𝕜) : ν (L + M) = ν L + ν M := by
    have hsum := finiteScalarRadon_add (ν L) (ν M) (hν L) (hν M)
    have : IsFiniteMeasure (ν L).variation := hfinite L
    have : IsFiniteMeasure (ν M).variation := hfinite M
    have : IsFiniteMeasure (ν L + ν M).variation := ⟨hsum.1⟩
    apply (huniq (L + M) _ hsum _).symm
    intro f
    refine ⟨(scalarIntegral_bound _ f).1, ?_⟩
    change L f + M f = scalarIntegral (ν L + ν M) f
    rw [scalarIntegral, VectorMeasure.integral_add_vectorMeasure
      (hrep L f).1 (hrep M f).1]
    exact congrArg₂ (· + ·) (hrep L f).2 (hrep M f).2
  have hsmul (c : 𝕜) (L : C₀(X, 𝕜) →L[𝕜] 𝕜) : ν (c • L) = c • ν L := by
    have hc := finiteScalarRadon_smul c (ν L) (hν L)
    have : IsFiniteMeasure (c • ν L).variation := ⟨hc.1⟩
    apply (huniq (c • L) _ hc _).symm
    intro f
    refine ⟨(scalarIntegral_bound _ f).1, ?_⟩
    change c * L f = scalarIntegral (c • ν L) f
    rw [scalarIntegral_smul_measure, (hrep L f).2]
  have hbound L : ‖ν L s‖ ≤ ‖L‖ := by
    have : IsFiniteMeasure (ν L).variation := hfinite L
    calc
      _ ≤ (ν L).variation.real s := VectorMeasure.norm_measure_le_variation
      _ ≤ (ν L).variation.real univ :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))
      _ = ‖L‖ := (hnorm L).symm
  let T : (C₀(X, 𝕜) →L[𝕜] 𝕜) →L[𝕜] 𝕜 :=
    LinearMap.mkContinuous
      { toFun := fun L => ν L s
        map_add' := fun L M => by rw [hadd]; rfl
        map_smul' := fun c L => by rw [hsmul]; rfl }
      1 (fun L => by change ‖ν L s‖ ≤ 1 * ‖L‖; simpa only [one_mul] using hbound L)
  refine ⟨T, fun L => hbound L, ?_⟩
  intro μ hμ L hL
  have : IsFiniteMeasure μ.variation := ⟨hμ.1⟩
  have hμeq : μ = ν L := huniq L μ hμ (fun f => ⟨(scalarIntegral_bound μ f).1, hL f⟩)
  change ν L s = μ s
  rw [hμeq]

/-- This verifies that the specification's weak convergence is exactly weak
 convergence of the canonical multiplication-integral functionals. The
 upstream norm equality makes this the total-variation norm topology. -/
lemma measureWeakConverges_iff (μ : ℕ → VectorMeasure X 𝕜) (ν : VectorMeasure X 𝕜)
    (hμ : ∀ n, FiniteScalarRadon (μ n)) (hν : FiniteScalarRadon ν) :
    letI : ∀ n, IsFiniteMeasure (μ n).variation := fun n => ⟨(hμ n).1⟩
    letI : IsFiniteMeasure ν.variation := ⟨hν.1⟩
    MeasureWeakConverges μ ν ↔
      ∀ T : (C₀(X, 𝕜) →L[𝕜] 𝕜) →L[𝕜] 𝕜,
        Tendsto (fun n => T (scalarMeasureFunctional (μ n))) atTop
          (𝓝 (T (scalarMeasureFunctional ν))) := by
  letI : ∀ n, IsFiniteMeasure (μ n).variation := fun n => ⟨(hμ n).1⟩
  letI : IsFiniteMeasure ν.variation := ⟨hν.1⟩
  constructor
  · rintro ⟨L, L₀, hL, hL₀, hweak⟩ T
    have heq n : L n = scalarMeasureFunctional (μ n) := by ext f; exact hL n f
    have heq₀ : L₀ = scalarMeasureFunctional ν := by ext f; exact hL₀ f
    simpa only [heq, heq₀] using hweak T
  · intro h
    exact ⟨(fun n => scalarMeasureFunctional (μ n)), scalarMeasureFunctional ν,
      fun _ _ => rfl, fun _ => rfl, h⟩

/-- Real set evaluation on the norm dual, including the empty space. -/
theorem set_evaluation_signed : SignedSetEvaluation.{u} := by
  intro X _ _ _ _ _ s _
  exact exists_set_evaluation FunctionSpaces.ScalarRieszMarkov.real_representation s

/-- Complex-linear set evaluation on the norm dual. -/
theorem set_evaluation_complex : ComplexSetEvaluation.{u} := by
  intro X _ _ _ _ _ s _
  exact exists_set_evaluation FunctionSpaces.ScalarRieszMarkov.complex_representation s

end Evaluation

/-- Apply the full dual's set evaluations, then use the geometric control
 measure and the finite-control-measure theorem. -/
lemma weak_application_of_uniformity (𝕜 : Type) [RCLike 𝕜]
    (hrmk : ScalarRepresentation.{u} 𝕜)
    (hvhs : ∀ {α : Type u} [MeasurableSpace α]
      (ρ : Measure α) [IsFiniteMeasure ρ] (μ : ℕ → VectorMeasure α 𝕜),
      (∀ n s, MeasurableSet s → ρ s = 0 → μ n s = 0) →
      (∀ s, MeasurableSet s → ∃ l : 𝕜, Tendsto (fun n => μ n s) atTop (𝓝 l)) →
      UniformVariation ρ μ) : WeakApplication.{u} 𝕜 := by
  intro X _ _ _ _ _ μ ν hμ hν hweak
  obtain ⟨L, L₀, hL, hL₀, hweak⟩ := hweak
  have hcontrol := control_measure_theorem 𝕜 X μ hμ
  have : IsFiniteMeasure (controlMeasure μ) := hcontrol.1
  have hac n s (_hs : MeasurableSet s) (hρ : controlMeasure μ s = 0) : μ n s = 0 := by
    apply enorm_eq_zero.1
    apply le_antisymm _ bot_le
    have hz := control_measure_dominates μ n hρ
    exact (VectorMeasure.enorm_measure_le_variation _ _).trans (le_of_eq hz)
  have hset s (_hs : MeasurableSet s) :
      Tendsto (fun n => μ n s) atTop (𝓝 (ν s)) := by
    obtain ⟨T, _, hT⟩ := exists_set_evaluation hrmk s
    have heq n : T (L n) = μ n s := hT (μ n) (hμ n) (L n) (hL n)
    simpa only [heq, hT ν hν L₀ hL₀] using hweak T
  refine ⟨hset, hvhs _ μ hac (fun s hs => ⟨ν s, hset s hs⟩), ?_⟩
  intro s hs hρ
  exact tendsto_nhds_unique (hset s hs) (by simpa only [hac _ s hs hρ] using tendsto_const_nhds)

/-- Weak convergence of finite signed Radon measures gives the full
 Vitali--Hahn--Saks conclusion for the specified regular control measure. -/
theorem weak_application_signed : WeakApplication.{u} ℝ := by
  apply weak_application_of_uniformity ℝ FunctionSpaces.ScalarRieszMarkov.real_representation
  intro α _ ρ _ μ hac hconv
  exact (vitali_hahn_saks_signed ρ μ hac hconv).1

/-- The complex version uses complex-linear functionals on the norm dual. -/
theorem weak_application_complex : WeakApplication.{u} ℂ := by
  apply weak_application_of_uniformity ℂ FunctionSpaces.ScalarRieszMarkov.complex_representation
  intro α _ ρ _ μ hac hconv
  exact (vitali_hahn_saks_complex ρ μ hac hconv).1

end ExpandedFA.Compactness.VitaliHahnSaks
