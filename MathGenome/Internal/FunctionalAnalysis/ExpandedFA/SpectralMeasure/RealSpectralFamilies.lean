import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.RealSpectralFamilies
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.RealSelfAdjointSpectral
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.SpectralFamilies
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Filter MeasureTheory
open scoped InnerProductSpace Topology
open Classical
namespace ExpandedFA.SpectralMeasure.RealSpectralFamilies
universe u v
variable {S : Type u} {H : Type v} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma integral_sub (E : RealProjectionValuedMeasure S H) (C : RealBoundedRealization E)
    (f g : RealBoundedFunction S) :
    C.integral (.add f (.smul (-1) g)) = C.integral f - C.integral g := by
  rw [C.integral_add, C.integral_smul]
  simp [sub_eq_add_neg]

/-- Bounded pointwise convergence in each vector's finite scalar measure. -/
lemma strong_integral_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (E : RealProjectionValuedMeasure S H) (C : RealBoundedRealization E)
    (f : RealBoundedFunction S) (a : ι → RealBoundedFunction S)
    (K : ℝ) (hb : ∀ i s, |a i s - f s| ≤ K)
    (hl : ∀ s, Tendsto (fun i => a i s) l (𝓝 (f s))) (x : H) :
    Tendsto (fun i => C.integral (a i) x) l (𝓝 (C.integral f x)) := by
  letI := C.scalar_finite x
  have hi : Tendsto (fun i => ∫ s, |a i s - f s| ^ 2 ∂C.scalar x)
      l (𝓝 (0 : ℝ)) := by
    have hh : Tendsto (fun i => ∫ s, |a i s - f s| ^ 2 ∂C.scalar x)
        l (𝓝 (∫ _ : S, (0 : ℝ) ∂C.scalar x)) := by
      apply tendsto_integral_filter_of_norm_le_const
      · exact Eventually.of_forall (fun i =>
          (((a i).measurable.sub f.measurable).norm.pow_const 2).stronglyMeasurable.aestronglyMeasurable)
      · refine ⟨(max K 0) ^ 2, Eventually.of_forall (fun i => Eventually.of_forall (fun s => ?_))⟩
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (abs_nonneg _) ((hb i s).trans (le_max_left _ _)) 2
      · exact Eventually.of_forall (fun s => by
          simpa only [Real.norm_eq_abs, sub_self, abs_zero, zero_pow (by decide : 2 ≠ 0)] using
            ((hl s).sub (tendsto_const_nhds (x := f s))).norm.pow 2)
    simpa using hh
  have hsquare : Tendsto (fun i => ‖C.integral (a i) x - C.integral f x‖ ^ 2)
      l (𝓝 (0 : ℝ)) := by
    have heq (i : ι) : ‖C.integral (a i) x - C.integral f x‖ ^ 2 =
        ∫ s, |a i s - f s| ^ 2 ∂C.scalar x := by
      rw [← sub_apply, ← integral_sub E C]
      simpa [RealBoundedFunction.add, RealBoundedFunction.smul, sub_eq_add_neg] using
        C.norm_square (.add (a i) (.smul (-1) f)) x
    simpa only [heq] using hi
  have hn := (Real.continuous_sqrt.tendsto 0).comp hsquare
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn

lemma projections_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (E : RealProjectionValuedMeasure S H) (C : RealBoundedRealization E)
    (B : ι → Set S) (D : Set S)
    (hB : ∀ i, MeasurableSet (B i)) (hD : MeasurableSet D)
    (hl : ∀ s, Tendsto (fun i => (B i).indicator (fun _ => (1 : ℝ)) s) l
      (𝓝 (D.indicator (fun _ => (1 : ℝ)) s))) (x : H) :
    Tendsto (fun i => E (B i) x) l (𝓝 (E D x)) := by
  have hh := strong_integral_tendsto E C (.indicator D hD)
    (fun i => .indicator (B i) (hB i)) 2 (fun i s => ?_) hl x
  · simpa only [C.integral_indicator] using hh
  by_cases h₁ : s ∈ B i <;> by_cases h₂ : s ∈ D <;>
    norm_num [RealBoundedFunction.indicator, h₁, h₂]

lemma indicator_Iic_right (r t : ℝ) :
    Tendsto (fun q : ℝ => if r ≤ q then (1 : ℝ) else 0) (nhdsWithin t (Ici t))
      (𝓝 (if r ≤ t then (1 : ℝ) else 0)) := by
  apply tendsto_const_nhds.congr'
  by_cases h : r ≤ t
  · filter_upwards [self_mem_nhdsWithin] with q hq
    simp [h, h.trans hq]
  · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (lt_of_not_ge h))] with q hq
    simp [h, not_le.mpr (show q < r from hq)]

lemma family_range_mono (E : RealProjectionValuedMeasure ℝ H) {s t : ℝ} (hst : s ≤ t) :
    LinearMap.range (realFamily E s).toLinearMap ≤ LinearMap.range (realFamily E t).toLinearMap := by
  rintro _ ⟨x, rfl⟩
  refine ⟨realFamily E s x, ?_⟩
  have h : Iic t ∩ Iic s = Iic s := inter_eq_right.mpr (Iic_subset_Iic.mpr hst)
  have he := E.inter (Iic t) (Iic s) measurableSet_Iic measurableSet_Iic
  rw [h] at he
  exact congrArg (fun T : H →L[ℝ] H => T x) he

lemma family_range_closed (E : RealProjectionValuedMeasure ℝ H) (t : ℝ) :
    IsClosed (LinearMap.range (realFamily E t).toLinearMap : Set H) := by
  have heq : (LinearMap.range (realFamily E t).toLinearMap : Set H) =
      {x | realFamily E t x = x} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact E.idempotent_apply measurableSet_Iic y
    · intro hx
      exact ⟨x, hx⟩
  rw [heq]
  exact isClosed_eq (realFamily E t).continuous continuous_id

lemma family_properties (E : RealProjectionValuedMeasure ℝ H) (C : RealBoundedRealization E) :
    Spec.FamilyConclusion E := by
  refine ⟨?_, fun _ _ h => family_range_mono E h, ?_, ?_, ?_⟩
  · intro t
    exact ⟨E.star_eq measurableSet_Iic, E.idempotent measurableSet_Iic, family_range_closed E t⟩
  · intro t x
    apply projections_tendsto E C (fun r => Iic r) (Iic t)
      (fun _ => measurableSet_Iic) measurableSet_Iic _ x
    intro r
    simpa only [indicator_apply, mem_Iic] using indicator_Iic_right r t
  · intro x
    have hh := projections_tendsto (l := atBot) E C (fun t => Iic t) ∅
      (fun _ => measurableSet_Iic) MeasurableSet.empty (fun r => ?_) x
    · simpa [realFamily] using hh
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_lt_atBot r] with t ht
    simp [not_le.mpr ht]
  · intro x
    have hh := projections_tendsto (l := atTop) E C (fun t => Iic t) univ
      (fun _ => measurableSet_Iic) MeasurableSet.univ (fun r => ?_) x
    · simpa [realFamily, E.univ] using hh
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop r] with t ht
    simp [ht]

theorem spectral_family_properties : Spec.FamilyProperties.{v} := by
  intro H _ _ _ A _ E C R hR hE
  exact family_properties E C


/-- Finite sum of everywhere bounded measurable functions. -/
def sumFunction {ι : Type*} (t : Finset ι) (f : ι → RealBoundedFunction S) :
    RealBoundedFunction S where
  toFun s := ∑ i ∈ t, f i s
  measurable := Finset.measurable_sum t (fun i _ => (f i).measurable)
  bounded := by
    choose K hK hf using fun i => (f i).bounded
    refine ⟨∑ i ∈ t, K i, Finset.sum_nonneg (fun i _ => hK i), fun s => ?_⟩
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => hf i s))

lemma integral_sumFunction {ι : Type*} (E : RealProjectionValuedMeasure S H)
    (C : RealBoundedRealization E) (t : Finset ι) (f : ι → RealBoundedFunction S) :
    C.integral (sumFunction t f) = ∑ i ∈ t, C.integral (f i) := by
  induction t using Finset.induction_on with
  | empty =>
    have heq : sumFunction ∅ f = .const 0 := by
      apply RealBoundedFunction.ext
      simp [sumFunction, RealBoundedFunction.const]
    rw [heq, C.integral_const]
    simp
  | @insert i t hi ih =>
    have heq : sumFunction (insert i t) f = .add (f i) (sumFunction t f) := by
      apply RealBoundedFunction.ext
      intro s
      simp [sumFunction, RealBoundedFunction.add, hi]
    rw [heq, C.integral_add, ih, Finset.sum_insert hi]

open private cutoff realStep from MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.SpectralFamilies

private def stepFunction {m M : ℝ} (P : TaggedPartition m M) : RealBoundedFunction ℝ :=
  .add (.smul P.lowerTag (.indicator (Iic m) measurableSet_Iic))
    (sumFunction Finset.univ (fun i : Fin P.n => .smul (P.tag i)
      (.add (.indicator (Iic (P.point i.succ)) measurableSet_Iic)
        (.smul (-1) (.indicator (Iic (P.point i.castSucc)) measurableSet_Iic)))))

private lemma stepFunction_apply {m M : ℝ} (P : TaggedPartition m M) (r : ℝ) :
    stepFunction P r = realStep P r := by
  simp only [stepFunction, RealBoundedFunction.add, RealBoundedFunction.smul,
    RealBoundedFunction.indicator, sumFunction, realStep, cutoff, Set.indicator_apply,
    mem_Iic, neg_mul, one_mul, sub_eq_add_neg]

private lemma integral_stepFunction {m M : ℝ} (P : TaggedPartition m M)
    (E : RealProjectionValuedMeasure ℝ H) (C : RealBoundedRealization E) :
    C.integral (stepFunction P) = realOperatorSum P E := by
  rw [stepFunction, C.integral_add, C.integral_smul, C.integral_indicator,
    integral_sumFunction]
  unfold realOperatorSum realFamily
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [C.integral_smul, integral_sub, C.integral_indicator, C.integral_indicator]

open RealSelfAdjointSpectral

/-- Restrict the pointwise bound to the spectral support before invoking the
bounded integral estimate. This avoids asserting a global bound on the coordinate. -/
lemma integral_bound_on_spectrum (A : H →L[ℝ] H)
    (E : RealProjectionValuedMeasure ℝ H) (C : RealBoundedRealization E)
    (hE : E (spectrum ℝ A)ᶜ = 0) (f : RealBoundedFunction ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hf : ∀ r ∈ spectrum ℝ A, |f r| ≤ K) :
    ‖C.integral f‖ ≤ K := by
  let g := RealBoundedFunction.mul f (.indicator (spectrum ℝ A) (spectrum.isClosed A).measurableSet)
  have heq : C.integral f = C.integral g := by
    apply integral_eq_on_support E C (spectrum.isClosed A).measurableSet hE
    intro r hr
    simp [g, RealBoundedFunction.mul, RealBoundedFunction.indicator, hr]
  rw [heq]
  apply C.integral_bound _ K hK
  intro r
  by_cases hr : r ∈ spectrum ℝ A
  · simpa [g, RealBoundedFunction.mul, RealBoundedFunction.indicator, hr] using hf r hr
  · simpa [g, RealBoundedFunction.mul, RealBoundedFunction.indicator, hr] using hK

lemma operatorSum_error (A : H →L[ℝ] H)
    (E : RealProjectionValuedMeasure ℝ H) (C : RealBoundedRealization E)
    (R : ℝ) (hR : 0 ≤ R) (hE : Resolves A E C R hR)
    {m M : ℝ} (hσ : spectrum ℝ A ⊆ Icc m M) (P : TaggedPartition m M) :
    ‖realOperatorSum P E - A‖ ≤ P.mesh := by
  let c := clippedCoordinate ‖A‖ (norm_nonneg A)
  have hid : C.integral c = A := resolves_coordinate_at_norm A E C R hR hE
  rw [← integral_stepFunction P E C, ← hid, ← integral_sub E C]
  apply integral_bound_on_spectrum A E C hE.1 _ P.mesh P.mesh_nonneg
  intro r hr
  have hc : c r = r := clippedCoordinate_on_spectrum A ‖A‖ (norm_nonneg A) le_rfl hr
  simpa only [RealBoundedFunction.add, RealBoundedFunction.smul, hc, neg_one_mul,
    ← sub_eq_add_neg, stepFunction_apply] using
    SpectralFamilies.realStep_error P (hσ hr).1 (hσ hr).2

lemma lower_projection (A : H →L[ℝ] H)
    (E : RealProjectionValuedMeasure ℝ H) (C : RealBoundedRealization E)
    (hE : E (spectrum ℝ A)ᶜ = 0) {m M : ℝ} (hσ : spectrum ℝ A ⊆ Icc m M) :
    realFamily E m = E {m} := by
  apply projection_eq_on_support E C (spectrum.isClosed A).measurableSet hE
    measurableSet_Iic (measurableSet_singleton m)
  intro r hr
  exact ⟨fun h => le_antisymm h (hσ hr).1, fun h => h.le⟩

lemma upper_projection (A : H →L[ℝ] H)
    (E : RealProjectionValuedMeasure ℝ H) (C : RealBoundedRealization E)
    (hE : E (spectrum ℝ A)ᶜ = 0) {m M : ℝ} (hσ : spectrum ℝ A ⊆ Icc m M) :
    realFamily E M = 1 := by
  rw [← E.univ]
  apply projection_eq_on_support E C (spectrum.isClosed A).measurableSet hE
    measurableSet_Iic MeasurableSet.univ
  intro r hr
  simp [(hσ hr).2]

lemma coefficient_operatorSum {m M : ℝ} (P : TaggedPartition m M)
    (E : RealProjectionValuedMeasure ℝ H) (x y : H) :
    ⟪x, realOperatorSum P E y⟫_ℝ =
      realScalarSum P (fun t => ⟪x, realFamily E t y⟫_ℝ) ⟪x, realFamily E m y⟫_ℝ := by
  simp only [realOperatorSum, realScalarSum, add_apply, sum_apply,
    smul_apply, sub_apply, inner_add_right, inner_sum, inner_smul_right, inner_sub_right]

lemma coefficient_error (A : H →L[ℝ] H)
    (E : RealProjectionValuedMeasure ℝ H) (C : RealBoundedRealization E)
    (R : ℝ) (hR : 0 ≤ R) (hE : Resolves A E C R hR)
    {m M : ℝ} (hσ : spectrum ℝ A ⊆ Icc m M) (P : TaggedPartition m M) (x y : H) :
    ‖realScalarSum P (fun t => ⟪x, realFamily E t y⟫_ℝ) ⟪x, realFamily E m y⟫_ℝ - ⟪x, A y⟫_ℝ‖ ≤
      P.mesh * (‖x‖ * ‖y‖) := by
  rw [← coefficient_operatorSum, ← inner_sub_right, ← sub_apply]
  calc
    ‖⟪x, (realOperatorSum P E - A) y⟫_ℝ‖ ≤ ‖x‖ * ‖(realOperatorSum P E - A) y‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖realOperatorSum P E - A‖ * ‖y‖) :=
      mul_le_mul_of_nonneg_left ((realOperatorSum P E - A).le_opNorm y) (norm_nonneg _)
    _ ≤ ‖x‖ * (P.mesh * ‖y‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (operatorSum_error A E C R hR hE hσ P) (norm_nonneg _)) (norm_nonneg _)
    _ = P.mesh * (‖x‖ * ‖y‖) := by ring

lemma singleton_operator (A : H →L[ℝ] H)
    (E : RealProjectionValuedMeasure ℝ H) (C : RealBoundedRealization E)
    (R : ℝ) (hR : 0 ≤ R) (hE : Resolves A E C R hR)
    {m : ℝ} (hσ : spectrum ℝ A ⊆ Icc m m) : A = m • (1 : H →L[ℝ] H) := by
  rw [← resolves_coordinate_at_norm A E C R hR hE, ← C.integral_const m]
  apply integral_eq_on_support E C (spectrum.isClosed A).measurableSet hE.1
  intro r hr
  rw [clippedCoordinate_on_spectrum A ‖A‖ (norm_nonneg A) le_rfl hr]
  exact le_antisymm (hσ hr).2 (hσ hr).1

/-- The coefficient variation is concentrated on the actual spectrum. -/
lemma coefficient_ae_spectrum (A : H →L[ℝ] H)
    (E : RealProjectionValuedMeasure ℝ H) (C : RealBoundedRealization E)
    (hE : E (spectrum ℝ A)ᶜ = 0) (x y : H) :
    ∀ᵐ r ∂(C.coefficient x y).variation, r ∈ spectrum ℝ A := by
  apply ae_iff.mpr
  change (C.coefficient x y).variation (spectrum ℝ A)ᶜ = 0
  apply (VectorMeasure.variation_apply_eq_zero (spectrum.isClosed A).measurableSet.compl).mpr
  intro B hBK hB
  have hproj : E B = 0 := by
    have hi := E.inter B (spectrum ℝ A)ᶜ hB (spectrum.isClosed A).measurableSet.compl
    rw [inter_eq_left.mpr hBK, hE, mul_zero] at hi
    exact hi.symm
  rw [C.coefficient_apply x y B hB, hproj]
  simp

/-- The ordinary real coordinate is integrable against the actual coefficient
variation, and its signed spectral integral is the operator coefficient. -/
lemma coordinate_coefficient_integral (A : H →L[ℝ] H)
    (E : RealProjectionValuedMeasure ℝ H) (C : RealBoundedRealization E)
    (R : ℝ) (hR : 0 ≤ R) (hE : Resolves A E C R hR) (x y : H) :
    Integrable (fun t : ℝ => t) (C.coefficient x y).variation ∧
    ⟪x, A y⟫_ℝ = (C.coefficient x y).integral (fun t : ℝ => t)
      (ContinuousLinearMap.lsmul ℝ ℝ) := by
  let c := clippedCoordinate ‖A‖ (norm_nonneg A)
  have hc : (c : ℝ → ℝ) =ᵐ[(C.coefficient x y).variation] (fun t => t) := by
    filter_upwards [coefficient_ae_spectrum A E C hE.1 x y] with t ht
    exact clippedCoordinate_on_spectrum A ‖A‖ (norm_nonneg A) le_rfl ht
  refine ⟨(C.coefficient_integrable c x y).congr hc, ?_⟩
  calc
    ⟪x, A y⟫_ℝ = ⟪x, C.integral c y⟫_ℝ :=
      congrArg (fun T : H →L[ℝ] H => ⟪x, T y⟫_ℝ)
        (resolves_coordinate_at_norm A E C R hR hE).symm
    _ = (C.coefficient x y).integral c (ContinuousLinearMap.lsmul ℝ ℝ) :=
      C.coefficient_integral c x y
    _ = _ := VectorMeasure.integral_congr_ae hc

theorem stieltjes_approximation : Spec.StieltjesApproximation.{v} := by
  intro H _ _ _ A _ E C R hR hE m M hσ
  refine ⟨operatorSum_error A E C R hR hE hσ, ?_, ?_, ?_, ?_⟩
  · intro ε hε
    exact ⟨ε, hε, fun P hP => (operatorSum_error A E C R hR hE hσ P).trans_lt hP⟩
  · intro x y
    refine ⟨?_, ?_⟩
    · intro ε hε
      let K := ‖x‖ * ‖y‖
      have hK : 0 < K + 1 := by dsimp [K]; positivity
      refine ⟨ε / (K + 1), div_pos hε hK, ?_⟩
      intro P hP
      have hsmall : P.mesh * (K + 1) < ε := (lt_div_iff₀ hK).mp hP
      rw [← lower_projection A E C hE.1 hσ]
      have hb := coefficient_error A E C R hR hE hσ P x y
      exact hb.trans_lt (by nlinarith [P.mesh_nonneg])
    · exact coordinate_coefficient_integral A E C R hR hE x y
  · intro he
    subst M
    exact singleton_operator A E C R hR hE hσ
  · intro P hn
    have hmM : m = M := by
      have hfin : (0 : Fin (P.n + 1)) = Fin.last P.n := by ext; simp [hn]
      exact P.first.symm.trans ((congrArg P.point hfin).trans P.last)
    have htag : P.lowerTag = m := by simp [SpectralFamilies.Spec.TaggedPartition.lowerTag, hn]
    have hsum : (∑ i : Fin P.n, P.tag i •
        (realFamily E (P.point i.succ) - realFamily E (P.point i.castSucc))) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact Fin.elim0 (hn ▸ i)
    rw [realOperatorSum, htag, hsum, add_zero, hmM, upper_projection A E C hE.1 hσ]

theorem spectral_family_exists : Spec.SpectralFamilyExists.{v} := by
  intro H _ _ _ A hA
  obtain ⟨E, C, hE⟩ := real_resolving_pair_exists A hA
  exact ⟨E, C, hE, family_properties E C,
    stieltjes_approximation H A hA E C ‖A‖ (norm_nonneg A) hE⟩

theorem real_or_complex_conclusion : Spec.RealOrComplexConclusion.{v} :=
  ⟨spectral_family_exists, spectral_family_properties, stieltjes_approximation,
    SpectralFamilies.spectral_family_properties, SpectralFamilies.stieltjes_approximation⟩

end ExpandedFA.SpectralMeasure.RealSpectralFamilies
