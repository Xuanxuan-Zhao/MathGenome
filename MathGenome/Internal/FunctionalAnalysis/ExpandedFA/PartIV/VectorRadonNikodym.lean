import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.VectorRadonNikodym
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.RadonNikodym
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.ReflexiveMeasureRange
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.PettisMeasurability
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.SetTheory.Cardinal.Subfield
import Mathlib.LinearAlgebra.Countable
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.MeasureTheory.Function.LpSeminorm.Trim
import Mathlib.Analysis.LocallyConvex.SeparatingDual

noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Topology
universe u v

namespace ExpandedFA.PartIV.VectorRadonNikodym
open VectorRadonNikodymSpec

theorem density_consequences : DensityConsequences.{u,v} := by
  intro X Y _ _ _ _ μ m g hg hsets
  have hm : μ.withDensityᵥ g = m := by
    ext A hA
    exact (withDensityᵥ_apply hg hA).trans (hsets A hA).symm
  refine ⟨?_, ?_⟩
  · intro A hA
    rw [← hm, Measure.variation_withDensityᵥ hg]
    refine ⟨withDensity_apply _ hA, ?_⟩
    rw [measureReal_def, withDensity_apply _ hA]
    exact (integral_norm_eq_lintegral_enorm hg.aestronglyMeasurable.restrict).symm
  · intro f hf hfsets
    apply hf.ae_eq_of_withDensityᵥ_eq hg
    ext A hA
    rw [withDensityᵥ_apply hf hA, withDensityᵥ_apply hg hA]
    exact (hfsets A hA).symm.trans (hsets A hA)

private theorem exists_norm_detecting_vector {𝕜 : Type} {Y : Type v}
    [RCLike 𝕜] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (f : Y →L[𝕜] 𝕜) :
    ∃ x : Y, ∀ g : Y →L[𝕜] 𝕜, g x = 0 → ‖f‖ ≤ 2 * ‖f - g‖ := by
  by_cases hf : f = 0
  · exact ⟨0, fun g _ => by simp [hf]⟩
  have hfpos : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hnot : ¬ ∀ x : Y, ‖f x‖ ≤ (‖f‖ / 2) * ‖x‖ := by
    intro h
    have := f.opNorm_le_bound (by positivity) h
    linarith
  push Not at hnot
  obtain ⟨x, hx⟩ := hnot
  have hxpos : 0 < ‖x‖ := by
    by_contra h
    have hxzero : x = 0 := norm_eq_zero.mp (le_antisymm (not_lt.mp h) (norm_nonneg x))
    simp [hxzero] at hx
  refine ⟨x, fun g hg => ?_⟩
  have hbound := (f - g).le_opNorm x
  simp only [sub_apply, hg, sub_zero] at hbound
  nlinarith

private theorem eq_top_of_trivial_annihilator {𝕜 : Type} {Y : Type v}
    [RCLike 𝕜] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (M : Submodule 𝕜 Y) (hM : IsClosed (M : Set Y))
    (h : ∀ f : Y →L[𝕜] 𝕜, (∀ x ∈ M, f x = 0) → f = 0) : M = ⊤ := by
  letI : IsClosed (M : Set Y) := hM
  apply top_unique
  intro x _
  by_contra hx
  have hqx : M.mkQ x ≠ 0 := fun heq => hx ((Submodule.Quotient.mk_eq_zero M).mp heq)
  obtain ⟨g, _, hg⟩ := exists_dual_vector 𝕜 (M.mkQ x) (norm_ne_zero_iff.mpr hqx)
  have hz : g.comp M.mkQL = 0 := h _ (by
    intro m hm
    simp [(Submodule.Quotient.mk_eq_zero M).mpr hm])
  have hval : g (M.mkQ x) = 0 := congrArg (fun f : Y →L[𝕜] 𝕜 => f x) hz
  rw [hg] at hval
  exact hqx (norm_eq_zero.mp (by simpa using congrArg (fun z : 𝕜 => ‖z‖) hval))

/-- Hahn–Banach and nearly norming a dense sequence in the dual prove this
without any compactness, nontriviality, or completeness assumption. -/
theorem separable_of_dual_separable (𝕜 : Type) [RCLike 𝕜]
    (Y : Type v) [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [SeparableSpace (Y →L[𝕜] 𝕜)] : SeparableSpace Y := by
  classical
  obtain ⟨f, hf⟩ := exists_dense_seq (Y →L[𝕜] 𝕜)
  choose x hx using fun n => exists_norm_detecting_vector (f n)
  let M := (Submodule.span 𝕜 (range x)).topologicalClosure
  have hM : M = ⊤ := by
    apply eq_top_of_trivial_annihilator M (Submodule.isClosed_topologicalClosure _)
    intro g hg
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨n, hn⟩ := hf.exists_dist_lt g (by positivity : 0 < ε / 3)
    have hgn : g (x n) = 0 := hg _
      (Submodule.le_topologicalClosure _ (Submodule.subset_span (mem_range_self n)))
    have hfn := hx n g hgn
    have htri := norm_add_le (g - f n) (f n)
    rw [sub_add_cancel] at htri
    rw [dist_eq_norm] at hn
    rw [norm_sub_rev (f n) g] at hfn
    linarith
  have hsepM : IsSeparable (M : Set Y) :=
    ((countable_range x).isSeparable.span (R := 𝕜)).closure
  rw [hM, Submodule.top_coe] at hsepM
  exact isSeparable_univ_iff.mp hsepM

theorem dual_separable : DualSeparability.{v} := by
  intro 𝕜 _ Y _ _ _ _ hY
  have hsurj : Function.Surjective (P1.C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 Y) := hY
  letI : SeparableSpace ((Y →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
    hsurj.denseRange.separableSpace (P1.C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 Y).continuous
  exact separable_of_dual_separable 𝕜 (Y →L[𝕜] 𝕜)

set_option backward.isDefEq.respectTransparency false in
theorem completion_invariant : CompletionInvariant.{u,v} := by
  intro X Y mX _ μ f
  have hle : mX ≤ inferInstanceAs (MeasurableSpace (NullMeasurableSpace X μ)) := fun A hA => hA.nullMeasurableSet
  have htrim : μ.completion.trim hle = μ := by
    apply @Measure.ext X mX
    intro A hA
    rw [trim_measurableSet_eq _ hA]
    rfl
  have hmeas : AEStronglyMeasurable f μ ↔ AEStronglyMeasurable[(inferInstanceAs (MeasurableSpace (NullMeasurableSpace X μ)))] f μ.completion := by
    constructor
    · rintro ⟨g, hg, hfg⟩
      exact ⟨g, hg.mono hle, hfg⟩
    · intro hf
      letI : MeasurableSpace Y := borel Y
      letI : BorelSpace Y := ⟨rfl⟩
      apply aestronglyMeasurable_iff_nullMeasurable_separable.mpr
      exact ⟨aemeasurable_iff_measurable.mp hf.aemeasurable, hf.isSeparable_ae_range⟩
  have hnorm (p : ℝ≥0∞) : eLpNorm f p μ = eLpNorm f p μ.completion := by
    by_cases hf : AEStronglyMeasurable f μ
    · have hf' : AEStronglyMeasurable[mX] f (μ.completion.trim hle) := by rwa [htrim]
      simpa only [htrim] using eLpNorm_trim_ae (p := p) hle hf'
    · rw [eLpNorm_of_not_aestronglyMeasurable hf,
        eLpNorm_of_not_aestronglyMeasurable (hmeas.not.mp hf)]
  refine ⟨hmeas, hnorm, ?_, fun _ => Iff.rfl⟩
  intro p
  simp only [MemLp, hnorm p, iff_self]

section RangeMeasure
variable (𝕜 : Type) [RCLike 𝕜] {X : Type u} {Y : Type v}
  [MeasurableSpace X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- The original measure, with codomain restricted to its literal closed
linear range span. This preserves norm countable additivity. -/
def rangeMeasure (m : VectorMeasure X Y) :
    VectorMeasure X (ReflexiveMeasureRangeSpec.rangeSpan 𝕜 m) where
  measureOf' A := ⟨m A, Submodule.le_topologicalClosure _
    (Submodule.subset_span (mem_range_self A))⟩
  empty' := Subtype.ext m.empty
  not_measurable' := by
    intro A hA
    exact Subtype.ext (m.not_measurable hA)
  m_iUnion' {f} hf hd := by
    apply (Topology.IsInducing.subtypeVal.hasSum_iff
      (g := (ReflexiveMeasureRangeSpec.rangeSpan 𝕜 m).subtype.toAddMonoidHom) _ _).mp
    exact m.m_iUnion hf hd

@[simp] theorem rangeMeasure_coe (m : VectorMeasure X Y) (A : Set X) :
    (rangeMeasure 𝕜 m A : Y) = m A := rfl

theorem rangeMeasure_variation (m : VectorMeasure X Y) :
    (rangeMeasure 𝕜 m).variation = m.variation := by
  apply le_antisymm
  · apply VectorMeasure.variation_le_of_forall_enorm_le
    intro A _
    exact VectorMeasure.enorm_measure_le_variation m A
  · apply VectorMeasure.variation_le_of_forall_enorm_le
    intro A _
    exact VectorMeasure.enorm_measure_le_variation (rangeMeasure 𝕜 m) A

end RangeMeasure


/-- Scalar RN and comparison of all set integrals give domination of a
real scalar test by the variation density. -/
theorem real_scalar_density {X : Type u} {Y : Type v}
    [MeasurableSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (μ : Measure X) [SigmaFinite μ] (m : VectorMeasure X Y)
    [IsFiniteMeasure m.variation]
    (hac : ∀ A, MeasurableSet A → μ A = 0 → m A = 0)
    (h : X → ℝ) (hh : Integrable h μ)
    (hrep : ∀ A, MeasurableSet A → ∫ x in A, h x ∂μ = m.variation.real A)
    (L : Y →L[ℝ] ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hL : ∀ y, |L y| ≤ c * ‖y‖) :
    ∃ f : X → ℝ, Integrable f μ ∧
      (∀ A, MeasurableSet A → ∫ x in A, f x ∂μ = L (m A)) ∧
      (∀ᵐ x ∂μ, |f x| ≤ c * h x) := by
  let ν : SignedMeasure X := m.mapRange L.toAddMonoidHom L.continuous
  have hν : ν ≪ᵥ μ.toENNRealVectorMeasure := by
    apply VectorMeasure.AbsolutelyContinuous.mk
    intro A hA hz
    rw [Measure.toENNRealVectorMeasure_apply_measurable hA] at hz
    change L (m A) = 0
    rw [hac A hA hz, map_zero]
  obtain ⟨f, _, hf, hsets, _⟩ := FunctionSpaces.signed_radon_nikodym μ ν hν
  have hsets' (A) (hA : MeasurableSet A) : ∫ x in A, f x ∂μ = L (m A) :=
    (hsets A hA).symm
  have hbound (A : Set X) : |L (m A)| ≤ c * m.variation.real A :=
    (hL _).trans (mul_le_mul_of_nonneg_left (VectorMeasure.norm_measure_le_variation) hc)
  have hp : f ≤ᵐ[μ] (fun x => c * h x) := by
    apply ae_le_of_forall_setIntegral_le hf (hh.const_mul c)
    intro A hA _
    rw [integral_const_mul, hrep A hA, hsets' A hA]
    exact (le_abs_self _).trans (hbound A)
  have hn : (fun x => -f x) ≤ᵐ[μ] (fun x => c * h x) := by
    apply ae_le_of_forall_setIntegral_le hf.neg (hh.const_mul c)
    intro A hA _
    simp only [Pi.neg_apply]
    rw [integral_neg, integral_const_mul, hrep A hA, hsets' A hA]
    exact (neg_le_abs _).trans (hbound A)
  refine ⟨f, hf, hsets', ?_⟩
  filter_upwards [hp, hn] with x hx hy
  exact abs_le.mpr ⟨by linarith, hx⟩

/-- Every scalar-linear test has an integrable density with a common
majorant. A factor two suffices uniformly for the real and complex fields. -/
theorem scalar_density_representatives (𝕜 : Type) [RCLike 𝕜]
    {X : Type u} {Y : Type v} [MeasurableSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (μ : Measure X) [SigmaFinite μ] (m : VectorMeasure X Y)
    (hm : m.variation univ < ∞)
    (hac : ∀ A, MeasurableSet A → μ A = 0 → m A = 0) :
    ∃ h : X → ℝ, Integrable h μ ∧ (∀ x, 0 ≤ h x) ∧
      ∀ ℓ : Y →L[𝕜] 𝕜, ∃ f : X → 𝕜, Integrable f μ ∧
        (∀ A, MeasurableSet A → ∫ x in A, f x ∂μ = ℓ (m A)) ∧
        (∀ᵐ x ∂μ, ‖f x‖ ≤ ‖ℓ‖ * h x) := by
  letI : NormedSpace ℝ Y := NormedSpace.restrictScalars ℝ 𝕜 Y
  letI : IsFiniteMeasure m.variation := ⟨hm⟩
  have hacv : m.variation ≪ μ := variation_absolutelyContinuous m μ hac
  let h : X → ℝ := fun x => (m.variation.rnDeriv μ x).toReal
  have hh : Integrable h μ := Measure.integrable_toReal_rnDeriv
  have hpos (x) : 0 ≤ h x := ENNReal.toReal_nonneg
  have hrep (A : Set X) (_hA : MeasurableSet A) :
      ∫ x in A, h x ∂μ = m.variation.real A := Measure.setIntegral_toReal_rnDeriv hacv A
  refine ⟨fun x => 2 * h x, hh.const_mul 2, fun x => by positivity, ?_⟩
  intro ℓ
  let Lr : Y →L[ℝ] ℝ := RCLike.reCLM.comp (ℓ.restrictScalars ℝ)
  let Li : Y →L[ℝ] ℝ := RCLike.imCLM.comp (ℓ.restrictScalars ℝ)
  obtain ⟨a, ha, harep, hab⟩ := real_scalar_density μ m hac h hh hrep Lr ‖ℓ‖
    (norm_nonneg _) (fun y => (RCLike.abs_re_le_norm _).trans (ℓ.le_opNorm y))
  obtain ⟨b, hb, hbrep, hbb⟩ := real_scalar_density μ m hac h hh hrep Li ‖ℓ‖
    (norm_nonneg _) (fun y => (RCLike.abs_im_le_norm _).trans (ℓ.le_opNorm y))
  let f : X → 𝕜 := fun x => (a x : 𝕜) + (b x : 𝕜) * RCLike.I
  have hai : Integrable (fun x => (a x : 𝕜)) μ := (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).integrable_comp ha
  have hbi : Integrable (fun x => (b x : 𝕜)) μ := (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).integrable_comp hb
  refine ⟨f, hai.add (hbi.mul_const _), ?_, ?_⟩
  · intro A hA
    change (∫ x in A, (a x : 𝕜) + (b x : 𝕜) * RCLike.I ∂μ) = _
    rw [integral_add hai.restrict (hbi.mul_const _).restrict, integral_mul_const,
      integral_ofReal,
      integral_ofReal, harep A hA, hbrep A hA]
    exact RCLike.re_add_im _
  · have hI : ‖(RCLike.I : 𝕜)‖ ≤ 1 := by rw [RCLike.norm_I]; split <;> norm_num
    filter_upwards [hab, hbb] with x hx hy
    calc
      ‖f x‖ ≤ ‖(a x : 𝕜)‖ + ‖(b x : 𝕜) * RCLike.I‖ := norm_add_le _ _
      _ ≤ |a x| + |b x| := by
        rw [norm_mul, RCLike.norm_ofReal, RCLike.norm_ofReal]
        gcongr
        exact mul_le_of_le_one_right (abs_nonneg _) hI
      _ ≤ ‖ℓ‖ * (2 * h x) := by linarith

/-- Scalar RN densities form a linear operator in L¹; no pointwise
linearity is asserted for individually chosen representatives. -/
theorem scalar_density_construction : VectorRadonNikodymSpec.ScalarDensityConstruction.{u,v} := by
  intro 𝕜 _ X Y _ _ _ _ μ _ m hm hac
  classical
  obtain ⟨h, hh, hp, hd⟩ := scalar_density_representatives 𝕜 μ m hm hac
  choose f hf hsets hbound using hd
  let F : (Y →L[𝕜] 𝕜) → Lp 𝕜 1 μ := fun ℓ => (hf ℓ).toL1 (f ℓ)
  have hF (ℓ) : F ℓ =ᵐ[μ] f ℓ := (hf ℓ).coeFn_toL1
  let T : (Y →L[𝕜] 𝕜) →ₗ[𝕜] Lp 𝕜 1 μ :=
    { toFun := F
      map_add' := by
        intro ℓ k
        have heq : f (ℓ + k) =ᵐ[μ] f ℓ + f k := by
          apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ (hf _) ((hf ℓ).add (hf k))
          intro A hA _
          simp only [Pi.add_apply]
          rw [integral_add (hf ℓ).restrict (hf k).restrict, hsets _ A hA,
            hsets _ A hA, hsets _ A hA]
          rfl
        exact Lp.ext ((hF _).trans (heq.trans (((hF ℓ).add (hF k)).symm.trans
          (Lp.coeFn_add (F ℓ) (F k)).symm)))
      map_smul' := by
        intro c ℓ
        have heq : f (c • ℓ) =ᵐ[μ] c • f ℓ := by
          apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ (hf _) ((hf ℓ).smul c)
          intro A hA _
          simp only [Pi.smul_apply]
          rw [integral_smul, hsets _ A hA, hsets _ A hA]
          rfl
        exact Lp.ext ((hF _).trans (heq.trans (((hF ℓ).const_smul c).symm.trans
          (Lp.coeFn_smul c (F ℓ)).symm))) }
  refine ⟨h, hh, hp, T, ?_⟩
  intro ℓ
  refine ⟨?_, ?_⟩
  · filter_upwards [hF ℓ, hbound ℓ] with x hx hb
    change ‖F ℓ x‖ ≤ _
    rwa [hx]
  · intro A hA
    exact (integral_congr_ae (ae_restrict_of_ae (hF ℓ))).trans (hsets ℓ A hA)


/-- A separable normed field has a countable dense subfield. -/
theorem exists_countable_dense_subfield (𝕜 : Type) [RCLike 𝕜] :
    ∃ F : Subfield 𝕜, Countable F ∧ Dense (F : Set 𝕜) := by
  let F := Subfield.closure (range (denseSeq 𝕜))
  refine ⟨F, ?_, ?_⟩
  · apply Cardinal.mk_le_aleph0_iff.mp
    letI : Countable (range (denseSeq 𝕜)) := (countable_range _).to_subtype
    exact (Subfield.cardinalMk_closure_le_max _).trans
      (max_le (Cardinal.mk_le_aleph0) le_rfl)
  · exact (denseRange_denseSeq 𝕜).mono Subfield.subset_closure

/-- Extend a bounded linear map over a dense subfield, then recover
linearity over the ambient field by continuity in the scalar. -/
theorem extend_from_dense_subfield {𝕜 : Type} [RCLike 𝕜]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (F : Subfield 𝕜) (hF : Dense (F : Set 𝕜))
    [NormedAlgebra F 𝕜] [IsBoundedSMul F 𝕜] [NormedSpace F E] [IsBoundedSMul F E] [IsScalarTower F 𝕜 E]
    (D : Submodule F E) (hD : Dense (D : Set E))
    (f : D →ₗ[F] 𝕜) (C : ℝ) (hf : ∀ d, ‖f d‖ ≤ C * ‖(d : E)‖) :
    ∃ L : E →L[𝕜] 𝕜, (∀ d : D, L d = f d) ∧ (∀ y, ‖L y‖ ≤ C * ‖y‖) := by
  let L₀ : E →L[F] 𝕜 := f.extendOfNorm D.subtype
  have hd : DenseRange D.subtype := hD.denseRange_val
  have hbound (y) : ‖L₀ y‖ ≤ C * ‖y‖ := f.norm_extendOfNorm_apply_le hd C hf y
  have hscalar (c : 𝕜) (y : E) : L₀ (c • y) = c • L₀ y := by
    apply hF.induction (P := fun c : 𝕜 => L₀ (c • y) = c • L₀ y) ?_
      (isClosed_eq (L₀.continuous.comp (continuous_id.smul continuous_const))
        (continuous_id.smul continuous_const)) c
    intro a ha
    exact L₀.map_smul (⟨a, ha⟩ : F) y
  let L : E →L[𝕜] 𝕜 :=
    { toFun := L₀
      map_add' := L₀.map_add
      map_smul' := hscalar
      cont := L₀.continuous }
  refine ⟨L, ?_, hbound⟩
  intro d
  exact f.extendOfNorm_eq hd ⟨C, hf⟩ d

/-- A dominated operator into scalar L¹ admits pointwise continuous linear
representatives when its domain is separable. -/
theorem dominated_operator_pointwise (𝕜 : Type) [RCLike 𝕜]
    {X : Type u} {E : Type v} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [SeparableSpace E]
    (μ : Measure X) (h : X → ℝ) (hp : ∀ x, 0 ≤ h x)
    (T : E →ₗ[𝕜] Lp 𝕜 1 μ)
    (hT : ∀ e, ∀ᵐ x ∂μ, ‖T e x‖ ≤ ‖e‖ * h x) :
    ∃ L : X → (E →L[𝕜] 𝕜),
      (∀ x e, ‖L x e‖ ≤ h x * ‖e‖) ∧
      (∀ e, (fun x => L x e) =ᵐ[μ] T e) := by
  classical
  obtain ⟨F, hcount, hFdense⟩ := exists_countable_dense_subfield 𝕜
  letI : Countable F := hcount
  letI : NormedAlgebra F 𝕜 :=
    { norm_smul_le := fun c z => by
        change ‖(c : 𝕜) * z‖ ≤ ‖(c : 𝕜)‖ * ‖z‖
        exact (norm_mul _ _).le }
  letI : IsBoundedSMul F 𝕜 := .of_norm_smul_le NormedAlgebra.norm_smul_le
  letI : NormedSpace F E := NormedSpace.restrictScalars F 𝕜 E
  letI : IsBoundedSMul F E := .of_norm_smul_le NormedSpace.norm_smul_le
  let D : Submodule F E := Submodule.span F (range (denseSeq E))
  have hD : Dense (D : Set E) :=
    (denseRange_denseSeq E).mono Submodule.subset_span
  letI : Countable D := inferInstanceAs (Countable (Submodule.span F (range (denseSeq E))))
  have hb : ∀ᵐ x ∂μ, ∀ d : D, ‖T d x‖ ≤ h x * ‖(d : E)‖ := by
    apply ae_all_iff.mpr
    intro d
    simpa only [mul_comm] using hT d
  have ha : ∀ᵐ x ∂μ, ∀ d e : D, T ((d + e : D) : E) x = T d x + T e x := by
    apply ae_all_iff.mpr
    intro d
    apply ae_all_iff.mpr
    intro e
    filter_upwards [Lp.coeFn_add (T d) (T e)] with x hx
    simpa only [Submodule.coe_add, map_add, Pi.add_apply] using hx
  have hs : ∀ᵐ x ∂μ, ∀ c : F, ∀ d : D,
      T ((c • d : D) : E) x = (c : 𝕜) • T d x := by
    apply ae_all_iff.mpr
    intro c
    apply ae_all_iff.mpr
    intro d
    have heq : T ((c • d : D) : E) = (c : 𝕜) • T d := by
      change T (c • (d : E)) = _
      rw [← IsScalarTower.algebraMap_smul 𝕜 c (d : E), map_smul]
      rfl
    rw [heq]
    exact Lp.coeFn_smul (c : 𝕜) (T d)
  let P : X → Prop := fun x =>
    (∀ d : D, ‖T d x‖ ≤ h x * ‖(d : E)‖) ∧
    (∀ d e : D, T ((d + e : D) : E) x = T d x + T e x) ∧
    (∀ c : F, ∀ d : D, T ((c • d : D) : E) x = (c : 𝕜) • T d x)
  have hP : ∀ᵐ x ∂μ, P x := hb.and (ha.and hs)
  have hex (x : X) (hx : P x) : ∃ L : E →L[𝕜] 𝕜,
      (∀ d : D, L d = T d x) ∧ (∀ e, ‖L e‖ ≤ h x * ‖e‖) := by
    let f : D →ₗ[F] 𝕜 :=
      { toFun := fun d => T d x
        map_add' := hx.2.1
        map_smul' := hx.2.2 }
    exact extend_from_dense_subfield F hFdense D hD f (h x) hx.1
  let L : X → E →L[𝕜] 𝕜 := fun x => if hx : P x then (hex x hx).choose else 0
  have hLb (x : X) (e : E) : ‖L x e‖ ≤ h x * ‖e‖ := by
    by_cases hx : P x
    · simpa only [L, dite_eq_left hx] using (hex x hx).choose_spec.2 e
    · simp only [L, dite_eq_right hx, zero_apply, norm_zero]
      exact mul_nonneg (hp x) (norm_nonneg _)
  have hLd (d : D) : (fun x => L x d) =ᵐ[μ] T d := by
    filter_upwards [hP] with x hx
    simpa only [L, dite_eq_left hx] using (hex x hx).choose_spec.1 d
  refine ⟨L, hLb, ?_⟩
  intro e
  obtain ⟨d, hdmem, hdlim⟩ := mem_closure_iff_seq_limit.mp (hD e)
  let ds : ℕ → D := fun n => ⟨d n, hdmem n⟩
  have hdiff (n : ℕ) : ∀ᵐ x ∂μ,
      ‖T (ds n) x - T e x‖ ≤ ‖(ds n : E) - e‖ * h x := by
    have heq : T ((ds n : E) - e) = T (ds n) - T e := T.map_sub _ _
    have heqae : T ((ds n : E) - e) =ᵐ[μ] (fun x => T (ds n) x - T e x) := by
      rw [heq]
      exact Lp.coeFn_sub _ _
    filter_upwards [hT ((ds n : E) - e), heqae] with x hx he
    rwa [he] at hx
  have halldiff : ∀ᵐ x ∂μ, ∀ n : ℕ,
      ‖T (ds n) x - T e x‖ ≤ ‖(ds n : E) - e‖ * h x := ae_all_iff.mpr hdiff
  have hallds : ∀ᵐ x ∂μ, ∀ n : ℕ, L x (ds n) = T (ds n) x :=
    ae_all_iff.mpr (fun n => hLd (ds n))
  filter_upwards [halldiff, hallds] with x hx he
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have hl : Tendsto (fun n => ‖L x (ds n) - T e x‖) atTop
      (𝓝 ‖L x e - T e x‖) :=
    (((L x).continuous.continuousAt.tendsto.comp hdlim).sub_const _).norm
  have hr : Tendsto (fun n => ‖(ds n : E) - e‖ * h x) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero, zero_mul] using (hdlim.sub_const e).norm.mul_const (h x)
  exact le_of_tendsto_of_tendsto hl hr (Eventually.of_forall fun n => by
    dsimp only
    rw [he n]
    exact hx n)

/-- Pettis measurability for a separable Banach target with a.e. scalar
measurability. Completeness of the measure is unnecessary. -/
theorem aestronglyMeasurable_of_scalar_tests (𝕜 : Type) [RCLike 𝕜]
    {X : Type u} {Y : Type v} [MeasurableSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y] [SeparableSpace Y]
    (μ : Measure X) (g : X → Y)
    (hg : ∀ ℓ : Y →L[𝕜] 𝕜, AEStronglyMeasurable (fun x => ℓ (g x)) μ) :
    AEStronglyMeasurable g μ := by
  letI : MeasurableSpace Y := borel Y
  letI : BorelSpace Y := ⟨rfl⟩
  obtain ⟨ℓ, hℓ⟩ := FunctionSpaces.exists_countable_separating_on_submodule 𝕜 (⊤ : Submodule 𝕜 Y)
  let J : Y → ℕ → 𝕜 := fun y n => ℓ n y
  have hJ : Continuous J := continuous_pi fun n => (ℓ n).continuous
  have hJi : Function.Injective J := by
    intro x y hxy
    apply sub_eq_zero.mp
    have hz : (⟨x - y, by simp⟩ : (⊤ : Submodule 𝕜 Y)) = 0 := by
      apply hℓ
      intro n
      have hn := congrFun hxy n
      simpa only [map_sub, sub_eq_zero] using hn
    exact congrArg Subtype.val hz
  have hJg : AEMeasurable (J ∘ g) μ := by
    apply AEMeasurable.of_eval
    intro n
    exact (hg (ℓ n)).aemeasurable
  exact ((hJ.measurableEmbedding hJi).aemeasurable_comp_iff.mp hJg).aestronglyMeasurable

/-- Reflexivity turns the pointwise bidual representatives into a Bochner
density. The norm bound and scalar coordinates establish integrability. -/
theorem bidual_density_reconstruction : VectorRadonNikodymSpec.BidualDensityReconstruction.{u,v} := by
  intro 𝕜 _ X Y _ _ _ _ _ _ hY μ h hh hp T hT
  classical
  obtain ⟨L, hLb, hLt⟩ := dominated_operator_pointwise 𝕜 μ h hp T hT
  choose g hg using fun x => hY (L x)
  have hpoint (x : X) (ℓ : Y →L[𝕜] 𝕜) : ℓ (g x) = L x ℓ :=
    congrArg (fun z : (Y →L[𝕜] 𝕜) →L[𝕜] 𝕜 => z ℓ) (hg x)
  have htests (ℓ : Y →L[𝕜] 𝕜) : (fun x => ℓ (g x)) =ᵐ[μ] T ℓ := by
    simpa only [hpoint] using hLt ℓ
  have hmeas : AEStronglyMeasurable g μ := by
    apply aestronglyMeasurable_of_scalar_tests 𝕜 μ g
    intro ℓ
    exact (L1.integrable_coeFn (T ℓ)).aestronglyMeasurable.congr (htests ℓ).symm
  have hnorm (x : X) : ‖g x‖ ≤ h x := by
    obtain ⟨ℓ, hℓ, hval⟩ := exists_dual_vector'' 𝕜 (g x)
    calc
      ‖g x‖ = ‖ℓ (g x)‖ := by rw [hval, RCLike.norm_ofReal, abs_norm]
      _ = ‖L x ℓ‖ := congrArg norm (hpoint x ℓ)
      _ ≤ h x * ‖ℓ‖ := hLb x ℓ
      _ ≤ h x := mul_le_of_le_one_right (hp x) hℓ
  letI : NormedSpace ℝ Y := NormedSpace.restrictScalars ℝ 𝕜 Y
  exact ⟨g, hh.mono' hmeas (Eventually.of_forall hnorm), htests⟩


/-- All measure-theoretic and nonseparable-range assembly is explicit here.
The two hypotheses are separate construction lemmas, not assumptions in
the final Radon–Nikodym statement. -/
theorem representation_of_scalar_reconstruction : Assembly.{u,v} := by
  intro hs hr 𝕜 _ X Y _ _ _ _ hY μ _ m hm hac
  let V := ReflexiveMeasureRangeSpec.rangeSpan 𝕜 m
  obtain ⟨hsep, hcomp, href⟩ := reflexive_measure_separableSpan 𝕜 hY m hm
  letI : SeparableSpace V := hsep
  letI : CompleteSpace V := hcomp
  letI : SeparableSpace (V →L[𝕜] 𝕜) := dual_separable 𝕜 href
  let n := rangeMeasure 𝕜 m
  have hn : n.variation univ < ∞ := by
    simpa only [n, rangeMeasure_variation] using hm
  have hnac (A : Set X) (hA : MeasurableSet A) (hμA : μ A = 0) : n A = 0 :=
    Subtype.ext (hac A hA hμA)
  obtain ⟨h, hh, hpos, T, hT⟩ := hs 𝕜 μ n hn hnac
  obtain ⟨g, hg, htests⟩ := hr 𝕜 href μ h hh hpos T (fun ℓ => (hT ℓ).1)
  letI : NormedSpace ℝ Y := NormedSpace.restrictScalars ℝ 𝕜 Y
  letI : NormedSpace ℝ V := NormedSpace.restrictScalars ℝ 𝕜 V
  have hrep (A : Set X) (hA : MeasurableSet A) : n A = ∫ x in A, g x ∂μ := by
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)).mpr
    intro ℓ
    rw [← ℓ.integral_comp_comm hg.restrict]
    exact ((hT ℓ).2 A hA).symm.trans
      (integral_congr_ae (ae_restrict_of_ae ((htests ℓ).symm)))
  let G : X → Y := fun x => (g x : Y)
  have hG : Integrable G μ := V.subtypeL.integrable_comp hg
  have hGrep (A : Set X) (hA : MeasurableSet A) : m A = ∫ x in A, G x ∂μ := by
    calc
      m A = ((∫ x in A, g x ∂μ : V) : Y) := congrArg Subtype.val (hrep A hA)
      _ = ∫ x in A, G x ∂μ := (V.subtypeL.integral_comp_comm hg.restrict).symm
  obtain ⟨hvar, huniq⟩ := density_consequences μ m G hG hGrep
  exact ⟨G, hG, fun x => (g x).property, hGrep, hvar, huniq⟩

/-- The full vector Radon–Nikodym theorem, including nonseparable reflexive
targets, obtained by scalar reconstruction on the separable range span. -/
theorem vector_radon_nikodym : Representation.{u,v} := by
  apply representation_of_scalar_reconstruction
  · exact scalar_density_construction
  · exact bidual_density_reconstruction

end ExpandedFA.PartIV.VectorRadonNikodym
