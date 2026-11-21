import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.ContinuousKernelTranspose
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.ContinuousKernel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarRieszMarkov
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ZeroAtInfty Topology
open ExpandedFA.FunctionSpaces.ScalarRieszMarkovSpec
open ExpandedFA.FunctionSpaces.PositiveRadonRepresentationSpec
open ExpandedFA.FunctionSpaces.ScalarRieszMarkov
universe u v w
namespace ExpandedFA.PartV.ContinuousKernelTranspose

/-- The canonical compact-space inclusion into C₀, with unchanged values. -/
def compactLift {𝕜 X : Type*} [RCLike 𝕜] [TopologicalSpace X] [CompactSpace X] :
    C(X, 𝕜) →L[𝕜] C₀(X, 𝕜) :=
  LinearMap.mkContinuous
    { toFun := ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty
      map_add' := fun _ _ => by ext x; rfl
      map_smul' := fun _ _ => by ext x; rfl }
    1 (fun f => by
      simp only [one_mul]
      exact (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr f.norm_coe_le_norm)

@[simp] lemma compactLift_apply {𝕜 X : Type*} [RCLike 𝕜] [TopologicalSpace X]
    [CompactSpace X] (f : C(X, 𝕜)) (x : X) : compactLift f x = f x := rfl

/-- Scalar-linear integration on C(X), the compact Riesz--Markov pairing. -/
def compactFunctional {𝕜 X : Type*} [RCLike 𝕜] [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (η : VectorMeasure X 𝕜)
    [IsFiniteMeasure η.variation] : C(X, 𝕜) →L[𝕜] 𝕜 :=
  (scalarMeasureFunctional η).comp compactLift

@[simp] lemma compactFunctional_apply {𝕜 X : Type*} [RCLike 𝕜] [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (η : VectorMeasure X 𝕜)
    [IsFiniteMeasure η.variation] (f : C(X, 𝕜)) :
    compactFunctional η f = scalarIntegral η f := rfl

section Interchange
variable {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
  [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  (ν : Measure Y) [IsFiniteMeasure ν] (k : C(X × Y, 𝕜))
  (η : VectorMeasure X 𝕜) [IsFiniteMeasure η.variation]

/-- Compose the continuous family of sections with a bounded functional. -/
def transposeDensity : C(Y, 𝕜) :=
  ⟨fun y => compactFunctional η (ContinuousKernel.Spec.kernelSection k y),
    (compactFunctional η).continuous.comp (ContinuousKernel.Spec.kernelSection k).continuous⟩

omit [T2Space X] [CompactSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y] in
lemma transposeDensity_apply (y : Y) :
    transposeDensity k η y = scalarIntegral η (fun x => k (x, y)) := rfl

/-- Bochner integration in C(X) commutes with the measure functional.
This does not form a product measure or assert product Borel measurability. -/
lemma iterated_integral (u : C(Y, 𝕜)) :
    scalarIntegral η (ContinuousKernel.Spec.KernelOperatorValue ν k u) =
      ∫ y, u y * transposeDensity k η y ∂ν := by
  change compactFunctional η (∫ y, u y • ContinuousKernel.Spec.kernelSection k y ∂ν) = _
  rw [← (compactFunctional η).integral_comp_comm
    (ContinuousKernel.Spec.kernel_section_integrable ν k u)]
  congr 1
  ext y
  exact (compactFunctional η).map_smul (u y) _

end Interchange

section Density
variable {𝕜 Y : Type*} [RCLike 𝕜] [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
  (h : C(Y, 𝕜))

omit [IsFiniteMeasure ν] in
lemma integrable_mul_continuous {f : Y → 𝕜} (hf : Integrable f ν) :
    Integrable (fun y => f y * h y) ν := by
  have hi := hf.bdd_smul ‖h‖ h.continuous.aestronglyMeasurable
    (Eventually.of_forall h.norm_coe_le_norm)
  change Integrable (fun y => h y * f y) ν at hi
  simpa only [mul_comm] using hi

/-- Bounded densities give domination of the genuine total variation. -/
lemma density_variation_le :
    (ν.withDensityᵥ (h : Y → 𝕜)).variation ≤ (‖h‖₊ : ℝ≥0∞) • ν := by
  rw [Measure.variation_withDensityᵥ
    (h.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  calc
    ν.withDensity (fun y => ‖h y‖ₑ) ≤ ν.withDensity (fun _ => (‖h‖₊ : ℝ≥0∞)) := by
      apply withDensity_mono
      filter_upwards with y
      exact_mod_cast h.norm_coe_le_norm y
    _ = _ := withDensity_const _

lemma density_finite_radon [T2Space Y] (hν : PositiveRadon ν) :
    FiniteScalarRadon (ν.withDensityᵥ (h : Y → 𝕜)) := by
  have : ν.Regular :=
    (ExpandedFA.FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular ν).mp hν
  have hle := density_variation_le ν h
  have : IsFiniteMeasure ((‖h‖₊ : ℝ≥0∞) • ν) :=
    ⟨by simp only [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top ν univ)⟩
  have : IsFiniteMeasure (ν.withDensityᵥ (h : Y → 𝕜)).variation :=
    isFiniteMeasure_of_le ((‖h‖₊ : ℝ≥0∞) • ν) hle
  have : ((‖h‖₊ : ℝ≥0∞) • ν).Regular := Measure.Regular.smul ENNReal.coe_ne_top
  exact ⟨measure_lt_top _ _,
    (ExpandedFA.FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mpr
      (regular_of_le hle)⟩

/-- Weighted scalar integration is continuous on L¹ for a bounded density. -/
lemma continuous_weightedIntegral :
    Continuous (fun f : Y →₁[ν] 𝕜 => ∫ y, f y * h y ∂ν) := by
  apply LipschitzWith.continuous (K := ‖h‖₊)
  apply LipschitzWith.of_dist_le_mul
  intro f g
  have hf := integrable_mul_continuous ν h (L1.integrable_coeFn f)
  have hg := integrable_mul_continuous ν h (L1.integrable_coeFn g)
  rw [dist_eq_norm, ← integral_sub hf hg]
  calc
    ‖∫ y, f y * h y - g y * h y ∂ν‖ ≤
        ∫ y, ‖f y * h y - g y * h y‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ‖h‖ * ‖f y - g y‖ ∂ν := by
      apply integral_mono (hf.sub hg).norm
        (((L1.integrable_coeFn f).sub (L1.integrable_coeFn g)).norm.const_mul _)
      intro y
      change ‖f y * h y - g y * h y‖ ≤ ‖h‖ * ‖f y - g y‖
      rw [← sub_mul, norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (h.norm_coe_le_norm y) (norm_nonneg _)
    _ = ‖h‖ * dist f g := by
      rw [integral_const_mul, L1.dist_eq_integral_dist]
      simp only [dist_eq_norm]

/-- The multiplication integral against the actual vector measure hν.
We compare its set-to-function extension with ordinary weighted integration,
first on indicators and then by L¹ continuity. -/
lemma scalarIntegral_density {f : Y → 𝕜} (hf : Integrable f ν) :
    scalarIntegral (ν.withDensityᵥ (h : Y → 𝕜)) f = ∫ y, f y * h y ∂ν := by
  let ρ := ν.withDensityᵥ (h : Y → 𝕜)
  let B := ContinuousLinearMap.mul ℝ 𝕜
  have hh : Integrable (h : Y → 𝕜) ν :=
    h.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hdom := density_variation_le ν h
  have hT : DominatedFinMeasAdditive ν (ρ.transpose B) (‖B‖ * ‖h‖) := by
    refine ⟨fun s t hs ht _ _ hst => cbmApplyMeasure_union ρ B hs ht hst, ?_⟩
    intro s hs _
    calc
      ‖ρ.transpose B s‖ ≤ ‖B‖ * ‖ρ s‖ := norm_cbmApplyMeasure_le ρ B s
      _ ≤ ‖B‖ * (‖h‖ * ν.real s) := by
        apply mul_le_mul_of_nonneg_left (a := ‖B‖) (b := ‖ρ s‖) (c := ‖h‖ * ν.real s) _ (norm_nonneg B)
        rw [show ρ s = ∫ y in s, h y ∂ν from withDensityᵥ_apply hh hs]
        simpa only [measureReal_restrict_apply_univ] using
          (norm_integral_le_of_norm_le_const (μ := ν.restrict s)
            (Eventually.of_forall h.norm_coe_le_norm))
      _ = (‖B‖ * ‖h‖) * ν.real s := by ring
  have heq : setToFun ν (ρ.transpose B) hT f = ∫ y, f y * h y ∂ν := by
    apply hf.induction (P := fun f => setToFun ν (ρ.transpose B) hT f = ∫ y, f y * h y ∂ν)
    · intro c s hs hsf
      rw [setToFun_indicator_const hT hs hsf.ne]
      change c * ρ s = _
      rw [show ρ s = ∫ y in s, h y ∂ν from withDensityᵥ_apply hh hs,
        ← integral_const_mul]
      rw [← integral_indicator hs]
      congr 1
      ext y
      by_cases hy : y ∈ s <;> simp [hy]
    · intro f g _ hf hg hfeq hgeq
      rw [setToFun_add hT hf hg, hfeq, hgeq, ← integral_add
        (integrable_mul_continuous ν h hf) (integrable_mul_continuous ν h hg)]
      congr 1
      ext y
      exact (add_mul _ _ _).symm
    · exact isClosed_eq (continuous_setToFun hT) (continuous_weightedIntegral ν h)
    · intro f g hfg _ heq
      rw [← setToFun_congr_ae hT hfg, heq]
      apply integral_congr_ae
      filter_upwards [hfg] with y hy
      rw [hy]
  calc
    scalarIntegral ρ f = setToFun ν (ρ.transpose B) hT f := by
      exact (setToFun_congr_measure_of_integrable (‖h‖₊ : ℝ≥0∞)
        ENNReal.coe_ne_top hdom hT (dominatedFinMeasAdditive_cbmApplyMeasure ρ B) f hf).symm
    _ = _ := heq

end Density
/-- Full transpose identity, including the representing Radon measure itself.
Riesz--Markov uniqueness is applied only after proving the interchange and
the density pairing. -/
theorem continuous_kernel_transpose : Spec.FullTheorem.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ _ _ _ _ ν _ hν k η hη
  let : IsFiniteMeasure η.variation := ⟨hη.1⟩
  let h := transposeDensity k η
  have hd := density_finite_radon ν h hν
  have hpair (u : C(Y, 𝕜)) := scalarIntegral_density ν h
    (u.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hi (u : C(Y, 𝕜)) := iterated_integral ν k η u
  refine ⟨ContinuousKernel.kernelOperator_norm_le ν k,
    ContinuousKernel.kernelOperator_isCompact ν k, h,
    transposeDensity_apply k η, hd, ?_, hpair, ?_⟩
  · intro u
    exact ⟨(compactLift (ContinuousKernel.Spec.KernelOperatorValue ν k u)).toBCF.integrable
      η.variation, integrable_mul_continuous ν h
        (u.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)), hi u⟩
  · intro ρ hρ
    constructor
    · intro hρrep
      apply scalarIntegral_injective ρ (ν.withDensityᵥ (h : Y → 𝕜)) hρ hd
      intro f
      let u : C(Y, 𝕜) := ⟨f, f.continuous⟩
      exact (hρrep u).trans ((hi u).trans (hpair u).symm)
    · rintro rfl u
      exact (hpair u).trans (hi u).symm

end ExpandedFA.PartV.ContinuousKernelTranspose
