import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.RealNormalControlTopology
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.VonNeumann.RealNormalControlMeasure
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.VonNeumann.RealNormalCyclicRealization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.VonNeumann.RealNormalRestrictedResolution
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarLpDuality
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
namespace ExpandedFA.VonNeumann.RealNormalControlTopology
universe u v w z
open RealAbelianComplexification.Spec.NativeLp

/-- Initial topologies agree when their scalar test functions have the same
range. Index sets may be empty and no bounded subset of the domain is used. -/
theorem initialTopology_eq_of_same_tests {A : Type u} {B : Type v}
    [TopologicalSpace B] {I : Type w} {J : Type z} (f : A → I → B) (g : A → J → B)
    (hfg : ∀ i, ∃ j, (fun a => f a i) = (fun a => g a j))
    (hgf : ∀ j, ∃ i, (fun a => g a j) = (fun a => f a i)) :
    TopologicalSpace.induced f Pi.topologicalSpace =
      TopologicalSpace.induced g Pi.topologicalSpace := by
  simp only [induced_to_pi]
  apply le_antisymm
  · apply le_iInf
    intro j
    obtain ⟨i, hi⟩ := hgf j
    rw [hi]
    exact iInf_le _ i
  · apply le_iInf
    intro i
    obtain ⟨j, hj⟩ := hfg i
    rw [hj]
    exact iInf_le _ j

/-- Both coefficient identities concern actual real vectors. This is the
whole-algebra conclusion once those identities have been established. -/
theorem topology_from_coefficients : Spec.TopologyFromCoefficients.{u} := by
  intro H _ _ _ N C hC
  rw [OperatorTopology.hilbert_weak_eq_coefficients ℝ H H]
  change TopologicalSpace.induced (fun f g => pairing C.involutionData f g)
      Pi.topologicalSpace =
    TopologicalSpace.induced (fun f => (C.Ψ f : H →L[ℝ] H))
      (TopologicalSpace.induced
        (fun (T : H →L[ℝ] H) (p : H × H) => ⟪p.2, T p.1⟫_ℝ) Pi.topologicalSpace)
  rw [induced_compose]
  apply initialTopology_eq_of_same_tests
  · intro g
    obtain ⟨x, y, h⟩ := hC.2 g
    exact ⟨(y, x), funext h⟩
  · intro p
    obtain ⟨g, h⟩ := hC.1 p.2 p.1
    exact ⟨g, funext h⟩

section Factorization
variable {X : Type u} [MeasurableSpace X] (μ : Measure X) (D : InvolutionData μ)

/-- These are the specific square-root and phase factors, rather than an
arbitrary complex factorization that might fail to belong to the real form. -/
theorem fixed_factorization (g : Fixed D 1) :
    ∃ a b : Fixed D 2,
      (a.val : X → ℂ) =ᵐ[μ] (fun x => (Real.sqrt ‖g.val x‖ : ℂ)) ∧
      (b.val : X → ℂ) =ᵐ[μ]
        (fun x => g.val x / (Real.sqrt ‖g.val x‖ : ℂ)) ∧
      (fun x => star (a.val x) * b.val x) =ᵐ[μ] g.val := by
  let r : X → ℂ := fun x => (Real.sqrt ‖g.val x‖ : ℂ)
  let s : X → ℂ := fun x => g.val x / r x
  have hr : Measurable r :=
    Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp
      (Lp.stronglyMeasurable g.val).measurable.norm)
  have hs : Measurable s := (Lp.stronglyMeasurable g.val).measurable.div hr
  have hr2 (x : X) : ‖r x‖ ^ 2 = ‖g.val x‖ := by
    simpa only [r, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] using Real.sq_sqrt (norm_nonneg (g.val x))
  have hs2 (x : X) : ‖s x‖ ^ 2 = ‖g.val x‖ := by
    dsimp only [s]
    rw [norm_div, div_pow, hr2]
    by_cases h : g.val x = 0
    · simp [h]
    · field_simp [norm_ne_zero_iff.mpr h]
  have hgi : Integrable (fun x => ‖g.val x‖) μ :=
    (memLp_one_iff_integrable.mp (Lp.memLp g.val)).norm
  have hrl : MemLp r 2 μ :=
    (memLp_two_iff_integrable_sq_norm hr.aestronglyMeasurable).mpr
      (by simpa only [hr2] using hgi)
  have hsl : MemLp s 2 μ :=
    (memLp_two_iff_integrable_sq_norm hs.aestronglyMeasurable).mpr
      (by simpa only [hs2] using hgi)
  have hrf : (hrl.toLp r) ∈ fixedSubmodule D 2 := by
    apply (mem_fixedSubmodule_iff_ae D _).mpr
    filter_upwards [MemLp.coeFn_toLp hrl,
      D.measurePreserving.quasiMeasurePreserving.ae (MemLp.coeFn_toLp hrl),
      fixed_ae D g] with x hx htx hfix
    rw [hx, htx]
    simp only [r, hfix, Complex.star_def, Complex.conj_ofReal, Complex.norm_conj]
  have hsf : (hsl.toLp s) ∈ fixedSubmodule D 2 := by
    apply (mem_fixedSubmodule_iff_ae D _).mpr
    filter_upwards [MemLp.coeFn_toLp hsl,
      D.measurePreserving.quasiMeasurePreserving.ae (MemLp.coeFn_toLp hsl),
      fixed_ae D g] with x hx htx hfix
    rw [hx, htx]
    simp only [s, r, hfix, star_div₀, Complex.star_def, Complex.conj_ofReal, Complex.norm_conj]
  refine ⟨⟨hrl.toLp r, hrf⟩, ⟨hsl.toLp s, hsf⟩,
    MemLp.coeFn_toLp hrl, MemLp.coeFn_toLp hsl, ?_⟩
  filter_upwards [MemLp.coeFn_toLp hrl, MemLp.coeFn_toLp hsl] with x hx hy
  rw [hx, hy]
  have hstar : star (r x) = r x := by simp [r]
  rw [hstar]
  change r x * (g.val x / r x) = g.val x
  by_cases h : g.val x = 0
  · simp [h]
  · have hr0 : r x ≠ 0 := by
      dsimp [r]
      exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (norm_pos_iff.mpr h))
    exact mul_div_cancel₀ _ hr0

theorem native_fixed_factorization : Spec.FixedFactorization.{u} := by
  intro X _ μ D g
  exact fixed_factorization μ D g

/-- Equality for every multiplier, using the Hilbert conjugation convention. -/
theorem factorization_integral (g : Fixed D 1) :
    ∃ a b : Fixed D 2, ∀ f : Fixed D ∞,
      (∫ x, star (a.val x) * f.val x * b.val x ∂μ) =
        ∫ x, f.val x * g.val x ∂μ := by
  obtain ⟨a, b, _, _, hab⟩ := fixed_factorization μ D g
  refine ⟨a, b, fun f => integral_congr_ae ?_⟩
  filter_upwards [hab] with x hx
  rw [← hx]
  ring
end Factorization

section Projection
variable {X : Type u} [MeasurableSpace X] {μ : Measure X}
variable (D : InvolutionData μ) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Contractive averaging onto the real form of the native complex quotient. -/
def fixedProjection : Lp ℂ p μ →L[ℝ] Fixed D p :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨(1 / 2 : ℝ) • (f + conjugatePullback D f), by
        change conjugatePullback D ((1 / 2 : ℝ) • (f + conjugatePullback D f)) =
          (1 / 2 : ℝ) • (f + conjugatePullback D f)
        rw [conjugatePullback_real_smul, conjugatePullback_add,
          conjugatePullback_involutive D f, add_comm]⟩
      map_add' := by
        intro f g
        apply Subtype.ext
        change (1/2 : ℝ) • ((f+g) + conjugatePullback D (f+g)) =
          (1/2 : ℝ) • (f + conjugatePullback D f) +
          (1/2 : ℝ) • (g + conjugatePullback D g)
        simp only [conjugatePullback_add, smul_add]
        abel
      map_smul' := by
        intro c f
        apply Subtype.ext
        change (1/2 : ℝ) • (c • f + conjugatePullback D (c • f)) =
          c • ((1/2 : ℝ) • (f + conjugatePullback D f))
        rw [conjugatePullback_real_smul, ← smul_add, smul_comm] }
    1 (fun f => by
      change ‖(1 / 2 : ℝ) • (f + conjugatePullback D f)‖ ≤ 1 * ‖f‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
      have h := norm_add_le f (conjugatePullback D f)
      rw [norm_conjugatePullback] at h
      linarith)

@[simp] theorem fixedProjection_val (f : Lp ℂ p μ) :
    (fixedProjection D p f).val = (1 / 2 : ℝ) • (f + conjugatePullback D f) := rfl

@[simp] theorem fixedProjection_fixed (f : Fixed D p) :
    fixedProjection D p f.val = f := by
  apply Subtype.ext
  change (1 / 2 : ℝ) • (f.val + conjugatePullback D f.val) = f.val
  rw [show conjugatePullback D f.val = f.val from f.property]
  module

theorem fixedProjection_norm (f : Lp ℂ p μ) : ‖fixedProjection D p f‖ ≤ ‖f‖ := by
  change ‖(1 / 2 : ℝ) • (f + conjugatePullback D f)‖ ≤ ‖f‖
  rw [norm_smul]
  have h := norm_add_le f (conjugatePullback D f)
  rw [norm_conjugatePullback] at h
  norm_num at *
  linarith

end Projection
section PairingProjection
variable {X : Type u} [MeasurableSpace X] {μ : Measure X}
variable (D : InvolutionData μ)
open RealAbelianComplexification.NativeLp

/-- Covariance of the ordinary complex bilinear pairing, on native classes. -/
theorem conjugate_pairing (f : Lp ℂ ∞ μ) (g : Lp ℂ 1 μ) :
    (∫ x, conjugatePullback D f x * conjugatePullback D g x ∂μ) =
      star (∫ x, f x * g x ∂μ) := by
  calc
    _ = ∫ x, star (f (D.tau x) * g (D.tau x)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [coeFn_conjugatePullback D f, coeFn_conjugatePullback D g]
        with x hf hg
      rw [hf, hg, star_mul]
      exact mul_comm _ _
    _ = star (∫ x, f (D.tau x) * g (D.tau x) ∂μ) := integral_conj
    _ = _ := congrArg star (D.measurePreserving.integral_comp
      (MeasurableEquiv.ofInvolutive D.tau D.involutive
        D.measurePreserving.measurable).measurableEmbedding (fun x => f x * g x))

theorem pairing_project_left (f : Lp ℂ ∞ μ) (g : Fixed D 1) :
    pairing D (fixedProjection D ∞ f) g = (∫ x, f x * g.val x ∂μ).re := by
  have hc := conjugate_pairing D f g.val
  rw [show conjugatePullback D g.val = g.val from g.property] at hc
  change ((ContinuousLinearMap.mul ℝ ℂ).lpPairing μ ∞ 1
    ((1/2 : ℝ) • (f + conjugatePullback D f)) g.val).re = _
  simp only [map_smul, map_add, smul_apply, add_apply]
  simp only [ContinuousLinearMap.lpPairing_eq_integral,
    ContinuousLinearMap.mul_apply', hc, Complex.add_re, Complex.smul_re,
    Complex.star_def, Complex.conj_re]
  ring

theorem pairing_project_right (f : Fixed D ∞) (g : Lp ℂ 1 μ) :
    pairing D f (fixedProjection D 1 g) = (∫ x, f.val x * g x ∂μ).re := by
  have hc := conjugate_pairing D f.val g
  rw [show conjugatePullback D f.val = f.val from f.property] at hc
  change ((ContinuousLinearMap.mul ℝ ℂ).lpPairing μ ∞ 1 f.val
    ((1/2 : ℝ) • (g + conjugatePullback D g))).re = _
  simp only [map_smul, map_add]
  simp only [ContinuousLinearMap.lpPairing_eq_integral,
    ContinuousLinearMap.mul_apply', hc, Complex.add_re, Complex.smul_re,
    Complex.star_def, Complex.conj_re]
  ring

/-- The upper estimate uses the inherited real norm, including zero measures. -/
theorem fixed_pairing_norm_le (f : Fixed D ∞) : ‖pairing D f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro g
  rw [pairing_eq_integral]
  calc
    ‖(∫ x, f.val x * g.val x ∂μ).re‖ ≤ ‖∫ x, f.val x * g.val x ∂μ‖ :=
      by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm _
    _ ≤ ‖f‖ * ‖g‖ := by
      change _ ≤ ‖f.val‖ * ‖g.val‖
      have h := FunctionSpaces.lp_pairing_apply_bound μ 1 ∞ f.val g.val
      rw [(FunctionSpaces.lp_pairing_integral μ 1 ∞ f.val g.val).2] at h
      simpa only [mul_comm] using h

end PairingProjection
section Predual
variable {X : Type u} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
variable (D : InvolutionData μ)

/-- Exact norm: taking the real part of a complex functional preserves its
norm; averaging a test into the real form is contractive. -/
theorem fixed_pairing_norm (f : Fixed D ∞) : ‖pairing D f‖ = ‖f‖ := by
  apply le_antisymm (fixed_pairing_norm_le D f)
  let T : Lp ℂ 1 μ →L[ℂ] ℂ := FunctionSpaces.lpIntegralPairing μ 1 ∞ f.val
  let TR : Lp ℂ 1 μ →L[ℝ] ℝ := Complex.reCLM.comp (T.restrictScalars ℝ)
  have hnormT : ‖T‖ = ‖f‖ :=
    FunctionSpaces.lp_pairing_exact_norm μ 1 ∞ (by norm_num) (Or.inl inferInstance) f.val
  have hnormTR : ‖TR‖ = ‖T‖ := by
    exact (StrongDual.extendRCLikeₗᵢ (𝕜 := ℂ)).symm.norm_map T
  have hTR (g : Lp ℂ 1 μ) : TR g = pairing D f (fixedProjection D 1 g) := by
    rw [pairing_project_right]
    change (FunctionSpaces.ScalarLpIntegralPairingSpec.IntegralPairingValue μ 1 ∞ f.val g).re = _
    rw [(FunctionSpaces.lp_pairing_integral μ 1 ∞ f.val g).2]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => mul_comm _ _)
  calc
    ‖f‖ = ‖TR‖ := hnormT.symm.trans hnormTR.symm
    _ ≤ ‖pairing D f‖ := by
      apply TR.opNorm_le_bound (norm_nonneg (pairing D f))
      intro g
      rw [hTR]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_left (fixedProjection_norm D 1 g) (norm_nonneg _))

/-- Every real functional on the fixed L¹ subspace extends by Hahn--Banach.
Complex L¹ duality and averaging its density then represent the original
functional on that very subspace. -/
theorem fixed_pairing_surjective : Function.Surjective (pairing D) := by
  intro L
  obtain ⟨F, hF, _⟩ := exists_extension_norm_eq (fixedSubmodule D 1) L
  let T : Lp ℂ 1 μ →L[ℂ] ℂ := F.extendRCLike
  obtain ⟨f, hf, _⟩ := FunctionSpaces.lp_one_infinity_duality_sigmaFinite μ T
  refine ⟨fixedProjection D ∞ f, ?_⟩
  apply ContinuousLinearMap.ext
  intro g
  rw [pairing_project_left]
  have hcomm : (∫ x, f x * g.val x ∂μ) = ∫ x, g.val x * f x ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall (fun x => mul_comm _ _))
  rw [hcomm, ← (hf.1 g.val).2]
  change (F.extendRCLike g.val : ℂ).re = L g
  rw [show (F.extendRCLike g.val : ℂ).re = F g.val from
    by simpa only [RCLike.re_eq_complex_re] using
      StrongDual.re_extendRCLike_apply (𝕜 := ℂ) F g.val]
  exact hF g

/-- An isometric SURJECTION with its map fixed to the ordinary real bilinear
integral; this identifies the actual native fixed-space Banach predual. -/
theorem native_predual : Spec.NativePredual.{u} := by
  intro X _ μ _ D
  let I : Fixed D ∞ →ₗᵢ[ℝ] (Fixed D 1 →L[ℝ] ℝ) :=
    { (pairing D).toLinearMap with norm_map' := fixed_pairing_norm μ D }
  refine ⟨LinearIsometryEquiv.ofSurjective I (fixed_pairing_surjective μ D), ?_⟩
  intro f g
  rfl
end Predual
section Coefficients
open TraceIdeals.RealComplexification
open RealAbelianComplexification
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
local instance : CompleteSpace (Space H) := TraceIdeals.RealComplexification.Spec.completeSpace

@[simp] theorem conjugation_inclusion (x : H) : conjugation (inclusion x) = inclusion x := by
  change (x, -(0 : H)) = (x, 0)
  rw [neg_zero]

/-- The original real vectors give conjugate-covariant complex measures. -/
theorem real_coefficient_covariance {N : H →L[ℝ] H}
    (C : RealNormalControlMeasure.Spec.AlgebraModel N) (x y : H)
    (B : Set (RealNormalControlMeasure.Spec.Spectrum N)) (hB : MeasurableSet B) :
    ⟪inclusion x, C.E (C.τ ⁻¹' B) (inclusion y)⟫_ℂ =
      star ⟪inclusion x, C.E B (inclusion y)⟫_ℂ := by
  have hc := C.covariance B hB (inclusion y)
  rw [conjugation_inclusion] at hc
  rw [← hc]
  simpa only [conjugation_inclusion] using
    inner_conjugation (inclusion x) (C.E B (inclusion y))

/-- Uniqueness of integrable densities, applied to the conjugate pullback,
proves fixedness without choosing real-valued representatives. -/
theorem coefficient_densities {N : H →L[ℝ] H}
    (C : RealNormalControlMeasure.Spec.AlgebraModel N) : Spec.CoefficientDensities C := by
  letI := C.finite
  intro x y
  obtain ⟨g, hg, hsets⟩ := NormalAlgebraControlMeasure.coefficient_density
    C.E C.μ C.control (inclusion x) (inclusion y)
  let q : Lp ℂ 1 C.μ := (memLp_one_iff_integrable.mpr hg).toLp g
  have hq : Integrable (fun z => q z) C.μ := memLp_one_iff_integrable.mp (Lp.memLp q)
  have hsetsq (B) (hB : MeasurableSet B) :
      ⟪inclusion x, C.E B (inclusion y)⟫_ℂ = ∫ z in B, q z ∂C.μ :=
    (hsets B hB).trans (setIntegral_congr_ae hB
      ((MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hg)).symm.mono (fun _ h _ => h)))
  have hCq : Integrable (fun z => conjugatePullback C.involutionData q z) C.μ :=
    memLp_one_iff_integrable.mp (Lp.memLp _)
  have hfixed : conjugatePullback C.involutionData q = q := by
    apply Lp.ext
    apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
      (fun _ _ _ => hCq.integrableOn) (fun _ _ _ => hq.integrableOn)
    intro B hB _
    have hτB : C.τ ⁻¹' (C.τ ⁻¹' B) = B := by
      ext z
      change (C.τ (C.τ z) ∈ B) ↔ z ∈ B
      rw [C.involutive]
    have hcomp := C.measurePreserving.setIntegral_preimage_emb
      C.τ.measurableEmbedding (fun z => q z) (C.τ ⁻¹' B)
    rw [hτB] at hcomp
    calc
      _ = ∫ z in B, star (q (C.τ z)) ∂C.μ :=
        setIntegral_congr_ae hB
          ((coeFn_conjugatePullback C.involutionData q).mono (fun _ h _ => h))
      _ = star (∫ z in B, q (C.τ z) ∂C.μ) := integral_conj
      _ = star (∫ z in C.τ ⁻¹' B, q z ∂C.μ) := congrArg star hcomp
      _ = star ⟪inclusion x, C.E (C.τ ⁻¹' B) (inclusion y)⟫_ℂ := by
        rw [hsetsq _ (C.τ.measurable hB)]
      _ = ⟪inclusion x, C.E B (inclusion y)⟫_ℂ := by
        rw [real_coefficient_covariance C x y B hB, star_star]
      _ = _ := hsetsq B hB
  exact ⟨⟨q, hfixed⟩, hsetsq⟩

/-- Every original-real matrix coefficient has one fixed native L¹ density,
with the exact identity for every symbol in the given algebra model. -/
theorem forward_coefficients : Spec.ForwardCoefficients.{u} := by
  intro H _ _ _ N C
  refine ⟨coefficient_densities C, ?_⟩
  intro x y
  obtain ⟨g, hsets⟩ := coefficient_densities C x y
  refine ⟨g, ?_⟩
  intro f
  obtain ⟨a, ha, hac, hae⟩ := C.representatives f
  have hrep := (C.on_representatives f a ha hac hae).2
  have hscalar := NormalAlgebraControlMeasure.spectralIntegral_coefficient_density
    C.E C.μ (inclusion x) (inclusion y)
    (memLp_one_iff_integrable.mp (Lp.memLp g.val)) hsets a ha
  rw [← SpectralMeasure.FugledePutnam.calculus_eq_integral C.E C.Φ C.calculus a ha,
    ← hrep, operator_inclusion, inner_inclusion] at hscalar
  rw [RealAbelianComplexification.NativeLp.pairing_eq_integral]
  have heq : (∫ z, a z * g.val z ∂C.μ) = ∫ z, f.val z * g.val z ∂C.μ :=
    integral_congr_ae (hae.mono (fun z h => congrArg (fun c => c * g.val z) h))
  rw [← heq, ← hscalar, Complex.ofReal_re]

/-- Combine the equivariant cyclic unitary with the faithful restricted
resolution on its actual closed range, retaining every supplied witness. -/
theorem cyclic_construction : Spec.CyclicConstruction.{u} := by
  intro H _ _ _ N hN C
  letI := C.finite
  obtain ⟨S, hS, U, eS, hcanonical, heS, hunit, hconj, hcontinuous, hinvariant,
    V, hreal, hmultiplier⟩ := RealNormalCyclicRealization.cyclic_realization H N hN C
  letI : CompleteSpace S := hS.completeSpace_coe
  obtain ⟨R, F, hrestriction, hnormal, hspectrum, hprojection, hmeasure, hcalculus⟩ :=
    RealNormalRestrictedResolution.restricted_resolution H N hN C S hS eS heS hinvariant
  exact ⟨S, hS, U, R, F, eS, hcanonical, heS, hunit, hconj, hcontinuous,
    hrestriction, hnormal, hspectrum, hprojection, hmeasure, hcalculus,
    V, hreal, hmultiplier⟩

/-- Transporting the two fixed square-root/phase factors through the real
cyclic unitary realizes each L¹ test as one coefficient on actual H. -/
theorem reverse_from_cyclic : Spec.ReverseFromCyclic.{u} := by
  intro H _ _ _ N C hcyc g
  letI := C.finite
  obtain ⟨S, hS, U, R, F, eS, _, _, _, _, _, _, _, _, _, _, _, V, _, hVmul⟩ := hcyc
  obtain ⟨a, b, _, _, hab⟩ := fixed_factorization C.μ C.involutionData g
  refine ⟨(V a : H), (V b : H), ?_⟩
  intro f
  rw [← hVmul f b]
  change pairing C.involutionData f g = inner ℝ (V a) (V (restrictedMultiplier C.involutionData f b))
  rw [V.inner_map_map]
  change pairing C.involutionData f g = inner ℝ a.val (restrictedMultiplier C.involutionData f b).val
  rw [NativeLp.pairing_eq_integral, NativeLp.l2_inner_real_formula]
  congr 1
  apply integral_congr_ae
  filter_upwards [hab, coeFn_restrictedMultiplier C.involutionData f b] with z hz hm
  rw [hm, ← hz]
  ring

/-- All remaining algebra/predual/topology conclusions assemble with the
upstream model's witnesses, once its equivariant cyclic model is proved. -/
theorem complete_of_cyclic : Spec.AssemblyFromCyclic.{u} := by
  intro hcyc H _ _ _ _ N hN
  obtain ⟨C⟩ := RealNormalControlMeasure.real_normal_control_measure H N hN
  letI := C.finite
  obtain ⟨I, hI⟩ := native_predual (RealNormalControlMeasure.Spec.Spectrum N) C.μ C.involutionData
  have hCyc := hcyc H N hN C
  have hcoeff : Spec.CoefficientFunctionals C :=
    ⟨(forward_coefficients H N C).2, reverse_from_cyclic H N C hCyc⟩
  exact ⟨{ C with
    predual := I
    predual_apply := hI
    densities := coefficient_densities C
    coefficients := hcoeff
    cyclic := hCyc
    topology := topology_from_coefficients H N C hcoeff }⟩
/-- The complete corrected real normal theorem, with a constructed finite
control measure, native real L¹ predual and real WOT on the entire algebra. -/
theorem real_normal_control_topology : Spec.RealNormalControlTopology.{u} :=
  complete_of_cyclic cyclic_construction

end Coefficients
end ExpandedFA.VonNeumann.RealNormalControlTopology
