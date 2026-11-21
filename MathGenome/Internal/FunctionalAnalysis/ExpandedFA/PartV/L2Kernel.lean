import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.L2Kernel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarLpIntegralPairing
import Mathlib.Tactic.Linarith

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal
universe u v
noncomputable section
namespace ExpandedFA.PartV.L2Kernel

variable {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [RCLike 𝕜] {μ : Measure X} {ν : Measure Y} [SigmaFinite μ] [SigmaFinite ν]

omit [SigmaFinite μ] in
lemma integral_sq_norm (f : X → 𝕜) (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) = ‖hf.toLp f‖ ^ 2 := by
  have h := congrArg RCLike.re (inner_self_eq_norm_sq_to_K (𝕜 := 𝕜) (hf.toLp f))
  rw [L2.inner_def, ← integral_re (L2.integrable_inner (hf.toLp f) (hf.toLp f))] at h
  simp only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

theorem kernel_sections : L2KernelSpec.Sections.{u,v} := by
  intro X Y 𝕜 _ _ _ μ ν _ _ k hk
  have hi := (memLp_two_iff_integrable_sq_norm hk.aestronglyMeasurable).mp hk
  filter_upwards [hk.aestronglyMeasurable.prodMk_left, hi.prod_right_ae] with x hx hxi
  exact (memLp_two_iff_integrable_sq_norm hx).mpr hxi

theorem kernel_representative_independence : L2KernelSpec.RepresentativeIndependence.{u,v} := by
  intro X Y 𝕜 _ _ _ μ ν _ _ k k' u u' hk hu
  filter_upwards [ae_ae_of_ae_prod hk] with x hx
  apply integral_congr_ae
  filter_upwards [hx, hu] with y hy hy'
  rw [hy, hy']

theorem kernel_absolute_section_integrability :
    L2KernelSpec.AbsoluteSectionIntegrability.{u,v} := by
  intro X Y 𝕜 _ _ _ μ ν _ _ k u hk hu
  filter_upwards [kernel_sections μ ν k hk] with x hx
  exact ⟨hx.integrable_mul hu, (hx.integrable_mul hu).norm⟩

lemma integral_section_sq_bound (k : X × Y → 𝕜) (u : Y → 𝕜)
    (hk : MemLp k 2 (μ.prod ν)) (hu : MemLp u 2 ν) :
    ∀ᵐ x ∂μ, ‖∫ y, k (x,y) * u y ∂ν‖ ^ 2 ≤
      (∫ y, ‖k (x,y)‖ ^ 2 ∂ν) * ‖hu.toLp u‖ ^ 2 := by
  filter_upwards [kernel_sections μ ν k hk] with x hx
  have hn : ‖∫ y, k (x,y) * u y ∂ν‖ ≤
      ‖hx.toLp (fun y => k (x,y))‖ * ‖hu.toLp u‖ := by
    rw [← ExpandedFA.FunctionSpaces.lp_pairing_on_representatives ν 2 2
      (fun y => k (x,y)) u hx hu]
    exact (ExpandedFA.FunctionSpaces.lp_pairing_apply_bound ν 2 2
      (hu.toLp u) (hx.toLp (fun y => k (x,y)))).trans_eq (mul_comm _ _)
  calc
    _ ≤ (‖hx.toLp (fun y => k (x,y))‖ * ‖hu.toLp u‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = _ := by rw [mul_pow, integral_sq_norm _ hx]

omit [SigmaFinite μ] in
lemma integral_output_measurable (k : X × Y → 𝕜) (u : Y → 𝕜)
    (hk : MemLp k 2 (μ.prod ν)) (hu : MemLp u 2 ν) :
    AEStronglyMeasurable (fun x => ∫ y, k (x,y) * u y ∂ν) μ :=
  (hk.aestronglyMeasurable.mul hu.aestronglyMeasurable.comp_snd).integral_prod_right'

theorem kernel_output_memLp : L2KernelSpec.OutputMemLp.{u,v} := by
  intro X Y 𝕜 _ _ _ μ ν _ _ k u hk hu
  have hm := integral_output_measurable k u hk hu
  have hi := (memLp_two_iff_integrable_sq_norm hk.aestronglyMeasurable).mp hk
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply (hi.integral_prod_left.mul_const (‖hu.toLp u‖ ^ 2)).mono'
    (hm.norm.pow 2)
  filter_upwards [integral_section_sq_bound k u hk hu] with x hx
  change |‖∫ y, k (x,y) * u y ∂ν‖ ^ 2| ≤ _
  rwa [abs_of_nonneg (sq_nonneg _)]

lemma integral_output_bound (k : X × Y → 𝕜) (u : Y → 𝕜)
    (hk : MemLp k 2 (μ.prod ν)) (hu : MemLp u 2 ν) :
    ‖(kernel_output_memLp μ ν k u hk hu).toLp _‖ ≤
      ‖hk.toLp k‖ * ‖hu.toLp u‖ := by
  have hi := (memLp_two_iff_integrable_sq_norm hk.aestronglyMeasurable).mp hk
  have ho := kernel_output_memLp μ ν k u hk hu
  have hsq : ‖ho.toLp _‖ ^ 2 ≤ (‖hk.toLp k‖ * ‖hu.toLp u‖) ^ 2 := by
    rw [← integral_sq_norm _ ho]
    calc
      _ ≤ ∫ x, (∫ y, ‖k (x,y)‖ ^ 2 ∂ν) * ‖hu.toLp u‖ ^ 2 ∂μ :=
        integral_mono_ae ((memLp_two_iff_integrable_sq_norm ho.aestronglyMeasurable).mp ho)
          (hi.integral_prod_left.mul_const _) (integral_section_sq_bound k u hk hu)
      _ = _ := by
        rw [integral_mul_const, ← integral_prod _ hi, integral_sq_norm k hk, mul_pow]
  nlinarith [norm_nonneg (ho.toLp (fun x => ∫ y, k (x,y) * u y ∂ν)),
    mul_nonneg (norm_nonneg (hk.toLp k)) (norm_nonneg (hu.toLp u))]

/-- The output class is formed only after its L² membership has been proved. -/
def integralOutput (k : Lp 𝕜 2 (μ.prod ν)) (u : Lp 𝕜 2 ν) : Lp 𝕜 2 μ :=
  (kernel_output_memLp μ ν k u (Lp.memLp k) (Lp.memLp u)).toLp _

lemma integralOutput_ae (k : Lp 𝕜 2 (μ.prod ν)) (u : Lp 𝕜 2 ν) :
    (integralOutput k u : X → 𝕜) =ᵐ[μ] fun x => ∫ y, k (x,y) * u y ∂ν :=
  MemLp.coeFn_toLp _

lemma integralOutput_norm (k : Lp 𝕜 2 (μ.prod ν)) (u : Lp 𝕜 2 ν) :
    ‖integralOutput k u‖ ≤ ‖k‖ * ‖u‖ := by
  simpa only [integralOutput, Lp.toLp_coeFn] using integral_output_bound k u (Lp.memLp k) (Lp.memLp u)

/-- Linearity descends from sectionwise integral linearity to the a.e. quotient. -/
def integralLinearMap (k : Lp 𝕜 2 (μ.prod ν)) : Lp 𝕜 2 ν →ₗ[𝕜] Lp 𝕜 2 μ where
  toFun := integralOutput k
  map_add' u v := by
    apply Lp.ext
    filter_upwards [integralOutput_ae k (u + v), integralOutput_ae k u,
      integralOutput_ae k v, Lp.coeFn_add (integralOutput k u) (integralOutput k v),
      kernel_sections μ ν k (Lp.memLp k)] with x huv hu hv hout hx
    rw [huv, hout, Pi.add_apply, hu, hv]
    calc
      _ = ∫ y, (k (x,y) * u y + k (x,y) * v y) ∂ν := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add u v] with y hy
        rw [hy, Pi.add_apply, mul_add]
      _ = _ := integral_add (hx.integrable_mul (Lp.memLp u))
        (hx.integrable_mul (Lp.memLp v))
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [integralOutput_ae k (c • u), integralOutput_ae k u,
      Lp.coeFn_smul c (integralOutput k u)] with x hcu hu hout
    simp only [RingHom.id_apply]
    rw [hcu, hout, Pi.smul_apply, hu]
    calc
      _ = ∫ y, c • (k (x,y) * u y) ∂ν := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c u] with y hy
        rw [hy, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]
      _ = _ := integral_smul c _

/-- A direct construction, including when either measure is zero. -/
def integralOperator (k : Lp 𝕜 2 (μ.prod ν)) : Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 μ :=
  (integralLinearMap k).mkContinuous ‖k‖ (integralOutput_norm k)

lemma integralOperator_ae (k : Lp 𝕜 2 (μ.prod ν)) (u : Lp 𝕜 2 ν) :
    (integralOperator k u : X → 𝕜) =ᵐ[μ] fun x => ∫ y, k (x,y) * u y ∂ν :=
  integralOutput_ae k u

lemma canonical_eq_integralOperator (k : Lp 𝕜 2 (μ.prod ν)) :
    L2KernelSpec.OperatorValue μ ν k = integralOperator k := by
  have hex : ∃ K : Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 μ, ∀ u,
      (K u : X → 𝕜) =ᵐ[μ] fun x => ∫ y, k (x,y) * u y ∂ν :=
    ⟨integralOperator k, integralOperator_ae k⟩
  have h := Classical.epsilon_spec hex
  ext u
  exact (h u).trans (integralOperator_ae k u).symm

/-- The canonical bounded operator attached to an ordinary product L² class. -/
def kernelOperator : L2KernelSpec.OperatorType.{u,v} := L2KernelSpec.OperatorValue

theorem kernel_representative_formula : L2KernelSpec.RepresentativeFormula.{u,v} := by
  intro X Y 𝕜 _ _ _ μ ν _ _ k u hk hu
  rw [canonical_eq_integralOperator]
  exact (integralOperator_ae (hk.toLp k) (hu.toLp u)).trans
    (kernel_representative_independence μ ν _ _ _ _ hk.coeFn_toLp hu.coeFn_toLp)

theorem kernel_norm_bound : L2KernelSpec.NormBound.{u,v} := by
  intro X Y 𝕜 _ _ _ μ ν _ _ k
  rw [canonical_eq_integralOperator]
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg k) (integralOutput_norm k)

theorem kernel_output_measurability : L2KernelSpec.OutputMeasurability.{u,v} := by
  intro X Y 𝕜 _ _ _ μ ν _ _ k u hk hu
  have hm := integral_output_measurable k u hk hu
  exact ⟨hm, hm.mk _, hm.stronglyMeasurable_mk.measurable, hm.ae_eq_mk.symm⟩

end ExpandedFA.PartV.L2Kernel
