import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.ContinuousL2Bridge
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.ContinuousKernel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.L2Kernel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.PositiveRadonRepresentation
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Tactic.Ring

/-! The two canonical kernel constructions commute with the continuous-to-L²
quotient maps. Product measurability follows from Mathlib's approximation by
simple functions on measurable open rectangles; the product Borel equality
is never assumed. Regularity and Urysohn approximation give density. -/

open MeasureTheory Filter
open scoped ENNReal
universe u v
noncomputable section
namespace ExpandedFA.PartV.ContinuousL2Bridge

theorem continuous_to_l2_inclusion : Spec.InclusionCorrect.{u} := by
  intro X 𝕜 _ _ _ _ _ _ μ _
  refine ⟨fun f => ContinuousMap.coeFn_toLp μ f, ?_⟩
  have h := ContinuousMap.toLp_norm_le (p := (2 : ℝ≥0∞)) (E := 𝕜) (𝕜 := 𝕜) μ
  have hm : (measureUnivNNReal μ : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ =
      Real.sqrt (μ.real Set.univ) := by
    change (μ.real Set.univ) ^ (2 : ℝ≥0∞).toReal⁻¹ = _
    norm_num [Real.sqrt_eq_rpow]
  rwa [hm] at h

theorem continuous_l2_dense : Spec.ContinuousDensity.{u} := by
  intro X 𝕜 _ _ _ _ _ _ μ _ hμ
  let : μ.Regular :=
    (ExpandedFA.FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular μ).mp hμ
  exact ContinuousMap.toLp_denseRange 𝕜 μ 𝕜 (by norm_num)

theorem continuous_product_l2 : Spec.ProductL2.{u,v} := by
  intro X Y 𝕜 _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ k
  let : MeasurableSpace 𝕜 := borel 𝕜
  let : BorelSpace 𝕜 := ⟨rfl⟩
  have hm : Measurable (fun z : X × Y => k z) :=
    (HasCompactSupport.of_compactSpace (fun z => k z)).measurable_of_prod k.continuous
  have hk : MemLp (fun z => k z) 2 (μ.prod ν) :=
    MemLp.of_bound hm.aestronglyMeasurable ‖k‖
      (Eventually.of_forall k.norm_coe_le_norm)
  refine ⟨hm, hk, ?_⟩
  have hb := Lp.norm_le_of_ae_bound (f := hk.toLp (fun z => k z)) (norm_nonneg k)
    (hk.coeFn_toLp.mono fun z hz => by rw [hz]; exact k.norm_coe_le_norm z)
  have hmass : (measureUnivNNReal (μ.prod ν) : ℝ) =
      μ.real Set.univ * ν.real Set.univ := by
    change (μ.prod ν).real Set.univ = _
    rw [← Set.univ_prod_univ, measureReal_prod_prod]
  have hfactor : (measureUnivNNReal (μ.prod ν) : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ =
      Real.sqrt (μ.real Set.univ) * Real.sqrt (ν.real Set.univ) := by
    rw [hmass, Real.mul_rpow measureReal_nonneg measureReal_nonneg]
    norm_num [Real.sqrt_eq_rpow]
  rw [hfactor] at hb
  exact hb.trans_eq (by ring)

theorem continuous_l2_operator_agreement : Spec.OperatorAgreement.{u,v} := by
  intro X Y 𝕜 _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ k hk
  apply ContinuousLinearMap.ext
  intro f
  have hf : MemLp (fun y => f y) 2 ν :=
    MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖
      (Eventually.of_forall f.norm_coe_le_norm)
  have hf' : hf.toLp (fun y => f y) = ContinuousMap.toLp 2 ν 𝕜 f := by
    apply Lp.ext
    exact hf.coeFn_toLp.trans (ContinuousMap.coeFn_toLp ν f).symm
  apply Lp.ext
  have hform := L2Kernel.kernel_representative_formula μ ν (fun z => k z)
    (fun y => f y) hk hf
  rw [hf'] at hform
  filter_upwards [hform, ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (𝕜 := 𝕜) μ
    (ContinuousKernel.Spec.KernelOperatorValue ν k f)] with x hx hy
  change L2KernelSpec.OperatorValue μ ν (hk.toLp _) (ContinuousMap.toLp 2 ν 𝕜 f) x =
    ContinuousMap.toLp 2 μ 𝕜 (ContinuousKernel.Spec.KernelOperatorValue ν k f) x
  rw [hx, hy, ContinuousKernel.Spec.KernelOperatorValue_apply]
  rfl

theorem continuous_l2_unique_extension : Spec.UniqueExtension.{u,v} := by
  intro X Y 𝕜 _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ hν k hk T
  have hagree := continuous_l2_operator_agreement μ ν k hk
  constructor
  · intro hT
    apply DFunLike.coe_injective
    apply (continuous_l2_dense (𝕜 := 𝕜) ν hν).equalizer T.continuous
      (L2KernelSpec.OperatorValue μ ν (hk.toLp (fun z => k z))).continuous
    funext f
    exact (hT f).trans (congrArg (fun A : C(Y, 𝕜) →L[𝕜] Lp 𝕜 2 μ => A f) hagree).symm
  · rintro rfl f
    exact congrArg (fun A : C(Y, 𝕜) →L[𝕜] Lp 𝕜 2 μ => A f) hagree

end ExpandedFA.PartV.ContinuousL2Bridge
