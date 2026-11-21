import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.ContinuousKernel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.Ascoli
import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
The canonical continuous-kernel operator. Currying the flipped kernel gives a
continuous map Y → C(X). Its product with a continuous input is Bochner
integrable in C(X); evaluation commutes with integration. This constructs the
continuous output without a countability assumption on X.

The pointwise integral estimate gives the sharp stated upper bound. Continuity
of k.curry supplies one continuity modulus for the whole image of the unit
ball, and the accepted compact-Hausdorff Ascoli theorem proves compactness.
No product measure or product measurability assertion is used.
-/

open MeasureTheory Filter
open scoped Topology
universe u v w
namespace ExpandedFA.PartV.ContinuousKernel

noncomputable def kernelIntegral : Spec.KernelIntegralType :=
  fun _ _ _ _ _ _ _ ν k u x => ∫ y, k (x, y) * u y ∂ν

section Construction
variable {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
  [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
  [MeasurableSpace Y] [BorelSpace Y]
  (ν : Measure Y) [IsFiniteMeasure ν] (k : C(X × Y, 𝕜))

/-- The continuous family of sections of the flipped kernel. -/
abbrev kernelSection : C(Y, C(X, 𝕜)) := Spec.kernelSection k

omit [T2Space X] [T2Space Y] in
lemma kernel_section_integrable (u : C(Y, 𝕜)) :
    Integrable (fun y => u y • kernelSection k y) ν :=
  Spec.kernel_section_integrable ν k u

/-- The integral in the Banach space C(X). -/
noncomputable abbrev kernelImage (u : C(Y, 𝕜)) : C(X, 𝕜) := Spec.kernelImage ν k u

omit [T2Space X] [T2Space Y] in
lemma kernelImage_apply (u : C(Y, 𝕜)) (x : X) :
    kernelImage ν k u x = kernelIntegral 𝕜 X Y ν k u x :=
  Spec.kernelImage_apply ν k u x

omit [CompactSpace X] [T2Space X] [T2Space Y] in
lemma kernel_integrable_section (u : C(Y, 𝕜)) (x : X) :
    Integrable (fun y => k (x, y) * u y) ν :=
  Spec.kernel_integrable_section ν k u x

end Construction

/-- The canonical operator, shared with the independent downstream interfaces. -/
noncomputable def kernelOperator : Spec.KernelOperatorType.{u, v, w} :=
  @Spec.KernelOperatorValue

section Construction
variable {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
  [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
  [MeasurableSpace Y] [BorelSpace Y]
  (ν : Measure Y) [IsFiniteMeasure ν] (k : C(X × Y, 𝕜))

lemma kernelOperator_apply (u : C(Y, 𝕜)) (x : X) :
    kernelOperator ν k u x = kernelIntegral 𝕜 X Y ν k u x :=
  Spec.KernelOperatorValue_apply ν k u x

lemma kernelOperator_norm_le : ‖kernelOperator ν k‖ ≤ ν.real Set.univ * ‖k‖ :=
  Spec.KernelOperatorValue_norm_le ν k

end Construction

theorem continuous_kernel_integrability : Spec.Integrability.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ _ _ ν _ k u x
  exact kernel_integrable_section ν k u x

theorem continuous_kernel_output_continuous : Spec.OutputContinuity.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ _ _ ν _ k u
  have h : Spec.KernelIntegralValue 𝕜 X Y ν k u = kernelImage ν k u :=
    funext fun x => (kernelImage_apply ν k u x).symm
  rw [h]
  exact (kernelImage ν k u).continuous

theorem continuous_kernel_bounded_operator : Spec.BoundedOperator.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ _ _ ν _ k
  refine ⟨kernelOperator ν k, ⟨kernelOperator_apply ν k, kernelOperator_norm_le ν k⟩, ?_⟩
  intro T hT
  ext u x
  exact (hT.1 u x).trans (kernelOperator_apply ν k u x).symm

theorem continuous_kernel_zero_cases : Spec.ZeroCases.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ _ _ ν _ k T hT hz
  rcases hz with hν | hx | hy
  · ext u x
    rw [hT]
    simp [Spec.KernelIntegralValue, hν]
  · have := hx
    ext u x
    exact isEmptyElim x
  · have := hy
    ext u x
    rw [hT]
    have hν : ν = 0 := Subsingleton.elim _ _
    simp [Spec.KernelIntegralValue, hν]

section
variable {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜] [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
  [MeasurableSpace Y] [BorelSpace Y]
  (ν : Measure Y) [IsFiniteMeasure ν] (k : C(X × Y, 𝕜))

/-- The oscillation estimate uses continuity of `k.curry : C(X, C(Y, 𝕜))`,
which is uniform in the integration variable without metrizing X or Y. -/
lemma kernelOperator_dist_le (u : C(Y, 𝕜)) (x x' : X) :
    dist (kernelOperator ν k u x) (kernelOperator ν k u x') ≤
      ν.real Set.univ * ‖u‖ * dist (k.curry x) (k.curry x') := by
  rw [dist_eq_norm, kernelOperator_apply, kernelOperator_apply]
  change ‖(∫ y, k (x, y) * u y ∂ν) - ∫ y, k (x', y) * u y ∂ν‖ ≤ _
  rw [← integral_sub (kernel_integrable_section ν k u x)
    (kernel_integrable_section ν k u x')]
  calc
    ‖∫ y, k (x, y) * u y - k (x', y) * u y ∂ν‖ ≤
        (‖k.curry x - k.curry x'‖ * ‖u‖) * ν.real Set.univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards with y
      rw [← sub_mul, norm_mul]
      exact mul_le_mul ((k.curry x - k.curry x').norm_coe_le_norm y)
        (u.norm_coe_le_norm y) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by rw [dist_eq_norm]; ring

/-- The image of the closed unit ball is equicontinuous in the given topology. -/
lemma kernelOperator_unitBall_equicontinuous :
    Equicontinuous (fun f : kernelOperator ν k '' Metric.closedBall 0 1 =>
      ((f : C(X, 𝕜)) : X → 𝕜)) := by
  intro x₀
  apply Metric.equicontinuousAt_of_continuity_modulus
    (fun x => ν.real Set.univ * dist (k.curry x₀) (k.curry x))
  · have h : Continuous (fun x => ν.real Set.univ * dist (k.curry x₀) (k.curry x)) :=
      continuous_const.mul (continuous_const.dist k.curry.continuous)
    simpa using (h.continuousAt (x := x₀)).tendsto
  · filter_upwards with x f
    obtain ⟨u, hu, huf⟩ := f.property
    have hu' : ‖u‖ ≤ 1 := by simpa using hu
    change dist ((f : C(X, 𝕜)) x₀) ((f : C(X, 𝕜)) x) ≤ _
    rw [← huf]
    exact (kernelOperator_dist_le ν k u x₀ x).trans (by
      calc
        _ ≤ ν.real Set.univ * 1 * dist (k.curry x₀) (k.curry x) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hu' measureReal_nonneg) dist_nonneg
        _ = _ := by rw [mul_one])

/-- Arzelà–Ascoli applies in the canonical compact-open topology, which on
compact X is exactly the supremum-norm topology. The common bound and
equicontinuity of the unit-ball image are exactly the accepted Ascoli hypotheses. -/
theorem kernelOperator_isCompact : IsCompactOperator (kernelOperator ν k) := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall _ zero_lt_one).mpr
  apply (ExpandedFA.PartV.Ascoli.arzela_ascoli 𝕜 X
    (kernelOperator ν k '' Metric.closedBall 0 1)).mpr
  refine ⟨?_, kernelOperator_unitBall_equicontinuous ν k⟩
  refine ⟨‖kernelOperator ν k‖, norm_nonneg _, ?_⟩
  rintro f ⟨u, hu, rfl⟩ x
  have hu' : ‖u‖ ≤ 1 := by simpa using hu
  exact ((kernelOperator ν k u).norm_coe_le_norm x).trans
    (((kernelOperator ν k).le_opNorm u).trans (by
      simpa using mul_le_mul_of_nonneg_left hu' (norm_nonneg (kernelOperator ν k))))

end

theorem continuous_kernel_compact_images : Spec.CompactImages.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ _ _ ν _ k T hT S hS
  have h : T = kernelOperator ν k := by
    ext u x
    exact (hT u x).trans (kernelOperator_apply ν k u x).symm
  rw [h]
  exact (kernelOperator_isCompact ν k).isCompact_closure_image_of_bounded hS

theorem continuous_kernel_theorem : Spec.FullTheorem.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ _ _ ν _ k
  refine ⟨kernelOperator ν k, ?_, ?_⟩
  · exact ⟨kernelOperator_apply ν k, kernelOperator_norm_le ν k,
      kernelOperator_isCompact ν k,
      fun S hS => (kernelOperator_isCompact ν k).isCompact_closure_image_of_bounded hS⟩
  · intro T hT
    ext u x
    exact (hT.1 u x).trans (kernelOperator_apply ν k u x).symm

/-- The defining integral, bound, and compactness of the canonical operator. -/
theorem canonical_operator_properties : Spec.CanonicalOperatorProperties.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ _ _ ν _ k
  exact ⟨fun u x => ⟨kernel_integrable_section ν k u x, kernelOperator_apply ν k u x⟩,
    kernelOperator_norm_le ν k, kernelOperator_isCompact ν k,
    fun S hS => (kernelOperator_isCompact ν k).isCompact_closure_image_of_bounded hS⟩

end ExpandedFA.PartV.ContinuousKernel
