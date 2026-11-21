import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C10.MobiusNonorientability
import MathGenome.Internal.MultivariableAnalysis.D04.C10.MobiusEmbedding
import MathGenome.Internal.MultivariableAnalysis.D04.C10.PatchGeometryGram
import MathGenome.Internal.MultivariableAnalysis.D04.C10.SurfaceAssembly
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

noncomputable section
set_option autoImplicit false
open Set Topology
open scoped RealInnerProductSpace BigOperators
namespace D04.MobiusNonorientability
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C10.MobiusEmbedding.Model
open Specs.D04.C10.PatchGeometryGram.Model
open Specs.D04.C10.MobiusNonorientability.Model
open Specs.D04.C10.SurfaceAssembly.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C15.DirectedSubstitution.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model

/-- Explicit normalized cross product on the center, in the order φᵤ × φᵥ. -/
def centerNormal (u : ℝ) : E 3 := WithLp.toLp 2
  ![Real.sin (u / 2) * Real.cos u, Real.sin (u / 2) * Real.sin u, -Real.cos (u / 2)]

lemma centerNormal_norm (u : ℝ) : ‖centerNormal u‖ = 1 := by
  have h0 := Real.sin_sq_add_cos_sq u
  have h1 := Real.sin_sq_add_cos_sq (u / 2)
  have hn : ‖centerNormal u‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [centerNormal, Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg (Real.sin (u / 2))]
  nlinarith [norm_nonneg (centerNormal u)]

lemma center_cross (R u : ℝ) :
    cross (du R (centerParameter u)) (dv (centerParameter u)) = R • centerNormal u := by
  ext i
  fin_cases i <;>
    simp [cross, du, dv, radius, centerParameter, centerNormal, crossProduct,
      Fin.sum_univ_succ] <;> try ring
  linear_combination -(R * Real.cos (u * (1 / 2))) * (Real.sin_sq_add_cos_sq u)

lemma center_unitNormal {R : ℝ} (hR : 0 < R) (u : ℝ) :
    unitNormal (phi R) (centerParameter u) = centerNormal u := by
  have hc := D04.MobiusEmbedding.derivative_columns R (centerParameter u)
  change ‖cross (fderiv ℝ (phi R) (centerParameter u) (D04.standardBasis 2 0))
    (fderiv ℝ (phi R) (centerParameter u) (D04.standardBasis 2 1))‖⁻¹ •
    cross (fderiv ℝ (phi R) (centerParameter u) (D04.standardBasis 2 0))
      (fderiv ℝ (phi R) (centerParameter u) (D04.standardBasis 2 1)) = _
  rw [hc.1, hc.2, center_cross, norm_smul, Real.norm_eq_abs,
    abs_of_pos hR, centerNormal_norm, mul_one, smul_smul, inv_mul_cancel₀ hR.ne']
  exact one_smul _ _

theorem center_normal : Specs.D04.C10.MobiusNonorientability.center_normalType := by
  intro R hR u
  exact center_unitNormal hR u

theorem normal_flip : Specs.D04.C10.MobiusNonorientability.normal_flipType := by
  intro R hR
  rw [center_unitNormal hR, center_unitNormal hR]
  ext i
  fin_cases i <;> simp [centerNormal]

lemma centerNormal_continuous : Continuous centerNormal := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp [centerNormal] <;> fun_prop

lemma center_choices {R : ℝ} (hR : 0 < R) (u : ℝ) (v : E 3) :
    IsUnitNormal (tangentPlane (phi R) (centerParameter u)) v ↔
      v = centerNormal u ∨ v = -centerNormal u := by
  have hi := D04.MobiusEmbedding.derivative_injective hR
    (p := centerParameter u) (by simp [centerParameter])
  have h := D04.PatchGeometryGram.normal_choices_linear
    (fderiv ℝ (phi R) (centerParameter u)).toLinearMap hi v
  change IsUnitNormal (tangentPlane (phi R) (centerParameter u)) v ↔ v = unitNormal (phi R) (centerParameter u) ∨
    v = -unitNormal (phi R) (centerParameter u) at h
  rw [center_unitNormal hR] at h
  exact h

/-- A continuous real function on a connected set cannot switch between ±1. -/
lemma constant_of_pm_one {S : Set ℝ} (hS : IsPreconnected S) {s : ℝ → ℝ}
    (hc : ContinuousOn s S) (hs : ∀ x ∈ S, s x = 1 ∨ s x = -1)
    {a : ℝ} (ha : a ∈ S) : ∀ x ∈ S, s x = s a := by
  intro x hx
  rcases hs a ha with ha' | ha' <;> rcases hs x hx with hx' | hx'
  · rw [ha', hx']
  · obtain ⟨z, hz, hzero⟩ := hS.intermediate_value hx ha hc
      (show (0 : ℝ) ∈ Icc (s x) (s a) by rw [ha', hx']; constructor <;> norm_num)
    rcases hs z hz with h | h <;> linarith
  · obtain ⟨z, hz, hzero⟩ := hS.intermediate_value ha hx hc
      (show (0 : ℝ) ∈ Icc (s a) (s x) by rw [ha', hx']; constructor <;> norm_num)
    rcases hs z hz with h | h <;> linarith
  · rw [ha', hx']

theorem center_constant_sign :
    Specs.D04.C10.MobiusNonorientability.center_constant_signType := by
  intro R hR v hv hn
  let s : ℝ → ℝ := fun u => ⟪v u, centerNormal u⟫
  have hs : ∀ u ∈ Icc 0 (2 * Real.pi), s u = 1 ∨ s u = -1 := by
    intro u hu
    rcases (center_choices hR u (v u)).mp (hn u hu) with he | he
    · left
      simp [s, he, real_inner_self_eq_norm_sq, centerNormal_norm]
    · right
      simp [s, he, real_inner_self_eq_norm_sq, centerNormal_norm]
  have hc : ContinuousOn s (Icc 0 (2 * Real.pi)) :=
    hv.inner centerNormal_continuous.continuousOn
  have h0 : (0 : ℝ) ∈ Icc 0 (2 * Real.pi) := ⟨le_rfl, by positivity⟩
  have hconst := constant_of_pm_one isPreconnected_Icc hc hs h0
  rcases hs 0 h0 with h | h
  · left
    intro u hu
    rw [center_unitNormal hR]
    rcases (center_choices hR u (v u)).mp (hn u hu) with he | he
    · exact he
    · have : s u = -1 := by
        simp [s, he, real_inner_self_eq_norm_sq, centerNormal_norm]
      have hh := hconst u hu
      rw [h] at hh
      linarith
  · right
    intro u hu
    rw [center_unitNormal hR]
    rcases (center_choices hR u (v u)).mp (hn u hu) with he | he
    · have : s u = 1 := by
        simp [s, he, real_inner_self_eq_norm_sq, centerNormal_norm]
      have hh := hconst u hu
      rw [h] at hh
      linarith
    · exact he

/-- On the center the prescribed local chart is a translation, so its derivative
range is exactly the original parameter plane, including at the seam. -/
lemma center_tangent {R a u : ℝ} (ha : 0 < a) (haR : a < R)
    (hu : u ∈ Icc 0 (2 * Real.pi)) :
    tangentSpace 1 2 (strip R a) (phi R (centerParameter u)) =
      tangentPlane (phi R) (centerParameter u) := by
  have hp : centerParameter u ∈ rectangle a :=
    ⟨hu.1, hu.2, by simpa [centerParameter] using ha.le⟩
  obtain ⟨c, hc, _, hcz, W, hW, h0W, he⟩ :=
    D04.MobiusEmbedding.local_charts R a ha haR _ hp
  have hβ : parameterChart a (centerParameter u) =
      fun x => centerParameter u + x := by
    funext x
    ext i
    fin_cases i <;> simp [parameterChart, centerParameter, ne_of_lt ha]
  rw [hβ] at he
  have ht : HasFDerivAt (fun x : E 2 => centerParameter u + x)
      (ContinuousLinearMap.id ℝ (E 2)) 0 :=
    (hasFDerivAt_id (0 : E 2)).const_add (centerParameter u)
  have hd : HasFDerivAt (phi R ∘ fun x => centerParameter u + x)
      (fderiv ℝ (phi R) (centerParameter u)) 0 := by
    have hpD := D04.MobiusEmbedding.hasFDerivAt_phi R (centerParameter u)
    have hpD' : HasFDerivAt (phi R) (fderiv ℝ (phi R) (centerParameter u))
        (centerParameter u + (0 : E 2)) := by simpa [hpD.fderiv] using hpD
    simpa using hpD'.comp 0 ht
  have hdiff := D04.EmbeddedChart.differential_extension c hc.1 hW h0W
    (fun x hx => (he hx.2).symm) hd.differentiableAt
  rw [hd.fderiv] at hdiff
  change Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential c 0 =
    fderiv ℝ (phi R) (centerParameter u) at hdiff
  change Specs.D04.C14.ChartIndependentTangentSpaces.Model.tangentSpace
    1 2 (strip R a) (phi R (centerParameter u)) = _
  rw [← hcz, D04.tangentSpace_chart c ⟨le_rfl, by norm_num⟩ (by omega) 0 hc.1,
    hdiff]
  rfl

theorem nonorientable : Specs.D04.C10.MobiusNonorientability.nonorientableType := by
  intro R a ha haR
  refine ⟨fun N => ?_⟩
  let γ : Icc (0 : ℝ) (2 * Real.pi) → strip R a := fun u =>
    ⟨phi R (centerParameter u), centerParameter u,
      ⟨u.property.1, u.property.2, by simpa [centerParameter] using ha.le⟩, rfl⟩
  have hγ : Continuous γ := by
    apply Continuous.subtype_mk
    exact (D04.MobiusEmbedding.smooth R).continuous.comp
      ((PiLp.continuous_toLp 2 _).comp (continuous_pi (by
        intro i
        fin_cases i <;> simp [centerParameter] <;> fun_prop)))
  let v : ℝ → E 3 := fun u =>
    if hu : u ∈ Icc 0 (2 * Real.pi) then N.toFun (γ ⟨u, hu⟩) else 0
  have hvγ : ∀ u : Icc (0 : ℝ) (2 * Real.pi), v u = N.toFun (γ u) := by
    intro u
    dsimp only [v]
    rw [dite_eq_left u.property]
  have hv : ContinuousOn v (Icc 0 (2 * Real.pi)) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun u : Icc (0 : ℝ) (2 * Real.pi) => v u)
    have he : (fun u : Icc (0 : ℝ) (2 * Real.pi) => v u) = N.toFun ∘ γ :=
      funext hvγ
    rw [he]
    exact N.continuous.comp hγ
  have hn : ∀ u ∈ Icc 0 (2 * Real.pi),
      IsUnitNormal (tangentPlane (phi R) (centerParameter u)) (v u) := by
    intro u hu
    rw [← center_tangent ha haR hu, hvγ ⟨u, hu⟩]
    exact N.normal (γ ⟨u, hu⟩)
  have h0 : (0 : ℝ) ∈ Icc 0 (2 * Real.pi) := ⟨le_rfl, by positivity⟩
  have h2 : 2 * Real.pi ∈ Icc (0 : ℝ) (2 * Real.pi) := ⟨by positivity, le_rfl⟩
  have hseam : γ ⟨0, h0⟩ = γ ⟨2 * Real.pi, h2⟩ := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [γ, phi, radius, centerParameter]
  have hvseam : v 0 = v (2 * Real.pi) := by
    rw [hvγ ⟨0, h0⟩, hvγ ⟨2 * Real.pi, h2⟩, hseam]
  rcases center_constant_sign R (ha.trans haR) v hv hn with h | h
  · rw [h 0 h0, h _ h2, normal_flip R (ha.trans haR)] at hvseam
    have hz := congrArg (fun x : E 3 => x 2) hvseam
    rw [center_unitNormal (ha.trans haR)] at hz
    norm_num [centerNormal] at hz
  · rw [h 0 h0, h _ h2, normal_flip R (ha.trans haR)] at hvseam
    have hz := congrArg (fun x : E 3 => x 2) hvseam
    rw [center_unitNormal (ha.trans haR)] at hz
    norm_num [centerNormal] at hz

theorem scalar_integration : Specs.D04.C10.MobiusNonorientability.scalar_integrationType := by
  intro R a ha haR
  have hM := (D04.MobiusEmbedding.embedded_manifold R a ha haR).1
  have hcompact := D04.MobiusEmbedding.compact R a ha haR
  refine ⟨fun c u => D04MetricDensity.chartDensity_positive c hM.1 u u.property, ?_⟩
  intro f hf
  obtain ⟨P, hP, _⟩ := D04SurfaceAssembly.scalar_construction hM hcompact f hf
  exact ⟨⟨P, hP, D04SurfaceAssembly.scalar_chart_formula hM hcompact f hf P Subset.rfl⟩,
    fun P hs => D04SurfaceAssembly.scalar_chart_formula hM hcompact f hf P hs⟩

end D04.MobiusNonorientability
