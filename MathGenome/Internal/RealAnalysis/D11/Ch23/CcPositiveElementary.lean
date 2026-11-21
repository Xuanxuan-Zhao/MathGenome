import MathGenome.Internal.RealAnalysis.D11.Ch19.PositiveFunctionalBound
import MathGenome.Internal.RealAnalysis.D11.Ch23.CompactDiniRiemannElementary
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.CcPositiveElementary

/-! The compact-support example in paper.tex:6314–6321.
Decrease to zero gives nonnegativity and one common compact support.
Dini on that support gives convergence in the uniform norm; the local bound
for a positive functional then gives order continuity. -/

universe u
open Filter Topology

namespace D11.Ch23

abbrev ccFunctions (X : Type u) [TopologicalSpace X] : Submodule ℝ (X → ℝ) :=
  Specs.ccFunctions X

abbrev ccFunctionsEquiv (X : Type u) [TopologicalSpace X] :
    D11.Ch19.Cc X ℝ ≃ₗ[ℝ] ccFunctions X := Specs.ccFunctionsEquiv X

/-- Closure under min, max, and truncation by one. -/
theorem ccFunctions_stone : Specs.CcFunctionsStone.{u} := by
  intro X _ _ _
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro f hf g hg
    exact ⟨hf.1.min hg.1, hf.2.inf hg.2⟩
  · intro f hf g hg
    exact ⟨hf.1.max hg.1, hf.2.sup hg.2⟩
  · intro f hf
    exact ⟨hf.1.min continuous_const,
      hf.2.comp_left (g := fun t : ℝ => min t 1) (min_eq_left zero_le_one)⟩

section OrderContinuity
variable {X : Type u} [TopologicalSpace X]
  (f : ℕ → D11.Ch19.Cc X ℝ)
  (hanti : ∀ x, Antitone (fun n => f n x))
  (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 0))

include hanti hlim

/-- All terms are nonnegative, even though this was not assumed separately. -/
lemma cc_decreasing_nonneg (n : ℕ) (x : X) : 0 ≤ f n x :=
  (hanti x).le_of_tendsto (hlim x) n

/-- Every closed support lies in the closed support of the first term. -/
lemma cc_decreasing_support (n : ℕ) : tsupport (f n) ⊆ tsupport (f 0) := by
  apply closure_mono
  intro x hx
  change f n x ≠ 0 at hx
  change f 0 x ≠ 0
  intro hz
  have hle := hanti x (Nat.zero_le n)
  have hnonneg := cc_decreasing_nonneg f hanti hlim n x
  exact hx (le_antisymm (hz ▸ hle) hnonneg)

variable [T2Space X]

/-- Dini on the common compact support gives global uniform convergence,
since every term vanishes outside that support. -/
lemma cc_decreasing_uniform :
    TendstoUniformly (fun n => (f n : X → ℝ)) (fun _ => 0) atTop := by
  let K : Set X := tsupport (f 0)
  have hK : IsCompact K := (f 0).hasCompactSupport
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hu : TendstoUniformly (fun n (x : K) => f n x) (fun _ => 0) atTop :=
    compact_dini _ (fun n => (f n).continuous.comp continuous_subtype_val)
      (fun n x => cc_decreasing_nonneg f hanti hlim n x)
      (fun x => hanti x) (fun x => hlim x)
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hu ε hε] with n hn
  intro x
  by_cases hx : x ∈ K
  · exact hn ⟨x, hx⟩
  · have hz : f n x = 0 := image_eq_zero_of_notMem_tsupport
      (fun hs => hx (cc_decreasing_support f hanti hlim n hs))
    simpa [hz] using hε

lemma cc_decreasing_norm :
    Tendsto (fun n => ‖(f n).toBoundedContinuousFunction‖) atTop (𝓝 0) := by
  have h : Tendsto (fun n => (f n).toBoundedContinuousFunction) atTop
      (𝓝 (0 : BoundedContinuousFunction X ℝ)) :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
      (cc_decreasing_uniform f hanti hlim)
  simpa only [norm_zero] using h.norm

end OrderContinuity

/-- Positivity alone gives the required sequential order continuity. -/
theorem cc_positive_orderContinuous : Specs.CcPositiveOrderContinuous.{u} := by
  intro X _ _ _ L hL f hanti hlim
  obtain ⟨C, _, hC⟩ := D11.Ch19.positive_functional_bound X L hL
    (tsupport (f 0)) (f 0).hasCompactSupport
  have hb : Tendsto (fun n => C * ‖(f n).toBoundedContinuousFunction‖)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (cc_decreasing_norm f hanti hlim).const_mul C
  apply squeeze_zero_norm _ hb
  intro n
  simpa only [Real.norm_eq_abs] using hC (f n) (cc_decreasing_support f hanti hlim n)

/-- Every positive functional on the canonical Cc subspace is elementary. -/
theorem cc_positive_elementary : Specs.CcPositiveElementary.{u} := by
  intro X _ _ _ L hL
  refine ⟨hL, ?_⟩
  intro f hanti hlim
  let e := ccFunctionsEquiv X
  let J : D11.Ch19.Cc X ℝ →ₗ[ℝ] ℝ := L.comp e.toLinearMap
  have hJ : ∀ g, (∀ x, 0 ≤ g x) → 0 ≤ J g := fun g hg => hL (e g) hg
  have h := cc_positive_orderContinuous J hJ (fun n => e.symm (f n)) hanti hlim
  simpa only [J, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    using h

end D11.Ch23
