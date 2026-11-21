import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.ExtendedFunctions
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.RelativeInteriorSegments
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.LocalLipschitz
import Mathlib.Analysis.Convex.Continuous

noncomputable section
open Set Topology Metric
universe u v
namespace VariationalNotes.ConvexAnalysis

private lemma finite_value {r : WithTop ℝ} (hr : r < ⊤) :
    r = ((r.untopD 0 : ℝ) : WithTop ℝ) := by
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hr)
  rw [← hs, WithTop.untopD_coe]

/-- Epigraph convexity applies to any finite upper heights. -/
lemma convex_upper_bound {E : Type u} [AddCommGroup E] [Module ℝ E]
    {f : E → WithTop ℝ} (hf : IsConvex f) {x y : E} {r s a b : ℝ}
    (hx : f x ≤ (r : WithTop ℝ)) (hy : f y ≤ (s : WithTop ℝ))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    f (a • x + b • y) ≤ ((a * r + b * s : ℝ) : WithTop ℝ) := by
  exact hf (show (x, r) ∈ Specs.epigraph f from hx)
    (show (y, s) ∈ Specs.epigraph f from hy) ha hb hab

lemma convex_effectiveDomain {E : Type u} [AddCommGroup E] [Module ℝ E]
    {f : E → WithTop ℝ} (hf : IsConvex f) : Convex ℝ (effectiveDomain f) := by
  intro x hx y hy a b ha hb hab
  have h := convex_upper_bound hf (finite_value hx).le (finite_value hy).le ha hb hab
  exact lt_of_le_of_lt h (WithTop.coe_lt_top _)

/-- On any convex set where an affine pullback is finite, it is a real convex function. -/
lemma convexOn_untopD_comp {E : Type u} {V : Type v}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup V] [Module ℝ V]
    {f : E → WithTop ℝ} (hf : IsConvex f) (p : V →ᵃ[ℝ] E)
    {C : Set V} (hC : Convex ℝ C) (hfin : ∀ x ∈ C, f (p x) < ⊤) :
    ConvexOn ℝ C (fun x => (f (p x)).untopD 0) := by
  refine ⟨hC, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := convex_upper_bound hf (finite_value (hfin x hx)).le
    (finite_value (hfin y hy)).le ha hb hab
  rw [← Convex.combo_affine_apply hab] at h
  exact WithTop.coe_le_coe.mp ((WithTop.coe_untopD_le _ _).trans h)

theorem localLipschitz_of_boundedAbove : Specs.localLipschitz_of_boundedAbove.{u} := by
  intro E _ _ f _ hf a hM
  obtain ⟨M, hM⟩ := hM
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hM
  have hfin : ∀ x ∈ Metric.ball a r, f x < ⊤ := fun x hx =>
    lt_of_le_of_lt (hball hx) (WithTop.coe_lt_top _)
  have hconv : ConvexOn ℝ (Metric.ball a r) (fun x => (f x).untopD 0) :=
    convexOn_untopD_comp hf (AffineMap.id ℝ E) (convex_ball a r) hfin
  have hbounded : (𝓝 a).IsBoundedUnder (· ≤ ·) (fun x => (f x).untopD 0) := by
    refine ⟨M, ?_⟩
    change ∀ᶠ x in 𝓝 a, (f x).untopD 0 ≤ M
    filter_upwards [hM] with x hx
    exact WithTop.coe_le_coe.mp ((WithTop.coe_untopD_le _ _).trans hx)
  have hloc : LocallyLipschitzOn (Metric.ball a r) (fun x => (f x).untopD 0) := by
    apply ((hconv.continuousOn_tfae isOpen_ball ⟨a, Metric.mem_ball_self hr⟩).out 4 1).mp
    exact ⟨a, Metric.mem_ball_self hr, hbounded⟩
  obtain ⟨K, U, hU, hLip⟩ := hloc (Metric.mem_ball_self hr)
  rw [isOpen_ball.nhdsWithin_eq (Metric.mem_ball_self hr)] at hU
  refine ⟨U ∩ Metric.ball a r, Filter.inter_mem hU (Metric.ball_mem_nhds a hr), K,
    fun x hx => hfin x hx.2, hLip.mono inter_subset_left⟩

/-- The direction-space chart is an isometry, so its local estimate uses
exactly the metric induced on the affine hull, with no dimension restriction. -/
theorem localLipschitz_relativeInterior : Specs.localLipschitz_relativeInterior.{u} := by
  intro E _ _ _ f _ hf a ha
  obtain ⟨aA, haA, hval⟩ := mem_intrinsicInterior.mp ha
  let A := affineSpan ℝ (Specs.effectiveDomain f)
  let : Nonempty A := ⟨aA⟩
  let e : A.direction ≃ᵃⁱ[ℝ] A := AffineIsometryEquiv.vaddConst ℝ aA
  let p : A.direction →ᵃ[ℝ] E := A.subtype.comp e.toAffineEquiv.toAffineMap
  let D : Set A := (Subtype.val : A → E) ⁻¹' Specs.effectiveDomain f
  let C : Set A.direction := p ⁻¹' Specs.effectiveDomain f
  have hC : Convex ℝ C := (convex_effectiveDomain hf).affine_preimage p
  have hconv : ConvexOn ℝ C (fun x => (f (p x)).untopD 0) :=
    convexOn_untopD_comp hf p hC (fun _ hx => hx)
  have hchart : e.symm aA ∈ interior C := by
    have hpre : e.symm aA ∈ e.toHomeomorph ⁻¹' interior D := by
      simpa only [mem_preimage, AffineIsometryEquiv.coe_toHomeomorph,
        AffineIsometryEquiv.apply_symm_apply] using haA
    rw [e.toHomeomorph.preimage_interior D] at hpre
    exact hpre
  obtain ⟨K, U, hU, hLip⟩ := hconv.locallyLipschitzOn_interior hchart
  rw [isOpen_interior.nhdsWithin_eq hchart] at hU
  have hV : U ∩ interior C ∈ 𝓝 (e.symm aA) :=
    Filter.inter_mem hU (isOpen_interior.mem_nhds hchart)
  refine ⟨aA, hval, e.symm ⁻¹' (U ∩ interior C),
    e.symm.continuous.continuousAt.preimage_mem_nhds hV, K, ?_, ?_⟩
  · intro x hx
    have hfin : f (p (e.symm x)) < ⊤ := (interior_subset : interior C ⊆ C) hx.2
    simpa only [p, AffineMap.comp_apply, AffineEquiv.coe_toAffineMap,
      AffineIsometryEquiv.coe_toAffineEquiv, AffineIsometryEquiv.apply_symm_apply,
      AffineSubspace.subtype_apply] using hfin
  · have h := hLip.comp e.symm.lipschitzWith.lipschitzOnWith
      (show MapsTo e.symm (e.symm ⁻¹' (U ∩ interior C)) U from fun _ hx => hx.1)
    simpa only [mul_one, Function.comp_def, p, AffineMap.comp_apply,
      AffineEquiv.coe_toAffineMap, AffineIsometryEquiv.coe_toAffineEquiv,
      AffineIsometryEquiv.apply_symm_apply, AffineSubspace.subtype_apply] using h

end VariationalNotes.ConvexAnalysis
