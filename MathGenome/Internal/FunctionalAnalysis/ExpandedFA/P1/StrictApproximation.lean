import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.StrictApproximation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.RotundDefinitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05Norming
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14Minimization
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Topology.Order.WithTop
import Mathlib.Tactic.Module

namespace ExpandedFA.P1.StrictApproximation
universe u v
open Set Metric
noncomputable section

/-- Supporting hyperplanes use real parts of scalar-linear functionals,
which represent all continuous real functionals isometrically. -/
theorem hyperplane_representation : Spec.HyperplaneRepresentation.{u,v} := by
  intro 𝕜 E _ _ _
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  intro g
  refine ⟨StrongDual.extendRCLike (𝕜 := 𝕜) g, ?_, StrongDual.norm_extendRCLike g, ?_⟩
  · intro z
    exact StrongDual.re_extendRCLike_apply g z
  · exact (StrongDual.extendRCLikeₗ (𝕜 := 𝕜)).map_eq_zero_iff

/-- Strict convexity is exactly the positive-ray equality case of the triangle inequality. -/
theorem rotund_iff_triangle_equality : Spec.TriangleCharacterization.{u,v} := by
  intro 𝕜 E _ _ _
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  rw [show RotundDefinitions.Spec.RotundValue 𝕜 E ↔ StrictConvexSpace ℝ E from
    RotundDefinitions.rotund_iff_strictConvexSpace 𝕜 E]
  constructor
  · intro h
    letI := h
    intro x y hx hy heq
    obtain ⟨r, hr, hxy⟩ := (sameRay_iff_norm_add.mpr heq).exists_pos_left hx hy
    exact ⟨r, hr, hxy.symm⟩
  · intro h
    apply StrictConvexSpace.of_norm_add
    intro x y hx hy heq
    obtain ⟨r, hr, hxy⟩ := h x y (by intro hz; simp [hz] at hx)
      (by intro hz; simp [hz] at hy) (by simpa only [hx, hy, one_add_one_eq_two] using heq)
    rw [hxy]
    exact SameRay.sameRay_pos_smul_right x hr

lemma nearest_point_unique {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [StrictConvexSpace ℝ E] {C : Set E} (hC : Convex ℝ C)
    (x z w : E) (hz : Spec.IsNearestPoint E C x z)
    (hw : Spec.IsNearestPoint E C x w) : z = w := by
  by_contra hne
  have heq : ‖x - w‖ = ‖x - z‖ := le_antisymm (hw.2 z hz.1) (hz.2 w hw.1)
  have hzw : x - z ≠ x - w := by
    intro h
    exact hne (sub_right_injective h)
  have hstrict := norm_combo_lt_of_ne (le_refl ‖x - z‖) heq.le hzw
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hmid : (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w ∈ C :=
    hC hz.1 hw.1 (by norm_num) (by norm_num) (by norm_num)
  have hid : (1 / 2 : ℝ) • (x - z) + (1 / 2 : ℝ) • (x - w) =
      x - ((1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w) := by module
  rw [hid] at hstrict
  exact (not_lt_of_ge (hz.2 _ hmid)) hstrict

/-- A norm-one functional for a norm-two sum exposes both unit endpoints. -/
private lemma exposing_functional (𝕜 : Type u) {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {x y : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : ‖x + y‖ = 2) :
    ∃ f : E →L[𝕜] 𝕜, ‖f‖ = 1 ∧ RCLike.re (f x) = 1 ∧ RCLike.re (f y) = 1 := by
  obtain ⟨f, hf, hfs⟩ := C05Norming.norming_functional_nonzero 𝕜 E (x + y)
    (by intro h; simp [h] at hxy)
  have hfx : RCLike.re (f x) ≤ 1 :=
    (RCLike.re_le_norm _).trans (by simpa [hf, hx] using f.le_opNorm x)
  have hfy : RCLike.re (f y) ≤ 1 :=
    (RCLike.re_le_norm _).trans (by simpa [hf, hy] using f.le_opNorm y)
  have hsum : RCLike.re (f x) + RCLike.re (f y) = 2 := by
    have := congrArg RCLike.re hfs
    simpa [map_add, hxy] using this
  exact ⟨f, hf, by linarith, by linarith⟩

/-- Uniqueness holds for every convex set, without any existence assumption. -/
theorem rotund_iff_nearest_unique : Spec.NearestCharacterization.{u,v} := by
  intro 𝕜 E _ _ _
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  constructor
  · intro h
    letI : StrictConvexSpace ℝ E :=
      (RotundDefinitions.rotund_iff_strictConvexSpace 𝕜 E).mp h
    intro C hC x z w hz hw
    exact nearest_point_unique hC x z w hz hw
  · intro h
    apply (RotundDefinitions.rotund_iff_strictConvexSpace 𝕜 E).mpr
    apply StrictConvexSpace.of_norm_add_ne_two
    intro x y hx hy hne hxy
    obtain ⟨f, hf, hfx, hfy⟩ := exposing_functional 𝕜 hx hy hxy
    let g : E →L[ℝ] ℝ := RCLike.reCLM.comp (f.restrictScalars ℝ)
    let C : Set E := {z | g z = 1}
    have hC : Convex ℝ C := (convex_singleton (1 : ℝ)).linear_preimage g.toLinearMap
    have hmin (z : E) (hz : ‖z‖ = 1) (hfz : g z = 1) :
        Spec.IsNearestPoint E C 0 z := by
      refine ⟨hfz, ?_⟩
      intro w hw
      simp only [zero_sub, norm_neg, hz]
      calc
        1 = RCLike.re (f w) := hw.symm
        _ ≤ ‖f w‖ := RCLike.re_le_norm _
        _ ≤ ‖w‖ := by simpa [hf] using f.le_opNorm w
    exact hne (h C hC 0 x y (hmin x hx hfx) (hmin y hy hfy))

private lemma real_support_bound {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E →L[ℝ] ℝ) (a : ℝ) (h : ∀ z : E, ‖z‖ ≤ 1 → g z ≤ a) : ‖g‖ ≤ a := by
  have hb : ∀ z ∈ closedBall (0 : E) 1, ‖g z‖ ≤ a := by
    intro z hz
    have hz' : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
    have hp := h z hz'
    have hn := h (-z) (by simpa using hz')
    simp only [map_neg] at hn
    simpa only [map_neg, Real.norm_eq_abs, abs_le] using And.intro (by linarith : -a ≤ g z) hp
  simpa using g.opNorm_bound_of_ball_bound (by norm_num : (0 : ℝ) < 1) a hb

/-- All supporting hyperplanes, at arbitrary levels and without normalization. -/
theorem rotund_iff_supporting_hyperplanes_unique : Spec.SupportingCharacterization.{u,v} := by
  intro 𝕜 E _ _ _
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  constructor
  · intro h f a hs x y hx hy hfx hfy
    letI : StrictConvexSpace ℝ E :=
      (RotundDefinitions.rotund_iff_strictConvexSpace 𝕜 E).mp h
    let g : E →L[ℝ] ℝ := RCLike.reCLM.comp (f.restrictScalars ℝ)
    have hg : g ≠ 0 := by
      change (StrongDual.extendRCLikeₗ (𝕜 := 𝕜)).symm f ≠ 0
      exact fun heq => hs.1 ((StrongDual.extendRCLikeₗ (𝕜 := 𝕜)).symm.map_eq_zero_iff.mp heq)
    have hga : ‖g‖ ≤ a := real_support_bound g a hs.2.1
    by_contra hne
    have hlt := norm_combo_lt_of_ne hx.le hy.le hne
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    let m := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y
    have hgm : g m = a := by
      change g ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) = a
      simp only [map_add, map_smul, smul_eq_mul]
      change 1 / 2 * RCLike.re (f x) + 1 / 2 * RCLike.re (f y) = a
      rw [hfx, hfy]
      ring
    have hpos : 0 < ‖g‖ := norm_pos_iff.mpr hg
    have hle : a ≤ ‖g‖ * ‖m‖ := by
      calc
        a = g m := hgm.symm
        _ ≤ ‖g m‖ := le_abs_self _
        _ ≤ ‖g‖ * ‖m‖ := g.le_opNorm m
    have : ‖g‖ * ‖m‖ < ‖g‖ := by nlinarith
    linarith
  · intro h
    apply (RotundDefinitions.rotund_iff_strictConvexSpace 𝕜 E).mpr
    apply StrictConvexSpace.of_norm_add_ne_two
    intro x y hx hy hne hxy
    obtain ⟨f, hf, hfx, hfy⟩ := exposing_functional 𝕜 hx hy hxy
    have hs : Spec.SupportsUnitBall 𝕜 E f 1 := by
      refine ⟨?_, ?_, x, hx.le, hfx⟩
      · intro hz
        simp [hz] at hf
      · intro z hz
        exact (RCLike.re_le_norm _).trans (by simpa [hf] using f.le_opNorm_of_le hz)
    exact hne (h f 1 hs x y hx hy hfx hfy)

/-- Reflexive existence uses the accepted convex direct method on distance.
Its sublevels are bounded even if the convex domain is unbounded. -/
lemma reflexive_best_approximation
    (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (hE : C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E) :
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    ∀ (C : Set E), C.Nonempty → IsClosed C → Convex ℝ C → ∀ x : E,
      ∃ z : E, Spec.IsNearestPoint E C x z := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  intro C hCne hCclosed hCconv x
  let Φ : E → WithTop ℝ := fun z => (dist z x : WithTop ℝ)
  have hconv : Convex ℝ {p : E × ℝ | Φ p.1 ≤ (p.2 : WithTop ℝ)} := by
    simpa [Φ] using (convexOn_univ_dist x).convex_epigraph
  have hlsc : LowerSemicontinuous Φ :=
    (WithTop.continuous_coe.comp (continuous_id.dist continuous_const)).lowerSemicontinuous
  have hproper : ∃ a : C, Φ (a : E) ≠ ⊤ := by
    obtain ⟨a, ha⟩ := hCne
    exact ⟨⟨a, ha⟩, WithTop.coe_ne_top⟩
  have hcoercive : C14Minimization.Spec.Coercive C (fun z : C => Φ (z : E)) := by
    intro a
    refine ⟨a + ‖x‖ + 1, ?_⟩
    intro z hz
    change (a : WithTop ℝ) < (dist (z : E) x : WithTop ℝ)
    rw [WithTop.coe_lt_coe, dist_eq_norm]
    have := norm_le_norm_sub_add (z : E) x
    linarith
  obtain ⟨z, m, _, hmin⟩ := C14Minimization.convex_direct_method 𝕜 E hE C hCne hCconv hCclosed
    Φ hconv hlsc hproper (Or.inr (Or.inl hcoercive))
  refine ⟨z, z.property, ?_⟩
  intro y hy
  have hm : dist (z : E) x ≤ dist y x := WithTop.coe_le_coe.mp (hmin ⟨y, hy⟩)
  simpa only [dist_eq_norm, norm_sub_rev] using hm

/-- Unique best approximation in a reflexive strictly convex Banach space,
including the zero space, zero distance, and unbounded closed convex sets. -/
theorem reflexive_unique_nearest_point : Spec.ReflexiveUniqueNearestPoint.{u,v} := by
  intro 𝕜 E _ _ _ _ hE hrot
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  intro C hCne hCclosed hCconv x
  obtain ⟨z, hz⟩ := reflexive_best_approximation 𝕜 E hE C hCne hCclosed hCconv x
  refine ⟨z, hz, ?_⟩
  intro w hw
  exact ((rotund_iff_nearest_unique 𝕜 E).mp hrot C hCconv x z w hz hw).symm

end
end ExpandedFA.P1.StrictApproximation
