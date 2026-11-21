import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BishopPhelps
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.BishopPhelpsSupportPoints
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Tactic.FieldSimp

namespace ExpandedFA.P1.BishopPhelps
open Set Metric
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Cone separation turns an approximate maximum into an exact supporting
functional with the same error bound. No completeness is needed here. -/
theorem support_of_approximate_maximum {C : Set E} (hC : Convex ℝ C)
    {x : E} (hx : x ∈ C) (f : E →L[ℝ] ℝ) {α : ℝ} (ha : 0 < α)
    (hmax : ∀ y ∈ C, f (y-x) ≤ α * ‖y-x‖) :
    ∃ g : E →L[ℝ] ℝ, ‖g-f‖ ≤ α ∧ ∀ y ∈ C, g y ≤ g x := by
  let p : E → ℝ := fun z => α * ‖z‖
  have hp : ConvexOn ℝ univ p := (convexOn_norm convex_univ).smul ha.le
  let D : Set (E × ℝ) := {q | p q.1 < q.2}
  let T : E →L[ℝ] E × ℝ := (ContinuousLinearMap.id ℝ E).prod f
  let A : Set (E × ℝ) := (fun y => T (y-x)) '' C
  have hA : Convex ℝ A := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ a b ha hb hab
    refine ⟨a • y + b • z, hC hy hz ha hb hab, ?_⟩
    change T (a • y + b • z - x) = a • T (y-x) + b • T (z-x)
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    have he : a • (y-x) + b • (z-x) = a • y + b • z - (a+b) • x := by
      rw [add_smul, smul_sub, smul_sub]
      abel
    rw [he, hab, one_smul]
  have hD : Convex ℝ D := by
    simpa only [D, mem_univ, true_and] using hp.convex_strict_epigraph
  have ho : IsOpen D := isOpen_lt (by dsimp [p]; fun_prop) continuous_snd
  have hA0 : (0 : E × ℝ) ∈ A := ⟨x, hx, by simp⟩
  have hd : Disjoint D A := by
    apply disjoint_left.mpr
    rintro q hq ⟨y, hy, rfl⟩
    exact (not_lt_of_ge (hmax y hy)) hq
  obtain ⟨k, a, hk, hkD, hkA⟩ := C06.real_normed_open_convex_separation
    D A ⟨(0,1), by simp [D, p]⟩ ⟨0,hA0⟩ hD hA hd ho
  have hclosure (z : E) : (z, p z) ∈ closure D := by
    have hs := hp.openSegment_subset_strict_epigraph (z, p z + 1) (z, p z)
      ⟨mem_univ _, by dsimp; linarith⟩ ⟨mem_univ _, le_rfl⟩
    have hs' : openSegment ℝ (z, p z + 1) (z, p z) ⊆ D := by simpa [D] using hs
    exact closure_mono hs' (segment_subset_closure_openSegment (right_mem_segment ℝ _ _))
  have hkb (z : E) : k (z, p z) ≤ a :=
    closure_minimal (fun q hq => (hkD q hq).le)
      (isClosed_le k.continuous continuous_const) (hclosure z)
  have ha0 : a = 0 := by
    have h1 := hkA 0 hA0
    have h2 := hkb 0
    change a ≤ k 0 at h1
    simp only [p, norm_zero, mul_zero] at h2
    have hz : k (0,0) = 0 := k.map_zero
    rw [map_zero] at h1
    rw [hz] at h2
    linarith
  let h : E →L[ℝ] ℝ := (-k).comp (ContinuousLinearMap.inl ℝ E ℝ)
  let s : ℝ := -k (0,1)
  have hsplit (z : E) (t : ℝ) : -k (z,t) = h z + s*t := by
    have heq : (z,t) = (z,0) + t • (0,1) := by ext <;> simp
    rw [heq, map_add, map_smul]
    simp [h, s]
    ring
  have hs : 0 < s := by
    have := hkD (0,1) (by simp [D,p])
    dsimp [s]
    linarith
  have hbound (z : E) : - (s*α*‖z‖) ≤ h z := by
    have := hkb z
    rw [ha0] at this
    have he := hsplit z (p z)
    dsimp [p] at he
    nlinarith
  have habs (z : E) : ‖h z‖ ≤ s*α*‖z‖ := by
    rw [Real.norm_eq_abs, abs_le]
    refine ⟨hbound z, ?_⟩
    have := hbound (-z)
    simpa using this
  let g : E →L[ℝ] ℝ := f + s⁻¹ • h
  refine ⟨g, ?_, ?_⟩
  · have heq : g-f = s⁻¹ • h := by dsimp [g]; abel
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
    have hn := h.opNorm_le_bound (mul_nonneg hs.le ha.le) habs
    calc
      s⁻¹ * ‖h‖ ≤ s⁻¹ * (s*α) := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hs.le)
      _ = α := by field_simp
  · intro y hy
    have hky := hkA (T (y-x)) ⟨y,hy,rfl⟩
    rw [ha0] at hky
    have he := hsplit (y-x) (f (y-x))
    change -k (T (y-x)) = _ at he
    have hi : h (y-x) + s * f (y-x) ≤ 0 := by linarith
    have hg : g (y-x) ≤ 0 := by
      change f (y-x) + s⁻¹ * h (y-x) ≤ 0
      have := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hs.le) hi
      field_simp at this ⊢
      nlinarith
    simpa [map_sub] using hg

/-- Quantitative Bishop--Phelps over the real field. -/
theorem real_approximation : Spec.RealApproximation.{u} := by
  intro E _ _ _ C hne hc hv f hb α ha
  let : CompleteSpace C := hc.isComplete.completeSpace_coe
  let F : C → ℝ := fun y => -f y
  have hF : LowerSemicontinuous F :=
    (f.continuous.comp continuous_subtype_val).neg.lowerSemicontinuous
  have hFb : BddBelow (range F) := by
    obtain ⟨M, hM⟩ := hb
    refine ⟨-M, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact neg_le_neg (hM ⟨y, y.property, rfl⟩)
  obtain ⟨b, hbC⟩ := hne
  obtain ⟨x, _, hterminal⟩ := exists_terminal_descent hF hFb ha (⟨b,hbC⟩ : C)
  have hmax : ∀ y ∈ C, f (y-(x : E)) ≤ α * ‖y-(x : E)‖ := by
    intro y hy
    by_contra hh
    have hd : Descent F α x (⟨y,hy⟩ : C) := by
      dsimp [Descent, F]
      change -f y + α * dist y (x : E) ≤ -f (x : E)
      rw [dist_eq_norm]
      rw [map_sub] at hh
      linarith
    have he := hterminal ⟨y,hy⟩ hd
    have hey : y = (x : E) := congrArg Subtype.val he
    simp [hey] at hh
  obtain ⟨g, hg, hs⟩ := support_of_approximate_maximum hv x.property f ha hmax
  exact ⟨x, x.property, g, hg, hs⟩

/-- Real-part restriction and complex extension preserve the error norm. -/
theorem complex_approximation : Spec.ComplexApproximation.{u} := by
  intro E _ _ _ C hne hc hv f hb α ha
  let e := StrongDual.extendRCLikeₗᵢ (𝕜 := ℂ) (F := E)
  let fr : E →L[ℝ] ℝ := e.symm f
  have hb' : BddAbove (fr '' C) := hb
  obtain ⟨x, hx, h, hh, hs⟩ := real_approximation E C hne hc hv fr hb' α ha
  refine ⟨x, hx, e h, ?_, ?_⟩
  · have he : e h - f = e (h-fr) := by simp [fr, map_sub]
    rw [he, e.norm_map]
    exact hh
  · intro y hy
    change ((StrongDual.extendRCLike h : E →L[ℂ] ℂ) y).re ≤
      ((StrongDual.extendRCLike h : E →L[ℂ] ℂ) x).re
    calc
      _ = h y := StrongDual.re_extendRCLike_apply (𝕜 := ℂ) h y
      _ ≤ h x := hs y hy
      _ = _ := (StrongDual.re_extendRCLike_apply (𝕜 := ℂ) h x).symm

/-- The boundary clause uses the accepted support-point theorem. -/
theorem real_boundary_density : Spec.RealBoundaryDensity.{u} :=
  BishopPhelpsSupportPoints.real_boundary_density

theorem complex_boundary_density : Spec.ComplexBoundaryDensity.{u} :=
  BishopPhelpsSupportPoints.complex_boundary_density

/-- A real functional supporting the unit ball attains its operator norm. -/
theorem norm_eq_of_support_unitBall (f : E →L[ℝ] ℝ) {x : E}
    (hx : x ∈ closedBall (0 : E) 1)
    (hs : ∀ y ∈ closedBall (0 : E) 1, f y ≤ f x) : ‖f x‖ = ‖f‖ := by
  have hp : 0 ≤ f x := by simpa using hs 0 (by simp)
  apply le_antisymm (f.unit_le_opNorm x (mem_closedBall_zero_iff.mp hx))
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _)
  intro y hy
  have h1 := hs y (by simpa using hy.le)
  have h2 := hs (-y) (by simpa using hy.le)
  rw [map_neg] at h2
  rw [Real.norm_eq_abs, abs_le]
  rw [Real.norm_eq_abs, abs_of_nonneg hp]
  exact ⟨by linarith, h1⟩

/-- Norm-attaining real scalar-linear functionals are norm dense. -/
theorem real_norm_attaining_dense : Spec.RealNormAttainingDense.{u} := by
  intro E _ _ _
  apply Metric.dense_iff.mpr
  intro f ε hε
  have hb : BddAbove (f '' closedBall (0 : E) 1) := by
    refine ⟨‖f‖, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact (le_abs_self _).trans (f.unit_le_opNorm y (mem_closedBall_zero_iff.mp hy))
  obtain ⟨x, hx, g, hg, hs⟩ := real_approximation E (closedBall 0 1)
    ⟨0, by simp⟩ isClosed_closedBall (convex_closedBall 0 1) f hb (ε/2) (by positivity)
  refine ⟨g, ?_, x, hx, norm_eq_of_support_unitBall g hx hs⟩
  change dist g f < ε
  rw [dist_eq_norm]
  linarith

/-- Complex extension of a norm-attaining real functional attains its norm. -/
theorem norm_attaining_extend {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (h : F →L[ℝ] ℝ) {x : F} (hx : x ∈ closedBall (0 : F) 1)
    (hn : ‖h x‖ = ‖h‖) :
    ‖(StrongDual.extendRCLike h : F →L[ℂ] ℂ) x‖ = ‖(StrongDual.extendRCLike h : F →L[ℂ] ℂ)‖ := by
  apply le_antisymm ((StrongDual.extendRCLike h : F →L[ℂ] ℂ).unit_le_opNorm x
    (mem_closedBall_zero_iff.mp hx))
  rw [StrongDual.norm_extendRCLike, ← hn]
  have hi := RCLike.abs_re_le_norm ((StrongDual.extendRCLike h : F →L[ℂ] ℂ) x)
  simpa [StrongDual.re_extendRCLike_apply, Real.norm_eq_abs] using hi

/-- Norm-attaining complex scalar-linear functionals are norm dense. -/
theorem complex_norm_attaining_dense : Spec.ComplexNormAttainingDense.{u} := by
  intro E _ _ _
  apply Metric.dense_iff.mpr
  intro f ε hε
  let e := StrongDual.extendRCLikeₗᵢ (𝕜 := ℂ) (F := E)
  obtain ⟨h, hh, x, hx, hn⟩ := Metric.dense_iff.mp (real_norm_attaining_dense E)
    (e.symm f) ε hε
  refine ⟨e h, ?_, x, hx, norm_attaining_extend h hx hn⟩
  have he : e h - f = e (h-e.symm f) := by simp
  change dist (e h) f < ε
  rw [dist_eq_norm, he, e.norm_map]
  exact (dist_eq_norm h (e.symm f)) ▸ hh

end ExpandedFA.P1.BishopPhelps
