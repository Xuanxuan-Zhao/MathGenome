import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14Goldstine
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12WeakStar
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05BidualIsometry
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06StrongSeparation
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.WeakDual

/-! Goldstine density via separation of a finite coordinate image.
A real separator is extended to the original scalar field with the same
norm. Its composite with the coordinate map contradicts the bidual norm
bound. All closures in the coordinate argument are ordinary norm closures. -/
namespace ExpandedFA.P1.C14Goldstine
universe u v w
open Set Metric
open scoped Topology BigOperators
noncomputable section

/-- A functional on a finite coordinate space commutes with bidual evaluation. -/
lemma bidual_finite_coordinates {𝕜 : Type u} {E : Type v} {ι : Type w}
    [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Fintype ι]
    (f : ι → E →L[𝕜] 𝕜) (ξ : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
    (g : (ι → 𝕜) →L[𝕜] 𝕜) :
    ξ (g.comp (ContinuousLinearMap.pi f)) = g (fun i => ξ (f i)) := by
  classical
  have heq : g.comp (ContinuousLinearMap.pi f) =
      ∑ i, g (fun j => if i = j then 1 else 0) • f i := by
    ext x
    simpa [sum_apply, smul_apply, smul_eq_mul,
      mul_comm] using g.toLinearMap.pi_apply_eq_sum_univ (fun i => f i x)
  rw [heq, map_sum]
  simpa [map_smul, smul_eq_mul, mul_comm] using
    (g.toLinearMap.pi_apply_eq_sum_univ (fun i => ξ (f i))).symm

/-- Every finite coordinate vector of a bidual unit vector is in the closure
of the coordinate image of the original closed unit ball. -/
lemma bidual_coordinates_mem_closure {𝕜 : Type u} {E : Type v} {ι : Type w}
    [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Fintype ι]
    (ξ : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜) (hξ : ‖ξ‖ ≤ 1)
    (f : ι → E →L[𝕜] 𝕜) :
    (fun i => ξ (f i)) ∈ closure
      ((ContinuousLinearMap.pi f) '' {x : E | ‖x‖ ≤ 1}) := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  let V := ContinuousLinearMap.pi f
  let a : ι → 𝕜 := fun i => ξ (f i)
  let C := closure (V '' {x : E | ‖x‖ ≤ 1})
  have hzero : (0 : ι → 𝕜) ∈ C :=
    subset_closure ⟨0, by simp, V.map_zero⟩
  have hconv : Convex ℝ C := by
    apply Convex.closure
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ r t hr ht hrt
    refine ⟨r • x + t • y, ?_, ?_⟩
    · have hb : Convex ℝ {z : E | ‖z‖ ≤ 1} := by
        have heq : closedBall (0 : E) 1 = {z : E | ‖z‖ ≤ 1} := by ext z; simp
        rw [← heq]
        exact convex_closedBall (0 : E) (1 : ℝ)
      exact hb hx hy hr ht hrt
    · ext i
      exact congrArg (fun z : ι → 𝕜 => z i) ((V.restrictScalars ℝ).map_add (r • x) (t • y) |>.trans
        (congrArg₂ (· + ·) ((V.restrictScalars ℝ).map_smul r x)
          ((V.restrictScalars ℝ).map_smul t y)))
  by_contra ha
  obtain ⟨h, _, hbd, hsep⟩ := C06.real_point_strong_separation C a
    ⟨0, hzero⟩ isClosed_closure hconv ha
  let s := sSup (h '' C)
  let q : E →L[ℝ] ℝ := h.comp (V.restrictScalars ℝ)
  have hq : ‖q‖ ≤ s := by
    have hb : ∀ x ∈ closedBall (0 : E) 1, ‖q x‖ ≤ s := by
      intro x hx
      have hx' : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
      have hp : q x ≤ s := le_csSup hbd
        (mem_image_of_mem h (subset_closure ⟨x, hx', rfl⟩))
      have hn : q (-x) ≤ s := le_csSup hbd
        (mem_image_of_mem h (subset_closure ⟨-x, by simpa using hx', rfl⟩))
      rw [map_neg] at hn
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith, hp⟩
    simpa using q.opNorm_bound_of_ball_bound (by norm_num : (0 : ℝ) < 1) s hb
  let g : (ι → 𝕜) →L[𝕜] 𝕜 := StrongDual.extendRCLike h
  let F : E →L[𝕜] 𝕜 := g.comp V
  have hext : (StrongDual.extendRCLike q : E →L[𝕜] 𝕜) = F := by
    ext x
    change (h (V x) : 𝕜) - RCLike.I * (h (V (RCLike.I • x)) : 𝕜) =
      (h (V x) : 𝕜) - RCLike.I * (h (RCLike.I • V x) : 𝕜)
    rw [map_smul]
  have hF : ‖F‖ ≤ s := by
    rw [← hext, StrongDual.norm_extendRCLike]
    exact hq
  have hval : RCLike.re (ξ F) = h a := by
    rw [show ξ F = g a from bidual_finite_coordinates f ξ g]
    exact StrongDual.re_extendRCLike_apply h a
  have hle : h a ≤ s := by
    calc
      h a = RCLike.re (ξ F) := hval.symm
      _ ≤ ‖ξ F‖ := RCLike.re_le_norm _
      _ ≤ ‖ξ‖ * ‖F‖ := ξ.le_opNorm F
      _ ≤ 1 * ‖F‖ := mul_le_mul_of_nonneg_right hξ (norm_nonneg _)
      _ ≤ s := by simpa using hF
  exact (not_lt_of_ge hle) hsep


/-- Simultaneously approximate every test in a finite set, in the closed unit ball. -/
theorem goldstine_finite_approximation : Spec.FiniteApproximation.{u, v} := by
  intro 𝕜 E _ _ _ ξ hξ s ε hε
  classical
  let f : s → E →L[𝕜] 𝕜 := fun i => i.1
  have ha := bidual_coordinates_mem_closure ξ hξ f
  obtain ⟨y, ⟨x, hx, rfl⟩, hy⟩ := Metric.mem_closure_iff.mp ha ε hε
  refine ⟨x, hx, ?_⟩
  intro g hg
  have hi := norm_le_pi_norm
    ((ContinuousLinearMap.pi f) x - fun i => ξ (f i)) (⟨g, hg⟩ : s)
  exact hi.trans_lt (by simpa only [dist_eq_norm, norm_sub_rev] using hy)

/-- The finite-family version, allowing repeated tests and m = 0. -/
theorem goldstine_finite_family : Spec.FiniteFamilyApproximation.{u, v} := by
  intro 𝕜 E _ _ _ ξ hξ m f ε hε
  classical
  obtain ⟨x, hx, h⟩ := goldstine_finite_approximation 𝕜 E ξ hξ
    (Finset.univ.image f) ε hε
  exact ⟨x, hx, fun j => h (f j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)⟩

/-- Goldstine's theorem in the explicitly specified weak-star topology σ(E″, E′). -/
theorem goldstine_density : Spec.Density.{u, v} := by
  intro 𝕜 E _ _ _
  let D := (E →L[𝕜] 𝕜) →L[𝕜] 𝕜
  let t := C12WeakStar.weakStarTopology 𝕜 (E →L[𝕜] 𝕜)
  have hc : @IsClosed D t {ξ | ‖ξ‖ ≤ 1} := by
    apply isClosed_induced_iff.mpr
    refine ⟨WeakDual.toStrongDual ⁻¹' closedBall (0 : D) 1,
      WeakDual.isClosed_closedBall (𝕜 := 𝕜) 0 1, ?_⟩
    ext ξ
    change ξ ∈ closedBall (0 : D) 1 ↔ ‖ξ‖ ≤ 1
    exact @mem_closedBall_zero_iff D _ ξ 1
  apply Set.Subset.antisymm
  · apply @closure_minimal D t _ _ _ hc
    rintro ξ ⟨x, hx, rfl⟩
    exact (C05BidualIsometry.canonicalEvaluation_norm 𝕜 E x).le.trans hx
  · intro ξ hξ
    apply (@mem_closure_iff_nhds_basis D t _ _ _ _ _
      (C12WeakStar.weakStarTopology_nhds_basis 𝕜 (E →L[𝕜] 𝕜) ξ)).mpr
    intro p hp
    obtain ⟨x, hx, h⟩ := goldstine_finite_approximation 𝕜 E ξ hξ p.1 p.2 hp
    refine ⟨C04CanonicalMap.canonicalEvaluation 𝕜 E x, ⟨x, hx, rfl⟩, ?_⟩
    exact h

end
end ExpandedFA.P1.C14Goldstine
