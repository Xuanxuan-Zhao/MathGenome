import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.GlobalGrowth
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachConvex.Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp

/-! The growth clause of `fa2:p2:subgradient-slater`.
The scaled-segment proof uses only convexity and the global upper bound.
In particular continuity is a conclusion, not an assumption.
-/
namespace ExpandedFA.BanachConvex

universe u

/-- A linear function of an arbitrarily large positive parameter cannot
have a positive slope when bounded above. -/
private lemma nonpos_of_scaled_le (d M : ℝ)
    (h : ∀ t : ℝ, 1 ≤ t → t * d ≤ M) : d ≤ 0 := by
  by_contra hd
  have hd : 0 < d := lt_of_not_ge hd
  let t := (|M| + 1) / d + 1
  have ht : 1 ≤ t := by
    dsimp [t]
    have := div_nonneg (show 0 ≤ |M| + 1 by positivity) hd.le
    linarith
  have heq : t * d = |M| + 1 + d := by
    dsimp [t]
    field_simp
  have := h t ht
  rw [heq] at this
  have := le_abs_self M
  linarith

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- One side of the sharp Lipschitz estimate, obtained by prolonging a
segment and using the upper growth bound at its far endpoint. -/
lemma convex_sub_le_of_global_growth (φ : X → ℝ) (k C : ℝ) (hk : 0 ≤ k)
    (hφ : ConvexOn ℝ Set.univ φ) (hg : ∀ x, φ x ≤ k * ‖x‖ + C)
    (x y : X) : φ y - φ x ≤ k * ‖y - x‖ := by
  have h := nonpos_of_scaled_le (φ y - φ x - k * ‖y - x‖)
    (k * ‖x‖ + C - φ x) ?_
  · linarith
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hti : 0 ≤ t⁻¹ := inv_nonneg.mpr ht0.le
  have hti1 : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht
  let z := x + t • (y - x)
  have heq : (1 - t⁻¹) • x + t⁻¹ • z = y := by
    dsimp [z]
    simp only [smul_add, smul_smul, inv_mul_cancel₀ ht0.ne', one_smul]
    module
  have hc := hφ.2 (Set.mem_univ x) (Set.mem_univ z)
    (sub_nonneg.mpr hti1) hti (show 1 - t⁻¹ + t⁻¹ = 1 by ring)
  rw [heq] at hc
  simp only [smul_eq_mul] at hc
  have hcm := mul_le_mul_of_nonneg_left hc ht0.le
  have hcancel : t * ((1 - t⁻¹) * φ x + t⁻¹ * φ z) =
      (t - 1) * φ x + φ z := by
    field_simp
  rw [hcancel] at hcm
  have hn : ‖z‖ ≤ ‖x‖ + t * ‖y - x‖ := by
    simpa only [z, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      using norm_add_le x (t • (y - x))
  have hz := (hg z).trans (add_le_add (mul_le_mul_of_nonneg_left hn hk) (le_refl C))
  nlinarith

theorem global_growth_lipschitz : Spec.GlobalGrowthLipschitz.{u} := by
  intro X _ _ φ k C hk hφ hg
  have hl : LipschitzWith ⟨k, hk⟩ φ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, dist_eq_norm]
    change |φ x - φ y| ≤ k * ‖x - y‖
    apply abs_le.mpr
    constructor
    · have h := convex_sub_le_of_global_growth φ k C hk hφ hg x y
      rw [norm_sub_rev y x] at h
      linarith
    · exact convex_sub_le_of_global_growth φ k C hk hφ hg y x
  exact ⟨hl, hl.continuous⟩

/-- Finiteness of the conjugate gives a global affine lower bound; scaling
it against the upper growth bound controls the norm of the functional.
This implication does not require convexity. -/
lemma norm_le_of_conjugate_ne_top_of_global_growth (φ : X → ℝ) (k C : ℝ)
    (hk : 0 ≤ k) (hg : ∀ x, φ x ≤ k * ‖x‖ + C) (f : X →L[ℝ] ℝ)
    (hf : P1.C06Conjugates.convexConjugate X
      (fun x => (φ x : WithTop ℝ)) f ≠ ⊤) : ‖f‖ ≤ k := by
  let r := (P1.C06Conjugates.convexConjugate X
    (fun x => (φ x : WithTop ℝ)) f).toReal
  have hb (x : X) : f x - φ x ≤ r := by
    apply EReal.coe_le_coe_iff.mp
    calc
      ((f x - φ x : ℝ) : EReal) =
          (f x : EReal) - P1.C06Conjugates.extendedRealValue (φ x : WithTop ℝ) :=
        EReal.coe_sub _ _
      _ ≤ P1.C06Conjugates.convexConjugate X
          (fun x => (φ x : WithTop ℝ)) f := by
        unfold P1.C06Conjugates.convexConjugate
        exact le_iSup (fun y : X => (f y : EReal) -
          P1.C06Conjugates.extendedRealValue (φ y : WithTop ℝ)) x
      _ ≤ (r : EReal) := EReal.le_coe_toReal hf
  have hlin (v : X) : f v ≤ k * ‖v‖ := by
    have h := nonpos_of_scaled_le (f v - k * ‖v‖) (r + C) ?_
    · linarith
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    have h := hb (t • v)
    have hg' := hg (t • v)
    simp only [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht0] at h hg'
    nlinarith
  apply f.opNorm_le_bound hk
  intro v
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have h := hlin (-v)
    simpa only [map_neg, norm_neg, neg_le] using h
  · exact hlin v

theorem global_growth_conjugate_domain : Spec.GlobalGrowthConjugateDomain.{u} := by
  intro X _ _ φ k C hk _hφ hg f hf
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_of_conjugate_ne_top_of_global_growth φ k C hk hg f hf

/-- Explicit transport from the shared half-extended representation of
the manuscript's functions, under precisely finiteness everywhere. -/
theorem global_growth_finite_extended : Spec.GlobalGrowthFiniteExtended.{u} := by
  intro X _ _ φ k C hk hfin hφ hg
  let ψ : X → ℝ := fun x => (φ x).untop (hfin x)
  have hrep (x : X) : φ x = (ψ x : WithTop ℝ) :=
    (WithTop.coe_untop (φ x) (hfin x)).symm
  have hc : ConvexOn ℝ Set.univ ψ := by
    refine ⟨convex_univ, ?_⟩
    intro x _hx y _hy a b ha hb hab
    change ψ (a • x + b • y) ≤ a * ψ x + b * ψ y
    apply WithTop.coe_le_coe.mp
    rw [← hrep (a • x + b • y)]
    exact hφ x y (ψ x) (ψ y) a b (hrep x) (hrep y) ha hb hab
  have hgψ (x : X) : ψ x ≤ k * ‖x‖ + C := by
    have h := hg x
    rw [hrep x] at h
    exact WithTop.coe_le_coe.mp h
  obtain ⟨hl, hcont⟩ := global_growth_lipschitz X ψ k C hk hc hgψ
  refine ⟨ψ, hrep, hl, hcont, ?_⟩
  have heq : φ = fun x => (ψ x : WithTop ℝ) := funext hrep
  rw [heq]
  exact global_growth_conjugate_domain X ψ k C hk hc hgψ

end ExpandedFA.BanachConvex
