import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.SlaterNormalCone
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachConvex.GlobalGrowth
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachConvex.LocalLipschitzSubgradients
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06OpenSeparation
import Batteries.Tactic.OpenPrivate

/-! Slater's normal-cone formula on a real normed space.
Separate the upper image of (φ, -g(·-x)) from the open negative quadrant
in ℝ². Positivity of the second coefficient follows from strict feasibility.
Continuity is used for existence of a subgradient when the multiplier is zero.
-/
namespace ExpandedFA.BanachConvex

open Set P1.ExtendedConvexFunctions
open private nonpos_of_scaled_le from MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachConvex.GlobalGrowth

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Transport a finite convex function to the canonical extended value space. -/
lemma extendedConvex_of_real_convex (φ : X → ℝ) (hc : ConvexOn ℝ univ φ) :
    ExtendedConvex X (fun y => (φ y : WithTop ℝ)) := by
  intro y z r s a b hy hz ha hb hab
  have hr : φ y = r := WithTop.coe_inj.mp hy
  have hs : φ z = s := WithTop.coe_inj.mp hz
  apply WithTop.coe_le_coe.mpr
  simpa only [smul_eq_mul, hr, hs] using hc.2 (mem_univ y) (mem_univ z) ha hb hab

/-- Continuity gives a bounded closed ball, so the accepted local theorem
supplies a continuous subgradient. This also applies to the zero space. -/
lemma subdifferential_nonempty_of_continuous_convex (φ : X → ℝ)
    (hcont : Continuous φ) (hc : ConvexOn ℝ univ φ) (x : X) :
    (subdifferential X (fun y => (φ y : WithTop ℝ)) x).Nonempty := by
  have hn : {y | φ y < φ x + 1} ∈ nhds x :=
    hcont.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by linarith))
  obtain ⟨R, hR, hbound⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hn
  exact subgradients_nonempty_of_ball_bound X (fun y => (φ y : WithTop ℝ))
    x R (φ x + 1) ⟨x, WithTop.coe_ne_top⟩ (extendedConvex_of_real_convex φ hc)
    hR (fun y hy => WithTop.coe_le_coe.mpr (hbound hy).le) x
    (Metric.mem_ball_self hR)

/-- Coordinates of a real functional on the plane. -/
lemma plane_functional_apply (h : (ℝ × ℝ) →L[ℝ] ℝ) (r s : ℝ) :
    h (r, s) = r * h (1, 0) + s * h (0, 1) := by
  have he : (r, s) = r • (1, 0) + s • (0, 1) := by ext <;> simp
  rw [he, map_add, map_smul, map_smul]
  rfl

/-- Separation produces a nonnegative multiplier and complementary slackness.
This part only uses finite convexity and Slater, without continuity. -/
lemma slater_supporting_multiplier (φ : X → ℝ) (hc : ConvexOn ℝ univ φ)
    (hz : ∃ z, φ z < 0) (x : X) (hx : φ x ≤ 0) (g : X →L[ℝ] ℝ)
    (hg : g ∈ normalCone X {y | φ y ≤ 0} x) :
    ∃ μ : ℝ, 0 ≤ μ ∧ μ * φ x = 0 ∧
      ∀ y, g (y - x) ≤ μ * (φ y - φ x) := by
  let A : Set (ℝ × ℝ) := Iic (0 : ℝ) ×ˢ Iic (0 : ℝ)
  let B : Set (ℝ × ℝ) := {p | ∃ y : X, φ y ≤ p.1 ∧ -g (y - x) ≤ p.2}
  have hA : Convex ℝ A := (convex_Iic (0 : ℝ)).prod (convex_Iic (0 : ℝ))
  have hB : Convex ℝ B := by
    rintro p ⟨y, hyp, hgp⟩ q ⟨z, hzq, hgq⟩ a b ha hb hab
    refine ⟨a • y + b • z, ?_, ?_⟩
    · have hh := hc.2 (mem_univ y) (mem_univ z) ha hb hab
      change φ (a • y + b • z) ≤ a * p.1 + b * q.1
      change φ (a • y + b • z) ≤ a * φ y + b * φ z at hh
      exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hyp ha)
        (mul_le_mul_of_nonneg_left hzq hb))
    · have he : a • y + b • z - x = a • (y - x) + b • (z - x) := by
        calc
          _ = a • y + b • z - (a + b) • x := by rw [hab, one_smul]
          _ = _ := by module
      change -g (a • y + b • z - x) ≤ a * p.2 + b * q.2
      rw [he, map_add, map_smul, map_smul]
      change -(a * g (y - x) + b * g (z - x)) ≤ _
      nlinarith [mul_le_mul_of_nonneg_left hgp ha, mul_le_mul_of_nonneg_left hgq hb]
  have hAi : interior A = Iio (0 : ℝ) ×ˢ Iio (0 : ℝ) := by
    change interior (Iic (0 : ℝ) ×ˢ Iic (0 : ℝ)) = _
    rw [interior_prod_eq, interior_Iic]
  have hdisj : Disjoint (interior A) B := by
    rw [disjoint_left]
    rintro p hp ⟨y, hy, hgy⟩
    rw [hAi] at hp
    have hy0 : φ y ≤ 0 := hy.trans hp.1.le
    have hg0 := hg.2 y hy0
    have hp2 : p.2 < 0 := hp.2
    linarith
  have hAne : (interior A).Nonempty := by
    rw [hAi]
    exact ⟨(-1, -1), by constructor <;> norm_num⟩
  have hBne : B.Nonempty := ⟨(φ x, 0), x, le_rfl, by simp⟩
  obtain ⟨h, α, hne, hleft, hright⟩ :=
    geometric_hahn_banach_of_nonempty_interior hA hB hdisj hAne hBne
  let a := h (1, 0)
  let b := h (0, 1)
  have hα : 0 ≤ α := by
    simpa only [map_zero] using hleft 0 (by change (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 0; exact ⟨le_rfl, le_rfl⟩)
  have ha : 0 ≤ a := by
    have hh := nonpos_of_scaled_le (-a) α (fun t ht => ?_)
    · linarith
    have hh := hleft (-t, 0) (by change -t ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 0; constructor <;> linarith)
    rw [plane_functional_apply] at hh
    dsimp [a] at *
    nlinarith
  have hb : 0 ≤ b := by
    have hh := nonpos_of_scaled_le (-b) α (fun t ht => ?_)
    · linarith
    have hh := hleft (0, -t) (by change (0 : ℝ) ≤ 0 ∧ -t ≤ (0 : ℝ); constructor <;> linarith)
    rw [plane_functional_apply] at hh
    dsimp [b] at *
    nlinarith
  have hineq (y : X) : 0 ≤ a * φ y - b * g (y - x) := by
    have hh := hα.trans (hright (φ y, -g (y - x)) ⟨y, le_rfl, le_rfl⟩)
    rw [plane_functional_apply] at hh
    dsimp [a, b] at *
    nlinarith
  have hbpos : 0 < b := by
    by_contra hbp
    have hb0 : b = 0 := le_antisymm (not_lt.mp hbp) hb
    have ha0 : a ≠ 0 := by
      intro ha0
      apply hne
      apply ContinuousLinearMap.ext
      rintro ⟨r, s⟩
      change h (r, s) = 0
      rw [plane_functional_apply]
      change r * a + s * b = 0
      simp [ha0, hb0]
    obtain ⟨z, hz⟩ := hz
    have hh := hineq z
    rw [hb0] at hh
    have := mul_neg_of_pos_of_neg (lt_of_le_of_ne ha (Ne.symm ha0)) hz
    nlinarith
  have hcomp : a * φ x = 0 := by
    have hh := hineq x
    simp only [sub_self, map_zero, mul_zero, sub_zero] at hh
    exact le_antisymm (mul_nonpos_of_nonneg_of_nonpos ha hx) hh
  refine ⟨a / b, div_nonneg ha hbpos.le, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, hcomp, zero_div]
  · intro y
    apply (mul_le_mul_iff_left₀ hbpos).mp
    have hh := hineq y
    have he : (a / b) * (φ y - φ x) * b = a * φ y := by
      field_simp
      nlinarith [hcomp]
    rw [he]
    nlinarith

/-- Slater's formula with all nonnegative multipliers, including zero. -/
theorem slater_normalCone : SlaterSpec.SlaterNormalCone.{u} := by
  intro X _ _ φ hcont hc hz x hx
  change normalCone X {y | φ y ≤ 0} x =
    {g | ∃ (f : X →L[ℝ] ℝ) (μ : ℝ),
      f ∈ subdifferential X (fun y => (φ y : WithTop ℝ)) x ∧
      0 ≤ μ ∧ μ * φ x = 0 ∧ g = μ • f}
  ext g
  constructor
  · intro hg
    obtain ⟨μ, hμ, hcomp, hs⟩ := slater_supporting_multiplier φ hc hz x hx g hg
    by_cases hμ0 : μ = 0
    · have hg0 : g = 0 := by
        apply ContinuousLinearMap.ext
        intro v
        have hp := hs (x + v)
        have hn := hs (x - v)
        simp only [hμ0, zero_mul, add_sub_cancel_left] at hp hn
        have he : x - v - x = -v := by module
        rw [he, map_neg] at hn
        change g v = 0
        linarith
      obtain ⟨f, hf⟩ := subdifferential_nonempty_of_continuous_convex φ hcont hc x
      exact ⟨f, 0, hf, le_rfl, by simp, by simp [hg0]⟩
    · refine ⟨μ⁻¹ • g, μ, ?_, hμ, hcomp, ?_⟩
      · apply (mem_subdifferential_iff_of_value _ x (φ x) rfl _).mpr
        intro y s hsy
        have hsy' : φ y = s := WithTop.coe_inj.mp hsy
        change φ x + μ⁻¹ * g (y - x) ≤ s
        have hh := mul_le_mul_of_nonneg_left (hs y) (inv_nonneg.mpr hμ)
        rw [← mul_assoc, inv_mul_cancel₀ hμ0, one_mul, hsy'] at hh
        linarith
      · rw [smul_smul, mul_inv_cancel₀ hμ0, one_smul]
  · rintro ⟨f, μ, hf, hμ, hcomp, rfl⟩
    refine ⟨hx, ?_⟩
    intro y hy
    have hs := (mem_subdifferential_iff_of_value _ x (φ x) rfl f).mp hf y (φ y) rfl
    have hh := mul_le_mul_of_nonneg_left hs hμ
    change μ * f (y - x) ≤ 0
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hμ hy]

/-- Complementarity forces the multiplier to vanish at a strictly feasible
point, while continuity provides the zero-multiplier witness for zero. -/
theorem normalCone_strict_sublevel : SlaterSpec.StrictSublevelNormalCone.{u} := by
  intro X _ _ φ hcont hc x hx
  have hformula := slater_normalCone X φ hcont hc ⟨x, hx⟩ x hx.le
  change normalCone X {y | φ y ≤ 0} x = {0}
  change normalCone X {y | φ y ≤ 0} x = _ at hformula
  rw [hformula]
  ext g
  constructor
  · rintro ⟨f, μ, _, _, hcomp, rfl⟩
    have hμ : μ = 0 := (mul_eq_zero.mp hcomp).resolve_right hx.ne
    simp [hμ]
  · intro hg
    have hg0 : g = 0 := hg
    obtain ⟨f, hf⟩ := subdifferential_nonempty_of_continuous_convex φ hcont hc x
    exact ⟨f, 0, hf, le_rfl, by simp, by simp [hg0]⟩

end ExpandedFA.BanachConvex
