import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C04.QuantitativeInverseBall
import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeInterfaces
import MathGenome.Internal.MultivariableAnalysis.D04.C04.Contraction
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith

noncomputable section
open Set
namespace D04

/-- The normalized defect is q-Lipschitz on the closed ball. Derivatives
exist in the ambient open set even at points of the sphere. -/
private theorem inverse_ball_defect_bound {n : ℕ}
    (U : Set (E n)) (f : E n → E n) (a : E n)
    (L : E n →L[ℝ] E n) (ρ q : ℝ)
    (hU : IsOpen U) (hf : CrOn 1 U f)
    (hball : Metric.closedBall a ρ ⊆ U)
    (hbound : ∀ x ∈ Metric.closedBall a ρ,
      ‖ContinuousLinearMap.id ℝ (E n) - L.comp (totalDerivative f x)‖ ≤ q)
    (x z : E n) (hx : x ∈ Metric.closedBall a ρ) (hz : z ∈ Metric.closedBall a ρ) :
    ‖(x - L (f x)) - (z - L (f z))‖ ≤ q * ‖x - z‖ := by
  have hd (w : E n) (hw : w ∈ Metric.closedBall a ρ) :
      HasFDerivAt f (totalDerivative f w) w := by
    have hf' : TotalDifferentiableOn U f := hf.1
    obtain ⟨B, hB⟩ := hf' w (hball hw)
    rw [totalDerivative_eq U f B w hB]
    exact (hasTotalDerivative_iff_hasFDerivAt U f B w hU (hball hw)).mp hB
  have hd' (w : E n) (hw : w ∈ Metric.closedBall a ρ) :
      HasFDerivWithinAt (fun v => v - L (f v))
        (ContinuousLinearMap.id ℝ (E n) - L.comp (totalDerivative f w))
        (Metric.closedBall a ρ) w :=
    ((hasFDerivAt_id w).sub (L.hasFDerivAt.comp w (hd w hw))).hasFDerivWithinAt
  exact (convex_closedBall a ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hd' hbound hz hx

/-- The quantitative closed-ball inverse theorem, including the one-point
space E 0. Only 1-q is divided by; no inverse operator norm is divided by. -/
theorem quantitative_inverse_ball :
    Specs.D04.C04.QuantitativeInverseBall.quantitative_inverse_ballType := by
  intro n U f a A ρ q hU hf ha hA hρ hball hq₀ hq₁ hbound
  let L : E n →L[ℝ] E n := A.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let d : E n → E n := fun x => x - L (f x)
  have hq : 0 < 1 - q := sub_pos.mpr hq₁
  have haBall : a ∈ Metric.closedBall a ρ := Metric.mem_closedBall_self hρ.le
  have hd (x z : E n) (hx : x ∈ Metric.closedBall a ρ)
      (hz : z ∈ Metric.closedBall a ρ) : ‖d x - d z‖ ≤ q * ‖x - z‖ :=
    inverse_ball_defect_bound U f a L ρ q hU hf hball hbound x z hx hz
  have hlower (x : E n) (hx : x ∈ Metric.closedBall a ρ)
      (z : E n) (hz : z ∈ Metric.closedBall a ρ) :
      (1 - q) * ‖x - z‖ ≤ ‖A.symm (f x - f z)‖ := by
    have he : x - z = (d x - d z) + L (f x - f z) := by
      dsimp [d]
      rw [map_sub]
      abel
    have ht := norm_add_le (d x - d z) (L (f x - f z))
    rw [← he] at ht
    have hd' := hd x z hx hz
    change (1 - q) * ‖x - z‖ ≤ ‖L (f x - f z)‖
    nlinarith
  have hinj : InjOn f (Metric.closedBall a ρ) := by
    intro x hx z hz he
    have hl := hlower x hx z hz
    rw [he, sub_self, map_zero, norm_zero] at hl
    have hz' : ‖x - z‖ = 0 := by nlinarith [norm_nonneg (x - z)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz')
  refine ⟨hlower, hinj, ?_, ?_, ?_⟩
  · intro y hy
    let T : E n → E n := fun x => d x + L y
    have hT (x z : E n) (hx : x ∈ Metric.closedBall a ρ)
        (hz : z ∈ Metric.closedBall a ρ) : ‖T x - T z‖ ≤ q * ‖x - z‖ := by
      simpa only [T, add_sub_add_right_eq_sub] using hd x z hx hz
    have hmaps : MapsTo T (Metric.closedBall a ρ) (Metric.closedBall a ρ) := by
      intro x hx
      have he : T x - a = (d x - d a) + L (y - f a) := by
        dsimp [T, d]
        rw [map_sub]
        abel
      have hx' : ‖x - a‖ ≤ ρ := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
      have ht := norm_add_le (d x - d a) (L (y - f a))
      rw [← he] at ht
      have hd' := hd x a hx haBall
      have hmul := mul_le_mul_of_nonneg_left hx' hq₀
      change ‖L (y - f a)‖ < (1 - q) * ρ at hy
      rw [Metric.mem_closedBall, dist_eq_norm]
      nlinarith
    let S := {x : E n | ‖x - a‖ ≤ ρ}
    have hS : S = Metric.closedBall a ρ := by
      ext x
      simp only [S, mem_ofPred_eq, Metric.mem_closedBall, dist_eq_norm]
    let Ts : S → S := fun x => ⟨T x, by
      change ‖T (x : E n) - a‖ ≤ ρ
      have hx : (x : E n) ∈ Metric.closedBall a ρ := by
        have hx₀ : ‖(x : E n) - a‖ ≤ ρ := x.property
        simpa only [Metric.mem_closedBall, dist_eq_norm] using hx₀
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hmaps hx⟩
    obtain ⟨xStar, hfix, _, _, _⟩ := contraction_principle S
      (closed_ball_complete a ρ) ⟨a, by simpa [S] using hρ.le⟩ Ts q hq₀ hq₁ (by
        intro x z
        exact hT x z (by rw [← hS]; exact x.property) (by rw [← hS]; exact z.property))
    have hx : (xStar : E n) ∈ Metric.closedBall a ρ := by rw [← hS]; exact xStar.property
    have hfix' : T xStar = (xStar : E n) := congrArg Subtype.val hfix
    have hfy : f xStar = y := by
      apply A.symm.injective
      change L (f xStar) = L y
      change (xStar : E n) - L (f xStar) + L y = (xStar : E n) at hfix'
      calc
        L (f xStar) = L (f xStar) +
            (((xStar : E n) - L (f xStar) + L y) - (xStar : E n)) := by
          rw [hfix']; simp
        _ = L y := by abel
    refine ⟨xStar, ⟨hx, hfy⟩, ?_⟩
    intro z hz
    exact hinj hz.1 hx (hz.2.trans hfy.symm)
  · intro y hy x hx hfx
    have hl := hlower x hx a haBall
    rw [hfx] at hl
    rw [Metric.mem_ball, dist_eq_norm]
    nlinarith
  · intro y z _ _ x_y hxy x_z hxz hfy hfz
    apply (le_div_iff₀ hq).mpr
    have hl := hlower x_y hxy x_z hxz
    rw [hfy, hfz] at hl
    simpa only [mul_comm] using hl

end D04
