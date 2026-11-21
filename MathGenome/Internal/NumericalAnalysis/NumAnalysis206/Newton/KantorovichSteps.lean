import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.KantorovichSteps
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Newton.Definitions
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Newton.Majorant
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Newton.SegmentRemainder
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Conditioning.Neumann
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
universe u v w
open Set Metric
namespace NumAnalysis206.Newton

/-- Composing with the fixed inverse preserves the Newton correction. -/
theorem kantorovich_preconditioning :
    Specs.NumAnalysis206.Newton.KantorovichSteps.PreconditioningStatement := by
  intro 𝕜 _ X Y _ _ _ _ _ _ F U x₀ A hU hF hx₀ hA G
  have hd (x : X) (hx : x ∈ U) :
      HasFDerivAt G (A.symm.toContinuousLinearMap.comp (fderiv 𝕜 F x)) x :=
    A.symm.hasFDerivAt.comp x
      ((hF x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · rw [(hd x₀ hx₀).fderiv, hA]
    ext x
    simp
  · intro x hx
    refine ⟨(hd x hx).fderiv, ?_, ?_⟩
    · rw [(hd x hx).fderiv]
      exact ContinuousLinearMap.isInvertible_equiv_comp
    · simp only [Specs.NumAnalysis206.Newton.operatorNewtonValue, (hd x hx).fderiv,
        ContinuousLinearMap.inverse_equiv_comp, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.coe_coe, G,
        ContinuousLinearEquiv.apply_symm_apply]

section Endomorphisms
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- A quantitative Neumann estimate at a finite radius. This also covers the
zero space, since only the inequality for the identity norm is used. -/
lemma inverse_bound_of_near_id (T : X →L[𝕜] X) {r : ℝ}
    (hT : ‖T - ContinuousLinearMap.id 𝕜 X‖ ≤ r) (hr : r < 1) :
    T.IsInvertible ∧ ‖T.inverse‖ ≤ 1 / (1 - r) := by
  let E := T - ContinuousLinearMap.id 𝕜 X
  obtain ⟨u, hu, _, hn⟩ := Conditioning.neumannSeries
    ContinuousLinearMap.norm_id_le E (lt_of_le_of_lt hT hr)
  let e : X ≃L[𝕜] X := ContinuousLinearEquiv.ofUnit u
  have he : e.toContinuousLinearMap = T := by
    change (u : X →L[𝕜] X) = T
    rw [hu]
    change ContinuousLinearMap.id 𝕜 X + (T - ContinuousLinearMap.id 𝕜 X) = T
    abel
  have hi : T.inverse = (↑u⁻¹ : X →L[𝕜] X) := by
    rw [← he, ContinuousLinearMap.inverse_equiv]
    rfl
  refine ⟨⟨e, he⟩, ?_⟩
  rw [hi]
  exact hn.trans (one_div_le_one_div_of_le (by linarith) (by dsimp [E]; linarith))

/-- The Newton equation cancels the affine part exactly. -/
lemma newton_remainder_identity (G : X → X) (z : X)
    (hi : (fderiv 𝕜 G z).IsInvertible) :
    G (operatorNewton (𝕜 := 𝕜) G z) - G z -
      fderiv 𝕜 G z (operatorNewton (𝕜 := 𝕜) G z - z) =
        G (operatorNewton (𝕜 := 𝕜) G z) := by
  have hs : operatorNewton (𝕜 := 𝕜) G z - z = -(fderiv 𝕜 G z).inverse (G z) := by
    change z - (fderiv 𝕜 G z).inverse (G z) - z = _
    abel
  rw [hs, map_neg, hi.self_apply_inverse]
  abel

end Endomorphisms

open Majorant

/-- Finite Newton steps are justified by simultaneous radius and residual
majorization. In particular, no inverse at the limiting radius is used. -/
theorem kantorovich_steps : Specs.NumAnalysis206.Newton.KantorovichSteps.Statement := by
  intro 𝕜 _ X Y _ _ _ _ _ _ F U x₀ A η L hU hF hx₀ hA hη hL hb hres hball hLip G x
  let : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
  have hp := kantorovich_preconditioning 𝕜 X Y F U x₀ A hU hF hx₀ hA
  have hGD : DifferentiableOn 𝕜 G U := hp.1
  have hG₀ : fderiv 𝕜 G x₀ = ContinuousLinearMap.id 𝕜 X := hp.2.1
  have hGLip : ∀ z ∈ closedBall x₀ (lowerRoot η L),
      ∀ y ∈ closedBall x₀ (lowerRoot η L),
      ‖fderiv 𝕜 G z - fderiv 𝕜 G y‖ ≤ L * ‖z - y‖ := by
    intro z hz y hy
    rw [(hp.2.2 z (hball hz)).1, (hp.2.2 y (hball hy)).1,
      ← ContinuousLinearMap.comp_sub]
    exact hLip z hz y hy
  have hmem (n : ℕ) (z : X) (hz : ‖z - x₀‖ ≤ iterate η L n) :
      z ∈ closedBall x₀ (lowerRoot η L) := by
    rw [mem_closedBall, dist_eq_norm]
    exact hz.trans (iterate_bounds hη hL hb n).2.le
  have hInv (n : ℕ) (z : X) (hz : ‖z - x₀‖ ≤ iterate η L n) :
      (fderiv 𝕜 G z).IsInvertible ∧
      ‖(fderiv 𝕜 G z).inverse‖ ≤ 1 / (1 - L * iterate η L n) := by
    apply inverse_bound_of_near_id
    · rw [← hG₀]
      exact (hGLip z (hmem n z hz) x₀ (by
        rw [mem_closedBall, dist_self]
        exact (root_data hη hL hb).2.2.2.2.1.le)).trans
          (mul_le_mul_of_nonneg_left hz hL.le)
    · have hd := (iterate_properties hη hL hb n).2.2.2.1
      linarith
  have hStep (n : ℕ) (z : X) (hz : ‖z - x₀‖ ≤ iterate η L n)
      (hr : ‖G z‖ ≤ majorant η L (iterate η L n)) :
      ‖operatorNewton (𝕜 := 𝕜) G z - z‖ ≤ iterate η L (n + 1) - iterate η L n := by
    have hi := hInv n z hz
    have hden := (iterate_properties hη hL hb n).2.2.2.1
    have heq : operatorNewton (𝕜 := 𝕜) G z - z = -(fderiv 𝕜 G z).inverse (G z) := by
      change z - (fderiv 𝕜 G z).inverse (G z) - z = _
      abel
    calc
      ‖operatorNewton (𝕜 := 𝕜) G z - z‖ = ‖(fderiv 𝕜 G z).inverse (G z)‖ := by
        rw [heq, norm_neg]
      _ ≤ ‖(fderiv 𝕜 G z).inverse‖ * ‖G z‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (1 / (1 - L * iterate η L n)) * majorant η L (iterate η L n) :=
        mul_le_mul hi.2 hr (norm_nonneg _) (by positivity)
      _ = iterate η L (n + 1) - iterate η L n := by
        change _ = newtonStep η L (iterate η L n) - iterate η L n
        rw [step_add]
        ring
  have hrec (n : ℕ) (hx : x n ∈ U) :
      x (n + 1) = operatorNewton (𝕜 := 𝕜) G (x n) := by
    change x (n + 1) = Specs.NumAnalysis206.Newton.operatorNewtonValue (𝕜 := 𝕜) G (x n)
    rw [(hp.2.2 (x n) hx).2.2]
    exact operatorNewtonIterates_succ F x₀ n
  have hmajor : ∀ n, ‖x n - x₀‖ ≤ iterate η L n ∧
      ‖G (x n)‖ ≤ majorant η L (iterate η L n) := by
    intro n
    induction n with
    | zero =>
      change ‖x₀ - x₀‖ ≤ 0 ∧ ‖G x₀‖ ≤ majorant η L 0
      simpa [majorant] using (And.intro (le_refl (0 : ℝ)) hres)
    | succ n ih =>
      have hm := hmem n (x n) ih.1
      have hi := (hInv n (x n) ih.1).1
      have hs := hStep n (x n) ih.1 ih.2
      have hnext := hrec n (hball hm)
      rw [← hnext] at hs
      have hnrad : ‖x (n + 1) - x₀‖ ≤ iterate η L (n + 1) := by
        calc
          ‖x (n + 1) - x₀‖ ≤ ‖x (n + 1) - x n‖ + ‖x n - x₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ (iterate η L (n + 1) - iterate η L n) + iterate η L n := add_le_add hs ih.1
          _ = iterate η L (n + 1) := sub_add_cancel _ _
      refine ⟨hnrad, ?_⟩
      have hnmem := hmem (n + 1) (x (n + 1)) hnrad
      have hrem := segment_remainder 𝕜 X X G U (closedBall x₀ (lowerRoot η L)) L
        hU hGD hball (convex_closedBall x₀ _) hL.le hGLip
        (x n) hm (x (n + 1)) hnmem
      have hcancel : G (x (n + 1)) - G (x n) -
          fderiv 𝕜 G (x n) (x (n + 1) - x n) = G (x (n + 1)) := by
        rw [hnext]
        exact newton_remainder_identity G (x n) hi
      rw [hcancel] at hrem
      calc
        ‖G (x (n + 1))‖ ≤ (L / 2) * ‖x (n + 1) - x n‖ ^ 2 := hrem
        _ ≤ (L / 2) * (iterate η L (n + 1) - iterate η L n) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ (norm_nonneg _) hs 2
        _ = majorant η L (iterate η L (n + 1)) :=
          ((iterate_properties hη hL hb n).2.2.2.2.2.2.2.1).symm
  refine ⟨hGD, hG₀, hGLip, fun z hz => (hp.2.2 z hz).2, ?_⟩
  intro n
  have hm := hmajor n
  have hxU := hball (hmem n (x n) hm.1)
  have hi := hInv n (x n) hm.1
  refine ⟨⟨hxU, (hF (x n) hxU).differentiableAt (hU.mem_nhds hxU),
    ((hp.2.2 (x n) hxU).2.1).mp hi.1⟩, hi.1, hm.1,
    (iterate_bounds hη hL hb n).2, hm.2, hi.2, ?_⟩
  rw [hrec n hxU]
  exact hStep n (x n) hm.1 hm.2

end NumAnalysis206.Newton
