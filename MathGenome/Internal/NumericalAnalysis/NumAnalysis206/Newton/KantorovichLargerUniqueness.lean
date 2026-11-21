import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.KantorovichLargerUniqueness
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Newton.KantorovichRatesUniqueness
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Newton.SegmentRemainder

noncomputable section
universe u v w
open Set Metric Filter
namespace NumAnalysis206.Newton
open Majorant

/-- Taylor's estimate excludes the annulus between the majorant roots, so the
small-ball uniqueness theorem gives uniqueness on the stipulated larger ball. -/
theorem kantorovich_larger_uniqueness :
    Specs.NumAnalysis206.Newton.KantorovichLargerUniqueness.Statement := by
  intro 𝕜 _ X Y _ _ _ _ _ _ F U x₀ A η L ρ hU hF hx₀ hA hη hL hb hres
    hρ hρupper hball hLip
  let : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
  let G : X → X := fun z => A.symm (F z)
  have hp := kantorovich_preconditioning 𝕜 X Y F U x₀ A hU hF hx₀ hA
  have hsmall : closedBall x₀ (lowerRoot η L) ⊆ closedBall x₀ ρ :=
    closedBall_subset_closedBall hρ
  have hsmallU : closedBall x₀ (lowerRoot η L) ⊆ U := hsmall.trans hball
  have hsmallLip : ∀ z ∈ closedBall x₀ (lowerRoot η L),
      ∀ y ∈ closedBall x₀ (lowerRoot η L),
      ‖A.symm.toContinuousLinearMap.comp (fderiv 𝕜 F z - fderiv 𝕜 F y)‖ ≤
        L * ‖z - y‖ := fun z hz y hy => hLip z (hsmall hz) y (hsmall hy)
  have hGLip : ∀ z ∈ closedBall x₀ ρ, ∀ y ∈ closedBall x₀ ρ,
      ‖fderiv 𝕜 G z - fderiv 𝕜 G y‖ ≤ L * ‖z - y‖ := by
    intro z hz y hy
    rw [(hp.2.2 z (hball hz)).1, (hp.2.2 y (hball hy)).1,
      ← ContinuousLinearMap.comp_sub]
    exact hLip z hz y hy
  have hxball : x₀ ∈ closedBall x₀ ρ := by
    rw [mem_closedBall, dist_self]
    exact ((root_data hη hL hb.le).2.2.2.2.1.le).trans hρ
  have hradius (y : X) (hy : y ∈ closedBall x₀ ρ) (hFy : F y = 0) :
      0 ≤ majorant η L ‖y - x₀‖ ∧ ‖y - x₀‖ ≤ lowerRoot η L := by
    have hGy : G y = 0 := by simp [G, hFy]
    have hrem := segment_remainder 𝕜 X X G U (closedBall x₀ ρ) L
      hU hp.1 hball (convex_closedBall x₀ _) hL.le hGLip x₀ hxball y hy
    have heq : G y - G x₀ - fderiv 𝕜 G x₀ (y - x₀) =
        -(G x₀ + (y - x₀)) := by
      rw [hGy, hp.2.1]
      simp only [ContinuousLinearMap.id_apply]
      abel
    rw [heq, norm_neg] at hrem
    have hnorm : ‖y - x₀‖ ≤ ‖G x₀ + (y - x₀)‖ + η := by
      calc
        ‖y - x₀‖ = ‖(G x₀ + (y - x₀)) - G x₀‖ := by congr 1; abel
        _ ≤ ‖G x₀ + (y - x₀)‖ + ‖G x₀‖ := norm_sub_le _ _
        _ ≤ ‖G x₀ + (y - x₀)‖ + η := add_le_add_right hres _
    have hm : 0 ≤ majorant η L ‖y - x₀‖ := by
      unfold majorant
      linarith
    refine ⟨hm, ?_⟩
    have hs : ‖y - x₀‖ < upperRoot η L :=
      (by simpa only [mem_closedBall, dist_eq_norm] using hy : ‖y - x₀‖ ≤ ρ).trans_lt hρupper
    by_contra hn
    have hneg := (strict_case hη hL hb).2 ‖y - x₀‖ (lt_of_not_ge hn) hs
    linarith
  refine ⟨hradius, ?_⟩
  obtain ⟨p, hpmem, hFp, hlim, huniq, _⟩ :=
    (kantorovich_rates_uniqueness 𝕜 X Y F U x₀ A η L
      hU hF hx₀ hA hη hL hb.le hres hsmallU hsmallLip).2
  refine ⟨p, hpmem, hFp, hlim, ?_⟩
  intro y hy hFy
  apply huniq y _ hFy
  rw [mem_closedBall, dist_eq_norm]
  exact (hradius y hy hFy).2

end NumAnalysis206.Newton
