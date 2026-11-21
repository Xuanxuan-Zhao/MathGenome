import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PrimitiveStieltjesEndpoint
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.RectifiableStieltjes
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open Set
open scoped BigOperators ENNReal

set_option maxHeartbeats 800000

namespace D12Complex.PrimitiveStieltjesEndpoint

/-- A uniform first-order remainder estimate on a compact subset of the open
domain. A fixed compact tube supplies uniform continuity of the derivative.
The mean-value inequality used here is the real-segment inequality, also for
complex derivatives; it does not assert a complex mean-value equality. -/
theorem uniform_remainder (Ω K : Set ℂ) (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (f F : ℂ → ℂ)
    (hf : ContinuousOn f Ω) (hF : ∀ z ∈ Ω, HasDerivAt F (f z) z)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ K, ∀ w ∈ K, ‖w - z‖ < δ →
      ‖F w - F z - f z * (w - z)‖ ≤ ε * ‖w - z‖ := by
  obtain ⟨r, hr, hrΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  have hT : IsCompact (Metric.cthickening r K) := hK.cthickening
  obtain ⟨d, hd, hdcont⟩ := Metric.uniformContinuousOn_iff.mp
    (hT.uniformContinuousOn_of_continuous (hf.mono hrΩ)) ε hε
  refine ⟨min r d, lt_min hr hd, ?_⟩
  intro z hz w _hw hzw
  have hzT : z ∈ Metric.cthickening r K := Metric.self_subset_cthickening K hz
  have hball : segment ℝ z w ⊆ Metric.ball z (min r d) :=
    (convex_ball z (min r d)).segment_subset
      (Metric.mem_ball_self (lt_min hr hd)) (by simpa [dist_eq_norm] using hzw)
  have hvT : ∀ v ∈ segment ℝ z w, v ∈ Metric.cthickening r K := by
    intro v hv
    exact Metric.mem_cthickening_of_dist_le v z r K hz
      ((hball hv).le.trans (min_le_left _ _))
  have hder : ∀ v ∈ segment ℝ z w,
      HasDerivWithinAt (fun x => F x - f z * x) (f v - f z) (segment ℝ z w) v := by
    intro v hv
    simpa using! ((hF v (hrΩ (hvT v hv))).sub
      ((hasDerivAt_id v).const_mul (f z))).hasDerivWithinAt
  have hbound : ∀ v ∈ segment ℝ z w, ‖f v - f z‖ ≤ ε := by
    intro v hv
    simpa only [dist_eq_norm] using
      (hdcont v (hvT v hv) z hzT ((hball hv).trans_le (min_le_right _ _))).le
  have h := (convex_segment z w : Convex ℝ (segment ℝ z w)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hder hbound (left_mem_segment ℝ z w) (right_mem_segment ℝ z w)
  convert h using 1; congr 1; ring

/-- The tagged sums converge for every fine partition and every independent
closed-cell tagging. Finite variation controls the sum of the local errors. -/
theorem hasIntegral_endpoint :
    Specs.D12Complex.Ch03.PrimitiveStieltjesEndpoint.hasIntegral_endpoint_type := by
  intro Ω hΩ f F hf hF γ hγ htrace ε hε
  classical
  have hK : IsCompact γ.trace := isCompact_Icc.image_of_continuousOn γ.continuousOn
  let V := (Stieltjes.totalVariation γ γ.a γ.b).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  let η := ε / (2 * (V + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨d, hd, hrem⟩ := uniform_remainder Ω γ.trace hΩ hK htrace f F hf hF hη
  obtain ⟨δ₁, hδ₁, hcellγ⟩ := SingleVariableAnalysis.Stieltjes.continuous_cell_oscillation
    (γ : ℝ → ℂ) γ.continuousOn (half_pos hd)
  have hfc : ContinuousOn (f ∘ γ) (Icc γ.a γ.b) :=
    hf.comp γ.continuousOn (fun x hx => htrace ⟨x, hx, rfl⟩)
  obtain ⟨δ₂, hδ₂, hcellf⟩ :=
    SingleVariableAnalysis.Stieltjes.continuous_cell_oscillation (f ∘ γ) hfc hη
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro P hP t
  have hP₁ := hP.trans_le (min_le_left δ₁ δ₂)
  have hP₂ := hP.trans_le (min_le_right δ₁ δ₂)
  have hmem (j : Fin (P.n + 1)) : P.point j ∈ Icc γ.a γ.b :=
    (SingleVariableAnalysis.Riemann.endpoints P).2.2 _
      (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  have hinc (i : Fin P.n) : P.point i.castSucc ≤ P.point i.succ :=
    P.strictMono.monotone (Fin.castSucc_le_succ i)
  have herror (i : Fin P.n) :
      ‖f (γ (t i)) * (γ (P.point i.succ) - γ (P.point i.castSucc)) -
          (F (γ (P.point i.succ)) - F (γ (P.point i.castSucc)))‖ ≤
        (2 * η) * ‖γ (P.point i.succ) - γ (P.point i.castSucc)‖ := by
    have hl : P.point i.castSucc ∈ Icc (P.point i.castSucc) (P.point i.succ) :=
      ⟨le_rfl, hinc i⟩
    have hr : P.point i.succ ∈ Icc (P.point i.castSucc) (P.point i.succ) :=
      ⟨hinc i, le_rfl⟩
    have hclose : ‖γ (P.point i.succ) - γ (P.point i.castSucc)‖ < d :=
      (hcellγ P hP₁ i _ hr _ hl).trans_lt (half_lt_self hd)
    have hR := hrem _ ⟨_, hmem i.castSucc, rfl⟩ _ ⟨_, hmem i.succ, rfl⟩ hclose
    have htag : ‖f (γ (t i)) - f (γ (P.point i.castSucc))‖ ≤ η :=
      hcellf P hP₂ i _ (t i).property _ hl
    calc
      _ = ‖(f (γ (t i)) - f (γ (P.point i.castSucc))) *
            (γ (P.point i.succ) - γ (P.point i.castSucc)) -
          (F (γ (P.point i.succ)) - F (γ (P.point i.castSucc)) -
            f (γ (P.point i.castSucc)) *
              (γ (P.point i.succ) - γ (P.point i.castSucc)))‖ := by congr 1; ring
      _ ≤ ‖(f (γ (t i)) - f (γ (P.point i.castSucc))) *
            (γ (P.point i.succ) - γ (P.point i.castSucc))‖ +
          ‖F (γ (P.point i.succ)) - F (γ (P.point i.castSucc)) -
            f (γ (P.point i.castSucc)) *
              (γ (P.point i.succ) - γ (P.point i.castSucc))‖ := norm_sub_le _ _
      _ ≤ η * ‖γ (P.point i.succ) - γ (P.point i.castSucc)‖ +
          η * ‖γ (P.point i.succ) - γ (P.point i.castSucc)‖ := by
        rw [norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right htag (norm_nonneg _)) hR
      _ = _ := by ring
  have htel : (∑ i : Fin P.n,
      (F (γ (P.point i.succ)) - F (γ (P.point i.castSucc)))) =
        F γ.target - F γ.source := by
    simpa only [P.first, P.last, ComplexPath.source, ComplexPath.target] using
      SingleVariableAnalysis.Stieltjes.sum_fin_increments (fun j => F (γ (P.point j)))
  have hv : (∑ i : Fin P.n, ‖γ (P.point i.succ) - γ (P.point i.castSucc)‖) ≤ V := by
    have hfin : Stieltjes.totalVariation γ γ.a γ.b < ⊤ := hγ
    have h := ENNReal.toReal_mono (ne_of_lt hfin)
      (le_iSup (fun Q : Stieltjes.Partition γ.a γ.b =>
        ∑ i : Fin Q.n, ENNReal.ofReal ‖γ (Q.point i.succ) - γ (Q.point i.castSucc)‖) P)
    simpa [V, Stieltjes.totalVariation, ENNReal.toReal_sum, ENNReal.toReal_ofReal] using h
  have hηV : (2 * η) * (V + 1) = ε := by
    dsimp [η]
    have hden : 2 * (V + 1) ≠ 0 := by positivity
    have hh := div_mul_cancel₀ ε hden
    nlinarith
  calc
    ‖Stieltjes.taggedSum P t (f ∘ γ) γ - (F γ.target - F γ.source)‖ =
        ‖∑ i : Fin P.n,
          (f (γ (t i)) * (γ (P.point i.succ) - γ (P.point i.castSucc)) -
            (F (γ (P.point i.succ)) - F (γ (P.point i.castSucc))))‖ := by
      rw [Finset.sum_sub_distrib, htel]
      rfl
    _ ≤ ∑ i : Fin P.n,
        ‖f (γ (t i)) * (γ (P.point i.succ) - γ (P.point i.castSucc)) -
          (F (γ (P.point i.succ)) - F (γ (P.point i.castSucc)))‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin P.n, (2 * η) *
        ‖γ (P.point i.succ) - γ (P.point i.castSucc)‖ :=
      Finset.sum_le_sum (fun i _ => herror i)
    _ = (2 * η) * ∑ i : Fin P.n,
        ‖γ (P.point i.succ) - γ (P.point i.castSucc)‖ := (Finset.mul_sum ..).symm
    _ ≤ (2 * η) * V := mul_le_mul_of_nonneg_left hv (by positivity)
    _ < ε := by nlinarith

/-- The canonical contour integral equals the primitive's endpoint increment. -/
theorem contourIntegral_endpoint :
    Specs.D12Complex.Ch03.PrimitiveStieltjesEndpoint.contourIntegral_endpoint_type := by
  intro Ω hΩ f F hf hF γ hγ htrace
  exact Stieltjes.integral_eq_of_hasIntegral γ.ordered
    (hasIntegral_endpoint Ω hΩ f F hf hF γ hγ htrace)

end D12Complex.PrimitiveStieltjesEndpoint
