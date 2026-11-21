import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.KantorovichRatesUniqueness
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Newton.KantorovichExistence
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Newton.SegmentRemainder

noncomputable section
universe u v w
open Set Metric Filter
namespace NumAnalysis206.Newton

/-- Applying the inverse finite-iterate derivative to the Taylor remainder
at a zero gives the Newton error, up to sign. -/
lemma newton_zero_error_identity {𝕜 : Type u} [RCLike 𝕜]
    {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    (G : X → X) (z y : X) (hy : G y = 0)
    (hi : (fderiv 𝕜 G z).IsInvertible) :
    y - operatorNewton (𝕜 := 𝕜) G z =
      -(fderiv 𝕜 G z).inverse (G y - G z - fderiv 𝕜 G z (y - z)) := by
  rw [hy, zero_sub, map_sub, map_neg, hi.inverse_apply_self]
  change y - (z - (fderiv 𝕜 G z).inverse (G z)) = _
  abel

open Majorant

/-- Rates and uniqueness on the closed Kantorovich ball, including the
critical double-root parameter. Only finite-iterate inverses are used. -/
theorem kantorovich_rates_uniqueness :
    Specs.NumAnalysis206.Newton.KantorovichRatesUniqueness.Statement := by
  intro 𝕜 _ X Y _ _ _ _ _ _ F U x₀ A η L hU hF hx₀ hA hη hL hb hres hball hLip x
  let : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
  let G : X → X := fun z => A.symm (F z)
  have hs := kantorovich_steps 𝕜 X Y F U x₀ A η L
    hU hF hx₀ hA hη hL hb hres hball hLip
  have hxmem (n : ℕ) : x n ∈ closedBall x₀ (lowerRoot η L) := by
    rw [mem_closedBall, dist_eq_norm]
    exact ((hs.2.2.2.2 n).2.2.1).trans ((hs.2.2.2.2 n).2.2.2.1).le
  have hrec (n : ℕ) : x (n + 1) = operatorNewton (𝕜 := 𝕜) G (x n) := by
    change x (n + 1) = Specs.NumAnalysis206.Newton.operatorNewtonValue (𝕜 := 𝕜) G (x n)
    rw [(hs.2.2.2.1 (x n) (hball (hxmem n))).2]
    exact operatorNewtonIterates_succ F x₀ n
  have hquad (y : X) (hy : y ∈ closedBall x₀ (lowerRoot η L)) (hFy : F y = 0)
      (n : ℕ) : ‖y - x (n + 1)‖ ≤ coefficient η L n * ‖y - x n‖ ^ 2 := by
    have hden := (iterate_properties hη hL hb n).2.2.2.1
    have hGy : G y = 0 := by simp [G, hFy]
    have hi := (hs.2.2.2.2 n).2.1
    have hinv := (hs.2.2.2.2 n).2.2.2.2.2.1
    have hrem := segment_remainder 𝕜 X X G U (closedBall x₀ (lowerRoot η L)) L
      hU hs.1 hball (convex_closedBall x₀ _) hL.le hs.2.2.1 (x n) (hxmem n) y hy
    calc
      ‖y - x (n + 1)‖ = ‖(fderiv 𝕜 G (x n)).inverse
          (G y - G (x n) - fderiv 𝕜 G (x n) (y - x n))‖ := by
        rw [hrec, newton_zero_error_identity G (x n) y hGy hi, norm_neg]
      _ ≤ ‖(fderiv 𝕜 G (x n)).inverse‖ *
          ‖G y - G (x n) - fderiv 𝕜 G (x n) (y - x n)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (1 / (1 - L * iterate η L n)) * ((L / 2) * ‖y - x n‖ ^ 2) :=
        mul_le_mul hinv hrem (norm_nonneg _) (by positivity)
      _ = coefficient η L n * ‖y - x n‖ ^ 2 := by
        unfold coefficient
        field_simp
  have herror (y : X) (hy : y ∈ closedBall x₀ (lowerRoot η L)) (hFy : F y = 0) :
      ∀ n : ℕ, ‖y - x n‖ ≤ error η L n := by
    intro n
    induction n with
    | zero =>
      change ‖y - x₀‖ ≤ lowerRoot η L - 0
      simpa only [sub_zero, mem_closedBall, dist_eq_norm] using hy
    | succ n ih =>
      have hp := iterate_properties hη hL hb n
      calc
        ‖y - x (n + 1)‖ ≤ coefficient η L n * ‖y - x n‖ ^ 2 := hquad y hy hFy n
        _ ≤ coefficient η L n * error η L n ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ih 2)
            hp.2.2.2.2.2.2.1.le
        _ = error η L (n + 1) := hp.2.2.2.2.2.2.2.2.1.symm
  refine ⟨fun y hy hFy => ⟨hquad y hy hFy, herror y hy hFy⟩, ?_⟩
  obtain ⟨_, _, p, hpmem, hFp, hlim, _⟩ := kantorovich_existence 𝕜 X Y F U x₀ A η L
    hU hF hx₀ hA hη hL hb hres hball hLip
  refine ⟨p, hpmem, hFp, hlim, ?_, ?_, ?_⟩
  · intro y hy hFy
    have ht : Tendsto (error η L) atTop (nhds 0) := by
      change Tendsto (fun n => lowerRoot η L - iterate η L n) atTop (nhds 0)
      simpa only [sub_self] using
        (tendsto_const_nhds (x := lowerRoot η L)).sub (iterate_tendsto hη hL hb)
    have hz : Tendsto (fun n => ‖y - x n‖) atTop (nhds 0) :=
      squeeze_zero (fun n => norm_nonneg _) (herror y hy hFy) ht
    have heq : ‖y - p‖ = 0 :=
      tendsto_nhds_unique ((tendsto_const_nhds.sub hlim).norm) hz
    exact sub_eq_zero.mp (norm_eq_zero.mp heq)
  · intro n
    have hp := iterate_properties hη hL hb n
    have he := herror p hpmem hFp n
    calc
      ‖p - x (n + 1)‖ ≤ coefficient η L n * ‖p - x n‖ ^ 2 := hquad p hpmem hFp n
      _ = (coefficient η L n * ‖p - x n‖) * ‖p - x n‖ := by ring
      _ ≤ (coefficient η L n * error η L n) * ‖p - x n‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left he hp.2.2.2.2.2.2.1.le) (norm_nonneg _)
      _ ≤ (1 / 2) * ‖p - x n‖ :=
        mul_le_mul_of_nonneg_right hp.2.2.2.2.2.2.2.2.2.1 (norm_nonneg _)
  · intro hb' n
    have hd : 0 < discriminant η L := Real.sqrt_pos.mpr (by linarith)
    exact (hquad p hpmem hFp n).trans
      (mul_le_mul_of_nonneg_right
        ((iterate_properties hη hL hb n).2.2.2.2.2.2.2.2.2.2 hd) (sq_nonneg _))

end NumAnalysis206.Newton
