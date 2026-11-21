import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Conditioning.BackwardToForward
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Conditioning.Definitions
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Conditioning.Errors
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section

open Filter
open scoped Topology NNReal ENNReal

universe u v w

namespace NumAnalysis206.Conditioning

/-- Differentiability gives a uniform bound on all small increments. -/
private theorem local_norm_bound
    {𝕜 : Type u} [RCLike 𝕜]
    {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type w} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {f : X → Y} {x : X} (hf : DifferentiableAt 𝕜 f x)
    {c : ℝ} (hc : 0 < c) :
    ∃ r : ℝ, 0 < r ∧ ∀ v : X, ‖v‖ ≤ r →
      ‖f (x + v) - f x‖ ≤ (‖fderiv 𝕜 f x‖ + c) * ‖v‖ := by
  have he := hf.hasFDerivAt.isLittleO.bound hc
  obtain ⟨s, hs, hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨s / 2, by positivity, ?_⟩
  intro v hv
  have hmem : x + v ∈ Metric.ball x s := by
    simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    linarith
  have hrem := hball hmem
  change ‖f (x + v) - f x - (fderiv 𝕜 f x) (x + v - x)‖ ≤ c * ‖x + v - x‖ at hrem
  simp only [add_sub_cancel_left] at hrem
  calc
    ‖f (x + v) - f x‖ ≤
        ‖f (x + v) - f x - (fderiv 𝕜 f x) v‖ + ‖(fderiv 𝕜 f x) v‖ :=
      by
        simpa only [sub_add_cancel] using
          (norm_add_le (f (x + v) - f x - (fderiv 𝕜 f x) v) ((fderiv 𝕜 f x) v))
    _ ≤ c * ‖v‖ + ‖fderiv 𝕜 f x‖ * ‖v‖ :=
      add_le_add hrem ((fderiv 𝕜 f x).le_opNorm v)
    _ = (‖fderiv 𝕜 f x‖ + c) * ‖v‖ := by ring

/-- W13: the relative estimate is uniform on a sufficiently small closed ball. -/
theorem actualPerturbation :
    Specs.NumAnalysis206.Conditioning.BackwardToForward.actualPerturbationStatement.{u,v,w} := by
  intro 𝕜 _ X _ _ _ Y _ _ U hU f x hx hf hx0 hfx a ha
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hypos : 0 < ‖f x‖ := norm_pos_iff.mpr hfx
  obtain ⟨r, hr, hbound⟩ := local_norm_bound hf (show 0 < a * ‖f x‖ / ‖x‖ by positivity)
  refine ⟨r, hr, ?_⟩
  intro v hv hvU yhat hyhat
  change ‖yhat - f x‖ / ‖f x‖ ≤
    (‖fderiv 𝕜 f x‖ * ‖x‖ / ‖f x‖ + a) * (‖v‖ / ‖x‖)
  rw [hyhat]
  apply (div_le_iff₀ hypos).2
  calc
    ‖f (x + v) - f x‖ ≤ (‖fderiv 𝕜 f x‖ + a * ‖f x‖ / ‖x‖) * ‖v‖ := hbound v hv
    _ = (‖fderiv 𝕜 f x‖ * ‖x‖ / ‖f x‖ + a) * (‖v‖ / ‖x‖) * ‖f x‖ := by
      field_simp

/-- W13: near feasible sizes yield the same estimate for a small infimum,
even if that infimum is zero or is not attained. -/
theorem backwardInfimum :
    Specs.NumAnalysis206.Conditioning.BackwardToForward.backwardInfimumStatement.{u,v,w} := by
  intro 𝕜 _ X _ _ _ Y _ _ U hU f x hx hf hx0 hfx a ha
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hypos : 0 < ‖f x‖ := norm_pos_iff.mpr hfx
  let K := Specs.NumAnalysis206.Conditioning.relativeConditionNumberValue 𝕜 U hU f x hx hf hx0 hfx
  have hK : 0 ≤ K := by
    change 0 ≤ ‖fderiv 𝕜 f x‖ * ‖x‖ / ‖f x‖
    positivity
  have hC : 0 < K + a := by linarith
  obtain ⟨r, hr, hbound⟩ := actualPerturbation 𝕜 U hU f x hx hf hx0 hfx a ha
  refine ⟨r / ‖x‖, by positivity, ?_⟩
  intro D yhat
  dsimp only
  let b := Specs.NumAnalysis206.Conditioning.Errors.relativeNormwiseBackwardError
    (fun z : U => f z) ⟨x, hx⟩ yhat D ‖x‖₊ (nnnorm_ne_zero_iff.mpr hx0)
  intro hb
  change b < ENNReal.ofReal (r / ‖x‖) at hb
  change Specs.NumAnalysis206.Conditioning.Errors.relativeForwardError
    (fun z : U => f z) ⟨x, hx⟩ yhat ‖f x‖₊ (nnnorm_ne_zero_iff.mpr hfx) ≤ (K + a) * b.toReal
  by_contra hnot
  have hbad := lt_of_not_ge hnot
  have hbsmall := ENNReal.toReal_lt_of_lt_ofReal hb
  have hbdiv : b.toReal <
      Specs.NumAnalysis206.Conditioning.Errors.relativeForwardError
        (fun z : U => f z) ⟨x, hx⟩ yhat ‖f x‖₊ (nnnorm_ne_zero_iff.mpr hfx) / (K + a) := by
    apply (lt_div_iff₀ hC).2
    nlinarith
  obtain ⟨t, hbt, htm⟩ := exists_between (lt_min hbsmall hbdiv)
  have htpos : 0 < t := lt_of_le_of_lt ENNReal.toReal_nonneg hbt
  have hbfin : b ≠ ⊤ := ne_top_of_lt hb
  have hblt : b < ENNReal.ofReal t := (ENNReal.lt_ofReal_iff_toReal_lt hbfin).2 hbt
  obtain ⟨v, hvfeas, hvsize⟩ := exists_feasible_size_lt
    (fun z : U => f z) ⟨x, hx⟩ yhat D
    (Specs.NumAnalysis206.Conditioning.Errors.relativeNormwiseSize ‖x‖₊ (nnnorm_ne_zero_iff.mpr hx0))
    (ENNReal.ofReal t) hblt
  change ((‖v‖₊ / ‖x‖₊ : ℝ≥0) : ℝ≥0∞) < ENNReal.ofReal t at hvsize
  have hvt : ‖v‖ / ‖x‖ < t := by
    simpa only [NNReal.coe_div, coe_nnnorm] using ENNReal.coe_lt_ofReal.mp hvsize
  have hvr : ‖v‖ ≤ r := by
    have := hvt.trans (lt_min_iff.mp htm).1
    exact le_of_lt ((div_lt_div_iff_of_pos_right hxpos).mp this)
  rcases hvfeas with ⟨_, hvU, hfy⟩
  have hlocal := hbound v hvr hvU yhat hfy.symm
  have hupper : (K + a) * (‖v‖ / ‖x‖) <
      Specs.NumAnalysis206.Conditioning.Errors.relativeForwardError
        (fun z : U => f z) ⟨x, hx⟩ yhat ‖f x‖₊ (nnnorm_ne_zero_iff.mpr hfx) := by
    have := (lt_div_iff₀ hC).mp ((lt_min_iff.mp htm).2)
    nlinarith
  exact (not_lt_of_ge hlocal) hupper

end NumAnalysis206.Conditioning
