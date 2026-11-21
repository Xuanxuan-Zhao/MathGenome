import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Conditioning.Definitions
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Conditioning.WorstCase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Abel

universe u v w
namespace NumAnalysis206.Conditioning
open Filter Metric Set
open scoped Topology
open Specs.NumAnalysis206.Conditioning (outputNorms worstCase relativeWorstCase)

section Core
variable {𝕜 : Type u} [RCLike 𝕜]
  {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {Y : Type w} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  {f : X → Y} {x : X} {L : X →L[𝕜] Y}

/-- Differentiability controls the remainder uniformly on a small closed ball. -/
theorem remainder_small (hf : HasFDerivAt f L x) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ v, ‖v‖ ≤ δ → ‖f (x + v) - f x - L v‖ ≤ ε * ‖v‖ := by
  have h := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hf).bound hε
  obtain ⟨a, ha, hb⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨a / 2, by positivity, fun v hv => hb ?_⟩
  simpa only [dist_zero_right] using lt_of_le_of_lt hv (by linarith : a / 2 < a)

/-- A canonical (locally finite) remainder modulus. -/
noncomputable def remainderModulus (f : X → Y) (x : X) (L : X →L[𝕜] Y) (r : ℝ) : ℝ :=
  sSup ((fun v => ‖f (x + v) - f x - L v‖ / ‖v‖) '' closedBall 0 r)

/-- A pointwise remainder bound bounds its supremum and certifies finiteness. -/
theorem modulus_bounds {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 ≤ ε)
    (h : ∀ v, ‖v‖ ≤ r → ‖f (x + v) - f x - L v‖ ≤ ε * ‖v‖) :
    0 ≤ remainderModulus f x L r ∧ remainderModulus f x L r ≤ ε ∧
    (∀ v, ‖v‖ ≤ r → ‖f (x + v) - f x - L v‖ ≤ remainderModulus f x L r * ‖v‖) := by
  let S := (fun v => ‖f (x + v) - f x - L v‖ / ‖v‖) '' closedBall 0 r
  have hzero : (0 : ℝ) ∈ S := by
    exact ⟨0, by simpa using hr, by simp⟩
  have hle : ∀ z ∈ S, z ≤ ε := by
    rintro _ ⟨v, hv, rfl⟩
    by_cases hv0 : v = 0
    · simpa [hv0] using hε
    · exact (div_le_iff₀ (norm_pos_iff.mpr hv0)).mpr (h v (by simpa using hv))
  have hbd : BddAbove S := ⟨ε, hle⟩
  have hnonneg : 0 ≤ sSup S := le_csSup hbd hzero
  refine ⟨hnonneg, csSup_le ⟨0, hzero⟩ hle, ?_⟩
  intro v hv
  by_cases hv0 : v = 0
  · simp [hv0]
  · apply (div_le_iff₀ (norm_pos_iff.mpr hv0)).mp
    exact le_csSup hbd ⟨v, by simpa using hv, rfl⟩

/-- The chosen modulus tends to zero as the radius decreases to zero. -/
theorem remainderModulus_tendsto (hf : HasFDerivAt f L x) :
    Tendsto (remainderModulus f x L) (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhdsWithin_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := remainder_small hf (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrd
  have hrδ : r ≤ δ := by
    have : |r| < δ := by simpa only [Real.dist_eq, sub_zero] using hrd
    exact (le_abs_self r).trans this.le
  have hm := modulus_bounds hr.le (half_pos hε).le (fun v hv => hb v (hv.trans hrδ))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hm.1]
  exact hm.2.1.trans_lt (by linarith)

/-- A uniform remainder bound makes the output supremum finite. -/
theorem output_bdd_of_remainder {r ε : ℝ} (_hr : 0 ≤ r) (hε : 0 ≤ ε)
    (h : ∀ v, ‖v‖ ≤ r → ‖f (x + v) - f x - L v‖ ≤ ε * ‖v‖) :
    BddAbove (outputNorms f x r) := by
  refine ⟨(‖L‖ + ε) * r, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  have hv' : ‖v‖ ≤ r := by simpa using hv
  calc
    ‖f (x + v) - f x‖ = ‖(f (x + v) - f x - L v) + L v‖ := by rw [sub_add_cancel]
    _ ≤ ‖f (x + v) - f x - L v‖ + ‖L v‖ := norm_add_le _ _
    _ ≤ ε * ‖v‖ + ‖L‖ * ‖v‖ := add_le_add (h v hv') (L.le_opNorm v)
    _ = (‖L‖ + ε) * ‖v‖ := by ring
    _ ≤ (‖L‖ + ε) * r := mul_le_mul_of_nonneg_left hv' (add_nonneg (norm_nonneg _) hε)

theorem zero_mem_outputNorms {r : ℝ} (hr : 0 ≤ r) : 0 ∈ outputNorms f x r := by
  exact ⟨0, by simpa using hr, by simp⟩

theorem worstCase_nonneg {r : ℝ} (hr : 0 < r) (hb : BddAbove (outputNorms f x r)) :
    0 ≤ worstCase f x r :=
  div_nonneg (le_csSup hb (zero_mem_outputNorms hr.le)) hr.le

/-- The two sides of the operator norm are recovered from perturbations
`r • w`, uniformly over all unit vectors, without choosing a maximizer. -/
theorem worstCase_error {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε)
    (h : ∀ v, ‖v‖ ≤ r → ‖f (x + v) - f x - L v‖ ≤ ε * ‖v‖) :
    |worstCase f x r - ‖L‖| ≤ ε := by
  have hb := output_bdd_of_remainder hr.le hε h
  have hK := worstCase_nonneg hr hb
  have hupper : worstCase f x r ≤ ‖L‖ + ε := by
    apply (div_le_iff₀ hr).mpr
    apply csSup_le ⟨0, zero_mem_outputNorms hr.le⟩
    rintro _ ⟨v, hv, rfl⟩
    have hv' : ‖v‖ ≤ r := by simpa using hv
    calc
      ‖f (x + v) - f x‖ = ‖(f (x + v) - f x - L v) + L v‖ := by rw [sub_add_cancel]
      _ ≤ ‖f (x + v) - f x - L v‖ + ‖L v‖ := norm_add_le _ _
      _ ≤ ε * ‖v‖ + ‖L‖ * ‖v‖ := add_le_add (h v hv') (L.le_opNorm v)
      _ = (‖L‖ + ε) * ‖v‖ := by ring
      _ ≤ (‖L‖ + ε) * r := mul_le_mul_of_nonneg_left hv' (add_nonneg (norm_nonneg _) hε)
  have hlower : ‖L‖ ≤ worstCase f x r + ε := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (add_nonneg hK hε)
    intro w hw
    let v : X := (algebraMap ℝ 𝕜 r) • w
    have hv : ‖v‖ = r := by simp [v, norm_smul, hw, abs_of_pos hr]
    have hLv : ‖L v‖ = r * ‖L w‖ := by simp [v, norm_smul, abs_of_pos hr]
    have hsup : ‖f (x + v) - f x‖ ≤ sSup (outputNorms f x r) :=
      le_csSup hb ⟨v, by simpa using hv.le, rfl⟩
    have htri : ‖L v‖ ≤ ‖f (x + v) - f x‖ + ‖f (x + v) - f x - L v‖ := by
      calc
        ‖L v‖ = ‖(f (x + v) - f x) - (f (x + v) - f x - L v)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    have hrem := h v hv.le
    rw [hv] at hrem
    rw [hLv] at htri
    have hcancel : worstCase f x r * r = sSup (outputNorms f x r) :=
      div_mul_cancel₀ _ hr.ne'
    nlinarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- An open domain contains all sufficiently small closed perturbation balls. -/
theorem small_domain {U : Set X} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ δ > 0, ∀ v, ‖v‖ ≤ δ → x + v ∈ U := by
  obtain ⟨a, ha, hb⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  refine ⟨a / 2, by positivity, ?_⟩
  intro v hv
  apply hb
  simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left] using
    lt_of_le_of_lt hv (by linarith : a / 2 < a)

end Core

/-- Local finiteness, together with the domain condition for all perturbations. -/
theorem local_bounded : Specs.NumAnalysis206.Conditioning.LocalBoundedType.{u, v, w} := by
  intro 𝕜 _ X _ _ _ Y _ _ U hU f x hx hf
  obtain ⟨a, ha, hdom⟩ := small_domain hU hx
  obtain ⟨b, hb, hrem⟩ := remainder_small hf.hasFDerivAt (ε := 1) zero_lt_one
  refine ⟨min a b, lt_min ha hb, ?_⟩
  intro r hr hrd
  have hball := fun v (hv : ‖v‖ ≤ r) => hrem v (hv.trans (hrd.trans (min_le_right _ _)))
  have hbd := output_bdd_of_remainder hr.le zero_le_one hball
  exact ⟨fun v hv => hdom v (hv.trans (hrd.trans (min_le_left _ _))),
    hbd, worstCase_nonneg hr hbd⟩

/-- The uniform modulus controls both the remainder and the worst-case gain. -/
theorem uniform_remainder : Specs.NumAnalysis206.Conditioning.UniformRemainderType.{u, v, w} := by
  intro 𝕜 _ X _ _ _ Y _ _ U _hU f x _hx hf
  obtain ⟨δ, hδ, hb⟩ := remainder_small hf.hasFDerivAt (ε := 1) zero_lt_one
  refine ⟨remainderModulus f x (fderiv 𝕜 f x), δ, hδ,
    remainderModulus_tendsto hf.hasFDerivAt, ?_⟩
  intro r hr hrd
  have hm := modulus_bounds hr.le zero_le_one (fun v hv => hb v (hv.trans hrd))
  exact ⟨hm.1, hm.2.2, worstCase_error hr hm.1 hm.2.2⟩

/-- Absolute worst-case amplification converges to the derivative norm. -/
theorem worst_case_limit : Specs.NumAnalysis206.Conditioning.WorstCaseLimitType.{u, v, w} := by
  intro 𝕜 _ X _ _ _ Y _ _ U _hU f x _hx hf
  apply Metric.tendsto_nhdsWithin_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := remainder_small hf.hasFDerivAt (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrd
  have hrδ : r ≤ δ := by
    have : |r| < δ := by simpa only [Real.dist_eq, sub_zero] using hrd
    exact (le_abs_self r).trans this.le
  have he := worstCase_error hr (half_pos hε).le (fun v hv => hb v (hv.trans hrδ))
  rw [Real.dist_eq]
  exact he.trans_lt (by linarith)

/-- The relative worst-case expression and its limit use the original
input and output scales. -/
theorem relative_worst_case : Specs.NumAnalysis206.Conditioning.RelativeWorstCaseType.{u, v, w} := by
  intro 𝕜 _ X _ _ _ Y _ _ U hU f x hx hf hx0 hy0
  have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  have hny : ‖f x‖ ≠ 0 := norm_ne_zero_iff.mpr hy0
  have heq : ∀ r, relativeWorstCase f x r = worstCase f x (r * ‖x‖) * ‖x‖ / ‖f x‖ := by
    intro r
    unfold relativeWorstCase worstCase
    by_cases hr : r = 0
    · simp [hr]
    · field_simp
  refine ⟨fun r _ => heq r, ?_⟩
  have hs : Tendsto (fun r : ℝ => r * ‖x‖) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hid : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using hid.mul_const ‖x‖
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hr (norm_pos_iff.mpr hx0)
  have hlim := ((worst_case_limit 𝕜 U hU f x hx hf).comp hs).mul_const ‖x‖
  simpa only [Function.comp_apply, ← heq] using hlim.div_const ‖f x‖

/-- In dimension zero the only perturbation is zero. -/
theorem zero_dimensional : Specs.NumAnalysis206.Conditioning.ZeroDimensionalType.{u, v, w} := by
  intro 𝕜 _ X _ _ _ Y _ _ hdim f x r hr
  have hz : ∀ v : X, v = 0 := finrank_zero_iff_forall_zero.mp hdim
  have hset : outputNorms f x r = {0} := by
    apply Set.Subset.antisymm
    · rintro _ ⟨v, _hv, rfl⟩
      simp [hz v]
    · intro z hz'
      have hz0 : z = 0 := Set.mem_singleton_iff.mp hz'
      rw [hz0]
      exact zero_mem_outputNorms hr.le
  simp [worstCase, hset]

end NumAnalysis206.Conditioning
