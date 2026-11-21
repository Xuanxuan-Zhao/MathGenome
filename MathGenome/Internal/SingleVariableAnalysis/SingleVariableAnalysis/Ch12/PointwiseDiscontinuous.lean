import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.StandardLimits
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.Continuity
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.SupNorm
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.PointwiseDiscontinuous

/-!
# The powers on the closed unit interval

K03.12.pointwise_discontinuous, paper.tex:1322–1327. Index n denotes the
positive exponent n+1, consistently with the upstream sequence interfaces.
Geometric decay proves the limit below 1. Continuity of a fixed power at 1
supplies values arbitrarily near 1 from below, proving that the supremum
error is exactly 1 even though it need not be attained. The same example is
decreasing on a compact domain, witnessing the need for a continuous limit
in Dini's theorem; no version of Dini is assumed in this proof.
-/
namespace SingleVariableAnalysis

open scoped Topology

/-- The positive integer powers, restricted to the real closed unit interval. -/
def unitPowerSequence (n : ℕ) (x : Set.Icc (0 : ℝ) 1) : ℝ := (x : ℝ) ^ (n + 1)

/-- Zero below 1, with value 1 at the right endpoint. -/
noncomputable def unitPowerLimit (x : Set.Icc (0 : ℝ) 1) : ℝ := if (x : ℝ) = 1 then 1 else 0

theorem unitPower_limit_below_one (x : Set.Icc (0 : ℝ) 1) (hx : (x : ℝ) < 1) :
    RealSequenceConverges (fun n => unitPowerSequence n x) 0 := by
  exact real_geometric_decay x (by simpa only [abs_of_nonneg x.property.1] using hx)

theorem unitPower_values_at_one :
    (∀ n, unitPowerSequence n ⟨1, ⟨zero_le_one, le_rfl⟩⟩ = 1) ∧
      unitPowerLimit ⟨1, ⟨zero_le_one, le_rfl⟩⟩ = 1 := by
  simp [unitPowerSequence, unitPowerLimit]

theorem unitPower_pointwise_limit : RealPointwiseConverges unitPowerSequence unitPowerLimit := by
  intro x
  by_cases hx : (x : ℝ) = 1
  · intro ε hε
    exact ⟨0, fun n _ => by simpa [unitPowerSequence, unitPowerLimit, hx] using hε⟩
  · simpa only [unitPowerLimit, ite_eq_right hx] using
      unitPower_limit_below_one x (lt_of_le_of_ne x.property.2 hx)

theorem unitPower_continuous_terms (n : ℕ) : Continuous (unitPowerSequence n) := by
  exact continuous_subtype_val.pow (n + 1)

/-- Points below the endpoint occur in every positive-radius neighborhood. -/
private theorem point_below_one (δ : ℝ) (hδ : 0 < δ) :
    ∃ x : Set.Icc (0 : ℝ) 1, (x : ℝ) < 1 ∧ |(x : ℝ) - 1| < δ := by
  let t := min (δ / 2) (1 / 2 : ℝ)
  have ht : 0 < t := lt_min (by linarith) (by norm_num)
  have htδ : t < δ := (min_le_left _ _).trans_lt (by linarith)
  have ht1 : t ≤ (1 / 2 : ℝ) := min_le_right _ _
  refine ⟨⟨1 - t, ⟨by linarith, by linarith⟩⟩, by dsimp; linarith, ?_⟩
  change |1 - t - 1| < δ
  rw [show 1 - t - 1 = -t by ring, abs_neg, abs_of_pos ht]
  exact htδ

theorem unitPower_discontinuous_at_one :
    ¬ ContinuousAt unitPowerLimit ⟨1, ⟨zero_le_one, le_rfl⟩⟩ := by
  intro h
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.mp h (1 / 2) (by norm_num)
  obtain ⟨x, hx, hd⟩ := point_below_one δ hδ
  have hdist : dist x (⟨1, ⟨zero_le_one, le_rfl⟩⟩ : Set.Icc (0 : ℝ) 1) < δ := by
    exact hd
  have hbad := hb hdist
  norm_num [unitPowerLimit, ne_of_lt hx, Real.dist_eq] at hbad

/-- For each fixed power, its values below 1 approach 1. -/
private theorem unitPower_near_one (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : Set.Icc (0 : ℝ) 1, (x : ℝ) < 1 ∧ 1 - ε < unitPowerSequence n x := by
  have hc : ContinuousAt (fun x : ℝ => x ^ (n + 1)) 1 :=
    (continuous_id.pow (n + 1)).continuousAt
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.mp hc ε hε
  obtain ⟨x, hx, hd⟩ := point_below_one δ hδ
  have hp := hb (show dist (x : ℝ) 1 < δ from hd)
  simp only [Real.dist_eq, one_pow] at hp
  exact ⟨x, hx, by dsimp [unitPowerSequence]; linarith [(abs_lt.mp hp).1]⟩

theorem unitPower_supremum_error (n : ℕ) :
    realSupError unitPowerSequence unitPowerLimit n = 1 := by
  have hbound (x : Set.Icc (0 : ℝ) 1) : |unitPowerSequence n x - unitPowerLimit x| ≤ 1 := by
    by_cases hx : (x : ℝ) = 1
    · simp [unitPowerSequence, unitPowerLimit, hx]
    · simp only [unitPowerLimit, ite_eq_right hx, sub_zero, unitPowerSequence,
        abs_of_nonneg (pow_nonneg x.property.1 _)]
      exact pow_le_one₀ x.property.1 x.property.2
  have hu : realSupError unitPowerSequence unitPowerLimit n ≤ 1 := by
    apply iSup_le
    intro x
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hbound x)
  apply le_antisymm hu
  have hfinite : realSupError unitPowerSequence unitPowerLimit n ≠ ⊤ :=
    (lt_of_le_of_lt hu ENNReal.one_lt_top).ne
  rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_iff_le_toReal hfinite]
  by_contra h
  have ht : (realSupError unitPowerSequence unitPowerLimit n).toReal < 1 := lt_of_not_ge h
  obtain ⟨x, hx, hp⟩ := unitPower_near_one n
    (1 - (realSupError unitPowerSequence unitPowerLimit n).toReal) (by linarith)
  have he : ENNReal.ofReal |unitPowerSequence n x - unitPowerLimit x| ≤
      realSupError unitPowerSequence unitPowerLimit n :=
    le_iSup (fun y : Set.Icc (0 : ℝ) 1 =>
      ENNReal.ofReal |unitPowerSequence n y - unitPowerLimit y|) x
  have he' := (ENNReal.ofReal_le_iff_le_toReal hfinite).mp he
  simp only [unitPowerLimit, ite_eq_right (ne_of_lt hx), sub_zero, unitPowerSequence,
    abs_of_nonneg (pow_nonneg x.property.1 _)] at he'
  dsimp [unitPowerSequence] at hp
  linarith

theorem unitPower_not_uniform : ¬ RealUniformConverges unitPowerSequence unitPowerLimit := by
  intro h
  obtain ⟨N, hN⟩ := h (1 / 2) (by norm_num)
  have he : realSupError unitPowerSequence unitPowerLimit N ≤ ENNReal.ofReal (1 / 2) :=
    iSup_le fun x => ENNReal.ofReal_le_ofReal (hN N le_rfl x).le
  rw [unitPower_supremum_error] at he
  norm_num at he

/-- Uniqueness of pointwise limits rules out a different uniform limit too. -/
theorem unitPower_no_uniform_limit :
    ¬ ∃ g : Set.Icc (0 : ℝ) 1 → ℝ, RealUniformConverges unitPowerSequence g := by
  rintro ⟨g, hg⟩
  have heq : g = unitPowerLimit := realPointwiseLimit_unique unitPowerSequence g unitPowerLimit
    (realUniformConverges_pointwise unitPowerSequence g hg) unitPower_pointwise_limit
  exact unitPower_not_uniform (heq ▸ hg)

theorem unitPower_decreasing_terms (x : Set.Icc (0 : ℝ) 1) :
    Antitone (fun n => unitPowerSequence n x) := by
  apply antitone_nat_of_succ_le
  intro n
  change (x : ℝ) ^ (n + 1 + 1) ≤ (x : ℝ) ^ (n + 1)
  rw [pow_succ]
  exact mul_le_of_le_one_right (pow_nonneg x.property.1 _) x.property.2

theorem unitPower_dini_counterexample :
    IsCompact (Set.Icc (0 : ℝ) 1) ∧
      (∀ n, Continuous (unitPowerSequence n)) ∧
      (∀ x : Set.Icc (0 : ℝ) 1, Antitone (fun n => unitPowerSequence n x)) ∧
      RealPointwiseConverges unitPowerSequence unitPowerLimit ∧
      ¬ Continuous unitPowerLimit ∧
      ¬ RealUniformConverges unitPowerSequence unitPowerLimit := by
  exact ⟨isCompact_Icc, unitPower_continuous_terms, unitPower_decreasing_terms,
    unitPower_pointwise_limit, fun h => unitPower_discontinuous_at_one h.continuousAt,
    unitPower_not_uniform⟩

end SingleVariableAnalysis
