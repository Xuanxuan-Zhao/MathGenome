import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.DyadicMomentRegularity
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.ProbabilityBounds
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch02.FirstBorelCantelli
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityFoundations.Ch05
universe u v

lemma dyadicStep_pos {T : ℝ} (hT : 0 < T) (n : ℕ) : 0 < dyadicStep T n :=
  div_pos hT (pow_pos (by norm_num) _)

lemma dyadicStep_le {T : ℝ} (hT : 0 < T) (n : ℕ) : dyadicStep T n ≤ T := by
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) n)).mpr
  exact le_mul_of_one_le_right hT.le (one_le_pow₀ (by norm_num))

lemma dyadic_grid_mem {T : ℝ} (hT : 0 < T) (n j : ℕ) (hj : j ≤ 2 ^ n) :
    (j : ℝ) * dyadicStep T n ∈ Set.Icc 0 T := by
  have hpow : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) _
  refine ⟨mul_nonneg (Nat.cast_nonneg _) (dyadicStep_pos hT n).le, ?_⟩
  calc
    (j : ℝ) * dyadicStep T n ≤ (2 ^ n : ℝ) * dyadicStep T n := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (dyadicStep_pos hT n).le
    _ = T := by dsimp [dyadicStep]; field_simp

lemma measurable_dyadicBadEvent {Ω : Type u} {S : Type v}
    [MeasurableSpace Ω] [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [SecondCountableTopology S] (X : ℝ → Ω → S) {T : ℝ} (hT : 0 < T)
    (hX : ∀ t ∈ Set.Icc 0 T, Measurable (X t)) (γ : ℝ) (n : ℕ) :
    MeasurableSet (dyadicBadEvent X T γ n) := by
  unfold dyadicBadEvent
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion (fun j : Fin (2 ^ n) => ?_)
  exact measurableSet_lt measurable_const
    ((hX _ (dyadic_grid_mem hT n (j.val + 1) j.isLt)).dist
      (hX _ (dyadic_grid_mem hT n j.val j.isLt.le)))

/-- Algebra for the finite union bound, in the exact geometric form of the source. -/
lemma dyadic_scale_identity {T : ℝ} (hT : 0 < T) (p β γ : ℝ) (n : ℕ) :
    (2 : ℝ) ^ n * (dyadicStep T n) ^ (1 + β - p * γ) =
      T ^ (1 + β - p * γ) * (2 : ℝ) ^ (-(n : ℝ) * (β - p * γ)) := by
  rw [dyadicStep, Real.div_rpow hT.le (by positivity)]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    (2 : ℝ) ^ (n : ℝ) * (T ^ (1 + β - p * γ) *
        2 ^ (-((n : ℝ) * (1 + β - p * γ)))) =
      T ^ (1 + β - p * γ) *
        (2 ^ (n : ℝ) * 2 ^ (-((n : ℝ) * (1 + β - p * γ)))) := by ring
    _ = _ := by rw [← Real.rpow_add (by norm_num)]; congr 2; ring

/-- Finitely many bad levels leave only finitely many finite ratios to absorb
into a single constant. -/
lemma dyadicBound_of_finite_bad_levels {Ω S : Type*} [MetricSpace S]
    (X : ℝ → Ω → S) {T : ℝ} (hT : 0 < T) (γ : ℝ) (ω : Ω)
    (hf : {n : ℕ | ω ∈ dyadicBadEvent X T γ n}.Finite) :
    DyadicBound X T γ ω := by
  let F (n : ℕ) (j : Fin (2 ^ n)) : ℝ :=
    dist (X ((j.val + 1 : ℕ) * dyadicStep T n) ω)
      (X ((j.val : ℝ) * dyadicStep T n) ω) / (dyadicStep T n) ^ γ
  have hb : BddAbove (⋃ n ∈ {n : ℕ | ω ∈ dyadicBadEvent X T γ n}, Set.range (F n)) :=
    hf.bddAbove_biUnion.mpr (fun n _ => (Set.finite_range (F n)).bddAbove)
  obtain ⟨A, hA⟩ := hb
  refine ⟨max 1 A, le_trans zero_le_one (le_max_left _ _), fun n j => ?_⟩
  have hs : 0 < (dyadicStep T n) ^ γ := Real.rpow_pos_of_pos (dyadicStep_pos hT n) _
  by_cases hn : ω ∈ dyadicBadEvent X T γ n
  · have hr : F n j ≤ A := hA (Set.mem_iUnion.mpr ⟨n,
        Set.mem_iUnion.mpr ⟨hn, Set.mem_range_self j⟩⟩)
    exact (div_le_iff₀ hs).mp (hr.trans (le_max_right _ _))
  · have hh : dist (X ((j.val + 1 : ℕ) * dyadicStep T n) ω)
        (X ((j.val : ℝ) * dyadicStep T n) ω) ≤ (dyadicStep T n) ^ γ := by
      exact le_of_not_gt (fun hh => hn ⟨j, hh⟩)
    exact hh.trans (le_mul_of_one_le_left hs.le (le_max_left _ _))

/-- On a bounded time interval, a power bound implies every smaller exponent. -/
lemma DyadicBound.of_le {Ω S : Type*} [MetricSpace S] {X : ℝ → Ω → S}
    {T γ δ : ℝ} {ω : Ω} (h : DyadicBound X T δ ω) (hT : 0 < T) (hγδ : γ ≤ δ) :
    DyadicBound X T γ ω := by
  obtain ⟨A, hA, hbound⟩ := h
  refine ⟨A * T ^ (δ - γ), mul_nonneg hA (Real.rpow_nonneg hT.le _), fun n j => ?_⟩
  have hs := dyadicStep_pos hT n
  have heq : (dyadicStep T n) ^ δ =
      (dyadicStep T n) ^ (δ - γ) * (dyadicStep T n) ^ γ := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  calc
    _ ≤ A * (dyadicStep T n) ^ δ := hbound n j
    _ = A * ((dyadicStep T n) ^ (δ - γ) * (dyadicStep T n) ^ γ) := by rw [heq]
    _ ≤ A * (T ^ (δ - γ) * (dyadicStep T n) ^ γ) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hs.le (dyadicStep_le hT n) (sub_nonneg.mpr hγδ))
          (Real.rpow_nonneg hs.le _)) hA
    _ = _ := by ring

section Process
variable {Ω : Type u} {S : Type v} [MeasurableSpace Ω] [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ → Ω → S)
  (T p β : ℝ) (C : ℝ≥0) (hT : 0 < T) (hp : 0 < p) (hβ : 0 < β)
  (hX : ∀ t ∈ Set.Icc 0 T, Measurable (X t))
  (hmoment : IncrementMomentCondition P X T p β C)

include hT hp hX hmoment

lemma adjacent_increment_probability (γ : ℝ) (n : ℕ) (j : Fin (2 ^ n)) :
    P {ω | (dyadicStep T n) ^ γ <
      dist (X ((j.val + 1 : ℕ) * dyadicStep T n) ω)
        (X ((j.val : ℝ) * dyadicStep T n) ω)} ≤
      ENNReal.ofReal ((C : ℝ) * (dyadicStep T n) ^ (1 + β - p * γ)) := by
  have hstep := dyadicStep_pos hT n
  have hs := dyadic_grid_mem hT n j.val j.isLt.le
  have ht := dyadic_grid_mem hT n (j.val + 1) j.isLt
  have hdist : |(j.val + 1 : ℕ) * dyadicStep T n -
      (j.val : ℝ) * dyadicStep T n| = dyadicStep T n := by
    rw [Nat.cast_add, Nat.cast_one]
    ring_nf
    exact abs_of_pos hstep
  have hm := hmoment _ hs _ ht
  rw [hdist] at hm
  have h := Ch01.moment_gt P
    (fun ω => dist (X ((j.val + 1 : ℕ) * dyadicStep T n) ω)
      (X ((j.val : ℝ) * dyadicStep T n) ω))
    ((hX _ ht).dist (hX _ hs)) ((dyadicStep T n) ^ γ) p
    (Real.rpow_pos_of_pos hstep _) hp
  simp only [abs_of_nonneg dist_nonneg, Ch01.nonnegativeExpectation] at h
  refine (h.trans (mul_le_mul_right hm _)).trans_eq ?_
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (Real.rpow_nonneg hstep.le γ) (-p))]
  congr 1
  rw [← Real.rpow_mul hstep.le]
  calc
    (dyadicStep T n) ^ (γ * -p) * ((C : ℝ) * (dyadicStep T n) ^ (1 + β)) =
        (C : ℝ) * ((dyadicStep T n) ^ (γ * -p) *
          (dyadicStep T n) ^ (1 + β)) := by ring
    _ = _ := by rw [← Real.rpow_add hstep]; congr 2; ring

include hβ

/-- Markov and a union bound over the `2^n` adjacent grid intervals. -/
theorem dyadic_probability_bound (γ : ℝ) (_hγ : 0 < γ) (_hγp : γ < β / p) (n : ℕ) :
    P (dyadicBadEvent X T γ n) ≤
      ENNReal.ofReal ((C : ℝ) * T ^ (1 + β - p * γ) *
        (2 : ℝ) ^ (-(n : ℝ) * (β - p * γ))) := by
  have heq : dyadicBadEvent X T γ n =
      ⋃ j : Fin (2 ^ n), {ω | (dyadicStep T n) ^ γ <
        dist (X ((j.val + 1 : ℕ) * dyadicStep T n) ω)
          (X ((j.val : ℝ) * dyadicStep T n) ω)} := by
    ext ω
    simp [dyadicBadEvent]
  rw [heq]
  refine (measure_iUnion_fintype_le P _).trans ?_
  calc
    _ ≤ ∑ _j : Fin (2 ^ n),
        ENNReal.ofReal ((C : ℝ) * (dyadicStep T n) ^ (1 + β - p * γ)) := by
      exact Finset.sum_le_sum (fun j _ =>
        adjacent_increment_probability P X T p β C hT hp hX hmoment γ n j)
    _ = ENNReal.ofReal ((2 : ℝ) ^ n *
        ((C : ℝ) * (dyadicStep T n) ^ (1 + β - p * γ))) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      norm_cast
    _ = _ := by
      congr 1
      calc
        _ = (C : ℝ) * ((2 : ℝ) ^ n * (dyadicStep T n) ^ (1 + β - p * γ)) := by ring
        _ = _ := by rw [dyadic_scale_identity hT]; ring

/-- The geometric estimate has finite sum for every admissible exponent. -/
theorem dyadic_summable (γ : ℝ) (hγ : 0 < γ) (hγp : γ < β / p) :
    (∑' n, P (dyadicBadEvent X T γ n)) < ∞ := by
  have hgap : 0 < β - p * γ := by
    have := (lt_div_iff₀ hp).mp hγp
    nlinarith
  have hr : (2 : ℝ) ^ (-(β - p * γ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hgap)
  have hs := (summable_geometric_of_lt_one
    (Real.rpow_nonneg (by norm_num) _) hr).mul_left ((C : ℝ) * T ^ (1 + β - p * γ))
  have heq (n : ℕ) : (C : ℝ) * T ^ (1 + β - p * γ) *
        (2 : ℝ) ^ (-(n : ℝ) * (β - p * γ)) =
      (C : ℝ) * T ^ (1 + β - p * γ) * ((2 : ℝ) ^ (-(β - p * γ))) ^ n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 2
    ring
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun n => ?_)) hs.tsum_ofReal_lt_top
  rw [← heq]
  exact dyadic_probability_bound P X T p β C hT hp hβ hX hmoment γ hγ hγp n

/-- A countable cofinal set of rational exponents gives one event for every
positive exponent below `β / p`. -/
theorem common_dyadic_event :
    ∃ G : Set Ω, MeasurableSet G ∧ P G = 1 ∧
      ∀ ω ∈ G, ∀ γ : ℝ, 0 < γ → γ < β / p → DyadicBound X T γ ω := by
  have hq (q : ℚ) : ∀ᵐ ω ∂P,
      0 < (q : ℝ) → (q : ℝ) < β / p → DyadicBound X T (q : ℝ) ω := by
    by_cases hq0 : 0 < (q : ℝ)
    · by_cases hqp : (q : ℝ) < β / p
      · have hf := Ch02.ae_finite_occurrences P (dyadicBadEvent X T (q : ℝ))
          (measurable_dyadicBadEvent X hT hX (q : ℝ))
          (dyadic_summable P X T p β C hT hp hβ hX hmoment q hq0 hqp)
        exact hf.mono (fun ω hω _ _ => dyadicBound_of_finite_bad_levels X hT q ω hω)
      · exact Filter.Eventually.of_forall (fun _ _ h => (hqp h).elim)
    · exact Filter.Eventually.of_forall (fun _ h _ => (hq0 h).elim)
  have hall : ∀ᵐ ω ∂P, ∀ q : ℚ,
      0 < (q : ℝ) → (q : ℝ) < β / p → DyadicBound X T (q : ℝ) ω :=
    (ae_all_iff).mpr hq
  apply (Ch01.almostSurely_iff_measurable_one P
    (fun ω => ∀ γ : ℝ, 0 < γ → γ < β / p → DyadicBound X T γ ω)).mp
  filter_upwards [hall] with ω hω
  intro γ hγ hγp
  obtain ⟨q, hγq, hqp⟩ := exists_rat_btwn hγp
  exact (hω q (hγ.trans hγq) hqp).of_le hT hγq.le

end Process
end ProbabilityFoundations.Ch05
