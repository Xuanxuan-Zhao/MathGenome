import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.BigO
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.Sequential
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.PiPeriod
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.DomainZeros

/-! The bounded ratio counterexample K03.02.domain_zeros (paper.tex:479–489).
All functions are tested on ℝ \ {0}. Values of total Lean functions at zero
play no role. The two explicit positive sequences witness the failure of a
finite ratio limit; big-O uses only the global sine bound, including zeros.
-/
noncomputable section
namespace SingleVariableAnalysis.DomainZeros
open Filter
open scoped Topology

abbrev domain : Set ℝ := {0}ᶜ

def numerator (x : ℝ) : ℝ := x * Real.sin (1 / x)
def denominator (x : ℝ) : ℝ := x
def positiveSample (n : ℕ) : ℝ := 1 / (Real.pi / 2 + 2 * Real.pi * n)
def negativeSample (n : ℕ) : ℝ := 1 / (3 * Real.pi / 2 + 2 * Real.pi * n)

theorem constructed_identifications :
    (∀ x, numerator x = x * realSeriesSin (1 / x)) ∧
    (∀ n : ℕ, positiveSample n = 1 / (analyticPi / 2 + 2 * analyticPi * n)) ∧
    (∀ n : ℕ, negativeSample n = 1 / (3 * analyticPi / 2 + 2 * analyticPi * n)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact congrArg (fun t : ℝ => x * t) (sinCosSeries_eq_real (1 / x)).1.symm
  · intro n
    rw [PiPeriod.analyticPi_eq_pi]
    rfl
  · intro n
    rw [PiPeriod.analyticPi_eq_pi]
    rfl

private theorem absolute_bound_all (x : ℝ) : |numerator x| ≤ |denominator x| := by
  simpa only [numerator, denominator, abs_mul, mul_one] using
    mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (1 / x)) (abs_nonneg x)

theorem absolute_bound : ∀ x ∈ domain, |numerator x| ≤ |denominator x| := by
  intro x _
  exact absolute_bound_all x

theorem bigO : ScalarBigO (RealApproachFilter domain (.punctured 0)) numerator denominator := by
  refine ⟨1, zero_le_one, Filter.Eventually.of_forall ?_⟩
  intro x
  simpa only [Real.norm_eq_abs, one_mul] using absolute_bound_all x

theorem numerator_limit : RelativePuncturedLimit numerator domain 0 0 := by
  intro ε hε
  refine ⟨ε, hε, fun x _ _ hx => ?_⟩
  have hb := absolute_bound_all x
  have hx' : |denominator x| < ε := by
    simpa only [Real.dist_eq, sub_zero, denominator] using hx
  simpa only [Real.dist_eq, sub_zero] using hb.trans_lt hx'

theorem denominator_nonzero : ∀ x ∈ domain, denominator x ≠ 0 := by
  intro x hx
  simpa only [domain, Set.mem_compl_iff, Set.mem_singleton_iff, denominator] using hx

theorem denominator_eventually_nonzero :
    ApproachEventually domain (.punctured 0) (fun x => denominator x ≠ 0) := by
  exact ⟨1, zero_lt_one, fun x hx _ => denominator_nonzero x hx⟩

theorem ratio_identity : ∀ x ∈ domain,
    numerator x / denominator x = Real.sin (1 / x) := by
  intro x hx
  exact mul_div_cancel_left₀ (Real.sin (1 / x)) (denominator_nonzero x hx)

private theorem positive_denominator (n : ℕ) : 0 < Real.pi / 2 + 2 * Real.pi * n := by
  positivity

private theorem negative_denominator (n : ℕ) : 0 < 3 * Real.pi / 2 + 2 * Real.pi * n := by
  positivity

theorem sample_membership : ∀ n,
    positiveSample n ∈ domain ∧ negativeSample n ∈ domain ∧
    0 < positiveSample n ∧ 0 < negativeSample n := by
  intro n
  have hp : 0 < positiveSample n := one_div_pos.mpr (positive_denominator n)
  have hm : 0 < negativeSample n := one_div_pos.mpr (negative_denominator n)
  exact ⟨by simpa [domain] using ne_of_gt hp,
    by simpa [domain] using ne_of_gt hm, hp, hm⟩

private theorem reciprocal_affine_limit (a : ℝ) :
    Tendsto (fun n : ℕ => 1 / (a + 2 * Real.pi * n)) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => 2 * Real.pi * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (show 0 < 2 * Real.pi by positivity)
      tendsto_natCast_atTop_atTop
  simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop a h)

theorem sample_limits :
    RealSequenceConverges positiveSample 0 ∧ RealSequenceConverges negativeSample 0 := by
  exact ⟨(realSequenceConverges_iff _ _).mpr (reciprocal_affine_limit (Real.pi / 2)),
    (realSequenceConverges_iff _ _).mpr (reciprocal_affine_limit (3 * Real.pi / 2))⟩

theorem sample_ratio_values : ∀ n,
    numerator (positiveSample n) / denominator (positiveSample n) = 1 ∧
    numerator (negativeSample n) / denominator (negativeSample n) = -1 := by
  intro n
  rw [ratio_identity _ (sample_membership n).1,
    ratio_identity _ (sample_membership n).2.1]
  simp only [positiveSample, negativeSample, one_div_one_div]
  have hp := Real.sin_add_nat_mul_two_pi (Real.pi / 2) n
  have hm := Real.sin_add_nat_mul_two_pi (3 * Real.pi / 2) n
  rw [show (n : ℝ) * (2 * Real.pi) = 2 * Real.pi * n by ring] at hp hm
  rw [hp, hm, Real.sin_pi_div_two]
  have h : 3 * Real.pi / 2 = Real.pi / 2 + Real.pi := by ring
  simp [h, Real.sin_add_pi, Real.sin_pi_div_two]

private theorem domain_accumulation : DomainAccumulation domain 0 := by
  intro δ hδ
  refine ⟨δ / 2, ?_, ?_, ?_⟩
  · simpa [domain] using ne_of_gt (half_pos hδ)
  · change 0 < |δ / 2 - 0|
    rw [sub_zero, abs_of_pos (half_pos hδ)]
    exact half_pos hδ
  · change |δ / 2 - 0| < δ
    rw [sub_zero, abs_of_pos (half_pos hδ)]
    exact half_lt_self hδ

theorem ratio_no_limit : ¬ ∃ L : ℝ,
    RelativePuncturedLimit (fun x => numerator x / denominator x) domain 0 L := by
  rintro ⟨L, hL⟩
  have hseq := (relativePuncturedLimit_sequential_iff _ _ _ _ domain_accumulation).mp hL
  have hp := hseq positiveSample
    (fun n => ⟨(sample_membership n).1, ne_of_gt (sample_membership n).2.2.1⟩)
    ((realSequenceConverges_iff _ _).mp sample_limits.1)
  have hm := hseq negativeSample
    (fun n => ⟨(sample_membership n).2.1, ne_of_gt (sample_membership n).2.2.2⟩)
    ((realSequenceConverges_iff _ _).mp sample_limits.2)
  have hp' : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 L) := by
    simpa only [(sample_ratio_values _).1] using hp
  have hm' : Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (𝓝 L) := by
    simpa only [(sample_ratio_values _).2] using hm
  have h1 : L = 1 := tendsto_nhds_unique hp' tendsto_const_nhds
  have h2 : L = -1 := tendsto_nhds_unique hm' tendsto_const_nhds
  linarith

theorem not_littleO :
    ¬ ScalarLittleO (RealApproachFilter domain (.punctured 0)) numerator denominator := by
  intro h
  exact ratio_no_limit ⟨0,
    (scalarLittleO_punctured_iff_ratio_limit domain 0 numerator denominator
      denominator_eventually_nonzero).mp h⟩

theorem not_equivalent : ¬ (
    ApproachEventually domain (.punctured 0) (fun x => denominator x ≠ 0) ∧
    RelativePuncturedLimit (fun x => numerator x / denominator x) domain 0 1) := by
  intro h
  exact ratio_no_limit ⟨1, h.2⟩

end SingleVariableAnalysis.DomainZeros
