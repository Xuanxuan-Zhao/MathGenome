import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Root
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.PositiveRoots
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Limsup
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Geometric
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Absolute
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Condensation

/-!
# The root test, with both extended endpoints and the boundary examples

K03.11.root. All roots are the previously constructed nonnegative integer
roots. The extended limsup is the upstream infimum of tail suprema.
The proof compares finite tails with geometric tails, and uses the ordinary
term test for divergence. The boundary root limits follow by taking inverses
and squares in the established limit of the nth root of n. Condensation
separately proves convergence of the reciprocal-square series.
-/

noncomputable section
namespace SingleVariableAnalysis

open Filter
open scoped Topology BigOperators

def realSeriesRootLimsup (a : ℕ → ℝ) : EReal :=
  sequenceLimsup (fun n => nonnegativeRoot (n+1) |a (n+1)|)
def complexSeriesRootLimsup (a : ℕ → ℂ) : EReal :=
  sequenceLimsup (fun n => nonnegativeRoot (n+1) ‖a (n+1)‖)

/-- An infimum of tail suprema of nonnegative roots is nonnegative. -/
theorem magnitude_root_limsup_nonneg (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) :
    0 ≤ sequenceLimsup (fun n => nonnegativeRoot (n+1) (b (n+1))) := by
  apply le_iInf
  intro N
  exact (EReal.coe_le_coe (nonnegativeRoot_nonneg (N+1) (Nat.succ_pos N)
    (b (N+1)) (hb _))).trans
      (le_iSup_of_le N (le_iSup_of_le le_rfl le_rfl))

theorem real_root_limsup_nonneg (a : ℕ → ℝ) : 0 ≤ realSeriesRootLimsup a :=
  magnitude_root_limsup_nonneg (fun n => |a n|) (fun _ => abs_nonneg _)

theorem complex_root_limsup_nonneg (a : ℕ → ℂ) : 0 ≤ complexSeriesRootLimsup a :=
  magnitude_root_limsup_nonneg (fun n => ‖a n‖) (fun _ => norm_nonneg _)

/-- A strict root limsup bound gives an eventual geometric majorant.
No boundedness assumption is needed, and q is strictly positive. -/
theorem geometric_bound_of_root_limsup_lt_one (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (h : sequenceLimsup (fun n => nonnegativeRoot (n+1) (b (n+1))) < 1) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∃ N : ℕ, ∀ n ≥ N, b n ≤ q^n := by
  obtain ⟨q, hq, hq1⟩ := EReal.exists_between_coe_real h
  have hq0 : 0 < q := EReal.coe_lt_coe_iff.mp
    ((magnitude_root_limsup_nonneg b hb).trans_lt hq)
  have hq1' : q < 1 := EReal.coe_lt_coe_iff.mp hq1
  change (⨅ N, ⨆ n ≥ N, (nonnegativeRoot (n+1) (b (n+1)) : EReal)) < (q : EReal) at hq
  obtain ⟨N, hN⟩ := iInf_lt_iff.mp hq
  refine ⟨q, hq0, hq1', N+1, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hk : N ≤ k := by omega
  have hr' : (nonnegativeRoot (k+1) (b (k+1)) : EReal) ≤
      ⨆ j ≥ N, (nonnegativeRoot (j+1) (b (j+1)) : EReal) := by
    exact (le_iSup (fun _ : k ≥ N =>
      (nonnegativeRoot (k+1) (b (k+1)) : EReal)) hk).trans
      (le_iSup (fun j => ⨆ _ : j ≥ N,
        (nonnegativeRoot (j+1) (b (j+1)) : EReal)) k)
  have hr : nonnegativeRoot (k+1) (b (k+1)) ≤ q :=
    EReal.coe_le_coe_iff.mp (hr'.trans hN.le)
  calc
    b (k+1) = nonnegativeRoot (k+1) (b (k+1)) ^ (k+1) :=
      (nonnegativeRoot_pow _ (Nat.succ_pos k) _ (hb _)).symm
    _ ≤ q ^ (k+1) := pow_le_pow_left₀
      (nonnegativeRoot_nonneg _ (Nat.succ_pos k) _ (hb _)) hr _

/-- Ordinary Cauchy tails allow comparison on an eventual tail. -/
theorem nonnegative_converges_of_geometric_bound (b : ℕ → ℝ)
    (hb : ∀ n, 0 ≤ b n) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (N : ℕ) (hN : ∀ n ≥ N, b n ≤ q^n) : RealSeriesConverges b := by
  have hg : RealSeriesConverges (fun n => q^n) :=
    ⟨_, real_geometric_series_hasSum q (by rwa [abs_of_nonneg hq0])⟩
  apply (real_series_cauchy_criterion b).mpr
  intro ε hε
  obtain ⟨M, hM⟩ := (real_series_cauchy_criterion _).mp hg ε hε
  refine ⟨max N M, fun p hp r hpr => ?_⟩
  rw [abs_of_nonneg (Finset.sum_nonneg (fun n _ => hb n))]
  apply lt_of_le_of_lt (Finset.sum_le_sum ?_) (le_abs_self _ |>.trans_lt
    (hM p (le_trans (le_max_right _ _) hp) r hpr))
  intro n hn
  exact hN n ((le_max_left _ _).trans (hp.trans (Finset.mem_Icc.mp hn).1))

theorem real_root_test_absolute (a : ℕ → ℝ) (h : realSeriesRootLimsup a < 1) :
    RealSeriesAbsolutelyConverges a := by
  obtain ⟨q, hq0, hq1, N, hN⟩ := geometric_bound_of_root_limsup_lt_one
    (fun n => |a n|) (fun _ => abs_nonneg _) h
  exact nonnegative_converges_of_geometric_bound _ (fun _ => abs_nonneg _)
    q hq0.le hq1 N hN

theorem complex_root_test_absolute (a : ℕ → ℂ) (h : complexSeriesRootLimsup a < 1) :
    ComplexSeriesAbsolutelyConverges a := by
  obtain ⟨q, hq0, hq1, N, hN⟩ := geometric_bound_of_root_limsup_lt_one
    (fun n => ‖a n‖) (fun _ => norm_nonneg _) h
  exact nonnegative_converges_of_geometric_bound _ (fun _ => norm_nonneg _)
    q hq0.le hq1 N hN

/-- If the magnitudes tend to zero, their root limsup cannot exceed one. -/
theorem root_limsup_le_one_of_tendsto_zero (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (h : RealSequenceConverges b 0) :
    sequenceLimsup (fun n => nonnegativeRoot (n+1) (b (n+1))) ≤ 1 := by
  obtain ⟨N, hN⟩ := h 1 zero_lt_one
  apply le_trans (iInf_le _ N)
  apply iSup_le
  intro n
  apply iSup_le
  intro hn
  have hsmall : b (n+1) ≤ 1 := by
    have := hN (n+1) (by omega)
    simpa only [sub_zero, abs_of_nonneg (hb _)] using this.le
  have hr : nonnegativeRoot (n+1) (b (n+1)) ≤ 1 := by
    apply (pow_le_pow_iff_left₀
      (nonnegativeRoot_nonneg _ (Nat.succ_pos n) _ (hb _)) zero_le_one
      (Nat.succ_ne_zero n)).mp
    simpa only [nonnegativeRoot_pow _ (Nat.succ_pos n) _ (hb _), one_pow] using hsmall
  exact EReal.coe_le_coe hr

theorem real_root_test_diverges (a : ℕ → ℝ) (h : 1 < realSeriesRootLimsup a) :
    RealSeriesDiverges a := by
  intro hc
  have ht := real_abs a 0 (real_series_term_limit a hc)
  have ht' : RealSequenceConverges (fun n => |a n|) 0 := by simpa using ht
  exact (not_le_of_gt h) (root_limsup_le_one_of_tendsto_zero (fun n => |a n|)
    (fun _ => abs_nonneg _) ht')

theorem complex_root_test_diverges (a : ℕ → ℂ) (h : 1 < complexSeriesRootLimsup a) :
    ComplexSeriesDiverges a := by
  intro hc
  have ht := complex_norm a 0 (complex_series_term_limit a hc)
  have ht' : RealSequenceConverges (fun n => ‖a n‖) 0 := by simpa using ht
  exact (not_le_of_gt h) (root_limsup_le_one_of_tendsto_zero (fun n => ‖a n‖)
    (fun _ => norm_nonneg _) ht')

theorem real_root_test_zero (a : ℕ → ℝ) (h : realSeriesRootLimsup a = 0) :
    RealSeriesAbsolutelyConverges a :=
  real_root_test_absolute a (by rw [h]; exact zero_lt_one)

theorem complex_root_test_zero (a : ℕ → ℂ) (h : complexSeriesRootLimsup a = 0) :
    ComplexSeriesAbsolutelyConverges a :=
  complex_root_test_absolute a (by rw [h]; exact zero_lt_one)

theorem real_root_test_top (a : ℕ → ℝ) (h : realSeriesRootLimsup a = ⊤) :
    RealSeriesDiverges a :=
  real_root_test_diverges a (by rw [h]; exact EReal.coe_lt_top 1)

theorem complex_root_test_top (a : ℕ → ℂ) (h : complexSeriesRootLimsup a = ⊤) :
    ComplexSeriesDiverges a :=
  complex_root_test_diverges a (by rw [h]; exact EReal.coe_lt_top 1)

/-- Root uniqueness transports inversion using only finite power algebra. -/
theorem nonnegativeRoot_inv (m : ℕ) (hm : 0 < m) (a : ℝ) (ha : 0 ≤ a) :
    nonnegativeRoot m a⁻¹ = (nonnegativeRoot m a)⁻¹ := by
  apply (nonnegativeRoot_unique m hm a⁻¹ (inv_nonneg.mpr ha) _
    (inv_nonneg.mpr (nonnegativeRoot_nonneg m hm a ha)) ?_).symm
  rw [inv_pow, nonnegativeRoot_pow m hm a ha]

/-- Root uniqueness also transports natural powers of a nonnegative base. -/
theorem nonnegativeRoot_pow_base (m : ℕ) (hm : 0 < m) (a : ℝ) (ha : 0 ≤ a)
    (k : ℕ) : nonnegativeRoot m (a^k) = (nonnegativeRoot m a)^k := by
  apply (nonnegativeRoot_unique m hm (a^k) (pow_nonneg ha k) _
    (pow_nonneg (nonnegativeRoot_nonneg m hm a ha) k) ?_).symm
  rw [← pow_mul, Nat.mul_comm k m, pow_mul, nonnegativeRoot_pow m hm a ha]

theorem harmonic_root_limit :
    RealSequenceConverges
      (fun n => nonnegativeRoot (n+1) |1 / ((n+1 : ℕ) : ℝ)|) 1 := by
  have h := real_inv _ 1 integer_root_self_limit one_ne_zero
  have he : (fun n => nonnegativeRoot (n+1) |1 / ((n+1 : ℕ) : ℝ)|) =
      (fun n => (nonnegativeRoot (n+1) ((n+1 : ℕ) : ℝ))⁻¹) := by
    funext n
    rw [abs_of_nonneg (by positivity), one_div,
      nonnegativeRoot_inv _ (Nat.succ_pos n) _ (Nat.cast_nonneg _)]
  rw [he]
  simpa only [inv_one] using h

theorem reciprocal_square_root_limit :
    RealSequenceConverges
      (fun n => nonnegativeRoot (n+1) |1 / (((n+1 : ℕ) : ℝ)^2)|) 1 := by
  have h := ((realSequenceConverges_iff _ _).mp harmonic_root_limit).pow 2
  apply (realSequenceConverges_iff _ _).mpr
  have he : (fun n => nonnegativeRoot (n+1) |1 / (((n+1 : ℕ) : ℝ)^2)|) =
      (fun n => nonnegativeRoot (n+1) |1 / ((n+1 : ℕ) : ℝ)| ^ 2) := by
    funext n
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity),
      one_div, one_div, ← inv_pow,
      nonnegativeRoot_pow_base _ (Nat.succ_pos n) _
        (inv_nonneg.mpr (Nat.cast_nonneg _)) 2]
  rw [he]
  simpa only [one_pow] using h

/-- An ordinary series converges if its tail after the first term converges. -/
theorem real_series_converges_of_shift (a : ℕ → ℝ)
    (h : RealSeriesConverges (fun n => a (n+1))) : RealSeriesConverges a := by
  obtain ⟨S, hS⟩ := h
  refine ⟨a 0 + S, (realSequenceConverges_iff _ _).mpr ?_⟩
  apply (tendsto_add_atTop_iff_nat 1).mp
  have ht := ((realSequenceConverges_iff _ _).mp hS).const_add (a 0)
  convert ht using 1
  funext N
  change (∑ i ∈ Finset.range (N+1+1), a i) =
    a 0 + ∑ i ∈ Finset.range (N+1), a (i+1)
  rw [Finset.sum_range_succ']
  exact add_comm _ _

/-- The convergent boundary example is proved separately by condensation. -/
theorem reciprocal_square_series_absolute :
    RealSeriesAbsolutelyConverges (fun n => 1 / (n : ℝ)^2) := by
  have hn : ∀ n : ℕ, 1 ≤ n → 0 ≤ 1 / (n : ℝ)^2 :=
    fun _ _ => one_div_nonneg.mpr (sq_nonneg _)
  have hm : AntitoneOn (fun n : ℕ => 1 / (n : ℝ)^2) (Set.Ici 1) := by
    intro m hml n hnl hmn
    exact one_div_le_one_div_of_le (sq_pos_of_pos (by exact_mod_cast hml))
      (pow_le_pow_left₀ (Nat.cast_nonneg m) (Nat.cast_le.mpr hmn) 2)
  have he : (fun k : ℕ => (2 : ℝ)^k * (1 / ((2^k : ℕ) : ℝ)^2)) =
      (fun k => (1/2 : ℝ)^k) := by
    funext k
    simp only [Nat.cast_pow, Nat.cast_ofNat, div_pow, one_pow]
    have hne : (2 : ℝ)^k ≠ 0 := pow_ne_zero k (by norm_num)
    field_simp
  have hc : RealSeriesConverges
      (fun k : ℕ => (2 : ℝ)^k * (1 / ((2^k : ℕ) : ℝ)^2)) := by
    rw [he]
    exact ⟨_, real_geometric_series_hasSum (1/2) (by norm_num)⟩
  have hs := (cauchy_condensation (fun n => 1 / (n : ℝ)^2) hn hm).mpr hc
  have ht := real_series_converges_of_shift (fun n => 1 / (n : ℝ)^2) hs
  change RealSeriesConverges (fun n => |1 / (n : ℝ)^2|)
  have he : (fun n : ℕ => |1 / (n : ℝ)^2|) = (fun n : ℕ => 1 / (n : ℝ)^2) := by
    funext n
    exact abs_of_nonneg (by positivity)
  rwa [he]

/-- A converging root sequence has precisely that extended limsup. -/
theorem root_limsup_eq_of_root_limit (b : ℕ → ℝ) (l : ℝ)
    (h : RealSequenceConverges (fun n => nonnegativeRoot (n+1) (b (n+1))) l) :
    sequenceLimsup (fun n => nonnegativeRoot (n+1) (b (n+1))) = (l : EReal) := by
  change (⨅ N, ⨆ n ≥ N, (nonnegativeRoot (n+1) (b (n+1)) : EReal)) = _
  rw [← limsup_eq_iInf_iSup_of_nat]
  exact (EReal.tendsto_coe.mpr ((realSequenceConverges_iff _ _).mp h)).limsup_eq

theorem root_test_boundary_examples :
    realSeriesRootLimsup (fun n => 1 / (n : ℝ)) = 1 ∧
    realSeriesRootLimsup (fun n => 1 / (n : ℝ)^2) = 1 ∧
    RealSeriesDiverges (fun n => 1 / (n : ℝ)) ∧
    RealSeriesAbsolutelyConverges (fun n => 1 / (n : ℝ)^2) := by
  refine ⟨?_, ?_, harmonic_series_diverges, reciprocal_square_series_absolute⟩
  · exact root_limsup_eq_of_root_limit (fun n => |1 / (n : ℝ)|) 1 harmonic_root_limit
  · exact root_limsup_eq_of_root_limit (fun n => |1 / (n : ℝ)^2|) 1
      reciprocal_square_root_limit

end SingleVariableAnalysis
