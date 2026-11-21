import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.MTest
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.Continuity
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Geometric
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.TentContinuity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The tent and the continuous uniformly convergent series of paper.tex:3958–3971.
The quotient metric supplies the global estimate; its radius-one formula and
integer-period shifts supply the affine cells. No derivative assertion is used.
-/

noncomputable section
namespace SingleVariableAnalysis

open scoped BigOperators Topology

def periodicTent : ℝ → ℝ :=
  Specs.SingleVariableAnalysis.Ch16.TentContinuity.periodicTentValue

theorem periodicTent_period : Function.Periodic periodicTent 2 := by
  intro x
  change ‖(↑(x + 2) : AddCircle (2 : ℝ))‖ = ‖(x : AddCircle (2 : ℝ))‖
  rw [AddCircle.coe_add_period]

theorem periodicTent_base (x : ℝ) (hx : x ∈ Set.Icc (-1) 1) :
    periodicTent x = |x| := by
  apply (AddCircle.norm_coe_eq_abs_iff (2 : ℝ) (by norm_num)).mpr
  simpa using abs_le.mpr hx

theorem periodicTent_bounds (x : ℝ) : 0 ≤ periodicTent x ∧ periodicTent x ≤ 1 := by
  refine ⟨norm_nonneg _, ?_⟩
  simpa [periodicTent, Specs.SingleVariableAnalysis.Ch16.TentContinuity.periodicTentValue]
    using AddCircle.norm_le_half_period (2 : ℝ) (x := (x : AddCircle (2 : ℝ)))
    (by norm_num)

theorem periodicTent_lipschitz (s t : ℝ) :
    |periodicTent s - periodicTent t| ≤ |s - t| := by
  calc
    |periodicTent s - periodicTent t| ≤
        ‖(s : AddCircle (2 : ℝ)) - (t : AddCircle (2 : ℝ))‖ :=
      abs_norm_sub_norm_le _ _
    _ ≤ |s - t| := by
      change ‖(↑(s - t) : AddCircle (2 : ℝ))‖ ≤ |s - t|
      exact QuotientAddGroup.norm_mk_le_norm

theorem periodicTent_continuous : Continuous periodicTent := by
  have h : LipschitzWith 1 periodicTent := by
    rw [lipschitzWith_iff_dist_le_mul]
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using periodicTent_lipschitz
  exact h.continuous

theorem periodicTent_even_cell (k : ℤ) (x : ℝ)
    (hl : 2 * (k : ℝ) ≤ x) (hu : x ≤ 2 * (k : ℝ) + 1) :
    periodicTent x = x - 2 * (k : ℝ) := by
  have hs := periodicTent_period.sub_int_mul_eq (x := x) k
  have hb := periodicTent_base (x - (k : ℝ) * 2) (by constructor <;> linarith)
  rw [hs, abs_of_nonneg (by linarith)] at hb
  convert hb using 1; ring

theorem periodicTent_odd_cell (k : ℤ) (x : ℝ)
    (hl : 2 * (k : ℝ) + 1 ≤ x) (hu : x ≤ 2 * (k : ℝ) + 2) :
    periodicTent x = 2 * (k : ℝ) + 2 - x := by
  have hs := periodicTent_period.sub_int_mul_eq (x := x) (k + 1)
  have hb := periodicTent_base (x - ((k + 1 : ℤ) : ℝ) * 2)
    (by push_cast; constructor <;> linarith)
  rw [hs, abs_of_nonpos (by push_cast; linarith)] at hb
  push_cast at hb
  linarith

theorem periodicTent_affine (k : ℤ) :
    ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
      ∀ x ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1),
        periodicTent x = periodicTent k + a * (x - k) := by
  obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro x hx
    have hb := periodicTent_even_cell j (2 * (j : ℝ)) (by rfl) (by linarith)
    have hf := periodicTent_even_cell j x (by simpa using hx.1) (by simpa using hx.2)
    push_cast
    rw [hb, hf]
    ring
  · refine ⟨-1, Or.inr rfl, ?_⟩
    intro x hx
    have hb := periodicTent_odd_cell j (2 * (j : ℝ) + 1) (by rfl) (by linarith)
    have hf := periodicTent_odd_cell j x (by simpa using hx.1)
      (by push_cast at hx; linarith [hx.2])
    push_cast
    rw [hb, hf]
    ring

def tentSeriesTerm : ℕ → ℝ → ℝ :=
  fun n x => (3 / 4 : ℝ) ^ n * periodicTent ((4 : ℝ) ^ n * x)

def tentSeries : ℝ → ℝ := fun x => ∑' n : ℕ, tentSeriesTerm n x

theorem tentSeriesTerm_bound (n : ℕ) (x : ℝ) :
    |tentSeriesTerm n x| ≤ (3 / 4 : ℝ) ^ n := by
  have hp : 0 ≤ (3 / 4 : ℝ) ^ n := pow_nonneg (by norm_num) n
  have hb := periodicTent_bounds ((4 : ℝ) ^ n * x)
  dsimp [tentSeriesTerm]
  rw [abs_mul, abs_of_nonneg hp, abs_of_nonneg hb.1]
  simpa using mul_le_mul_of_nonneg_left hb.2 hp

theorem tentSeries_summable (x : ℝ) : Summable (fun n => tentSeriesTerm n x) := by
  apply Summable.of_norm_bounded
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num))
  simpa only [Real.norm_eq_abs] using fun n => tentSeriesTerm_bound n x

theorem tentSeries_uniform : RealUniformConverges
    (fun N x => realPartialSum (fun n => tentSeriesTerm n x) N) tentSeries := by
  have hM : RealSeriesConverges (fun n : ℕ => (3 / 4 : ℝ) ^ n) :=
    (real_geometric_series_converges_iff _).mpr (by norm_num)
  obtain ⟨⟨f, hf⟩, _⟩ := real_m_test tentSeriesTerm (fun n => (3 / 4 : ℝ) ^ n)
    (fun n => pow_nonneg (by norm_num) n) tentSeriesTerm_bound hM
  have he : f = tentSeries := by
    funext x
    have h₁ := (realSequenceConverges_iff _ _).mp
      (realUniformConverges_pointwise _ _ hf x)
    have h₂ := ((tentSeries_summable x).hasSum.tendsto_sum_nat).comp
      (Filter.tendsto_add_atTop_nat 1)
    exact tendsto_nhds_unique h₁ h₂
  rwa [he] at hf

theorem tentSeries_continuous : Continuous tentSeries := by
  apply realUniformLimit_continuous _ _ _ tentSeries_uniform
  intro N
  unfold realPartialSum
  apply continuous_finsetSum
  intro n _
  exact continuous_const.mul
    (periodicTent_continuous.comp (continuous_const.mul continuous_id))

end SingleVariableAnalysis
