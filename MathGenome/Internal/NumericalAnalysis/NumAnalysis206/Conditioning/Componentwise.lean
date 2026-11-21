import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Conditioning.Componentwise
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Conditioning.Errors
import Mathlib.Tactic.LinearCombination

noncomputable section
open scoped BigOperators NNReal ENNReal
universe u v w
namespace NumAnalysis206.Conditioning.Componentwise

def residual : Specs.NumAnalysis206.Conditioning.Componentwise.residualType :=
  @Specs.NumAnalysis206.Conditioning.Componentwise.residual

def rowScale : Specs.NumAnalysis206.Conditioning.Componentwise.rowScaleType :=
  @Specs.NumAnalysis206.Conditioning.Componentwise.rowScale

def feasible : Specs.NumAnalysis206.Conditioning.Componentwise.feasibleType :=
  @Specs.NumAnalysis206.Conditioning.Componentwise.feasible

def backwardError : Specs.NumAnalysis206.Conditioning.Componentwise.backwardErrorType :=
  @Specs.NumAnalysis206.Conditioning.Componentwise.backwardError

def formula : Specs.NumAnalysis206.Conditioning.Componentwise.formulaType :=
  @Specs.NumAnalysis206.Conditioning.Componentwise.formula

variable {I : Type u} {J : Type v} {K : Type w} [Fintype J] [RCLike K]

/-- The conjugate phase, expressed using field division. It vanishes at zero. -/
def phase (z : K) : K := (‖z‖ : K) / z

lemma phase_mul (z : K) : phase z * z = (‖z‖ : K) := by
  by_cases hz : z = 0
  · simp [phase, hz]
  · exact div_mul_cancel₀ _ hz

lemma norm_phase_le (z : K) : ‖phase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [phase, hz]
  · simp [phase, norm_div, hz]

lemma lower_bound (A : Matrix I J K) (b : I → K) (x : J → K)
    (E : Matrix I J ℝ≥0) (f : I → ℝ≥0) (ε : ℝ≥0)
    (h : feasible A b x E f ε) :
    ∀ i, ‖residual A b x i‖₊ ≤ ε * rowScale E f x i := by
  obtain ⟨dA, db, heq, hA, hb⟩ := h
  intro i
  have hr : residual A b x i = (∑ j, dA i j * x j) - db i := by
    have hi := congrFun heq i
    simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Pi.add_apply, add_mul,
      Finset.sum_add_distrib] at hi
    change b i - ∑ j, A i j * x j = _
    linear_combination -hi
  rw [hr]
  apply NNReal.coe_le_coe.mp
  change ‖(∑ j, dA i j * x j) - db i‖ ≤ (ε : ℝ) * (rowScale E f x i : ℝ)
  simp only [rowScale, Specs.NumAnalysis206.Conditioning.Componentwise.rowScale,
    NNReal.coe_add, NNReal.coe_sum, NNReal.coe_mul, coe_nnnorm]
  calc
    ‖(∑ j, dA i j * x j) - db i‖ ≤ ‖∑ j, dA i j * x j‖ + ‖db i‖ := norm_sub_le _ _
    _ ≤ (∑ j, ‖dA i j * x j‖) + ‖db i‖ := add_le_add (norm_sum_le _ _) le_rfl
    _ ≤ (∑ j, (ε : ℝ) * (E i j : ℝ) * ‖x j‖) + (ε : ℝ) * (f i : ℝ) := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro j _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr (hA i j)) (norm_nonneg _)
      · exact NNReal.coe_le_coe.mpr (hb i)
    _ = _ := by simp only [mul_add, Finset.mul_sum, mul_assoc]

lemma row_factor (r : K) (D ε : ℝ≥0) (h : ‖r‖₊ ≤ ε * D) :
    ‖r / ((D : ℝ) : K)‖ ≤ (ε : ℝ) ∧
      (r / ((D : ℝ) : K)) * ((D : ℝ) : K) = r := by
  by_cases hD : D = 0
  · have hr : r = 0 := by simpa [hD] using h
    simp [hD, hr]
  · have hpos : (0 : ℝ) < D := by exact_mod_cast (pos_iff_ne_zero.mpr hD)
    constructor
    · rw [norm_div, RCLike.norm_ofReal, abs_of_nonneg D.coe_nonneg]
      apply (div_le_iff₀ hpos).mpr
      exact NNReal.coe_le_coe.mpr h
    · apply div_mul_cancel₀
      exact_mod_cast (ne_of_gt hpos)

lemma upper_bound (A : Matrix I J K) (b : I → K) (x : J → K)
    (E : Matrix I J ℝ≥0) (f : I → ℝ≥0) (ε : ℝ≥0)
    (h : ∀ i, ‖residual A b x i‖₊ ≤ ε * rowScale E f x i) :
    feasible A b x E f ε := by
  let c : I → K := fun i => residual A b x i / (((rowScale E f x i : ℝ)) : K)
  have hc (i : I) : ‖c i‖ ≤ (ε : ℝ) ∧
      c i * (((rowScale E f x i : ℝ)) : K) = residual A b x i :=
    row_factor _ _ _ (h i)
  let dA : Matrix I J K := fun i j => c i * ((E i j : ℝ) : K) * phase (x j)
  let db : I → K := fun i => -(c i * ((f i : ℝ) : K))
  refine ⟨dA, db, ?_, ?_, ?_⟩
  · ext i
    have hscale : (((rowScale E f x i : ℝ)) : K) =
        (∑ j, ((E i j : ℝ) : K) * (‖x j‖ : K)) + ((f i : ℝ) : K) := by
      simp [rowScale, Specs.NumAnalysis206.Conditioning.Componentwise.rowScale]
    have hr : (∑ j, dA i j * x j) - db i = residual A b x i := by
      simp only [dA, db, mul_assoc, phase_mul, sub_neg_eq_add]
      rw [← Finset.mul_sum, ← mul_add, ← hscale]
      exact (hc i).2
    have hi : b i - ∑ j, A i j * x j = (∑ j, dA i j * x j) - db i := hr.symm
    change (A + dA).mulVec x i = (b + db) i
    simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Pi.add_apply, add_mul,
      Finset.sum_add_distrib]
    linear_combination -hi
  · intro i j
    apply NNReal.coe_le_coe.mp
    change ‖c i * ((E i j : ℝ) : K) * phase (x j)‖ ≤ (ε : ℝ) * (E i j : ℝ)
    rw [norm_mul, norm_mul, RCLike.norm_ofReal, abs_of_nonneg (E i j).coe_nonneg]
    calc
      _ ≤ ‖c i‖ * (E i j : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (norm_phase_le _) (mul_nonneg (norm_nonneg _) (E i j).coe_nonneg)
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right (hc i).1 (E i j).coe_nonneg
  · intro i
    apply NNReal.coe_le_coe.mp
    change ‖-(c i * ((f i : ℝ) : K))‖ ≤ (ε : ℝ) * (f i : ℝ)
    rw [norm_neg, norm_mul, RCLike.norm_ofReal, abs_of_nonneg (f i).coe_nonneg]
    exact mul_le_mul_of_nonneg_right (hc i).1 (f i).coe_nonneg

variable [Fintype I]

theorem feasible_iff :
    Specs.NumAnalysis206.Conditioning.Componentwise.feasible_iffStatement := by
  intro I J K _ _ _ A b x E f ε
  exact ⟨lower_bound A b x E f ε, upper_bound A b x E f ε⟩

lemma formula_le_iff (A : Matrix I J K) (b : I → K) (x : J → K)
    (E : Matrix I J ℝ≥0) (f : I → ℝ≥0) (ε : ℝ≥0) :
    formula A b x E f ≤ (ε : ℝ≥0∞) ↔ feasible A b x E f ε := by
  exact (NumAnalysis206.Conditioning.componentwiseSize_le_iff
    (rowScale E f x) (residual A b x) ε).trans (feasible_iff A b x E f ε).symm

/-- The extended infimum agrees with the componentwise maximum, even if it is infinite. -/
theorem backwardError_eq_formula :
    Specs.NumAnalysis206.Conditioning.Componentwise.backwardError_eq_formulaStatement := by
  intro I J K _ _ _ A b x E f
  change backwardError A b x E f = formula A b x E f
  apply le_antisymm
  · by_cases ht : formula A b x E f = ⊤
    · rw [ht]; exact le_top
    · have hc := ENNReal.coe_toNNReal ht
      have hf : feasible A b x E f (formula A b x E f).toNNReal :=
        (formula_le_iff A b x E f _).mp hc.ge
      calc
        backwardError A b x E f ≤ ((formula A b x E f).toNNReal : ℝ≥0∞) :=
          sInf_le ⟨_, hf, rfl⟩
        _ = formula A b x E f := hc
  · apply le_sInf
    rintro t ⟨ε, hε, rfl⟩
    exact (formula_le_iff A b x E f ε).mpr hε

/-- The infimum is achieved by actual perturbations at every finite value. -/
theorem finite_attained :
    Specs.NumAnalysis206.Conditioning.Componentwise.finite_attainedStatement := by
  intro I J K _ _ _ A b x E f ht
  have hc := ENNReal.coe_toNNReal ht
  refine ⟨_, hc, ?_⟩
  apply (formula_le_iff A b x E f _).mp
  rw [hc, backwardError_eq_formula A b x E f]
  exact le_rfl

/-- A row with no allowed effect and nonzero residual is infeasible at every finite budget. -/
theorem zero_row : Specs.NumAnalysis206.Conditioning.Componentwise.zero_rowStatement := by
  intro I J K _ _ _ A b x E f i hs hr
  rw [backwardError_eq_formula A b x E f]
  exact NumAnalysis206.Conditioning.componentwiseSize_zero_scale
    (rowScale E f x) (residual A b x) i hs hr

theorem empty_rows : Specs.NumAnalysis206.Conditioning.Componentwise.empty_rowsStatement := by
  intro I J K _ _ _ _ A b x E f
  rw [backwardError_eq_formula A b x E f]
  simp [Specs.NumAnalysis206.Conditioning.Componentwise.formula,
    Specs.NumAnalysis206.Conditioning.Errors.componentwiseSize]

end NumAnalysis206.Conditioning.Componentwise
