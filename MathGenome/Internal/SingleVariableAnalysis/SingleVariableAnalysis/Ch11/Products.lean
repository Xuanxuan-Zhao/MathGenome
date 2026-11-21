import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.PartialSums
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.LogConstruction
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.ExpAddition
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Products

/-!
# Ordered infinite products

K03.11.products, paper.tex:1139–1148. The product convention excludes
zero factors and zero limits. The finite-prefix identity and the quotient
of two consecutive partial products prove the elementary results. For positive
real factors, the finite logarithm identity reduces the characterization to
continuity of log and exp. The canonical log and exp are used only through the
upstream identifications of the project's inverse and factorial-series functions.
No unconditional summability of the logarithmic series is imposed.
-/
noncomputable section
namespace SingleVariableAnalysis
open Filter
open scoped BigOperators Topology

namespace Products

/-- Splitting off a prefix of length m, including the empty prefix. -/
theorem partial_product_split {K : Type*} [CommMonoid K] (v : ℕ → K) (m N : ℕ) :
    (∏ n ∈ Finset.range (N + m + 1), v n) =
      (∏ n ∈ Finset.range m, v n) * ∏ n ∈ Finset.range (N + 1), v (n + m) := by
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (Finset.prod_range_add v m (N + 1))

/-- A nonzero product limit forces the factors to tend to one. -/
theorem factors_tendsto_one {K : Type*} [NormedField K] (v : ℕ → K)
    (hv : ∀ n, v n ≠ 0) (P : K) (hP : P ≠ 0)
    (h : Tendsto (fun N => ∏ n ∈ Finset.range (N + 1), v n) atTop (𝓝 P)) :
    Tendsto v atTop (𝓝 1) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hshift := h.comp (tendsto_add_atTop_nat 1)
  have hquot := hshift.div h hP
  simp only [div_self hP] at hquot
  apply hquot.congr
  intro n
  change (∏ i ∈ Finset.range (n + 1 + 1), v i) /
    (∏ i ∈ Finset.range (n + 1), v i) = v (n + 1)
  rw [Finset.prod_range_succ]
  exact mul_div_cancel_left₀ (v (n + 1)) (Finset.prod_ne_zero_iff.mpr (fun i _ => hv i))

/-- Multiplication by the nonzero prefix preserves and reflects a limit. -/
theorem prefix_tendsto_iff {K : Type*} [NormedField K] (v : ℕ → K)
    (hv : ∀ n, v n ≠ 0) (m : ℕ) (Q : K) :
    Tendsto (fun N => ∏ n ∈ Finset.range (N + 1), v (n + m)) atTop (𝓝 Q) ↔
      Tendsto (fun N => ∏ n ∈ Finset.range (N + 1), v n) atTop
        (𝓝 ((∏ n ∈ Finset.range m, v n) * Q)) := by
  let C := ∏ n ∈ Finset.range m, v n
  have hC : C ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hv i)
  constructor
  · intro h
    apply (tendsto_add_atTop_iff_nat m).mp
    exact (h.const_mul C).congr (fun N => (partial_product_split v m N).symm)
  · intro h
    have ht := ((tendsto_add_atTop_iff_nat m).mpr h).const_mul C⁻¹
    simp only [partial_product_split v m] at ht
    change Tendsto (fun N => C⁻¹ * (C * ∏ n ∈ Finset.range (N + 1), v (n + m)))
      atTop (𝓝 (C⁻¹ * (C * Q))) at ht
    simpa only [← mul_assoc, inv_mul_cancel₀ hC, one_mul] using ht

end Products

/-- Inclusive ordered partial product. -/
def realPartialProduct (v : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∏ n ∈ Finset.range (N + 1), v n

/-- Nonzero factors with a nonzero finite partial-product limit. -/
def RealProductHasLimit (v : ℕ → ℝ) (P : ℝ) : Prop :=
  (∀ n, v n ≠ 0) ∧ P ≠ 0 ∧ RealSequenceConverges (realPartialProduct v) P

def RealProductConverges (v : ℕ → ℝ) : Prop :=
  ∃ P : ℝ, RealProductHasLimit v P

theorem real_product_necessary (v : ℕ → ℝ) (P : ℝ)
    (h : RealProductHasLimit v P) : RealSequenceConverges v 1 := by
  exact (realSequenceConverges_iff _ _).mpr
    (Products.factors_tendsto_one v h.1 P h.2.1 ((realSequenceConverges_iff _ _).mp h.2.2))

theorem real_product_prefix_iff (v : ℕ → ℝ) (hv : ∀ n, v n ≠ 0) (m : ℕ) (Q : ℝ) :
    RealProductHasLimit (fun n => v (n + m)) Q ↔
      RealProductHasLimit v ((∏ n ∈ Finset.range m, v n) * Q) := by
  have hC : (∏ n ∈ Finset.range m, v n) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hv i)
  constructor
  · rintro ⟨_, hQ, h⟩
    refine ⟨hv, mul_ne_zero hC hQ, ?_⟩
    exact (realSequenceConverges_iff _ _).mpr
      ((Products.prefix_tendsto_iff v hv m Q).mp ((realSequenceConverges_iff _ _).mp h))
  · rintro ⟨_, hQ, h⟩
    refine ⟨fun n => hv (n + m), (mul_ne_zero_iff.mp hQ).2, ?_⟩
    exact (realSequenceConverges_iff _ _).mpr
      ((Products.prefix_tendsto_iff v hv m Q).mpr ((realSequenceConverges_iff _ _).mp h))

theorem real_product_tail_converges_iff (v : ℕ → ℝ) (hv : ∀ n, v n ≠ 0) (m : ℕ) :
    RealProductConverges (fun n => v (n + m)) ↔ RealProductConverges v := by
  constructor
  · rintro ⟨Q, hQ⟩
    exact ⟨_, (real_product_prefix_iff v hv m Q).mp hQ⟩
  · rintro ⟨P, hP⟩
    let C := ∏ n ∈ Finset.range m, v n
    have hC : C ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hv i)
    refine ⟨P / C, (real_product_prefix_iff v hv m (P / C)).mpr ?_⟩
    simpa only [show (∏ n ∈ Finset.range m, v n) = C from rfl,
      mul_div_cancel₀ P hC] using hP

theorem real_product_finite_changes_iff (v w : ℕ → ℝ)
    (hv : ∀ n, v n ≠ 0) (hw : ∀ n, w n ≠ 0) (m : ℕ)
    (heq : ∀ n, m ≤ n → v n = w n) :
    RealProductConverges v ↔ RealProductConverges w := by
  rw [← real_product_tail_converges_iff v hv m,
    ← real_product_tail_converges_iff w hw m]
  have h : (fun n => v (n + m)) = (fun n => w (n + m)) :=
    funext (fun n => heq (n + m) (Nat.le_add_left m n))
  rw [h]

theorem real_product_zero_factor_excluded (v : ℕ → ℝ) (n : ℕ) (hn : v n = 0) :
    ¬ RealProductConverges v := by
  rintro ⟨P, hv, _⟩
  exact hv n hn

theorem real_product_zero_limit_excluded (v : ℕ → ℝ)
    (h : RealSequenceConverges (realPartialProduct v) 0) : ¬ RealProductConverges v := by
  rintro ⟨P, _, hP, hp⟩
  exact hP (tendsto_nhds_unique ((realSequenceConverges_iff _ _).mp hp)
    ((realSequenceConverges_iff _ _).mp h))

theorem real_half_product_formula (N : ℕ) :
    realPartialProduct (fun _ => (1 / 2 : ℝ)) N = (1 / 2 : ℝ) ^ (N + 1) := by
  simp [realPartialProduct]

theorem real_half_product_counterexample :
    (∀ n : ℕ, (fun _ : ℕ => (1 / 2 : ℝ)) n ≠ 0) ∧
    RealSequenceConverges (realPartialProduct (fun _ => (1 / 2 : ℝ))) 0 ∧
    ¬ RealProductConverges (fun _ => (1 / 2 : ℝ)) := by
  have ht : Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ (N + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).comp (tendsto_add_atTop_nat 1)
  have h : RealSequenceConverges (realPartialProduct (fun _ => (1 / 2 : ℝ))) 0 := by
    apply (realSequenceConverges_iff _ _).mpr
    exact ht.congr (fun N => (real_half_product_formula N).symm)
  exact ⟨fun _ => by norm_num, h, real_product_zero_limit_excluded _ h⟩

/-- Inclusive ordered partial product. -/
def complexPartialProduct (v : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∏ n ∈ Finset.range (N + 1), v n

/-- Nonzero factors with a nonzero finite partial-product limit. -/
def ComplexProductHasLimit (v : ℕ → ℂ) (P : ℂ) : Prop :=
  (∀ n, v n ≠ 0) ∧ P ≠ 0 ∧ ComplexSequenceConverges (complexPartialProduct v) P

def ComplexProductConverges (v : ℕ → ℂ) : Prop :=
  ∃ P : ℂ, ComplexProductHasLimit v P

theorem complex_product_necessary (v : ℕ → ℂ) (P : ℂ)
    (h : ComplexProductHasLimit v P) : ComplexSequenceConverges v 1 := by
  exact (complexSequenceConverges_iff _ _).mpr
    (Products.factors_tendsto_one v h.1 P h.2.1 ((complexSequenceConverges_iff _ _).mp h.2.2))

theorem complex_product_prefix_iff (v : ℕ → ℂ) (hv : ∀ n, v n ≠ 0) (m : ℕ) (Q : ℂ) :
    ComplexProductHasLimit (fun n => v (n + m)) Q ↔
      ComplexProductHasLimit v ((∏ n ∈ Finset.range m, v n) * Q) := by
  have hC : (∏ n ∈ Finset.range m, v n) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hv i)
  constructor
  · rintro ⟨_, hQ, h⟩
    refine ⟨hv, mul_ne_zero hC hQ, ?_⟩
    exact (complexSequenceConverges_iff _ _).mpr
      ((Products.prefix_tendsto_iff v hv m Q).mp ((complexSequenceConverges_iff _ _).mp h))
  · rintro ⟨_, hQ, h⟩
    refine ⟨fun n => hv (n + m), (mul_ne_zero_iff.mp hQ).2, ?_⟩
    exact (complexSequenceConverges_iff _ _).mpr
      ((Products.prefix_tendsto_iff v hv m Q).mpr ((complexSequenceConverges_iff _ _).mp h))

theorem complex_product_tail_converges_iff (v : ℕ → ℂ) (hv : ∀ n, v n ≠ 0) (m : ℕ) :
    ComplexProductConverges (fun n => v (n + m)) ↔ ComplexProductConverges v := by
  constructor
  · rintro ⟨Q, hQ⟩
    exact ⟨_, (complex_product_prefix_iff v hv m Q).mp hQ⟩
  · rintro ⟨P, hP⟩
    let C := ∏ n ∈ Finset.range m, v n
    have hC : C ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hv i)
    refine ⟨P / C, (complex_product_prefix_iff v hv m (P / C)).mpr ?_⟩
    simpa only [show (∏ n ∈ Finset.range m, v n) = C from rfl,
      mul_div_cancel₀ P hC] using hP

theorem complex_product_finite_changes_iff (v w : ℕ → ℂ)
    (hv : ∀ n, v n ≠ 0) (hw : ∀ n, w n ≠ 0) (m : ℕ)
    (heq : ∀ n, m ≤ n → v n = w n) :
    ComplexProductConverges v ↔ ComplexProductConverges w := by
  rw [← complex_product_tail_converges_iff v hv m,
    ← complex_product_tail_converges_iff w hw m]
  have h : (fun n => v (n + m)) = (fun n => w (n + m)) :=
    funext (fun n => heq (n + m) (Nat.le_add_left m n))
  rw [h]

theorem complex_product_zero_factor_excluded (v : ℕ → ℂ) (n : ℕ) (hn : v n = 0) :
    ¬ ComplexProductConverges v := by
  rintro ⟨P, hv, _⟩
  exact hv n hn

theorem complex_product_zero_limit_excluded (v : ℕ → ℂ)
    (h : ComplexSequenceConverges (complexPartialProduct v) 0) : ¬ ComplexProductConverges v := by
  rintro ⟨P, _, hP, hp⟩
  exact hP (tendsto_nhds_unique ((complexSequenceConverges_iff _ _).mp hp)
    ((complexSequenceConverges_iff _ _).mp h))

theorem complex_half_product_formula (N : ℕ) :
    complexPartialProduct (fun _ => (1 / 2 : ℂ)) N = (1 / 2 : ℂ) ^ (N + 1) := by
  simp [complexPartialProduct]

theorem complex_half_product_counterexample :
    (∀ n : ℕ, (fun _ : ℕ => (1 / 2 : ℂ)) n ≠ 0) ∧
    ComplexSequenceConverges (complexPartialProduct (fun _ => (1 / 2 : ℂ))) 0 ∧
    ¬ ComplexProductConverges (fun _ => (1 / 2 : ℂ)) := by
  have ht : Tendsto (fun N : ℕ => (1 / 2 : ℂ) ^ (N + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℂ)‖ < 1)).comp
      (tendsto_add_atTop_nat 1)
  have h : ComplexSequenceConverges (complexPartialProduct (fun _ => (1 / 2 : ℂ))) 0 := by
    apply (complexSequenceConverges_iff _ _).mpr
    exact ht.congr (fun N => (complex_half_product_formula N).symm)
  exact ⟨fun _ => by norm_num, h, complex_product_zero_limit_excluded _ h⟩

/-- Positive partial products cannot have a negative limit, and zero is excluded. -/
theorem real_positive_product_limit_positive (v : ℕ → ℝ) (hv : ∀ n, 0 < v n)
    (P : ℝ) (h : RealProductHasLimit v P) : 0 < P := by
  have hnonneg : 0 ≤ P := le_of_tendsto_of_tendsto'
    tendsto_const_nhds ((realSequenceConverges_iff _ _).mp h.2.2)
    (fun N => (Finset.prod_pos (fun n _ => hv n)).le)
  exact lt_of_le_of_ne hnonneg h.2.1.symm

/-- The finite logarithm identity uses the previously constructed inverse log. -/
theorem real_log_partial_product (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) (N : ℕ) :
    seriesLog (realPartialProduct v N) = realPartialSum (fun n => seriesLog (v n)) N := by
  rw [seriesLog_eq_realLog (realPartialProduct v N) (Finset.prod_pos (fun n _ => hv n))]
  unfold realPartialProduct realPartialSum
  rw [Real.log_prod (fun n _ => (hv n).ne')]
  exact Finset.sum_congr rfl (fun n _ => (seriesLog_eq_realLog _ (hv n)).symm)

theorem real_exp_log_partial_sum (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) (N : ℕ) :
    realPartialProduct v N = realSeriesExp (realPartialSum (fun n => seriesLog (v n)) N) := by
  rw [← real_log_partial_product v hv N]
  exact (expSeries_seriesLog _ (Finset.prod_pos (fun n _ => hv n))).symm

/-- A finite logarithmic sum produces exactly the exponential of that sum. -/
theorem real_product_of_log_sum (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) (S : ℝ)
    (h : RealSeriesHasSum (fun n => seriesLog (v n)) S) :
    RealProductHasLimit v (realSeriesExp S) := by
  refine ⟨fun n => (hv n).ne', (real_expSeries_pos S).ne', ?_⟩
  apply (realSequenceConverges_iff _ _).mpr
  have he : realSeriesExp = Real.exp := funext expSeries_eq_realExp
  have ht : Tendsto (fun N => realSeriesExp (realPartialSum (fun n => seriesLog (v n)) N))
      atTop (𝓝 (realSeriesExp S)) := by
    rw [he]
    exact Real.continuous_exp.continuousAt.tendsto.comp ((realSequenceConverges_iff _ _).mp h)
  exact ht.congr (fun N => (real_exp_log_partial_sum v hv N).symm)

/-- For each positive target P, both limits correspond under the inverse log. -/
theorem real_product_log_limit_iff (v : ℕ → ℝ) (hv : ∀ n, 0 < v n)
    (P : ℝ) (hP : 0 < P) :
    RealProductHasLimit v P ↔
      RealSeriesHasSum (fun n => seriesLog (v n)) (seriesLog P) := by
  constructor
  · intro h
    apply (realSequenceConverges_iff _ _).mpr
    have ht := (Real.continuousAt_log hP.ne').tendsto.comp
      ((realSequenceConverges_iff _ _).mp h.2.2)
    rw [← seriesLog_eq_realLog P hP] at ht
    apply ht.congr
    intro N
    change Real.log (realPartialProduct v N) = _
    rw [← seriesLog_eq_realLog (realPartialProduct v N) (Finset.prod_pos (fun n _ => hv n))]
    exact real_log_partial_product v hv N
  · intro h
    have ht := real_product_of_log_sum v hv (seriesLog P) h
    rwa [show realSeriesExp (seriesLog P) = P from expSeries_seriesLog P hP] at ht

/-- Equivalence for ordinary ordered series, including conditional log series. -/
theorem real_positive_product_iff_log_series (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) :
    RealProductConverges v ↔ RealSeriesConverges (fun n => seriesLog (v n)) := by
  constructor
  · rintro ⟨P, h⟩
    exact ⟨seriesLog P, (real_product_log_limit_iff v hv P
      (real_positive_product_limit_positive v hv P h)).mp h⟩
  · rintro ⟨S, h⟩
    exact ⟨realSeriesExp S, real_product_of_log_sum v hv S h⟩

end SingleVariableAnalysis
