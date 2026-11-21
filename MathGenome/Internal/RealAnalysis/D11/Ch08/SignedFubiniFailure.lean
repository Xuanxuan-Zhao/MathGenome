import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.SignedFubiniFailure
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral
import MathGenome.Internal.RealAnalysis.D11.Ch05.AtomicIntegrals
import MathGenome.Internal.RealAnalysis.D11.Ch08.ProductSigma
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! The signed counting example in paper.tex:2865–2878. All scalar integrals
used below have separately proved integrability; no value of a totalized
integral on the nonintegrable product function is used. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace D11.Ch08.SignedFubiniFailure

abbrev exampleFunction : ℕ+ → ℕ+ → ℝ :=
  Specs.D11.Ch08.SignedFubiniFailure.exampleFunction_value

private lemma self_ne_succ (n : ℕ+) : n ≠ n + 1 := by
  intro h
  have h' := congrArg (fun k : ℕ+ => (k : ℕ)) h
  simp only [PNat.add_coe, PNat.val_ofNat] at h'
  omega

private lemma succ_ne_one (n : ℕ+) : n + 1 ≠ 1 := by
  intro h
  have h' := congrArg (fun k : ℕ+ => (k : ℕ)) h
  have := n.pos
  simp only [PNat.add_coe, PNat.val_ofNat] at h'
  omega

private lemma row_one (n : ℕ+) :
    exampleFunction 1 n = if n = 1 then 1 else 0 := by
  have h : (1 : ℕ+) ≠ n + 1 := (succ_ne_one n).symm
  simp [exampleFunction, Specs.D11.Ch08.SignedFubiniFailure.exampleFunction_value, h, eq_comm]

private lemma row_succ (k n : ℕ+) :
    exampleFunction (k + 1) n =
      (if n = k + 1 then 1 else 0) - (if n = k then 1 else 0) := by
  by_cases h : n = k + 1
  · subst n
    simp [exampleFunction, Specs.D11.Ch08.SignedFubiniFailure.exampleFunction_value,
      (self_ne_succ k).symm]
  · by_cases h' : n = k
    · subst n
      simp [exampleFunction, Specs.D11.Ch08.SignedFubiniFailure.exampleFunction_value,
        self_ne_succ k, (self_ne_succ k).symm]
    · simp [exampleFunction, Specs.D11.Ch08.SignedFubiniFailure.exampleFunction_value,
        Ne.symm h, h, h', Ne.symm h']

private lemma column (m n : ℕ+) :
    exampleFunction m n =
      (if m = n then 1 else 0) - (if m = n + 1 then 1 else 0) := by
  by_cases h : m = n
  · subst m
    simp [exampleFunction, Specs.D11.Ch08.SignedFubiniFailure.exampleFunction_value,
      self_ne_succ]
  · simp only [exampleFunction, Specs.D11.Ch08.SignedFubiniFailure.exampleFunction_value,
      ite_eq_right h, zero_sub]
    split_ifs <;> norm_num

theorem product_full : Specs.D11.Ch08.SignedFubiniFailure.product_full := by
  apply top_unique
  intro s _
  exact Set.Countable.measurableSet (Set.to_countable s)

theorem measurable_function : Specs.D11.Ch08.SignedFubiniFailure.measurable_function :=
  measurable_of_countable _

theorem sections_finite_support :
    Specs.D11.Ch08.SignedFubiniFailure.sections_finite_support := by
  classical
  constructor
  · intro m
    change (Function.support (exampleFunction m)).Finite
    induction m using PNat.recOn with
    | one =>
      apply (Set.finite_singleton (1 : ℕ+)).subset
      intro n hn
      by_contra h
      have h' : n ≠ 1 := by simpa only [Set.mem_singleton_iff] using h
      exact hn (by simp [row_one, h'])
    | succ k _ =>
      apply (Set.toFinite ({k + 1, k} : Set ℕ+)).subset
      intro n hn
      by_contra h
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h
      exact hn (by simp [row_succ, h.1, h.2])
  · intro n
    change (Function.support (fun m => exampleFunction m n)).Finite
    apply (Set.toFinite ({n, n + 1} : Set ℕ+)).subset
    intro m hm
    by_contra h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h
    exact hm (by simp [column, h.1, h.2])

private lemma integrable_of_finite_support (g : ℕ+ → ℝ)
    (hg : (Function.support g).Finite) : Integrable g Measure.count := by
  apply integrable_count_iff.mpr
  apply summable_of_hasFiniteSupport
  have heq : Function.support (fun x => ‖g x‖) = Function.support g := by
    ext x
    simp
  change (Function.support (fun x => ‖g x‖)).Finite
  rw [heq]
  exact hg

theorem sections_integrable : Specs.D11.Ch08.SignedFubiniFailure.sections_integrable := by
  constructor
  · intro m
    exact (D11.Ch06.ScalarIntegral.native_integrable_iff _ _
      (measurable_of_countable _)).mpr
      (integrable_of_finite_support _ (sections_finite_support.1 m))
  · intro n
    exact (D11.Ch06.ScalarIntegral.native_integrable_iff _ _
      (measurable_of_countable _)).mpr
      (integrable_of_finite_support _ (sections_finite_support.2 n))

theorem row_sums (m : ℕ+) :
    (∑' n : ℕ+, exampleFunction m n) = if m = 1 then 1 else 0 := by
  induction m using PNat.recOn with
  | one => simp [row_one]
  | succ k _ =>
    simp_rw [row_succ]
    rw [((hasSum_ite_eq (k + 1) (1 : ℝ)).summable).tsum_sub
      (hasSum_ite_eq k (1 : ℝ)).summable]
    simp [succ_ne_one]

theorem column_sums (n : ℕ+) : (∑' m : ℕ+, exampleFunction m n) = 0 := by
  simp_rw [column]
  rw [((hasSum_ite_eq n (1 : ℝ)).summable).tsum_sub
    (hasSum_ite_eq (n + 1) (1 : ℝ)).summable]
  simp

theorem iterated_sums : Specs.D11.Ch08.SignedFubiniFailure.iterated_sums := by
  change (∑' m : ℕ+, ∑' n : ℕ+, exampleFunction m n) = 1 ∧
    (∑' n : ℕ+, ∑' m : ℕ+, exampleFunction m n) = 0
  constructor
  · simp_rw [row_sums]
    simp
  · simp_rw [column_sums]
    simp

private lemma integral_counting (g : ℕ+ → ℝ) (hg : (Function.support g).Finite) :
    (∫ n : ℕ+, g n ∂Measure.count) = ∑' n : ℕ+, g n := by
  rw [integral_countable (integrable_of_finite_support g hg)]
  simp

private lemma row_integral (m : ℕ+) :
    (∫ n : ℕ+, exampleFunction m n ∂Measure.count) = if m = 1 then 1 else 0 := by
  rw [integral_counting _ (sections_finite_support.1 m), row_sums]

private lemma column_integral (n : ℕ+) :
    (∫ m : ℕ+, exampleFunction m n ∂Measure.count) = 0 := by
  rw [integral_counting _ (sections_finite_support.2 n), column_sums]

private lemma single_finite_support (a : ℕ+) :
    (Function.support (fun n : ℕ+ => if n = a then (1 : ℝ) else 0)).Finite := by
  apply (Set.finite_singleton a).subset
  intro n hn
  by_contra h
  have h' : n ≠ a := by simpa only [Set.mem_singleton_iff] using h
  exact hn (by simp [h'])

theorem outer_integrable : Specs.D11.Ch08.SignedFubiniFailure.outer_integrable := by
  change Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value Measure.count
      (fun m : ℕ+ => ∫ n : ℕ+, exampleFunction m n ∂Measure.count) ∧
    Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value Measure.count
      (fun n : ℕ+ => ∫ m : ℕ+, exampleFunction m n ∂Measure.count)
  constructor
  · simp_rw [row_integral]
    exact (D11.Ch06.ScalarIntegral.native_integrable_iff _ _
      (measurable_of_countable _)).mpr
      (integrable_of_finite_support _ (single_finite_support 1))
  · simp_rw [column_integral]
    exact (D11.Ch06.ScalarIntegral.native_integrable_iff _ _
      (measurable_of_countable _)).mpr (integrable_zero _ _ _)

theorem iterated_integrals : Specs.D11.Ch08.SignedFubiniFailure.iterated_integrals := by
  change (∫ m : ℕ+, ∫ n : ℕ+, exampleFunction m n ∂Measure.count ∂Measure.count) = 1 ∧
    (∫ n : ℕ+, ∫ m : ℕ+, exampleFunction m n ∂Measure.count ∂Measure.count) = 0
  constructor
  · simp_rw [row_integral]
    rw [integral_counting _ (single_finite_support 1)]
    simp
  · simp_rw [column_integral]
    simp

/-- The infinitely many diagonal entries alone force infinite absolute mass. -/
theorem absolute_sum : Specs.D11.Ch08.SignedFubiniFailure.absolute_sum := by
  change (∑' p : ℕ+ × ℕ+, ENNReal.ofReal |exampleFunction p.1 p.2|) = ∞
  apply top_unique
  have hinj : Function.Injective (fun n : ℕ+ => (n, n)) := by
    intro a b h
    exact congrArg Prod.fst h
  have h := ENNReal.tsum_comp_le_tsum_of_injective hinj
    (fun p : ℕ+ × ℕ+ => ENNReal.ofReal |exampleFunction p.1 p.2|)
  simpa [exampleFunction, Specs.D11.Ch08.SignedFubiniFailure.exampleFunction_value,
    ENNReal.tsum_const_eq_top_of_ne_zero (one_ne_zero : (1 : ℝ≥0∞) ≠ 0)] using h

theorem absolute_product_integral :
    Specs.D11.Ch08.SignedFubiniFailure.absolute_product_integral := by
  change D11.Ch05.NonnegativeIntegral.nonnegativeIntegral
    ((Measure.count : Measure ℕ+).prod Measure.count)
    (fun p : ℕ+ × ℕ+ => ENNReal.ofReal |exampleFunction p.1 p.2|) = ∞
  rw [D11.Ch05.NonnegativeIntegral.integral_eq_lintegral,
    lintegral_prod_symm _ (measurable_of_countable _).aemeasurable]
  apply top_unique
  calc
    ∞ = ∫⁻ _ : ℕ+, (1 : ℝ≥0∞) ∂Measure.count := by
      rw [lintegral_count]
      exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
    _ ≤ ∫⁻ n : ℕ+, ∫⁻ m : ℕ+,
        ENNReal.ofReal |exampleFunction m n| ∂Measure.count ∂Measure.count := by
      apply lintegral_mono
      intro n
      change (1 : ℝ≥0∞) ≤ ∫⁻ m : ℕ+, ENNReal.ofReal |exampleFunction m n| ∂Measure.count
      rw [lintegral_count]
      have h := ENNReal.le_tsum (f := fun m : ℕ+ =>
        ENNReal.ofReal |exampleFunction m n|) n
      simpa [exampleFunction, Specs.D11.Ch08.SignedFubiniFailure.exampleFunction_value] using h

theorem not_integrable : Specs.D11.Ch08.SignedFubiniFailure.not_integrable := by
  intro h
  have hfin := h.2
  change D11.Ch05.NonnegativeIntegral.nonnegativeIntegral
    ((Measure.count : Measure ℕ+).prod Measure.count)
    (fun p : ℕ+ × ℕ+ => ENNReal.ofReal ‖exampleFunction p.1 p.2‖) < ∞ at hfin
  simp only [Real.norm_eq_abs] at hfin
  have habs : D11.Ch05.NonnegativeIntegral.nonnegativeIntegral
      ((Measure.count : Measure ℕ+).prod Measure.count)
      (fun p : ℕ+ × ℕ+ => ENNReal.ofReal |exampleFunction p.1 p.2|) = ∞ :=
    absolute_product_integral
  rw [habs] at hfin
  exact (lt_irrefl ∞) hfin

theorem interchange_failure : Specs.D11.Ch08.SignedFubiniFailure.interchange_failure := by
  change (∫ m : ℕ+, ∫ n : ℕ+, exampleFunction m n ∂Measure.count ∂Measure.count) ≠
    (∫ n : ℕ+, ∫ m : ℕ+, exampleFunction m n ∂Measure.count ∂Measure.count)
  rw [iterated_integrals.1, iterated_integrals.2]
  exact one_ne_zero

end D11.Ch08.SignedFubiniFailure
