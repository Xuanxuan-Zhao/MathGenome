import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch02.IndependentGrouping
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch02.IndependentIntegrals
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.ProbabilityBounds
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch08.KolmogorovMaximalInequality

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ProbabilityFoundations.Ch08

universe u

namespace Kolmogorov

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {n : ℕ}

def initialIndices (n k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val < k)

noncomputable def initialSum (X : Fin n → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ initialIndices n k, X i ω

omit mΩ in
lemma initialSum_zero (X : Fin n → Ω → ℝ) : initialSum X 0 = 0 := by
  ext ω
  simp [initialSum, initialIndices]

omit mΩ in
lemma initialSum_of_le (X : Fin n → Ω → ℝ) {k : ℕ} (hk : n ≤ k) :
    initialSum X k = fun ω => ∑ i, X i ω := by
  ext ω
  simp [initialSum, initialIndices, show ∀ i : Fin n, i.val < k from
    fun i => lt_of_lt_of_le i.isLt hk]

omit mΩ in
lemma initialSum_succ (X : Fin n → Ω → ℝ) {k : ℕ} (hk : k < n) :
    initialSum X (k + 1) = fun ω => initialSum X k ω + X ⟨k, hk⟩ ω := by
  have he : initialIndices n (k + 1) = insert ⟨k, hk⟩ (initialIndices n k) := by
    ext i
    simp [initialIndices, Fin.ext_iff]
    omega
  ext ω
  simp only [initialSum]
  rw [he, Finset.sum_insert]
  · exact add_comm _ _
  · simp [initialIndices]

noncomputable def pastFiltration (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) :
    Filtration ℕ mΩ where
  seq k := ⨆ i : Fin n, ⨆ (_ : i.val < k), (inferInstance : MeasurableSpace ℝ).comap (X i)
  mono' _ _ hkl := iSup₂_le fun i hi =>
    le_iSup_of_le i (le_iSup_of_le (lt_of_lt_of_le hi hkl) le_rfl)
  le' _k := iSup₂_le fun i _ => (hX i).comap_le

lemma initialSum_stronglyMeasurable (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (k : ℕ) :
    StronglyMeasurable[pastFiltration X hX k] (initialSum X k) := by
  apply Measurable.stronglyMeasurable
  apply Finset.measurable_sum
  intro i hi
  apply Measurable.mono (comap_measurable _ :
    Measurable[(inferInstance : MeasurableSpace ℝ).comap (X i)] (X i))
  · exact le_iSup_of_le i (le_iSup_of_le (Finset.mem_filter.mp hi).2 le_rfl)
  · exact le_rfl

lemma initialSum_memLp (P : Measure Ω) (X : Fin n → Ω → ℝ)
    (h2 : ∀ i, MemLp (X i) 2 P) (k : ℕ) : MemLp (initialSum X k) 2 P :=
  memLp_finsetSum _ (fun i _ => h2 i)

lemma past_indep_next (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hI : iIndepFun X P)
    {k : ℕ} (hk : k < n) :
    Indep (pastFiltration X hX k)
      ((inferInstance : MeasurableSpace ℝ).comap (X ⟨k, hk⟩)) P := by
  have hd : Disjoint {i : Fin n | i.val < k} ({⟨k, hk⟩} : Set (Fin n)) := by
    apply Set.disjoint_left.mpr
    intro i hi hj
    simp only [Set.mem_singleton_iff] at hj
    subst i
    exact (lt_irrefl k) hi
  have hi := indep_iSup_of_disjoint (fun i => (hX i).comap_le) hI.iIndep hd
  simpa [pastFiltration] using hi

lemma mixed_integral_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hI : iIndepFun X P)
    (h2 : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, (∫ ω, X i ω ∂P) = 0)
    {k : ℕ} (hk : k < n) (s : Set Ω) (hs : MeasurableSet[pastFiltration X hX k] s) :
    (∫ ω in s, initialSum X k ω * X ⟨k, hk⟩ ω ∂P) = 0 := by
  have hm := (initialSum_stronglyMeasurable X hX k).measurable.indicator hs
  have hind : IndepFun (s.indicator (initialSum X k)) (X ⟨k, hk⟩) P :=
    (IndepFun_iff_Indep _ _ _).mpr
      (indep_of_indep_of_le_left (past_indep_next P X hX hI hk) hm.comap_le)
  have ha : MeasurableSet s := (pastFiltration X hX).le k _ hs
  rw [← integral_indicator ha]
  have he : s.indicator (fun ω => initialSum X k ω * X ⟨k, hk⟩ ω) =
      fun ω => s.indicator (initialSum X k) ω * X ⟨k, hk⟩ ω := by
    ext ω
    by_cases hω : ω ∈ s <;> simp [hω]
  rw [he, hind.integral_fun_mul_eq_mul_integral
    (hm.mono ((pastFiltration X hX).le k) le_rfl).aestronglyMeasurable
    (h2 ⟨k, hk⟩).aestronglyMeasurable, hmean, mul_zero]

set_option backward.isDefEq.respectTransparency false in
lemma square_submartingale (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hI : iIndepFun X P)
    (h2 : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, (∫ ω, X i ω ∂P) = 0) :
    Submartingale (fun k ω => (initialSum X k ω) ^ 2) (pastFiltration X hX) P := by
  have hLp := initialSum_memLp P X h2
  apply submartingale_of_setIntegral_le_succ
  · intro k
    exact (initialSum_stronglyMeasurable X hX k).pow 2
  · intro k
    exact (hLp k).integrable_sq
  · intro k s hs
    by_cases hk : k < n
    · have hm : Integrable (fun ω => initialSum X k ω * X ⟨k, hk⟩ ω) (P.restrict s) :=
        ((hLp k).integrable_mul (h2 ⟨k, hk⟩)).integrableOn
      have hS := (hLp k).integrable_sq.integrableOn (s := s)
      have hY := (h2 ⟨k, hk⟩).integrable_sq.integrableOn (s := s)
      rw [initialSum_succ X hk]
      have heq : (fun ω => (initialSum X k ω + X ⟨k, hk⟩ ω) ^ 2) =
          (fun ω => (initialSum X k ω) ^ 2 +
            2 * (initialSum X k ω * X ⟨k, hk⟩ ω) + (X ⟨k, hk⟩ ω) ^ 2) := by
        ext ω
        ring
      have hSM : Integrable (fun ω => (initialSum X k ω) ^ 2 +
          2 * (initialSum X k ω * X ⟨k, hk⟩ ω)) (P.restrict s) := hS.add (hm.const_mul 2)
      rw [heq, integral_add hSM hY,
        integral_add hS (hm.const_mul 2), integral_const_mul,
        mixed_integral_zero P X hX hI h2 hmean hk s hs, mul_zero, add_zero]
      exact le_add_of_nonneg_right (integral_nonneg fun ω => sq_nonneg _)
    · have hn : n ≤ k := Nat.le_of_not_gt hk
      rw [initialSum_of_le X hn, initialSum_of_le X (Nat.le_succ_of_le hn)]

lemma final_second_moment (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hI : iIndepFun X P)
    (h2 : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, (∫ ω, X i ω ∂P) = 0) :
    (∫ ω, (initialSum X n ω) ^ 2 ∂P) = ∑ i, Ch01.realVariance P (X i) := by
  have hmeas : Measurable (fun ω => ∑ i, X i ω) :=
    Finset.measurable_sum _ (fun i _ => hX i)
  have hzero : (∫ ω, ∑ i, X i ω ∂P) = 0 := by
    rw [integral_finsetSum _ (fun i _ => (h2 i).integrable (by norm_num))]
    simp [hmean]
  rw [initialSum_of_le X le_rfl]
  calc
    _ = variance (fun ω => ∑ i, X i ω) P := by
      rw [variance_eq_integral hmeas.aemeasurable, hzero]
      simp
    _ = ∑ i, variance (X i) P := by
      have he : (fun ω => ∑ i, X i ω) = ∑ i, X i := by
        ext ω
        simp
      rw [he]
      exact IndepFun.variance_sum (s := Finset.univ) (fun i _ => h2 i)
        (fun i _ j _ hij => hI.indepFun hij)
    _ = _ := Finset.sum_congr rfl fun i _ => variance_eq_integral (hX i).aemeasurable

lemma maximal_bound (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hI : iIndepFun X P)
    (h2 : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, (∫ ω, X i ω ∂P) = 0)
    (a : ℝ) (ha : 0 < a) :
    P {ω | ∃ k ∈ Finset.Icc 1 n, a ≤ |initialSum X k ω|} ≤
      ENNReal.ofReal ((∑ i, Ch01.realVariance P (X i)) / a ^ 2) := by
  let ε : ℝ≥0 := ⟨a ^ 2, sq_nonneg a⟩
  have hsub := square_submartingale P X hX hI h2 hmean
  have hmax := maximal_ineq hsub (fun k ω => sq_nonneg _) (ε := ε) n
  have hset : {ω | ∃ k ∈ Finset.Icc 1 n, a ≤ |initialSum X k ω|} ⊆
      {ω | (ε : ℝ) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => (initialSum X k ω) ^ 2)} := by
    intro ω hω
    obtain ⟨k, hk, hcross⟩ := hω
    change (ε : ℝ) ≤ _
    apply (Finset.le_sup'_iff _).mpr
    refine ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hk).2), ?_⟩
    change a ^ 2 ≤ (initialSum X k ω) ^ 2
    simpa only [sq_abs] using pow_le_pow_left₀ ha.le hcross 2
  have hb : (ε : ℝ≥0∞) *
      P {ω | ∃ k ∈ Finset.Icc 1 n, a ≤ |initialSum X k ω|} ≤
      ENNReal.ofReal (∑ i, Ch01.realVariance P (X i)) := by
    calc
      _ ≤ _ := mul_le_mul le_rfl (measure_mono hset) zero_le zero_le
      _ ≤ _ := hmax
      _ ≤ ENNReal.ofReal (∫ ω, (initialSum X n ω) ^ 2 ∂P) :=
        ENNReal.ofReal_le_ofReal (setIntegral_le_integral
          (initialSum_memLp P X h2 n).integrable_sq
          (Filter.Eventually.of_forall fun ω => sq_nonneg _))
      _ = _ := by rw [final_second_moment P X hX hI h2 hmean]
  have hε : (ε : ℝ≥0∞) = ENNReal.ofReal (a ^ 2) := by
    exact ENNReal.ofReal_coe_nnreal.symm
  rw [hε, mul_comm] at hb
  rw [ENNReal.ofReal_div_of_pos (sq_pos_of_pos ha)]
  exact (ENNReal.le_div_iff_mul_le
    (Or.inl (by simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using sq_pos_of_pos ha))
    (Or.inl ENNReal.ofReal_ne_top)).mpr hb

end Kolmogorov
/-- Kolmogorov's maximal inequality for a finite mutually independent centered
square-integrable real family. Indices `i : Fin n` label X₁,…,Xₙ; the
existence event records Sₖ crossing the non-strict threshold, for 1 ≤ k ≤ n. -/
theorem kolmogorov_maximal {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hI : Ch02.IndependentRandomElements P X)
    (h2 : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, (∫ ω, X i ω ∂P) = 0)
    (a : ℝ) (ha : 0 < a) :
    P {ω | ∃ k ∈ Finset.Icc 1 n,
      a ≤ |∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), X i ω|} ≤
      ENNReal.ofReal ((∑ i, Ch01.realVariance P (X i)) / a ^ 2) := by
  exact Kolmogorov.maximal_bound P X hX
    ((Ch02.independentRandomElements_iff_iIndepFun P X).mp hI) h2 hmean a ha

end ProbabilityFoundations.Ch08
