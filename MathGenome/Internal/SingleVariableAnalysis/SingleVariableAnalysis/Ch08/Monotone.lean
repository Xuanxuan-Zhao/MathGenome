import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Monotone
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Continuous
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.FiniteChanges
import Mathlib.Topology.Order.ExtendFrom

namespace SingleVariableAnalysis.Riemann
open scoped BigOperators Topology
open Filter

/-- On every partition, monotonicity bounds the gap by mesh times total rise. -/
theorem monotone_darboux_gap_le (f : ℝ → ℝ) {a b : ℝ}
    (hf : BoundedOnInterval f a b) (hm : MonotoneOn f (Set.Icc a b))
    (P : Partition a b) :
    upperSum f P hf - lowerSum f P hf ≤ mesh P * (f b - f a) := by
  have hv (j : Fin (P.n+1)) : P.point j ∈ Set.Icc a b := by
    exact ⟨by simpa only [P.first] using P.strictMono.monotone (Fin.zero_le j),
      by simpa only [P.last] using P.strictMono.monotone (Fin.le_last j)⟩
  have hc (i : Fin P.n) :
      cellSupremum f P hf i - cellInfimum f P hf i ≤
        f (P.point i.succ) - f (P.point i.castSucc) := by
    have hu : cellSupremum f P hf i ≤ f (P.point i.succ) := by
      apply (cell_bounds f P hf i).2.2
      rintro _ ⟨x, hx, rfl⟩
      exact hm (cell_subset_interval P i hx) (hv _) hx.2
    have hl : f (P.point i.castSucc) ≤ cellInfimum f P hf i := by
      apply (cell_bounds f P hf i).1.2
      rintro _ ⟨x, hx, rfl⟩
      exact hm (hv _) (cell_subset_interval P i hx) hx.1
    linarith
  calc
    upperSum f P hf - lowerSum f P hf =
        ∑ i : Fin P.n, (cellSupremum f P hf i - cellInfimum f P hf i) *
          cellLength P i := by
      simp only [upperSum, lowerSum, D.upperSumValue, D.lowerSumValue,
        sub_mul, Finset.sum_sub_distrib]
    _ ≤ ∑ i : Fin P.n,
        (f (P.point i.succ) - f (P.point i.castSucc)) * cellLength P i :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hc i) (cell_positive P i).le
    _ ≤ ∑ i : Fin P.n,
        (f (P.point i.succ) - f (P.point i.castSucc)) * mesh P := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (cellLength_le_mesh P i)
        (sub_nonneg.mpr (hm (hv _) (hv _) (P.strictMono.monotone (Fin.castSucc_le_succ i))))
    _ = mesh P * (f b - f a) := by
      rw [← Finset.sum_mul, sum_cell_differences (fun j => f (P.point j)), P.last, P.first, mul_comm]

theorem real_integrable_of_monotoneOn (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedOnInterval f a b) (hm : MonotoneOn f (Set.Icc a b)) :
    RealIntegrable f a b := by
  rcases lt_or_eq_of_le hab with hab | rfl
  · apply (darboux_criterion f hab hf).mpr
    intro ε hε
    let C := f b - f a
    have hC : 0 ≤ C := sub_nonneg.mpr (hm (Set.left_mem_Icc.mpr hab.le)
      (Set.right_mem_Icc.mpr hab.le) hab.le)
    obtain ⟨P, _, hP⟩ := arbitrarily_fine hab (ε / (C+1)) (by positivity)
    refine ⟨P, (monotone_darboux_gap_le f hf hm P).trans_lt ?_⟩
    calc
      mesh P * C ≤ mesh P * (C+1) :=
        mul_le_mul_of_nonneg_left (by linarith) (mesh_nonneg P)
      _ < ε / (C+1) * (C+1) := mul_lt_mul_of_pos_right hP (by positivity)
      _ = ε := by field_simp
  · exact realIntegrable_degenerate f a

theorem real_monotone_integrable :
    Specs.SingleVariableAnalysis.Ch08.Monotone.realMonotoneIntegrable := by
  intro f a b hab hf hm
  rcases hm with hm | hm
  · exact real_integrable_of_monotoneOn f hab hf hm
  · have hn : MonotoneOn (fun x => -f x) (Set.Icc a b) :=
      fun _ hx _ hy hxy => neg_le_neg (hm hx hy hxy)
    have hb : BoundedOnInterval (fun x => -f x) a b := by
      simpa only [neg_one_mul] using BoundedOnInterval.mul hf (-1)
    obtain ⟨h, _⟩ := real_mul_value (real_integrable_of_monotoneOn _ hab hb hn) (-1)
    simpa only [neg_one_mul, neg_neg] using h

/-- Restoring arbitrary finite endpoint values preserves a bound. -/
theorem norm_bound_of_eqOn_open {E : Type*} [NormedAddCommGroup E]
    (f g : ℝ → E) {a b : ℝ}
    (hb : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, ‖g x‖ ≤ M)
    (he : Set.EqOn f g (Set.Ioo a b)) :
    ∃ M : ℝ, ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M := by
  obtain ⟨M, hM⟩ := hb
  refine ⟨max M (max ‖f a‖ ‖f b‖), fun x hx => ?_⟩
  rcases eq_or_lt_of_le hx.1 with h | h
  · subst x
    exact (le_max_left _ _).trans (le_max_right _ _)
  · rcases eq_or_lt_of_le hx.2 with h' | h'
    · subst x
      exact (le_max_right _ _).trans (le_max_right _ _)
    · rw [he ⟨h, h'⟩]
      exact (hM x hx).trans (le_max_left _ _)

theorem finite_disagreement_of_eqOn_open {E : Type*} (f g : ℝ → E) {a b : ℝ}
    (he : Set.EqOn f g (Set.Ioo a b)) :
    {x | x ∈ Set.Icc a b ∧ g x ≠ f x}.Finite := by
  apply ((Set.finite_singleton b).insert a).subset
  intro x hx
  by_cases ha : x = a
  · exact Or.inl ha
  · apply Or.inr
    by_contra hb
    exact hx.2 (he ⟨lt_of_le_of_ne hx.1.1 (Ne.symm ha),
      lt_of_le_of_ne hx.1.2 hb⟩).symm

/-- A real continuous closed-cell extension need only agree on its interior. -/
theorem real_integrable_of_continuous_extension (f g : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn g (Set.Icc a b))
    (he : Set.EqOn f g (Set.Ioo a b)) : RealIntegrable f a b := by
  have hg : RealIntegrable g a b := real_continuous_integrable g hab
    (fun x hx => (relativeContinuousAt_within_iff _ _ _).mpr (hc x hx))
  have hb : BoundedOnInterval f a b := by
    obtain ⟨M, hM⟩ := hg.bounded.abs_bound
    obtain ⟨N, hN⟩ := norm_bound_of_eqOn_open f g
      ⟨M, by simpa only [Real.norm_eq_abs] using hM⟩ he
    exact boundedOnInterval_of_abs (by simpa only [Real.norm_eq_abs] using hN)
  exact (real_finite_changes g f hg.bounded hb
    (finite_disagreement_of_eqOn_open f g he) hg).choose

theorem complex_integrable_of_continuous_extension (f g : ℝ → ℂ) {a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn g (Set.Icc a b))
    (he : Set.EqOn f g (Set.Ioo a b)) : ComplexIntegrable f a b := by
  have hg : ComplexIntegrable g a b := complex_continuous_integrable g hab
    (fun x hx => (relativeContinuousAt_within_iff _ _ _).mpr (hc x hx))
  exact (complex_finite_changes g f hg.norm_bound
    (norm_bound_of_eqOn_open f g hg.norm_bound he)
    (finite_disagreement_of_eqOn_open f g he) hg).choose

/-- Integrable adjacent closed restrictions give an integrable whole; their
bounds provide the whole-interval bound required by the splitting theorem. -/
theorem RealIntegrable.join {f : ℝ → ℝ} {a c b : ℝ}
    (hl : RealIntegrable f a c) (hr : RealIntegrable f c b) :
    RealIntegrable f a b := by
  obtain ⟨M, hM⟩ := hl.bounded.abs_bound
  obtain ⟨N, hN⟩ := hr.bounded.abs_bound
  have hb : BoundedOnInterval f a b := by
    apply boundedOnInterval_of_abs (M := max M N)
    intro x hx
    by_cases hxc : x ≤ c
    · exact (hM x ⟨hx.1, hxc⟩).trans (le_max_left _ _)
    · exact (hN x ⟨(le_of_not_ge hxc), hx.2⟩).trans (le_max_right _ _)
  exact (real_split f hl.ordered hr.ordered hb).1.mpr ⟨hl, hr⟩

/-- Glue along all cells of a finite strict partition, with no extra bound. -/
theorem real_integrable_of_partition_cells (f : ℝ → ℝ) {a b : ℝ}
    (P : Partition a b)
    (hc : ∀ i : Fin P.n, RealIntegrable f (P.point i.castSucc) (P.point i.succ)) :
    RealIntegrable f a b := by
  have hprefix : ∀ j : ℕ, ∀ hj : j < P.n+1,
      RealIntegrable f a (P.point ⟨j, hj⟩) := by
    intro j
    induction j with
    | zero =>
      intro hj
      simpa only [show (⟨0, hj⟩ : Fin (P.n+1)) = 0 from rfl, P.first]
        using realIntegrable_degenerate f a
    | succ j ih =>
      intro hj
      exact (ih (by omega)).join (hc ⟨j, by omega⟩)
  simpa only [show (⟨P.n, Nat.lt_succ_self _⟩ : Fin (P.n+1)) = Fin.last P.n from rfl,
    P.last] using hprefix P.n (Nat.lt_succ_self _)

theorem complex_integrable_of_partition_cells (f : ℝ → ℂ) {a b : ℝ}
    (P : Partition a b)
    (hc : ∀ i : Fin P.n, ComplexIntegrable f (P.point i.castSucc) (P.point i.succ)) :
    ComplexIntegrable f a b :=
  ⟨real_integrable_of_partition_cells _ P (fun i => (hc i).1),
   real_integrable_of_partition_cells _ P (fun i => (hc i).2)⟩

theorem real_step_integrable :
    Specs.SingleVariableAnalysis.Ch08.Monotone.realStepIntegrable := by
  intro f a b P h
  apply real_integrable_of_partition_cells f P
  intro i
  obtain ⟨c, hc⟩ := h i
  exact real_integrable_of_continuous_extension f (fun _ => c)
    (P.strictMono (Fin.castSucc_lt_succ (i := i))).le continuousOn_const hc

theorem complex_step_integrable :
    Specs.SingleVariableAnalysis.Ch08.Monotone.complexStepIntegrable := by
  intro f a b P h
  apply complex_integrable_of_partition_cells f P
  intro i
  obtain ⟨c, hc⟩ := h i
  exact complex_integrable_of_continuous_extension f (fun _ => c)
    (P.strictMono (Fin.castSucc_lt_succ (i := i))).le continuousOn_const hc

theorem real_piecewise_continuous_integrable :
    Specs.SingleVariableAnalysis.Ch08.Monotone.realPiecewiseContinuousIntegrable := by
  intro f a b P h
  apply real_integrable_of_partition_cells f P
  intro i
  obtain ⟨hc, L, R, hl, hr⟩ := h i
  apply real_integrable_of_continuous_extension f
    (extendFrom (Set.Ioo (P.point i.castSucc) (P.point i.succ)) f)
    (P.strictMono (Fin.castSucc_lt_succ (i := i))).le
    (continuousOn_Icc_extendFrom_Ioo hc hl hr)
  exact fun x hx => (extendFrom_extends hc x hx).symm

theorem complex_piecewise_continuous_integrable :
    Specs.SingleVariableAnalysis.Ch08.Monotone.complexPiecewiseContinuousIntegrable := by
  intro f a b P h
  apply complex_integrable_of_partition_cells f P
  intro i
  obtain ⟨hc, L, R, hl, hr⟩ := h i
  apply complex_integrable_of_continuous_extension f
    (extendFrom (Set.Ioo (P.point i.castSucc) (P.point i.succ)) f)
    (P.strictMono (Fin.castSucc_lt_succ (i := i))).le
    (continuousOn_Icc_extendFrom_Ioo hc hl hr)
  exact fun x hx => (extendFrom_extends hc x hx).symm

end SingleVariableAnalysis.Riemann
