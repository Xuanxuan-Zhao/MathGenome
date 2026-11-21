import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.Uniform
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Alternating
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Series

/-! K03.12.series. Ordinary convergence is always ordered partial-sum
convergence, including the constant conditionally convergent example.
The diagonal example retains the source indices n ≥ 1, with u₀ = 0. -/

namespace SingleVariableAnalysis

open scoped BigOperators Topology

universe u

noncomputable def realFunctionPartialSum : {E : Type u} → (ℕ → E → ℝ) → ℕ → E → ℝ :=
  fun u N x => ∑ n ∈ Finset.range (N + 1), u n x

noncomputable def RealFunctionSeriesPointwiseHasSum : {E : Type u} → (ℕ → E → ℝ) → (E → ℝ) → Prop :=
  fun u f => RealPointwiseConverges (realFunctionPartialSum u) f

noncomputable def RealFunctionSeriesPointwiseConverges : {E : Type u} → (ℕ → E → ℝ) → Prop :=
  fun u => ∃ f, RealFunctionSeriesPointwiseHasSum u f

noncomputable def RealFunctionSeriesUniformHasSum : {E : Type u} → (ℕ → E → ℝ) → (E → ℝ) → Prop :=
  fun u f => RealUniformConverges (realFunctionPartialSum u) f

noncomputable def RealFunctionSeriesUniformConverges : {E : Type u} → (ℕ → E → ℝ) → Prop :=
  fun u => ∃ f, RealFunctionSeriesUniformHasSum u f

noncomputable def RealFunctionSeriesUniformAbsoluteConverges : {E : Type u} → (ℕ → E → ℝ) → Prop :=
  fun u => RealFunctionSeriesUniformConverges (fun n x => |u n x|)

noncomputable def RealFunctionSeriesNormallyConverges : {E : Type u} → (ℕ → E → ℝ) → Prop :=
  fun u => ∃ M : ℕ → ℝ, (∀ n, IsLUB (insert 0 (Set.range (fun x => |u n x|))) (M n)) ∧ RealSeriesConverges M

noncomputable def complexFunctionPartialSum : {E : Type u} → (ℕ → E → ℂ) → ℕ → E → ℂ :=
  fun u N x => ∑ n ∈ Finset.range (N + 1), u n x

noncomputable def ComplexFunctionSeriesPointwiseHasSum : {E : Type u} → (ℕ → E → ℂ) → (E → ℂ) → Prop :=
  fun u f => ComplexPointwiseConverges (complexFunctionPartialSum u) f

noncomputable def ComplexFunctionSeriesPointwiseConverges : {E : Type u} → (ℕ → E → ℂ) → Prop :=
  fun u => ∃ f, ComplexFunctionSeriesPointwiseHasSum u f

noncomputable def ComplexFunctionSeriesUniformHasSum : {E : Type u} → (ℕ → E → ℂ) → (E → ℂ) → Prop :=
  fun u f => ComplexUniformConverges (complexFunctionPartialSum u) f

noncomputable def ComplexFunctionSeriesUniformConverges : {E : Type u} → (ℕ → E → ℂ) → Prop :=
  fun u => ∃ f, ComplexFunctionSeriesUniformHasSum u f

noncomputable def ComplexFunctionSeriesUniformAbsoluteConverges : {E : Type u} → (ℕ → E → ℂ) → Prop :=
  fun u => RealFunctionSeriesUniformConverges (fun n x => ‖u n x‖)

noncomputable def ComplexFunctionSeriesNormallyConverges : {E : Type u} → (ℕ → E → ℂ) → Prop :=
  fun u => ∃ M : ℕ → ℝ, (∀ n, IsLUB (insert 0 (Set.range (fun x => ‖u n x‖))) (M n)) ∧ RealSeriesConverges M

/-- The series definition agrees pointwise with ordinary scalar series sums. -/
theorem real_function_series_pointwise_iff {E : Type u} (u : ℕ → E → ℝ) (f : E → ℝ) :
    RealFunctionSeriesPointwiseHasSum u f ↔
      ∀ x, RealSeriesHasSum (fun n => u n x) (f x) := Iff.rfl

theorem complex_function_series_pointwise_iff {E : Type u} (u : ℕ → E → ℂ) (f : E → ℂ) :
    ComplexFunctionSeriesPointwiseHasSum u f ↔
      ∀ x, ComplexSeriesHasSum (fun n => u n x) (f x) := Iff.rfl

theorem real_function_series_uniform_pointwise {E : Type u} (u : ℕ → E → ℝ) (f : E → ℝ)
    (h : RealFunctionSeriesUniformHasSum u f) : RealFunctionSeriesPointwiseHasSum u f :=
  realUniformConverges_pointwise _ _ h

theorem complex_function_series_uniform_pointwise {E : Type u} (u : ℕ → E → ℂ) (f : E → ℂ)
    (h : ComplexFunctionSeriesUniformHasSum u f) : ComplexFunctionSeriesPointwiseHasSum u f :=
  complexUniformConverges_pointwise _ _ h

noncomputable def constantAlternatingHarmonic {E : Type u} (n : ℕ) (_ : E) : ℝ :=
  (-1 : ℝ) ^ n / ((n : ℝ) + 1)

theorem constant_alternating_harmonic_separation (E : Type u) [Nonempty E] :
    RealFunctionSeriesUniformConverges (constantAlternatingHarmonic (E := E)) ∧
    (∀ x : E, ¬ RealSeriesConverges (fun n => |constantAlternatingHarmonic n x|)) ∧
    ¬ RealFunctionSeriesUniformAbsoluteConverges (constantAlternatingHarmonic (E := E)) := by
  obtain ⟨hconv, hdiv⟩ := alternating_harmonic_conditional
  have hpoint : ∀ x : E, ¬ RealSeriesConverges (fun n => |constantAlternatingHarmonic n x|) :=
    fun _ => hdiv
  refine ⟨?_, hpoint, ?_⟩
  · obtain ⟨S, hS⟩ := hconv
    refine ⟨fun _ => S, ?_⟩
    intro ε hε
    obtain ⟨N, hN⟩ := hS ε hε
    exact ⟨N, fun n hn _ => hN n hn⟩
  · rintro ⟨f, hf⟩
    let x : E := Classical.choice inferInstance
    exact hpoint x ⟨f x, real_function_series_uniform_pointwise _ _ hf x⟩

/-- The source diagonal series, including its zero term at index zero. -/
noncomputable def diagonalHarmonic (n : ℕ) (k : ℕ+) : ℝ :=
  if n = (k : ℕ) then 1 / (n : ℝ) else 0

theorem diagonal_harmonic_nonnegative (n : ℕ) (k : ℕ+) : 0 ≤ diagonalHarmonic n k := by
  unfold diagonalHarmonic
  split_ifs <;> positivity

theorem diagonal_harmonic_partialSum (N : ℕ) (k : ℕ+) :
    realFunctionPartialSum (fun n x => |diagonalHarmonic n x|) N k =
      if (k : ℕ) ≤ N then 1 / ((k : ℕ) : ℝ) else 0 := by
  have habs : ∀ n k, |diagonalHarmonic n k| = diagonalHarmonic n k :=
    fun n k => abs_of_nonneg (diagonal_harmonic_nonnegative n k)
  simp only [realFunctionPartialSum]
  simp only [habs]
  simp only [diagonalHarmonic, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_iff]

theorem diagonal_harmonic_error (N : ℕ) (k : ℕ+) :
    |realFunctionPartialSum (fun n x => |diagonalHarmonic n x|) N k -
      1 / ((k : ℕ) : ℝ)| =
      if (k : ℕ) ≤ N then 0 else 1 / ((k : ℕ) : ℝ) := by
  rw [diagonal_harmonic_partialSum]
  split_ifs <;> simp

/-- The uniform remainder is exactly the first omitted reciprocal, not just bounded by it. -/
theorem diagonal_harmonic_tail_supremum (N : ℕ) :
    IsLUB (Set.range (fun k : ℕ+ =>
      |realFunctionPartialSum (fun n x => |diagonalHarmonic n x|) N k -
        1 / ((k : ℕ) : ℝ)|)) (1 / ((N : ℝ) + 1)) := by
  constructor
  · rintro _ ⟨k, rfl⟩
    dsimp only
    rw [diagonal_harmonic_error]
    split_ifs with hk
    · positivity
    · apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast (show N + 1 ≤ (k : ℕ) by omega)
  · intro B hB
    have h := hB (Set.mem_range_self (⟨N + 1, Nat.succ_pos _⟩ : ℕ+))
    have hh := (diagonal_harmonic_error N (⟨N + 1, Nat.succ_pos _⟩ : ℕ+)).symm.trans_le h
    simpa using hh

theorem diagonal_harmonic_tail_limit :
    RealSequenceConverges (fun N : ℕ => 1 / ((N : ℝ) + 1)) 0 := by
  have h := (real_shift_iff (fun N : ℕ => 1 / (N : ℝ)) 0 1).mpr harmonic_term_limit
  simpa only [Nat.cast_add, Nat.cast_one] using h

theorem diagonal_harmonic_uniform_absolute :
    RealFunctionSeriesUniformAbsoluteConverges diagonalHarmonic := by
  refine ⟨fun k : ℕ+ => 1 / ((k : ℕ) : ℝ), ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := diagonal_harmonic_tail_limit ε hε
  refine ⟨N, fun n hn k => ?_⟩
  have h := hN n hn
  dsimp only at h ⊢
  rw [sub_zero, abs_of_nonneg (by positivity)] at h
  exact ((diagonal_harmonic_tail_supremum n).1 (Set.mem_range_self k)).trans_lt h

theorem diagonal_harmonic_term_supremum (n : ℕ) :
    IsLUB (insert 0 (Set.range (fun k : ℕ+ => |diagonalHarmonic n k|)))
      (1 / (n : ℝ)) := by
  constructor
  · intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | ⟨k, rfl⟩
    · positivity
    · dsimp only
      rw [abs_of_nonneg (diagonal_harmonic_nonnegative _ _)]
      unfold diagonalHarmonic
      split_ifs <;> simp
  · intro B hB
    by_cases hn : 0 < n
    · have h := hB (Set.mem_insert_of_mem 0
        (Set.mem_range_self (⟨n, hn⟩ : ℕ+)))
      simpa [diagonalHarmonic] using h
    · have h := hB (Set.mem_insert 0 _)
      have : n = 0 := by omega
      simpa [this] using h

theorem diagonal_harmonic_suprema_diverge :
    ¬ RealSeriesConverges (fun n : ℕ => 1 / (n : ℝ)) := harmonic_series_diverges

theorem diagonal_harmonic_not_normal :
    ¬ RealFunctionSeriesNormallyConverges diagonalHarmonic := by
  rintro ⟨M, hM, hconv⟩
  have he : M = fun n : ℕ => 1 / (n : ℝ) := by
    funext n
    exact (hM n).unique (diagonal_harmonic_term_supremum n)
  rw [he] at hconv
  exact diagonal_harmonic_suprema_diverge hconv

/-- Uniform convergence of nonnegative numerical majorant partial sums controls
finite tails of a function series. Completeness is used only to obtain its
pointwise limits. This applies to arbitrary domains, including the empty one. -/
private theorem uniform_series_of_majorant {E V : Type*}
    [NormedAddCommGroup V] [CompleteSpace V]
    (u : ℕ → E → V) (M : ℕ → E → ℝ)
    (hM : ∀ n x, ‖u n x‖ ≤ M n x) (g : E → ℝ)
    (hg : RealUniformConverges (realFunctionPartialSum M) g) :
    ∃ f : E → V, TendstoUniformly
      (fun N x => ∑ n ∈ Finset.range (N + 1), u n x) f Filter.atTop := by
  let F := fun N x => ∑ n ∈ Finset.range (N + 1), u n x
  let G := realFunctionPartialSum M
  have hd : ∀ m n, m ≤ n → ∀ x, ‖F n x - F m x‖ ≤ |G n x - G m x| := by
    intro m n hmn x
    dsimp only [F, G, realFunctionPartialSum]
    rw [← Finset.sum_Ico_eq_sub _ (Nat.succ_le_succ hmn),
      ← Finset.sum_Ico_eq_sub _ (Nat.succ_le_succ hmn)]
    exact (norm_sum_le_of_le _ (fun i _ => hM i x)).trans (le_abs_self _)
  have hd' : ∀ m n x, ‖F m x - F n x‖ ≤ |G m x - G n x| := by
    intro m n x
    rcases le_total m n with hmn | hnm
    · rw [norm_sub_rev, abs_sub_comm]
      exact hd m n hmn x
    · exact hd n m hnm x
  have hcG := ((realUniformConverges_iff _ _).mp hg).tendstoUniformlyOn
      (s := Set.univ) |>.uniformCauchySeqOn
  have hcF : UniformCauchySeqOn F Filter.atTop Set.univ := by
    rw [Metric.uniformCauchySeqOn_iff] at hcG ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hcG ε hε
    refine ⟨N, fun m hm n hn x hx => ?_⟩
    rw [dist_eq_norm]
    exact (hd' m n x).trans_lt (by simpa only [Real.dist_eq] using hN m hm n hn x hx)
  have hp : ∀ x, ∃ v : V, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds v) := by
    intro x
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hcF ε hε
    exact ⟨N, fun m hm n hn => hN m hm n hn x (Set.mem_univ x)⟩
  choose f hf using hp
  exact ⟨f, tendstoUniformlyOn_univ.mp
    (hcF.tendstoUniformlyOn_of_tendsto (fun x _ => hf x))⟩

theorem real_function_series_absolute_uniform {E : Type u} (u : ℕ → E → ℝ)
    (h : RealFunctionSeriesUniformAbsoluteConverges u) :
    RealFunctionSeriesUniformConverges u := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨f, hf⟩ := uniform_series_of_majorant u (fun n x => |u n x|)
    (fun n x => by rw [Real.norm_eq_abs]) g hg
  exact ⟨f, (realUniformConverges_iff _ _).mpr hf⟩

theorem complex_function_series_absolute_uniform {E : Type u} (u : ℕ → E → ℂ)
    (h : ComplexFunctionSeriesUniformAbsoluteConverges u) :
    ComplexFunctionSeriesUniformConverges u := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨f, hf⟩ := uniform_series_of_majorant u (fun n x => ‖u n x‖)
    (fun _ _ => le_rfl) g hg
  exact ⟨f, (complexUniformConverges_iff _ _).mpr hf⟩

/-- Summability of the exact suprema implies uniform absolute convergence. -/
theorem real_function_series_normal_absolute {E : Type u} (u : ℕ → E → ℝ)
    (h : RealFunctionSeriesNormallyConverges u) :
    RealFunctionSeriesUniformAbsoluteConverges u := by
  obtain ⟨M, hM, S, hS⟩ := h
  have hg : RealUniformConverges (realFunctionPartialSum (fun n (_ : E) => M n))
      (fun _ => S) := by
    intro ε hε
    obtain ⟨N, hN⟩ := hS ε hε
    exact ⟨N, fun n hn _ => hN n hn⟩
  obtain ⟨f, hf⟩ := uniform_series_of_majorant (fun n x => |u n x|)
    (fun n (_ : E) => M n) (fun n x => by
      simpa only [Real.norm_eq_abs, abs_abs] using
        (hM n).1 (Set.mem_insert_of_mem 0 (Set.mem_range_self x))) (fun _ => S) hg
  exact ⟨f, (realUniformConverges_iff _ _).mpr hf⟩

theorem complex_function_series_normal_absolute {E : Type u} (u : ℕ → E → ℂ)
    (h : ComplexFunctionSeriesNormallyConverges u) :
    ComplexFunctionSeriesUniformAbsoluteConverges u := by
  obtain ⟨M, hM, S, hS⟩ := h
  have hg : RealUniformConverges (realFunctionPartialSum (fun n (_ : E) => M n))
      (fun _ => S) := by
    intro ε hε
    obtain ⟨N, hN⟩ := hS ε hε
    exact ⟨N, fun n hn _ => hN n hn⟩
  obtain ⟨f, hf⟩ := uniform_series_of_majorant (fun n x => ‖u n x‖)
    (fun n (_ : E) => M n) (fun n x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
        (hM n).1 (Set.mem_insert_of_mem 0 (Set.mem_range_self x))) (fun _ => S) hg
  exact ⟨f, (realUniformConverges_iff _ _).mpr hf⟩

end SingleVariableAnalysis
