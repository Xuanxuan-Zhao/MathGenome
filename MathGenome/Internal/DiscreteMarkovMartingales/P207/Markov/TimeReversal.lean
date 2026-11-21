import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.TimeReversal
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.Stationarity
import Mathlib.Algebra.BigOperators.Intervals

open MeasureTheory
open scoped ENNReal MeasureTheory
universe u v
namespace P207.Markov
noncomputable section

namespace TimeReversal
abbrev IsReversible : StationaritySpec.IsReversibleType.{u} := @P207.Markov.IsReversible
abbrev supportLaw : TimeReversalSpec.supportLawType.{u} := @P207.Markov.supportLaw
abbrev reverseKernel : TimeReversalSpec.reverseKernelType.{u} := @P207.Markov.reverseKernel
end TimeReversal

 theorem stationary_support_closed : TimeReversalSpec.support_closed.{u} := by
  intro S P π hπ i j hi hj
  have hle : π i * P i j ≤ π j :=
    (ENNReal.le_tsum i).trans_eq ((stationary_iff_masses P π).mp hπ j)
  rw [hj] at hle
  exact (mul_eq_zero.mp (le_antisymm hle bot_le)).resolve_left (ne_of_gt hi)

 theorem stationarySupport_isClosed : TimeReversalSpec.stationarySupport_isClosed.{u} := by
  intro S P π hπ i hi j hij
  by_contra hj
  have hz := stationary_support_closed P π hπ i j hi
    (le_antisymm (not_lt.mp hj) bot_le)
  exact (ne_of_gt hij) hz

 theorem supportLaw_apply {S : Type u} (π : ProbabilityLaw S)
    (i : StationarySupport π) : supportLaw π i = π i.val := rfl

 theorem supportLaw_map : TimeReversalSpec.supportLaw_map.{u} := by
  intro S π
  classical
  apply PMF.ext
  intro i
  rw [PMF.map_apply]
  by_cases hi : 0 < π i
  · rw [tsum_eq_single (⟨i, hi⟩ : StationarySupport π)]
    · simp [supportLaw_apply]
    · intro j hj
      have hji : i ≠ j.val := fun he => hj (Subtype.ext he.symm)
      simp [hji]
  · have hz : π i = 0 := le_antisymm (not_lt.mp hi) bot_le
    rw [hz]
    have hzero : ∀ j : StationarySupport π,
        (if i = j.val then supportLaw π j else 0) = 0 := by
      intro j
      have hji : i ≠ j.val := fun he => hi (he ▸ j.property)
      simp [hji]
    simp only [hzero, tsum_zero]

 theorem reverseKernel_apply {S : Type u} (P : StochasticMatrix S)
    (π : ProbabilityLaw S) (hπ : IsStationary P π) (i j : StationarySupport π) :
    reverseKernel P π hπ i j = π j.val * P j.val i.val / π i.val := rfl

 theorem reverseKernel_row_sum : TimeReversalSpec.reverseKernel_row_sum.{u} := by
  intro S P π hπ i
  exact (reverseKernel P π hπ i).tsum_coe

/-- Weighted flow identity, with both endpoints on the support. -/
theorem reverseKernel_flow {S : Type u} (P : StochasticMatrix S) (π : ProbabilityLaw S)
    (hπ : IsStationary P π) (i j : StationarySupport π) :
    π i.val * reverseKernel P π hπ i j = π j.val * P j.val i.val := by
  rw [reverseKernel_apply, ENNReal.mul_div_cancel (ne_of_gt i.property) (π.apply_ne_top _)]

 theorem reverseKernel_stationary : TimeReversalSpec.reverseKernel_stationary.{u} := by
  intro S P π hπ
  apply (stationary_iff_masses _ _).mpr
  intro j
  simp only [supportLaw_apply, reverseKernel_flow]
  rw [ENNReal.tsum_mul_left]
  have hs : ∑' i : StationarySupport π, P j.val i.val = 1 := by
    calc
      _ = ∑' i, P j.val i := tsum_subtype_eq_of_support_subset
        (s := {i | 0 < π i}) (f := fun i => P j.val i) (fun i hi => by
          by_contra hn
          exact hi (stationary_support_closed P π hπ j.val i j.property
            (le_antisymm (not_lt.mp hn) bot_le)))
      _ = 1 := (P j.val).tsum_coe
  rw [hs, mul_one]

/-- A telescoping identity that uses weighted flows, so needs no cancellation
and remains valid when some weights are zero. -/
theorem path_product_of_flow {A : Type*} (P Q : A → A → ℝ≥0∞)
    (w : A → ℝ≥0∞) (h : ∀ i j, w i * Q i j = w j * P j i)
    (n : ℕ) (x : ℕ → A) :
    w (x 0) * ∏ k ∈ Finset.range n, Q (x k) (x (k + 1)) =
    w (x n) * ∏ k ∈ Finset.range n, P (x (k + 1)) (x k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ih, Finset.prod_range_succ]
    calc
      _ = (w (x n) * Q (x n) (x (n + 1))) *
          ∏ k ∈ Finset.range n, P (x (k + 1)) (x k) := by ac_rfl
      _ = (w (x (n + 1)) * P (x (n + 1)) (x n)) *
          ∏ k ∈ Finset.range n, P (x (k + 1)) (x k) := by rw [h]
      _ = _ := by ac_rfl

/-- A finite word, extended after its final coordinate by its final state. -/
def extendWord {A : Type*} {n : ℕ} (x : Fin (n + 1) → A) (k : ℕ) : A :=
  x ⟨min k n, Nat.lt_succ_of_le (min_le_right _ _)⟩

 theorem extendWord_apply {A : Type*} {n : ℕ} (x : Fin (n + 1) → A)
    (k : ℕ) (hk : k ≤ n) : extendWord x k = x ⟨k, Nat.lt_succ_of_le hk⟩ := by
  simp [extendWord, Nat.min_eq_left hk]

 theorem word_preimage {A : Type*} {n : ℕ} (x : Fin (n + 1) → A) :
    (fun ω : ℕ → A => fun a : Fin (n + 1) => ω a.val) ⁻¹' {x} =
      prefixCylinder n (extendWord x) := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, prefixCylinder, Set.mem_ofPred_eq]
  constructor
  · intro h k hk
    rw [extendWord_apply x k hk]
    exact congrFun h ⟨k, Nat.lt_succ_of_le hk⟩
  · intro h
    funext a
    simpa only [extendWord_apply x a.val (Nat.le_of_lt_succ a.isLt)] using
      h a.val (Nat.le_of_lt_succ a.isLt)

 theorem reversed_word_preimage {A : Type*} {n : ℕ} (x : Fin (n + 1) → A) :
    (fun ω : ℕ → A => fun a : Fin (n + 1) => ω (n - a.val)) ⁻¹' {x} =
      prefixCylinder n (fun k => extendWord x (n - k)) := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, prefixCylinder, Set.mem_ofPred_eq]
  constructor
  · intro h k hk
    rw [extendWord_apply x (n - k) (Nat.sub_le _ _)]
    have := congrFun h ⟨n - k, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    simpa [Nat.sub_sub_self hk] using this
  · intro h
    funext a
    have ha := Nat.le_of_lt_succ a.isLt
    simpa [Nat.sub_sub_self ha, extendWord_apply x a.val ha] using
      h (n - a.val) (Nat.sub_le _ _)

 theorem reflected_path_product {A : Type*} (P : A → A → ℝ≥0∞)
    (n : ℕ) (x : ℕ → A) :
    (∏ k ∈ Finset.range n, P (x (n - k)) (x (n - (k + 1)))) =
      ∏ k ∈ Finset.range n, P (x (k + 1)) (x k) := by
  calc
    _ = ∏ k ∈ Finset.range n,
        (fun j => P (x (j + 1)) (x j)) (n - 1 - k) := by
      apply Finset.prod_congr rfl
      intro k hk
      have hk := Finset.mem_range.mp hk
      congr 2 <;> omega
    _ = _ := Finset.prod_range_reflect (fun j => P (x (j + 1)) (x j)) n

section FiniteLaws
variable {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
  [DiscreteMeasurableSpace S]

theorem forward_segment_atom (P : StochasticMatrix S) (π : ProbabilityLaw S)
    (n : ℕ) (x : Fin (n + 1) → S) :
    (pathLaw P π).map (fun ω (a : Fin (n + 1)) => ω a.val) {x} =
      π (extendWord x 0) * ∏ k ∈ Finset.range n,
        P (extendWord x k) (extendWord x (k + 1)) := by
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _),
    word_preimage, pathLaw_prefix]

theorem reverse_segment_atom (P : StochasticMatrix S) (π : ProbabilityLaw S)
    (n : ℕ) (x : Fin (n + 1) → S) :
    (pathLaw P π).map (fun ω (a : Fin (n + 1)) => ω (n - a.val)) {x} =
      π (extendWord x n) * ∏ k ∈ Finset.range n,
        P (extendWord x (k + 1)) (extendWord x k) := by
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _),
    reversed_word_preimage, pathLaw_prefix]
  simp only [Nat.sub_zero]
  rw [reflected_path_product (fun i j => P i j)]

/-- This comparison is on the original state space, including its null states. -/
theorem reversed_segment_law_zero (P : StochasticMatrix S) (π : ProbabilityLaw S)
    (hπ : IsStationary P π) (n : ℕ) :
    (pathLaw P π).map (fun ω (a : Fin (n + 1)) => ω (n - a.val)) =
    (pathLaw (reverseKernel P π hπ) (supportLaw π)).map
      (fun ω (a : Fin (n + 1)) => (ω a.val).val) := by
  classical
  haveI : Nonempty (StationarySupport π) :=
    ⟨(supportLaw π).support_nonempty.choose⟩
  apply Measure.ext_of_singleton
  intro x
  by_cases hx : ∀ a, 0 < π (x a)
  · let y : ℕ → StationarySupport π := fun k =>
      ⟨extendWord x k, hx ⟨min k n, Nat.lt_succ_of_le (min_le_right _ _)⟩⟩
    have he : (fun ω : ℕ → StationarySupport π =>
        fun a : Fin (n + 1) => (ω a.val).val) ⁻¹' {x} = prefixCylinder n y := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, prefixCylinder, Set.mem_ofPred_eq]
      constructor
      · intro h k hk
        apply Subtype.ext
        change (ω k).val = extendWord x k
        rw [extendWord_apply x k hk]
        exact congrFun h ⟨k, Nat.lt_succ_of_le hk⟩
      · intro h
        funext a
        have ha := Nat.le_of_lt_succ a.isLt
        have := congrArg Subtype.val (h a.val ha)
        simpa only [y, extendWord_apply x a.val ha] using this
    rw [reverse_segment_atom,
      Measure.map_apply (by fun_prop) (measurableSet_singleton _), he, pathLaw_prefix,
      supportLaw_apply]
    exact (path_product_of_flow (fun i j : StationarySupport π => P i.val j.val)
      (fun i j => reverseKernel P π hπ i j) (fun i => π i.val) (reverseKernel_flow P π hπ) n y).symm
  · obtain ⟨a, ha⟩ := not_forall.mp hx
    have hz : π (x a) = 0 := le_antisymm (not_lt.mp ha) bot_le
    have hm : pathLaw P π {ω | ω (n - a.val) = x a} = 0 := by
      have hh := DeterministicTransitions.marginal_mass
        (coordinate_isMarkovChain P π) (n - a.val) (x a)
      simpa only [coordinate, stationary_evolve P π hπ, hz] using hh
    have he : (fun ω : ℕ → StationarySupport π =>
        fun b : Fin (n + 1) => (ω b.val).val) ⁻¹' {x} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      have hh := congrFun (Set.mem_singleton_iff.mp hω) a
      exact ha (hh ▸ (ω a.val).property)
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _),
      Measure.map_apply (by fun_prop) (measurableSet_singleton _), he, measure_empty]
    apply measure_mono_null _ hm
    intro ω hω
    exact congrFun (Set.mem_singleton_iff.mp hω) a

end FiniteLaws

theorem reversed_segment_law : TimeReversalSpec.reversed_segment_law.{u} := by
  intro S _ _ _ P π hπ n r
  haveI : Nonempty S := ⟨π.support_nonempty.choose⟩
  have hs := stationary_future_law P π coordinate coordinateFiltration (pathLaw P π)
    (coordinate_isMarkovChain P π) hπ r
  have he := congrArg (fun μ : Measure (ℕ → S) =>
    μ.map (fun ω (a : Fin (n + 1)) => ω (n - a.val))) hs
  rw [Measure.map_map (by fun_prop)
    (show Measurable (fun ω n => coordinate (r + n) ω) from
      measurable_pi_iff.mpr (fun n => measurable_pi_apply (r + n)))] at he
  exact he.trans (reversed_segment_law_zero P π hπ n)

theorem chain_reversed_segment_law : TimeReversalSpec.chain_reversed_segment_law.{u,v} := by
  intro S _ _ _ _ Ω m P π X ℱ μ _ h hπ n r
  have he := congrArg (fun ρ : Measure (ℕ → S) =>
    ρ.map (fun ω (a : Fin (n + 1)) => ω (r + (n - a.val))))
    (chain_pathLaw P π X ℱ μ h)
  rw [Measure.map_map (by fun_prop)
    (measurable_pi_iff.mpr (fun k => h.1.measurable))] at he
  exact he.trans (reversed_segment_law P π hπ n r)

theorem reversible_iff_detailedBalance : TimeReversalSpec.reversible_iff_detailedBalance.{u} := by
  intro S _ _ _ P π
  haveI : Nonempty S := ⟨π.support_nonempty.choose⟩
  constructor
  · intro h i j
    let x : Fin 2 → S := fun a => if a.val = 0 then i else j
    have he := congrArg (fun μ : Measure (Fin 2 → S) => μ {x}) (h.2 1)
    rw [forward_segment_atom, reverse_segment_atom] at he
    simpa [x, extendWord, Finset.prod_range_succ] using he
  · intro h
    refine ⟨detailedBalance_stationary P π h, ?_⟩
    intro n
    apply Measure.ext_of_singleton
    intro x
    rw [forward_segment_atom, reverse_segment_atom]
    exact path_product_of_flow (fun i j => P i j) (fun i j => P i j) π h n (extendWord x)

end
end P207.Markov
