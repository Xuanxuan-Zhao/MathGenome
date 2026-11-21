import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.WeakMaximal
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Foundation.TwoTimeAndExamples
import Mathlib.Probability.Martingale.OptionalStopping

open MeasureTheory
open scoped MeasureTheory

universe u
namespace P207
variable {Ω : Type u} [m : MeasurableSpace Ω]

theorem constant_extension (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (n : ℕ)
    (h : IsSubmartingaleUpTo X ℱ μ n) :
    IsSubmartingale (fun k => X (min k n)) ℱ μ := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    exact (h.1 _ (min_le_right _ _)).mono (ℱ.mono (min_le_left _ _)) le_rfl
  · intro k
    exact h.2.1 _ (min_le_right _ _)
  · intro k
    by_cases hk : k < n
    · simpa only [min_eq_left hk.le, min_eq_left (Nat.succ_le_of_lt hk)] using h.2.2 k hk
    · have hnk : n ≤ k := Nat.le_of_not_gt hk
      simp only [min_eq_right hnk, min_eq_right (hnk.trans (Nat.le_succ k))]
      rw [condExp_of_stronglyMeasurable (ℱ.le k)
        ((h.1 n le_rfl).stronglyMeasurable.mono (ℱ.mono hnk)) (h.2.1 n le_rfl)]

/-- The stopping argument works for signed submartingales: outside the crossing
set, the bounded hitting time equals the horizon, so the complementary integrals
cancel as real numbers. -/
private theorem localized_maximal (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (h : Submartingale X ℱ μ) (n : ℕ) (ε : ℝ) :
    ε * (μ {ω | ε ≤ finiteMax X n ω}).toReal ≤
      ∫ ω in {ω | ε ≤ finiteMax X n ω}, X n ω ∂μ := by
  let A := {ω | ε ≤ finiteMax X n ω}
  let τ : Ω → WithTop ℕ := fun ω =>
    (hittingBtwn X {y : ℝ | ε ≤ y} 0 n ω : ℕ)
  have hm : MeasurableSet A := measurableSet_le measurable_const
    (Finset.measurable_range_sup'' fun k _ => (h.stronglyMeasurable k).measurable.mono (ℱ.le k) le_rfl)
  have ht : IsStoppingTime ℱ τ :=
    h.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hb : ∀ ω, τ ω ≤ n := by
    intro ω
    change ((hittingBtwn X {y : ℝ | ε ≤ y} 0 n ω : ℕ) : WithTop ℕ) ≤ (n : WithTop ℕ)
    exact_mod_cast (hittingBtwn_le (u := X) (s := {y : ℝ | ε ≤ y}) (n := 0) (m := n) ω)
  have hi : Integrable (stoppedValue X τ) μ := h.integrable_stoppedValue ht hb
  have hlow : ε * (μ A).toReal ≤ ∫ ω in A, stoppedValue X τ ω ∂μ := by
    apply setIntegral_ge_of_const_le_real hm (measure_ne_top _ _) _ hi.integrableOn
    intro ω hω
    apply stoppedValue_hittingBtwn_mem
    change ε ≤ (Finset.range (n + 1)).sup' _ (fun k => X k ω) at hω
    obtain ⟨k, hk, hx⟩ := (Finset.le_sup'_iff _).mp hω
    exact ⟨k, ⟨Nat.zero_le _, Nat.le_of_lt_succ (Finset.mem_range.mp hk)⟩, hx⟩
  have hcompl : ∫ ω in Aᶜ, stoppedValue X τ ω ∂μ = ∫ ω in Aᶜ, X n ω ∂μ := by
    apply setIntegral_congr_fun hm.compl
    intro ω hω
    have hnot : ¬ ε ≤ finiteMax X n ω := hω
    have heq : hittingBtwn X {y : ℝ | ε ≤ y} 0 n ω = n := by
      simp only [hittingBtwn, Set.mem_ofPred_eq, ite_eq_right_iff, forall_exists_index, and_imp]
      intro k hk hx
      exact False.elim (hnot ((Finset.le_sup'_iff _).mpr
        ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk.2), hx⟩))
    simp [τ, stoppedValue, heq]
    rfl
  have hstop : (∫ ω, stoppedValue X τ ω ∂μ) ≤ ∫ ω, X n ω ∂μ := by
    have hs := h.expected_stoppedValue_mono ht (isStoppingTime_const ℱ n) hb
      (fun _ => le_rfl)
    simpa only [stoppedValue_const] using hs
  have hlocal : (∫ ω in A, stoppedValue X τ ω ∂μ) ≤ ∫ ω in A, X n ω ∂μ := by
    rw [← integral_add_compl hm hi, ← integral_add_compl hm (h.integrable n), hcompl] at hstop
    exact (add_le_add_iff_right _).mp hstop
  exact hlow.trans hlocal

/-- The complete finite-horizon signed estimate from paper.tex §5.1. -/
theorem weak_maximal (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (n : ℕ)
    (h : IsSubmartingaleUpTo X ℱ μ n) (ε : ℝ) (_hε : 0 < ε) :
    ε * (μ {ω | ε ≤ finiteMax X n ω}).toReal ≤
      (∫ ω in {ω | ε ≤ finiteMax X n ω}, X n ω ∂μ) ∧
    (∫ ω in {ω | ε ≤ finiteMax X n ω}, X n ω ∂μ) ≤
      ∫ ω, max (X n ω) 0 ∂μ := by
  classical
  have hmax : finiteMax (fun k => X (min k n)) n = finiteMax X n := by
    funext ω
    unfold finiteMax
    apply Finset.sup'_congr _ rfl
    intro k hk
    change X (min k n) ω = X k ω
    rw [min_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
  constructor
  · have hext := (submartingale_iff_library μ ℱ _).mp (constant_extension μ ℱ X n h)
    simpa only [hmax, min_self] using localized_maximal μ ℱ _ hext n ε
  · have hm : MeasurableSet {ω | ε ≤ finiteMax X n ω} :=
      measurableSet_le measurable_const (Finset.measurable_range_sup'' fun k hk =>
        (h.1 k hk).mono (ℱ.le k) le_rfl)
    rw [← integral_indicator hm]
    apply integral_mono ((h.2.1 n le_rfl).indicator hm) (h.2.1 n le_rfl).pos_part
    intro ω
    by_cases hω : ω ∈ {ω | ε ≤ finiteMax X n ω}
    · simp only [Set.indicator_of_mem hω]
      exact le_max_left _ _
    · simp only [Set.indicator_of_notMem hω]
      exact le_max_right _ _

/-- In the nonnegative case the positive part at the terminal time is `X n`. -/
theorem weak_maximal_nonnegative (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (n : ℕ)
    (h : IsSubmartingaleUpTo X ℱ μ n) (hnonneg : ∀ k, k ≤ n → 0 ≤ᵐ[μ] X k)
    (ε : ℝ) (hε : 0 < ε) :
    ε * (μ {ω | ε ≤ finiteMax X n ω}).toReal ≤
      (∫ ω in {ω | ε ≤ finiteMax X n ω}, X n ω ∂μ) ∧
    (∫ ω in {ω | ε ≤ finiteMax X n ω}, X n ω ∂μ) ≤ ∫ ω, X n ω ∂μ := by
  have heq : (∫ ω, max (X n ω) 0 ∂μ) = ∫ ω, X n ω ∂μ :=
    integral_congr_ae ((hnonneg n le_rfl).mono fun _ hω => max_eq_left hω)
  simpa only [heq] using weak_maximal μ ℱ X n h ε hε

end P207
