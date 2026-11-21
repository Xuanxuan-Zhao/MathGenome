import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.BoundaryHarmonic
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Walk.ReversibleDirichletForm
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.FinitePositiveRecurrence
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Foundation.Stopping
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.HittingProbability
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal MeasureTheory Classical

universe u
namespace P207.Markov
noncomputable section

namespace BoundaryHarmonic
abbrev boundaryExtension : BoundaryHarmonicSpec.boundaryExtensionType.{u} :=
  @P207.Markov.boundaryExtension
abbrev boundaryPayoff : BoundaryHarmonicSpec.boundaryPayoffType.{u} := @P207.Markov.boundaryPayoff
abbrev boundaryHarmonic : BoundaryHarmonicSpec.boundaryHarmonicType.{u} :=
  @P207.Markov.boundaryHarmonic
abbrev IsBoundaryHarmonic : BoundaryHarmonicSpec.IsBoundaryHarmonicType.{u} :=
  @P207.Markov.IsBoundaryHarmonic
end BoundaryHarmonic

theorem boundaryPayoff_at_hit : BoundaryHarmonicSpec.boundaryPayoff_at_hit.{u} := by
  intro S B g c ω n hn
  have he : hittingAfter coordinate B 0 ω = (n : WithTop ℕ) := hn
  have hb : ω n ∈ B := by
    have h := hittingAfter_mem_set_of_ne_top (u := coordinate) (s := B) (n := 0)
      (ω := ω) (show hittingAfter coordinate B 0 ω ≠ ⊤ by rw [he]; simp)
    rw [he] at h
    exact h
  refine ⟨hb, ?_⟩
  change P207.fullStoppedValue _ _ _ ω = _
  simp only [P207.fullStoppedValue, hn]
  change P207.Markov.boundaryExtension B g (ω n) = _
  simp [P207.Markov.boundaryExtension, hb]

theorem hittingTime_univ_zero : BoundaryHarmonicSpec.hittingTime_univ_zero.{u} := by
  intro S ω
  simp [hittingTime, hittingAfter_univ]

/-- Removing a nonboundary initial coordinate shifts first entrance by one. -/
theorem hittingTime_shift {S : Type u} (B : Set S) (ω : ℕ → S) (h₀ : ω 0 ∉ B) :
    hittingTime B ω = hittingTime B (fun k => ω (1 + k)) + 1 := by
  have hs (n : ℕ) : hittingTime B ω ≤ (n + 1 : ℕ) ↔
      hittingTime B (fun k => ω (1 + k)) ≤ n := by
    simp only [hittingTime_le_iff]
    constructor
    · rintro ⟨k, hk, hkB⟩
      cases k with
      | zero => exact (h₀ hkB).elim
      | succ k => exact ⟨k, by omega, by simpa [Nat.add_comm] using hkB⟩
    · rintro ⟨k, hk, hkB⟩
      exact ⟨1 + k, by omega, hkB⟩
  apply WithTop.eq_of_forall_le_coe_iff
  intro n
  cases n with
  | zero =>
    have hn : ¬ hittingTime B ω ≤ (0 : ℕ) := by
      simpa only [hittingTime_le_iff, Nat.le_zero, exists_eq_left] using h₀
    cases ht : hittingTime B (fun k => ω (1 + k)) <;> simp_all
  | succ n =>
    change hittingTime B ω ≤ (n : WithTop ℕ) + 1 ↔
      hittingTime B (fun k => ω (1 + k)) + 1 ≤ (n : WithTop ℕ) + 1
    rw [WithTop.add_le_add_iff_right (show (1 : WithTop ℕ) ≠ ⊤ by simp)]
    exact hs n

/-- The payoff is unchanged by this shift, including on the infinite layer. -/
theorem boundaryPayoff_shift {S : Type u} (B : Set S) (g : B → ℝ) (c : ℝ)
    (ω : ℕ → S) (h₀ : ω 0 ∉ B) :
    P207.Markov.boundaryPayoff B g c ω =
      P207.Markov.boundaryPayoff B g c (fun k => ω (1 + k)) := by
  have hs := hittingTime_shift B ω h₀
  cases ht : hittingTime B (fun k => ω (1 + k)) with
  | top => simp [P207.Markov.boundaryPayoff, P207.fullStoppedValue, hs, ht]
  | coe n =>
    have hn : hittingTime B ω = ((n + 1 : ℕ) : WithTop ℕ) := by
      simpa [ht] using hs
    change P207.fullStoppedValue _ _ _ ω = P207.fullStoppedValue _ _ _ _
    simp only [P207.fullStoppedValue, hn, ht, WithTop.coe_ne_top, ite_false]
    change P207.Markov.boundaryExtension B g (ω (n + 1)) =
      P207.Markov.boundaryExtension B g (ω (1 + n))
    rw [Nat.add_comm]

section Measurability
variable {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- No finiteness assertion is needed for measurability of the payoff. -/
theorem measurable_boundaryPayoff (B : Set S) (g : B → ℝ) (c : ℝ) :
    Measurable (P207.Markov.boundaryPayoff B g c) := by
  have h := P207.measurable_fullStoppedValue (hittingTime_isStoppingTime B)
    (fun n ω => P207.Markov.boundaryExtension B g (ω n))
    (fun n => (measurable_of_countable (P207.Markov.boundaryExtension B g)).comp
      (P207.adapted_naturalFiltration coordinate (fun k => measurable_pi_apply k) n))
    (fun _ => c) measurable_const
  exact h.mono ((P207.stoppedSigma_le_terminal (hittingTime_isStoppingTime B)).trans
    (P207.terminalSigma_le coordinateFiltration)) le_rfl

end Measurability

section Boundedness
variable {S : Type u} [Fintype S]

theorem boundaryPayoff_bounded (B : Set S) (g : B → ℝ) (c : ℝ) :
    ∃ C : ℝ, ∀ ω, ‖P207.Markov.boundaryPayoff B g c ω‖ ≤ C := by
  refine ⟨‖c‖ + ∑ x : S, ‖P207.Markov.boundaryExtension B g x‖, fun ω => ?_⟩
  have hs : 0 ≤ ∑ x : S, ‖P207.Markov.boundaryExtension B g x‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  unfold P207.Markov.boundaryPayoff P207.fullStoppedValue
  split_ifs
  · exact le_add_of_nonneg_right hs
  · exact (Finset.single_le_sum (fun x (_ : x ∈ Finset.univ) => norm_nonneg
      (P207.Markov.boundaryExtension B g x)) (Finset.mem_univ _)).trans
      (le_add_of_nonneg_left (norm_nonneg c))

end Boundedness

section Finite
variable {S : Type u} [Fintype S] [Nonempty S] [MeasurableSpace S]
  [DiscreteMeasurableSpace S]

local instance boundary_statePathLaw_probability (P : StochasticMatrix S) (x : S) :
    IsProbabilityMeasure (statePathLaw P x) := pathLaw_probability P (PMF.pure x)

theorem hittingTime_finite_ae (P : StochasticMatrix S) (hi : Irreducible P)
    (B : Set S) (hB : B.Nonempty) (x : S) :
    ∀ᵐ ω ∂statePathLaw P x, hittingTime B ω < ⊤ := by
  obtain ⟨b, hb⟩ := hB
  have hm := finite_meanHittingTime_lt_top P hi x b
  have hd : Measurable (hittingDuration ({b} : Set S)) := by
    unfold hittingDuration
    apply Measurable.tsum
    intro n
    exact Measurable.ite (measurableSet_hittingTime_gt {b} n)
      measurable_const measurable_const
  have ha := ae_lt_top hd hm.ne
  filter_upwards [ha] with ω hω
  have ht : hittingTime {b} ω < ⊤ := by
    by_contra h
    have he : hittingTime {b} ω = ⊤ := top_le_iff.mp (le_of_not_gt h)
    rw [hittingDuration_at_top {b} ω he] at hω
    exact (lt_irrefl _) hω
  obtain ⟨n, hn⟩ := (hittingTime_finite_iff {b} ω).mp ht
  apply (hittingTime_finite_iff B ω).mpr
  exact ⟨n, (Set.mem_singleton_iff.mp hn) ▸ hb⟩

/-- First-step disintegration for any bounded measurable real path function. -/
theorem boundary_first_step_expectation (P : StochasticMatrix S) (i : S)
    (f : (ℕ → S) → ℝ) (hf : Measurable f)
    (hb : ∃ C : ℝ, ∀ ω, ‖f ω‖ ≤ C) :
    (∫ ω, f (fun k => ω (1 + k)) ∂statePathLaw P i) =
      ∑ j, realMatrix P i j * stateExpectation P j f := by
  have hc := coordinate_isMarkovChain P (PMF.pure i)
  have he := fixed_future_integral P (PMF.pure i) coordinate coordinateFiltration
    (statePathLaw P i) hc f hf hb 1 Set.univ MeasurableSet.univ
  simp only [Measure.restrict_univ] at he
  change (∫ ω, f (fun k => ω (1 + k)) ∂statePathLaw P i) =
    ∫ ω, stateExpectation P (ω 1) f ∂statePathLaw P i at he
  rw [he]
  obtain ⟨C, hC⟩ := hb
  have hF := measurable_stateExpectation P f
  have hint : Integrable (fun j => stateExpectation P j f)
      ((statePathLaw P i).map (fun ω => ω 1)) :=
    Integrable.of_bound hF.aestronglyMeasurable C
      (Eventually.of_forall (stateExpectation_bound P f C hC))
  rw [← integral_map (μ := statePathLaw P i) (φ := fun ω : ℕ → S => ω 1)
    (measurable_pi_apply 1).aemeasurable hF.aestronglyMeasurable,
    integral_fintype hint]
  apply Finset.sum_congr rfl
  intro j hj
  have hm := DeterministicTransitions.marginal_mass hc 1 j
  have hm' : statePathLaw P i {ω | ω 1 = j} = P i j := by
    simpa [statePathLaw, coordinate, evolve, power_one, PMF.pure_bind] using hm
  rw [measureReal_def, Measure.map_apply (measurable_pi_apply 1) (measurableSet_singleton j)]
  change (statePathLaw P i {ω | ω 1 = j}).toReal * _ = _
  rw [hm']
  rfl

/-- The expected entrance payoff agrees with the data at boundary states. -/
theorem boundaryHarmonic_boundary (P : StochasticMatrix S) (B : Set S)
    (g : B → ℝ) (x : B) : P207.Markov.boundaryHarmonic P B g x = g x := by
  change (∫ ω, P207.Markov.boundaryPayoff B g 0 ω ∂statePathLaw P x) = g x
  calc
    _ = ∫ _ : ℕ → S, g x ∂statePathLaw P x := by
      apply integral_congr_ae
      filter_upwards [coordinate_zero_ae P (x : S)] with ω hω
      have ht : hittingTime B ω = (0 : ℕ) := by
        apply le_antisymm _ bot_le
        exact (hittingTime_le_iff B ω 0).mpr ⟨0, le_rfl, hω ▸ x.property⟩
      obtain ⟨hb, he⟩ := boundaryPayoff_at_hit B g 0 ω 0 ht
      exact he.trans (congrArg g (Subtype.ext hω))
    _ = _ := by simp

/-- The first-step equation in the interior; no reversibility is needed here. -/
theorem boundaryHarmonic_harmonic (P : StochasticMatrix S) (B : Set S)
    (g : B → ℝ) (x : S) (hx : x ∉ B) :
    (∑ y, realMatrix P x y * P207.Markov.boundaryHarmonic P B g y) =
      P207.Markov.boundaryHarmonic P B g x := by
  change (∑ y, realMatrix P x y * stateExpectation P y (P207.Markov.boundaryPayoff B g 0)) = _
  rw [← boundary_first_step_expectation P x _ (measurable_boundaryPayoff B g 0)
    (boundaryPayoff_bounded B g 0)]
  apply integral_congr_ae
  filter_upwards [coordinate_zero_ae P x] with ω hω
  exact (boundaryPayoff_shift B g 0 ω (hω ▸ hx)).symm

/-- Altering the payoff on the null infinite layer leaves its expectation unchanged. -/
theorem boundary_representation (P : StochasticMatrix S) (hi : Irreducible P)
    (B : Set S) (hB : B.Nonempty) (g : B → ℝ) (c : ℝ) (x : S) :
    P207.Markov.boundaryHarmonic P B g x = stateExpectation P x (P207.Markov.boundaryPayoff B g c) := by
  apply integral_congr_ae
  filter_upwards [hittingTime_finite_ae P hi B hB x] with ω hω
  simp only [P207.Markov.boundaryPayoff, P207.fullStoppedValue, ne_of_lt hω, ite_false]

/-- Finite boundary data give a genuinely integrable entrance payoff. -/
theorem integrable_boundaryPayoff (P : StochasticMatrix S) (B : Set S)
    (g : B → ℝ) (c : ℝ) (x : S) :
    Integrable (P207.Markov.boundaryPayoff B g c) (statePathLaw P x) := by
  obtain ⟨C, hC⟩ := boundaryPayoff_bounded B g c
  exact Integrable.of_bound (measurable_boundaryPayoff B g c).aestronglyMeasurable C
    (Eventually.of_forall hC)

omit [Nonempty S] in
/-- Equal boundary values and interior harmonicity determine a function uniquely. -/
theorem boundary_harmonic_ext (P : StochasticMatrix S) (π : ProbabilityLaw S)
    (hπ : ∀ x, 0 < π x) (hi : Irreducible P) (hr : IsReversible P π)
    (B : Set S) (hB : B.Nonempty) (g : B → ℝ) (f h : S → ℝ)
    (hf : P207.Markov.IsBoundaryHarmonic P B g f)
    (hh : P207.Markov.IsBoundaryHarmonic P B g h) : f = h := by
  let w : WeightedSpace π hπ := fun x => f x - h x
  have hwB (x : S) (hx : x ∈ B) : w x = 0 := by
    change f x - h x = 0
    rw [hf.1 ⟨x, hx⟩, hh.1 ⟨x, hx⟩, sub_self]
  have hwh (x : S) (hx : x ∉ B) : (∑ y, realMatrix P x y * w y) = w x := by
    change (∑ y, realMatrix P x y * (f y - h y)) = f x - h x
    simp only [mul_sub, Finset.sum_sub_distrib, hf.2 x hx, hh.2 x hx]
  have hz : WeightedSpace.dirichletForm π hπ P w w = 0 := by
    change (∑ x, (π x).toReal * w x * (w x - ∑ y, realMatrix P x y * w y)) = 0
    apply Finset.sum_eq_zero
    intro x hx
    by_cases hxB : x ∈ B
    · rw [hwB x hxB]
      simp
    · rw [hwh x hxB, sub_self, mul_zero]
  have hb := (reversible_iff_detailedBalance P π).mp hr
  obtain ⟨b, hbB⟩ := hB
  funext x
  obtain ⟨n, hn⟩ := (hi x b).1
  have he := WeightedSpace.equal_of_power_positive π hπ P w
    (WeightedSpace.equal_on_edge_of_dirichlet_zero π hπ P hb w hz) n x b hn
  have hwz : w x = 0 := he.trans (hwB b hbB)
  exact sub_eq_zero.mp hwz

/-- The Dirichlet boundary equations have the asserted unique hitting-expectation solution. -/
theorem boundary_harmonic_unique : BoundaryHarmonicSpec.boundary_harmonic_unique.{u} := by
  intro S _ _ _ _ P π hπ hi hr B hB g
  have hh : P207.Markov.IsBoundaryHarmonic P B g (P207.Markov.boundaryHarmonic P B g) :=
    ⟨boundaryHarmonic_boundary P B g, boundaryHarmonic_harmonic P B g⟩
  exact ⟨hh, fun f hf => boundary_harmonic_ext P π hπ hi hr B hB g f _ hf hh⟩

end Finite
end
end P207.Markov
