import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.Stationarity
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.CanonicalPathLaw
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.DeterministicTransitions

open MeasureTheory
open scoped ENNReal MeasureTheory
universe u v
namespace P207.Markov
noncomputable section

namespace Stationarity
abbrev IsStationary : StationaritySpec.IsStationaryType.{u} := @P207.Markov.IsStationary
abbrev DetailedBalance : StationaritySpec.DetailedBalanceType.{u} := @P207.Markov.DetailedBalance
abbrev ShiftInvariant : StationaritySpec.ShiftInvariantType.{u,v} := @P207.Markov.ShiftInvariant
abbrev BlockShiftInvariant : StationaritySpec.BlockShiftInvariantType.{u,v} :=
  @P207.Markov.BlockShiftInvariant
abbrev IsReversible : StationaritySpec.IsReversibleType.{u} := @P207.Markov.IsReversible
end Stationarity

theorem stationary_iff_masses : StationaritySpec.stationary_iff_masses.{u} := by
  intro S P π
  constructor
  · intro h j
    simpa only [PMF.bind_apply] using congrArg (fun ν : PMF S => ν j) h
  · intro h
    exact PMF.ext fun j => (PMF.bind_apply π P j).trans (h j)

theorem stationary_evolve : StationaritySpec.stationary_evolve.{u} := by
  intro S P π h n
  induction n with
  | zero => exact evolve_zero π P
  | succ n ih =>
    rw [evolve_add, ih]
    simpa only [IsStationary, evolve, power_one] using h

theorem detailedBalance_stationary : StationaritySpec.detailedBalance_stationary.{u} := by
  intro S P π h
  apply (stationary_iff_masses P π).mpr
  intro j
  calc
    ∑' i, π i * P i j = ∑' i, π j * P j i := tsum_congr fun i => h i j
    _ = π j * ∑' i, P j i := ENNReal.tsum_mul_left
    _ = π j := by rw [(P j).tsum_coe, mul_one]

theorem stationary_positive : StationaritySpec.stationary_positive.{u} := by
  intro S _ P π hirr hπ j
  obtain ⟨i, hi⟩ : ∃ i, 0 < π i := by
    by_contra hn
    have hz : ∀ i, π i = 0 := fun i => le_antisymm
      (not_lt.mp (fun hh => hn ⟨i, hh⟩)) bot_le
    have := π.tsum_coe
    simp only [hz, tsum_zero] at this
    exact zero_ne_one this
  obtain ⟨n, hn⟩ := (hirr i j).1
  have he := congrArg (fun ν : PMF S => ν j) (stationary_evolve P π hπ n)
  rw [evolve_apply] at he
  exact lt_of_lt_of_le (ENNReal.mul_pos_iff.mpr ⟨hi, hn⟩)
    ((ENNReal.le_tsum i).trans_eq he)

section Chain
variable {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
  [DiscreteMeasurableSpace S] {Ω : Type v} [m : MeasurableSpace Ω]
  (P : StochasticMatrix S) (π : ProbabilityLaw S) (X : ℕ → Ω → S)
  (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (h : IsMarkovChain P π X ℱ μ)
include h

/-- Moving the origin of time preserves the Markov property in the shifted filtration. -/
theorem shifted_chain (r : ℕ) :
    IsMarkovChain P (evolve π P r) (fun n => X (r + n))
      ⟨(fun n => ℱ (r + n)), (fun _ _ hab => ℱ.mono (Nat.add_le_add_left hab r)),
        (fun n => ℱ.le (r + n))⟩ μ := by
  refine ⟨fun n => h.1 (r + n), ?_, ?_⟩
  · intro i
    simpa using DeterministicTransitions.marginal_mass h r i
  · intro n j
    simpa only [Nat.add_assoc] using h.2.2 (r + n) j

theorem stationary_future_law (hπ : IsStationary P π) (r : ℕ) :
    μ.map (fun ω n => X (r + n) ω) = pathLaw P π := by
  have hs := chain_pathLaw P (evolve π P r) (fun n => X (r + n)) _ μ
    (shifted_chain P π X ℱ μ h r)
  rwa [stationary_evolve P π hπ r] at hs

/-- Equality of future path laws pushes forward to every finite selection. -/
theorem stationary_shiftInvariant (hπ : IsStationary P π) : ShiftInvariant X μ := by
  intro k t r
  have hh := congrArg (fun ν : Measure (ℕ → S) =>
    ν.map (fun ω (a : Fin k) => ω (t a)))
    ((stationary_future_law P π X ℱ μ h hπ r).trans
      (stationary_future_law P π X ℱ μ h hπ 0).symm)
  simpa only [Measure.map_map (by fun_prop : Measurable (fun ω (a : Fin k) => ω (t a)))
    (measurable_pi_iff.mpr (fun n => h.1.measurable)), Function.comp_def,
    Nat.zero_add] using hh

/-- Comparing the marginal laws at zero and one suffices for the converse. -/
theorem stationary_of_marginal_eq
    (heq : μ.map (X 1) = μ.map (X 0)) : IsStationary P π := by
  have hm := (marginal_law P π X ℱ μ h 1).symm.trans
    (heq.trans (chain_initial_law P π X ℱ μ h))
  have hp : evolve π P 1 = π := by
    apply PMF.ext
    intro j
    have hj := congrArg (fun ν : Measure S => ν {j}) hm
    simpa only [law_measure_singleton] using hj
  simpa only [IsStationary, evolve, power_one] using hp

theorem stationary_iff_shiftInvariant : IsStationary P π ↔ ShiftInvariant X μ := by
  refine ⟨stationary_shiftInvariant P π X ℱ μ h, ?_⟩
  intro hs
  apply stationary_of_marginal_eq P π X ℱ μ h
  have he := congrArg (fun ν : Measure (Fin 1 → S) => ν.map (fun f => f 0))
    (hs 1 (fun _ => 0) 1)
  rw [Measure.map_map (measurable_pi_apply 0)
    (measurable_pi_iff.mpr (fun _ => h.1.measurable (i := 1 + 0))),
    Measure.map_map (measurable_pi_apply 0)
    (measurable_pi_iff.mpr (fun _ => h.1.measurable (i := 0)))] at he
  simpa only [Function.comp_def, Nat.add_zero] using he

theorem stationary_iff_blockShiftInvariant :
    IsStationary P π ↔ BlockShiftInvariant X μ := by
  constructor
  · intro hπ n r
    exact stationary_shiftInvariant P π X ℱ μ h hπ (n + 1) (fun a => a.val) r
  · intro hb
    apply stationary_of_marginal_eq P π X ℱ μ h
    have he := congrArg (fun ν : Measure (Fin 1 → S) => ν.map (fun f => f 0)) (hb 0 1)
    rw [Measure.map_map (measurable_pi_apply 0)
      (measurable_pi_iff.mpr (fun (a : Fin 1) => h.1.measurable (i := 1 + a.val))),
      Measure.map_map (measurable_pi_apply 0)
      (measurable_pi_iff.mpr (fun (a : Fin 1) => h.1.measurable (i := a.val)))] at he
    simpa only [Function.comp_def, Fin.val_zero, Nat.add_zero] using he
end Chain
end
end P207.Markov
