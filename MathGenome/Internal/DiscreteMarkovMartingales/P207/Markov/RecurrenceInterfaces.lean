import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.RecurrenceInterfaces
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.Interfaces
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Foundation.ProcessInterfaces

open MeasureTheory Filter
open scoped ENNReal MeasureTheory
set_option backward.isDefEq.respectTransparency false
universe u v
namespace P207.Markov
noncomputable section

namespace RecurrenceInterfaces
abbrev Accessible : RecurrenceInterfacesSpec.AccessibleType := @P207.Markov.Accessible
abbrev Communicate : RecurrenceInterfacesSpec.CommunicateType := @P207.Markov.Communicate
abbrev communicatingClass : RecurrenceInterfacesSpec.communicatingClassType := @P207.Markov.communicatingClass
abbrev IsCommunicatingClass : RecurrenceInterfacesSpec.IsCommunicatingClassType := @P207.Markov.IsCommunicatingClass
abbrev Irreducible : RecurrenceInterfacesSpec.IrreducibleType := @P207.Markov.Irreducible
abbrev IsClosed : RecurrenceInterfacesSpec.IsClosedType := @P207.Markov.IsClosed
abbrev IsClosedCommunicatingClass : RecurrenceInterfacesSpec.IsClosedCommunicatingClassType := @P207.Markov.IsClosedCommunicatingClass
abbrev positiveReturnTime : RecurrenceInterfacesSpec.positiveReturnTimeType := @P207.Markov.positiveReturnTime
abbrev returnTime : RecurrenceInterfacesSpec.returnTimeType := @P207.Markov.returnTime
abbrev returnProbability : RecurrenceInterfacesSpec.returnProbabilityType := @P207.Markov.returnProbability
abbrev meanReturnTime : RecurrenceInterfacesSpec.meanReturnTimeType := @P207.Markov.meanReturnTime
abbrev Recurrent : RecurrenceInterfacesSpec.RecurrentType := @P207.Markov.Recurrent
abbrev Transient : RecurrenceInterfacesSpec.TransientType := @P207.Markov.Transient
abbrev PositiveRecurrent : RecurrenceInterfacesSpec.PositiveRecurrentType := @P207.Markov.PositiveRecurrent
abbrev NullRecurrent : RecurrenceInterfacesSpec.NullRecurrentType := @P207.Markov.NullRecurrent
abbrev returnLengths : RecurrenceInterfacesSpec.returnLengthsType := @P207.Markov.returnLengths
abbrev period : RecurrenceInterfacesSpec.periodType := @P207.Markov.period
abbrev Aperiodic : RecurrenceInterfacesSpec.AperiodicType := @P207.Markov.Aperiodic
end RecurrenceInterfaces

theorem accessible_refl {S : Type u} (P : StochasticMatrix S) (i : S) :
    Accessible P i i := by
  refine ⟨0, ?_⟩
  simp [power_zero, identity_apply]

theorem accessible_trans {S : Type u} (P : StochasticMatrix S) {i j k : S}
    (hij : Accessible P i j) (hjk : Accessible P j k) : Accessible P i k := by
  obtain ⟨m, hm⟩ := hij
  obtain ⟨n, hn⟩ := hjk
  refine ⟨m + n, ?_⟩
  rw [chapman_kolmogorov]
  exact (ENNReal.mul_pos_iff.mpr ⟨hm, hn⟩).trans_le (ENNReal.le_tsum (f := fun x => power P m i x * power P n x k) j)

theorem communicate_equivalence {S : Type u} (P : StochasticMatrix S) :
    Equivalence (Communicate P) := by
  refine ⟨fun i => ⟨accessible_refl P i, accessible_refl P i⟩,
    fun h => ⟨h.2, h.1⟩, ?_⟩
  intro i j k hij hjk
  exact ⟨accessible_trans P hij.1 hjk.1, accessible_trans P hjk.2 hij.2⟩

theorem isClosed_iff {S : Type u} (P : StochasticMatrix S) (C : Set S) :
    IsClosed P C ↔ ∀ i ∈ C, ∀ j ∉ C, P i j = 0 := by
  constructor
  · intro h i hi j hj
    exact le_antisymm (not_lt.mp (fun hp => hj (h i hi j hp))) zero_le
  · intro h i hi j hp
    by_contra hj
    simp [h i hi j hj] at hp

theorem positiveReturnTime_le_iff {S : Type u} {Ω : Type v}
    (X : ℕ → Ω → S) (i : S) (ω : Ω) (n : ℕ) :
    positiveReturnTime X i ω ≤ n ↔ ∃ k, 1 ≤ k ∧ k ≤ n ∧ X k ω = i := by
  classical
  unfold positiveReturnTime hittingAfter
  split_ifs with h
  · constructor
    · intro hn
      have hs := Nat.sInf_mem h
      exact ⟨_, hs.1, WithTop.coe_le_coe.mp hn, hs.2⟩
    · rintro ⟨k, h1, h2, h3⟩
      exact WithTop.coe_le_coe.mpr ((Nat.sInf_le (s := {k : ℕ | 1 ≤ k ∧ X k ω ∈ ({i} : Set S)}) ⟨h1, h3⟩).trans h2)
  · constructor
    · simp
    · rintro ⟨k, h1, _, h3⟩
      exact (h ⟨k, h1, h3⟩).elim

theorem positiveReturnTime_finite_iff {S : Type u} {Ω : Type v}
    (X : ℕ → Ω → S) (i : S) (ω : Ω) :
    positiveReturnTime X i ω < ⊤ ↔ ∃ k : ℕ, 1 ≤ k ∧ X k ω = i := by
  rw [lt_top_iff_ne_top]
  simp [positiveReturnTime, hittingAfter_eq_top_iff]

theorem positiveReturnTime_isStoppingTime {S : Type u} [MeasurableSpace S]
    [MeasurableSingletonClass S] {Ω : Type v} [m : MeasurableSpace Ω]
    (X : ℕ → Ω → S) (ℱ : Filtration ℕ m) (hX : Adapted ℱ X) (i : S) :
    P207.IsDiscreteStoppingTime ℱ (positiveReturnTime X i) := by
  exact hX.isStoppingTime_hittingAfter (measurableSet_singleton i)

section Discrete
variable {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

theorem returnTime_isStoppingTime (i : S) :
    P207.IsDiscreteStoppingTime coordinateFiltration (returnTime i) := by
  exact positiveReturnTime_isStoppingTime coordinate coordinateFiltration
    (P207.adapted_naturalFiltration coordinate (fun n => measurable_pi_apply n)) i

theorem measurableSet_returnTime_finite (i : S) :
    MeasurableSet {ω : ℕ → S | returnTime i ω < ⊤} := by
  have he : {ω : ℕ → S | returnTime i ω < ⊤} =
      ⋃ k : ℕ, ⋃ (_ : 1 ≤ k), {ω | ω k = i} := by
    ext ω
    simp [returnTime, positiveReturnTime_finite_iff, coordinate]
  rw [he]
  exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ =>
    measurableSet_eq_fun (measurable_pi_apply k) measurable_const

theorem measurable_returnTime (i : S) : Measurable (returnTime i) := by
  apply measurable_to_countable'
  intro t
  rcases WithTop.recTopCoe (C := fun t : WithTop ℕ => t = ⊤ ∨ ∃ n : ℕ, t = n)
    (Or.inl rfl) (fun n => Or.inr ⟨n, rfl⟩) t with ht | ⟨n, rfl⟩
  · subst t
    simpa only [Set.preimage_singleton, not_lt_top_iff, Set.compl_ofPred] using
      (measurableSet_returnTime_finite i).compl
  · exact coordinateFiltration.le n _ (MeasureTheory.IsStoppingTime.measurableSet_eq_of_countable (returnTime_isStoppingTime i) n)

theorem measurable_returnDuration (i : S) :
    Measurable (fun ω : ℕ → S => ENat.toENNReal (returnTime i ω)) := by
  exact (measurable_of_countable (fun t : WithTop ℕ => ENat.toENNReal t)).comp
    (measurable_returnTime i)

local instance recurrence_statePathLaw_probability (P : StochasticMatrix S) (i : S) :
    IsProbabilityMeasure (statePathLaw P i) := by
  unfold statePathLaw
  infer_instance

theorem returnProbability_le_one (P : StochasticMatrix S) (i : S) :
    returnProbability P i ≤ 1 := by
  exact prob_le_one

theorem positiveRecurrent_recurrent (P : StochasticMatrix S) (i : S)
    (h : PositiveRecurrent P i) : Recurrent P i := by
  have hf := ae_lt_top (measurable_returnDuration i) h.ne
  apply (mem_ae_iff_prob_eq_one (measurableSet_returnTime_finite i)).mp
  filter_upwards [hf] with ω hω
  exact ENat.toENNReal_lt_top.mp hω

theorem transient_iff_not_recurrent (P : StochasticMatrix S) (i : S) :
    Transient P i ↔ ¬ Recurrent P i := by
  exact lt_iff_le_and_ne.trans (by simp [Recurrent, returnProbability_le_one P i])

end Discrete

theorem period_eq_zero_iff {S : Type u} (P : StochasticMatrix S) (i : S) :
    period P i = 0 ↔ returnLengths P i = ∅ := by
  rw [period, Nat.setGcd_eq_zero_iff]
  constructor
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro n hn
    have hz := h hn
    simp only [Set.mem_singleton_iff] at hz
    have := hn.1
    omega
  · intro h
    simp [h]

theorem period_dvd_returnLength {S : Type u} (P : StochasticMatrix S) (i : S)
    (n : ℕ) (hn : n ∈ returnLengths P i) : period P i ∣ n :=
  Nat.setGcd_dvd_of_mem hn

theorem dvd_period_iff {S : Type u} (P : StochasticMatrix S) (i : S) (d : ℕ) :
    d ∣ period P i ↔ ∀ n ∈ returnLengths P i, d ∣ n :=
  Nat.dvd_setGcd_iff

end
end P207.Markov
