import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch18.FiniteDiscreteExamples
import MathGenome.Internal.PointSetTopology.D10Topology.Ch02.EmbeddingsAndCharacteristicMaps
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.TotalBoundedPermanence

/-! The two examples in paper.tex, d10:18:sierpinski and d10:18:discrete.
All metric conclusions concern the specified unit metric. -/

open Set Filter TopologicalSpace
open scoped Topology
universe u

namespace D10Topology.Ch18

theorem sierpinski_properties :
    let := Ch02.CharacteristicMaps.topology
    T0Space Bool ∧ CompactSpace Bool ∧ PreconnectedSpace Bool ∧
      ¬ T1Space Bool ∧ ¬ T2Space Bool := by
  let := Ch02.CharacteristicMaps.topology
  have h0 : T0Space Bool := by
    apply (t0Space_iff_exists_isOpen_xor_mem Bool).mpr
    intro x y hxy
    refine ⟨{true}, (Ch02.sierpinski_isOpen_iff _).mpr (Or.inr (Or.inl rfl)), ?_⟩
    cases x <;> cases y <;> simp_all
  have hn1 : ¬ T1Space Bool := by
    intro h
    let := h
    have ho := (isClosed_singleton (x := true)).isOpen_compl
    change (false ∈ ({true} : Set Bool)ᶜ → true ∈ ({true} : Set Bool)ᶜ) at ho
    simpa using ho (by simp)
  have hc : PreconnectedSpace Bool := by
    apply preconnectedSpace_iff_clopen.mpr
    intro U hU
    rcases (Ch02.sierpinski_isOpen_iff U).mp hU.isOpen with h | h | h
    · exact Or.inl h
    · subst U
      have ho := hU.isClosed.isOpen_compl
      change (false ∈ ({true} : Set Bool)ᶜ → true ∈ ({true} : Set Bool)ᶜ) at ho
      exact False.elim (by simpa using ho (by simp))
    · exact Or.inr h
  refine ⟨h0, inferInstance, hc, hn1, ?_⟩
  intro h2
  let := h2
  exact hn1 inferInstance

theorem sierpinski_constant_sequence (x : Bool) :
    Tendsto (fun _ : ℕ => true) atTop (@nhds Bool Ch02.CharacteristicMaps.topology x) := by
  let := Ch02.CharacteristicMaps.topology
  apply tendsto_nhds.mpr
  intro U ho hx
  have ht : true ∈ U := by
    cases x
    · exact ho hx
    · exact hx
  exact Eventually.of_forall (fun _ => ht)

section UnitMetric
variable {X : Type u} [d : MetricSpace X]
  (hd : ∀ x y : X, x ≠ y → dist x y = 1)
include hd

theorem unit_discrete_ball_half (x : X) : Metric.ball x (1 / 2) = {x} := by
  ext y
  constructor
  · intro hy
    have heq : y = x := by
      by_contra hne
      have hh := hd y x hne
      rw [Metric.mem_ball, hh] at hy
      norm_num at hy
    exact mem_singleton_iff.mpr heq
  · rintro rfl
    simp

theorem unit_discrete_topology : DiscreteTopology X := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro x
  rw [← unit_discrete_ball_half hd x]
  exact Metric.isOpen_ball

theorem unit_discrete_cauchy_eventually_constant (s : ℕ → X) (hs : CauchySeq s) :
    ∃ N : ℕ, ∀ n, N ≤ n → s n = s N := by
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hs (1 / 2) (by norm_num)
  refine ⟨N, fun n hn => ?_⟩
  by_contra hne
  have hh := hN n hn N le_rfl
  rw [hd (s n) (s N) hne] at hh
  norm_num at hh

theorem unit_discrete_complete : CompleteSpace X := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro s hs
  obtain ⟨N, hN⟩ := unit_discrete_cauchy_eventually_constant hd s hs
  refine ⟨s N, tendsto_nhds_of_eventually_eq ?_⟩
  exact eventually_atTop.mpr ⟨N, hN⟩

end UnitMetric

theorem infinite_unit_discrete_properties {X : Type u} [Infinite X] [d : MetricSpace X]
    (hd : ∀ x y : X, x ≠ y → dist x y = 1) :
    (∀ x y : X, dist x y ≤ 1) ∧ CompleteSpace X ∧
      ¬ CompactSpace X ∧ ¬ TotallyBounded (univ : Set X) := by
  let := unit_discrete_topology hd
  have hb := Ch09.infinite_unit_discrete_not_totallyBounded hd
  refine ⟨hb.1, unit_discrete_complete hd, ?_, ?_⟩
  · intro hc
    let := hc
    exact Set.infinite_univ
      (isCompact_iff_finite.mp (isCompact_univ : IsCompact (univ : Set X)))
  · exact fun h => hb.2 ((Ch09.totallyBounded_iff_mathlib d.toPseudoMetricSpace).mpr h)

theorem uncountable_unit_discrete_properties {X : Type u} [Uncountable X] [d : MetricSpace X]
    (hd : ∀ x y : X, x ≠ y → dist x y = 1) :
    (∀ x : X, ∃ K : Set X, IsCompact K ∧ K ∈ 𝓝 x) ∧
      FirstCountableTopology X ∧ ¬ SeparableSpace X ∧
        ¬ SecondCountableTopology X ∧ ¬ LindelofSpace X := by
  let := unit_discrete_topology hd
  have hns : ¬ SeparableSpace X := by
    intro hs
    exact not_countable (α := X) (separableSpace_iff_countable.mp hs)
  refine ⟨?_, inferInstance, hns, ?_, ?_⟩
  · intro x
    exact ⟨{x}, isCompact_singleton, (isOpen_discrete _).mem_nhds (mem_singleton x)⟩
  · intro hs
    let := hs
    exact hns inferInstance
  · intro hl
    let := hl
    exact not_countable (α := X) countable_of_Lindelof_of_discrete

end D10Topology.Ch18
