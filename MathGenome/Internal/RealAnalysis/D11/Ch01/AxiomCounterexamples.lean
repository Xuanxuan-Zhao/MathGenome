import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureDefinitions
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.AxiomCounterexamples
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated

open Set MeasureTheory
open scoped ENNReal

namespace D11.Ch01.AxiomCounterexamples

private theorem threePoint_cases (x : ThreePoint) :
    x = pointOne ∨ x = pointTwo ∨ x = pointThree := by
  rcases x with ⟨x, hx⟩
  simp only [mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

private theorem first_measurable (s : Set ThreePoint) :
    MeasurableSet[MeasurableSpace.generateFrom {{pointOne}}] s ↔ s ∈ firstFamily := by
  rw [measurableSet_generateFrom_singleton_iff]
  have hc : ({pointOne} : Set ThreePoint)ᶜ = {pointTwo, pointThree} := by
    ext x
    rcases threePoint_cases x with rfl | rfl | rfl <;>
      simp [pointOne, pointTwo, pointThree]
  simp only [hc, firstFamily, mem_insert_iff, mem_singleton_iff]
  tauto

private theorem second_measurable (s : Set ThreePoint) :
    MeasurableSet[MeasurableSpace.generateFrom {{pointTwo}}] s ↔ s ∈ secondFamily := by
  rw [measurableSet_generateFrom_singleton_iff]
  have hc : ({pointTwo} : Set ThreePoint)ᶜ = {pointOne, pointThree} := by
    ext x
    rcases threePoint_cases x with rfl | rfl | rfl <;>
      simp [pointOne, pointTwo, pointThree]
  simp only [hc, secondFamily, mem_insert_iff, mem_singleton_iff]
  tauto

theorem union_sigma_failure : Specs.D11.Ch01.AxiomCounterexamples.union_sigma_failure := by
  have h0 : ({pointOne} : Set ThreePoint) ∈ firstFamily ∪ secondFamily := by
    simp [firstFamily, secondFamily]
  have h1 : ({pointTwo} : Set ThreePoint) ∈ firstFamily ∪ secondFamily := by
    simp [firstFamily, secondFamily]
  have h01 : ({pointOne} ∪ {pointTwo} : Set ThreePoint) ∉ firstFamily ∪ secondFamily := by
    intro h
    simp only [mem_union, firstFamily, secondFamily, mem_insert_iff,
      mem_singleton_iff] at h
    rcases h with (h | h | h | h) | (h | h | h | h)
    all_goals
      have ha := congrArg (fun s : Set ThreePoint => pointOne ∈ s) h
      have hb := congrArg (fun s : Set ThreePoint => pointTwo ∈ s) h
      have hc := congrArg (fun s : Set ThreePoint => pointThree ∈ s) h
      simp [pointOne, pointTwo, pointThree] at ha hb hc
  have hA : ¬ IsSetAlgebra (firstFamily ∪ secondFamily) :=
    fun h => h01 (h.union_mem h0 h1)
  refine ⟨⟨MeasurableSpace.generateFrom {{pointOne}}, MeasurableSpace.generateFrom {{pointTwo}},
    first_measurable, second_measurable⟩, h0, h1, h01, hA, ?_⟩
  rintro ⟨m, hm⟩
  let : MeasurableSpace ThreePoint := m
  exact h01 ((hm _).mp (((hm _).mpr h0).union ((hm _).mpr h1)))

theorem finiteCofinite_isAlgebra : Specs.D11.Ch01.AxiomCounterexamples.finiteCofinite_isAlgebra := by
  refine ⟨Or.inl finite_empty, ?_, ?_⟩
  · intro s hs
    rcases hs with hs | hs
    · exact Or.inr (by simpa using hs)
    · exact Or.inl hs
  · intro s t hs ht
    rcases hs with hs | hs
    · rcases ht with ht | ht
      · exact Or.inl (hs.union ht)
      · exact Or.inr (ht.subset (by intro x hx hxt; exact hx (Or.inr hxt)))
    · exact Or.inr (hs.subset (by intro x hx hxs; exact hx (Or.inl hxs)))

theorem charge_values : Specs.D11.Ch01.AxiomCounterexamples.charge_values := by
  constructor
  · intro s hs
    simp [cofiniteCharge, hs]
  · intro s hs
    simp [cofiniteCharge, infinite_of_finite_compl hs]

private theorem charge_union {s t : Set ℕ}
    (hs : s ∈ finiteCofinite) (ht : t ∈ finiteCofinite) (hd : Disjoint s t) :
    cofiniteCharge (s ∪ t) = cofiniteCharge s + cofiniteCharge t := by
  rcases hs with hs | hs
  · rcases ht with ht | ht
    · simp [charge_values.1 _ hs, charge_values.1 _ ht,
        charge_values.1 _ (hs.union ht)]
    · have hu : (s ∪ t)ᶜ.Finite :=
        ht.subset (by intro x hx hxt; exact hx (Or.inr hxt))
      simp [charge_values.1 _ hs, charge_values.2 _ ht, charge_values.2 _ hu]
  · have ht' : t.Finite := hs.subset (disjoint_left.mp hd.symm)
    have hu : (s ∪ t)ᶜ.Finite :=
      hs.subset (by intro x hx hxs; exact hx (Or.inl hxs))
    simp [charge_values.2 _ hs, charge_values.1 _ ht', charge_values.2 _ hu]

theorem finite_additive_charge : Specs.D11.Ch01.AxiomCounterexamples.finite_additive_charge := by
  intro hA
  refine ⟨{
    value := fun s => cofiniteCharge s.1
    empty := charge_values.1 _ finite_empty
    union := fun s t hd => charge_union s.2 t.2 hd
  }, fun _ => rfl⟩

theorem charge_finite_additivity : Specs.D11.Ch01.AxiomCounterexamples.charge_finite_additivity := by
  intro n E hE hd
  obtain ⟨p, hp⟩ := finite_additive_charge finiteCofinite_isAlgebra
  have h := MeasureDefinitions.finite_additivity finiteCofinite_isAlgebra p
    Finset.univ (fun i => ⟨E i, hE i⟩) (fun i _ j _ hij => hd hij)
  simpa only [hp, Finset.mem_univ, iUnion_true, Finset.sum_const_zero] using h

theorem countable_additivity_failure :
    Specs.D11.Ch01.AxiomCounterexamples.countable_additivity_failure := by
  have hU : (⋃ n : ℕ, ({n} : Set ℕ)) = univ := by
    ext x
    simp
  have h1 : cofiniteCharge univ = 1 := charge_values.2 _ (by simp)
  have h0 : (∑' n : ℕ, cofiniteCharge {n}) = 0 := by
    simp [cofiniteCharge]
  refine ⟨fun n => Or.inl (finite_singleton n), ?_, hU, h1, h0, ?_⟩
  · intro i j hij
    simpa using hij
  · rw [hU, h1, h0]
    exact one_ne_zero

theorem no_countably_additive_extension :
    Specs.D11.Ch01.AxiomCounterexamples.no_countably_additive_extension := by
  rintro ⟨μ, hμ⟩
  let : MeasurableSpace ℕ := ⊤
  have hU : μ univ = 1 := (hμ univ (Or.inr (by simp))).trans
    (charge_values.2 _ (by simp))
  have hn : ∀ n : ℕ, μ {n} = 0 := fun n =>
    (hμ {n} (Or.inl (finite_singleton n))).trans (charge_values.1 _ (finite_singleton n))
  have h := measure_iUnion (μ := μ)
    (show Pairwise (fun i j : ℕ => Disjoint ({i} : Set ℕ) {j}) from
      fun _ _ hij => by simpa using hij)
    (fun _ => MeasurableSpace.measurableSet_top)
  have hUnion : (⋃ n : ℕ, ({n} : Set ℕ)) = univ := by
    ext x
    simp
  rw [hUnion] at h
  simp only [hn, tsum_zero] at h
  exact one_ne_zero (hU.symm.trans h)

end D11.Ch01.AxiomCounterexamples
