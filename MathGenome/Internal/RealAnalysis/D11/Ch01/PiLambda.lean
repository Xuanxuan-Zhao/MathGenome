import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.PiLambda

/-! # The π–λ theorem

The native Dynkin generation is least by `generate_le` and contains its
generators by `GenerateHas.basic`. For an intersection-closed family,
Mathlib's π–λ theorem identifies its generated sigma-algebra with the
measurable-space structure carried by that same generated Dynkin system.
We take the underlying families to obtain precisely the source equality.
-/

open Set MeasurableSpace
open scoped MeasureTheory

universe u

namespace D11.Ch01.PiLambda

theorem lambdaSystem_iff :
  ∀ {α : Type u} (L : Set (Set α)),
  (∃ D : DynkinSystem α, ∀ s, D.Has s ↔ s ∈ L) ↔
    Set.univ ∈ L ∧ (∀ s ∈ L, sᶜ ∈ L) ∧
      (∀ E : ℕ → Set α, Pairwise (fun i j => Disjoint (E i) (E j)) →
        (∀ n, E n ∈ L) → (⋃ n, E n) ∈ L) := by
  intro α L
  constructor
  · rintro ⟨D, hD⟩
    refine ⟨(hD Set.univ).mp D.has_univ, ?_, ?_⟩
    · intro s hs
      exact (hD sᶜ).mp (D.has_compl ((hD s).mpr hs))
    · intro E hdisj hE
      exact (hD (⋃ n, E n)).mp (D.has_iUnion hdisj fun n => (hD (E n)).mpr (hE n))
  · rintro ⟨hU, hc, hu⟩
    refine ⟨{
      Has := fun s => s ∈ L
      has_empty := by simpa using hc Set.univ hU
      has_compl := fun {s} hs => hc s hs
      has_iUnion_nat := fun {E} hd hE => hu E hd hE
    }, fun _ => Iff.rfl⟩

theorem generated_contains :
  ∀ {α : Type u} (P : Set (Set α)),
    P ⊆ {s : Set α | (DynkinSystem.generate P).Has s} := by
  intro α P s hs
  exact DynkinSystem.GenerateHas.basic s hs

theorem generated_le_iff :
  ∀ {α : Type u} (P : Set (Set α)) (D : DynkinSystem α),
    {s : Set α | (DynkinSystem.generate P).Has s} ⊆ {s : Set α | D.Has s} ↔
      P ⊆ {s : Set α | D.Has s} := by
  intro α P D
  constructor
  · intro h s hs
    exact h (generated_contains P hs)
  · intro h
    exact D.generate_le h

theorem pi_lambda :
  ∀ {α : Type u} (P : Set (Set α)),
    (∀ s ∈ P, ∀ t ∈ P, s ∩ t ∈ P) →
      {s : Set α | (DynkinSystem.generate P).Has s} =
        {s : Set α | MeasurableSet[MeasurableSpace.generateFrom P] s} := by
  intro α P hP
  have hp : IsPiSystem P := fun s hs t ht _ => hP s hs t ht
  ext s
  change (DynkinSystem.generate P).Has s ↔ MeasurableSet[MeasurableSpace.generateFrom P] s
  rw [DynkinSystem.generateFrom_eq hp]
  rfl

end D11.Ch01.PiLambda
