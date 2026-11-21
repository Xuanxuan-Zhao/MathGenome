import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.SetSystems
import Mathlib.MeasureTheory.PiSystem

/-!
Independent statements for paper.tex:372–400, the π–λ theorem.

The λ-system is the native `MeasurableSpace.DynkinSystem`; the first
statement checks its equivalence with the paper's whole-space,
complement, and countable disjoint-union axioms. Its native `generate`
is the least λ-system, as expressed by the next two statements.
Sigma-algebra generation is the canonical `MeasurableSpace.generateFrom`
already used by SetSystems.

The paper's intersection hypothesis is written explicitly in `pi_lambda`.
Unlike Mathlib's `IsPiSystem`, it includes empty binary intersections.
Binary closure also implies closure under every nonempty finite
intersection. No nonemptiness assumption on the ambient type or family
is imposed; requiring the empty finite intersection as well would merely
give a specialization of this theorem.
-/

open Set MeasurableSpace
open scoped MeasureTheory

universe u

namespace Specs.D11.Ch01.PiLambda

def lambdaSystem_iff : Prop :=
  ∀ {α : Type u} (L : Set (Set α)),
  (∃ D : DynkinSystem α, ∀ s, D.Has s ↔ s ∈ L) ↔
    Set.univ ∈ L ∧ (∀ s ∈ L, sᶜ ∈ L) ∧
      (∀ E : ℕ → Set α, Pairwise (fun i j => Disjoint (E i) (E j)) →
        (∀ n, E n ∈ L) → (⋃ n, E n) ∈ L)

def generated_contains : Prop :=
  ∀ {α : Type u} (P : Set (Set α)),
    P ⊆ {s : Set α | (DynkinSystem.generate P).Has s}

def generated_le_iff : Prop :=
  ∀ {α : Type u} (P : Set (Set α)) (D : DynkinSystem α),
    {s : Set α | (DynkinSystem.generate P).Has s} ⊆ {s : Set α | D.Has s} ↔
      P ⊆ {s : Set α | D.Has s}

def pi_lambda : Prop :=
  ∀ {α : Type u} (P : Set (Set α)),
    (∀ s ∈ P, ∀ t ∈ P, s ∩ t ∈ P) →
      {s : Set α | (DynkinSystem.generate P).Has s} =
        {s : Set α | MeasurableSet[MeasurableSpace.generateFrom P] s}

end Specs.D11.Ch01.PiLambda
