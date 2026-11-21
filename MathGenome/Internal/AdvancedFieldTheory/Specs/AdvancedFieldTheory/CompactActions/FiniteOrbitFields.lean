import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Foundations
import Mathlib.Topology.Algebra.OpenSubgroup

/-! Independent specification for the finite-stage construction in C11,
notes/003/advanced-field-theory.tex, lines 957–994.
The base is the actual fixed subfield; stages are literal intermediate fields.
Faithfulness is unnecessary for these finite-stage assertions. -/

universe u v
noncomputable section
open scoped Classical
set_option linter.checkUnivs false
namespace Specs.AdvancedFieldTheory.CompactActions

def fixedBase (G : Type u) (E : Type v) [Group G] [Field E]
    [MulSemiringAction G E] : Subfield E := FixedPoints.subfield G E

def fixedBase_type := ∀ (G : Type u) (E : Type v) [Group G] [Field E]
    [MulSemiringAction G E], Subfield E

def orbitGenerators (G : Type u) (E : Type v) [Group G] [Field E]
    [MulSemiringAction G E] (S : Finset E) : Set E :=
  {y | ∃ x ∈ S, ∃ g : G, g • x = y}

def orbitGenerators_type := ∀ (G : Type u) (E : Type v) [Group G] [Field E]
    [MulSemiringAction G E], Finset E → Set E

def orbitField (G : Type u) (E : Type v) [Group G] [Field E]
    [MulSemiringAction G E] (S : Finset E) : IntermediateField (fixedBase G E) E :=
  IntermediateField.adjoin (fixedBase G E) (orbitGenerators G E S)

def orbitField_type := ∀ (G : Type u) (E : Type v) [Group G] [Field E]
    [MulSemiringAction G E], Finset E → IntermediateField (fixedBase G E) E

def finite_orbits_type : Prop :=
  ∀ (G : Type u) (E : Type v) [Group G] [Field E] [MulSemiringAction G E]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G],
    (∀ a : E, IsOpen (MulAction.stabilizer G a : Set G)) →
    ∀ a : E, (MulAction.orbit G a).Finite

def finiteOrbitStage_type : Prop :=
  ∀ (G : Type u) (E : Type v) [Group G] [Field E] [MulSemiringAction G E]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G],
    (∀ a : E, IsOpen (MulAction.stabilizer G a : Set G)) →
    ∀ S : Finset E,
    (orbitGenerators G E S).Finite ∧
    (∀ (g : G) (x : E), x ∈ orbitField G E S → g • x ∈ orbitField G E S) ∧
    ∃ ρ : G →* (orbitField G E S ≃ₐ[fixedBase G E] orbitField G E S),
      (∀ (g : G) (x : orbitField G E S), (ρ g x : E) = g • (x : E)) ∧
      Finite ρ.range ∧
      IntermediateField.fixedField ρ.range = ⊥ ∧
      FiniteDimensional (fixedBase G E) (orbitField G E S) ∧
      IsGalois (fixedBase G E) (orbitField G E S) ∧
      Function.Surjective ρ

def directed_cover_cofinal_type : Prop :=
  ∀ (G : Type u) (E : Type v) [Group G] [Field E] [MulSemiringAction G E],
    (∀ S T : Finset E, orbitField G E S ≤ orbitField G E (S ∪ T) ∧
      orbitField G E T ≤ orbitField G E (S ∪ T)) ∧
    (∀ x : E, ∃ S : Finset E, x ∈ orbitField G E S) ∧
    (∀ M : IntermediateField (fixedBase G E) E,
      FiniteDimensional (fixedBase G E) M → IsGalois (fixedBase G E) M →
      ∃ S : Finset E, M ≤ orbitField G E S) ∧
    orbitField G E ∅ = ⊥

end Specs.AdvancedFieldTheory.CompactActions
