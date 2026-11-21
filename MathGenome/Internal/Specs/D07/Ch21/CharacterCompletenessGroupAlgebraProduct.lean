import MathGenome.Internal.Specs.D07.Ch21.RegularDecomposition
import MathGenome.Internal.Specs.D07.Ch21.GroupAlgebra
import Mathlib.Algebra.Algebra.Pi

/-!
The first paragraph of the proof of K07.21.character_completeness,
paper.tex:6390–6404. The factors are the actual endomorphism algebras,
with multiplication given by composition. A complete family contains
one representative of each irreducible type; finite dimension of its
members is a conclusion of the upstream regular-representation theorem,
and is not imposed as an additional hypothesis here.
-/
namespace Specs.D07.Ch21.CharacterCompletenessGroupAlgebraProduct

universe u r v
noncomputable section

open Specs.D07.Ch21.RegularDecomposition

/-- Type of the simultaneous, unital complex algebra action. -/
def ActionMapType : Type (max (u + 1) (r + 1) (v + 1)) :=
  ∀ (G : Type u) [Group G] (I : Type r) (V : I → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)],
    (∀ i, Representation ℂ G (V i)) →
      MonoidAlgebra ℂ G →ₐ[ℂ] (∀ i, Module.End ℂ (V i))

/-- Each component is exactly the linear extension of the original action. -/
def actionMapValue : ActionMapType.{u,r,v} :=
  fun _ _ _ _ _ _ ρ => AlgHom.pi (fun i => (ρ i).asAlgebraHom)

/-- Faithfulness is already forced by completeness, without a
nonrepetition assumption on the family. -/
def ActionMapInjective : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (I : Type r) [Fintype I]
    (V : I → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)),
    (∀ i, Representation.IsIrreducible (ρ i)) → IsComplete ρ →
      Function.Injective (actionMapValue G I V ρ)

/-- Both sides of the action map have dimension |G|, by the regular
square sum and dim End(V_i) = (dim V_i)^2. -/
def ProductDimension : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (I : Type r) [Fintype I]
    (V : I → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)),
    (∀ i, Representation.IsIrreducible (ρ i)) →
    (∀ i j, i ≠ j → ¬ Nonempty ((ρ i).Equiv (ρ j))) → IsComplete ρ →
      Module.finrank ℂ (MonoidAlgebra ℂ G) = Fintype.card G ∧
      Module.finrank ℂ (∀ i, Module.End ℂ (V i)) = Fintype.card G

def ActionMapSurjective : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (I : Type r) [Fintype I]
    (V : I → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)),
    (∀ i, Representation.IsIrreducible (ρ i)) →
    (∀ i j, i ≠ j → ¬ Nonempty ((ρ i).Equiv (ρ j))) → IsComplete ρ →
      Function.Surjective (actionMapValue G I V ρ)

/-- The isomorphism is the specified action map, rather than an unrelated
abstract equivalence of algebras of the same dimension. -/
def GroupAlgebraProduct : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (I : Type r) [Fintype I]
    (V : I → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)),
    (∀ i, Representation.IsIrreducible (ρ i)) →
    (∀ i j, i ≠ j → ¬ Nonempty ((ρ i).Equiv (ρ j))) → IsComplete ρ →
      ∃ e : MonoidAlgebra ℂ G ≃ₐ[ℂ] (∀ i, Module.End ℂ (V i)),
        e.toAlgHom = actionMapValue G I V ρ

end
end Specs.D07.Ch21.CharacterCompletenessGroupAlgebraProduct
