import MathGenome.Internal.Specs.D07.Ch12.AdjoinDefinition
import Mathlib.FieldTheory.LinearDisjoint

/-!
Independent specification for K07.12.compositum_degree_bound,
paper.tex:3671–3678. The common ambient field Ω and its `Algebra K Ω`
fix the embeddings. The compositum is the lattice supremum, identified with
the generated field by the upstream `CompositumSup` statement.

All degree assertions below assume both intermediate extensions are finite.
`Module.rank` is cardinal dimension; `Module.finrank` is its natural value
under these hypotheses. Independence is tested in Ω with the canonical
F-action induced by inclusion. The basis is arbitrary, including its index
universe: no special power basis or separability is assumed.

The subsequent cubic-field counterexample is separately allocated to
K07.12.compositum_degree_bound.trivial_intersection_insufficient.
-/

universe u v w s

namespace Specs.D07.Ch12.CompositumDegreeBound

/-- The compositum of two finite intermediate extensions is finite. -/
def FiniteCompositum : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    (E F : IntermediateField K Ω) [FiniteDimensional K E] [FiniteDimensional K F],
    FiniteDimensional K ↥(E ⊔ F)

/-- The degree bound in the source's cardinal-valued degree convention. -/
def CardinalDegreeBound : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    (E F : IntermediateField K Ω) [FiniteDimensional K E] [FiniteDimensional K F],
    Module.rank K ↥(E ⊔ F) ≤ Module.rank K E * Module.rank K F

/-- The natural-number form of the bound, with finiteness explicit. -/
def DegreeBound : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    (E F : IntermediateField K Ω) [FiniteDimensional K E] [FiniteDimensional K F],
    Module.finrank K ↥(E ⊔ F) ≤ Module.finrank K E * Module.finrank K F

/-- Equality holds exactly when the chosen K-basis of E remains independent
in the common overfield after extending scalars to F. -/
def EqualityIffBasisIndependent : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    (E F : IntermediateField K Ω) [FiniteDimensional K E] [FiniteDimensional K F]
    (I : Type w) (b : Module.Basis I K E),
    (Module.finrank K ↥(E ⊔ F) = Module.finrank K E * Module.finrank K F ↔
      LinearIndependent F (fun i => (b i : Ω)))

/-- The equality condition uses the ordinary linear-disjointness predicate,
which is defined by injectivity of the multiplication map on the tensor product. -/
def EqualityIffLinearDisjoint : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    (E F : IntermediateField K Ω) [FiniteDimensional K E] [FiniteDimensional K F],
    (Module.finrank K ↥(E ⊔ F) = Module.finrank K E * Module.finrank K F ↔
      E.LinearDisjoint F)

/-- The source's basis-independence assertion, allowing different index types. -/
def BasisIndependenceInvariant : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    (E F : IntermediateField K Ω) [FiniteDimensional K E] [FiniteDimensional K F]
    (I : Type w) (J : Type s) (b : Module.Basis I K E) (c : Module.Basis J K E),
    (LinearIndependent F (fun i => (b i : Ω)) ↔
      LinearIndependent F (fun j => (c j : Ω)))

end Specs.D07.Ch12.CompositumDegreeBound
