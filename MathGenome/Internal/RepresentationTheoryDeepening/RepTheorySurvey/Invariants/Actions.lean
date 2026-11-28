import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.Actions
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ComoduleFiniteness

open LinearAlgebraicGroups
open scoped TensorProduct

universe u v w

namespace RepTheorySurvey.Invariants

/-- An action of an abstract group by algebra automorphisms over the ground field. -/
abbrev GroupAlgebraAction (k : Type u) (G : Type v) (A : Type w)
    [Field k] [Group G] [Ring A] [Algebra k A] := Specs.GroupAlgebraAction k G A

namespace GroupAlgebraAction

variable {k : Type u} {G : Type v} {A : Type w}
  [Field k] [Group G] [Ring A] [Algebra k A]

abbrev toRepresentation (ρ : GroupAlgebraAction k G A) : Representation k G A :=
  Specs.groupRepresentation ρ

abbrev fixedSubalgebra (ρ : GroupAlgebraAction k G A) : Subalgebra k A :=
  Specs.groupFixedSubalgebra ρ

abbrev IsReynolds (ρ : GroupAlgebraAction k G A) (R : A →ₗ[k] ρ.fixedSubalgebra) : Prop :=
  Specs.groupIsReynolds ρ R

@[simp]
theorem fixedSubalgebra_toSubmodule (ρ : GroupAlgebraAction k G A) :
    ρ.fixedSubalgebra.toSubmodule = ρ.toRepresentation.invariants := rfl

end GroupAlgebraAction

namespace GroupRepresentation

abbrev LocallyFinite {k : Type u} {G : Type v} {V : Type w}
    [Field k] [Group G] [AddCommGroup V] [Module k V] (ρ : Representation k G V) : Prop :=
  Specs.groupLocallyFinite ρ

/-- In `LinearlyReductive.{u,v,w} k G`, the third universe is that of the representation spaces. -/
abbrev LinearlyReductive (k : Type u) (G : Type v) [Field k] [Group G] : Prop :=
  Specs.groupLinearlyReductive.{u,v,w} k G

/-- The span of each orbit is a finite-dimensional subrepresentation. -/
theorem locallyFinite_of_finite {k : Type u} {G : Type v} {V : Type w}
    [Field k] [Group G] [Finite G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) : LocallyFinite ρ := by
  intro x
  let orbit : Set V := Set.range (fun g : G ↦ ρ g x)
  let W : Submodule k V := Submodule.span k orbit
  have stable (g : G) : W ≤ W.comap (ρ g) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨h, rfl⟩
    exact Submodule.subset_span (s := orbit) ⟨g * h, by simp⟩
  refine ⟨⟨W, fun g _ hy ↦ stable g hy⟩, ?_, FiniteDimensional.span_of_finite k
    (Set.finite_range (fun g : G ↦ ρ g x))⟩
  exact Submodule.subset_span (s := orbit) ⟨1, by simp⟩

end GroupRepresentation

namespace RationalRepresentation

abbrev trivial := @Specs.rationalTrivial

abbrev IsComoduleMap := @Specs.isComoduleMap

abbrev LocallyFinite := @Specs.rationalLocallyFinite

abbrev IsSimpleSubcomodule := @Specs.rationalIsSimpleSubcomodule

abbrev LinearlyReductive := @Specs.rationalLinearlyReductive

/-- Every vector of a right comodule lies in a finite-dimensional subcomodule. -/
theorem locallyFinite {k V : Type u} [Field k] {H : HopfAlgebraCategory k}
    [AddCommGroup V] [Module k V] (ρ : RightComodule k H V) : LocallyFinite ρ :=
  ρ.exists_finiteSubcomodule

end RationalRepresentation

/-- An algebra coaction over a commutative Hopf algebra over the ground field. -/
abbrev RationalAlgebraAction {k : Type u} [Field k] (H : HopfAlgebraCategory k) (A : Type u)
    [Ring A] [Algebra k A] := Specs.RationalAlgebraAction H A

namespace RationalAlgebraAction

variable {k : Type u} [Field k] {H : HopfAlgebraCategory k} {A : Type u} [Ring A] [Algebra k A]

abbrev toRightComodule (ρ : RationalAlgebraAction H A) : RightComodule k H A :=
  Specs.rationalToRightComodule ρ

abbrev fixedSubalgebra (ρ : RationalAlgebraAction H A) : Subalgebra k A :=
  Specs.rationalFixedSubalgebra ρ

abbrev IsReynolds (ρ : RationalAlgebraAction H A) (R : A →ₗ[k] ρ.fixedSubalgebra) : Prop :=
  Specs.rationalIsReynolds ρ R

@[simp]
theorem fixedSubalgebra_toSubmodule (ρ : RationalAlgebraAction H A) :
    ρ.fixedSubalgebra.toSubmodule = RationalRepresentations.invariants H ρ.toRightComodule := rfl

end RationalAlgebraAction

end RepTheorySurvey.Invariants
