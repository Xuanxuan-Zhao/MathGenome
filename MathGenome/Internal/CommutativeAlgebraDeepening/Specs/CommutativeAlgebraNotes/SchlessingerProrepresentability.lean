import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SchlessingerTangentVectorSpace

/-! Theorem 6.10 for normalized functors on local Artin algebras. -/

universe u w

namespace CommutativeAlgebraNotes.SchlessingerProrepresentabilitySpec

open CategoryTheory SchlessingerConditionsSpec SchlessingerTangentVectorSpaceSpec

/-- Under H1–H3, the transformation of any given hull represents the functor
exactly when H4 holds. -/
def HullRepresentsIff : Prop :=
  ∀ {k : Type u} [Field k] {F : ArtinFunctorModel.{u,w} k},
    H1Model F → H2Model F → H3Model F → ∀ h : HullModel F,
      IsIso h.transformation ↔ H4Model F

/-- Every prorepresentable functor satisfies all four Schlessinger conditions. -/
def ConditionsOfProrepresentable : Prop :=
  ∀ {k : Type u} [Field k] {F : ArtinFunctorModel.{u,w} k},
    ProrepresentableModel F → H1Model F ∧ H2Model F ∧ H3Model F ∧ H4Model F

end CommutativeAlgebraNotes.SchlessingerProrepresentabilitySpec
