import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SchlessingerTangentVectorSpace

universe u w

namespace CommutativeAlgebraNotes.SchlessingerConditionsFromHullSpec

open SchlessingerConditionsSpec SchlessingerTangentVectorSpaceSpec

/-- A hull is surjective on every Artin algebra. -/
def HullComponentSurjective : Prop :=
  ∀ {k : Type u} [Field k] {F : ArtinFunctorModel.{u,w} k} (h : HullModel F)
    (A : LocalArtinAlgebra.{u,u} k), Function.Surjective (h.transformation.app A)

/-- The existence of a hull implies all three conditions of Schlessinger's criterion. -/
def ConditionsFromHull : Prop :=
  ∀ {k : Type u} [Field k] (F : ArtinFunctorModel.{u,w} k),
    Nonempty (HullModel F) → H1Model F ∧ H2Model F ∧ H3Model F

end CommutativeAlgebraNotes.SchlessingerConditionsFromHullSpec
