import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SchlessingerTangentVectorSpace

universe u w

namespace CommutativeAlgebraNotes.SchlessingerHullCriterionSpec

open CategoryTheory SchlessingerConditionsSpec SchlessingerTangentVectorSpaceSpec

/-- Evaluation on the quotient maps identifies natural transformations from
`h_R` with compatible elements on the positive-power Artin quotients of `R`. -/
def FormalFamilyCorrespondence : Prop :=
  ∀ {k : Type u} [Field k] (R : CompleteLocalAlgebraModel k) (F : ArtinFunctorModel.{u,w} k),
    let realizes (τ : (representableModel.{u,w} R).toFunctor ⟶ F.toFunctor)
        (x : CompatibleFamilyModel R F) :=
      ∀ n : ℕ, τ.app (truncationModel R n) (ULift.up (toTruncationModel R n)) = x.val n
    (∀ τ, ∃! x, realizes τ x) ∧ (∀ x, ∃! τ, realizes τ x)

/-- Theorem 6.9 in the classical category of local Artin algebras over a field. -/
def HullCriterion : Prop :=
  ∀ {k : Type u} [Field k] (F : ArtinFunctorModel.{u,w} k),
    Nonempty (HullModel F) ↔ H1Model F ∧ H2Model F ∧ H3Model F

end CommutativeAlgebraNotes.SchlessingerHullCriterionSpec
