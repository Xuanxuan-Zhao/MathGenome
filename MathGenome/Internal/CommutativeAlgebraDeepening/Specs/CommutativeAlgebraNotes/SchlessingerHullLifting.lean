import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ConstructSchlessingerCandidate

/-! Smoothness of the map induced by the tower in the forward direction of Theorem 6.9. -/

universe u w

namespace CommutativeAlgebraNotes.SchlessingerHullLiftingSpec

open CategoryTheory LocalArtinAlgebra SchlessingerConditionsSpec SchlessingerCandidateSpec
  IsLocalRing

/-- The compatible formal object on the limit of the constructed tower gives a
smooth map, provided its induced transformation has the stage evaluation formula
and the tangent bijection proved in the construction. -/
def TowerSmooth : Prop :=
  ∀ {k : Type u} [Field k] {F : ArtinFunctorModel.{u,w} k} {r : ℕ}
    (T : Tower F r)
    (hc : letI := quotientLocal T.limitIdeal ((T.limit_le 0).trans (T.below 0))
      IsAdicComplete (maximalIdeal (Series k r ⧸ T.limitIdeal)) (Series k r ⧸ T.limitIdeal))
    (τ : (representableModel.{u,w} (T.ring hc)).toFunctor ⟶ F.toFunctor),
    H1Model F → H2Model F →
    (∀ (A : LocalArtinAlgebra.{u,u} k) (a : CompleteLocalAlgebra.Hom (T.ring hc) A),
      ∃ (i : ℕ) (f : Hom (T.stage i) A), (T.projection i).postcomp f = a) →
    (∀ (A : LocalArtinAlgebra.{u,u} k) (i : ℕ) (f : Hom (T.stage i) A),
      τ.app A (ULift.up ((T.projection i).postcomp f)) = F.toFunctor.map f (T.element i)) →
    Function.Bijective ((τ.app (dualModel k)) :
      TangentModel (representableModel.{u,w} (T.ring hc)) → TangentModel F) →
    SmoothModel τ

end CommutativeAlgebraNotes.SchlessingerHullLiftingSpec
