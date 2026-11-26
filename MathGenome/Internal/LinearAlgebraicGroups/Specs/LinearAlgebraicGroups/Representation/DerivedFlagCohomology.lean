import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CentralDerived
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagCohomology

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace LinearAlgebraicGroups.Specs.DerivedFlagCohomology

open FlagLineBundle (OppositeBorelPair BorelProjection)
open FlagCohomology (FlagKernelPair flagLineData flagCohomology IsCohomologyMap)
open GeometricRadicals (IsSemisimple)
open SchemeDerivedGroup (IsDerivedSubgroup)
open Unipotent (closedSubgroupAlgebraicGroup)
open QuotientEmbedding (Presentation)
open CharacterDescent (Character)

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

/-- The marked subgroups of the derived group are the scheme intersections
with the marked subgroups of the original group. -/
structure Restriction (D : ClosedSubgroup G.val) (P : OppositeBorelPair G)
    (P' : OppositeBorelPair (closedSubgroupAlgebraicGroup D)) where
  torus : P'.torus.group ⟶ P.torus.group
  positive : P'.positive.group ⟶ P.positive.group
  negative : P'.negative.group ⟶ P.negative.group
  torusPullback : IsPullback P'.torus.inclusion.hom.hom torus.hom.hom
    D.inclusion.hom.hom P.torus.inclusion.hom.hom
  positivePullback : IsPullback P'.positive.inclusion.hom.hom positive.hom.hom
    D.inclusion.hom.hom P.positive.inclusion.hom.hom
  negativePullback : IsPullback P'.negative.inclusion.hom.hom negative.hom.hom
    D.inclusion.hom.hom P.negative.inclusion.hom.hom

/-- The comparison uses the map induced by inclusion on right fppf quotients
and the pullback of covariant functions under that inclusion. -/
def Compares {D : ClosedSubgroup G.val} {P : OppositeBorelPair G}
    {P' : OppositeBorelPair (closedSubgroupAlgebraicGroup D)}
    (r : Restriction D P P')
    (Q : Presentation P.negative) (p : BorelProjection P) (χ : Character P.torus.group)
    (h : FlagKernelPair Q)
    (Q' : Presentation P'.negative) (p' : BorelProjection P') (h' : FlagKernelPair Q') : Prop :=
  let χ' : Character P'.torus.group := r.torus ≫ χ
  let F := flagLineData Q p χ h
  let F' := flagLineData Q' p' χ' h'
  ∃ (e : Q'.scheme ≅ Q.scheme)
    (w : Q'.projection ≫ e.hom = D.inclusion.hom.hom ≫ Q.projection)
    (α : F.sheaf ⟶ (Scheme.Modules.pushforward e.hom.left).obj F'.sheaf),
    Q'.quotientIso.inv ≫ rightQuotientMap D.inclusion r.negative
        (Grp.hom_ext _ _ r.negativePullback.w) ≫ Q.quotientIso.hom =
      (fppfOver k).uliftYoneda.map e.hom ∧
    F.IsPullbackMap F' e.hom.left D.inclusion.hom.hom.left (congrArg Over.Hom.left w.symm) α ∧
    IsIso α ∧
    ∀ n : ℕ, ∃ c : flagCohomology Q p χ h n ≅ flagCohomology Q' p' χ' h' n,
      IsCohomologyMap (RingHom.id k) e.hom.left (by simp) α n
        (c.hom ≫ (ModuleCat.restrictScalarsId'App (RingHom.id k) rfl _).inv)

/-- Over an algebraically closed field the marked derived flag gives the same
cohomology, in every degree, for the restricted character. -/
def DerivedFlagComparison : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (P : OppositeBorelPair G),
    ∃ (D : ClosedSubgroup G.val) (P' : OppositeBorelPair (closedSubgroupAlgebraicGroup D))
      (r : Restriction D P P'),
      IsDerivedSubgroup D ∧ IsSemisimple (closedSubgroupAlgebraicGroup D) ∧
      Nonempty (BorelProjection P') ∧ Nonempty (Presentation P'.negative) ∧
      ∀ (Q : Presentation P.negative) (p : BorelProjection P) (χ : Character P.torus.group)
        (h : FlagKernelPair Q)
        (Q' : Presentation P'.negative) (p' : BorelProjection P') (h' : FlagKernelPair Q'),
        Compares r Q p χ h Q' p' h'

end LinearAlgebraicGroups.Specs.DerivedFlagCohomology
