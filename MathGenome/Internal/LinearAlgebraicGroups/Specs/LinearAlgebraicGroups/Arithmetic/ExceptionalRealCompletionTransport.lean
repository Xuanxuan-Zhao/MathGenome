import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.BorelProper
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes

noncomputable section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory LieAlgebrasAndRepresentations

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalRealCompletionTransport

open LinearAlgebraicGroups.Arithmetic.AdelicGroups (PointsIn asMatrix)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition)
open AbsoluteDynkinTypes (HasDynkinType IsAbsolutelyAlmostSimple)
open AdjointRepresentation (GroupPoints)
open BorelProper (IsParabolic)
open CharacterDescent (Cocharacter)
open GeometricRadicals (GeometricGroup IsUnipotentRadical)
open IntegralModels (MatrixRealization)
open Pinning (AttachedDatum SplitBorelPair)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)

/-- Geometric Dynkin type on an attached datum of the actual geometric group. -/
def HasAbsoluteType {F : Type u} [Field F] (G : AffineAlgebraicGroup F)
    (t : FiniteDynkinType) : Prop :=
  ∃ (P : SplitBorelPair (AlgebraicClosure F)) (_ : P.G = GeometricGroup G)
    (D : AttachedDatum P),
    letI := D.comm
    HasDynkinType (RootData.integralCartan D.datum.rootDatum D.base) t

abbrev realTestAlgebra {F : Type u} [Field F] (e : F ≃+* ℝ) (R : CommAlgCat.{0} ℝ) :
    Algebra F (ULift.{u} R) :=
  ((ULift.ringEquiv.symm.toRingHom.comp (algebraMap ℝ R)).comp e.toRingHom).toAlgebra

/-- Real test algebras viewed over the completion by transporting scalars
along its ring equivalence with the reals. -/
abbrev realTestOver {F : Type u} [Field F] (e : F ≃+* ℝ) (R : CommAlgCat.{0} ℝ) :
    CommAlgCat.{u} F :=
  letI := realTestAlgebra e R
  CommAlgCat.of F (ULift.{u} R)

def realTestMap {F : Type u} [Field F] (e : F ≃+* ℝ) {R S : CommAlgCat.{0} ℝ}
    (f : R ⟶ S) : realTestOver e R ⟶ realTestOver e S := by
  letI := realTestAlgebra e R
  letI := realTestAlgebra e S
  exact CommAlgCat.ofHom
    ({ toRingHom := f.hom.toRingHom.ulift
       commutes' := fun x => congrArg ULift.up (f.hom.commutes (e x)) } :
      ULift.{u} R →ₐ[F] ULift.{u} S)

abbrev realTest : CommAlgCat.{0} ℝ := CommAlgCat.of ℝ ℝ

/-- The transported real field, as a test algebra, identifies with the
completion itself by the inverse of the same ring equivalence. -/
def completionTestMap {F : Type u} [Field F] (e : F ≃+* ℝ) :
    realTestOver e realTest ⟶ CommAlgCat.of F F := by
  letI := realTestAlgebra e realTest
  exact CommAlgCat.ofHom
    ({ toRingHom := e.symm.toRingHom.comp ULift.ringEquiv.toRingHom
       commutes' := fun x => by
         change e.symm (e x) = x
         exact e.symm_apply_apply x } : ULift.{u} ℝ →ₐ[F] F)

/-- Images in the group of rational points of the unipotent radicals of
rational parabolic subgroups. -/
def parabolicRadicalPoints {F : Type u} [Field F] (G : AffineAlgebraicGroup F) :
    Set (GroupPoints G.val (CommAlgCat.of F F)) :=
  {g | ∃ (P : ClosedSubgroup G.val) (_ : IsParabolic G P) (U : ClosedSubgroup P.group)
      (_ : IsUnipotentRadical (closedSubgroupAlgebraicGroup P) U)
      (x : GroupPoints U.group (CommAlgCat.of F F)),
      ((groupPointsFunctor F).map (U.inclusion ≫ P.inclusion)).app (CommAlgCat.of F F) x = g}

/-- Images in the group of rational points of the cocharacter contracting
subgroups. -/
def cocharacterRadicalPoints {F : Type u} [Field F] (G : AffineAlgebraicGroup F) :
    Set (GroupPoints G.val (CommAlgCat.of F F)) :=
  {g | ∃ (c : Cocharacter G.val) (L : LimitDecomposition c),
    g ∈ (((groupPointsFunctor F).map L.contracting.inclusion).app (CommAlgCat.of F F)).hom.range}

/-- Transport the actual real completion of the given matrix group to
a real model. The comparison on points is the evaluation of a natural
multiplicative comparison on real test algebras. -/
def RealCompletionTransport : Prop :=
  ∀ {K : Type u} [Field K] [NumberField K] (G : AffineAlgebraicGroup K)
    (i : MatrixRealization G),
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G →
    ∀ (t : FiniteDynkinType), (t = .E6 ∨ t = .E7 ∨ t = .E8) → HasAbsoluteType G t →
    ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
      let F := w.Completion
      let e := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw
      let Gv := baseChangedAlgebraicGroup F G
      ∃ (H : AffineAlgebraicGroup ℝ) (j : MatrixRealization H)
        (η : ∀ R : CommAlgCat.{0} ℝ, GroupPoints H.val R ≃*
          GroupPoints Gv.val (realTestOver e R))
        (q : PointsIn j ℝ ≃ₜ* PointsIn i F) (hs : j.size = i.size),
        IsAbsolutelyAlmostSimple H ∧ GeometricallySimplyConnected H ∧ HasAbsoluteType H t ∧
        (∀ {R S : CommAlgCat.{0} ℝ} (f : R ⟶ S) (p : GroupPoints H.val R),
          η S (((groupPointsFunctor ℝ).obj H.val).map f p) =
            ((groupPointsFunctor F).obj Gv.val).map (realTestMap e f) (η R p)) ∧
        (∀ p : PointsIn j ℝ,
          (show Points G.val.X (CommAlgCat.of K F) from q p).left =
            (baseChangePoint K F G.val.X (CommAlgCat.of F F)
              (((groupPointsFunctor F).obj Gv.val).map (completionTestMap e) (η realTest p))).left) ∧
        (∀ (p : PointsIn j ℝ) (a b : Fin j.size),
          asMatrix j ℝ p (ULift.up a) (ULift.up b) =
            e (asMatrix i F (q p) (ULift.up (Fin.cast hs a)) (ULift.up (Fin.cast hs b)))) ∧
        (let φ := η realTest
         let ev := ((groupPointsFunctor F).obj Gv.val).map (completionTestMap e)
         ∀ (p : GroupPoints H.val realTest),
           (p ∈ Subgroup.closure (parabolicRadicalPoints H) ↔
             ev (φ p) ∈ Subgroup.closure (parabolicRadicalPoints Gv)) ∧
           (p ∈ Subgroup.closure (cocharacterRadicalPoints H) ↔
             ev (φ p) ∈ Subgroup.closure (cocharacterRadicalPoints Gv)))

end LinearAlgebraicGroups.Specs.ExceptionalRealCompletionTransport
