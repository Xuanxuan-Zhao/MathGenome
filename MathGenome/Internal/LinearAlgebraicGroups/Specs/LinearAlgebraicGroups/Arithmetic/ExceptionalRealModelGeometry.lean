import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes

noncomputable section

set_option autoImplicit false

open CategoryTheory LieAlgebrasAndRepresentations

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalRealModelGeometry

open AbsoluteDynkinTypes (HasDynkinType IsAbsolutelyAlmostSimple)
open AdjointRepresentation (GroupPoints)
open GeometricRadicals (GeometricGroup)
open Pinning (AttachedDatum SplitBorelPair)
open SimplyConnectedLattice (GeometricallySimplyConnected)

/-- The Cartan type of an attached based datum on the geometric group. -/
def HasAbsoluteType {F : Type u} [Field F] (G : AffineAlgebraicGroup F)
    (t : FiniteDynkinType) : Prop :=
  ∃ (P : SplitBorelPair (AlgebraicClosure F)) (_ : P.G = GeometricGroup G)
    (D : AttachedDatum P),
    letI := D.comm
    HasDynkinType (RootData.integralCartan D.datum.rootDatum D.base) t

abbrev realTestAlgebra {F : Type u} [Field F] (e : F ≃+* ℝ) (R : CommAlgCat.{0} ℝ) :
    Algebra F (ULift.{u} R) :=
  ((ULift.ringEquiv.symm.toRingHom.comp (algebraMap ℝ R)).comp e.toRingHom).toAlgebra

/-- Lift a small real test algebra and transport its scalar map along the field equivalence. -/
abbrev realTestOver {F : Type u} [Field F] (e : F ≃+* ℝ) (R : CommAlgCat.{0} ℝ) :
    TestAlgebra F :=
  letI := realTestAlgebra e R
  CommAlgCat.of F (ULift.{u} R)

/-- The lift of a real algebra morphism for the transported scalar structures. -/
def realTestMap {F : Type u} [Field F] (e : F ≃+* ℝ) {R S : CommAlgCat.{0} ℝ}
    (f : R ⟶ S) : realTestOver e R ⟶ realTestOver e S := by
  letI := realTestAlgebra e R
  letI := realTestAlgebra e S
  exact CommAlgCat.ofHom
    ({ toRingHom := f.hom.toRingHom.ulift
       commutes' := fun x => congrArg ULift.up (f.hom.commutes (e x)) } :
      ULift.{u} R →ₐ[F] ULift.{u} S)

/-- A natural multiplicative comparison on all real test algebras transports the
three geometric predicates to the real model, preserving the chosen exceptional type. -/
def RealModelGeometry : Prop :=
  ∀ {F : Type u} [Field F] (e : F ≃+* ℝ) (G : AffineAlgebraicGroup F)
    (H : AffineAlgebraicGroup ℝ)
    (η : ∀ R : CommAlgCat.{0} ℝ, GroupPoints H.val R ≃*
      GroupPoints G.val (realTestOver e R)),
    (∀ {R S : CommAlgCat.{0} ℝ} (f : R ⟶ S) (p : GroupPoints H.val R),
      η S (((groupPointsFunctor ℝ).obj H.val).map f p) =
        ((groupPointsFunctor F).obj G.val).map (realTestMap e f) (η R p)) →
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G →
    ∀ t : FiniteDynkinType, (t = .E6 ∨ t = .E7 ∨ t = .E8) → HasAbsoluteType G t →
      IsAbsolutelyAlmostSimple H ∧ GeometricallySimplyConnected H ∧ HasAbsoluteType H t

end LinearAlgebraicGroups.Specs.ExceptionalRealModelGeometry
