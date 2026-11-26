import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Category.CommAlgCat.FiniteType
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RealAlbertGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.RelativeRank

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.F4RealCompletion

open LinearAlgebraicGroups.Arithmetic.AdelicGroups (PointsIn)
open RealAlbertGroups (HasAbsoluteTypeF4 NoncompactRealParabolicGeneration RealPointsConnected)
open ProjectiveRecurrence (parabolicRadicalPoints)
open IntegralModels (MatrixRealization)

/-- The actual closed matrix realization of an F₄ group at a real completion. -/
def Statement : Prop :=
  ∀ {F : Type u} [NontriviallyNormedField F] (e : F ≃+* ℝ), Isometry e →
    ∀ (G : AffineAlgebraicGroup F) (i : MatrixRealization G), HasAbsoluteTypeF4 G →
      ConnectedSpace (PointsIn i F) ∧
      (0 < RelativeRank.relativeRank G → ¬ CompactSpace (PointsIn i F)) ∧
      (¬ CompactSpace (PointsIn i F) →
        Dense (Subgroup.closure (G := PointsIn i F) (parabolicRadicalPoints G) :
          Set (PointsIn i F)))

/-- The local conclusions using the two frozen real-group propositions. -/
def ConditionalStatement : Prop :=
  NoncompactRealParabolicGeneration → RealPointsConnected → Statement.{u}

/-- Positive relative rank forces noncompactness in the matrix topology. -/
def PositiveRankNoncompact : Prop :=
  ∀ {F : Type u} [NontriviallyNormedField F]
    (G : AffineAlgebraicGroup F) (i : MatrixRealization G),
    GeometricRadicals.IsSemisimple G → 0 < RelativeRank.relativeRank G →
    ¬ CompactSpace (PointsIn i F)

/-- Scalar extension along the isometry to a universe lift of the real numbers
preserves the matrix point group and its topology. -/
def RealCompletionPointComparison : Prop :=
  ∀ {F : Type u} [NontriviallyNormedField F] (e : F ≃+* ℝ), Isometry e →
    ∀ (G : AffineAlgebraicGroup F) (i : MatrixRealization G),
      letI : Algebra F (ULift.{u} ℝ) := (e.trans ULift.ringEquiv.symm).toRingHom.toAlgebra
      let H := (groupBaseChange F (ULift.{u} ℝ)).obj G.val
      ∃ h : IsAffine H.X.left ∧ LocallyOfFiniteType H.X.hom ∧ QuasiCompact H.X.hom,
        ∃ j : MatrixRealization (⟨H, h⟩ : AffineAlgebraicGroup (ULift.{u} ℝ)),
          Nonempty (PointsIn j (ULift.{u} ℝ) ≃ₜ* PointsIn i F)

/-- A finite-type Hopf presentation of the original group has a small real
coordinate algebra. The real scalar map is induced by the given field equivalence. -/
def SmallRealCoordinates : Prop :=
  ∀ {F : Type u} [Field F] (e : F ≃+* ℝ) (G : AffineAlgebraicGroup F),
    ∃ (A : HopfAlgebraCategory F) (_ : Algebra.FiniteType F A),
      Nonempty (specGroup A ≅ G.val) ∧
      ∃ (P : FGAlgCatSkeleton ℝ) (r : P.eval.obj ≃+* A),
        r.toRingHom.comp (algebraMap ℝ P.eval.obj) =
          (algebraMap F A).comp e.symm.toRingHom

/-- The lifted test algebra with its scalar map from the isomorphic field. -/
noncomputable def liftTestAlgebraObj {F : Type u} [Field F] {K : Type} [Field K] (e : F ≃+* K)
    (R : TestAlgebra K) : TestAlgebra F :=
  let a : F →+* ULift.{u} R :=
    ULift.ringEquiv.symm.toRingHom.comp ((algebraMap K R).comp e.toRingHom)
  letI : Algebra F (ULift.{u} R) := a.toAlgebra
  CommAlgCat.of F (ULift.{u} R)

/-- Transport small test algebras to the universe of an isomorphic field. -/
noncomputable def liftTestAlgebra {F : Type u} [Field F] {K : Type} [Field K] (e : F ≃+* K) :
    TestAlgebra K ⥤ TestAlgebra F where
  obj := liftTestAlgebraObj e
  map {R S} f :=
    let A := liftTestAlgebraObj e R
    let B := liftTestAlgebraObj e S
    ConcreteCategory.ofHom (C := TestAlgebra F) (X := A) (Y := B)
      (@AlgHom.mk F A B _ _ _ A.algebra B.algebra
        ((ULift.ringEquiv.symm.toRingHom.comp f.hom.toRingHom).comp ULift.ringEquiv.toRingHom)
        (fun x => congrArg ULift.up (f.hom.commutes (e x))))
  map_id R := by
    apply CommAlgCat.hom_ext
    exact AlgHom.ext fun _ => rfl
  map_comp f g := by
    apply CommAlgCat.hom_ext
    exact AlgHom.ext fun _ => rfl

/-- The completion itself is the lift of the rational real test algebra. -/
noncomputable def realRationalTestAlgebraIso {F : Type u} [Field F] (e : F ≃+* ℝ) :
    CommAlgCat.of F F ≅ (liftTestAlgebra e).obj (CommAlgCat.of ℝ ℝ) := by
  let a : F ≃+* ULift.{u} ℝ := e.trans ULift.ringEquiv.symm
  letI : Algebra F (ULift.{u} ℝ) := a.toRingHom.toAlgebra
  let b : F ≃ₐ[F] ULift.{u} ℝ := AlgEquiv.ofRingEquiv (f := a) (fun _ => rfl)
  exact CommAlgCat.isoMk b

/-- A group over a real completion admits a real affine algebraic group
model whose points are identified on all real test algebras, with the
original matrix topology on the rational point group. For reductive groups
the point map carries parabolic radicals into parabolic radicals. -/
def SmallRealGroupPresentation : Prop :=
  ∀ {F : Type u} [NontriviallyNormedField F] (e : F ≃+* ℝ), Isometry e →
    ∀ (G : AffineAlgebraicGroup F) (i : MatrixRealization G),
    ∃ H : AffineAlgebraicGroup ℝ,
      (GeometricRadicals.IsSemisimple G → GeometricRadicals.IsSemisimple H) ∧
      ∃ p : ∀ R : TestAlgebra ℝ,
        ((groupPointsFunctor ℝ).obj H.val).obj R ≃*
          ((groupPointsFunctor F).obj G.val).obj ((liftTestAlgebra e).obj R),
        (∀ {R S : TestAlgebra ℝ} (f : R ⟶ S) (x : ((groupPointsFunctor ℝ).obj H.val).obj R),
          p S (((groupPointsFunctor ℝ).obj H.val).map f x) =
            ((groupPointsFunctor F).obj G.val).map ((liftTestAlgebra e).map f) (p R x)) ∧
        ∃ (j : MatrixRealization H) (f : PointsIn j ℝ ≃ₜ* PointsIn i F),
          (∀ x : PointsIn j ℝ,
            ((groupPointsFunctor F).obj G.val).map (realRationalTestAlgebraIso e).hom (f x) =
              p (CommAlgCat.of ℝ ℝ) x) ∧
          (GeometricRadicals.IsReductive G → GeometricRadicals.IsReductive H →
            f '' (parabolicRadicalPoints H : Set (PointsIn j ℝ)) ⊆ parabolicRadicalPoints G)

/-- In the local matrix group the parabolic-radical points are exactly the
points of the contracting subgroups of ground-field cocharacters. -/
def RadicalPointComparison : Prop :=
  ∀ {F : Type u} [NontriviallyNormedField F] (G : AffineAlgebraicGroup F),
    GeometricRadicals.IsReductive G →
      parabolicRadicalPoints G = ProjectiveRecurrence.cocharacterRadicalPoints G

end LinearAlgebraicGroups.Specs.Arithmetic.F4RealCompletion
