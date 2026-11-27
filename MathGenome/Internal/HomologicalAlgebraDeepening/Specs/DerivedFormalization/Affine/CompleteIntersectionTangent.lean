import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.CompleteIntersectionConormal
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.DerivedHom
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace

open CategoryTheory Opposite

universe u z

namespace Specs.DerivedFormalization.Affine.CompleteIntersectionTangent

open _root_.DerivedFormalization _root_.DerivedFormalization.Affine
open CompleteIntersectionConormal
open CotangentComplex (ComparisonSystem oneObject)
open Tensor (ModuleTensor regular)
open DG.HomComplex (homComplex component)
open DG.Derived (homotopyCategory derivedCategory quotient)
open DG.DerivedKProjective (derivedCategoryInstance)
open _root_.CommutativeAlgebraNotes (MarkedDeformation)

namespace Marked
export Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace
  (B q jacobian DeformationClasses JacobianCokernel trivial)
end Marked

noncomputable section

variable {k : Type u} [Field k] [CharZero k] {s r : ℕ} (f : Fin r → Polynomial k s)

/-- Compare the ordinary quotient algebras using the classes of the same polynomials. -/
structure QuotientComparison where
  algebraIso : Quotient f ≃ₐ[k] Marked.B f
  polynomial (p : Polynomial k s) : algebraIso (quotientClass f p) = Marked.q f p
  cokernelIso : JacobianCokernel f ≃ₗ[k] Marked.JacobianCokernel f
  on_class (a : Fin r → Quotient f) :
    cokernelIso ((transposeJacobian f).range.mkQ a) =
      (Marked.jacobian f).range.mkQ (fun i => algebraIso (a i))

def QuotientComparisonExists : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {s r : ℕ} (f : Fin r → Polynomial k s),
    Nonempty (QuotientComparison f)

abbrev algebra := (quotientCDGA f).toCommDGAlgebra
abbrev category := oneObject (quotientCDGA f)
abbrev laws := DG.Derived.HomotopyCategoryLaws (category f)

variable {f} (h : laws f)

noncomputable local instance : Category (derivedCategory (category f) h) :=
  derivedCategoryInstance (category f) h

abbrev LocalizedCategory := derivedCategory (category f) h
abbrev localizedModule (M : (quotientCDGA f).Module) : LocalizedCategory h :=
  letI := homotopyCategory (category f) h
  (quotient (category f) h).obj M

abbrev localizedMap {M N : (quotientCDGA f).Module} (g : M ⟶ N) :
    localizedModule h M ⟶ localizedModule h N :=
  letI := homotopyCategory (category f) h
  (quotient (category f) h).map (CotangentComplex.moduleClass h g)

/-- Cohomology after localization, with its comparison on strict representatives. -/
structure DegreeOneCohomology where
  functor : LocalizedCategory h ⥤ ModuleCat.{u} k
  representative (M : (quotientCDGA f).Module) :
    functor.obj (localizedModule h M) ≅ (M.complex ()).homology 1
  naturality {M N : (quotientCDGA f).Module} (g : M ⟶ N) :
    functor.map (localizedMap h g) ≫ (representative N).hom =
      (representative M).hom ≫ HomologicalComplex.homologyMap (g.app ()) 1

abbrev forgetQuotient (f : Fin r → Polynomial k s) :=
  DG.OrdinaryComplex.restrictScalars k (Quotient f)

abbrev ordinaryCohomology (f : Fin r → Polynomial k s) :=
  (forgetQuotient f).obj ((conormalHom f).homology 1)

variable {h}

/-- Compare degree-one cohomology through the strict cochain model and its
isomorphism to the localized object. -/
noncomputable def cohomologyIso (H : DegreeOneCohomology h)
    {M : (quotientCDGA f).Module} {X : LocalizedCategory h}
    (a : X ≅ localizedModule h M) (b : (restriction f).obj (conormalHom f) ≅ M.complex ()) :
    H.functor.obj X ≅ ordinaryCohomology f :=
  H.functor.mapIso a ≪≫ H.representative M ≪≫
    (HomologicalComplex.homologyFunctor _ _ 1).mapIso b.symm ≪≫
    (ShortComplex.homologyFunctorIso (forgetQuotient f)).app ((conormalHom f).sc 1)

open Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace
  (LiftClasses TangentModule Coeff Corresponds presentation EvaluatesRelations)
open Specs.CommutativeAlgebraNotes.SquareZeroLiftTorsor (ActsByReduction liftClass)

/-- The deformation coordinates use the torsor on lifts with the marked
constant family as origin. -/
structure MarkedCoordinates (f : Fin r → Polynomial k s) where
  equivLifts : Marked.DeformationClasses.{u,z} f ≃ LiftClasses (k := k) (Marked.B f)
  action : AddTorsor (TangentModule f) (LiftClasses (k := k) (Marked.B f))
  epsilonCoordinates : Coeff (k := k) (Marked.B f) ≃ₗ[Marked.B f] Marked.B f
  relationCoordinates : TangentModule f ≃ₗ[Marked.B f] Marked.JacobianCokernel f
  equiv : Marked.DeformationClasses.{u,z} f ≃ Marked.JacobianCokernel f
  on_lift : ∀ D L, Corresponds D L →
    equivLifts (MarkedDeformation.classModel D) = liftClass L
  action_reduction : ActsByReduction (presentation f) action.toAddAction.toVAdd
  evaluation : EvaluatesRelations f epsilonCoordinates relationCoordinates
  pointed : ∀ X, equiv X = relationCoordinates
    (action.vsub (equivLifts X)
      (equivLifts (MarkedDeformation.classModel (Marked.trivial.{u,z} k (Marked.B f)))))

/-- A derived Hom on the stated localization agrees with the internal Hom
for every strict K-projective replacement. -/
def ComputesDerivedHom (F : (LocalizedCategory h)ᵒᵖ × LocalizedCategory h ⥤ LocalizedCategory h) : Prop :=
  ∀ {P M : (quotientCDGA f).Module} (p : P ⟶ M),
    DG.Module.quasiIsomorphism p → DG.KProjective.isKProjective P →
    ∀ N : (quotientCDGA f).Module,
      Nonempty (F.obj (op (localizedModule h M), localizedModule h N) ≅
        localizedModule h (DerivedHom.internalHom P N))

/-- The first cohomology of derived Hom from the cotangent complex is the
space of marked first-order deformations. Its coordinates on a cycle are
evaluation on the equation symbols, modulo the transposed Jacobian. -/
def TangentSpace : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {s r : ℕ} (f : Fin r → Polynomial k s),
    RingTheory.Sequence.IsRegular (Polynomial k s) (List.ofFn f) →
    ∃ (P : KoszulPresentation f) (O : P.relativeDifferentials)
      (T : ModuleTensor.{u,u} k) (h : laws f) (C : ComparisonSystem T (groundMap f) h)
      (E : ConormalComparison P O T) (H : DegreeOneCohomology h)
      (F : (LocalizedCategory h)ᵒᵖ × LocalizedCategory h ⥤ LocalizedCategory h),
      ComputesDerivedHom F ∧
      let M := (P.model O).module T
      let N := regular (algebra f)
      let X := F.obj (op C.derivedObject, localizedModule h N)
      ∃ (a : X ≅ localizedModule h (DerivedHom.internalHom M N))
        (b : (restriction f).obj (conormalHom f) ≅ (DerivedHom.internalHom M N).complex ())
        (J : QuotientComparison f) (I : CokernelComparison f) (G : MarkedCoordinates.{u,z} f),
        (∀ (m n : ℤ) (hmn : m + n = 0)
          (v : CochainComplex.HomComplex.Cochain (conormal f) (quotientStalk f) n)
          (x : Tensor.term M m),
          component (b.hom.f n v) () m 0 hmn x =
            (show (quotientCDGA f).complex.X 0 from v.v m 0 hmn (E.iso.hom.f m x))) ∧
        letI := G.equiv.addCommGroup
        letI := G.equiv.addEquiv.module k
        ∃ e : H.functor.obj X ≃ₗ[k] Marked.DeformationClasses.{u,z} f,
          e 0 = MarkedDeformation.classModel (Marked.trivial.{u,z} k (Marked.B f)) ∧
          ∀ v : (conormalHom f).cycles 1,
            G.equiv (e ((cohomologyIso H a b).inv ((conormalHom f).homologyπ 1 v))) =
              J.cokernelIso (I.iso ((conormalHom f).homologyπ 1 v))

end

end Specs.DerivedFormalization.Affine.CompleteIntersectionTangent
