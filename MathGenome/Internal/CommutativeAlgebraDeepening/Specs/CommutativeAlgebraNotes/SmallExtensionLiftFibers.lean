import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SchlessingerSplitCorrections
import Mathlib.Algebra.Torsor.Defs

/-! Lift fibres and their tangent torsors in the proof of Theorem 6.10. -/

universe u w

namespace CommutativeAlgebraNotes.SmallExtensionLiftFibersSpec

open CategoryTheory LocalArtinAlgebra SchlessingerConditionsSpec
  SchlessingerTangentVectorSpaceSpec SchlessingerSplitCorrectionsSpec
open scoped TensorProduct

attribute [local instance] extensionKernelFinite

variable {k : Type u} [Field k] {B A : LocalArtinAlgebra.{u,u} k}

abbrev LiftFiber (F : ArtinFunctorModel.{u,w} k) (g : Hom B A) (x : F.toFunctor.obj A) :=
  {y : F.toFunctor.obj B // onHom F g y = x}

/-- The common reduction of both components is the image along the first projection. -/
abbrev PullbackFiber (F : ArtinFunctorModel.{u,w} k) (g : Hom B A) (x : F.toFunctor.obj A) :=
  {p : F.toFunctor.obj (pullbackModel g g) // onHom F (g.comp (pullbackFstModel g g)) p = x}

abbrev LiftTensor (F : ArtinFunctorModel.{u,w} k) (g : Hom B A) (laws : VectorLaws F) :=
  letI := tangentAddCommGroupModel F laws
  letI := tangentModuleModel F laws
  TangentModel F ⊗[k] ExtensionKernel g

/-- The difference morphism on the double fibre product, in square-zero coordinates. -/
def DifferenceFormula (g : Hom B A)
    (d : Hom (pullbackModel g g) (splitModel k (ExtensionKernel g))) : Prop :=
  ∀ p : pullbackModel g g,
    (d.val p).fst = B.residue p.val.1 ∧ ((d.val p).snd : B) = p.val.2 - p.val.1

/-- Intrinsic coordinates for the lift fibre. These data also make sense when it is empty. -/
structure LiftFiberCoordinates (F : ArtinFunctorModel.{u,w} k) (g : Hom B A)
    (x : F.toFunctor.obj A) (laws : VectorLaws F)
    (c : SplitTensorComparison F laws (ExtensionKernel g)) where
  pairs : PullbackFiber F g x ≃ LiftFiber F g x × LiftFiber F g x
  pairs_apply : ∀ p,
    ((pairs p).1.val, (pairs p).2.val) =
      (onHom F (pullbackFstModel g g) p.val, onHom F (pullbackSndModel g g) p.val)
  differenceHom : Hom (pullbackModel g g) (splitModel k (ExtensionKernel g))
  differenceFormula : DifferenceFormula g differenceHom
  coordinates : LiftFiber F g x → LiftFiber F g x ≃ LiftTensor F g laws
  coordinates_apply : ∀ y z,
    coordinates y z = c.equiv (onHom F differenceHom (pairs.symm (y, z)).val)
  cocycle :
    letI := tangentAddCommGroupModel F laws
    letI := tangentModuleModel F laws
    ∀ y z t, coordinates y z + coordinates z t = coordinates y t

/-- Translation by a tensor is the unique lift with that difference from the given lift. -/
def LiftFiberCoordinates.translate
    {F : ArtinFunctorModel.{u,w} k} {g : Hom B A} {x : F.toFunctor.obj A}
    {laws : VectorLaws F} {c : SplitTensorComparison F laws (ExtensionKernel g)}
    (D : LiftFiberCoordinates F g x laws c) (θ : LiftTensor F g laws) (y : LiftFiber F g x) :
    LiftFiber F g x :=
  (D.coordinates y).symm θ

/-- A natural transformation maps lifts to lifts over the image of the fixed base element. -/
def onLiftFiber {F G : ArtinFunctorModel.{u,w} k} (τ : F.toFunctor ⟶ G.toFunctor)
    {g : Hom B A} {x : F.toFunctor.obj A} (y : LiftFiber F g x) :
    LiftFiber G g (τ.app A x) :=
  ⟨τ.app B y.val, (ConcreteCategory.congr_hom (τ.naturality g) y.val).symm.trans
    (congrArg (τ.app A) y.property)⟩

def CoordinatesStatement : Prop :=
  ∀ {k : Type u} [Field k] (F : ArtinFunctorModel.{u,w} k), H1Model F → H2Model F → H4Model F →
    ∀ {B A : LocalArtinAlgebra.{u,u} k} (g : Hom B A), SmallExtensionModel g →
    ∀ (x : F.toFunctor.obj A) (laws : VectorLaws F)
      (c : SplitTensorComparison F laws (ExtensionKernel g)),
      Nonempty (LiftFiberCoordinates F g x laws c)

def TorsorStatement : Prop :=
  ∀ {k : Type u} [Field k] (F : ArtinFunctorModel.{u,w} k), H1Model F → H2Model F → H4Model F →
    ∀ {B A : LocalArtinAlgebra.{u,u} k} (g : Hom B A), SmallExtensionModel g →
    ∀ x : F.toFunctor.obj A, Nonempty (LiftFiber F g x) →
    ∃ (laws : VectorLaws F) (c : SplitTensorComparison F laws (ExtensionKernel g))
      (D : LiftFiberCoordinates F g x laws c),
      letI := tangentAddCommGroupModel F laws
      letI := tangentModuleModel F laws
      ∃ t : AddTorsor (LiftTensor F g laws) (LiftFiber F g x),
        (∀ θ y, @VAdd.vadd _ _ t.toVAdd θ y = D.translate θ y) ∧
        (∀ y z, @VSub.vsub _ _ t.toVSub z y = D.coordinates y z)

def NaturalityStatement : Prop :=
  ∀ {k : Type u} [Field k] {F G : ArtinFunctorModel.{u,w} k}
    (τ : F.toFunctor ⟶ G.toFunctor) {B A : LocalArtinAlgebra.{u,u} k}
    {g : Hom B A} {x : F.toFunctor.obj A}
    {lawsF : VectorLaws F} {lawsG : VectorLaws G}
    {cF : SplitTensorComparison F lawsF (ExtensionKernel g)}
    {cG : SplitTensorComparison G lawsG (ExtensionKernel g)}
    (DF : LiftFiberCoordinates F g x lawsF cF)
    (DG : LiftFiberCoordinates G g (τ.app A x) lawsG cG),
    letI := tangentAddCommGroupModel F lawsF
    letI := tangentModuleModel F lawsF
    letI := tangentAddCommGroupModel G lawsG
    letI := tangentModuleModel G lawsG
    ∀ (l : TangentModel F →ₗ[k] TangentModel G),
      (∀ t, l t = τ.app (dualModel k) t) →
      (∀ y z, DG.coordinates (onLiftFiber τ y) (onLiftFiber τ z) =
        TensorProduct.map l LinearMap.id (DF.coordinates y z)) ∧
      (∀ θ y, onLiftFiber τ (DF.translate θ y) =
        DG.translate (TensorProduct.map l LinearMap.id θ) (onLiftFiber τ y))

end CommutativeAlgebraNotes.SmallExtensionLiftFibersSpec
