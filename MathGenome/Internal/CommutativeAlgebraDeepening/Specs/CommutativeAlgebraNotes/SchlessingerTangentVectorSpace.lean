import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SchlessingerConditions
import Mathlib.LinearAlgebra.Contraction
import Mathlib.Algebra.Module.TransferInstance
import Batteries.Tactic.OpenPrivate

/-! Independent models for the tangent operations and split-algebra comparison. -/

universe u w

namespace CommutativeAlgebraNotes.SchlessingerTangentVectorSpaceSpec

open CategoryTheory LocalArtinAlgebra SchlessingerConditionsSpec
open scoped TensorProduct

variable {k : Type u} [Field k]

section Maps

variable {I J : Type u} [AddCommGroup I] [Module k I] [Module.Finite k I]
  [AddCommGroup J] [Module k J] [Module.Finite k J]

/-- The map of split square-zero algebras induced by a linear map of the ideals. -/
def splitMapModel (f : I →ₗ[k] J) : Hom (splitModel k I) (splitModel k J) := by
  letI : Module kᵐᵒᵖ I := splitOppositeModule k I
  letI : Module kᵐᵒᵖ J := splitOppositeModule k J
  letI : IsCentralScalar k I := ⟨fun _ _ => rfl⟩
  letI : IsCentralScalar k J := ⟨fun _ _ => rfl⟩
  refine ⟨TrivSqZeroExt.map f, ⟨fun x hx => ?_⟩⟩
  have hy := (TrivSqZeroExt.isUnit_iff_isUnit_fst (x := TrivSqZeroExt.map f x)).mp hx
  have hfst : (TrivSqZeroExt.map f x).fst = x.fst := TrivSqZeroExt.fst_map f x
  exact TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (hfst ▸ hy)

end Maps

abbrev SplitValue (F : ArtinFunctorModel.{u,w} k) (I : Type u)
    [AddCommGroup I] [Module k I] [Module.Finite k I] :=
  F.toFunctor.obj (splitModel k I)

/-- Evaluation of the set-valued functor on a morphism. -/
abbrev onHom (F : ArtinFunctorModel.{u,w} k) {A B : LocalArtinAlgebra.{u,u} k}
    (f : Hom A B) : F.toFunctor.obj A → F.toFunctor.obj B := F.toFunctor.map f

abbrev onLinear (F : ArtinFunctorModel.{u,w} k)
    {I J : Type u} [AddCommGroup I] [Module k I] [Module.Finite k I]
    [AddCommGroup J] [Module k J] [Module.Finite k J] (f : I →ₗ[k] J) :
    SplitValue F I → SplitValue F J := onHom F (splitMapModel f)

open private splitWithActions from MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.LocalArtinAlgebras in
/-- On the field itself the two right actions agree by commutativity. -/
theorem split_eq_dual (k : Type u) [Field k] : splitModel k k = dualModel k := by
  have hm : splitOppositeModule k k = Semiring.toOppositeModule :=
    Module.ext' _ _ fun r a => mul_comm r.unop a
  have aux (P Q : Module kᵐᵒᵖ k) (h : P = Q)
      (hP : letI := P; IsCentralScalar k k) (hQ : letI := Q; IsCentralScalar k k) :
      (letI := P; letI := hP; splitWithActions k k) =
        (letI := Q; letI := hQ; splitWithActions k k) := by
    subst Q
    rfl
  exact aux _ _ hm _ _

private theorem eqToHom_apply_heq {A B : LocalArtinAlgebra.{u,u} k}
    (h : A = B) (a : A) : HEq ((show Hom A B from eqToHom h).val a) a := by
  cases h
  rfl

theorem split_eq_dual_apply (x : splitModel k k) :
    ((show Hom (splitModel k k) (dualModel k) from eqToHom (split_eq_dual k)).val x :
      TrivSqZeroExt k k) = x :=
  eq_of_heq (eqToHom_apply_heq (split_eq_dual k) x)

/-- The coordinate-preserving identification of the split line with the dual numbers. -/
def tangentIdentification (F : ArtinFunctorModel.{u,w} k) :
    SplitValue F k ≃ TangentModel F :=
  (F.toFunctor.mapIso (eqToIso (split_eq_dual k))).toEquiv

/-- The structure map from the field object. -/
def fromFieldModel (A : LocalArtinAlgebra.{u,u} k) : Hom (fieldModel k) A :=
  ⟨Algebra.ofId k A, ⟨fun c hc => by
    have h := hc.map A.residue
    change IsUnit (A.residue (algebraMap k A c)) at h
    simpa only [A.residue_algebraMap] using h⟩⟩

abbrev pointedValue (F : ArtinFunctorModel.{u,w} k) (A : LocalArtinAlgebra.{u,u} k) :
    F.toFunctor.obj A := onHom F (fromFieldModel A) default

def tangentPair (F : ArtinFunctorModel.{u,w} k) :
    SplitValue F (k × k) → SplitValue F k × SplitValue F k :=
  fun x => (onLinear F (LinearMap.fst k k k) x, onLinear F (LinearMap.snd k k k) x)

def addMap : k × k →ₗ[k] k := LinearMap.fst k k k + LinearMap.snd k k k

def scaleMap (a : k) : k →ₗ[k] k := a • LinearMap.id

def tangentZero (F : ArtinFunctorModel.{u,w} k) : SplitValue F k :=
  pointedValue F (splitModel k k)

noncomputable def tangentAdd (F : ArtinFunctorModel.{u,w} k) (x y : SplitValue F k) : SplitValue F k :=
  haveI : Nonempty (SplitValue F (k × k)) := ⟨pointedValue F (splitModel k (k × k))⟩
  onLinear F addMap (Function.invFun (tangentPair F) (x, y))

def tangentScale (F : ArtinFunctorModel.{u,w} k) (a : k) (x : SplitValue F k) : SplitValue F k :=
  onLinear F (scaleMap a) x

/-- The vector-space identities for the operations prescribed by the split algebra maps. -/
structure VectorLaws (F : ArtinFunctorModel.{u,w} k) : Prop where
  add_assoc (x y z : SplitValue F k) :
    tangentAdd F (tangentAdd F x y) z = tangentAdd F x (tangentAdd F y z)
  add_comm (x y : SplitValue F k) : tangentAdd F x y = tangentAdd F y x
  add_zero (x : SplitValue F k) : tangentAdd F x (tangentZero F) = x
  neg_add_cancel (x : SplitValue F k) :
    tangentAdd F (tangentScale F (-1) x) x = tangentZero F
  one_smul (x : SplitValue F k) : tangentScale F 1 x = x
  mul_smul (a b : k) (x : SplitValue F k) :
    tangentScale F (a * b) x = tangentScale F a (tangentScale F b x)
  smul_zero (a : k) : tangentScale F a (tangentZero F) = tangentZero F
  smul_add (a : k) (x y : SplitValue F k) :
    tangentScale F a (tangentAdd F x y) = tangentAdd F (tangentScale F a x) (tangentScale F a y)
  zero_smul (x : SplitValue F k) : tangentScale F 0 x = tangentZero F
  add_smul (a b : k) (x : SplitValue F k) :
    tangentScale F (a + b) x = tangentAdd F (tangentScale F a x) (tangentScale F b x)

noncomputable abbrev splitAddCommGroupModel (F : ArtinFunctorModel.{u,w} k)
    (laws : VectorLaws F) : AddCommGroup (SplitValue F k) where
  add := tangentAdd F
  zero := tangentZero F
  neg := tangentScale F (-1)
  add_assoc := laws.add_assoc
  add_comm := laws.add_comm
  add_zero := laws.add_zero
  zero_add x := (laws.add_comm _ _).trans (laws.add_zero x)
  neg_add_cancel := laws.neg_add_cancel
  nsmul := @nsmulRec _ ⟨tangentZero F⟩ ⟨tangentAdd F⟩
  zsmul := @zsmulRec _ ⟨tangentZero F⟩ ⟨tangentAdd F⟩ ⟨tangentScale F (-1)⟩
    (@nsmulRec _ ⟨tangentZero F⟩ ⟨tangentAdd F⟩)

noncomputable abbrev splitModuleModel (F : ArtinFunctorModel.{u,w} k) (laws : VectorLaws F) :
    letI := splitAddCommGroupModel F laws
    Module k (SplitValue F k) :=
  letI := splitAddCommGroupModel F laws
  { smul := tangentScale F
    one_smul := laws.one_smul
    mul_smul := laws.mul_smul
    smul_zero := laws.smul_zero
    smul_add := laws.smul_add
    zero_smul := laws.zero_smul
    add_smul := laws.add_smul }

noncomputable abbrev tangentAddCommGroupModel (F : ArtinFunctorModel.{u,w} k)
    (laws : VectorLaws F) : AddCommGroup (TangentModel F) :=
  letI := splitAddCommGroupModel F laws
  (tangentIdentification F).symm.addCommGroup

noncomputable def tangentToSplitAddEquiv (F : ArtinFunctorModel.{u,w} k) (laws : VectorLaws F) :
    letI := splitAddCommGroupModel F laws
    letI := tangentAddCommGroupModel F laws
    TangentModel F ≃+ SplitValue F k :=
  letI := splitAddCommGroupModel F laws
  letI := tangentAddCommGroupModel F laws
  { (tangentIdentification F).symm with
    map_add' := fun _ _ => (tangentIdentification F).symm_apply_apply _ }

noncomputable abbrev tangentModuleModel (F : ArtinFunctorModel.{u,w} k) (laws : VectorLaws F) :
    letI := tangentAddCommGroupModel F laws
    Module k (TangentModel F) :=
  letI := splitAddCommGroupModel F laws
  letI := splitModuleModel F laws
  letI := tangentAddCommGroupModel F laws
  (tangentToSplitAddEquiv F laws).module k

/-- H3 is finite generation over the field for the canonical tangent operations. -/
def H3Model (F : ArtinFunctorModel.{u,w} k) : Prop :=
  ∃ laws : VectorLaws F,
    letI := tangentAddCommGroupModel F laws
    letI := tangentModuleModel F laws
    Module.Finite k (TangentModel F)

def VectorLawsStatement : Prop :=
  ∀ {k : Type u} [Field k] (F : ArtinFunctorModel.{u,w} k), H2Model F → VectorLaws F


section Contraction

variable {T : Type (max u w)} [AddCommGroup T] [Module k T]
variable {I : Type u} [AddCommGroup I] [Module k I] [Module.Finite k I]

/-- A tensor acts on covectors by contracting its second factor. -/
noncomputable def tensorContraction : T ⊗[k] I ≃ₗ[k] Module.Dual k I →ₗ[k] T :=
  (TensorProduct.comm k T I).trans
    ((TensorProduct.congr (Module.evalEquiv k I) (LinearEquiv.refl k T)).trans
      (dualTensorHomEquiv k (Module.Dual k I) T))

@[simp] theorem tensorContraction_tmul (t : T) (i : I) (l : Module.Dual k I) :
    tensorContraction (t ⊗ₜ[k] i) l = l i • t := by
  simp [tensorContraction]

end Contraction

/-- The comparison with tensors is characterized without a choice of basis.
Pushing an element forward along a covector agrees with contracting its tensor. -/
structure SplitTensorComparison (F : ArtinFunctorModel.{u,w} k) (laws : VectorLaws F)
    (I : Type u) [AddCommGroup I] [Module k I] [Module.Finite k I] where
  equiv :
    letI := tangentAddCommGroupModel F laws
    letI := tangentModuleModel F laws
    SplitValue F I ≃ TangentModel F ⊗[k] I
  contract :
    letI := tangentAddCommGroupModel F laws
    letI := tangentModuleModel F laws
    ∀ (x : SplitValue F I) (l : Module.Dual k I),
      tensorContraction (equiv x) l = tangentIdentification F (onLinear F l x)

abbrev onNatural (F G : ArtinFunctorModel.{u,w} k) (τ : F.toFunctor ⟶ G.toFunctor)
    (A : LocalArtinAlgebra.{u,u} k) : F.toFunctor.obj A → G.toFunctor.obj A := τ.app A

def SplitTensorStatement : Prop :=
  ∀ {k : Type u} [Field k] (F : ArtinFunctorModel.{u,w} k), H2Model F →
    ∀ (laws : VectorLaws F) (I : Type u) [AddCommGroup I] [Module k I] [Module.Finite k I],
      Nonempty (SplitTensorComparison F laws I)

def TensorPureFormula : Prop :=
  ∀ {k : Type u} [Field k] (F : ArtinFunctorModel.{u,w} k) (laws : VectorLaws F)
    {I : Type u} [AddCommGroup I] [Module k I] [Module.Finite k I]
    (e : SplitTensorComparison F laws I) (t : TangentModel F) (i : I),
    letI := tangentAddCommGroupModel F laws
    letI := tangentModuleModel F laws
    e.equiv.symm (t ⊗ₜ[k] i) =
      onLinear F (LinearMap.toSpanSingleton k I i) ((tangentIdentification F).symm t)

def TensorNaturalityInIdeal : Prop :=
  ∀ {k : Type u} [Field k] (F : ArtinFunctorModel.{u,w} k) (laws : VectorLaws F)
    {I J : Type u} [AddCommGroup I] [Module k I] [Module.Finite k I]
    [AddCommGroup J] [Module k J] [Module.Finite k J]
    (eI : SplitTensorComparison F laws I) (eJ : SplitTensorComparison F laws J)
    (f : I →ₗ[k] J) (x : SplitValue F I),
    letI := tangentAddCommGroupModel F laws
    letI := tangentModuleModel F laws
    eJ.equiv (onLinear F f x) = TensorProduct.map LinearMap.id f (eI.equiv x)

def TangentMapStatement : Prop :=
  ∀ {k : Type u} [Field k] (F G : ArtinFunctorModel.{u,w} k) (τ : F.toFunctor ⟶ G.toFunctor)
    (_hF : H2Model F) (_hG : H2Model G) (lawsF : VectorLaws F) (lawsG : VectorLaws G),
    letI := tangentAddCommGroupModel F lawsF
    letI := tangentModuleModel F lawsF
    letI := tangentAddCommGroupModel G lawsG
    letI := tangentModuleModel G lawsG
    ∃ g : TangentModel F →ₗ[k] TangentModel G,
      ∀ t, g t = onNatural F G τ (dualModel k) t

def TensorNaturalityInFunctor : Prop :=
  ∀ {k : Type u} [Field k] (F G : ArtinFunctorModel.{u,w} k) (τ : F.toFunctor ⟶ G.toFunctor)
    (lawsF : VectorLaws F) (lawsG : VectorLaws G)
    {I : Type u} [AddCommGroup I] [Module k I] [Module.Finite k I]
    (eF : SplitTensorComparison F lawsF I) (eG : SplitTensorComparison G lawsG I),
    letI := tangentAddCommGroupModel F lawsF
    letI := tangentModuleModel F lawsF
    letI := tangentAddCommGroupModel G lawsG
    letI := tangentModuleModel G lawsG
    ∀ (g : TangentModel F →ₗ[k] TangentModel G),
    (∀ t, g t = onNatural F G τ (dualModel k) t) →
    ∀ x : SplitValue F I,
      eG.equiv (onNatural F G τ (splitModel k I) x) =
        TensorProduct.map g LinearMap.id (eF.equiv x)

def H3Finite : Prop :=
  ∀ {k : Type u} [Field k] (F : ArtinFunctorModel.{u,w} k) (laws : VectorLaws F),
    letI := tangentAddCommGroupModel F laws
    letI := tangentModuleModel F laws
    H3Model F ↔ Module.Finite k (TangentModel F)

def SplitMapType :=
  ∀ {k : Type u} [Field k] {I J : Type u}
    [AddCommGroup I] [Module k I] [Module.Finite k I]
    [AddCommGroup J] [Module k J] [Module.Finite k J],
    (I →ₗ[k] J) → Hom (splitModel k I) (splitModel k J)

end CommutativeAlgebraNotes.SchlessingerTangentVectorSpaceSpec
