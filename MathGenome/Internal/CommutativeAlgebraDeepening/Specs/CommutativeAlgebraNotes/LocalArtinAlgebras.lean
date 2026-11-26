import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Finiteness.NilpotentKer
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.LocalRing.Pullback
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-! Shared objects for the local Artin category and marked deformations. -/

universe u v w z

namespace CommutativeAlgebraNotes

/-- Local Artin algebras with a specified residue field. The augmentation to the
field is local, so its kernel is the maximal ideal. -/
structure LocalArtinAlgebra (k : Type u) [Field k] where
  carrier : Type v
  [commRing : CommRing carrier]
  [algebra : Algebra k carrier]
  [localRing : IsLocalRing carrier]
  [artinianRing : IsArtinianRing carrier]
  residue : carrier →ₐ[k] k
  [localResidue : IsLocalHom residue]

attribute [instance] LocalArtinAlgebra.commRing LocalArtinAlgebra.algebra
  LocalArtinAlgebra.localRing LocalArtinAlgebra.artinianRing LocalArtinAlgebra.localResidue

namespace LocalArtinAlgebra

variable {k : Type u} [Field k]

instance : CoeSort (LocalArtinAlgebra.{u,v} k) (Type v) := ⟨carrier⟩

/-- Morphisms in the local Artin category are local (k)-algebra maps. -/
abbrev Hom (A B : LocalArtinAlgebra.{u,v} k) := { f : A →ₐ[k] B // IsLocalHom f }

instance {A B : LocalArtinAlgebra.{u,v} k} : CoeOut (Hom A B) (A →ₐ[k] B) := ⟨Subtype.val⟩

instance {A B : LocalArtinAlgebra.{u,v} k} : CoeFun (Hom A B) (fun _ => A → B) :=
  ⟨fun f => (f : A →ₐ[k] B)⟩

instance {A B : LocalArtinAlgebra.{u,v} k} (f : Hom A B) :
    IsLocalHom (f : A →ₐ[k] B) := f.property

@[ext]
theorem Hom.ext {A B : LocalArtinAlgebra.{u,v} k} {f g : Hom A B}
    (h : ∀ a, f a = g a) : f = g :=
  Subtype.ext (AlgHom.ext h)

def Hom.id (A : LocalArtinAlgebra.{u,v} k) : Hom A A := ⟨AlgHom.id k A, ⟨fun _ h => h⟩⟩

def Hom.comp {A B C : LocalArtinAlgebra.{u,v} k} (g : Hom B C) (f : Hom A B) : Hom A C :=
  ⟨(g : B →ₐ[k] C).comp (f : A →ₐ[k] B), ⟨fun a h =>
    (isUnit_map_iff (f : A →ₐ[k] B) a).mp ((isUnit_map_iff (g : B →ₐ[k] C) (f a)).mp h)⟩⟩

instance : CategoryTheory.Category (LocalArtinAlgebra.{u,v} k) where
  Hom := Hom
  id := Hom.id
  comp f g := g.comp f
  id_comp _ := Hom.ext (fun _ => rfl)
  comp_id _ := Hom.ext (fun _ => rfl)
  assoc _ _ _ := Hom.ext (fun _ => rfl)

@[simp]
theorem residue_algebraMap (A : LocalArtinAlgebra.{u,v} k) (c : k) :
    A.residue (algebraMap k A c) = c :=
  A.residue.commutes c

instance residueAlgebra (A : LocalArtinAlgebra.{u,v} k) : Algebra A k :=
  A.residue.toRingHom.toAlgebra

instance residueTower (A : LocalArtinAlgebra.{u,v} k) : IsScalarTower k A k :=
  IsScalarTower.of_algHom A.residue

/-- The residue of a local map over the fixed field is the identity on that field. -/
@[simp]
theorem Hom.residue_apply {A B : LocalArtinAlgebra.{u,v} k} (f : Hom A B) (a : A) :
    B.residue (f a) = A.residue a := by
  have hzero : A.residue (a - algebraMap k A (A.residue a)) = 0 := by simp
  have h : ¬ IsUnit (a - algebraMap k A (A.residue a)) := by
    intro hu
    simpa [hzero] using hu.map A.residue
  have h' : B.residue (f (a - algebraMap k A (A.residue a))) = 0 := by
    by_contra hn
    exact h <| IsUnit.of_map (f : A →ₐ[k] B) _ <|
      IsUnit.of_map B.residue _ (isUnit_iff_ne_zero.mpr hn)
  change B.residue ((f : A →ₐ[k] B) (a - _)) = 0 at h'
  simpa only [map_sub, AlgHom.commutes, residue_algebraMap, Algebra.algebraMap_self_apply, sub_eq_zero] using h'

/-- The algebra structure on the target obtained from a morphism. -/
abbrev Hom.toAlgebra {A B : LocalArtinAlgebra.{u,v} k} (f : Hom A B) : Algebra A B :=
  (f : A →ₐ[k] B).toRingHom.toAlgebra

theorem Hom.residueScalarTower {A B : LocalArtinAlgebra.{u,v} k} (f : Hom A B) :
    letI : Algebra A B := f.toAlgebra
    IsScalarTower A B k :=
  letI : Algebra A B := f.toAlgebra
  IsScalarTower.of_algebraMap_eq fun a => (f.residue_apply a).symm

/-- A small extension is surjective with a one-dimensional kernel annihilated
by the source maximal ideal. The dimension is over the specified field. -/
def SmallExtensionModel {A B : LocalArtinAlgebra.{u,v} k} (f : Hom A B) : Prop :=
  Function.Surjective f ∧
    Module.finrank k (RingHom.ker (f : A →ₐ[k] B).toRingHom) = 1 ∧
    ∀ a ∈ IsLocalRing.maximalIdeal A,
      ∀ b ∈ RingHom.ker (f : A →ₐ[k] B).toRingHom, a * b = 0

/-- The ordinary residue field of the bundled ring is its specified field. -/
theorem ker_residue (A : LocalArtinAlgebra.{u,v} k) :
    RingHom.ker A.residue = IsLocalRing.maximalIdeal A := by
  ext a
  rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    ← isUnit_map_iff A.residue a, isUnit_iff_ne_zero, not_not]

theorem residue_surjective (A : LocalArtinAlgebra.{u,v} k) : Function.Surjective A.residue :=
  fun c => ⟨algebraMap k A c, A.residue_algebraMap c⟩

noncomputable def residueEquivModel (A : LocalArtinAlgebra.{u,v} k) :
    IsLocalRing.ResidueField A ≃ₐ[k] k :=
  let f : IsLocalRing.ResidueField A →ₐ[k] k :=
    Ideal.Quotient.liftₐ _ A.residue (ker_residue A).ge
  AlgEquiv.ofBijective f ⟨f.toRingHom.injective, fun c =>
    ⟨IsLocalRing.residue A (algebraMap k A c), A.residue_algebraMap c⟩⟩

/-- A local Artin algebra with specified residue field is finite over that field. -/
theorem moduleFinite (A : LocalArtinAlgebra.{u,v} k) : Module.Finite k A := by
  apply Module.finite_of_surjective_of_ker_le_nilradical A.residue A.residue_surjective
  · rw [ker_residue]
    change IsLocalRing.maximalIdeal A ≤ (⊥ : Ideal A).radical
    rw [← IsArtinianRing.jacobson_eq_radical, IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
  · exact IsNoetherian.noetherian _

private theorem pullbackFst_isLocal {A B C : LocalArtinAlgebra.{u,v} k}
    (f : A →ₐ[k] C) (g : B →ₐ[k] C) [IsLocalHom g] :
    IsLocalHom (AlgHom.pullbackFst f g) := by
  constructor
  rintro ⟨⟨a, b⟩, h⟩ ha
  change IsUnit a at ha
  apply (AlgHom.isUnit_pullback_mk_iff f g h).2
  change f a = g b at h
  exact ⟨ha, IsUnit.of_map g b (h ▸ ha.map f)⟩

private theorem pullbackSnd_isLocal {A B C : LocalArtinAlgebra.{u,v} k}
    (f : A →ₐ[k] C) (g : B →ₐ[k] C) [IsLocalHom f] :
    IsLocalHom (AlgHom.pullbackSnd f g) := by
  constructor
  rintro ⟨⟨a, b⟩, h⟩ hb
  change IsUnit b at hb
  apply (AlgHom.isUnit_pullback_mk_iff f g h).2
  change f a = g b at h
  exact ⟨IsUnit.of_map f a (h.symm ▸ hb.map g), hb⟩

/-- The fibre product ring consists of the compatible pairs with coordinatewise
operations, and its residue is the common residue of the two coordinates. -/
abbrev pullbackModel {A B C : LocalArtinAlgebra.{u,v} k} (f : Hom A C) (g : Hom B C) :
    LocalArtinAlgebra.{u,v} k :=
  let f' : A →ₐ[k] C := f
  let g' : B →ₐ[k] C := g
  letI : Module.Finite k A := moduleFinite A
  letI : Module.Finite k B := moduleFinite B
  letI : Module.Finite k (f'.pullback g') :=
    Module.Finite.of_injective (f'.pullback g').val.toLinearMap Subtype.val_injective
  letI : IsLocalRing (f'.pullback g') := AlgHom.isLocalRing_pullback f' g'
  letI : IsArtinianRing (f'.pullback g') := IsArtinianRing.of_finite k _
  { carrier := f'.pullback g'
    residue := A.residue.comp (f'.pullbackFst g')
    localResidue := ⟨fun x hx =>
      (pullbackFst_isLocal f' g').map_nonunit x (IsUnit.of_map A.residue _ hx)⟩ }

def pullbackFstModel {A B C : LocalArtinAlgebra.{u,v} k} (f : Hom A C) (g : Hom B C) :
    Hom (pullbackModel f g) A :=
  ⟨AlgHom.pullbackFst (f : A →ₐ[k] C) (g : B →ₐ[k] C), pullbackFst_isLocal (f : A →ₐ[k] C) (g : B →ₐ[k] C)⟩

def pullbackSndModel {A B C : LocalArtinAlgebra.{u,v} k} (f : Hom A C) (g : Hom B C) :
    Hom (pullbackModel f g) B :=
  ⟨AlgHom.pullbackSnd (f : A →ₐ[k] C) (g : B →ₐ[k] C), pullbackSnd_isLocal (f : A →ₐ[k] C) (g : B →ₐ[k] C)⟩

/-- The base field with its identity residue map. -/
abbrev fieldModel (k : Type u) [Field k] : LocalArtinAlgebra.{u,u} k where
  carrier := k
  residue := AlgHom.id k k
  localResidue := ⟨fun _ h => h⟩

/-- The right scalar action on a vector space used in the split square-zero algebra. -/
abbrev splitOppositeModule (k : Type u) [Field k] (I : Type v) [AddCommGroup I]
    [Module k I] : Module kᵐᵒᵖ I :=
  Module.compHom I (RingEquiv.toOpposite k).symm.toRingHom

private def splitWithActions (k : Type u) [Field k] (I : Type v) [AddCommGroup I] [Module k I]
    [Module kᵐᵒᵖ I] [IsCentralScalar k I] [Module.Finite k I] :
    LocalArtinAlgebra.{u,max u v} k :=
  let π := TrivSqZeroExt.fstHom k k I
  letI : IsLocalHom π := ⟨fun _ h => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr h⟩
  letI : IsLocalRing (TrivSqZeroExt k I) := (π : TrivSqZeroExt k I →+* k).domain_isLocalRing
  letI : Module.Finite k (TrivSqZeroExt k I) :=
    Module.Finite.of_injective
      (π.toLinearMap.prod (TrivSqZeroExt.sndHom k I))
      (fun _ _ h => TrivSqZeroExt.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  letI : IsArtinianRing (TrivSqZeroExt k I) := IsArtinianRing.of_finite k _
  { carrier := TrivSqZeroExt k I, residue := π }

/-- The finite-dimensional split square-zero algebra (k \oplus I). -/
def splitModel (k : Type u) [Field k] (I : Type v) [AddCommGroup I] [Module k I]
    [Module.Finite k I] : LocalArtinAlgebra.{u,max u v} k :=
  letI : Module kᵐᵒᵖ I := splitOppositeModule k I
  letI : IsCentralScalar k I := ⟨fun _ _ => rfl⟩
  splitWithActions k I

/-- The dual numbers (k[\epsilon]/(\epsilon^2)), in their square-zero model. -/
abbrev dualModel (k : Type u) [Field k] : LocalArtinAlgebra.{u,u} k :=
  splitWithActions k k

end LocalArtinAlgebra

open scoped TensorProduct
open LocalArtinAlgebra

/-- Flat deformations of (B) with a specified identification of their special
fibre. The total algebra can have arbitrary dimension over the base. -/
structure MarkedDeformation {k : Type u} [Field k] (A : LocalArtinAlgebra.{u,v} k)
    (B : Type w) [CommRing B] [Algebra k B] where
  carrier : Type (max v z)
  [commRing : CommRing carrier]
  [algebra : Algebra A carrier]
  [flat : Module.Flat A carrier]
  marking : k ⊗[A] carrier ≃ₐ[k] B

attribute [instance] MarkedDeformation.commRing MarkedDeformation.algebra MarkedDeformation.flat

namespace MarkedDeformation

variable {k : Type u} [Field k] {A A' : LocalArtinAlgebra.{u,v} k}
variable {B : Type w} [CommRing B] [Algebra k B]

instance : CoeSort (MarkedDeformation.{u,v,w,z} A B) (Type (max v z)) := ⟨carrier⟩

/-- The special fibre of an (A)-algebra is formed using its given residue map. -/
abbrev SpecialFibre (A : LocalArtinAlgebra.{u,v} k) (D : Type z) [CommRing D] [Algebra A D] :=
  k ⊗[A] D

/-- The equivalence on special fibres induced by an isomorphism over (A). -/
def specialFibreCongr {D E : Type z} [CommRing D] [Algebra A D]
    [CommRing E] [Algebra A E] (e : D ≃ₐ[A] E) :
    SpecialFibre A D ≃ₐ[k] SpecialFibre A E :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : k ≃ₐ[k] k) e

/-- A marked isomorphism is an algebra isomorphism over the base that respects
the given special-fibre identifications. -/
def MarkedIso (D E : MarkedDeformation.{u,v,w,z} A B) :=
  { e : D ≃ₐ[A] E // (specialFibreCongr e).trans E.marking = D.marking }

def Isomorphic (D E : MarkedDeformation.{u,v,w,z} A B) : Prop := Nonempty (MarkedIso D E)

instance : Setoid (MarkedDeformation.{u,v,w,z} A B) where
  r := Isomorphic
  iseqv := by
    refine ⟨fun D => ⟨⟨AlgEquiv.refl, ?_⟩⟩, ?_, ?_⟩
    · rw [specialFibreCongr, Algebra.TensorProduct.congr_refl]
      exact AlgEquiv.ext (fun _ => rfl)
    · intro D E h
      obtain ⟨e, he⟩ := h
      refine ⟨⟨e.symm, AlgEquiv.ext fun x => ?_⟩⟩
      have hsymm : specialFibreCongr e.symm = (specialFibreCongr e).symm := by
        rw [specialFibreCongr, specialFibreCongr, ← Algebra.TensorProduct.congr_symm,
          AlgEquiv.refl_symm]
      simpa only [AlgEquiv.trans_apply, hsymm, AlgEquiv.apply_symm_apply] using
        (DFunLike.congr_fun he (specialFibreCongr e.symm x)).symm
    · intro D E F hDE hEF
      obtain ⟨e, he⟩ := hDE
      obtain ⟨f, hf⟩ := hEF
      refine ⟨⟨e.trans f, AlgEquiv.ext fun x => ?_⟩⟩
      have htrans : specialFibreCongr (e.trans f) =
          (specialFibreCongr e).trans (specialFibreCongr f) := by
        rw [specialFibreCongr, specialFibreCongr, specialFibreCongr,
          ← Algebra.TensorProduct.congr_trans]
        rfl
      simpa only [htrans, AlgEquiv.trans_apply] using
        (DFunLike.congr_fun hf (specialFibreCongr e x)).trans (DFunLike.congr_fun he x)

/-- The set of marked flat deformations up to marked isomorphism. -/
def Classes (A : LocalArtinAlgebra.{u,v} k) (B : Type w) [CommRing B] [Algebra k B] :=
  Quotient (inferInstance : Setoid (MarkedDeformation.{u,v,w,z} A B))

/-- The canonical identification of the two special fibres for a base change. -/
def baseChangeSpecialFibre (f : LocalArtinAlgebra.Hom A A')
    (D : MarkedDeformation.{u,v,w,z} A B) :
    letI : Algebra A A' := f.toAlgebra
    SpecialFibre A' (A' ⊗[A] D) ≃ₐ[k] SpecialFibre A D :=
  letI : Algebra A A' := f.toAlgebra
  letI := f.residueScalarTower
  Algebra.TensorProduct.cancelBaseChange A A' k k D

/-- The base changed deformation has total algebra (A' \otimes_A D) and
inherits its marking via the canonical identification of special fibres. -/
abbrev baseChangeModel (f : LocalArtinAlgebra.Hom A A')
    (D : MarkedDeformation.{u,v,w,z} A B) : MarkedDeformation.{u,v,w,z} A' B :=
  letI : Algebra A A' := f.toAlgebra
  { carrier := A' ⊗[A] D
    marking := (baseChangeSpecialFibre f D).trans D.marking }

/-- The class represented by a marked deformation. -/
def classModel (D : MarkedDeformation.{u,v,w,z} A B) : Classes.{u,v,w,z} A B :=
  Quotient.mk _ D

theorem baseChangeModel_isomorphic (f : LocalArtinAlgebra.Hom A A')
    {D E : MarkedDeformation.{u,v,w,z} A B} (h : Isomorphic D E) :
    Isomorphic (baseChangeModel f D) (baseChangeModel f E) := by
  obtain ⟨e, he⟩ := h
  let : Algebra A A' := f.toAlgebra
  let := f.residueScalarTower
  let e' : (A' ⊗[A] D) ≃ₐ[A'] (A' ⊗[A] E) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : A' ≃ₐ[A'] A') e
  have hn :
      (specialFibreCongr e').trans (baseChangeSpecialFibre f E) =
        (baseChangeSpecialFibre f D).trans (specialFibreCongr e) := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply Algebra.TensorProduct.ext'
    intro c x
    induction x using TensorProduct.inductionOn with
    | tmul a d => simp [e', specialFibreCongr, baseChangeSpecialFibre]
    | add x y ihx ihy => simp only [TensorProduct.tmul_add, map_add, ihx, ihy]
  refine ⟨⟨e', AlgEquiv.ext fun x => ?_⟩⟩
  have hx : baseChangeSpecialFibre f E (specialFibreCongr e' x) =
      specialFibreCongr e (baseChangeSpecialFibre f D x) := DFunLike.congr_fun hn x
  change E.marking (baseChangeSpecialFibre f E (specialFibreCongr e' x)) =
    D.marking (baseChangeSpecialFibre f D x)
  rw [hx]
  exact DFunLike.congr_fun he (baseChangeSpecialFibre f D x)

/-- Base change of marked isomorphism classes along any local algebra map. -/
def baseChangeClassesModel (f : LocalArtinAlgebra.Hom A A') :
    Classes.{u,v,w,z} A B → Classes.{u,v,w,z} A' B :=
  Quotient.map (baseChangeModel f) (fun _ _ h => baseChangeModel_isomorphic f h)

end MarkedDeformation

namespace LocalArtinAlgebrasSpec

-- These declarations describe types that have the maximum of their inputs' universes.
set_option linter.checkUnivs false

open CategoryTheory LocalArtinAlgebra MarkedDeformation

def PullbackType := ∀ {k : Type u} [Field k] {A B C : LocalArtinAlgebra.{u,v} k},
  Hom A C → Hom B C → LocalArtinAlgebra.{u,v} k

def PullbackFstType := ∀ {k : Type u} [Field k] {A B C : LocalArtinAlgebra.{u,v} k}
    (f : Hom A C) (g : Hom B C), Hom (pullbackModel f g) A

def PullbackSndType := ∀ {k : Type u} [Field k] {A B C : LocalArtinAlgebra.{u,v} k}
    (f : Hom A C) (g : Hom B C), Hom (pullbackModel f g) B

def PullbackUniversal : Prop := ∀ {k : Type u} [Field k] {A B C : LocalArtinAlgebra.{u,v} k}
    (f : Hom A C) (g : Hom B C),
  @IsPullback (LocalArtinAlgebra.{u,v} k) _ (pullbackModel f g) A B C
    (pullbackFstModel f g) (pullbackSndModel f g) f g

def SmallExtensionType := ∀ {k : Type u} [Field k] {A B : LocalArtinAlgebra.{u,v} k},
  Hom A B → Prop

def FieldType := ∀ (k : Type u) [Field k], LocalArtinAlgebra.{u,u} k

def FieldTerminal : Prop := ∀ {k : Type u} [Field k] (A : LocalArtinAlgebra.{u,u} k),
  ∃! _ : Hom A (fieldModel k), True

def FieldInitial : Prop := ∀ {k : Type u} [Field k] (A : LocalArtinAlgebra.{u,u} k),
  ∃! _ : Hom (fieldModel k) A, True

def SplitType := ∀ (k : Type u) [Field k] (I : Type v) [AddCommGroup I] [Module k I]
  [Module.Finite k I], LocalArtinAlgebra.{u,max u v} k

def DualNumbersPresentation : Prop := ∀ (k : Type u) [Field k],
  ∃ e : AdjoinRoot ((Polynomial.X : Polynomial k) ^ 2) ≃ₐ[k] dualModel k,
    e (AdjoinRoot.root _) = (DualNumber.eps : DualNumber k)

def ResidueEquivType := ∀ {k : Type u} [Field k] (A : LocalArtinAlgebra.{u,v} k),
  IsLocalRing.ResidueField A ≃ₐ[k] k

def ResidueEquivFormula : Prop :=
  ∀ {k : Type u} [Field k] (A : LocalArtinAlgebra.{u,v} k) (a : A),
    residueEquivModel A (IsLocalRing.residue A a) = A.residue a

def ClassOfType := ∀ {k : Type u} [Field k] {A : LocalArtinAlgebra.{u,v} k}
    {B : Type w} [CommRing B] [Algebra k B],
  MarkedDeformation.{u,v,w,z} A B → Classes.{u,v,w,z} A B

def ClassEquality : Prop := ∀ {k : Type u} [Field k] {A : LocalArtinAlgebra.{u,v} k}
    {B : Type w} [CommRing B] [Algebra k B] {D E : MarkedDeformation.{u,v,w,z} A B},
  classModel D = classModel E ↔
    ∃ e : D ≃ₐ[A] E, (specialFibreCongr e).trans E.marking = D.marking

def BaseChangeType := ∀ {k : Type u} [Field k] {A A' : LocalArtinAlgebra.{u,v} k}
    {B : Type w} [CommRing B] [Algebra k B],
  Hom A A' → MarkedDeformation.{u,v,w,z} A B → MarkedDeformation.{u,v,w,z} A' B

def BaseChangeClassesType := ∀ {k : Type u} [Field k] {A A' : LocalArtinAlgebra.{u,v} k}
    {B : Type w} [CommRing B] [Algebra k B],
  Hom A A' → Classes.{u,v,w,z} A B → Classes.{u,v,w,z} A' B

def BaseChangeClassFormula : Prop := ∀ {k : Type u} [Field k] {A A' : LocalArtinAlgebra.{u,v} k}
    {B : Type w} [CommRing B] [Algebra k B]
    (f : Hom A A') (D : MarkedDeformation.{u,v,w,z} A B),
  baseChangeClassesModel f (classModel D) = classModel (baseChangeModel f D)

def BaseChangeIdentity : Prop := ∀ {k : Type u} [Field k] {A : LocalArtinAlgebra.{u,v} k}
    {B : Type w} [CommRing B] [Algebra k B] (x : Classes.{u,v,w,z} A B),
  baseChangeClassesModel (Hom.id A) x = x

def BaseChangeComposition : Prop :=
  ∀ {k : Type u} [Field k] {A A' : LocalArtinAlgebra.{u,v} k}
    {B : Type w} [CommRing B] [Algebra k B] {A'' : LocalArtinAlgebra.{u,v} k}
    (f : Hom A A') (g : Hom A' A'')
    (x : Classes.{u,v,w,z} A B),
  baseChangeClassesModel (g.comp f) x = baseChangeClassesModel g (baseChangeClassesModel f x)

end LocalArtinAlgebrasSpec

end CommutativeAlgebraNotes
