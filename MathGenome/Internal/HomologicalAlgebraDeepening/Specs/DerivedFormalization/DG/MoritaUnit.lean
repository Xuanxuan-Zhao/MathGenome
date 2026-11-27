import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.CompactFiniteCells
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedBimoduleAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedCoproducts

open CategoryTheory CategoryTheory.Limits
open _root_.DerivedFormalization

universe u v w vA z t s j

namespace Specs.DerivedFormalization.DG.MoritaUnit

open AmbientDerived (category)
open BalancedTensor (CochainMap bimodule tmul left)
open BimoduleAdjunction (ordinaryHom ordinaryTensor)
open CompactFiniteCells (CompactAt)
open CompactRepresentables (LocalizationMapAdditive)
open Derived (HomotopyCategoryLaws)
open DerivedBimoduleAdjunction
  (AmbientSignedModels SignedModels DerivedAdjunctionData AdjunctionComparison
    StrictComparisonLaws ComparisonOnRepresentedInputs)
open DerivedCoefficientLift (Descent strictTransition)
open DerivedCoproducts (derivedCofan)
open DerivedKProjective (derivedCategoryInstance)
open HomComplex (homotopyClass)
open IndexedSemiFree (StrictSum)
open KProjective (isKProjective)
open Yoneda (representable)

noncomputable section

local notation "D" => Derived.derivedCategory
local notation "Q" => Derived.quotient

variable {k : Type u} [CommRing k]

/-- An ordinary chain map over a common coefficient universe, using the
specified degree maps of the bimodule. -/
def toComplexHom {C E : ModuleCochain.{u,v} k} (f : CochainMap C E) : C ⟶ E where
  f n := ModuleCat.ofHom (f.f n)
  comm' i n hin := by
    have h : i + 1 = n := by simpa [ComplexShape.up] using hin
    subst n
    exact ModuleCat.hom_ext (LinearMap.ext (fun x => (f.comm i x).symm))

/-- The bimodule's actual dg functor maps on morphism complexes are
quasi-isomorphisms. -/
def MorphismQuasiIsomorphisms
    {A : DGCategoryModel.{u,max v w z,w} k} {B : DGCategoryModel.{u,max v w z,z} k}
    (T : bimodule A B) : Prop :=
  ∀ a b : A.Obj, QuasiIso (toComplexHom (T.map a b))

/-- The image cofan uses the functor's maps of the given inclusions. -/
def mapCofan {C E : Type*} [Category* C] [Category* E] (G : C ⥤ E)
    {I : Type j} {N : I → C} (c : Cofan N) : Cofan (fun i => G.obj (N i)) :=
  Cofan.mk (G.obj c.pt) (fun i => G.map (c.inj i))

/-- Preservation of all existing coproducts with the specified index universe.
Equivalently, the canonical comparison from the coproduct of the images is
invertible whenever that coproduct is given. -/
def PreservesCoproducts.{idx, c, d, m, n} {C : Type c} {E : Type d}
    [Category.{m} C] [Category.{n} E] (G : C ⥤ E) : Prop :=
  ∀ {I : Type idx} {N : I → C} (c : Cofan N), IsColimit c →
    Nonempty (IsColimit (mapCofan G c))

section AtBound

variable {A : DGCategoryModel.{u,max v w z,w} k} {B : DGCategoryModel.{u,max v w z,z} k}
variable {T : bimodule A B} {m : SignedModels.{u,v,w,z} T}
variable {hA : HomotopyCategoryLaws A} {hB : HomotopyCategoryLaws B}

/-- The unit on a representable, after the tensor evaluation and Hom descent
isomorphisms, is the localization of the strict bimodule morphism. Its
component at (a), expressed in the Hom complex, is the given map of
complexes (T(a,b)). -/
def ComputesRepresentableUnit
    (d : DerivedAdjunctionData.{u,v,w,z} m.tensor m.hom hA hB) : Prop :=
  letI := Derived.homotopyCategory A hA
  letI := Derived.homotopyCategory B hB
  letI := derivedCategoryInstance A hA
  letI := derivedCategoryInstance B hB
  let QA := Q A hA
  let QB := Q B hB
  let G₀ := ordinaryHom.{u,v,w,z} m.hom
  let G := d.hom.derived
  ∀ b : A.Obj,
    let R := representable (A := A) b
    ∃ (hp : isKProjective R)
      (e : (ordinaryTensor.{u,v,w,z} m.tensor).obj R ≅ T.obj b),
      (∀ (a : A.Obj) (c : B.Obj) (i j n : ℤ) (h : i+j=n)
        (f : (A.hom a b).X i) (x : ((T.obj a).complex c).X j),
        (e.hom.app c).f n (m.tensor.degree R c n (tmul T R c a i j n h f x)) =
          left T c i j n h f x) ∧
      let η := m.adjunction.unit.app R ≫ G₀.map e.hom
      (∀ a : A.Obj, η.app a ≫ (m.hom.objectwise (T.obj b) a).inv =
        toComplexHom (T.map a b)) ∧
      d.adjunction.unit.app (QA.obj R) ≫
        G.map ((d.onProjective R hp).hom ≫ QB.map (homotopyClass e.hom)) ≫
        (d.onInput (T.obj b)).hom = QA.map (homotopyClass η)

end AtBound

/-- At a common adequate bound, the two Morita hypotheses on the represented
bimodule imply coproduct preservation and invertibility of the unit on
every object. The adjunction is the given G13 adjunction on these same
localizations. -/
def MoritaUnitAt : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,max v w z,w} k}
    {B : DGCategoryModel.{u,max v w z,z} k} {T : bimodule A B}
    (m : SignedModels.{u,v,w,z} T)
    (hA : HomotopyCategoryLaws A) (hB : HomotopyCategoryLaws B),
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    letI := derivedCategoryInstance A hA
    letI := derivedCategoryInstance B hB
    ∀ (S : Preadditive (D B hB))
      (d : DerivedAdjunctionData.{u,v,w,z} m.tensor m.hom hA hB),
      LocalizationMapAdditive hB S →
      d.Realizes m.adjunction → d.ComputesRepresentatives → d.IsExact →
      (∀ a, isKProjective (T.obj a)) →
      (∀ a, CompactAt.{u,z,max v w z,max v w z} hB S ((Q B hB).obj (T.obj a))) →
      MorphismQuasiIsomorphisms.{u,v,w,z} T →
      PreservesCoproducts.{j} d.hom.derived ∧
      ComputesRepresentableUnit d ∧
      ∀ X : D A hA, IsIso (d.adjunction.unit.app X)

section CoefficientTransition

variable {A : DGCategoryModel.{u,vA,w} k} {B : DGCategoryModel.{u,v,z} k}

set_option quotPrecheck false

set_option hygiene false in
local notation "A₀" => category.{u,vA,w,max v z t} A
set_option hygiene false in
local notation "B₀" => category.{u,v,z,max vA w t} B
set_option hygiene false in
local notation "A₁" => category.{u,vA,w,max v z t s} A
set_option hygiene false in
local notation "B₁" => category.{u,v,z,max vA w t s} B
set_option hygiene false in
local notation "U" => strictTransition.{u,vA,w,max v z t,s} A
set_option hygiene false in
local notation "V" => strictTransition.{u,v,z,max vA w t,s} B

variable {T : bimodule A B}
variable {m : AmbientSignedModels.{u,v,w,vA,z,t} T}
variable {m' : AmbientSignedModels.{u,v,w,vA,z,max t s} T}
variable {hA : HomotopyCategoryLaws A₀} {hB : HomotopyCategoryLaws B₀}
variable {hA' : HomotopyCategoryLaws A₁} {hB' : HomotopyCategoryLaws B₁}
variable {d : DerivedAdjunctionData.{u,max vA v t,w,z} m.models.tensor m.models.hom hA hB}
variable {d' : DerivedAdjunctionData.{u,max vA v t s,w,z} m'.models.tensor m'.models.hom hA' hB'}

/-- The larger coproduct comparison on represented inputs. Its source is the
image under the upper right adjoint of the derived cofan of the actual strict
sum. Maps from the summands to a represented module agree, by the adjunction
square, with the transitions of their lower-bound images. -/
def TransitionCoproducts
    (dI : Descent hA hA' U) (dJ : Descent hB hB' V)
    (ed :
      letI := Derived.homotopyCategory A₀ hA
      letI := Derived.homotopyCategory B₀ hB
      letI := Derived.homotopyCategory A₁ hA'
      letI := Derived.homotopyCategory B₁ hB'
      letI := derivedCategoryInstance A₀ hA
      letI := derivedCategoryInstance B₀ hB
      letI := derivedCategoryInstance A₁ hA'
      letI := derivedCategoryInstance B₁ hB'
      AdjunctionComparison d.adjunction d'.adjunction dI.D dJ.D) : Prop :=
  letI := Derived.homotopyCategory A₀ hA
  letI := Derived.homotopyCategory B₀ hB
  letI := Derived.homotopyCategory A₁ hA'
  letI := Derived.homotopyCategory B₁ hB'
  letI := derivedCategoryInstance A₀ hA
  letI := derivedCategoryInstance B₀ hB
  letI := derivedCategoryInstance A₁ hA'
  letI := derivedCategoryInstance B₁ hB'
  let QB := Q B₀ hB
  let G := d.hom.derived
  let G' := d'.hom.derived
  ∀ {I : Type s} (N : I → RightDGModuleModel B₀),
    ∃ (P : RightDGModuleModel B₁) (b : StrictSum (fun i => (V).obj (N i)) P),
      let c := derivedCofan hB' b
      Nonempty (IsColimit c) ∧
      ∃ hc : IsColimit (mapCofan G' c),
        ∀ (M : RightDGModuleModel B₀) (f : ∀ i, QB.obj (N i) ⟶ QB.obj M),
          Cofan.IsColimit.desc hc
            (fun i => G'.map ((dJ.representedIso (N i)).inv ≫ dJ.D.map (f i))) ≫
              ed.hom.inv.app (QB.obj M) =
          Cofan.IsColimit.desc hc
            (fun i => G'.map (dJ.representedIso (N i)).inv ≫
              ed.hom.inv.app (QB.obj (N i)) ≫ dI.D.map (G.map (f i)))

/-- At a larger common bound, the represented bimodule retains
K-projectivity, compactness (including its shifts), and the quasi-isomorphism
condition. The same derived adjunction comparisons identify the larger
coproduct calculation on represented inputs. -/
def MoritaUnitTransition : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,vA,w} k}
    {B : DGCategoryModel.{u,v,z} k} (T : bimodule A B)
    (m : AmbientSignedModels.{u,v,w,vA,z,t} T)
    (m' : AmbientSignedModels.{u,v,w,vA,z,max t s} T)
    (hA : HomotopyCategoryLaws A₀) (hB : HomotopyCategoryLaws B₀)
    (hA' : HomotopyCategoryLaws A₁) (hB' : HomotopyCategoryLaws B₁),
    letI := Derived.homotopyCategory A₀ hA
    letI := Derived.homotopyCategory B₀ hB
    letI := Derived.homotopyCategory A₁ hA'
    letI := Derived.homotopyCategory B₁ hB'
    letI := derivedCategoryInstance A₀ hA
    letI := derivedCategoryInstance B₀ hB
    letI := derivedCategoryInstance A₁ hA'
    letI := derivedCategoryInstance B₁ hB'
    ∀ (S : Preadditive (D B₀ hB)) (S' : Preadditive (D B₁ hB')),
      LocalizationMapAdditive hB S → LocalizationMapAdditive hB' S' →
      (∀ a, isKProjective (m.bimodule.obj a)) →
      (∀ a, CompactAt.{u,z,max vA v w z t,max vA v w z t} hB S
        ((Q B₀ hB).obj (m.bimodule.obj a))) →
      MorphismQuasiIsomorphisms.{u,max vA v t,w,z} m.bimodule →
      (∀ a, isKProjective (m'.bimodule.obj a)) ∧
      (∀ (a : A.Obj) (n : ℤ), CompactAt.{u,z,max vA v w z t s,max vA v w z t s} hB' S'
        ((Q B₁ hB').obj (ShiftCone.shift (m'.bimodule.obj a) n))) ∧
      MorphismQuasiIsomorphisms.{u,max vA v t s,w,z} m'.bimodule ∧
      ∃ (dI : Descent hA hA' U) (dJ : Descent hB hB' V)
        (e : AdjunctionComparison m.models.adjunction m'.models.adjunction U V)
        (eT : ∀ a : A.Obj, (V).obj (m.bimodule.obj a) ≅ m'.bimodule.obj a),
        dI.FullyFaithful ∧ dJ.FullyFaithful ∧
        StrictComparisonLaws.{u,max vA v t,w,z,max vA v t s} e
          (Equiv.refl _) (Equiv.refl _)
          (fun _ _ _ => ULift.moduleEquiv.symm) (fun _ _ _ => ULift.moduleEquiv.symm) eT ∧
        ∃ (d : DerivedAdjunctionData.{u,max vA v t,w,z} m.models.tensor m.models.hom hA hB)
          (d' : DerivedAdjunctionData.{u,max vA v t s,w,z} m'.models.tensor m'.models.hom hA' hB'),
          d.Realizes m.models.adjunction ∧ d.ComputesRepresentatives ∧ d.IsExact ∧
          d'.Realizes m'.models.adjunction ∧ d'.ComputesRepresentatives ∧ d'.IsExact ∧
          ∃ ed : AdjunctionComparison d.adjunction d'.adjunction dI.D dJ.D,
            ComparisonOnRepresentedInputs d d' dI dJ e ed ∧
            PreservesCoproducts.{s} d'.hom.derived ∧ TransitionCoproducts dI dJ ed

end CoefficientTransition

end

end Specs.DerivedFormalization.DG.MoritaUnit
