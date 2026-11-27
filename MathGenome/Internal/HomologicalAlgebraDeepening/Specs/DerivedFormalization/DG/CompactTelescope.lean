import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedKProjective
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.Telescope
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

open CategoryTheory CategoryTheory.Limits
open _root_.DerivedFormalization

universe j d e u v w t v'

namespace Specs.DerivedFormalization.DG.CompactTelescope

open AmbientDerived (category strictInput)
open Derived (HomotopyCategoryLaws)
open DerivedKProjective (derivedCategoryInstance)
open HomComplex (homotopyClass)
open ShiftCone (cone coneInclusion)
open Telescope (oneSubSuccessor telescopeComparison)

noncomputable section

section HomGroups

variable {D : Type d} [Category.{e} D] [Preadditive D]

/-- Covariant Hom into the category of abelian groups. -/
abbrev homGroup (C : D) : D ⥤ AddCommGrpCat.{e} :=
  preadditiveCoyoneda.obj (Opposite.op C)

/-- Compactness means preservation of all existing coproducts indexed by small types. -/
def Compact (C : D) : Prop :=
  ∀ I : Type j, PreservesColimitsOfShape (Discrete I) (homGroup C)

variable {Y : ℕ → D} {T : D}

/-- The cocone whose legs are the given maps, with compatibility checked at successors. -/
def sequenceCocone (step : ∀ n, Y n ⟶ Y (n + 1)) (incl : ∀ n, Y n ⟶ T)
    (comm : ∀ n, step n ≫ incl (n + 1) = incl n) :
    Cocone (Functor.ofSequence step) where
  pt := T
  ι := NatTrans.ofSequence (F := Functor.ofSequence step) (G := (Functor.const ℕ).obj T)
    incl fun n => by
      rw [Functor.ofSequence_map_homOfLE_succ]
      change step n ≫ incl (n + 1) = incl n ≫ 𝟙 T
      exact (comm n).trans (Category.comp_id (incl n)).symm

/-- The actual stage maps induce the group-colimit isomorphism, and each
element of the target group comes from a single stage. -/
def HomSequenceColimit (C : D) (step : ∀ n, Y n ⟶ Y (n + 1))
    (incl : ∀ n, Y n ⟶ T) : Prop :=
  ∃ comm : ∀ n, step n ≫ incl (n + 1) = incl n,
    Nonempty (IsColimit ((homGroup C).mapCocone (sequenceCocone step incl comm))) ∧
    ∀ f : C ⟶ T, ∃ (n : ℕ) (g : C ⟶ Y n), g ≫ incl n = f

end HomGroups

variable {k : Type u} [CommRing k]

/-- The strict inclusion of stage `n` through the target summand of the cone. -/
def telescopeStage {A : DGCategoryModel.{u,v,w} k}
    {X : ℕ → RightDGModuleModel A} (step : ∀ n, X n ⟶ X (n + 1))
    {U : Cofan X} (hU : IsColimit U) (n : ℕ) :
    X n ⟶ cone (oneSubSuccessor step hU) :=
  U.inj n ≫ coneInclusion (oneSubSuccessor step hU)

abbrev representedMap {B : DGCategoryModel.{u,v',w} k} (h : HomotopyCategoryLaws B)
    {M N : RightDGModuleModel B} (f : M ⟶ N) :
    letI := Derived.homotopyCategory B h
    letI := derivedCategoryInstance B h
    (Derived.quotient B h).obj M ⟶ (Derived.quotient B h).obj N := by
  letI := Derived.homotopyCategory B h
  letI := derivedCategoryInstance B h
  exact (Derived.quotient B h).map (homotopyClass f)

/-- Form the telescope in the strict input category, then use its image and
the images of the actual stage maps in the specified derived category. -/
def CompactTelescopeAt {A : DGCategoryModel.{u,v,w} k} {B : DGCategoryModel.{u,v',w} k}
    (h : HomotopyCategoryLaws B) (F : RightDGModuleModel A ⥤ RightDGModuleModel B) : Prop :=
  letI := Derived.homotopyCategory B h
  letI := derivedCategoryInstance B h
  let D := Derived.derivedCategory B h
  ∃ AD : Preadditive D,
    letI := AD
    ∀ (C : D), Compact.{max v' w} C →
    ∀ {X : ℕ → RightDGModuleModel A} (step : ∀ n, X n ⟶ X (n + 1))
      {U : Cofan X} (hU : IsColimit U),
      HomSequenceColimit C (fun n => representedMap h (F.map (step n)))
        (fun n => representedMap h (F.map (telescopeStage step hU n)))

/-- The canonical comparison with the objectwise colimit is a strict
quasi-isomorphism and induces the compatible isomorphism in the common
derived category at every adequate bound. -/
def OriginalTelescopeComparison : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k),
    let B := category.{u,v,w,t} A
    let F := strictInput.{u,v,w,t} A
    ∀ (h : HomotopyCategoryLaws B),
      letI := Derived.homotopyCategory B h
      letI := derivedCategoryInstance B h
      ∀ {X : ℕ → RightDGModuleModel A} (step : ∀ n, X n ⟶ X (n + 1))
        {U : Cofan X} (hU : IsColimit U)
        {L : Cocone (Functor.ofSequence step)} (_hL : IsColimit L),
        let p := telescopeComparison step hU L
        Module.quasiIsomorphism p ∧ IsIso (representedMap h (F.map p)) ∧
          ∀ n, representedMap h (F.map (telescopeStage step hU n)) ≫
            representedMap h (F.map p) = representedMap h (F.map (L.ι.app n))

/-- Compactness in the common derived category gives the group-colimit
comparison for a sequence of modules over the original dg category. -/
def OriginalCompactTelescope : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (h : HomotopyCategoryLaws (category.{u,v,w,t} A)),
    CompactTelescopeAt h (strictInput.{u,v,w,t} A)

/-- The same comparison for sequences in the entire adequate module
category, including sequences in semi-free resolutions. -/
def NativeCompactTelescope : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,max v w,w} k)
    (h : HomotopyCategoryLaws A),
    CompactTelescopeAt h (𝟭 (RightDGModuleModel A))

end

end Specs.DerivedFormalization.DG.CompactTelescope
