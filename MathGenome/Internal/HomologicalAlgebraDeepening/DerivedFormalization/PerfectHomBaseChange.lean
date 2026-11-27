import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.PerfectHomBaseChange
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedHomComparisonMaps
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.PerfectDuals
import Mathlib.CategoryTheory.Adjunction.Unique

/-! Strong monoidal transport of the evaluation pairing proves derived Hom base change. -/

namespace DerivedFormalization.PerfectHomBaseChange

open CategoryTheory Category MonoidalCategory
open Functor.LaxMonoidal (ε μ)
open Functor.OplaxMonoidal (η δ)

noncomputable section

set_option linter.style.haveILetI false

section Monoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]

/-- A strong monoidal functor transports both triangle identities of an exact pairing. -/
@[implicit_reducible]
private def mapPairing (F : C ⥤ D) [F.Monoidal] (P Q : C) [ExactPairing P Q] :
    ExactPairing (F.obj P) (F.obj Q) where
  coevaluation' := ε F ≫ F.map (η_ P Q) ≫ δ F P Q
  evaluation' := μ F Q P ≫ F.map (ε_ P Q) ≫ η F
  coevaluation_evaluation' := by
    calc
      _ = F.obj Q ◁ ε F ≫ μ F Q (𝟙_ C) ≫
          F.map (Q ◁ η_ P Q ≫ (α_ Q P Q).inv ≫ ε_ P Q ▷ Q) ≫
          δ F (𝟙_ C) Q ≫ η F ▷ F.obj Q := by
        simp only [whiskerLeft_comp, comp_whiskerRight, assoc, Functor.map_comp,
          Functor.Monoidal.map_whiskerLeft, Functor.Monoidal.map_whiskerRight,
          Functor.Monoidal.map_associator_inv, Functor.Monoidal.μ_δ_assoc]
      _ = _ := by
        rw [ExactPairing.coevaluation_evaluation, F.map_comp, assoc,
          ← Functor.LaxMonoidal.right_unitality_assoc, ← Functor.OplaxMonoidal.left_unitality]
  evaluation_coevaluation' := by
    calc
      _ = ε F ▷ F.obj P ≫ μ F (𝟙_ C) P ≫
          F.map (η_ P Q ▷ P ≫ (α_ P Q P).hom ≫ P ◁ ε_ P Q) ≫
          δ F P (𝟙_ C) ≫ F.obj P ◁ η F := by
        simp only [whiskerLeft_comp, comp_whiskerRight, assoc, Functor.map_comp,
          Functor.Monoidal.map_whiskerLeft, Functor.Monoidal.map_whiskerRight,
          Functor.Monoidal.map_associator, Functor.Monoidal.μ_δ_assoc]
      _ = _ := by
        rw [ExactPairing.evaluation_coevaluation, F.map_comp, assoc,
          ← Functor.LaxMonoidal.left_unitality_assoc, ← Functor.OplaxMonoidal.right_unitality]

/-- The counit of the adjunction induced by a pairing is tensor evaluation. -/
private theorem pairing_counit (P Q : C) [ExactPairing P Q] (Y : C) :
    (tensorRightAdjunction P Q).counit.app Y =
      (α_ Y Q P).hom ≫ Y ◁ ε_ P Q ≫ (ρ_ Y).hom := by
  rw [← Adjunction.homEquiv_symm_id, tensorRightAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  simp [tensorRightHomEquiv]

/-- Strong monoidal transport of the canonical mate for a dualizable right factor. -/
private theorem isIso_homComparison (F : C ⥤ D) [F.Monoidal]
    (P Q : C) [ExactPairing P Q] {HR : C ⥤ C} {HS : D ⥤ D}
    (adjR : tensorRight P ⊣ HR) (adjS : tensorRight (F.obj P) ⊣ HS) (Y : C) :
    IsIso (adjS.homEquiv _ _ (μ F (HR.obj Y) P ≫ F.map (adjR.counit.app Y))) := by
  letI := mapPairing F P Q
  let adjQ := tensorRightAdjunction P Q
  let adjFQ := tensorRightAdjunction (F.obj P) (F.obj Q)
  let iR := (adjQ.rightAdjointUniq adjR).hom.app Y
  let iS := (adjFQ.rightAdjointUniq adjS).hom.app (F.obj Y)
  let b := adjS.homEquiv (F.obj (HR.obj Y)) (F.obj Y) (μ F (HR.obj Y) P ≫ F.map (adjR.counit.app Y))
  have hR : iR ▷ P ≫ adjR.counit.app Y = adjQ.counit.app Y :=
    adjQ.rightAdjointUniq_hom_app_counit adjR Y
  have hS : (adjS.homEquiv (F.obj Y ⊗ F.obj Q) (F.obj Y)).symm iS =
      adjFQ.counit.app (F.obj Y) :=
    adjFQ.homEquiv_symm_rightAdjointUniq_hom_app adjS (F.obj Y)
  have h : (μ F Y Q ≫ F.map iR) ≫ b = iS := by
    apply (adjS.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply, hS]
    change ((μ F Y Q ≫ F.map iR) ▷ F.obj P) ≫
      μ F (HR.obj Y) P ≫ F.map (adjR.counit.app Y) = adjFQ.counit.app (F.obj Y)
    rw [comp_whiskerRight, assoc, Functor.LaxMonoidal.μ_natural_left_assoc, ← F.map_comp, hR]
    dsimp only [adjQ, adjFQ]
    simp only [pairing_counit, Functor.map_comp,
      Functor.LaxMonoidal.associativity_assoc, ← Functor.LaxMonoidal.μ_natural_right_assoc]
    change _ = (α_ (F.obj Y) (F.obj Q) (F.obj P)).hom ≫
      F.obj Y ◁ (μ F Q P ≫ F.map (ε_ P Q) ≫ η F) ≫ (ρ_ (F.obj Y)).hom
    rw [Functor.LaxMonoidal.right_unitality F Y]
    simp only [whiskerLeft_comp, assoc, Functor.Monoidal.whiskerLeft_η_ε_assoc]
  haveI : IsIso ((μ F Y Q ≫ F.map iR) ≫ b) := by
    rw [h]
    exact inferInstanceAs (IsIso iS)
  exact IsIso.of_isIso_comp_left (μ F Y Q ≫ F.map iR) b

end Monoidal

open Specs.DerivedFormalization.PerfectHomBaseChange
open Specs.DerivedFormalization.Cochains (derivedValue)
open Specs.DerivedFormalization.CochainTensorTransport (AdequateModel)
open Specs.DerivedFormalization.DerivedHomAdjunction (Closed homFrom)
open Specs.DerivedFormalization.DerivedHomModels (Models)
open Specs.DerivedFormalization.PerfectDuals (dualValue)
open Specs.DerivedFormalization.DerivedHomComparisonMaps (evaluationValue)
open DerivedFormalization.DerivedHomComparisonMaps (baseChange)

universe u w a v t

attribute [local instance] HasDerivedCategory.standard

section Derived

variable {R : Type u} [CommRing R] {A : Type a} [CommRing A] {e : R ≃+* A}
  {M : AdequateModel e} {T : Specs.DerivedFormalization.DerivedTensor.Model M}
  {H : Models.{u,a} R}

/-- The closed adjunction uses the bifunctor's tensor of morphisms, while
the pairing adjunction uses whiskering. The two agree on objects. -/
private def tensorRightIso (T : Specs.DerivedFormalization.DerivedTensor.Model M)
    (P : derivedValue.{a} R) :
    letI := T.monoidal
    Specs.DerivedFormalization.DerivedHomAdjunction.tensorRight T P ≅ tensorRight P :=
  letI := T.monoidal
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {Z Z'} k => by
    change (k ⊗ₘ 𝟙 P) ≫ 𝟙 (Z' ⊗ P) = 𝟙 (Z ⊗ P) ≫ k ▷ P
    rw [comp_id, id_comp, tensorHom_id])

private def whiskeringAdjunction (c : Closed T H) (P : derivedValue.{a} R) :
    letI := T.monoidal
    tensorRight P ⊣ homFrom H P :=
  (c.adjunction P).ofNatIsoLeft (tensorRightIso T P)

private theorem whiskeringAdjunction_homEquiv (c : Closed T H)
    (Z P Y : derivedValue.{a} R) :
    letI := T.monoidal
    (whiskeringAdjunction c P).homEquiv Z Y = (c.equiv Z P Y).toEquiv := by
  letI := T.monoidal
  ext k
  rw [whiskeringAdjunction, Adjunction.homEquiv_ofNatIsoLeft_apply]
  change (c.adjunction P).homEquiv Z Y (𝟙 _ ≫ k) = _
  rw [id_comp, Closed.adjunction_homEquiv]

private theorem whiskeringAdjunction_counit (c : Closed T H) (P Y : derivedValue.{a} R) :
    letI := T.monoidal
    (whiskeringAdjunction c P).counit.app Y = evaluationValue c P Y := by
  letI := T.monoidal
  rw [← Adjunction.homEquiv_symm_id, whiskeringAdjunction_homEquiv]
  rfl

end Derived

theorem baseChange_isIso : BaseChangeIso.{u,w,a} := by
  intro R S _ _ A B _ _ e d MR MS TR TS HR HS f F L cR cS m P Y hp
  letI := TR.monoidal
  letI := TS.monoidal
  letI := TR.symmetric
  letI := TS.symmetric
  letI := m.braided
  obtain ⟨pairing, _⟩ :=
    ((DerivedFormalization.PerfectDuals.perfectDuality TR HR cR).2 P hp).2.2.1
  letI := pairing
  have h := isIso_homComparison L.derived P (dualValue TR HR P)
    (whiskeringAdjunction cR P) (whiskeringAdjunction cS (L.derived.obj P)) Y
  rw [whiskeringAdjunction_homEquiv, whiskeringAdjunction_counit] at h
  change IsIso (baseChange cR cS m P Y)
  exact h

theorem liftedBaseChange_isIso : LiftedBaseChangeIso.{u,w,a,v,t} := by
  intro R S _ _ A B _ _ e d MR MS TR TS HR HS f F L cR cS m P Y hp
  exact baseChange_isIso cR cS m _ _
    (DerivedFormalization.PerfectDuals.perfectLift.{u,v,max w a t} P hp)

end

end DerivedFormalization.PerfectHomBaseChange
