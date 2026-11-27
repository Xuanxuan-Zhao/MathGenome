import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.StrictComplexDescent
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.QuasiIsomorphismDetection
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.EffectiveModuleDescent
import Mathlib.CategoryTheory.Localization.Equivalence

/-! Degreewise faithfully flat descent and its localization at quasi-isomorphisms. -/

open CategoryTheory
open scoped DerivedFormalization.Descent

namespace DerivedFormalization.Descent.StrictComplexDescent

universe u v w

noncomputable section

open StrictComplexDescentSpec

attribute [local instance] StrictModuleDataSpec.category moduleDataZero

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]

/-- The chain isomorphism and its degreewise components encode the same strict data. -/
def degreewiseEquivalence : Degreewise.{u,v,w} A B ≌ Datum.{u,v,w} A B :=
  CategoryTheory.Equivalence.mk (fromDegreewise.{u,v,w} A B) (toDegreewise.{u,v,w} A B)
    (eqToIso (by rfl)) (eqToIso (by rfl))

theorem degreewisePresentation : DegreewisePresentation.{u,v,w} := by
  intro A B _ _ _
  exact ⟨degreewiseEquivalence.{u,v,w} A B, rfl, rfl⟩

variable [Module.FaithfullyFlat A B]

/-- Termwise scalar extension with strict datum and termwise formation of invariants. -/
def equivalence : Complex.{max u v w} A ≌ Datum.{u,v,w} A B :=
  ((EffectiveModuleDescent.equivalence.{u,v,w} A B).mapHomologicalComplex
    (ComplexShape.up ℤ)).trans (degreewiseEquivalence.{u,v,w} A B)

/-- The weak equivalences of the two complex categories correspond under scalar extension. -/
theorem inverseImage_quasiIsomorphisms :
    (quasiIsomorphisms.{u,v,w} A B).inverseImage (equivalence.{u,v,w} A B).functor =
      baseQuasiIsomorphisms.{max u v w} A := by
  ext X Y f
  let extend := ModuleCat.extendScalars.{u,v,max u v w} (algebraMap A B)
  change QuasiIso ((extend.mapHomologicalComplex (ComplexShape.up ℤ)).map f) ↔ QuasiIso f
  exact (quasiIso_iff_extendScalars (algebraMap A B)
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance) f).symm

private theorem inverse_maps_quasiIsomorphisms
    {X Y : Datum.{u,v,w} A B} (f : X ⟶ Y) (hf : quasiIsomorphisms.{u,v,w} A B f) :
    baseQuasiIsomorphisms.{max u v w} A ((equivalence.{u,v,w} A B).inverse.map f) := by
  let e := equivalence.{u,v,w} A B
  let W := quasiIsomorphisms.{u,v,w} A B
  rw [← inverseImage_quasiIsomorphisms.{u,v,w} A B]
  change W ((e.inverse ⋙ e.functor).map f)
  let _ : W.RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage
      (baseQuasiIsomorphisms.{max u v w} B) (forget.{u,v,w} A B)
  exact (W.arrow_mk_iso_iff (Arrow.isoMk' ((e.inverse ⋙ e.functor).map f) f
    (e.counitIso.app X) (e.counitIso.app Y) (e.counitIso.hom.naturality f).symm)).mpr hf

/-- The lifts of the two descent functors form an equivalence of the localized categories. -/
theorem localized :
    ∃ e' : (baseQuasiIsomorphisms.{max u v w} A).Localization ≌
        (quasiIsomorphisms.{u,v,w} A B).Localization,
      Nonempty ((equivalence.{u,v,w} A B).functor ⋙ (quasiIsomorphisms.{u,v,w} A B).Q ≅
        (baseQuasiIsomorphisms.{max u v w} A).Q ⋙ e'.functor) ∧
      Nonempty ((equivalence.{u,v,w} A B).inverse ⋙ (baseQuasiIsomorphisms.{max u v w} A).Q ≅
        (quasiIsomorphisms.{u,v,w} A B).Q ⋙ e'.inverse) := by
  let e := equivalence.{u,v,w} A B
  let W₁ := baseQuasiIsomorphisms.{max u v w} A
  let W₂ := quasiIsomorphisms.{u,v,w} A B
  have hF : W₁.IsInvertedBy (e.functor ⋙ W₂.Q) := by
    intro X Y f hf
    apply Localization.inverts W₂.Q W₂
    change (W₂.inverseImage e.functor) f
    rw [inverseImage_quasiIsomorphisms.{u,v,w} A B]
    exact hf
  have hG : W₂.IsInvertedBy (e.inverse ⋙ W₁.Q) :=
    fun _ _ f hf ↦ Localization.inverts W₁.Q W₁ _ (inverse_maps_quasiIsomorphisms.{u,v,w} A B f hf)
  let F := Localization.lift (e.functor ⋙ W₂.Q) hF W₁.Q
  let G := Localization.lift (e.inverse ⋙ W₁.Q) hG W₂.Q
  let facF := Localization.fac (e.functor ⋙ W₂.Q) hF W₁.Q
  let facG := Localization.fac (e.inverse ⋙ W₁.Q) hG W₂.Q
  let unit : (e.functor ⋙ W₂.Q) ⋙ G ≅ W₁.Q :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ facG ≪≫ e.funInvIdAssoc W₁.Q
  let counit : (e.inverse ⋙ W₁.Q) ⋙ F ≅ W₂.Q :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ facF ≪≫ e.invFunIdAssoc W₂.Q
  exact ⟨Localization.equivalence W₁.Q W₁ W₂.Q W₂ _ F _ G unit counit,
    ⟨facF.symm⟩, ⟨facG.symm⟩⟩

/-- Strict descent of unbounded complexes, including the induced localization equivalence. -/
theorem effective : Effective.{u,v,w} := by
  intro A B _ _ _ _
  exact ⟨EffectiveModuleDescent.baseChange_coherence A B, equivalence.{u,v,w} A B, rfl, rfl,
    inverseImage_quasiIsomorphisms.{u,v,w} A B, localized.{u,v,w} A B⟩

end

end DerivedFormalization.Descent.StrictComplexDescent
