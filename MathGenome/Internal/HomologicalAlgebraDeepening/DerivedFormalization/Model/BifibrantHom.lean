import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.BifibrantHom
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Model.Localization

open CategoryTheory HomotopicalAlgebra

universe v u v' u'

namespace DerivedFormalization.Model

variable {C : Type u} [Category.{v} C]

section ModelCategory

variable [ModelCategory C]

/-- For a cofibrant source and fibrant target, equality of classes is precisely
the homotopy relation of Q03. -/
theorem leftHomotopyClass_mk_eq_iff {A B : C} [IsCofibrant A] [IsFibrant B]
    (f g : A ⟶ B) : LeftHomotopyClass.mk f = LeftHomotopyClass.mk g ↔ LeftHomotopic f g :=
  (LeftHomotopyClass.mk_eq_mk_iff f g).trans (leftHomotopic_iff_leftHomotopyRel f g).symm

/-- Precomposition of left homotopy classes into a fibrant object. -/
def precompLeftHomotopyClass {A' A B : C} [IsFibrant B] (k : A' ⟶ A) :
    LeftHomotopyClass A B → LeftHomotopyClass A' B :=
  Quot.lift (fun f => LeftHomotopyClass.mk (k ≫ f))
    (fun _ _ h => LeftHomotopyClass.sound (LeftHomotopyRel.precomp h k))

variable {D : Type u'} [Category.{v'} D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]

/-- The map on homotopy classes induced by the localization functor. -/
abbrev homotopyClassToLocalizationHom {A B : C} :
    LeftHomotopyClass A B → (L.obj A ⟶ L.obj B) :=
  leftHomotopyClassToHom L

@[simp]
theorem homotopyClassToLocalizationHom_mk {A B : C} (f : A ⟶ B) :
    homotopyClassToLocalizationHom L (LeftHomotopyClass.mk f) = L.map f :=
  leftHomotopyClassToHom_mk L f

/-- The canonical map is bijective for a cofibrant source and a fibrant target. -/
theorem homotopyClassToLocalizationHom_bijective (A B : C) [IsCofibrant A] [IsFibrant B] :
    Function.Bijective (homotopyClassToLocalizationHom L (A := A) (B := B)) :=
  bijective_leftHomotopyClassToHom L A B

theorem homotopyClassToLocalizationHom_precomp {A' A B : C}
    [IsCofibrant A'] [IsCofibrant A] [IsFibrant B]
    (k : A' ⟶ A) (h : LeftHomotopyClass A B) :
    homotopyClassToLocalizationHom L (precompLeftHomotopyClass k h) =
      L.map k ≫ homotopyClassToLocalizationHom L h := by
  obtain ⟨f, rfl⟩ := h.mk_surjective
  exact L.map_comp k f

theorem homotopyClassToLocalizationHom_postcomp {A B B' : C}
    [IsCofibrant A] [IsFibrant B] [IsFibrant B']
    (k : B ⟶ B') (h : LeftHomotopyClass A B) :
    homotopyClassToLocalizationHom L (h.postcomp k) =
      homotopyClassToLocalizationHom L h ≫ L.map k := by
  obtain ⟨f, rfl⟩ := h.mk_surjective
  exact L.map_comp f k

end ModelCategory

/-- The same canonical bijection for the replacement localization of Q05. -/
theorem Replacement.homotopyClassToHom [FunctorialModelCategory C]
    (r : Replacement C) (A B : C) [IsCofibrant A] [IsFibrant B] :
    ∃ φ : LeftHomotopyClass A B → (r.localization.obj A ⟶ r.localization.obj B),
      Function.Bijective φ ∧ ∀ f : A ⟶ B, φ (LeftHomotopyClass.mk f) = r.localization.map f := by
  have := r.isLocalization
  exact ⟨homotopyClassToLocalizationHom r.localization,
    homotopyClassToLocalizationHom_bijective r.localization A B,
    homotopyClassToLocalizationHom_mk r.localization⟩

end DerivedFormalization.Model
