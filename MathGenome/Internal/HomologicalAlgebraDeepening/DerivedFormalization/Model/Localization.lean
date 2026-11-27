import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Localization
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Model.Whitehead

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra CategoryTheory.Functor

universe v u v' u'

namespace DerivedFormalization.Model

open Specs.ModelLocalization

abbrev HomotopyCategory (C : Type u) [Category.{v} C] [ModelCategory C] :=
  homotopyCategoryValue C

abbrev homotopyClassFunctor {C : Type u} [Category.{v} C] [ModelCategory C] :
    BifibrantObject C ⥤ HomotopyCategory C := homotopyClassFunctorValue

variable {C : Type u} [Category.{v} C]

section

variable [ModelCategory C]

/-- Two maps of bifibrant objects represent the same class exactly when they are homotopic. -/
theorem homotopyClass_map_eq_iff {X Y : BifibrantObject C} (f g : X ⟶ Y) :
    homotopyClassFunctor.map f = homotopyClassFunctor.map g ↔ LeftHomotopic f.hom g.hom :=
  (BifibrantObject.toHoCat_map_eq_iff f g).trans
    (BifibrantObject.homRel_iff_leftHomotopyRel.trans
      (leftHomotopic_iff_leftHomotopyRel f.hom g.hom).symm)

abbrev Replacement.toBifibrant (r : Replacement C) : C ⥤ BifibrantObject C :=
  toBifibrantValue r

/-- The functor sending a map to the homotopy class of its bifibrant replacement. -/
abbrev Replacement.localization (r : Replacement C) : C ⥤ HomotopyCategory C :=
  r.toBifibrant ⋙ homotopyClassFunctor

theorem Replacement.map_weakEquivalence_iff (r : Replacement C) {X Y : C} (f : X ⟶ Y) :
    (weakEquivalences C (r.Q.map f) ↔ weakEquivalences C f) ∧
    (weakEquivalences C (r.R.map f) ↔ weakEquivalences C f) := by
  let W := weakEquivalences C
  constructor
  · calc
      W (r.Q.map f) ↔ W (r.Q.map f ≫ r.p.app Y) :=
        (W.postcomp_iff _ _ (r.trivialFibration Y).2).symm
      _ ↔ W (r.p.app X ≫ f) := by
        change W (r.Q.map f ≫ r.p.app Y) ↔ W (r.p.app X ≫ (𝟭 C).map f)
        rw [r.p.naturality]
      _ ↔ W f := W.precomp_iff _ _ (r.trivialFibration X).2
  · calc
      W (r.R.map f) ↔ W (r.i.app X ≫ r.R.map f) :=
        (W.precomp_iff _ _ (r.trivialCofibration X).2).symm
      _ ↔ W (f ≫ r.i.app Y) := by
        change W (r.i.app X ≫ r.R.map f) ↔ W ((𝟭 C).map f ≫ r.i.app Y)
        rw [r.i.naturality]
      _ ↔ W f := W.postcomp_iff _ _ (r.trivialCofibration Y).2

end

/-- Factor the natural initial and terminal maps pointwise using the two
functorial factorizations. -/
theorem replacementExists (C : Type u) [Category.{v} C] [FunctorialModelCategory C] :
    Nonempty (Replacement C) := by
  let fromInitial : (Functor.const C).obj (⊥_ C) ⟶ 𝟭 C :=
    { app := initial.to
      naturality _ _ _ := initialIsInitial.hom_ext _ _ }
  let toTerminal : 𝟭 C ⟶ (Functor.const C).obj (⊤_ C) :=
    { app := terminal.from
      naturality _ _ _ := terminalIsTerminal.hom_ext _ _ }
  let qFactor := functorialFactorizationData (cofibrations C) (trivialFibrations C)
  let rFactor := functorialFactorizationData (trivialCofibrations C) (fibrations C)
  let q := (qFactor.functorCategory C).factorizationData fromInitial
  let r := (rFactor.functorCategory C).factorizationData toTerminal
  exact ⟨{
    Q := q.Z
    R := r.Z
    p := q.p
    i := r.i
    cofibrant := fun X =>
      (isCofibrant_iff_of_isInitial (q.i.app X) initialIsInitial).2
        ((cofibration_iff _).2 (q.hi X))
    fibrant := fun X =>
      (isFibrant_iff_of_isTerminal (r.p.app X) terminalIsTerminal).2
        ((fibration_iff _).2 (r.hp X))
    trivialFibration := fun X => q.hp X
    trivialCofibration := fun X => r.hi X }⟩

variable [FunctorialModelCategory C]

/-- A natural transformation with weak-equivalence components becomes a
natural isomorphism after postcomposition with the localization. -/
private noncomputable def replacementIso {F G : C ⥤ C} (τ : F ⟶ G)
    (hτ : ∀ X, weakEquivalences C (τ.app X)) :
    F ⋙ (weakEquivalences C).Q ≅ G ⋙ (weakEquivalences C).Q := by
  let L := (weakEquivalences C).Q
  haveI : ∀ X, IsIso ((whiskerRight τ L).app X) :=
    fun X => CategoryTheory.Localization.inverts L _ _ (hτ X)
  haveI := NatIso.isIso_of_isIso_app (whiskerRight τ L)
  exact asIso (whiskerRight τ L)

/-- The functor of bifibrant replacements and homotopy classes localizes at weak
equivalences. -/
theorem Replacement.isLocalization (r : Replacement C) :
    r.localization.IsLocalization (weakEquivalences C) := by
  let L := (weakEquivalences C).Q
  let incl := BifibrantObject.localizerMorphism C
  let F := incl.localizedFunctor homotopyClassFunctor L
  let E := F.asEquivalence
  have square : incl.functor ⋙ L ≅ homotopyClassFunctor ⋙ E.functor :=
    CatCommSq.iso incl.functor homotopyClassFunctor L F
  have comparison : r.localization ⋙ E.functor ≅ L := calc
    r.localization ⋙ E.functor ≅ r.toBifibrant ⋙ (incl.functor ⋙ L) :=
      Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ square.symm
    _ ≅ (r.Q ⋙ r.R) ⋙ L := (Functor.associator _ _ _).symm
    _ ≅ r.Q ⋙ (𝟭 C ⋙ L) :=
      Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (replacementIso r.i fun X => (r.trivialCofibration X).2).symm
    _ ≅ L :=
      isoWhiskerLeft _ L.leftUnitor ≪≫
        replacementIso r.p (fun X => (r.trivialFibration X).2) ≪≫ L.leftUnitor
  exact Functor.IsLocalization.of_equivalence_target L _ r.localization E.symm
    (isoWhiskerRight comparison.symm E.inverse ≪≫ Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ E.unitIso.symm ≪≫ r.localization.rightUnitor)

/-- The equivalence on functor categories includes every natural transformation
between weak-equivalence-inverting functors. -/
theorem Replacement.universalProperty : universalPropertyType.{v, u, v', u'} := by
  intro C _ _ r
  have := r.isLocalization
  refine ⟨CategoryTheory.Localization.inverts _ _, fun D _ => ?_⟩
  exact inferInstanceAs
    (CategoryTheory.Localization.whiskeringLeftFunctor r.localization (weakEquivalences C) D
      ).IsEquivalence

/-- The localization detects weak equivalences. -/
theorem Replacement.weakEquivalence_iff_isIso (r : Replacement C) {X Y : C} (f : X ⟶ Y) :
    IsIso (r.localization.map f) ↔ weakEquivalences C f := by
  constructor
  · intro hf
    let g := r.toBifibrant.map f
    have : IsIso (homotopyClassFunctor.map g) := hf
    obtain ⟨h, hh⟩ := homotopyClassFunctor.map_surjective (inv (homotopyClassFunctor.map g))
    have hW : weakEquivalences C g.hom := by
      apply (whitehead g.hom).2
      refine ⟨h.hom, (homotopyClass_map_eq_iff (g ≫ h) (𝟙 _)).1 ?_,
        (homotopyClass_map_eq_iff (h ≫ g) (𝟙 _)).1 ?_⟩
      · rw [Functor.map_comp, hh, CategoryTheory.Functor.map_id, IsIso.hom_inv_id]
      · rw [Functor.map_comp, hh, CategoryTheory.Functor.map_id, IsIso.inv_hom_id]
    have hRQ : weakEquivalences C (r.R.map (r.Q.map f)) := hW
    exact ((r.map_weakEquivalence_iff f).1).1 (((r.map_weakEquivalence_iff (r.Q.map f)).2).1 hRQ)
  · have := r.isLocalization
    exact CategoryTheory.Localization.inverts r.localization (weakEquivalences C) f

/-- The same detection statement for any choice of localization functor. -/
theorem weakEquivalence_iff_isIso_of_isLocalization
    {D : Type u'} [Category.{v'} D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    {X Y : C} (f : X ⟶ Y) :
    IsIso (L.map f) ↔ weakEquivalences C f := by
  let W := weakEquivalences C
  let r := (replacementExists C).some
  have := r.isLocalization
  let E := CategoryTheory.Localization.uniq r.localization L W
  let e := CategoryTheory.Localization.compUniqFunctor r.localization L W
  constructor
  · intro hf
    have : IsIso (E.functor.map (r.localization.map f)) := by
      change IsIso ((r.localization ⋙ E.functor).map f)
      rw [← NatIso.naturality_2 e f]
      infer_instance
    exact (r.weakEquivalence_iff_isIso f).1 (isIso_of_reflects_iso _ E.functor)
  · exact CategoryTheory.Localization.inverts L W f

end DerivedFormalization.Model
