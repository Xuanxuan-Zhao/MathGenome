import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.DerivedAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Model.QuillenAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Model.BifibrantHom
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Model.Brown
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.CategoryTheory.Localization.Opposite
import Mathlib.CategoryTheory.HomCongr

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

namespace DerivedFormalization.Model

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [ModelCategory C] [ModelCategory D] {L : C ⥤ D} {U : D ⥤ C} {adj : L ⊣ U}

theorem IsQuillen.map_weakEquivalence_cofibrant (h : IsQuillen adj)
    {X X' : C} [IsCofibrant X] [IsCofibrant X'] (f : X ⟶ X')
    (hf : weakEquivalences C f) : weakEquivalences D (L.map f) :=
  brown_cofibrant (weakEquivalences D) (CofibrantObject.ι ⋙ L)
    (by intro A B g hg; exact (h.2 (CofibrantObject.ι.map g) hg).2)
    (X := ⟨X, ‹IsCofibrant X›⟩) (Y := ⟨X', ‹IsCofibrant X'›⟩) (ObjectProperty.homMk f) hf

theorem IsQuillen.map_weakEquivalence_fibrant (h : IsQuillen adj)
    {Y Y' : D} [IsFibrant Y] [IsFibrant Y'] (f : Y ⟶ Y')
    (hf : weakEquivalences D f) : weakEquivalences C (U.map f) :=
  brown_fibrant (weakEquivalences C) (FibrantObject.ι ⋙ U)
    (by intro A B g hg; exact (((isQuillen_iff_right adj).1 h).2 (FibrantObject.ι.map g) hg).2)
    (X := ⟨Y, ‹IsFibrant Y›⟩) (Y := ⟨Y', ‹IsFibrant Y'›⟩) (ObjectProperty.homMk f) hf

theorem IsQuillen.map_cofibrantReplacement_weakEquivalence (h : IsQuillen adj)
    (c : Replacement C) {X X' : C} (f : X ⟶ X') (hf : weakEquivalences C f) :
    weakEquivalences D (L.map (c.Q.map f)) := by
  have := c.cofibrant X
  have := c.cofibrant X'
  exact h.map_weakEquivalence_cofibrant _ ((c.map_weakEquivalence_iff f).1.mpr hf)

theorem IsQuillen.map_fibrantReplacement_weakEquivalence (h : IsQuillen adj)
    (d : Replacement D) {Y Y' : D} (f : Y ⟶ Y') (hf : weakEquivalences D f) :
    weakEquivalences C (U.map (d.R.map f)) := by
  have := d.fibrant Y
  have := d.fibrant Y'
  exact h.map_weakEquivalence_fibrant _ ((d.map_weakEquivalence_iff f).2.mpr hf)

/-- The left Quillen functor takes cylinders of cofibrant objects to cylinders. -/
noncomputable def IsQuillen.mapCylinder (h : IsQuillen adj) {X : C} [IsCofibrant X]
    (P : Cylinder X) : Cylinder (L.obj X) := by
  haveI : P.val.IsGood := P.property
  haveI : IsCofibrant P.val.I := inferInstance
  let T : HomotopicalAlgebra.Cylinder (L.obj X) :=
    { toPrecylinder := P.val.toPrecylinder.map L
      weakEquivalence_π := ⟨h.map_weakEquivalence_cofibrant P.val.π (mem_weakEquivalences _)⟩ }
  refine ⟨T, ⟨?_⟩⟩
  let := adj.isLeftAdjoint
  have he : T.i = coprodComparison L X X ≫ L.map P.val.i := by
    apply coprod.hom_ext
    · change coprod.inl ≫ T.i = coprod.inl ≫ (coprodComparison L X X ≫ L.map P.val.i)
      rw [inl_coprodComparison_assoc, ← L.map_comp, P.val.inl_i, T.inl_i]
      rfl
    · change coprod.inr ≫ T.i = coprod.inr ≫ (coprodComparison L X X ≫ L.map P.val.i)
      rw [inr_coprodComparison_assoc, ← L.map_comp, P.val.inr_i, T.inr_i]
      rfl
  have hc : cofibrations D (coprodComparison L X X ≫ L.map P.val.i) :=
    (cofibrations D).comp_mem _ _ ((cofibrations D).of_isIso _) (h.1 _ (mem_cofibrations _))
  exact (cofibration_iff T.i).2 (he.symm ▸ hc)

/-- Ordinary adjunction carries the homotopy relation to the homotopy relation. -/
theorem IsQuillen.homEquiv_leftHomotopic_iff (h : IsQuillen adj)
    {X : C} {Y : D} [IsCofibrant X] [IsFibrant Y] (f g : L.obj X ⟶ Y) :
    LeftHomotopic f g ↔ LeftHomotopic (adj.homEquiv X Y f) (adj.homEquiv X Y g) := by
  have : IsCofibrant (L.obj X) := h.isCofibrant_obj inferInstance
  have : IsFibrant (U.obj Y) := h.isFibrant_obj inferInstance
  obtain ⟨P, _⟩ := HomotopicalAlgebra.Cylinder.exists_very_good X
  let P' : Cylinder X := ⟨P, inferInstance⟩
  let T := h.mapCylinder P'
  rw [leftHomotopic_iff_exists_on_cylinder T, leftHomotopic_iff_exists_on_cylinder P']
  constructor
  · rintro ⟨H, h₀, h₁⟩
    change L.obj P.I ⟶ Y at H
    refine ⟨adj.homEquiv P.I Y H, ?_, ?_⟩
    · rw [← adj.homEquiv_naturality_left]
      exact congrArg (adj.homEquiv X Y) (show L.map P.i₀ ≫ H = f from h₀)
    · rw [← adj.homEquiv_naturality_left]
      exact congrArg (adj.homEquiv X Y) (show L.map P.i₁ ≫ H = g from h₁)
  · rintro ⟨H, h₀, h₁⟩
    refine ⟨show (↑T : HomotopicalAlgebra.Cylinder (L.obj X)).I ⟶ Y from
      (adj.homEquiv P.I Y).symm H, ?_, ?_⟩
    · change L.map P.i₀ ≫ _ = _
      rw [← adj.homEquiv_naturality_left_symm, h₀, Equiv.symm_apply_apply]
    · change L.map P.i₁ ≫ _ = _
      rw [← adj.homEquiv_naturality_left_symm, h₁, Equiv.symm_apply_apply]

end DerivedFormalization.Model

namespace DerivedFormalization.Model

open Opposite

section HomBifunctor

universe w va vb vh ua ub uh

variable {A : Type ua} {B : Type ub} {H : Type uh}
  [Category.{va} A] [Category.{vb} B] [Category.{vh} H]

/-- The hom bifunctor with a common universe for comparing homs in two categories. -/
private def homBifunctor (F : A ⥤ H) (G : B ⥤ H) : Aᵒᵖ × B ⥤ Type (max w vh) where
  obj X := ULift.{w} (F.obj X.1.unop ⟶ G.obj X.2)
  map f := ↾fun g => ULift.up (F.map f.1.unop ≫ g.down ≫ G.map f.2)
  map_id X := by ext g; simp
  map_comp f g := by ext k; simp [Category.assoc]

variable {F : A ⥤ B} {G : B ⥤ A}

set_option backward.isDefEq.respectTransparency false in
/-- Read a natural isomorphism of lifted hom bifunctors as an adjunction. -/
private def adjunctionOfHomBifunctor
    (e : homBifunctor.{va} F (𝟭 B) ≅ homBifunctor.{vb} (𝟭 A) G) : F ⊣ G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => Equiv.ulift.symm.trans
        ((e.app (op X, Y)).toEquiv.trans Equiv.ulift)
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        have hn := types_congr_hom
          (e.inv.naturality (show (op X, Y) ⟶ (op X', Y) from Prod.mkHom f.op (𝟙 Y))) (ULift.up g)
        change e.inv.app (op X', Y) (ULift.up ((𝟭 A).map f ≫ g ≫ G.map (𝟙 Y))) =
          ULift.up (F.map f ≫ (e.inv.app (op X, Y) (ULift.up g)).down ≫ (𝟭 B).map (𝟙 Y)) at hn
        have hg : g ≫ G.map (𝟙 Y) = g := by
          rw [G.map_id]
          exact Category.comp_id g
        change e.inv.app (op X', Y) (ULift.up (f ≫ g ≫ G.map (𝟙 Y))) =
          ULift.up (F.map f ≫ (e.inv.app (op X, Y) (ULift.up g)).down ≫ 𝟙 Y) at hn
        rw [hg] at hn
        have hi : (e.inv.app (op X, Y) (ULift.up g)).down ≫ 𝟙 Y =
            (e.inv.app (op X, Y) (ULift.up g)).down :=
          Category.comp_id (show F.obj X ⟶ Y from (e.inv.app (op X, Y) (ULift.up g)).down)
        exact (congrArg (fun z => z.down) hn).trans (congrArg (fun k => F.map f ≫ k) hi)
      homEquiv_naturality_right := by
        intro X Y Y' f g
        have hn := types_congr_hom
          (e.hom.naturality (show (op X, Y) ⟶ (op X, Y') from Prod.mkHom (𝟙 (op X)) g)) (ULift.up f)
        change e.hom.app (op X, Y') (ULift.up (F.map (𝟙 X) ≫ f ≫ (𝟭 B).map g)) =
          ULift.up ((𝟙 X) ≫ (e.hom.app (op X, Y) (ULift.up f)).down ≫ G.map g) at hn
        have hf : F.map (𝟙 X) ≫ f ≫ g = f ≫ g := by
          rw [F.map_id]
          exact Category.id_comp (f ≫ g)
        change e.hom.app (op X, Y') (ULift.up (F.map (𝟙 X) ≫ f ≫ g)) =
          ULift.up ((𝟙 X) ≫ (e.hom.app (op X, Y) (ULift.up f)).down ≫ G.map g) at hn
        rw [hf, Category.id_comp] at hn
        exact congrArg (fun z => z.down) hn }

private theorem adjunctionOfHomBifunctor_homEquiv
    (e : homBifunctor.{va} F (𝟭 B) ≅ homBifunctor.{vb} (𝟭 A) G)
    (X : A) (Y : B) (f : F.obj X ⟶ Y) :
    (adjunctionOfHomBifunctor e).homEquiv X Y f = (e.hom.app (op X, Y) (ULift.up f)).down := by
  rw [adjunctionOfHomBifunctor, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

end HomBifunctor

section Derived

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [FunctorialModelCategory C] [FunctorialModelCategory D]
  {L : C ⥤ D} {U : D ⥤ C} {adj : L ⊣ U}

variable (c : Replacement C) (d : Replacement D)

local instance cofibrantLocalization : c.localization.IsLocalization (weakEquivalences C) :=
  c.isLocalization

local instance fibrantLocalization : d.localization.IsLocalization (weakEquivalences D) :=
  d.isLocalization

private noncomputable def cofibrantComparison : c.Q ⋙ c.localization ≅ c.localization :=
  NatIso.ofComponents
    (fun X => Localization.isoOfHom c.localization (weakEquivalences C) (c.p.app X)
      (c.trivialFibration X).2)
    (fun f => by
      change c.localization.map (c.Q.map f) ≫ c.localization.map (c.p.app _) =
        c.localization.map (c.p.app _) ≫ c.localization.map f
      simpa only [← Functor.map_comp, Functor.id_map] using congrArg (fun k => c.localization.map k) (c.p.naturality f))

private noncomputable def fibrantComparison : d.localization ≅ d.R ⋙ d.localization :=
  NatIso.ofComponents
    (fun Y => Localization.isoOfHom d.localization (weakEquivalences D) (d.i.app Y)
      (d.trivialCofibration Y).2)
    (fun f => by
      change d.localization.map f ≫ d.localization.map (d.i.app _) =
        d.localization.map (d.i.app _) ≫ d.localization.map (d.R.map f)
      simpa only [← Functor.map_comp, Functor.id_map] using congrArg (fun k => d.localization.map k) (d.i.naturality f))

variable (h : IsQuillen adj)

include h in
private theorem leftCompositeInverts :
    (weakEquivalences C).IsInvertedBy ((c.Q ⋙ L) ⋙ d.localization) :=
  fun _ _ f hf => Localization.inverts d.localization (weakEquivalences D) _
    (h.map_cofibrantReplacement_weakEquivalence c f hf)

include h in
private theorem rightCompositeInverts :
    (weakEquivalences D).IsInvertedBy ((d.R ⋙ U) ⋙ c.localization) :=
  fun _ _ f hf => Localization.inverts c.localization (weakEquivalences C) _
    (h.map_fibrantReplacement_weakEquivalence d f hf)

variable {c d}
variable {F : HomotopyCategory C ⥤ HomotopyCategory D}
  {G : HomotopyCategory D ⥤ HomotopyCategory C}
variable (eL : c.localization ⋙ F ≅ (c.Q ⋙ L) ⋙ d.localization)
  (eR : d.localization ⋙ G ≅ (d.R ⋙ U) ⋙ c.localization)

private noncomputable def leftRepresentative {X : C} {Y : D}
    (f : L.obj (c.Q.obj X) ⟶ d.R.obj Y) :
    F.obj (c.localization.obj X) ⟶ d.localization.obj Y :=
  eL.hom.app X ≫ d.localization.map f ≫ (fibrantComparison d).inv.app Y

private noncomputable def rightRepresentative {X : C} {Y : D}
    (f : c.Q.obj X ⟶ U.obj (d.R.obj Y)) :
    c.localization.obj X ⟶ G.obj (d.localization.obj Y) :=
  (cofibrantComparison c).inv.app X ≫ c.localization.map f ≫ eR.inv.app Y

private noncomputable def leftClassEquiv (X : C) (Y : D) :
    LeftHomotopyClass (L.obj (c.Q.obj X)) (d.R.obj Y) ≃
      (F.obj (c.localization.obj X) ⟶ d.localization.obj Y) := by
  letI := c.cofibrant X
  letI := d.fibrant Y
  letI := h.isCofibrant_obj (c.cofibrant X)
  exact (Equiv.ofBijective _ (homotopyClassToLocalizationHom_bijective d.localization _ _)).trans
    (((eL.app X).symm).homCongr ((fibrantComparison d).app Y).symm)

private noncomputable def rightClassEquiv (X : C) (Y : D) :
    LeftHomotopyClass (c.Q.obj X) (U.obj (d.R.obj Y)) ≃
      (c.localization.obj X ⟶ G.obj (d.localization.obj Y)) := by
  letI := c.cofibrant X
  letI := d.fibrant Y
  letI := h.isFibrant_obj (d.fibrant Y)
  exact (Equiv.ofBijective _ (homotopyClassToLocalizationHom_bijective c.localization _ _)).trans
    (((cofibrantComparison c).app X).homCongr (eR.app Y).symm)

private theorem leftClassEquiv_mk {X : C} {Y : D} (f : L.obj (c.Q.obj X) ⟶ d.R.obj Y) :
    leftClassEquiv h eL X Y (LeftHomotopyClass.mk f) = leftRepresentative eL f := by
  exact congrArg (fun m => eL.hom.app X ≫ m ≫ (fibrantComparison d).inv.app Y)
    (homotopyClassToLocalizationHom_mk d.localization f)

private theorem rightClassEquiv_mk {X : C} {Y : D} (f : c.Q.obj X ⟶ U.obj (d.R.obj Y)) :
    rightClassEquiv h eR X Y (LeftHomotopyClass.mk f) = rightRepresentative eR f := by
  exact congrArg (fun m => (cofibrantComparison c).inv.app X ≫ m ≫ eR.inv.app Y)
    (homotopyClassToLocalizationHom_mk c.localization f)

private noncomputable def homotopyClassEquiv (X : C) [IsCofibrant X] (Y : D) [IsFibrant Y] :
    LeftHomotopyClass (L.obj X) Y ≃ LeftHomotopyClass X (U.obj Y) := by
  letI := h.isCofibrant_obj (show IsCofibrant X from inferInstance)
  letI := h.isFibrant_obj (show IsFibrant Y from inferInstance)
  refine Equiv.ofBijective (Quot.lift (fun f => LeftHomotopyClass.mk (adj.homEquiv X Y f)) ?_) ?_
  · intro f g hfg
    exact (leftHomotopyClass_mk_eq_iff _ _).2 ((h.homEquiv_leftHomotopic_iff f g).1
      ((leftHomotopic_iff_leftHomotopyRel f g).2 hfg))
  · constructor
    · intro f g hfg
      obtain ⟨f, rfl⟩ := f.mk_surjective
      obtain ⟨g, rfl⟩ := g.mk_surjective
      exact (leftHomotopyClass_mk_eq_iff _ _).2 ((h.homEquiv_leftHomotopic_iff f g).2
        ((leftHomotopyClass_mk_eq_iff _ _).1 hfg))
    · intro g
      obtain ⟨g, rfl⟩ := g.mk_surjective
      exact ⟨LeftHomotopyClass.mk ((adj.homEquiv X Y).symm g), by
        change LeftHomotopyClass.mk (adj.homEquiv X Y ((adj.homEquiv X Y).symm g)) = _
        rw [Equiv.apply_symm_apply]⟩

private noncomputable def representativeEquiv (X : C) (Y : D) :
    (F.obj (c.localization.obj X) ⟶ d.localization.obj Y) ≃
      (c.localization.obj X ⟶ G.obj (d.localization.obj Y)) := by
  letI := c.cofibrant X
  letI := d.fibrant Y
  exact (leftClassEquiv h eL X Y).symm.trans
    ((homotopyClassEquiv h (c.Q.obj X) (d.R.obj Y)).trans (rightClassEquiv h eR X Y))

private theorem representativeEquiv_apply {X : C} {Y : D}
    (f : L.obj (c.Q.obj X) ⟶ d.R.obj Y) :
    representativeEquiv h eL eR X Y (leftRepresentative eL f) =
      rightRepresentative eR (adj.homEquiv (c.Q.obj X) (d.R.obj Y) f) := by
  have := c.cofibrant X
  have := d.fibrant Y
  rw [← leftClassEquiv_mk h eL f]
  change rightClassEquiv h eR X Y
    (homotopyClassEquiv h (c.Q.obj X) (d.R.obj Y)
      ((leftClassEquiv h eL X Y).symm (leftClassEquiv h eL X Y (LeftHomotopyClass.mk f)))) = _
  rw [Equiv.symm_apply_apply]
  exact rightClassEquiv_mk h eR _

include h in
private theorem leftRepresentative_surjective (X : C) (Y : D) :
    Function.Surjective (leftRepresentative eL (X := X) (Y := Y)) := by
  intro k
  obtain ⟨m, rfl⟩ := (leftClassEquiv h eL X Y).surjective k
  obtain ⟨f, rfl⟩ := m.mk_surjective
  exact ⟨f, (leftClassEquiv_mk h eL f).symm⟩

private theorem leftRepresentative_naturality {X' X : C} {Y Y' : D}
    (u : X' ⟶ X) (v : Y ⟶ Y') (f : L.obj (c.Q.obj X) ⟶ d.R.obj Y) :
    F.map (c.localization.map u) ≫ leftRepresentative eL f ≫ d.localization.map v =
      leftRepresentative eL (L.map (c.Q.map u) ≫ f ≫ d.R.map v) := by
  have hL := eL.hom.naturality_assoc u
    (d.localization.map f ≫ (fibrantComparison d).inv.app Y ≫ d.localization.map v)
  have hR := (fibrantComparison d).inv.naturality v
  change F.map (c.localization.map u) ≫ eL.hom.app X ≫ _ =
    eL.hom.app X' ≫ d.localization.map (L.map (c.Q.map u)) ≫ _ at hL
  change d.localization.map (d.R.map v) ≫ (fibrantComparison d).inv.app Y' =
    (fibrantComparison d).inv.app Y ≫ d.localization.map v at hR
  simp only [leftRepresentative, Functor.map_comp, Category.assoc]
  rw [hL, ← hR]

private theorem rightRepresentative_naturality {X' X : C} {Y Y' : D}
    (u : X' ⟶ X) (v : Y ⟶ Y') (f : c.Q.obj X ⟶ U.obj (d.R.obj Y)) :
    c.localization.map u ≫ rightRepresentative eR f ≫ G.map (d.localization.map v) =
      rightRepresentative eR (c.Q.map u ≫ f ≫ U.map (d.R.map v)) := by
  have hL := (cofibrantComparison c).inv.naturality_assoc u
    (c.localization.map f ≫ eR.inv.app Y ≫ G.map (d.localization.map v))
  have hR := eR.inv.naturality v
  change c.localization.map u ≫ (cofibrantComparison c).inv.app X ≫ _ =
    (cofibrantComparison c).inv.app X' ≫ c.localization.map (c.Q.map u) ≫ _ at hL
  change c.localization.map (U.map (d.R.map v)) ≫ eR.inv.app Y' =
    eR.inv.app Y ≫ G.map (d.localization.map v) at hR
  simp only [rightRepresentative, Functor.map_comp, Category.assoc]
  rw [hL, ← hR]

private abbrev productLocalization := c.localization.op.prod d.localization

private abbrev productWeakEquivalences :=
  (weakEquivalences C).op.prod (weakEquivalences D)

private noncomputable def restrictedHomIso :
    productLocalization (c := c) (d := d) ⋙ homBifunctor.{v₁} F (𝟭 _) ≅
      productLocalization (c := c) (d := d) ⋙ homBifunctor.{v₂} (𝟭 _) G := by
  refine NatIso.ofComponents (fun X =>
    (Equiv.ulift.trans ((representativeEquiv h eL eR X.1.unop X.2).trans
      Equiv.ulift.symm)).toIso) ?_
  intro X Y m
  apply ConcreteCategory.hom_ext
  intro x
  change ULift.up (representativeEquiv h eL eR Y.1.unop Y.2
      (F.map (c.localization.map m.1.unop) ≫ x.down ≫ d.localization.map m.2)) =
    ULift.up (c.localization.map m.1.unop ≫ representativeEquiv h eL eR X.1.unop X.2 x.down ≫
      G.map (d.localization.map m.2))
  obtain ⟨f, hf⟩ := leftRepresentative_surjective h eL X.1.unop X.2 x.down
  rw [← hf, leftRepresentative_naturality, representativeEquiv_apply, representativeEquiv_apply,
    adj.homEquiv_naturality_left, adj.homEquiv_naturality_right, rightRepresentative_naturality]

local instance restrictLifting {E : Type*} [Category* E]
    (K : (HomotopyCategory C)ᵒᵖ × HomotopyCategory D ⥤ E) :
    Localization.Lifting (productLocalization (c := c) (d := d)) productWeakEquivalences
      (productLocalization (c := c) (d := d) ⋙ K) K :=
  ⟨Iso.refl _⟩

private noncomputable def localizedHomIso :
    homBifunctor.{v₁} F (𝟭 _) ≅ homBifunctor.{v₂} (𝟭 _) G :=
  Localization.liftNatIso (productLocalization (c := c) (d := d)) productWeakEquivalences
    _ _ _ _ (restrictedHomIso h eL eR)

private theorem localizedHomIso_app (X : C) (Y : D)
    (k : F.obj (c.localization.obj X) ⟶ d.localization.obj Y) :
    ((localizedHomIso h eL eR).hom.app (op (c.localization.obj X), d.localization.obj Y)
      (ULift.up k)).down = representativeEquiv h eL eR X Y k := by
  change ((localizedHomIso h eL eR).hom.app
    ((productLocalization (c := c) (d := d)).obj (op X, Y)) (ULift.up k)).down = _
  simp only [localizedHomIso, Localization.liftNatIso_hom, Localization.liftNatTrans_app,
    Localization.Lifting.iso, restrictLifting, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The derived adjunction for the specified functorial replacements. -/
noncomputable def IsQuillen.derivedAdjunction (h : IsQuillen adj)
    (c : Replacement C) (d : Replacement D) : DerivedAdjunctionData adj c d := by
  let F := Localization.lift _ (leftCompositeInverts c d h) c.localization
  let G := Localization.lift _ (rightCompositeInverts c d h) d.localization
  let eL : c.localization ⋙ F ≅ _ := Localization.fac _ (leftCompositeInverts c d h) c.localization
  let eR : d.localization ⋙ G ≅ _ := Localization.fac _ (rightCompositeInverts c d h) d.localization
  let a := adjunctionOfHomBifunctor (localizedHomIso h eL eR)
  refine ⟨F, G, eL, eR, a, ?_⟩
  intro X Y f k hk
  change k ≫ (fibrantComparison d).hom.app Y = eL.hom.app X ≫ d.localization.map f at hk
  have hk' : k = leftRepresentative eL f := by
    rw [← cancel_mono ((fibrantComparison d).hom.app Y), hk]
    simp only [leftRepresentative, Category.assoc, Iso.inv_hom_id_app]
    exact (congrArg (fun m => eL.hom.app X ≫ m) (Category.comp_id (d.localization.map f))).symm
  change (cofibrantComparison c).hom.app X ≫ a.homEquiv _ _ k ≫ eR.hom.app Y = _
  rw [hk', adjunctionOfHomBifunctor_homEquiv, localizedHomIso_app, representativeEquiv_apply]
  simp only [rightRepresentative, Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

/-- The localized replacement composites are adjoint, with a hom-set
bijection induced by ordinary adjunction on representatives. -/
theorem IsQuillen.nonempty_derivedAdjunction (h : IsQuillen adj)
    (c : Replacement C) (d : Replacement D) : Nonempty (DerivedAdjunctionData adj c d) :=
  ⟨h.derivedAdjunction c d⟩


variable (a : DerivedAdjunctionData adj c d)

/-- The computed map of the left derived functor, expressed in the comparison
coordinates. -/
theorem DerivedAdjunctionData.left_map {X X' : C} (f : X ⟶ X') :
    a.left.map (c.localization.map f) =
      a.leftComparison.hom.app X ≫ d.localization.map (L.map (c.Q.map f)) ≫
        a.leftComparison.inv.app X' := by
  have hn := a.leftComparison.hom.naturality_assoc f (a.leftComparison.inv.app X')
  change a.left.map (c.localization.map f) ≫ a.leftComparison.hom.app X' ≫
    a.leftComparison.inv.app X' = _ at hn
  rw [Iso.hom_inv_id_app] at hn
  exact (Category.comp_id _).symm.trans hn

/-- The computed map of the right derived functor, expressed in the comparison
coordinates. -/
theorem DerivedAdjunctionData.right_map {Y Y' : D} (f : Y ⟶ Y') :
    a.right.map (d.localization.map f) =
      a.rightComparison.hom.app Y ≫ c.localization.map (U.map (d.R.map f)) ≫
        a.rightComparison.inv.app Y' := by
  have hn := a.rightComparison.hom.naturality_assoc f (a.rightComparison.inv.app Y')
  change a.right.map (d.localization.map f) ≫ a.rightComparison.hom.app Y' ≫
    a.rightComparison.inv.app Y' = _ at hn
  rw [Iso.hom_inv_id_app] at hn
  exact (Category.comp_id _).symm.trans hn

/-- At a cofibrant object the localized left adjoint computes the derived one. -/
theorem DerivedAdjunctionData.isIso_leftComparison_cofibrant (h : IsQuillen adj)
    (X : C) [IsCofibrant X] :
    IsIso (a.leftComparison.hom.app X ≫ d.localization.map (L.map (c.p.app X))) := by
  have := c.cofibrant X
  have : IsIso (d.localization.map (L.map (c.p.app X))) :=
    Localization.inverts d.localization (weakEquivalences D) _
      (h.map_weakEquivalence_cofibrant (X' := X) _ (c.trivialFibration X).2)
  infer_instance

/-- At a fibrant object the localized right adjoint computes the derived one. -/
theorem DerivedAdjunctionData.isIso_rightComparison_fibrant (h : IsQuillen adj)
    (Y : D) [IsFibrant Y] :
    IsIso (c.localization.map (U.map (d.i.app Y)) ≫ a.rightComparison.inv.app Y) := by
  have := d.fibrant Y
  have : IsIso (c.localization.map (U.map (d.i.app Y))) :=
    Localization.inverts c.localization (weakEquivalences C) _
      (h.map_weakEquivalence_fibrant (Y := Y) _ (d.trivialCofibration Y).2)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- On a cofibrant source the derived unit is represented by the adjoint of
the fibrant replacement of its left adjoint image. -/
theorem DerivedAdjunctionData.unit_cofibrant (X : C) [IsCofibrant X] :
    a.adjunction.unit.app (c.localization.obj X) ≫
        a.right.map (a.leftComparison.hom.app X ≫ d.localization.map (L.map (c.p.app X))) ≫
        a.rightComparison.hom.app (L.obj X) =
      c.localization.map (adj.homEquiv X (d.R.obj (L.obj X)) (d.i.app (L.obj X))) := by
  let f := L.map (c.p.app X) ≫ d.i.app (L.obj X)
  let k := a.leftComparison.hom.app X ≫ d.localization.map (L.map (c.p.app X))
  have hk : k ≫ d.localization.map (d.i.app (L.obj X)) =
      a.leftComparison.hom.app X ≫ d.localization.map f := by
    simp only [k, f, Functor.map_comp, Category.assoc]
  have he := a.homEquiv_representative X (L.obj X) f k hk
  change c.localization.map (c.p.app X) ≫ a.adjunction.homEquiv _ _ k ≫
    a.rightComparison.hom.app (L.obj X) =
    c.localization.map (adj.homEquiv _ _ (L.map (c.p.app X) ≫ d.i.app (L.obj X))) at he
  rw [adj.homEquiv_naturality_left, c.localization.map_comp] at he
  have hp : IsIso (c.localization.map (show c.Q.obj X ⟶ X from c.p.app X)) :=
    Localization.inverts c.localization (weakEquivalences C) _ (c.trivialFibration X).2
  change c.localization.map (show c.Q.obj X ⟶ X from c.p.app X) ≫
    a.adjunction.homEquiv (c.localization.obj X) (d.localization.obj (L.obj X)) k ≫
    a.rightComparison.hom.app (L.obj X) =
    c.localization.map (show c.Q.obj X ⟶ X from c.p.app X) ≫
      c.localization.map (adj.homEquiv X (d.R.obj (L.obj X)) (d.i.app (L.obj X))) at he
  have eq : a.adjunction.homEquiv (c.localization.obj X) (d.localization.obj (L.obj X)) k ≫
      a.rightComparison.hom.app (L.obj X) = _ :=
    (cancel_epi (c.localization.map (show c.Q.obj X ⟶ X from c.p.app X))).1 he
  exact (Category.assoc (a.adjunction.unit.app (c.localization.obj X)) (a.right.map k)
    (a.rightComparison.hom.app (L.obj X))).symm.trans eq

set_option backward.isDefEq.respectTransparency false in
/-- On a fibrant target the derived counit is represented by the adjoint of
the cofibrant replacement of its right adjoint image. -/
theorem DerivedAdjunctionData.counit_fibrant (Y : D) [IsFibrant Y] :
    a.left.map (c.localization.map (U.map (d.i.app Y)) ≫ a.rightComparison.inv.app Y) ≫
        a.adjunction.counit.app (d.localization.obj Y) =
      a.leftComparison.hom.app (U.obj Y) ≫ d.localization.map
        ((adj.homEquiv (c.Q.obj (U.obj Y)) Y).symm (c.p.app (U.obj Y))) := by
  let g := (adj.homEquiv (c.Q.obj (U.obj Y)) Y).symm (c.p.app (U.obj Y))
  let k := a.leftComparison.hom.app (U.obj Y) ≫ d.localization.map g
  have hk : k ≫ d.localization.map (d.i.app Y) =
      a.leftComparison.hom.app (U.obj Y) ≫ d.localization.map (g ≫ d.i.app Y) := by
    simp only [k, Functor.map_comp, Category.assoc]
  have he := a.homEquiv_representative (U.obj Y) Y (g ≫ d.i.app Y) k hk
  change c.localization.map (c.p.app (U.obj Y)) ≫ a.adjunction.homEquiv _ _ k ≫
    a.rightComparison.hom.app Y = c.localization.map (adj.homEquiv _ _ (g ≫ d.i.app Y)) at he
  rw [adj.homEquiv_naturality_right, show adj.homEquiv _ Y g = c.p.app (U.obj Y)
    from Equiv.apply_symm_apply _ _, c.localization.map_comp] at he
  let e := a.adjunction.homEquiv (c.localization.obj (U.obj Y)) (d.localization.obj Y)
  have hp : IsIso (c.localization.map (show c.Q.obj (U.obj Y) ⟶ U.obj Y from c.p.app (U.obj Y))) :=
    Localization.inverts c.localization (weakEquivalences C) _ (c.trivialFibration (U.obj Y)).2
  change c.localization.map (show c.Q.obj (U.obj Y) ⟶ U.obj Y from c.p.app (U.obj Y)) ≫
    e k ≫ a.rightComparison.hom.app Y = _ at he
  have eq : e k ≫ a.rightComparison.hom.app Y = c.localization.map (U.map (d.i.app Y)) :=
    (cancel_epi _).1 he
  have he' : e k =
      c.localization.map (U.map (d.i.app Y)) ≫ a.rightComparison.inv.app Y := by
    apply (cancel_mono (a.rightComparison.hom.app Y)).mp
    rw [Category.assoc, Iso.inv_hom_id_app]
    exact eq.trans (Category.comp_id _).symm
  change e.symm (c.localization.map (U.map (d.i.app Y)) ≫ a.rightComparison.inv.app Y) = k
  exact (congrArg e.symm he'.symm).trans (Equiv.symm_apply_apply e k)

end Derived

end DerivedFormalization.Model
