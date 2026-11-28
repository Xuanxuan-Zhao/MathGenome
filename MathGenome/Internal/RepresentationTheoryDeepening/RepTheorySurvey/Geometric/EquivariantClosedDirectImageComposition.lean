import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.EquivariantClosedDirectImageComposition

import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.EquivariantIntersectionComplexes
noncomputable section

namespace RepTheorySurvey.Geometric.EquivariantClosedDirectImageComposition

open CategoryTheory
open Analytic Analytic.IntersectionComplex LocalSheaf

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 550000

section
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
variable {E : B ⥤ A} {V : D ⥤ C} {J : A ⥤ C} {K : B ⥤ D}
variable {S : C ⥤ A} {R : D ⥤ B} (σ : E ⋙ J ≅ K ⋙ V) (a : J ⊣ S) (b : K ⊣ R)

private theorem mate_counit (F : D) :
    J.map (adjointSquareMap σ a b F) ≫ a.counit.app _ =
      σ.hom.app (R.obj F) ≫ V.map (b.counit.app F) := by
  exact (a.homEquiv_counit (g := adjointSquareMap σ a b F)).symm.trans
    (Equiv.symm_apply_apply (a.homEquiv _ _) _)

@[reassoc]
private theorem mate_naturality {F G : D} (u : F ⟶ G) :
    E.map (R.map u) ≫ adjointSquareMap σ a b G =
      adjointSquareMap σ a b F ≫ S.map (V.map u) := by
  unfold adjointSquareMap
  rw [← a.homEquiv_naturality_left, ← a.homEquiv_naturality_right]
  congr 1
  rw [← Functor.comp_map E J, σ.hom.naturality_assoc]
  change σ.hom.app (R.obj F) ≫ V.map (K.map (R.map u)) ≫ V.map (b.counit.app G) = _
  rw [← Functor.map_comp, b.counit_naturality u, Functor.map_comp, Category.assoc]

private theorem mate_change_right {R' : D ⥤ B} (b' : K ⊣ R') (F : D) :
    adjointSquareMap σ a b F =
      E.map ((b.rightAdjointUniq b').hom.app F) ≫ adjointSquareMap σ a b' F := by
  apply (a.homEquiv _ _).symm.injective
  rw [a.homEquiv_naturality_left_symm, adjointSquareMap, Equiv.symm_apply_apply]
  rw [adjointSquareMap, Equiv.symm_apply_apply]
  rw [← Functor.comp_map E J, σ.hom.naturality_assoc]
  change _ = σ.hom.app (R.obj F) ≫
    V.map (K.map ((b.rightAdjointUniq b').hom.app F)) ≫ V.map (b'.counit.app F)
  rw [← Functor.map_comp, Adjunction.rightAdjointUniq_hom_app_counit]

end

section
variable {A B C D E F : Type*}
variable [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
variable {V₁ : A ⥤ D} {V₂ : B ⥤ E} {V₃ : C ⥤ F}
variable {K₁ : B ⥤ A} {K₂ : C ⥤ B} {J₁ : E ⥤ D} {J₂ : F ⥤ E}
variable {R₁ : A ⥤ B} {R₂ : B ⥤ C} {S₁ : D ⥤ E} {S₂ : E ⥤ F}
variable (a₁ : J₁ ⊣ S₁) (a₂ : J₂ ⊣ S₂) (b₁ : K₁ ⊣ R₁) (b₂ : K₂ ⊣ R₂)
variable (σ₁ : V₂ ⋙ J₁ ≅ K₁ ⋙ V₁) (σ₂ : V₃ ⋙ J₂ ≅ K₂ ⋙ V₂)

private def paste :
    V₃ ⋙ (J₂ ⋙ J₁) ≅ (K₂ ⋙ K₁) ⋙ V₁ :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight σ₂ J₁ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft K₂ σ₁ ≪≫
    (Functor.associator _ _ _).symm

private theorem mate_paste (P : A) :
    adjointSquareMap (paste σ₁ σ₂) (a₂.comp a₁) (b₂.comp b₁) P =
      adjointSquareMap σ₂ a₂ b₂ (R₁.obj P) ≫ S₂.map (adjointSquareMap σ₁ a₁ b₁ P) := by
  apply ((a₂.comp a₁).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [mate_counit]
  simp only [paste, Adjunction.comp_counit_app, Functor.comp_map, Functor.comp_obj,
    Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Iso.symm_hom, Category.id_comp, Category.comp_id, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc, Functor.map_comp]
  let u := adjointSquareMap σ₁ a₁ b₁ P
  let w := adjointSquareMap σ₂ a₂ b₂ (R₁.obj P)
  have hn : J₂.map (S₂.map u) ≫ a₂.counit.app _ = a₂.counit.app _ ≫ u :=
    a₂.counit_naturality u
  have h₁ : J₁.map (J₂.map (S₂.map u)) ≫ J₁.map (a₂.counit.app _) =
      J₁.map (a₂.counit.app _) ≫ J₁.map u := by
    rw [← J₁.map_comp, hn, J₁.map_comp]
  have h₂ : J₁.map (J₂.map w) ≫ J₁.map (a₂.counit.app _) =
      J₁.map (σ₂.hom.app (R₂.obj (R₁.obj P))) ≫ J₁.map (V₂.map (b₂.counit.app _)) := by
    rw [← J₁.map_comp, mate_counit σ₂ a₂ b₂, J₁.map_comp]
  rw [reassoc_of% h₁, reassoc_of% h₂, mate_counit σ₁ a₁ b₁]
  have h₃ : J₁.map (V₂.map (b₂.counit.app (R₁.obj P))) ≫ σ₁.hom.app (R₁.obj P) =
      σ₁.hom.app (K₂.obj (R₂.obj (R₁.obj P))) ≫ V₁.map (K₁.map (b₂.counit.app (R₁.obj P))) :=
    σ₁.hom.naturality _
  rw [reassoc_of% h₃]

end

section
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
variable {E : B ⥤ A} {V : D ⥤ C} {J : A ⥤ C} {K : B ⥤ D}
variable {S S' : C ⥤ A} {R R' : D ⥤ B}
variable {J' : A ⥤ C} {K' : B ⥤ D}
variable (σ : E ⋙ J ≅ K ⋙ V) (a : J ⊣ S) (b : K ⊣ R)
variable (cJ : J' ≅ J) (cK : K' ≅ K) (a' : J' ⊣ S') (b' : K' ⊣ R')

private def transportSquare : E ⋙ J' ≅ K' ⋙ V :=
  Functor.isoWhiskerLeft E cJ ≪≫ σ ≪≫ Functor.isoWhiskerRight cK.symm V

private theorem mate_transport (P : D) :
    adjointSquareMap (transportSquare σ cJ cK) (a.ofNatIsoLeft cJ.symm)
      (b.ofNatIsoLeft cK.symm) P = adjointSquareMap σ a b P := by
  unfold adjointSquareMap
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
  congr 1
  simp only [transportSquare, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app_assoc, Adjunction.ofNatIsoLeft_counit,
    Functor.comp_obj, Iso.symm_inv, Iso.inv_hom_id_app_assoc, ← Functor.map_comp]

private theorem mate_adjust_target (σ' : E ⋙ J' ≅ K' ⋙ V) (d : K' ⊣ R) (P : D) :
    adjointSquareMap σ' a' d P ≫ (a'.rightAdjointUniq (a.ofNatIsoLeft cJ.symm)).hom.app _ =
      adjointSquareMap σ' (a.ofNatIsoLeft cJ.symm) d P := by
  let a₀ := a.ofNatIsoLeft cJ.symm
  apply (a₀.homEquiv _ _).symm.injective
  rw [a₀.homEquiv_naturality_left_symm, Adjunction.homEquiv_symm_rightAdjointUniq_hom_app]
  rw [← a'.homEquiv_counit, adjointSquareMap, Equiv.symm_apply_apply,
    adjointSquareMap, Equiv.symm_apply_apply]

private theorem mate_adjust (P : D) :
    adjointSquareMap (transportSquare σ cJ cK) a' b' P ≫
      (a'.rightAdjointUniq (a.ofNatIsoLeft cJ.symm)).hom.app _ =
    E.map ((b'.rightAdjointUniq (b.ofNatIsoLeft cK.symm)).hom.app P) ≫
      adjointSquareMap σ a b P := by
  rw [mate_change_right _ _ _ (b.ofNatIsoLeft cK.symm), Category.assoc,
    mate_adjust_target a cJ a', mate_transport]

end
section Pullbacks
variable {W X Y Z : TopCat.{0}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)

private theorem inverseImageComposition_assoc (K : Sheaves Z) :
    (inverseImageComposition (f ≫ g) h).hom.app K ≫
      (inverseImageComposition f g).hom.app ((inverseImage h).obj K) =
    (inverseImageComposition f (g ≫ h)).hom.app K ≫
      (inverseImage f).map ((inverseImageComposition g h).hom.app K) := by
  let a := inverseDirectAdjunction f
  let b := inverseDirectAdjunction g
  let c := inverseDirectAdjunction h
  let d := inverseDirectAdjunction (f ≫ g)
  let e := inverseDirectAdjunction (g ≫ h)
  let s := inverseDirectAdjunction (f ≫ g ≫ h)
  change (s.leftAdjointUniq (c.comp d)).hom.app K ≫
      (d.leftAdjointUniq (b.comp a)).hom.app _ =
    (s.leftAdjointUniq (e.comp a)).hom.app K ≫
      (inverseImage f).map ((e.leftAdjointUniq (c.comp b)).hom.app K)
  apply (s.homEquiv _ _).injective
  rw [s.homEquiv_naturality_right, s.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.comp_unit_app, Adjunction.comp_unit_app]
  change (c.unit.app K ≫ (directImage h).map (d.unit.app _)) ≫
      (directImage h).map ((directImage (f ≫ g)).map ((d.leftAdjointUniq (b.comp a)).hom.app ((inverseImage h).obj K))) =
    (e.unit.app K ≫ (directImage (g ≫ h)).map (a.unit.app _)) ≫
      (directImage (g ≫ h)).map ((directImage f).map ((inverseImage f).map ((e.leftAdjointUniq (c.comp b)).hom.app K)))
  rw [Category.assoc, ← Functor.map_comp, Adjunction.unit_leftAdjointUniq_hom_app]
  rw [Category.assoc, ← Functor.map_comp,
    ← Functor.comp_map (inverseImage f) (directImage f), ← a.unit.naturality,
    Functor.map_comp, ← Category.assoc, Functor.id_map]
  have he := Adjunction.unit_leftAdjointUniq_hom_app e (c.comp b) K
  rw [he]
  simp only [Adjunction.comp_unit_app, Category.assoc, Functor.map_comp]
  rfl

private abbrev Cx (T : TopCat.{0}) := CochainComplex (Sheaves T) ℤ

private abbrev pullD {X Y : TopCat.{0}} (f : X ⟶ Y) := (inverseImage f).mapDerivedCategory
local notation "L" => pullD
local notation "l" => inverseImage
local notation "Q" => DerivedCategory.Q
local notation "M" => Functor.mapHomologicalComplex
local notation "fac" => Functor.mapDerivedCategoryFactors
local notation "μ" => derivedInverseImageComposition
local notation "μ₀" => inverseImageComposition

private theorem compComplex {A B C : TopCat.{0}} (x : A ⟶ B) (y : B ⟶ C) (K : Cx C) :
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (l y ⋙ l x)) (.up ℤ)).hom.app K = 𝟙 _ := by
  ext n
  rfl

@[reassoc]
private theorem derivedComp_factor {W X Y : TopCat.{0}} (f : W ⟶ X) (g : X ⟶ Y) (K : Cx Y) :
    (μ f g).hom.app (DerivedCategory.Q.obj K) ≫ (L f).map ((fac (l g)).hom.app K) ≫
      (fac (l f)).hom.app ((M (l g) (.up ℤ)).obj K) =
    (fac (l (f ≫ g))).hom.app K ≫
      DerivedCategory.Q.map (((μ₀ f g).hom.mapHomologicalComplex (.up ℤ)).app K) := by
  let c := Functor.mapDerivedCategoryCompIso (l g) (l f)
  have hc := Functor.mapDerivedCategoryCompIso_hom_app_Q_obj (l g) (l f) K
  have hh : (μ f g).hom.app (DerivedCategory.Q.obj K) ≫ c.hom.app (DerivedCategory.Q.obj K) =
      (fac (l (f ≫ g))).hom.app K ≫
        DerivedCategory.Q.map (((μ₀ f g).hom.mapHomologicalComplex (.up ℤ)).app K) ≫
          (fac (l g ⋙ l f)).inv.app K := by
    dsimp only [c]
    unfold derivedInverseImageComposition
    simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id_app, Category.comp_id]
    exact NatTrans.mapDerivedCategory_app_Q_obj (μ₀ f g).hom K
  rw [← cancel_mono ((fac (l g ⋙ l f)).inv.app K)]
  simp only [Category.assoc]
  rw [← hh]
  rw [hc, compComplex]
  erw [DerivedCategory.Q.map_id, Category.id_comp]

private theorem derivedComp_assoc_Q (K : Cx Z) :
    (μ (f ≫ g) h).hom.app (DerivedCategory.Q.obj K) ≫ (μ f g).hom.app ((L h).obj (DerivedCategory.Q.obj K)) =
    (μ f (g ≫ h)).hom.app (DerivedCategory.Q.obj K) ≫ (L f).map ((μ g h).hom.app (DerivedCategory.Q.obj K)) := by
  let Kh := (M (l h) (.up ℤ)).obj K
  let Kgh := (M (l g) (.up ℤ)).obj Kh
  let E := (L f).map ((L g).map ((fac (l h)).hom.app K)) ≫
    (L f).map ((fac (l g)).hom.app Kh) ≫ (fac (l f)).hom.app Kgh
  rw [← cancel_mono E]
  dsimp only [E]
  have hn := (μ f g).hom.naturality ((fac (l h)).hom.app K)
  simp only [Category.assoc]
  erw [← reassoc_of% hn]
  erw [derivedComp_factor f g Kh]
  erw [derivedComp_factor_assoc (f ≫ g) h K]
  let u := (μ g h).hom.app (DerivedCategory.Q.obj K)
  let v := (L g).map ((fac (l h)).hom.app K)
  let w := (fac (l g)).hom.app Kh
  have group : (L f).map u ≫ (L f).map v ≫ (L f).map w = (L f).map (u ≫ v ≫ w) := by
    simp only [Functor.map_comp]
  rw [reassoc_of% group]
  erw [derivedComp_factor g h K]
  let τ := ((μ₀ g h).hom.mapHomologicalComplex (.up ℤ)).app K
  rw [(L f).map_comp]
  simp only [Category.assoc]
  have ht := (fac (l f)).hom.naturality τ
  erw [ht, derivedComp_factor_assoc f (g ≫ h) K]
  simp only [Functor.comp_map]
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  congr 2
  ext n : 1
  exact inverseImageComposition_assoc f g h (K.X n)

private theorem derivedComp_assoc (K : Derived Z) :
    (μ (f ≫ g) h).hom.app K ≫ (μ f g).hom.app ((L h).obj K) =
    (μ f (g ≫ h)).hom.app K ≫ (L f).map ((μ g h).hom.app K) := by
  let p := (μ (f ≫ g) h).hom ≫ Functor.whiskerLeft (L h) (μ f g).hom
  let q := (μ f (g ≫ h)).hom ≫ Functor.whiskerRight (μ g h).hom (L f)
  have pq : p = q := by
    apply Localization.natTrans_ext (DerivedCategory.Q (C := Sheaves Z))
      (HomologicalComplex.quasiIso (Sheaves Z) (.up ℤ))
    intro K
    exact derivedComp_assoc_Q f g h K
  exact congr_app pq K

private theorem pullbackComp_assoc (K : BoundedBelow Z) :
    (boundedBelowPullbackComposition (f ≫ g) h).hom.app K ≫
      (boundedBelowPullbackComposition f g).hom.app ((boundedBelowInverseImage h).obj K) =
    (boundedBelowPullbackComposition f (g ≫ h)).hom.app K ≫
      (boundedBelowInverseImage f).map ((boundedBelowPullbackComposition g h).hom.app K) := by
  apply ObjectProperty.hom_ext
  exact derivedComp_assoc f g h K.obj

end Pullbacks

section Squares

variable {U₁ U₂ U₃ X₁ X₂ X₃ : TopCat.{0}}
  {j₁ : U₁ ⟶ U₂} {j₂ : U₂ ⟶ U₃} {k₁ : X₁ ⟶ X₂} {k₂ : X₂ ⟶ X₃}
  {e₁ : U₁ ⟶ X₁} {e₂ : U₂ ⟶ X₂} {e₃ : U₃ ⟶ X₃}

private theorem paste_comm (s₁ : j₁ ≫ e₂ = e₁ ≫ k₁) (s₂ : j₂ ≫ e₃ = e₂ ≫ k₂) :
    (j₁ ≫ j₂) ≫ e₃ = e₁ ≫ (k₁ ≫ k₂) :=
  (congrArg (j₁ ≫ ·) s₂).trans (congrArg (· ≫ k₂) s₁)

variable (P : ∀ {A B : TopCat.{0}}, (A ⟶ B) → BoundedBelow B ⥤ BoundedBelow A)
  (m : ∀ {A B C : TopCat.{0}} (f : A ⟶ B) (g : B ⟶ C),
    P (f ≫ g) ≅ P g ⋙ P f)

private abbrev pullbackTransport {A B : TopCat.{0}} {p q : A ⟶ B} (eq : p = q) (K : BoundedBelow B) :
    (P p).obj K ⟶ (P q).obj K :=
  eqToHom (congrArg (fun t => (P t).obj K) eq)

private theorem map_transport {A B C : TopCat.{0}} (t : A ⟶ B) {p q : B ⟶ C}
    (eq : p = q) (K : BoundedBelow C) :
    (m t p).hom.app K ≫ (P t).map (pullbackTransport P eq K) =
      pullbackTransport P (congrArg (t ≫ ·) eq) K ≫ (m t q).hom.app K := by
  subst q
  simp

private theorem transport_app {A B C : TopCat.{0}} {p q : A ⟶ B} (r : B ⟶ C)
    (eq : p = q) (K : BoundedBelow C) :
    (m p r).hom.app K ≫ pullbackTransport P eq ((P r).obj K) =
      pullbackTransport P (congrArg (· ≫ r) eq) K ≫ (m q r).hom.app K := by
  subst q
  simp

@[reassoc]
private theorem pullbackTransport_trans {A B : TopCat.{0}} {p q r : A ⟶ B}
    (a : p = q) (b : q = r) (K : BoundedBelow B) :
    pullbackTransport P a K ≫ pullbackTransport P b K = pullbackTransport P (a.trans b) K := by
  subst q
  subst r
  simp [pullbackTransport]

private def generalPullbackSquare (s : j₁ ≫ e₂ = e₁ ≫ k₁) :
    P e₂ ⋙ P j₁ ≅ P k₁ ⋙ P e₁ :=
  (m j₁ e₂).symm ≪≫ eqToIso (congrArg (fun t => P t) s) ≪≫ m e₁ k₁

private theorem pullbackSquare_app (s : j₁ ≫ e₂ = e₁ ≫ k₁) (K : BoundedBelow X₂) :
    (generalPullbackSquare P m s).hom.app K =
      (m j₁ e₂).inv.app K ≫ pullbackTransport P s K ≫ (m e₁ k₁).hom.app K := by
  simp only [generalPullbackSquare, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    eqToIso.hom, eqToHom_app, pullbackTransport]

variable (assocPB : ∀ {A B C D : TopCat.{0}} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D)
  (K : BoundedBelow D), (m (f ≫ g) h).hom.app K ≫ (m f g).hom.app ((P h).obj K) =
  (m f (g ≫ h)).hom.app K ≫ (P f).map ((m g h).hom.app K))

include assocPB in
private theorem pullbackSquare_pasting
    (s₁ : j₁ ≫ e₂ = e₁ ≫ k₁) (s₂ : j₂ ≫ e₃ = e₂ ≫ k₂) (K : BoundedBelow X₃) :
    (generalPullbackSquare P m (paste_comm s₁ s₂)).hom.app K ≫ (P e₁).map ((m k₁ k₂).hom.app K) =
    (m j₁ j₂).hom.app ((P e₃).obj K) ≫ (P j₁).map ((generalPullbackSquare P m s₂).hom.app K) ≫
      (generalPullbackSquare P m s₁).hom.app ((P k₂).obj K) := by
  rw [← cancel_epi ((m (j₁ ≫ j₂) e₃).hom.app K)]
  simp only [pullbackSquare_app P m, Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% (assocPB j₁ j₂ e₃ K)]
  -- Cancel the decomposition of the second square after reassociating the pullbacks.
  have undo₂ :
      (P j₁).map ((m j₂ e₃).hom.app K) ≫ (P j₁).map ((m j₂ e₃).inv.app K) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    exact (P j₁).map_id _
  rw [reassoc_of% undo₂, reassoc_of% (map_transport P m j₁ s₂ K)]
  rw [← reassoc_of% (assocPB j₁ e₂ k₂ K), Iso.hom_inv_id_app_assoc,
    reassoc_of% (transport_app P m k₂ s₁ K)]
  rw [← assocPB e₁ k₁ k₂ K]
  exact (pullbackTransport_trans_assoc P (congrArg (j₁ ≫ ·) s₂) (congrArg (· ≫ k₂) s₁) K
    ((m (e₁ ≫ k₁) k₂).hom.app K ≫ (m e₁ k₁).hom.app ((P k₂).obj K))).symm

include assocPB in
private theorem pullbackSquare_general_paste
    (s₁ : j₁ ≫ e₂ = e₁ ≫ k₁) (s₂ : j₂ ≫ e₃ = e₂ ≫ k₂) :
    generalPullbackSquare P m (paste_comm s₁ s₂) =
      transportSquare (paste (generalPullbackSquare P m s₁) (generalPullbackSquare P m s₂))
        (m j₁ j₂) (m k₁ k₂) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  rw [← cancel_mono ((P e₁).map ((m k₁ k₂).hom.app K))]
  rw [pullbackSquare_pasting P m assocPB s₁ s₂ K]
  simp only [transportSquare, paste, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj,
    Category.id_comp, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  rw [(P e₁).map_id, Category.comp_id]

end Squares

local notation "P" => boundedBelowInverseImage
local notation "m" => boundedBelowPullbackComposition

open RepTheorySurvey.Geometric.EquivariantIntersectionComplexesSpecs
open RepTheorySurvey.Geometric.EquivariantClosedDirectImageCompositionSpecs
open RepTheorySurvey.Geometric.LocalSheaf
open RepTheorySurvey.Geometric.ClosedEquivarianceExtensionSpecs
  (above parameterInclusion projectionSquare)

local notation "R" => derivedDirectImage

private def pushComposition (a : DerivedAdjunctions) {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    R (f ≫ g) ≅ R f ⋙ R g :=
  (a (f ≫ g)).rightAdjointUniq (((a g).comp (a f)).ofNatIsoLeft (m f g).symm)

section Pasting

variable {U₁ U₂ U₃ X₁ X₂ X₃ : TopCat.{0}}
  {j₁ : U₁ ⟶ U₂} {j₂ : U₂ ⟶ U₃} {k₁ : X₁ ⟶ X₂} {k₂ : X₂ ⟶ X₃}
  {e₁ : U₁ ⟶ X₁} {e₂ : U₂ ⟶ X₂} {e₃ : U₃ ⟶ X₃}

private theorem pullbackSquare_paste
    (s₁ : j₁ ≫ e₂ = e₁ ≫ k₁) (s₂ : j₂ ≫ e₃ = e₂ ≫ k₂) :
    pullbackSquare (paste_comm s₁ s₂) =
      transportSquare (paste (pullbackSquare s₁) (pullbackSquare s₂))
        (m j₁ j₂) (m k₁ k₂) :=
  pullbackSquare_general_paste boundedBelowInverseImage boundedBelowPullbackComposition
    pullbackComp_assoc s₁ s₂

private theorem directImageComparison_paste (a : DerivedAdjunctions)
    (s₁ : j₁ ≫ e₂ = e₁ ≫ k₁) (s₂ : j₂ ≫ e₃ = e₂ ≫ k₂) (K : BoundedBelow X₁) :
    directImageComparison (paste_comm s₁ s₂) (a (j₁ ≫ j₂)) (a (k₁ ≫ k₂)) K ≫
      (pushComposition a j₁ j₂).hom.app _ =
    (P e₃).map ((pushComposition a k₁ k₂).hom.app K) ≫
      directImageComparison s₂ (a j₂) (a k₂) ((R k₁).obj K) ≫
        (R j₂).map (directImageComparison s₁ (a j₁) (a k₁) K) := by
  unfold directImageComparison
  rw [pullbackSquare_paste s₁ s₂]
  unfold pushComposition
  rw [mate_adjust, mate_paste]

private abbrev compare (a : DerivedAdjunctions) (s : j₁ ≫ e₂ = e₁ ≫ k₁)
    {F : BoundedBelow X₁} {G : BoundedBelow X₂} (c : (R k₁).obj F ≅ G) :
    (P e₂).obj G ⟶ (R j₁).obj ((P e₁).obj F) :=
  (P e₂).map c.inv ≫ directImageComparison s (a j₁) (a k₁) F

private theorem compare_paste (a : DerivedAdjunctions)
    (s₁ : j₁ ≫ e₂ = e₁ ≫ k₁) (s₂ : j₂ ≫ e₃ = e₂ ≫ k₂)
    {F : BoundedBelow X₁} {G : BoundedBelow X₂} {K : BoundedBelow X₃}
    (c₁ : (R k₁).obj F ≅ G) (c₂ : (R k₂).obj G ≅ K) :
    compare a (paste_comm s₁ s₂)
      ((pushComposition a k₁ k₂).app F ≪≫ (R k₂).mapIso c₁ ≪≫ c₂) ≫
        (pushComposition a j₁ j₂).hom.app _ =
    compare a s₂ c₂ ≫ (R j₂).map (compare a s₁ c₁) := by
  simp only [compare, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Functor.map_comp,
    Category.assoc]
  rw [directImageComparison_paste a s₁ s₂ F]
  have cancel :
      (P e₃).map ((pushComposition a k₁ k₂).inv.app F) ≫
        (P e₃).map ((pushComposition a k₁ k₂).hom.app F) = 𝟙 _ := by
    rw [← (P e₃).map_comp, (pushComposition a k₁ k₂).inv_hom_id_app F, (P e₃).map_id]
  rw [reassoc_of% cancel]
  simp only [directImageComparison]
  rw [mate_naturality_assoc (pullbackSquare s₂) (a j₂) (a k₂) c₁.inv]

end Pasting

private theorem jetMapsCommute_comp {J : JetSystem.{0}} {X Y Z : TopCat.{0}}
    {A : JetAction J X} {B : JetAction J Y} {C : JetAction J Z} {f : X ⟶ Y} {g : Y ⟶ Z}
    (_hab : A.cutoff ≤ B.cutoff) (hbc : B.cutoff ≤ C.cutoff)
    (hf : JetMapsCommute A B f) (hg : JetMapsCommute B C g) :
    JetMapsCommute A C (f ≫ g) := by
  intro k hx hz
  exact paste_comm (hf k hx (hbc.trans hz)) (hg k (hbc.trans hz) hz)

private theorem from_intertwining {A B : Type*} [Category* A] [Category* B]
    {L M : A ⥤ B} {U V : A} {W D : B} (c : U ≅ V)
    (η : L.obj V ⟶ M.obj V) (p : M.obj U ⟶ W) (q : L.obj U ⟶ D) (r : D ⟶ W)
    (h : L.map c.hom ≫ η ≫ M.map c.inv ≫ p = q ≫ r) :
    η ≫ (M.map c.inv ≫ p) = (L.map c.inv ≫ q) ≫ r := by
  have hh := congrArg (L.map c.inv ≫ ·) h
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id] at hh
  rw [L.map_id V, Category.id_comp] at hh
  simpa only [Category.assoc] using hh

private theorem to_intertwining {A B : Type*} [Category* A] [Category* B]
    {L M : A ⥤ B} {U V : A} {W D : B} (c : U ≅ V)
    (η : L.obj V ⟶ M.obj V) (p : M.obj U ⟶ W) (q : L.obj U ⟶ D) (r : D ⟶ W)
    (h : η ≫ (M.map c.inv ≫ p) = (L.map c.inv ≫ q) ≫ r) :
    L.map c.hom ≫ η ≫ M.map c.inv ≫ p = q ≫ r := by
  have hh := congrArg (L.map c.hom ≫ ·) h
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id] at hh
  rw [L.map_id U, Category.id_comp] at hh
  exact hh

private theorem comparison_isIso {A B : Type*} [Category* A] [Category* B]
    {L : A ⥤ B} {U V : A} {D E : B}
    (c : U ≅ V) (d : L.obj U ⟶ D) (q : D ≅ E)
    (p : L.obj V ⟶ E) [IsIso p] (h : (L.map c.inv ≫ d) ≫ q.hom = p) :
    IsIso d := by
  have h' : IsIso ((L.map c.inv ≫ d) ≫ q.hom) := h.symm ▸ inferInstance
  exact (isIso_comp_left_iff _ _).mp ((isIso_comp_right_iff _ _).mp h')

private theorem paste_intertwining {A B C : Type*} [Category* A] [Category* B] [Category* C]
    {R₁ : A ⥤ B} {R₂ : B ⥤ C} {R₀ : A ⥤ C} (q : R₀ ≅ R₁ ⋙ R₂)
    {U₁ V₁ : A} {U₂ V₂ : B} {U₃ V₃ : C}
    (γ₁ : U₁ ⟶ V₁) (γ₂ : U₂ ⟶ V₂) (γ₃ : U₃ ⟶ V₃)
    {a₁ : U₂ ⟶ R₁.obj U₁} {p₁ : V₂ ⟶ R₁.obj V₁}
    {a₂ : U₃ ⟶ R₂.obj U₂} {p₂ : V₃ ⟶ R₂.obj V₂}
    {a : U₃ ⟶ R₀.obj U₁} {p : V₃ ⟶ R₀.obj V₁}
    (h₁ : γ₂ ≫ p₁ = a₁ ≫ R₁.map γ₁) (h₂ : γ₃ ≫ p₂ = a₂ ≫ R₂.map γ₂)
    (ha : a ≫ q.hom.app U₁ = a₂ ≫ R₂.map a₁)
    (hp : p ≫ q.hom.app V₁ = p₂ ≫ R₂.map p₁) :
    γ₃ ≫ p = a ≫ R₀.map γ₁ := by
  apply (cancel_mono (q.hom.app V₁)).mp
  rw [Category.assoc, hp, Category.assoc, q.hom.naturality γ₁,
    ← Category.assoc a, ha]
  simp only [Functor.comp_map, Category.assoc]
  rw [reassoc_of% h₂, ← Functor.map_comp, h₁, Functor.map_comp]

/-- The action and projection mates with their intertwining equation at a fixed level. -/
private def DirectImageComparisonAt {U V X Y : TopCat.{0}}
    (a : DerivedAdjunctions) {j : U ⟶ V} {k : X ⟶ Y}
    {e₁ p₁ : U ⟶ X} {e₂ p₂ : V ⟶ Y}
    (ha : j ≫ e₂ = e₁ ≫ k) (hp : j ≫ p₂ = p₁ ≫ k)
    {F : BoundedBelow X} {G : BoundedBelow Y} (c : (R k).obj F ≅ G)
    (γ₁ : (P e₁).obj F ⟶ (P p₁).obj F) (γ₂ : (P e₂).obj G ⟶ (P p₂).obj G) : Prop :=
  let act := directImageComparison ha (a j) (a k) F
  let proj := directImageComparison hp (a j) (a k) F
  IsIso act ∧ IsIso proj ∧
    (P e₂).map c.hom ≫ γ₂ ≫ (P p₂).map c.inv ≫ proj = act ≫ (R j).map γ₁

private theorem directImageComparisonAt_paste {U V T X Y Z : TopCat.{0}}
    (a : DerivedAdjunctions) {j₁ : U ⟶ V} {j₂ : V ⟶ T} {f : X ⟶ Y} {g : Y ⟶ Z}
    {e₁ p₁ : U ⟶ X} {e₂ p₂ : V ⟶ Y} {e₃ p₃ : T ⟶ Z}
    (a₁ : j₁ ≫ e₂ = e₁ ≫ f) (a₂ : j₂ ≫ e₃ = e₂ ≫ g)
    (b₁ : j₁ ≫ p₂ = p₁ ≫ f) (b₂ : j₂ ≫ p₃ = p₂ ≫ g)
    {F : BoundedBelow X} {G : BoundedBelow Y} {K : BoundedBelow Z}
    (c₁ : (R f).obj F ≅ G) (c₂ : (R g).obj G ≅ K)
    {γ₁ : (P e₁).obj F ⟶ (P p₁).obj F} {γ₂ : (P e₂).obj G ⟶ (P p₂).obj G}
    {γ₃ : (P e₃).obj K ⟶ (P p₃).obj K}
    (h₁ : DirectImageComparisonAt a a₁ b₁ c₁ γ₁ γ₂)
    (h₂ : DirectImageComparisonAt a a₂ b₂ c₂ γ₂ γ₃) :
    DirectImageComparisonAt a (paste_comm a₁ a₂) (paste_comm b₁ b₂)
      ((pushComposition a f g).app F ≪≫ (R g).mapIso c₁ ≪≫ c₂) γ₁ γ₃ := by
  let c := (pushComposition a f g).app F ≪≫ (R g).mapIso c₁ ≪≫ c₂
  let act := directImageComparison (paste_comm a₁ a₂) (a (j₁ ≫ j₂)) (a (f ≫ g)) F
  let proj := directImageComparison (paste_comm b₁ b₂) (a (j₁ ≫ j₂)) (a (f ≫ g)) F
  let q := pushComposition a j₁ j₂
  obtain ⟨ha₁, hp₁, hh₁⟩ := h₁
  obtain ⟨ha₂, hp₂, hh₂⟩ := h₂
  have ih₁ : γ₂ ≫ compare a b₁ c₁ = compare a a₁ c₁ ≫ (R j₁).map γ₁ :=
    from_intertwining c₁ γ₂ _ _ _ hh₁
  have ih₂ : γ₃ ≫ compare a b₂ c₂ = compare a a₂ c₂ ≫ (R j₂).map γ₂ :=
    from_intertwining c₂ γ₃ _ _ _ hh₂
  have ha : ((P e₃).map c.inv ≫ act) ≫ q.hom.app _ =
      compare a a₂ c₂ ≫ (R j₂).map (compare a a₁ c₁) :=
    compare_paste a a₁ a₂ c₁ c₂
  have hp : ((P p₃).map c.inv ≫ proj) ≫ q.hom.app _ =
      compare a b₂ c₂ ≫ (R j₂).map (compare a b₁ c₁) :=
    compare_paste a b₁ b₂ c₁ c₂
  have : IsIso (compare a a₁ c₁) := by dsimp only [compare]; infer_instance
  have : IsIso (compare a a₂ c₂) := by dsimp only [compare]; infer_instance
  have : IsIso (compare a b₁ c₁) := by dsimp only [compare]; infer_instance
  have : IsIso (compare a b₂ c₂) := by dsimp only [compare]; infer_instance
  have hact : IsIso act := comparison_isIso c act (q.app _) _ ha
  have hproj : IsIso proj := comparison_isIso c proj (q.app _) _ hp
  refine ⟨hact, hproj, ?_⟩
  have hh := paste_intertwining q γ₁ γ₂ γ₃ ih₁ ih₂ ha hp
  exact to_intertwining c γ₃ proj act _ hh

private theorem equivariantDirectImage_comp {J : JetSystem.{0}} {X Y Z : TopCat.{0}}
    (a : DerivedAdjunctions) {A : JetAction J X} {B : JetAction J Y} {C : JetAction J Z}
    {f : X ⟶ Y} {g : Y ⟶ Z} (hbc : B.cutoff ≤ C.cutoff)
    {hf : JetMapsCommute A B f} {hg : JetMapsCommute B C g}
    (h : JetMapsCommute A C (f ≫ g))
    {F : BoundedBelow X} {G : BoundedBelow Y} {K : BoundedBelow Z}
    {α : A.Equivariance F.obj} {β : B.Equivariance G.obj} {δ : C.Equivariance K.obj}
    (h₁ : EquivariantDirectImageComparison a A B f hf F α G β)
    (h₂ : EquivariantDirectImageComparison a B C g hg G β K δ) :
    EquivariantDirectImageComparison a A C (f ≫ g) h F α K δ := by
  obtain ⟨c₁, eq₁⟩ := h₁
  obtain ⟨c₂, eq₂⟩ := h₂
  let c := (pushComposition a f g).app F ≪≫ (R g).mapIso c₁ ≪≫ c₂
  refine ⟨c, ?_⟩
  intro k hx hz
  let hy := hbc.trans hz
  let H := J.group k
  let j₁ := parameterInclusion H f
  let j₂ := parameterInclusion H g
  let e₁ := (A.action k hx).act
  let e₂ := (B.action k hy).act
  let e₃ := (C.action k hz).act
  let p₁ := AnalyticAction.projection H X
  let p₂ := AnalyticAction.projection H Y
  let p₃ := AnalyticAction.projection H Z
  let γ₁ : (P e₁).obj F ⟶ (P p₁).obj F := ObjectProperty.homMk (α.datum k hx).iso.hom
  let γ₂ : (P e₂).obj G ⟶ (P p₂).obj G := ObjectProperty.homMk (β.datum k hy).iso.hom
  let γ₃ : (P e₃).obj K ⟶ (P p₃).obj K := ObjectProperty.homMk (δ.datum k hz).iso.hom
  let a₁ : j₁ ≫ e₂ = e₁ ≫ f := hf k hx hy
  let a₂ : j₂ ≫ e₃ = e₂ ≫ g := hg k hy hz
  let b₁ : j₁ ≫ p₂ = p₁ ≫ f := projectionSquare H f
  let b₂ : j₂ ≫ p₃ = p₂ ≫ g := projectionSquare H g
  obtain ⟨ha₁, hp₁, hh₁⟩ := eq₁ k hx hy
  obtain ⟨ha₂, hp₂, hh₂⟩ := eq₂ k hy hz
  have h₁k : DirectImageComparisonAt a a₁ b₁ c₁ γ₁ γ₂ :=
    ⟨ha₁, hp₁, ObjectProperty.hom_ext _ hh₁⟩
  have h₂k : DirectImageComparisonAt a a₂ b₂ c₂ γ₂ γ₃ :=
    ⟨ha₂, hp₂, ObjectProperty.hom_ext _ hh₂⟩
  obtain ⟨ha, hp, hcomm⟩ := directImageComparisonAt_paste a a₁ a₂ b₁ b₂ c₁ c₂ h₁k h₂k
  exact ⟨ha, hp, congrArg (fun u => u.hom) hcomm⟩

private theorem closed_ordinary_comparison {J : JetSystem.{0}} {W : TopCat.{0}} {Z : Set W}
    (a : DerivedAdjunctions) (hZ : IsClosed Z)
    (b : P (closedInclusion Z) ⊣ closedExtensionPlus hZ)
    (A : JetAction J (TopCat.of Z)) (B : JetAction J W)
    (hi : JetMapsCommute A B (closedInclusion Z))
    (G : BoundedBelow (TopCat.of Z)) (β : A.Equivariance G.obj)
    (δ : (above B A.cutoff).Equivariance ((closedExtensionPlus hZ).obj G).obj)
    (hδ : ClosedExtensionArrow a hZ b A B hi G β δ) :
    EquivariantDirectImageComparison a A (above B A.cutoff) (closedInclusion Z)
      (fun k hz hw => hi k hz ((le_max_left _ _).trans hw))
      G β ((closedExtensionPlus hZ).obj G) δ := by
  let i := closedInclusion Z
  let c := (a i).rightAdjointUniq b
  refine ⟨c.app G, ?_⟩
  intro k hz hk
  let hx := (le_max_left _ _).trans hk
  let H := J.group k
  let t := parameterInclusion H i
  let e := (B.action k hx).act
  let p := AnalyticAction.projection H W
  let s := hi k hz hx
  let r := projectionSquare H i
  obtain ⟨hisIso, hmatches⟩ := hδ
  obtain ⟨ha, hp⟩ := hisIso k hk
  have hcomm := hmatches k hk
  change IsIso (adjointSquareMap (pullbackSquare s) (a t) b G) at ha
  change IsIso (adjointSquareMap (pullbackSquare r) (a t) b G) at hp
  have ea := mate_change_right (pullbackSquare s) (a t) (a i) b G
  have ep := mate_change_right (pullbackSquare r) (a t) (a i) b G
  change directImageComparison s (a t) (a i) G =
    (P e).map (c.hom.app G) ≫ adjointSquareMap (pullbackSquare s) (a t) b G at ea
  change directImageComparison r (a t) (a i) G =
    (P p).map (c.hom.app G) ≫ adjointSquareMap (pullbackSquare r) (a t) b G at ep
  refine ⟨ea.symm ▸ inferInstance, ep.symm ▸ inferInstance, ?_⟩
  let γ : (P (A.action k hz).act).obj G ⟶ (P (AnalyticAction.projection H (TopCat.of Z))).obj G :=
    ObjectProperty.homMk (β.datum k hz).iso.hom
  let η : (P e).obj ((closedExtensionPlus hZ).obj G) ⟶
      (P p).obj ((closedExtensionPlus hZ).obj G) :=
    ObjectProperty.homMk (δ.datum k hk).iso.hom
  have hh : η ≫ adjointSquareMap (pullbackSquare r) (a t) b G =
      adjointSquareMap (pullbackSquare s) (a t) b G ≫ (R t).map γ :=
    ObjectProperty.hom_ext _ hcomm
  have ht : (P e).map (c.hom.app G) ≫ η ≫ (P p).map (c.inv.app G) ≫
      directImageComparison r (a t) (a i) G =
    directImageComparison s (a t) (a i) G ≫ (R t).map γ := by
    rw [ea, ep]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    rw [(P p).map_id, Category.id_comp, hh]
  exact congrArg (fun u => u.hom) ht

/-- Compose the two equivariant homeomorphism comparisons with the normalized
closed extension. The input closed-extension property can be instantiated from
the equivariant IC theorem at its jet system and its canonical adjunctions. -/
theorem equivariantClosedDirectImageComposition_conditional
    (_equivariantIC : EquivariantIntersectionComplexesSpecs.Expected.EquivariantIntersectionComplexes) :
    EquivariantClosedDirectImageComposition := by
  intro J a b hclosed X Y W Z hZ f v A_X A_Y A_Z B hXY hYZ hf hv hi F α G β G_Z β_Z h₁ h₂
  let i := closedInclusion Z
  let c := (a i).rightAdjointUniq (b hZ)
  obtain ⟨hisIso, δ, hmatches⟩ :=
    hclosed hZ B A_Z (fun k hw hzk => hi k hzk hw) (@a) (b hZ) G_Z β_Z
  have hδ : ClosedExtensionArrow a hZ (b hZ) A_Z B hi G_Z β_Z δ := ⟨hisIso, hmatches⟩
  let B' := above B A_Z.cutoff
  let hz : A_Z.cutoff ≤ B'.cutoff := le_max_right _ _
  have hi' : JetMapsCommute A_Z B' i := fun k hzk hwk => hi k hzk ((le_max_left _ _).trans hwk)
  let hvi := jetMapsCommute_comp hYZ hz hv hi'
  let h := jetMapsCommute_comp hXY (hYZ.trans hz) hf hvi
  refine ⟨c, fun K => (a i).rightAdjointUniq_hom_app_counit (b hZ) K, δ, h, hδ, ?_⟩
  have h₃ := closed_ordinary_comparison a hZ (b hZ) A_Z B hi G_Z β_Z δ hδ
  exact equivariantDirectImage_comp a (hYZ.trans hz) h h₁
    (equivariantDirectImage_comp a hz hvi h₂ h₃)

end RepTheorySurvey.Geometric.EquivariantClosedDirectImageComposition

theorem _root_.«RepTheorySurvey».«Geometric».«EquivariantClosedDirectImageComposition».«equivariantClosedDirectImageComposition» : _root_.«RepTheorySurvey».«Geometric».«EquivariantClosedDirectImageCompositionSpecs».«EquivariantClosedDirectImageComposition» :=
  @_root_.«RepTheorySurvey».«Geometric».«EquivariantClosedDirectImageComposition».«equivariantClosedDirectImageComposition_conditional» (@_root_.«RepTheorySurvey».«Geometric».«EquivariantIntersectionComplexes».«equivariantIntersectionComplexes»)
