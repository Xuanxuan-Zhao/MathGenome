import Specs.LinearAlgebraicGroups.Descent.InnerProductFactors
import LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import LinearAlgebraicGroups.Classification.ReductiveProductWithSplitTorus
import LinearAlgebraicGroups.Reductive.RadicalBaseChange
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj

universe u

namespace LinearAlgebraicGroups.Descent.InnerProductFactors

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme)
open Specs.AutomorphismSequence
open Specs.RelativeFormComparison

open Specs.GeometricRadicals (IsReductive)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open NonabelianCohomology (Cocycle pointAction)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

open private exists_coordinate_model standard descend_standard_iso extendedHom_comp extendedHom_id
  from LinearAlgebraicGroups.Descent.Forms
open private schemeIsoEquiv groundIso hopfIsoEquiv hopfIsoEquiv_apply schemeIsoEquiv_ground
  hopfInduced_iff hopfSchemeIso
  from LinearAlgebraicGroups.Descent.RelativeFormComparison
open private extendedGroupIso extendedSpecIso_hom_fst extendedSpecIso_natural
  from LinearAlgebraicGroups.Affine.ClosedSubgroups

/-- An invariant relative isomorphism descends with its specified scalar extension. -/
private theorem descendRelativeIso [IsGalois k K] {G H : AffineAlgebraicGroup k}
    (r : relativePoints G.val (fieldTest k K) ≅ relativePoints H.val (fieldTest k K))
    (hr : ∀ σ : Gal(K/k), restrictIso (fieldMap k K σ) r = r) :
    ∃ e : G.val ≅ H.val, groundIso e = r := by
  obtain ⟨A, _, ⟨g⟩⟩ := exists_coordinate_model G
  obtain ⟨B, _, ⟨h⟩⟩ := exists_coordinate_model H
  let t := extendedGroupIso (k := k) K
  have ht : Forms.IsScalarExtensionComparison t := fun C => extendedSpecIso_hom_fst K C
  obtain ⟨E, hE, hσ⟩ := RelativeFormComparison.hopfIsomorphismComparison t ht g h
  let f := E.symm r
  have hf (σ : Gal(K/k)) : HopfConjugates σ f f :=
    (hσ σ f f).mpr (by rw [E.apply_symm_apply, hr])
  obtain ⟨f₀, hf₀⟩ := descend_standard_iso f (fun σ x => hf σ x)
  let e := g.symm ≪≫ Forms.spectrumIso f₀ ≪≫ h
  refine ⟨e, ?_⟩
  rw [← schemeIsoEquiv_ground (S := K)]
  have he : hopfIsoEquiv t g h f = r :=
    (hopfInduced_iff t g h f r).mp ((hE f r).mpr (E.apply_symm_apply r))
  -- Natural scalar extension of inverse pullback.
  rw [← he, hopfIsoEquiv_apply]
  congr 1
  apply Iso.ext
  have hn := extendedSpecIso_natural K f₀.inv
  have hinv : extendedHopfMap K f₀.inv = f.inv := by
    apply (cancel_mono f.hom).mp
    rw [f.inv_hom_id, ← hf₀]
    rw [← extendedHom_comp, f₀.inv_hom_id, extendedHom_id]
  have hn' : specGroupMap f.inv ≫ (t B).hom =
      (t A).hom ≫ (groupBaseChange k K).map (specGroupMap f₀.inv) := by
    rw [← hinv]
    exact Grp.hom_ext _ _ hn
  simp only [e, Forms.spectrumIso, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    hopfSchemeIso, Iso.trans_inv, Iso.symm_hom, Category.assoc]
  change (groupBaseChange k K).map g.inv ≫
      (groupBaseChange k K).map (specGroupMap f₀.inv) ≫ (groupBaseChange k K).map h.hom =
    (groupBaseChange k K).map g.inv ≫ (t A).inv ≫
      specGroupMap f.inv ≫ (t B).hom ≫ (groupBaseChange k K).map h.hom
  have hc : (t A).inv ≫ (specGroupMap f.inv ≫ (t B).hom) =
      (groupBaseChange k K).map (specGroupMap f₀.inv) := by
    rw [hn', Iso.inv_hom_id_assoc]
  simpa only [Category.assoc] using congrArg (fun m => (groupBaseChange k K).map g.inv ≫
    m ≫ (groupBaseChange k K).map h.hom) hc.symm

open private smooth_baseChange_iff connected_baseChange_iff
  from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private geometricallyConnected_of_connected
  from LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private reductive_of_groupIso from LinearAlgebraicGroups.RootData.RankOneFlag

private theorem reductiveOfRelativeIso {G H : AffineAlgebraicGroup k}
    (hG : IsReductive G)
    (r : relativePoints G.val (fieldTest k K) ≅ relativePoints H.val (fieldTest k K)) :
    IsReductive H := by
  let e := (schemeIsoEquiv K G.val H.val).symm r
  have hG' := (_root_.LinearAlgebraicGroups.Reductive.RadicalBaseChange.reductiveFieldExtension (K := K) G hG.1 hG.2.1).mpr hG
  have hH' : IsReductive (baseChangedAlgebraicGroup K H) :=
    reductive_of_groupIso (A := baseChangedAlgebraicGroup K G) e hG'
  have hs : Smooth H.val.X.hom := (smooth_baseChange_iff (K := K) H.val.X).mp hH'.1
  let := hH'.2.1
  have : ConnectedSpace H.val.X.left := (connected_baseChange_iff (K := K) H).mp
    (GeometricallyConnected.connectedSpace_of_subsingleton
      (baseChangedAlgebraicGroup K H).val.X.hom)
  exact (_root_.LinearAlgebraicGroups.Reductive.RadicalBaseChange.reductiveFieldExtension H hs (geometricallyConnected_of_connected H)).mp hH'


section RelativeProducts

variable {S : SchemeOver k} {G₁ G₂ H₁ H₂ : GroupScheme k}

private abbrev relYoneda (S : SchemeOver k) :=
  yonedaGrp (C := SchemeOver k) ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.forget S).op

private abbrev relMap (S : SchemeOver k) {G H : GroupScheme k} (f : G ⟶ H) :=
  (relYoneda S).map f

private abbrev post {U : SchemeOver k} {G H : GroupScheme k} (p : G ⟶ H) :
    (U ⟶ G.X) →* (U ⟶ H.X) :=
  ((yonedaGrp.map p).app (op U)).hom

private theorem post_apply {U : SchemeOver k} {G H : GroupScheme k} (p : G ⟶ H)
    (x : U ⟶ G.X) : post p x = x ≫ p.hom.hom := rfl

private abbrev productFst (A B : GroupScheme k) : A ⊗ B ⟶ A := fst A B
private abbrev productSnd (A B : GroupScheme k) : A ⊗ B ⟶ B := snd A B

private theorem post_lift_fst {U : SchemeOver k} {A B : GroupScheme k}
    (x : U ⟶ A.X) (y : U ⟶ B.X) : post (productFst A B) (lift x y) = x := by
  change lift x y ≫ fst A.X B.X = x
  exact lift_fst x y

private theorem post_lift_snd {U : SchemeOver k} {A B : GroupScheme k}
    (x : U ⟶ A.X) (y : U ⟶ B.X) : post (productSnd A B) (lift x y) = y := by
  change lift x y ≫ snd A.X B.X = y
  exact lift_snd x y

private theorem productPoints_ext {U : SchemeOver k} {A B : GroupScheme k}
    {x y : U ⟶ (A ⊗ B).X}
    (h₁ : post (productFst A B) x = post (productFst A B) y)
    (h₂ : post (productSnd A B) x = post (productSnd A B) y) : x = y :=
  CartesianMonoidalCategory.hom_ext x y h₁ h₂

private def productMap
    (a : relativePoints G₁ S ⟶ relativePoints H₁ S)
    (b : relativePoints G₂ S ⟶ relativePoints H₂ S) :
    relativePoints (G₁ ⊗ G₂) S ⟶ relativePoints (H₁ ⊗ H₂) S where
  app U := GrpCat.ofHom
    { toFun := fun x =>
        lift (a.app U (post (productFst G₁ G₂) x))
          (b.app U (post (productSnd G₁ G₂) x))
      map_one' := by
        apply productPoints_ext
        · change lift _ _ ≫ fst H₁.X H₂.X = post (productFst H₁ H₂) 1
          rw [lift_fst, map_one, map_one, map_one]
        · change lift _ _ ≫ snd H₁.X H₂.X = post (productSnd H₁ H₂) 1
          rw [lift_snd, map_one, map_one, map_one]
      map_mul' x y := by
        apply productPoints_ext
        · rw [map_mul (post (productFst H₁ H₂))]
          simp only [post_lift_fst, map_mul]
        · rw [map_mul (post (productSnd H₁ H₂))]
          simp only [post_lift_snd, map_mul] }
  naturality U V p := by
    apply GrpCat.ext
    intro x
    apply productPoints_ext
    · change lift _ _ ≫ fst H₁.X H₂.X = (p.unop.left ≫ lift _ _) ≫ fst H₁.X H₂.X
      rw [lift_fst, Category.assoc, lift_fst]
      simp only [post_apply]
      exact NatTrans.naturality_apply a p (post (productFst G₁ G₂) x)
    · change lift _ _ ≫ snd H₁.X H₂.X = (p.unop.left ≫ lift _ _) ≫ snd H₁.X H₂.X
      rw [lift_snd, Category.assoc, lift_snd]
      simp only [post_apply]
      exact NatTrans.naturality_apply b p (post (productSnd G₁ G₂) x)

@[reassoc]
private theorem productMap_fst
    (a : relativePoints G₁ S ⟶ relativePoints H₁ S)
    (b : relativePoints G₂ S ⟶ relativePoints H₂ S) :
    productMap a b ≫ relMap S (productFst H₁ H₂) = relMap S (productFst G₁ G₂) ≫ a := by
  ext U x
  exact post_lift_fst (A := H₁) (B := H₂) _ _

@[reassoc]
private theorem productMap_snd
    (a : relativePoints G₁ S ⟶ relativePoints H₁ S)
    (b : relativePoints G₂ S ⟶ relativePoints H₂ S) :
    productMap a b ≫ relMap S (productSnd H₁ H₂) = relMap S (productSnd G₁ G₂) ≫ b := by
  ext U x
  exact post_lift_snd (A := H₁) (B := H₂) _ _

private theorem relativeProduct_ext {J : (Over S)ᵒᵖ ⥤ GrpCat.{u}}
    {a b : J ⟶ relativePoints (H₁ ⊗ H₂) S}
    (h₁ : a ≫ relMap S (productFst H₁ H₂) = b ≫ relMap S (productFst H₁ H₂))
    (h₂ : a ≫ relMap S (productSnd H₁ H₂) = b ≫ relMap S (productSnd H₁ H₂)) : a = b := by
  ext U x
  exact productPoints_ext
    (ConcreteCategory.congr_hom (NatTrans.congr_app h₁ U) x)
    (ConcreteCategory.congr_hom (NatTrans.congr_app h₂ U) x)

private def productIso
    (a : relativePoints G₁ S ≅ relativePoints H₁ S)
    (b : relativePoints G₂ S ≅ relativePoints H₂ S) :
    relativePoints (G₁ ⊗ G₂) S ≅ relativePoints (H₁ ⊗ H₂) S where
  hom := productMap a.hom b.hom
  inv := productMap a.inv b.inv
  hom_inv_id := by
    apply relativeProduct_ext
    · rw [Category.assoc, productMap_fst a.inv b.inv, ← Category.assoc,
        productMap_fst a.hom b.hom, Category.assoc, Iso.hom_inv_id, Category.comp_id,
        Category.id_comp]
    · rw [Category.assoc, productMap_snd a.inv b.inv, ← Category.assoc,
        productMap_snd a.hom b.hom, Category.assoc, Iso.hom_inv_id, Category.comp_id,
        Category.id_comp]
  inv_hom_id := by
    apply relativeProduct_ext
    · rw [Category.assoc, productMap_fst a.hom b.hom, ← Category.assoc,
        productMap_fst a.inv b.inv, Category.assoc, Iso.inv_hom_id, Category.comp_id,
        Category.id_comp]
    · rw [Category.assoc, productMap_snd a.hom b.hom, ← Category.assoc,
        productMap_snd a.inv b.inv, Category.assoc, Iso.inv_hom_id, Category.comp_id,
        Category.id_comp]

private theorem restrict_productIso {T : SchemeOver k} (p : T ⟶ S)
    (a : relativePoints G₁ S ≅ relativePoints H₁ S)
    (b : relativePoints G₂ S ≅ relativePoints H₂ S) :
    restrictIso p (productIso a b) = productIso (restrictIso p a) (restrictIso p b) := by
  apply Iso.ext
  ext U x
  rfl

private theorem productIso_trans {J₁ J₂ : GroupScheme k}
    (a : relativePoints G₁ S ≅ relativePoints H₁ S)
    (b : relativePoints G₂ S ≅ relativePoints H₂ S)
    (c : relativePoints H₁ S ≅ relativePoints J₁ S)
    (d : relativePoints H₂ S ≅ relativePoints J₂ S) :
    productIso a b ≪≫ productIso c d = productIso (a ≪≫ c) (b ≪≫ d) := by
  apply Iso.ext
  apply relativeProduct_ext
  · simp only [Iso.trans_hom, productIso]
    rw [Category.assoc, productMap_fst c.hom d.hom, ← Category.assoc,
      productMap_fst a.hom b.hom, Category.assoc, productMap_fst]
  · simp only [Iso.trans_hom, productIso]
    rw [Category.assoc, productMap_snd c.hom d.hom, ← Category.assoc,
      productMap_snd a.hom b.hom, Category.assoc, productMap_snd]

end RelativeProducts


section AdjointProjections

open private groupSectionsMap groupSectionsMap_locallySurjective descends_locallySurjective
  groupSections_isSheaf groupSheaf_separated
  from LinearAlgebraicGroups.Descent.AutomorphismSequence

private abbrev relGround (S : SchemeOver k) {G H : GroupScheme k} (e : G ≅ H) :=
  (relYoneda S).mapIso e

private theorem restrict_comp {S T : SchemeOver k} (a : T ⟶ S)
    {G H J : GroupScheme k} (i : relativePoints G S ≅ relativePoints H S)
    (j : relativePoints H S ≅ relativePoints J S) :
    restrictIso a (i ≪≫ j) = restrictIso a i ≪≫ restrictIso a j :=
  Iso.ext (by rfl)

private theorem restrict_relGround {S T : SchemeOver k} (a : T ⟶ S)
    {G H : GroupScheme k} (e : G ≅ H) :
    restrictIso a (relGround S e) = relGround T e :=
  Iso.ext (by rfl)

private theorem innerProjection_comm {S : SchemeOver k} {G H : GroupScheme k}
    (p : G ⟶ H) (g : S ⟶ G.X) :
    (innerAut g).asIso.hom ≫ relMap S p =
      relMap S p ≫ (innerAut (post p g)).asIso.hom := by
  ext U x
  change U.unop.left ⟶ G.X at x
  change post p ((U.unop.hom ≫ g) * x * (U.unop.hom ≫ g)⁻¹) =
    (U.unop.hom ≫ post p g) * post p x * (U.unop.hom ≫ post p g)⁻¹
  have hp : post p (U.unop.hom ≫ g) = U.unop.hom ≫ post p g := by
    change (U.unop.hom ≫ g) ≫ p.hom.hom = U.unop.hom ≫ g ≫ p.hom.hom
    exact Category.assoc _ _ _
  rw [map_mul, map_mul, map_inv, hp]

/-- The projection of a product induces a map on actual adjoint group sections. -/
private theorem adjointProjection {G H : AffineAlgebraicGroup k}
    (V : AdjointQuotient G) (W : AdjointQuotient H)
    (innG : groupSections V.quotient.val ⟶ automorphisms G.val)
    (innH : groupSections W.quotient.val ⟶ automorphisms H.val)
    (hG : ∀ (U : SchemeOver k) (g : U ⟶ G.val.X),
      innG.app (op U) ⟨g ≫ V.projection.hom.hom⟩ = innerAut g)
    (hH : ∀ (U : SchemeOver k) (g : U ⟶ H.val.X),
      innH.app (op U) ⟨g ≫ W.projection.hom.hom⟩ = innerAut g)
    (injH : ∀ U, Function.Injective (innH.app U))
    (p : G.val ⟶ H.val) (s : H.val ⟶ G.val) (hs : s ≫ p = 𝟙 _) :
    ∃ d : groupSections V.quotient.val ⟶ groupSections W.quotient.val,
      groupSectionsMap V.projection ≫ d = groupSectionsMap (p ≫ W.projection) := by
  refine descends_locallySurjective _ _ (groupSectionsMap_locallySurjective _ V.fppf)
    (groupSections_isSheaf W.quotient.val) ?_
  intro U x y h
  have hxy : innerAut x.down = innerAut y.down := by
    rw [← hG U.unop, ← hG U.unop]
    exact congrArg (innG.app U) h
  have hpi := congrArg (fun f : RelativeAut G.val U.unop =>
    f.asIso.hom ≫ relMap U.unop p) hxy
  rw [innerProjection_comm, innerProjection_comm] at hpi
  have hsec : relMap U.unop s ≫ relMap U.unop p = 𝟙 _ := by
    rw [← (relYoneda U.unop).map_comp, hs]
    exact (relYoneda U.unop).map_id H.val
  have hpi' : innerAut (post p x.down) = innerAut (post p y.down) := by
    apply Aut.ext
    apply Iso.ext
    have he := congrArg (fun f => relMap U.unop s ≫ f) hpi
    simp only [← Category.assoc (relMap U.unop s), hsec, Category.id_comp] at he
    exact he
  apply injH U
  change innH.app U ⟨post p x.down ≫ W.projection.hom.hom⟩ =
    innH.app U ⟨post p y.down ≫ W.projection.hom.hom⟩
  rw [hH, hH, hpi']


private theorem innerProjection_assoc {S : SchemeOver k} {G H J : GroupScheme k}
    (b : G ⟶ H) (p : H ⟶ J) (g : S ⟶ G.X) :
    (innerAut g).asIso.hom ≫ relMap S b ≫ relMap S p =
      relMap S b ≫ relMap S p ≫ (innerAut (post (b ≫ p) g)).asIso.hom := by
  have hc : relMap S (b ≫ p) = relMap S b ≫ relMap S p := (relYoneda S).map_comp b p
  have h := innerProjection_comm (b ≫ p) g
  rw [hc] at h
  exact h.trans (Category.assoc (relMap S b) (relMap S p) (innerAut (post (b ≫ p) g)).asIso.hom)

set_option maxHeartbeats 1800000 in
private theorem innerAut_productIso {G A B : GroupScheme k} {U : SchemeOver k}
    (b : G ≅ A ⊗ B) (g : U ⟶ G.X) :
    (innerAut g).asIso =
      relGround U b ≪≫ productIso
        (innerAut (post (b.hom ≫ productFst A B) g)).asIso
        (innerAut (post (b.hom ≫ productSnd A B) g)).asIso ≪≫ (relGround U b).symm := by
  suffices hh : (innerAut g).asIso ≪≫ relGround U b =
      relGround U b ≪≫ productIso
        (innerAut (post (b.hom ≫ productFst A B) g)).asIso
        (innerAut (post (b.hom ≫ productSnd A B) g)).asIso by
    simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
      using congrArg (fun i => i ≪≫ (relGround U b).symm) hh
  apply Iso.ext
  apply relativeProduct_ext
  · simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, productIso, productMap_fst]
    exact innerProjection_assoc b.hom (productFst A B) g
  · simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, productIso, productMap_snd]
    exact innerProjection_assoc b.hom (productSnd A B) g

set_option maxHeartbeats 1600000 in
private theorem productOfInnerProjections {Q Q₁ Q₂ : AffineAlgebraicGroup k}
    (b : Q.val ≅ Q₁.val ⊗ Q₂.val) (V : AdjointQuotient Q)
    (V₁ : AdjointQuotient Q₁) (V₂ : AdjointQuotient Q₂)
    (inn : groupSections V.quotient.val ⟶ automorphisms Q.val)
    (inn₁ : groupSections V₁.quotient.val ⟶ automorphisms Q₁.val)
    (inn₂ : groupSections V₂.quotient.val ⟶ automorphisms Q₂.val)
    (h : ∀ (U : SchemeOver k) (g : U ⟶ Q.val.X),
      inn.app (op U) ⟨g ≫ V.projection.hom.hom⟩ = innerAut g)
    (h₁ : ∀ (U : SchemeOver k) (g : U ⟶ Q₁.val.X),
      inn₁.app (op U) ⟨g ≫ V₁.projection.hom.hom⟩ = innerAut g)
    (h₂ : ∀ (U : SchemeOver k) (g : U ⟶ Q₂.val.X),
      inn₂.app (op U) ⟨g ≫ V₂.projection.hom.hom⟩ = innerAut g)
    (d₁ : groupSections V.quotient.val ⟶ groupSections V₁.quotient.val)
    (d₂ : groupSections V.quotient.val ⟶ groupSections V₂.quotient.val)
    (hd₁ : groupSectionsMap V.projection ≫ d₁ =
      groupSectionsMap ((b.hom ≫ productFst Q₁.val Q₂.val) ≫ V₁.projection))
    (hd₂ : groupSectionsMap V.projection ≫ d₂ =
      groupSectionsMap ((b.hom ≫ productSnd Q₁.val Q₂.val) ≫ V₂.projection))
    {S : SchemeOver k} (q : (groupSections V.quotient.val).obj (op S)) :
    (inn.app (op S) q).asIso ≪≫ relGround S b =
      relGround S b ≪≫ productIso ((inn₁.app (op S) (d₁.app (op S) q)).asIso)
        ((inn₂.app (op S) (d₂.app (op S) q)).asIso) := by
  let R := productIso ((inn₁.app (op S) (d₁.app (op S) q)).asIso)
    ((inn₂.app (op S) (d₂.app (op S) q)).asIso)
  let f : RelativeAut Q.val S := Aut.of (relGround S b ≪≫ R ≪≫ relGround S b.symm)
  let p := groupSectionsMap V.projection
  let := groupSectionsMap_locallySurjective V.projection V.fppf
  have hf : inn.app (op S) q = f := by
    refine groupSheaf_separated (AutomorphismSequence.automorphisms_isSheaf Q.val)
      (Presheaf.imageSieve_mem (Specs.Fppf.schemeTopology k) p q) _ _ ?_
    rintro U a ⟨g, hg⟩
    have hg₀ : restrictAut a (inn.app (op S) q) = innerAut g.down := by
      change (automorphisms Q.val).map a.op (inn.app (op S) q) = _
      rw [← NatTrans.naturality_apply inn, ← hg]
      exact h U g.down
    have hg₁ : restrictAut a (inn₁.app (op S) (d₁.app (op S) q)) =
        innerAut (post (b.hom ≫ productFst Q₁.val Q₂.val) g.down) := by
      change (automorphisms Q₁.val).map a.op ((d₁ ≫ inn₁).app (op S) q) = _
      rw [← NatTrans.naturality_apply (d₁ ≫ inn₁), ← hg]
      have hx := ConcreteCategory.congr_hom (NatTrans.congr_app hd₁ (op U)) g
      change inn₁.app (op U) (d₁.app (op U) (p.app (op U) g)) = _
      change d₁.app (op U) (p.app (op U) g) =
        ⟨post (b.hom ≫ productFst Q₁.val Q₂.val) g.down ≫ V₁.projection.hom.hom⟩ at hx
      exact (congrArg (fun x => inn₁.app (op U) x) hx).trans (h₁ U _)
    have hg₂ : restrictAut a (inn₂.app (op S) (d₂.app (op S) q)) =
        innerAut (post (b.hom ≫ productSnd Q₁.val Q₂.val) g.down) := by
      change (automorphisms Q₂.val).map a.op ((d₂ ≫ inn₂).app (op S) q) = _
      rw [← NatTrans.naturality_apply (d₂ ≫ inn₂), ← hg]
      have hx := ConcreteCategory.congr_hom (NatTrans.congr_app hd₂ (op U)) g
      change inn₂.app (op U) (d₂.app (op U) (p.app (op U) g)) = _
      change d₂.app (op U) (p.app (op U) g) =
        ⟨post (b.hom ≫ productSnd Q₁.val Q₂.val) g.down ≫ V₂.projection.hom.hom⟩ at hx
      exact (congrArg (fun x => inn₂.app (op U) x) hx).trans (h₂ U _)
    change restrictAut a (inn.app (op S) q) = restrictAut a f
    rw [hg₀]
    apply Aut.ext
    have hfr : (restrictAut a f).asIso =
        relGround U b ≪≫ productIso (restrictAut a (inn₁.app (op S) (d₁.app (op S) q))).asIso
          (restrictAut a (inn₂.app (op S) (d₂.app (op S) q))).asIso ≪≫ (relGround U b).symm := by
      change restrictIso a (relGround S b ≪≫ R ≪≫ relGround S b.symm) = _
      simp only [restrict_comp, restrict_relGround, R, restrict_productIso]
      rfl
    rw [hfr, hg₁, hg₂]
    exact innerAut_productIso b g.down
  rw [hf]
  change (relGround S b ≪≫ R ≪≫ (relGround S b).symm) ≪≫ relGround S b =
    relGround S b ≪≫ R
  rw [Iso.trans_assoc, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

end AdjointProjections

section CocycleDescent

local instance galTopology : TopologicalSpace (Gal(K/k)) := krullTopology k K

local instance automorphismTopology (G : GroupScheme k) :
    TopologicalSpace (RelativeAut G (fieldTest k K)) := ⊥

local instance automorphismDiscrete (G : GroupScheme k) :
    DiscreteTopology (RelativeAut G (fieldTest k K)) := ⟨rfl⟩

private abbrev AdjointCocycle (V : GroupScheme k) :=
  @Cocycle (Gal(K/k)) (NonabelianCohomology.Points k K V.X) _ (krullTopology k K) _ ⊥ (pointAction k K V.X)

/-- Map an adjoint cocycle to automorphisms by a morphism of the presheaves. -/
private def automorphismCocycle {V G : GroupScheme k}
    (m : groupSections V ⟶ automorphisms G) (d : AdjointCocycle (K := K) V) :
    Cocycle (automorphismAction k K G) := by
  let S := fieldTest k K
  let : TopologicalSpace (NonabelianCohomology.Points k K V.X) := ⊥
  let : DiscreteTopology (NonabelianCohomology.Points k K V.X) := ⟨rfl⟩
  let f : NonabelianCohomology.Points k K V.X →* RelativeAut G S :=
    (m.app (op S)).hom.comp { toFun := ULift.up, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hf (σ : Gal(K/k)) (x : NonabelianCohomology.Points k K V.X) :
      f (pointAction k K V.X σ x) = automorphismAction k K G σ (f x) :=
    ConcreteCategory.congr_hom (m.naturality (fieldMap k K σ).op)
      (ULift.up x : (groupSections V).obj (op S))
  exact Specs.QuasiSplitInnerForms.mapCocycle f continuous_of_discreteTopology hf d

private theorem comparisonOfCocycle [IsSepClosure k K] {Q : AffineAlgebraicGroup k}
    (hQ : IsReductive Q) (d : Cocycle (automorphismAction k K Q.val)) :
    ∃ (H : AffineAlgebraicGroup k)
      (i : relativePoints Q.val (fieldTest k K) ≅ relativePoints H.val (fieldTest k K)),
      IsReductive H ∧ ∀ σ, d σ = transportedAut k K i σ := by
  obtain ⟨C⟩ := RelativeFormComparison.relativeFormClassification (S := K) Q
  obtain ⟨H, i, hi, _⟩ := C.realizes d
  exact ⟨H.val, i, reductiveOfRelativeIso hQ i, hi⟩


private theorem restriction_displacement {G H : GroupScheme k}
    (i : relativePoints G (fieldTest k K) ≅ relativePoints H (fieldTest k K))
    (σ : Gal(K/k)) :
    restrictIso (fieldMap k K σ) i = (transportedAut k K i σ).asIso ≪≫ i := by
  change _ = (restrictIso (fieldMap k K σ) i ≪≫ i.symm) ≪≫ i
  rw [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

private theorem displacement_comp_cancel {G H J : GroupScheme k}
    (i : relativePoints G (fieldTest k K) ≅ relativePoints H (fieldTest k K))
    (j : relativePoints G (fieldTest k K) ≅ relativePoints J (fieldTest k K))
    (σ : Gal(K/k)) (h : transportedAut k K i σ = transportedAut k K j σ) :
    restrictIso (fieldMap k K σ) (i.symm ≪≫ j) = i.symm ≪≫ j := by
  let r := i.symm ≪≫ j
  have he : transportedAut k K r σ = 1 := by
    rw [QuasiSplitInnerForms.differenceOfTrivializations i j σ, h, mul_inv_cancel, map_one]
  have he' : restrictIso (fieldMap k K σ) r ≪≫ r.symm = Iso.refl _ :=
    congrArg Aut.asIso he
  simpa only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl, Iso.refl_trans]
    using congrArg (fun f => f ≪≫ r) he'

end CocycleDescent

section CategoricalProduct

private def tensorToProduct (A B : GroupScheme k) : A ⊗ B ≅ prod A B :=
  (tensorProductIsBinaryProduct A B).conePointUniqueUpToIso (limit.isLimit (pair A B))

private theorem tensorToProduct_fst (A B : GroupScheme k) :
    (tensorToProduct A B).hom ≫ prod.fst = productFst A B :=
  (tensorProductIsBinaryProduct A B).conePointUniqueUpToIso_hom_comp
    (limit.isLimit (pair A B)) (Discrete.mk WalkingPair.left)

private theorem tensorToProduct_snd (A B : GroupScheme k) :
    (tensorToProduct A B).hom ≫ prod.snd = productSnd A B :=
  (tensorProductIsBinaryProduct A B).conePointUniqueUpToIso_hom_comp
    (limit.isLimit (pair A B)) (Discrete.mk WalkingPair.right)

end CategoricalProduct

open private affineProduct from LinearAlgebraicGroups.Classification.ReductiveProductWithSplitTorus

private theorem projectComparison {C : Type*} [Category C] {X Y U V X' Y' : C}
    (i : X ⟶ Y) (e : Y ⟶ V) (b : X ⟶ U) (j : U ⟶ V)
    (p : U ⟶ X') (q : V ⟶ Y') (i' : X' ⟶ Y')
    (h : i ≫ e = b ≫ j) (hp : j ≫ q = p ≫ i') :
    (b ≫ p) ≫ i' = i ≫ e ≫ q := by
  calc
    (b ≫ p) ≫ i' = b ≫ p ≫ i' := Category.assoc b p i'
    _ = b ≫ j ≫ q := congrArg (b ≫ ·) hp.symm
    _ = (b ≫ j) ≫ q := (Category.assoc b j q).symm
    _ = (i ≫ e) ≫ q := congrArg (· ≫ q) h.symm
    _ = i ≫ e ≫ q := Category.assoc i e q

set_option maxHeartbeats 2200000 in
/-- The actual inner form of a product descends as the product of the two ordered forms. -/
theorem innerProductFactors : Specs.InnerProductFactors.Statement.{u} := by
  intro F _ Q₁ Q₂ Q H hQ₁ hQ₂ _ b ⟨V, inn, h, hinj, i, hi⟩
  let K := SeparableClosure F
  let S := fieldTest F K
  let b₀ := b ≪≫ (tensorToProduct Q₁.val Q₂.val).symm
  let p₁ := b₀.hom ≫ productFst Q₁.val Q₂.val
  let p₂ := b₀.hom ≫ productSnd Q₁.val Q₂.val
  let s₁ := lift (𝟙 Q₁.val) (0 : Q₁.val ⟶ Q₂.val) ≫ b₀.inv
  let s₂ := lift (0 : Q₂.val ⟶ Q₁.val) (𝟙 Q₂.val) ≫ b₀.inv
  have hs₁ : s₁ ≫ p₁ = 𝟙 _ := by simp [s₁, p₁, Category.assoc]
  have hs₂ : s₂ ≫ p₂ = 𝟙 _ := by simp [s₂, p₂, Category.assoc]
  obtain ⟨V₁⟩ := AutomorphismSequence.adjointQuotient_exists Q₁
  obtain ⟨V₂⟩ := AutomorphismSequence.adjointQuotient_exists Q₂
  obtain ⟨inn₁, h₁, inj₁⟩ := AutomorphismSequence.adjointInner Q₁ V₁
  obtain ⟨inn₂, h₂, inj₂⟩ := AutomorphismSequence.adjointInner Q₂ V₂
  obtain ⟨d₁, hd₁⟩ := adjointProjection V V₁ inn inn₁ h h₁ inj₁ p₁ s₁ hs₁
  obtain ⟨d₂, hd₂⟩ := adjointProjection V V₂ inn inn₂ h h₂ inj₂ p₂ s₂ hs₂
  obtain ⟨C⟩ := RelativeFormComparison.relativeFormClassification (S := K) Q
  let M : Forms.SchemeModels K Q :=
    ⟨H, ⟨(schemeIsoEquiv K Q.val H.val).symm i⟩⟩
  obtain ⟨a, ha, _⟩ := C.computes M i
  obtain ⟨d, hd, _⟩ := QuasiSplitInnerForms.liftInnerCocycle Q.val V.quotient.val
    inn (hinj (op S)) a (fun σ => (ha σ).symm ▸ hi σ)
  let c₁ := automorphismCocycle (d₁ ≫ inn₁) d
  let c₂ := automorphismCocycle (d₂ ≫ inn₂) d
  have hc₁ (σ : Gal(K/F)) : c₁ σ ∈ (inn₁.app (op S)).hom.range :=
    ⟨d₁.app (op S) ⟨d σ⟩, rfl⟩
  have hc₂ (σ : Gal(K/F)) : c₂ σ ∈ (inn₂.app (op S)).hom.range :=
    ⟨d₂.app (op S) ⟨d σ⟩, rfl⟩
  obtain ⟨H₁, i₁, hH₁, hi₁⟩ := comparisonOfCocycle hQ₁.1 c₁
  obtain ⟨H₂, i₂, hH₂, hi₂⟩ := comparisonOfCocycle hQ₂.1 c₂
  let P := affineProduct H₁ H₂
  let j : relativePoints Q.val S ≅ relativePoints P.val S :=
    relGround S b₀ ≪≫ productIso i₁ i₂
  have hdisp (σ : Gal(K/F)) :
      transportedAut F K i σ = transportedAut F K j σ := by
    have he := productOfInnerProjections b₀ V V₁ V₂ inn inn₁ inn₂ h h₁ h₂
      d₁ d₂ hd₁ hd₂ (S := S) ⟨d σ⟩
    change (inn.app (op S) ⟨d σ⟩).asIso ≪≫ relGround S b₀ =
      relGround S b₀ ≪≫ productIso (c₁ σ).asIso (c₂ σ).asIso at he
    rw [hd σ, ha σ, hi₁ σ, hi₂ σ] at he
    have hj : restrictIso (fieldMap F K σ) j = (transportedAut F K i σ).asIso ≪≫ j := by
      change restrictIso (fieldMap F K σ) (relGround S b₀ ≪≫ productIso i₁ i₂) = _
      rw [restrict_comp, restrict_relGround, restrict_productIso,
        restriction_displacement i₁ σ, restriction_displacement i₂ σ, ← productIso_trans,
        ← Iso.trans_assoc, ← he, Iso.trans_assoc] <;> rfl
    apply Aut.ext
    change (transportedAut F K i σ).asIso = restrictIso (fieldMap F K σ) j ≪≫ j.symm
    rw [hj, Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
  obtain ⟨e₀, he₀⟩ := descendRelativeIso (K := K) (G := H) (H := P) (i.symm ≪≫ j)
    (fun σ => displacement_comp_cancel i j σ (hdisp σ))
  have he : i ≪≫ relGround S e₀ = j := by
    change i ≪≫ groundIso (S := K) e₀ = j
    rw [he₀, ← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]
  let e := e₀ ≪≫ tensorToProduct H₁.val H₂.val
  refine ⟨H₁, H₂, e, hH₁, hH₂, i, i₁, i₂, ⟨V, inn, h, hinj, hi⟩,
    ⟨V₁, inn₁, h₁, inj₁, fun σ => hi₁ σ ▸ hc₁ σ⟩,
    ⟨V₂, inn₂, h₂, inj₂, fun σ => hi₂ σ ▸ hc₂ σ⟩, ?_⟩
  have hb₁ : p₁ = b.hom ≫ prod.fst := by
    change (b.hom ≫ (tensorToProduct Q₁.val Q₂.val).inv) ≫ _ = _
    rw [Category.assoc, ← tensorToProduct_fst, Iso.inv_hom_id_assoc]
  have hb₂ : p₂ = b.hom ≫ prod.snd := by
    change (b.hom ≫ (tensorToProduct Q₁.val Q₂.val).inv) ≫ _ = _
    rw [Category.assoc, ← tensorToProduct_snd, Iso.inv_hom_id_assoc]
  have he₁ : e.hom ≫ prod.fst = e₀.hom ≫ productFst H₁.val H₂.val := by
    change (e₀.hom ≫ (tensorToProduct H₁.val H₂.val).hom) ≫ _ = _
    rw [Category.assoc, tensorToProduct_fst]
  have he₂ : e.hom ≫ prod.snd = e₀.hom ≫ productSnd H₁.val H₂.val := by
    change (e₀.hom ≫ (tensorToProduct H₁.val H₂.val).hom) ≫ _ = _
    rw [Category.assoc, tensorToProduct_snd]
  have he' : i.hom ≫ relMap S e₀.hom =
      relMap S b₀.hom ≫ productMap i₁.hom i₂.hom := congrArg Iso.hom he
  change relMap S (b.hom ≫ prod.fst) ≫ i₁.hom = i.hom ≫ relMap S (e.hom ≫ prod.fst) ∧
    relMap S (b.hom ≫ prod.snd) ≫ i₂.hom = i.hom ≫ relMap S (e.hom ≫ prod.snd)
  constructor
  · rw [← hb₁, he₁]
    have hQ : relMap S p₁ = relMap S b₀.hom ≫ relMap S (productFst Q₁.val Q₂.val) :=
      (relYoneda S).map_comp b₀.hom (productFst Q₁.val Q₂.val)
    have hH : relMap S (e₀.hom ≫ productFst H₁.val H₂.val) =
        relMap S e₀.hom ≫ relMap S (productFst H₁.val H₂.val) :=
      (relYoneda S).map_comp e₀.hom (productFst H₁.val H₂.val)
    calc
      relMap S p₁ ≫ i₁.hom = (relMap S b₀.hom ≫ relMap S (productFst Q₁.val Q₂.val)) ≫
          i₁.hom := congrArg (· ≫ i₁.hom) hQ
      _ = i.hom ≫ relMap S e₀.hom ≫ relMap S (productFst H₁.val H₂.val) :=
        projectComparison _ _ _ _ _ _ _ he' (productMap_fst i₁.hom i₂.hom)
      _ = _ := congrArg (i.hom ≫ ·) hH.symm
  · rw [← hb₂, he₂]
    have hQ : relMap S p₂ = relMap S b₀.hom ≫ relMap S (productSnd Q₁.val Q₂.val) :=
      (relYoneda S).map_comp b₀.hom (productSnd Q₁.val Q₂.val)
    have hH : relMap S (e₀.hom ≫ productSnd H₁.val H₂.val) =
        relMap S e₀.hom ≫ relMap S (productSnd H₁.val H₂.val) :=
      (relYoneda S).map_comp e₀.hom (productSnd H₁.val H₂.val)
    calc
      relMap S p₂ ≫ i₂.hom = (relMap S b₀.hom ≫ relMap S (productSnd Q₁.val Q₂.val)) ≫
          i₂.hom := congrArg (· ≫ i₂.hom) hQ
      _ = i.hom ≫ relMap S e₀.hom ≫ relMap S (productSnd H₁.val H₂.val) :=
        projectComparison _ _ _ _ _ _ _ he' (productMap_snd i₁.hom i₂.hom)
      _ = _ := congrArg (i.hom ≫ ·) hH.symm

end
end LinearAlgebraicGroups.Descent.InnerProductFactors
