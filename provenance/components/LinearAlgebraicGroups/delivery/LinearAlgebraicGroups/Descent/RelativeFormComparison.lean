import Specs.LinearAlgebraicGroups.Descent.RelativeFormComparison
import LinearAlgebraicGroups.Descent.Forms
import LinearAlgebraicGroups.Descent.AutomorphismSequence
import Batteries.Tactic.OpenPrivate
import Mathlib.CategoryTheory.HomCongr

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Descent.RelativeFormComparison

open LinearAlgebraicGroups.Specs
open Specs.AutomorphismSequence Specs.RelativeFormComparison
open Forms NonabelianCohomology

open private relativeYoneda relativeYonedaIso relativeYonedaFullyFaithful relativeSectionEquiv
  from LinearAlgebraicGroups.Descent.AutomorphismSequence
open private spectrumIsoEquiv spectrumIso_trans transportedDifference transported transported_apply standard difference_apply
  cohomologyRelabel cohomologyRelabel_basepoint relabelCocycle_surjective relabelAction_continuous
  exists_coordinate_model from LinearAlgebraicGroups.Descent.Forms

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {k S : Type u} [Field k] [Field S] [Algebra k S]

local notation "V" => fieldTest k S

section SchemeComparison

variable (S) in
/-- Yoneda's identification of isomorphisms after scalar extension with
isomorphisms of the two relative point functors. -/
private def schemeIsoEquiv (G H : GroupScheme k) :
    ((groupBaseChange k S).obj G ≅ (groupBaseChange k S).obj H) ≃
      (relativePoints G V ≅ relativePoints H V) :=
  ((relativeYonedaFullyFaithful V).isoEquiv).trans
    (Iso.isoCongr (relativeYonedaIso V G) (relativeYonedaIso V H))

set_option maxHeartbeats 1200000 in
private theorem schemeIsoEquiv_trans {G H J : GroupScheme k}
    (i : (groupBaseChange k S).obj G ≅ (groupBaseChange k S).obj H)
    (j : (groupBaseChange k S).obj H ≅ (groupBaseChange k S).obj J) :
    schemeIsoEquiv S G J (i ≪≫ j) =
      schemeIsoEquiv S G H i ≪≫ schemeIsoEquiv S H J j := by
  let F := relativeYoneda (k := k)
  apply Iso.ext
  change (relativeYonedaIso V G).inv ≫ (F V).map (i.hom ≫ j.hom) ≫
    (relativeYonedaIso V J).hom =
    ((relativeYonedaIso V G).inv ≫ (F V).map i.hom ≫ (relativeYonedaIso V H).hom) ≫
    (relativeYonedaIso V H).inv ≫ (F V).map j.hom ≫ (relativeYonedaIso V J).hom
  rw [(F V).map_comp i.hom j.hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem schemeIsoEquiv_apply {G H : GroupScheme k}
    (f : (groupBaseChange k S).obj G ≅ (groupBaseChange k S).obj H) :
    IsInduced k S f (schemeIsoEquiv S G H f) := by
  intro U x
  change (relativeSectionEquiv U H.X ((relativeSectionEquiv U G.X).symm x ≫
    f.hom.hom.hom)).left = _
  rfl

private theorem induced_iff {G H : GroupScheme k}
    (f : (groupBaseChange k S).obj G ≅ (groupBaseChange k S).obj H)
    (i : relativePoints G V ≅ relativePoints H V) :
    IsInduced k S f i ↔ schemeIsoEquiv S G H f = i := by
  constructor
  · intro h
    apply Iso.ext
    apply NatTrans.ext
    funext U
    apply GrpCat.ext
    intro x
    apply Over.OverMorphism.ext
    exact (schemeIsoEquiv_apply f U.unop x).trans (h U.unop x).symm
  · rintro rfl
    exact schemeIsoEquiv_apply f

theorem schemeIsomorphismComparison : SchemeIsomorphismComparison.{u} := by
  intro k S _ _ _ G H
  exact ⟨schemeIsoEquiv S G H, induced_iff⟩

private abbrev groundIso {G H : GroupScheme k} (i : G ≅ H) :
    relativePoints G V ≅ relativePoints H V :=
  (yonedaGrp ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.forget V).op).mapIso i

private theorem schemeIsoEquiv_ground {G H : GroupScheme k} (i : G ≅ H) :
    schemeIsoEquiv S G H ((groupBaseChange k S).mapIso i) = groundIso i := by
  apply (induced_iff _ _).mp
  intro U x
  change x.left ≫ i.hom.hom.hom.left =
    pullback.lift x.left U.hom.left _ ≫ ((baseChange k S).map i.hom.hom.hom).left ≫
      pullback.fst H.X.hom (fieldSpecMap k S)
  simp only [baseChange, Over.pullback_map_left, pullback.lift_fst, pullback.lift_fst_assoc]

private theorem restrict_ground {G H : GroupScheme k} (i : G ≅ H) (σ : Gal(S/k)) :
    restrictIso (fieldMap k S σ) (groundIso i) = groundIso i := by
  apply Iso.ext
  apply NatTrans.ext
  funext U
  rfl

end SchemeComparison

section Coordinates

variable {A B : HopfAlgebraCategory k}

private abbrev scalar (A : HopfAlgebraCategory k) (σ : Gal(S/k)) :
    extendedHopf S A →+* extendedHopf S A :=
  (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k A)).toRingHom

private theorem scalar_apply (A : HopfAlgebraCategory k) (σ : Gal(S/k)) (x : extendedHopf S A) :
    scalar A σ x = (SemilinearAction.scalarExtension (K := S) A).act σ x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private abbrev projection (A : HopfAlgebraCategory k) :
    Spec (CommRingCat.of (extendedHopf S A)) ⟶ (specGroup A).X.left :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : A →ₐ[k] S ⊗[k] A).toRingHom)

private abbrev scalarSpec (A : HopfAlgebraCategory k) (σ : Gal(S/k)) :
    Spec (CommRingCat.of (extendedHopf S A)) ⟶ Spec (CommRingCat.of (extendedHopf S A)) :=
  Spec.map (CommRingCat.ofHom (scalar A σ))

private theorem scalarSpec_projection (A : HopfAlgebraCategory k) (σ : Gal(S/k)) :
    scalarSpec A σ ≫ projection (S := S) A = projection A := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change A at x
  change (σ 1) ⊗ₜ[k] x = (1 : S) ⊗ₜ[k] x
  rw [map_one]

private theorem scalarSpec_field (A : HopfAlgebraCategory k) (σ : Gal(S/k)) :
    scalarSpec A σ ≫ (specGroup (extendedHopf S A)).X.hom =
      (specGroup (extendedHopf S A)).X.hom ≫ (fieldMap k S σ).left := by
  change Spec.map (CommRingCat.ofHom (scalar A σ)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S (extendedHopf S A))) =
    Spec.map (CommRingCat.ofHom (algebraMap S (extendedHopf S A))) ≫
      Spec.map (CommRingCat.ofHom σ.toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

variable (t : ∀ C : HopfAlgebraCategory k,
  specGroup (extendedHopf S C) ≅ (groupBaseChange k S).obj (specGroup C))
variable (ht : IsScalarExtensionComparison t)

private abbrev coordinatePoint (U : Over V) (x : U.left ⟶ (specGroup A).X) :
    U.left.left ⟶ Spec (CommRingCat.of (extendedHopf S A)) :=
  pullback.lift x.left U.hom.left ((Over.w x).trans (Over.w U.hom).symm) ≫
    (t A).inv.hom.hom.left

include ht in
private theorem coordinatePoint_projection (U : Over V) (x : U.left ⟶ (specGroup A).X) :
    coordinatePoint t U x ≫ projection A = x.left := by
  have he : (t A).hom.hom.hom.left ≫
      pullback.fst (specGroup A).X.hom (fieldSpecMap k S) = projection (S := S) A := ht A
  rw [← he]
  let e := (Grp.forget _ ⋙ Over.forget _).mapIso (t A)
  change (pullback.lift x.left U.hom.left _ ≫ e.inv) ≫ e.hom ≫
    pullback.fst (specGroup A).X.hom (fieldSpecMap k S) = _
  rw [Category.assoc, Iso.inv_hom_id_assoc, pullback.lift_fst]

private theorem coordinatePoint_field (U : Over V) (x : U.left ⟶ (specGroup A).X) :
    coordinatePoint t U x ≫ (specGroup (extendedHopf S A)).X.hom = U.hom.left := by
  rw [Category.assoc, Over.w (t A).inv.hom.hom]
  exact pullback.lift_snd ..

include ht in
private theorem coordinatePoint_ext {X : Scheme.{u}}
    {p q : X ⟶ Spec (CommRingCat.of (extendedHopf S A))}
    (h₁ : p ≫ projection A = q ≫ projection A)
    (h₂ : p ≫ (specGroup (extendedHopf S A)).X.hom =
      q ≫ (specGroup (extendedHopf S A)).X.hom) : p = q := by
  let e := (t A).hom.hom.hom.left
  let : IsIso e := ((Grp.forget _ ⋙ Over.forget _).mapIso (t A)).isIso_hom
  apply (cancel_mono e).mp
  apply pullback.hom_ext
  · simpa only [Category.assoc, e, ht A] using h₁
  · have hs : e ≫ pullback.snd (specGroup A).X.hom (fieldSpecMap k S) =
        (specGroup (extendedHopf S A)).X.hom := Over.w (t A).hom.hom.hom
    simpa only [Category.assoc, hs] using h₂

include ht in
private theorem coordinatePoint_restrict (σ : Gal(S/k)) (U : Over V)
    (x : U.left ⟶ (specGroup A).X) :
    coordinatePoint t ((Over.map (fieldMap k S σ)).obj U) x =
      coordinatePoint t U x ≫ scalarSpec A σ := by
  apply coordinatePoint_ext t ht
  · rw [coordinatePoint_projection t ht, Category.assoc, scalarSpec_projection,
      coordinatePoint_projection t ht]
  · rw [coordinatePoint_field, Category.assoc, scalarSpec_field, ← Category.assoc,
      coordinatePoint_field]
    rfl

variable {G H : GroupScheme k}

private abbrev hopfSchemeIso (g : specGroup A ≅ G) (h : specGroup B ≅ H)
    (i : extendedHopf S A ≅ extendedHopf S B) :
    (groupBaseChange k S).obj G ≅ (groupBaseChange k S).obj H :=
  (t A ≪≫ (groupBaseChange k S).mapIso g).symm ≪≫
    spectrumIso i ≪≫ t B ≪≫ (groupBaseChange k S).mapIso h

variable (g : specGroup A ≅ G) (h : specGroup B ≅ H)

private def hopfIsoEquiv :
    (extendedHopf S A ≅ extendedHopf S B) ≃ (relativePoints G V ≅ relativePoints H V) :=
  (spectrumIsoEquiv _ _).trans
    ((Iso.isoCongr (t A ≪≫ (groupBaseChange k S).mapIso g)
      (t B ≪≫ (groupBaseChange k S).mapIso h)).trans (schemeIsoEquiv S G H))

private theorem hopfIsoEquiv_apply (i : extendedHopf S A ≅ extendedHopf S B) :
    hopfIsoEquiv t g h i = schemeIsoEquiv S G H (hopfSchemeIso t g h i) := rfl

private theorem hopfInduced_iff (i : extendedHopf S A ≅ extendedHopf S B)
    (r : relativePoints G V ≅ relativePoints H V) :
    IsInducedByHopf t g h i r ↔ hopfIsoEquiv t g h i = r :=
  induced_iff (hopfSchemeIso t g h i) r

private theorem hopfIsoEquiv_ground (i : extendedHopf S A ≅ extendedHopf S B) :
    hopfIsoEquiv t g h i = groundIso g.symm ≪≫
      hopfIsoEquiv t (Iso.refl (specGroup A)) (Iso.refl (specGroup B)) i ≪≫ groundIso h := by
  rw [← schemeIsoEquiv_ground (S := S) g.symm, ← schemeIsoEquiv_ground (S := S) h]
  simp only [hopfIsoEquiv_apply, ← schemeIsoEquiv_trans, hopfSchemeIso,
    Functor.mapIso_refl, Iso.trans_refl, Functor.mapIso_symm, Iso.trans_symm, Iso.trans_assoc]

include ht in
private theorem hopfIsoEquiv_evaluate (i : extendedHopf S A ≅ extendedHopf S B)
    (U : Over V) (x : U.left ⟶ (specGroup A).X) :
    (((hopfIsoEquiv t (Iso.refl (specGroup A)) (Iso.refl (specGroup B)) i).hom.app
      (op U)).hom x).left =
      coordinatePoint t U x ≫ Spec.map (CommRingCat.ofHom i.inv.hom.toAlgHom.toRingHom) ≫
        projection B := by
  have he := schemeIsoEquiv_apply
    (hopfSchemeIso t (Iso.refl (specGroup A)) (Iso.refl (specGroup B)) i) U x
  have hp : (t B).hom.hom.hom.left ≫
      pullback.fst (specGroup B).X.hom (fieldSpecMap k S) = projection (S := S) B := ht B
  rw [hopfIsoEquiv_apply, he, ← hp]
  simp only [hopfSchemeIso, Functor.mapIso_refl, Iso.trans_refl, Iso.symm_hom, Iso.trans_hom,
    Grp.comp_hom_hom, Over.comp_left, Category.assoc]
  rfl

private theorem conjugates_inverse (σ : Gal(S/k))
    {i j : extendedHopf S A ≅ extendedHopf S B} (hσ : HopfConjugates σ i j) :
    ∀ y, scalar A σ (i.inv.hom y) = j.inv.hom (scalar B σ y) := by
  intro y
  have h := congrArg j.inv.hom (hσ (i.inv.hom y))
  simpa only [← scalar_apply, show ∀ x, j.inv.hom (j.hom.hom x) = x from
    ConcreteCategory.congr_hom j.hom_inv_id, show ∀ x, i.hom.hom (i.inv.hom x) = x from
    ConcreteCategory.congr_hom i.inv_hom_id] using h

private theorem spectrum_conjugates (σ : Gal(S/k))
    {i j : extendedHopf S A ≅ extendedHopf S B} (hσ : HopfConjugates σ i j) :
    scalarSpec A σ ≫ Spec.map (CommRingCat.ofHom i.inv.hom.toAlgHom.toRingHom) =
    Spec.map (CommRingCat.ofHom j.inv.hom.toAlgHom.toRingHom) ≫ scalarSpec B σ := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro y
  exact conjugates_inverse σ hσ y

include ht in
private theorem restrict_hopfIso_spec (σ : Gal(S/k))
    {i j : extendedHopf S A ≅ extendedHopf S B} (hσ : HopfConjugates σ i j) :
    restrictIso (fieldMap k S σ)
      (hopfIsoEquiv t (Iso.refl (specGroup A)) (Iso.refl (specGroup B)) i) =
    hopfIsoEquiv t (Iso.refl (specGroup A)) (Iso.refl (specGroup B)) j := by
  apply Iso.ext
  apply NatTrans.ext
  funext U
  apply GrpCat.ext
  intro x
  change U.unop.left ⟶ (specGroup A).X at x
  apply Over.OverMorphism.ext
  let U' := (Over.map (fieldMap k S σ)).obj U.unop
  change (((hopfIsoEquiv t (Iso.refl (specGroup A)) (Iso.refl (specGroup B)) i).hom.app
    (op U')).hom x).left = _
  rw [hopfIsoEquiv_evaluate t ht i U' x, hopfIsoEquiv_evaluate t ht j U.unop x,
    coordinatePoint_restrict t ht, Category.assoc, ← Category.assoc (scalarSpec A σ),
    spectrum_conjugates σ hσ]
  simp only [Category.assoc, scalarSpec_projection]

private theorem restrict_trans {G H J : GroupScheme k}
    (σ : Gal(S/k)) (i : relativePoints G V ≅ relativePoints H V)
    (j : relativePoints H V ≅ relativePoints J V) :
    restrictIso (fieldMap k S σ) (i ≪≫ j) =
      restrictIso (fieldMap k S σ) i ≪≫ restrictIso (fieldMap k S σ) j := by
  apply Iso.ext
  rfl

include ht in
private theorem restrict_hopfIso (σ : Gal(S/k))
    {i j : extendedHopf S A ≅ extendedHopf S B} (hσ : HopfConjugates σ i j) :
    restrictIso (fieldMap k S σ) (hopfIsoEquiv t g h i) = hopfIsoEquiv t g h j := by
  rw [hopfIsoEquiv_ground, restrict_trans, restrict_trans, restrict_ground, restrict_ground,
    restrict_hopfIso_spec t ht σ hσ, ← hopfIsoEquiv_ground]

private theorem conjugates_exists (σ : Gal(S/k)) (i : extendedHopf S A ≅ extendedHopf S B) :
    ∃ j, HopfConjugates σ i j := by
  refine ⟨(transportedDifference i σ).asIso ≪≫ i, ?_⟩
  intro x
  have hd := difference_apply (transported i) (standard S A) σ x
  rw [transported_apply] at hd
  change i.hom.hom ((transportedDifference i σ).asIso.hom.hom
    ((SemilinearAction.scalarExtension (K := S) A).act σ x)) = _
  rw [show (transportedDifference i σ).asIso.hom.hom
    ((SemilinearAction.scalarExtension (K := S) A).act σ x) =
      i.inv.hom ((SemilinearAction.scalarExtension (K := S) B).act σ (i.hom.hom x)) from hd]
  exact ConcreteCategory.congr_hom i.inv_hom_id _

theorem hopfIsomorphismComparison : HopfIsomorphismComparison.{u} := by
  intro k S _ _ _ A B G H t ht g h
  refine ⟨hopfIsoEquiv t g h, hopfInduced_iff t g h, fun σ i j => ⟨
    restrict_hopfIso t ht g h σ, ?_⟩⟩
  intro he
  obtain ⟨j', hj'⟩ := conjugates_exists σ i
  have hj := (hopfIsoEquiv t g h).injective ((restrict_hopfIso t ht g h σ hj').symm.trans he)
  rwa [← hj]

private theorem hopfIsoEquiv_trans {C : HopfAlgebraCategory k} {J : GroupScheme k}
    (l : specGroup C ≅ J)
    (i : extendedHopf S A ≅ extendedHopf S B) (j : extendedHopf S B ≅ extendedHopf S C) :
    hopfIsoEquiv t g l (i ≪≫ j) = hopfIsoEquiv t g h i ≪≫ hopfIsoEquiv t h l j := by
  simp only [hopfIsoEquiv_apply, spectrumIso_trans, hopfSchemeIso, ← schemeIsoEquiv_trans]
  apply Iso.ext
  simp

include ht in
private theorem hopf_transport (i : extendedHopf S A ≅ extendedHopf S B)
    {ρ : Gal(S/k) →* MulAut (Coefficients S A)}
    {a : @Cocycle (Gal(S/k)) (Coefficients S A) _ (krullTopology k S) _ ⊥ ρ}
    (ha : IsTransportedCocycle i a) (σ : Gal(S/k)) :
    hopfIsoEquiv t g g (a σ).asIso =
      (transportedAut k S (hopfIsoEquiv t g h i) σ).asIso := by
  have hσ : HopfConjugates σ i ((a σ).asIso ≪≫ i) := by
    intro x
    change i.hom.hom ((a σ).asIso.hom.hom _) = _
    rw [ha σ x]
    exact ConcreteCategory.congr_hom i.inv_hom_id _
  change _ = restrictIso (fieldMap k S σ) (hopfIsoEquiv t g h i) ≪≫
    (hopfIsoEquiv t g h i).symm
  rw [restrict_hopfIso t ht g h σ hσ, hopfIsoEquiv_trans t g g h,
    Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]

theorem hopfCocycleComparison : HopfCocycleComparison.{u} := by
  intro k S _ _ _ A B G H t ht g h i r hr ρ a ha σ
  rw [← (hopfInduced_iff t g h i r).mp hr]
  exact (hopfInduced_iff t g g _ _).mpr (hopf_transport t ht g h i ha σ)

end Coordinates

section ClassificationProof

local instance relativeTopology (G : GroupScheme k) :
    TopologicalSpace (RelativeAut G V) := ⊥

local instance relativeDiscrete (G : GroupScheme k) :
    DiscreteTopology (RelativeAut G V) := ⟨rfl⟩

local instance hopfTopology (A : HopfAlgebraCategory k) :
    TopologicalSpace (Coefficients S A) := ⊥

local instance hopfDiscrete (A : HopfAlgebraCategory k) :
    DiscreteTopology (Coefficients S A) := ⟨rfl⟩

private def coefficientEquiv {A : HopfAlgebraCategory k} {G : GroupScheme k}
    (t : ∀ C : HopfAlgebraCategory k,
      specGroup (extendedHopf S C) ≅ (groupBaseChange k S).obj (specGroup C))
    (g : specGroup A ≅ G) : Coefficients S A ≃* RelativeAut G V where
  toEquiv := Aut.isoEquiv.trans ((hopfIsoEquiv t g g).trans Aut.isoEquiv.symm)
  map_mul' a b := by
    apply Aut.ext
    exact hopfIsoEquiv_trans t g g g b.asIso a.asIso

set_option maxHeartbeats 1000000 in
theorem relativeFormClassification : Classification.{u} := by
  intro k S _ _ _ _ G
  obtain ⟨A, hA, g, t, e, _, ht, hbase, he, _, _⟩ := schemeComparison (K := S) G
  obtain ⟨ρ, d, hρ, hcont, hd, hcomputes, hrealizes⟩ := separableClosureForms (S := S) A hA
  let c := coefficientEquiv t g
  have ha (σ : Gal(S/k)) (b : Coefficients S A) :
      c (ρ σ b) = automorphismAction k S G.val σ (c b) := by
    apply Aut.ext
    exact (restrict_hopfIso t ht g g σ (hρ σ b)).symm
  have haction : relabelAction c ρ = automorphismAction k S G.val := by
    apply MonoidHom.ext
    intro σ
    apply MulEquiv.ext
    intro b
    change c (ρ σ (c.symm b)) = _
    rw [ha, c.apply_symm_apply]
  suffices ∃ q : SchemeFormClasses S G ≃ H1 (relabelAction c ρ),
      Continuous (fun p : Gal(S/k) × RelativeAut G.val (fieldTest k S) =>
        relabelAction c ρ p.1 p.2) ∧
      q (Quotient.mk _ ⟨G, ⟨Iso.refl _⟩⟩) = basepoint (relabelAction c ρ) ∧
      (∀ (H : SchemeModels S G)
        (i : relativePoints G.val (fieldTest k S) ≅ relativePoints H.val.val (fieldTest k S)),
        ∃ a : Cocycle (relabelAction c ρ),
          (∀ σ, a σ = transportedAut k S i σ) ∧ q (Quotient.mk _ H) = classOf a) ∧
      ∀ a : Cocycle (relabelAction c ρ), ∃ (H : SchemeModels S G)
        (i : relativePoints G.val (fieldTest k S) ≅ relativePoints H.val.val (fieldTest k S)),
        (∀ σ, a σ = transportedAut k S i σ) ∧ q (Quotient.mk _ H) = classOf a by
    rw [haction] at this
    obtain ⟨q, hq, hb, hqcompute, hqrealize⟩ := this
    exact ⟨⟨q, hq, hb, hqcompute, hqrealize⟩⟩
  let q := e.symm.trans (d.trans (cohomologyRelabel c))
  have hclass (B : Models S A) (a : Cocycle ρ) (hb : d (Quotient.mk _ B) = classOf a) :
      q (Quotient.mk _ (realizeSchemeModel S g t B)) = classOf (relabelCocycle c a) := by
    change cohomologyRelabel c (d (e.symm (Quotient.mk _ (realizeSchemeModel S g t B)))) = _
    rw [← he, e.symm_apply_apply, hb]
    rfl
  have hvalues {B : HopfAlgebraCategory k} {H : GroupScheme k} (h : specGroup B ≅ H)
      (i : extendedHopf S A ≅ extendedHopf S B) {a : Cocycle ρ}
      (hi : IsTransportedCocycle i a) (σ : Gal(S/k)) :
      relabelCocycle c a σ = transportedAut k S (hopfIsoEquiv t g h i) σ := by
    apply Aut.ext
    exact hopf_transport t ht g h i hi σ
  refine ⟨q, relabelAction_continuous c hcont, ?_, ?_, ?_⟩
  · change cohomologyRelabel c (d (e.symm (Quotient.mk _ ⟨G, ⟨Iso.refl _⟩⟩))) = _
    rw [← hbase, e.symm_apply_apply, hd, cohomologyRelabel_basepoint]
  · intro H i
    obtain ⟨B, hB, ⟨h⟩⟩ := exists_coordinate_model H.val
    let j := (hopfIsoEquiv t g h).symm i
    have hj : hopfIsoEquiv t g h j = i := (hopfIsoEquiv t g h).apply_symm_apply i
    let M : Models S A := ⟨B, hB, ⟨j⟩⟩
    obtain ⟨a, ha, hqa⟩ := hcomputes M j
    refine ⟨relabelCocycle c a, fun σ => ?_, ?_⟩
    · rw [← hj]
      exact hvalues h j ha σ
    · have hM : Quotient.mk (schemeModelSetoid S G) (realizeSchemeModel S g t M) =
          Quotient.mk (schemeModelSetoid S G) H := by
        apply Quotient.sound
        exact ⟨h⟩
      rw [← hM]
      exact hclass M a hqa
  · intro a
    obtain ⟨b, rfl⟩ := relabelCocycle_surjective c a
    obtain ⟨B, i, hb⟩ := hrealizes b
    let H := realizeSchemeModel S g t B
    let j := hopfIsoEquiv t g (Iso.refl (specGroup B.val)) i
    refine ⟨H, j, hvalues (Iso.refl _) i hb, ?_⟩
    obtain ⟨a', ha', hqa'⟩ := hcomputes B i
    have hba : b = a' := by
      apply Subtype.ext
      funext σ
      apply Aut.ext
      have e₁ := hopf_transport t ht g (Iso.refl (specGroup B.val)) i hb σ
      have e₂ := hopf_transport t ht g (Iso.refl (specGroup B.val)) i ha' σ
      exact (hopfIsoEquiv t g g).injective (e₁.trans e₂.symm)
    rw [hba]
    exact hclass B a' hqa'

end ClassificationProof

end

end LinearAlgebraicGroups.Descent.RelativeFormComparison
