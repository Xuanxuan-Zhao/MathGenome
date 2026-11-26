import Specs.LinearAlgebraicGroups.Arithmetic.CentralCoverDescent
import LinearAlgebraicGroups.Arithmetic.CentralCoverInnerLift
import LinearAlgebraicGroups.Arithmetic.CentralCoverPinnedLift
import LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import LinearAlgebraicGroups.Classification.PinnedEquivalence
import LinearAlgebraicGroups.Descent.AutomorphismSequence
import Mathlib.AlgebraicGeometry.Artinian
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Arithmetic.CentralCoverDescent

open _root_.LinearAlgebraicGroups.Specs
open Specs.CentralIsogenies (IsCentralIsogeny IsTorusRestriction)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.GeometricRadicals (GeometricGroup IsSemisimple IsSplitTorus)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Descent Descent.Forms
open Descent.NonabelianCohomology (Cocycle)

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open private standard standardAct descend_standard_hom coefficientAction coefficientAction_apply
  transportedDifference transportedCocycle transportedCocycle_spec formAction twist evalAut eval_mul
  baseHom_equivariant
  from LinearAlgebraicGroups.Descent.Forms
open private comparison_equivariant from LinearAlgebraicGroups.Descent.AffineGroups
open private LinearAlgebraicGroups.extendedGroupIso LinearAlgebraicGroups.extendedSpecIso_natural
  LinearAlgebraicGroups.specGroupMap_comp from LinearAlgebraicGroups.Affine.ClosedSubgroups

variable {k E : Type u} [Field k] [Field E] [Algebra k E]

set_option backward.isDefEq.respectTransparency false in
private theorem descendEquivariantHopfMap [FiniteDimensional k E] [IsGalois k E]
    {Q : HopfAlgebraCategory k} {B : HopfAlgebraCategory E}
    (D : HopfDescentDatum k B) (hB : Algebra.FiniteType E B)
    (f : extendedHopf E Q ⟶ B) (hf : (standard E Q).Equivariant D f) :
    ∃ (U : HopfAlgebraCategory k) (_ : Algebra.FiniteType k U)
      (g : Q ⟶ U) (j : extendedHopf E U ≅ B),
      extendedHopfMap E g ≫ j.hom = f := by
  let H := descendHopf D
  letI := H.operations.toHopfAlgebra
  have hc := comparison_equivariant H
  have he : (standard E Q).Equivariant (standard E H.algebra) (f ≫ H.iso.inv) := by
    intro σ x
    change H.iso.inv.hom (f.hom ((standardAct E Q).act σ x)) =
      (standardAct E H.algebra).act σ (H.iso.inv.hom (f.hom x))
    apply H.comparison.injective
    have h := hc σ (H.iso.inv.hom (f.hom x))
    change H.comparison ((standardAct E H.algebra).act σ (H.iso.inv.hom (f.hom x))) =
      D.action.act σ (H.comparison (H.iso.inv.hom (f.hom x))) at h
    change H.comparison (H.iso.inv.hom (f.hom ((standardAct E Q).act σ x))) =
      H.comparison ((standardAct E H.algebra).act σ (H.iso.inv.hom (f.hom x)))
    rw [h]
    change H.comparison (H.comparison.symm (f.hom ((standardAct E Q).act σ x))) =
      D.action.act σ (H.comparison (H.comparison.symm (f.hom x)))
    rw [H.comparison.apply_symm_apply, H.comparison.apply_symm_apply]
    exact hf σ x
  obtain ⟨g, hg⟩ := descend_standard_hom (f ≫ H.iso.inv) he
  exact ⟨H.algebra, (affineDescentProperties H).1 hB, g, H.iso, by rw [hg, Category.assoc, H.iso.inv_hom_id, Category.comp_id]⟩

variable [FiniteDimensional k E] [IsGalois k E]

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem descendHopfFormOfMap
    {P Q R : HopfAlgebraCategory k} (hR : Algebra.FiniteType k R)
    (p : P ⟶ R) (i : extendedHopf E P ≅ extendedHopf E Q)
    (hlift : ∀ b : Aut (extendedHopf E P),
      ∃! c : Aut (extendedHopf E R),
        b.asIso.hom ≫ extendedHopfMap E p = extendedHopfMap E p ≫ c.asIso.hom) :
    ∃ (U : HopfAlgebraCategory k) (_ : Algebra.FiniteType k U)
      (g : Q ⟶ U) (j : extendedHopf E U ≅ extendedHopf E R),
      extendedHopfMap E g ≫ j.hom = i.inv ≫ extendedHopfMap E p := by
  classical
  letI : TopologicalSpace (Aut (extendedHopf E P)) := ⊥
  letI : TopologicalSpace (Aut (extendedHopf E R)) := ⊥
  let f := extendedHopfMap E p
  let L (b : Aut (extendedHopf E P)) := (hlift b).exists.choose
  have hL (b : Aut (extendedHopf E P)) : b.asIso.hom ≫ f = f ≫ (L b).asIso.hom :=
    (hlift b).exists.choose_spec
  have hu (b : Aut (extendedHopf E P)) (c : Aut (extendedHopf E R))
      (hc : b.asIso.hom ≫ f = f ≫ c.asIso.hom) : L b = c :=
    (hlift b).unique (hL b) hc
  have hLe (b : Aut (extendedHopf E P)) (x : extendedHopf E P) :
      f.hom (evalAut b x) = evalAut (L b) (f.hom x) :=
    ConcreteCategory.congr_hom (hL b) x
  have hmul (b c : Aut (extendedHopf E P)) : L (b * c) = L b * L c := by
    apply hu
    apply CommHopfAlgCat.hom_ext
    apply BialgHom.ext
    intro x
    change f.hom (evalAut (b * c) x) = evalAut (L b * L c) (f.hom x)
    rw [eval_mul, eval_mul, hLe, hLe]
  have hstd (σ : Gal(E/k)) (x : extendedHopf E P) :
      f.hom ((standardAct E P).act σ x) = (standardAct E R).act σ (f.hom x) :=
    baseHom_equivariant (K := E) p σ x
  have hscalar (V : HopfAlgebraCategory k) (σ : Gal(E/k))
      (b : Aut (extendedHopf E V)) (x : extendedHopf E V) :
      evalAut (formAction E V σ b) ((standardAct E V).act σ x) =
        (standardAct E V).act σ (evalAut b x) :=
    coefficientAction_apply (standard E V) σ b x
  have het (σ : Gal(E/k)) (b : Aut (extendedHopf E P)) :
      L (formAction E P σ b) = formAction E R σ (L b) := by
    apply hu
    apply CommHopfAlgCat.hom_ext
    apply BialgHom.ext
    intro x
    obtain ⟨y, rfl⟩ := ((standardAct E P).act σ).surjective x
    change f.hom (evalAut (formAction E P σ b) ((standardAct E P).act σ y)) =
      evalAut (formAction E R σ (L b)) (f.hom ((standardAct E P).act σ y))
    rw [hscalar, hstd, hstd, hscalar, hLe]
  let a := transportedCocycle i continuous_of_discreteTopology
  let c : Cocycle (formAction E R) :=
    ⟨fun σ => L (a σ), continuous_of_discreteTopology, fun σ τ => by
      change L (a (σ * τ)) = L (a σ) * formAction E R σ (L (a τ))
      have ha : a (σ * τ) = a σ * formAction E P σ (a τ) := a.property.2 σ τ
      exact (congrArg L ha).trans ((hmul (a σ) (formAction E P σ (a τ))).trans
        (congrArg (fun z => L (a σ) * z) (het σ (a τ))))⟩
  let D := twist (standard E R) c
  have hmap : (standard E Q).Equivariant D (i.inv ≫ f) := by
    intro σ x
    let y : extendedHopf E P := i.inv.hom x
    have hy : i.hom.hom y = x := ConcreteCategory.congr_hom i.inv_hom_id x
    have ha := transportedCocycle_spec i (h := continuous_of_discreteTopology) σ y
    change evalAut (a σ) ((standardAct E P).act σ y) =
      i.inv.hom ((standardAct E Q).act σ (i.hom.hom y)) at ha
    change f.hom (i.inv.hom ((standardAct E Q).act σ x)) =
      evalAut (L (a σ)) ((standardAct E R).act σ (f.hom y))
    calc
      _ = f.hom (evalAut (a σ) ((standardAct E P).act σ y)) :=
        congrArg f.hom ((congrArg (fun z => i.inv.hom ((standardAct E Q).act σ z))
          hy.symm).trans ha.symm)
      _ = _ := by rw [hLe, hstd]
  haveI := hR
  exact descendEquivariantHopfMap D (by change Algebra.FiniteType E (E ⊗[k] R); infer_instance)
    (i.inv ≫ f) hmap


open CategoryTheory.Limits
open private centralIsogeny_postIso from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private transportSubgroup from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private maximalTransport from LinearAlgebraicGroups.Classification.PinnedEquivalence
open private groupBaseChangeTower smooth_baseChange_iff connected_baseChange_iff
  radical_transport solvable_of_iso from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private geometricallyConnected_of_connected from LinearAlgebraicGroups.Solvable.WordDomainGeometry

private abbrev forgetScheme (k : Type u) [Field k] : GroupScheme k ⥤ Scheme.{u} :=
  Grp.forget (SchemeOver k) ⋙ Over.forget _

set_option maxHeartbeats 450000 in
set_option backward.isDefEq.respectTransparency false in
private theorem centralIsogeny_preIso {G H J : GroupScheme k} {f : H ⟶ J}
    (e : G ≅ H) (hf : IsCentralIsogeny f) : IsCentralIsogeny (e.hom ≫ f) := by
  obtain ⟨hfin, hflat, hsurj, N, hN, hc⟩ := hf
  letI := hfin
  letI := hflat
  letI := hsurj
  letI : IsIso e.hom.hom.hom.left := (forgetScheme k).map_isIso e.hom
  let N' := transportSubgroup e.symm N
  refine ⟨inferInstanceAs (IsFinite (e.hom.hom.hom.left ≫ f.hom.hom.left)),
    inferInstanceAs (Flat (e.hom.hom.hom.left ≫ f.hom.hom.left)),
    inferInstanceAs (Surjective (e.hom.hom.hom.left ≫ f.hom.hom.left)), N', ?_, ?_⟩
  · refine hN.of_iso (Iso.refl _) ((Grp.forget (SchemeOver k)).mapIso e.symm)
        (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · change N.inclusion.hom.hom ≫ e.inv.hom.hom = 𝟙 _ ≫
        (N.inclusion.hom.hom ≫ e.inv.hom.hom)
      rw [Category.id_comp]
    · simp
    · change f.hom.hom ≫ 𝟙 _ = e.inv.hom.hom ≫ e.hom.hom.hom ≫ f.hom.hom
      simp only [Category.comp_id, ← Category.assoc]
      rw [← Grp.comp_hom_hom, e.inv_hom_id]
      exact (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · apply (centralizes_iff _ _).mpr
    intro U t x
    have hc' := (centralizes_iff _ _).mp hc U t (x ≫ e.hom.hom.hom)
    have c := hc'.map (((yonedaGrp.map e.inv).app (op U)).hom)
    change Commute ((t ≫ (N.inclusion.hom.hom ≫ e.inv.hom.hom))) (x ≫ 𝟙 G.X)
    change Commute ((t ≫ N.inclusion.hom.hom) ≫ e.inv.hom.hom)
      (((x ≫ e.hom.hom.hom) ≫ 𝟙 H.X) ≫ e.inv.hom.hom) at c
    simpa only [Category.assoc, Category.comp_id, ← Grp.comp_hom_hom, e.hom_inv_id,
      Grp.id_hom_hom] using c

set_option backward.isDefEq.respectTransparency false in
private def geometricIsoOfForm {H H₀ : AffineAlgebraicGroup k}
    (e : (groupBaseChange k E).obj H.val ≅ (groupBaseChange k E).obj H₀.val) :
    (GeometricGroup H).val ≅ (GeometricGroup H₀).val := by
  let C := AlgebraicClosure k
  let f : E →ₐ[k] C := IsAlgClosed.lift
  letI : Algebra E C := f.toRingHom.toAlgebra
  letI : IsScalarTower k E C := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (f.commutes a).symm)
  let t := groupBaseChangeTower (k := k) (K := E) C
  exact t.app H.val ≪≫ (groupBaseChange E C).mapIso e ≪≫ (t.app H₀.val).symm

private theorem geometricSimpleConnectednessOfForm {H H₀ : AffineAlgebraicGroup k}
    (e : (groupBaseChange k E).obj H.val ≅ (groupBaseChange k E).obj H₀.val)
    (h : GeometricallySimplyConnected H₀) : GeometricallySimplyConnected H := by
  intro J hJ q hq
  let c := geometricIsoOfForm (H := H) (H₀ := H₀) e
  letI := h J hJ (q ≫ c.hom) (centralIsogeny_postIso c hq)
  exact IsIso.of_isIso_comp_right q c.hom

set_option backward.isDefEq.respectTransparency false in
private theorem semisimplicityOfForm {H H₀ : AffineAlgebraicGroup k}
    (e : (groupBaseChange k E).obj H.val ≅ (groupBaseChange k E).obj H₀.val)
    (h : IsSemisimple H₀) : IsSemisimple H := by
  let F := AlgebraicClosure k
  let c := geometricIsoOfForm (H := H) (H₀ := H₀) e
  let m := (forgetScheme F).mapIso c
  have hw : m.hom ≫ (GeometricGroup H₀).val.X.hom = (GeometricGroup H).val.X.hom :=
    c.hom.hom.hom.w
  have hs₀ := (smooth_baseChange_iff (K := F) H₀.val.X).mpr h.1
  have hs : Smooth (GeometricGroup H).val.X.hom := by
    rw [← hw]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @Smooth) m.hom _).mpr hs₀
  haveI : ConnectedSpace (GeometricGroup H₀).val.X.left :=
    h.2.1.geometrically_connectedSpace _ _ _ (IsPullback.of_hasPullback _ _)
  haveI : ConnectedSpace ((forgetScheme F).obj (GeometricGroup H₀).val : Scheme) :=
    ‹ConnectedSpace (GeometricGroup H₀).val.X.left›
  have hconn : ConnectedSpace (GeometricGroup H).val.X.left :=
    m.hom.homeomorph.symm.surjective.connectedSpace m.hom.homeomorph.symm.continuous
  letI := (connected_baseChange_iff (K := F) H).mp hconn
  refine ⟨(smooth_baseChange_iff (K := F) H.val.X).mp hs,
    geometricallyConnected_of_connected H, ?_⟩
  let R := Specs.GeometricRadicals.geometricSolvableRadical H₀
  have hR := LinearAlgebraicGroups.GeometricRadicals.geometricSolvableRadicalLargest H₀
  have hRt := radical_transport c.symm (fun J => Specs.SchemeDerivedGroup.IsSolvable J.val)
    (fun d hx hy => solvable_of_iso d hx.1 hx.2.1 hy.1 hy.2.1) R hR
  obtain ⟨j, _, _⟩ := LinearAlgebraicGroups.GeometricRadicals.radicalUnique (GeometricGroup H)
    (fun J => Specs.SchemeDerivedGroup.IsSolvable J.val)
    (LinearAlgebraicGroups.GeometricRadicals.geometricSolvableRadicalLargest H) hRt
  obtain ⟨i⟩ := h.2.2
  exact ⟨j ≪≫ i⟩


open private exists_coordinate_model spectrumIsoEquiv from LinearAlgebraicGroups.Descent.Forms

variable (E) in
private theorem spectrumExtensionNaturality {P Q : HopfAlgebraCategory k} (f : P ⟶ Q) :
    specGroupMap (extendedHopfMap E f) ≫ (LinearAlgebraicGroups.extendedGroupIso E P).hom =
      (LinearAlgebraicGroups.extendedGroupIso E Q).hom ≫ (groupBaseChange k E).map (specGroupMap f) := by
  apply Grp.hom_ext
  exact LinearAlgebraicGroups.extendedSpecIso_natural E f

set_option backward.isDefEq.respectTransparency false in
private theorem hopfLiftOfGroupLift
    {P R : HopfAlgebraCategory k} (p : P ⟶ R)
    (hlift : ∀ b : Aut (specGroup (extendedHopf E P)),
      ∃! c : Aut (specGroup (extendedHopf E R)),
        c.asIso.hom ≫ specGroupMap (extendedHopfMap E p) =
          specGroupMap (extendedHopfMap E p) ≫ b.asIso.hom) :
    ∀ b : Aut (extendedHopf E P), ∃! c : Aut (extendedHopf E R),
      b.asIso.hom ≫ extendedHopfMap E p = extendedHopfMap E p ≫ c.asIso.hom := by
  let toSpec (A : HopfAlgebraCategory E) : Aut A ≃ Aut (specGroup A) :=
    (Aut.isoEquiv : Aut A ≃ (A ≅ A)).trans
      ((Equiv.trans (Equiv.mk Iso.symm Iso.symm (fun _ => rfl) (fun _ => rfl)) (spectrumIsoEquiv A A)).trans
        (Aut.isoEquiv : Aut (specGroup A) ≃ (specGroup A ≅ specGroup A)).symm)
  have toSpec_hom (A : HopfAlgebraCategory E) (b : Aut A) :
      (toSpec A b).asIso.hom = specGroupMap b.asIso.hom := rfl
  intro b
  obtain ⟨d, hd, hu⟩ := hlift (toSpec _ b)
  let c := (toSpec (extendedHopf E R)).symm d
  have hc : toSpec _ c = d := (toSpec _).apply_symm_apply d
  refine ⟨c, ?_, ?_⟩
  · apply Quiver.Hom.op_inj
    apply (hopfSpec.fullyFaithful (R := CommRingCat.of E)).map_injective
    change specGroupMap (b.asIso.hom ≫ extendedHopfMap E p) =
      specGroupMap (extendedHopfMap E p ≫ c.asIso.hom)
    rw [LinearAlgebraicGroups.specGroupMap_comp, LinearAlgebraicGroups.specGroupMap_comp, ← toSpec_hom, ← toSpec_hom, hc, hd]
  · intro b' h
    apply (toSpec (extendedHopf E R)).injective
    rw [hc]
    apply hu
    simp only [toSpec_hom, ← LinearAlgebraicGroups.specGroupMap_comp, h]

set_option backward.isDefEq.respectTransparency false in
private theorem descendSchemeFormOfMap
    {G₀ H₀ G : AffineAlgebraicGroup k} (p₀ : H₀.val ⟶ G₀.val)
    (e : (groupBaseChange k E).obj G₀.val ≅ (groupBaseChange k E).obj G.val)
    (hlift : ∀ b : Aut ((groupBaseChange k E).obj G₀.val),
      ∃! c : Aut ((groupBaseChange k E).obj H₀.val),
        c.asIso.hom ≫ (groupBaseChange k E).map p₀ =
          (groupBaseChange k E).map p₀ ≫ b.asIso.hom) :
    ∃ (H : AffineAlgebraicGroup k) (q : H.val ⟶ G.val)
      (a : (groupBaseChange k E).obj H₀.val ≅ (groupBaseChange k E).obj H.val),
      a.hom ≫ (groupBaseChange k E).map q = (groupBaseChange k E).map p₀ ≫ e.hom := by
  let F := groupBaseChange k E
  obtain ⟨P, _, ⟨jP⟩⟩ := exists_coordinate_model G₀
  obtain ⟨Q, _, ⟨jQ⟩⟩ := exists_coordinate_model G
  obtain ⟨R, hR, ⟨jR⟩⟩ := exists_coordinate_model H₀
  let Y := hopfSpec.fullyFaithful (R := CommRingCat.of k)
  let p : P ⟶ R := (Y.preimage (jR.hom ≫ p₀ ≫ jP.inv)).unop
  have hp : specGroupMap p = jR.hom ≫ p₀ ≫ jP.inv := Y.map_preimage _
  let tP := LinearAlgebraicGroups.extendedGroupIso E P ≪≫ F.mapIso jP
  let tQ := LinearAlgebraicGroups.extendedGroupIso E Q ≪≫ F.mapIso jQ
  let tR := LinearAlgebraicGroups.extendedGroupIso E R ≪≫ F.mapIso jR
  let f := specGroupMap (extendedHopfMap E p)
  have hf : f ≫ tP.hom = tR.hom ≫ F.map p₀ := by
    change (f ≫ (LinearAlgebraicGroups.extendedGroupIso E P).hom) ≫ F.map jP.hom =
      (LinearAlgebraicGroups.extendedGroupIso E R).hom ≫ F.map jR.hom ≫ F.map p₀
    rw [spectrumExtensionNaturality, Category.assoc, ← F.map_comp, ← F.map_comp, hp]
    simp
  let i := (spectrumIsoEquiv _ _).symm (tP ≪≫ e ≪≫ tQ.symm)
  have hi : specGroupMap i.inv = tP.hom ≫ e.hom ≫ tQ.inv :=
    congrArg Iso.hom ((spectrumIsoEquiv _ _).apply_symm_apply (tP ≪≫ e ≪≫ tQ.symm))
  have liftSpectral (b : Aut (specGroup (extendedHopf E P))) :
      ∃! c : Aut (specGroup (extendedHopf E R)), c.asIso.hom ≫ f = f ≫ b.asIso.hom := by
    let b₀ := Aut.autMulEquivOfIso tP b
    obtain ⟨c₀, hc₀, hu⟩ := hlift b₀
    let L := Aut.autMulEquivOfIso tR
    have hback : F.map p₀ ≫ tP.inv = tR.inv ≫ f := by
      apply (cancel_mono tP.hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, hf, Iso.inv_hom_id_assoc]
    have hL (c : Aut (specGroup (extendedHopf E R))) :
        c.asIso.hom ≫ f = f ≫ b.asIso.hom ↔ (L c).asIso.hom ≫ F.map p₀ =
          F.map p₀ ≫ b₀.asIso.hom := by
      change _ ↔ (tR.inv ≫ c.asIso.hom ≫ tR.hom) ≫ F.map p₀ =
        F.map p₀ ≫ tP.inv ≫ b.asIso.hom ≫ tP.hom
      have hleft : (tR.inv ≫ c.asIso.hom ≫ tR.hom) ≫ F.map p₀ =
          tR.inv ≫ (c.asIso.hom ≫ f) ≫ tP.hom := by
        simp only [Category.assoc, hf]
      have hright : F.map p₀ ≫ tP.inv ≫ b.asIso.hom ≫ tP.hom =
          tR.inv ≫ (f ≫ b.asIso.hom) ≫ tP.hom := by
        rw [← Category.assoc (F.map p₀), hback]
        simp only [Category.assoc]
      rw [hleft, hright]
      simp only [← Category.assoc tR.inv _ tP.hom, cancel_epi, cancel_mono]
    exact ⟨L.symm c₀, (hL _).2 (by simpa only [MulEquiv.apply_symm_apply] using hc₀),
      fun c hc => L.injective (by simpa only [MulEquiv.apply_symm_apply] using hu (L c) ((hL c).1 hc))⟩
  obtain ⟨U, hU, g, j, hj⟩ := descendHopfFormOfMap hR p i (hopfLiftOfGroupLift p liftSpectral)
  let H := schemeModel U hU
  let q := specGroupMap g ≫ jQ.hom
  let a := tR.symm ≪≫ (spectrumIso j).symm ≪≫ LinearAlgebraicGroups.extendedGroupIso E U
  refine ⟨H, q, a, ?_⟩
  have h := congrArg (fun v => specGroupMap v) hj
  simp only [LinearAlgebraicGroups.specGroupMap_comp] at h
  change specGroupMap j.hom ≫ specGroupMap (extendedHopfMap E g) =
    f ≫ specGroupMap i.inv at h
  change (tR.inv ≫ specGroupMap j.hom ≫ (LinearAlgebraicGroups.extendedGroupIso E U).hom) ≫ F.map q =
    F.map p₀ ≫ e.hom
  rw [F.map_comp, Category.assoc, Category.assoc, ← Category.assoc (LinearAlgebraicGroups.extendedGroupIso E U).hom,
    ← spectrumExtensionNaturality]
  have hcomp :
      (specGroupMap j.hom ≫ specGroupMap (extendedHopfMap E g)) ≫ tQ.hom =
        (f ≫ specGroupMap i.inv) ≫ tQ.hom :=
    congrArg (fun v => v ≫ tQ.hom) h
  have hh : specGroupMap i.inv ≫ tQ.hom = tP.hom ≫ e.hom := by
    rw [hi]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have he : (f ≫ specGroupMap i.inv) ≫ tQ.hom = tR.hom ≫ F.map p₀ ≫ e.hom := by
    rw [Category.assoc, hh, ← Category.assoc, hf, Category.assoc]
  have heq := congrArg (fun v => tR.inv ≫ v) (hcomp.trans he)
  simpa only [tQ, Iso.trans_hom, Functor.mapIso_hom, Category.assoc, Iso.inv_hom_id_assoc] using heq



open Specs.Pinning (SplitBorelPair PinnedGroup AttachedDatum BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model fibre splitTorus)
open Specs.RationalRealization (Realization)
open private fibreTowerIso model_simplyConnected corootSpan centralIsogeny_baseChange splitBorelPair
  from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies
open private pinnedLift from LinearAlgebraicGroups.Classification.PinnedEquivalence

private theorem baseChangeTorusMarking {D : BasedRootDatum.{u}} (M : Model D)
    {P : SplitBorelPair k} {Q : SplitBorelPair E}
    (e : (fibre k).obj M.group ≅ P.G.val) (t : (fibre k).obj (splitTorus D) ≅ P.T.group)
    (he : (fibre k).map M.torus ≫ e.hom = t.hom ≫ P.T.inclusion)
    (d : (fibre E).obj M.group ≅ Q.G.val) (s : (fibre E).obj (splitTorus D) ≅ Q.T.group)
    (hd : (fibre E).map M.torus ≫ d.hom = s.hom ≫ Q.T.inclusion) :
    ∃ (j : (groupBaseChange k E).obj P.G.val ≅ Q.G.val)
      (v : (groupBaseChange k E).obj P.T.group ≅ Q.T.group),
      v.hom ≫ Q.T.inclusion = (groupBaseChange k E).map P.T.inclusion ≫ j.hom := by
  let F := groupBaseChange k E
  let n := fibreTowerIso k E
  let j := (F.mapIso e).symm ≪≫ (n.app M.group).symm ≪≫ d
  let v := (F.mapIso t).symm ≪≫ (n.app (splitTorus D)).symm ≪≫ s
  refine ⟨j, v, ?_⟩
  have hn : (n.inv.app (splitTorus D)) ≫ (fibre E).map M.torus =
      F.map ((fibre k).map M.torus) ≫ n.inv.app M.group :=
    (n.inv.naturality M.torus).symm
  have hP : t.inv ≫ (fibre k).map M.torus = P.T.inclusion ≫ e.inv := by
    apply (cancel_mono e.hom).mp
    simp only [Category.assoc, he, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  change (F.map t.inv ≫ n.inv.app (splitTorus D) ≫ s.hom) ≫ Q.T.inclusion =
    F.map P.T.inclusion ≫ F.map e.inv ≫ n.inv.app M.group ≫ d.hom
  simp only [Category.assoc, ← hd]
  rw [← Category.assoc (n.inv.app (splitTorus D)), hn]
  simp only [← Category.assoc, ← F.map_comp, hP]

private theorem referenceTarget (G : AffineAlgebraicGroup k) (hG : IsSemisimple G)
    (S : ClosedSubgroup (baseChangedAlgebraicGroup E G).val)
    (hs : IsSplitTorus S.group) (hm : IsGeometricallyMaximal S) :
    ∃ (P : SplitBorelPair k) (j : (groupBaseChange k E).obj P.G.val ≅
        (groupBaseChange k E).obj G.val)
      (v : (groupBaseChange k E).obj P.T.group ≅ S.group),
      IsSemisimple P.G ∧ v.hom ≫ S.inclusion = (groupBaseChange k E).map P.T.inclusion ≫ j.hom := by
  let F := groupBaseChange k E
  let G' := baseChangedAlgebraicGroup E G
  have hG' := (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := E) G hG.1 hG.2.1).mpr hG
  let Q := splitBorelPair G' (reductive_of_semisimple G' hG') S hs hm
  let D := Classification.Pinning.attachedDatum Q
  obtain ⟨M⟩ := Classification.IntegralRealization.integralRealization D.toBased
  obtain ⟨_, U, e, t, _, he, _, _, _⟩ := M.fieldFibre k
  obtain ⟨A, V, d, s, _, hd, _, _, _⟩ := M.fieldFibre E
  obtain ⟨W, ⟨p⟩⟩ := Classification.Pinning.pinningsExist A Q
  let Qp : PinnedGroup A := ⟨Q, W, p⟩
  obtain ⟨w, _⟩ := pinnedLift V.pinned Qp V.attached D (Groupoid.inv (show D.toBased ⟶ V.attached.toBased from V.datumIso))
  have hw : (fibre E).map M.torus ≫ (d ≪≫ w.group).hom =
      (s ≪≫ w.torus).hom ≫ Qp.pair.T.inclusion := by
    change (fibre E).map M.torus ≫ (d.hom ≫ w.group.hom) =
      (s.hom ≫ w.torus.hom) ≫ Qp.pair.T.inclusion
    rw [← Category.assoc, hd, Category.assoc, w.torus_comm, Category.assoc]
  obtain ⟨j, v, hj⟩ := baseChangeTorusMarking M e t he (d ≪≫ w.group) (s ≪≫ w.torus) hw
  exact ⟨U.pinned.pair, j, v,
    semisimplicityOfForm (H := U.pinned.pair.G) (H₀ := G) j hG, hj⟩

private theorem extendSourceTorus {P : SplitBorelPair k} (D : AttachedDatum P)
    (hD : Specs.SimplyConnectedLattice.corootLattice D = ⊤) :
    ∃ (T : ClosedSubgroup ((groupBaseChange k E).obj P.G.val))
      (e : (groupBaseChange k E).obj P.T.group ≅ T.group),
      IsSplitTorus T.group ∧ IsGeometricallyMaximal T ∧
      e.hom ≫ T.inclusion = (groupBaseChange k E).map P.T.inclusion ∧
      GeometricallySimplyConnected (baseChangedAlgebraicGroup E P.G) := by
  let F := groupBaseChange k E
  obtain ⟨M⟩ := Classification.IntegralRealization.integralRealization D.toBased
  obtain ⟨A, U, d, s, _, hd, _, _, _⟩ := M.fieldFibre k
  obtain ⟨_, V, i, t, _, hi, _, _, _⟩ := M.fieldFibre E
  obtain ⟨W, ⟨p⟩⟩ := Classification.Pinning.pinningsExist A P
  let Pp : PinnedGroup A := ⟨P, W, p⟩
  obtain ⟨b, _⟩ := pinnedLift U.pinned Pp U.attached D (Groupoid.inv (show D.toBased ⟶ U.attached.toBased from U.datumIso))
  let d' := d ≪≫ b.group
  let s' := s ≪≫ b.torus
  have hd' : (fibre k).map M.torus ≫ d'.hom = s'.hom ≫ P.T.inclusion := by
    change (fibre k).map M.torus ≫ (d.hom ≫ b.group.hom) =
      (s.hom ≫ b.torus.hom) ≫ Pp.pair.T.inclusion
    rw [← Category.assoc, hd, Category.assoc, b.torus_comm, Category.assoc]
  obtain ⟨j, v, hj⟩ := baseChangeTorusMarking M d' s' hd' i t hi
  let T := transportSubgroup j.symm V.pinned.pair.T
  have hmark : v.hom ≫ T.inclusion = F.map P.T.inclusion := by
    change v.hom ≫ V.pinned.pair.T.inclusion ≫ j.inv = _
    rw [← Category.assoc, hj, Category.assoc, j.hom_inv_id, Category.comp_id]
  let e := (fibreTowerIso k E).app M.group ≪≫ F.mapIso d'
  exact ⟨T, v, V.pinned.pair.split, maximalTransport j.symm _ V.pinned.pair.maximal, hmark,
    model_simplyConnected M hD e⟩


open private baseChangeMapPullback from LinearAlgebraicGroups.Affine.Components

/-- The lift needed to apply affine Galois descent to the split cover. -/
def SplitCoverAutomorphismLifting : Prop :=
  ∀ {K : Type u} [Field K] (H G : AffineAlgebraicGroup K),
    IsSemisimple H → IsSemisimple G → GeometricallySimplyConnected H →
    ∀ (T : ClosedSubgroup H.val) (S : ClosedSubgroup G.val),
      IsSplitTorus T.group → IsGeometricallyMaximal T →
      IsSplitTorus S.group → IsGeometricallyMaximal S →
      ∀ (q : H.val ⟶ G.val) (qT : T.group ⟶ S.group),
        IsCentralIsogeny q → IsTorusRestriction q qT →
        ∀ b : Aut G.val, ∃! c : Aut H.val, c.asIso.hom ≫ q = q ≫ b.asIso.hom

set_option maxHeartbeats 650000 in
set_option backward.isDefEq.respectTransparency false in
theorem coverDescent_of_automorphismLifting (liftAut : SplitCoverAutomorphismLifting.{u}) :
    Specs.CentralCoverDescent.CoverDescent.{u} := by
  intro K E _ _ _ _ _ G hG
  dsimp only
  intro S hsS hmS
  let F := groupBaseChange K E
  obtain ⟨P, j, s, hP, hSj⟩ := referenceTarget G hG S hsS hmS
  let D := Classification.Pinning.attachedDatum P
  letI := D.comm
  obtain ⟨W, B, p, pT, hW, hWsc, hp, hpT, hCoroot, _⟩ :=
    Classification.SimplyConnectedLattice.splitCover P.G hP P.T P.split P.maximal D.datum
  obtain ⟨T, t, hsT, hmT, ht, hWscE⟩ := extendSourceTorus (E := E) B hCoroot
  let S₀ := transportSubgroup j.symm S
  have hSm₀ : IsGeometricallyMaximal S₀ := maximalTransport j.symm S hmS
  have heS : s.hom ≫ S₀.inclusion = F.map P.T.inclusion := by
    change s.hom ≫ S.inclusion ≫ j.inv = _
    rw [← Category.assoc, hSj, Category.assoc, j.hom_inv_id, Category.comp_id]
  have heT : T.inclusion = t.inv ≫ F.map W.T.inclusion := by
    rw [← ht, Iso.inv_hom_id_assoc]
  let r : T.group ⟶ S₀.group := t.inv ≫ F.map pT ≫ s.hom
  have hr : IsTorusRestriction (F.map p) r := by
    have cp : F.map pT ≫ F.map P.T.inclusion = F.map W.T.inclusion ≫ F.map p := by
      rw [← F.map_comp, hpT.1, F.map_comp]
    have pb := (baseChangeMapPullback (K := E) pT.hom.hom).flip
    letI : Flat (F.map pT).hom.hom.left := MorphismProperty.of_isPullback pb hpT.2.1
    letI : Surjective (F.map pT).hom.hom.left := MorphismProperty.of_isPullback pb hpT.2.2
    letI : IsIso t.inv.hom.hom.left := (forgetScheme E).map_isIso t.inv
    letI : IsIso s.hom.hom.hom.left := (forgetScheme E).map_isIso s.hom
    refine ⟨?_, inferInstanceAs (Flat (t.inv.hom.hom.left ≫
      (F.map pT).hom.hom.left ≫ s.hom.hom.hom.left)),
      inferInstanceAs (Surjective (t.inv.hom.hom.left ≫
        (F.map pT).hom.hom.left ≫ s.hom.hom.hom.left))⟩
    change (t.inv ≫ F.map pT ≫ s.hom) ≫ S₀.inclusion = T.inclusion ≫ F.map p
    rw [Category.assoc, Category.assoc, heS, cp, ← Category.assoc, ← heT]
  have hpE : IsCentralIsogeny (F.map p) := centralIsogeny_baseChange E W p hp
  have hsWE := (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := E) W.G hW.1 hW.2.1).mpr hW
  have hsPE := (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := E) P.G hP.1 hP.2.1).mpr hP
  obtain ⟨H, q, a, ha⟩ := descendSchemeFormOfMap p j
    (liftAut (baseChangedAlgebraicGroup E W.G) (baseChangedAlgebraicGroup E P.G)
      hsWE hsPE hWscE T S₀ hsT hmT hsS hSm₀ (F.map p) r hpE hr)
  have hq : F.map q = a.inv ≫ F.map p ≫ j.hom := by
    rw [← ha, Iso.inv_hom_id_assoc]
  let V := transportSubgroup a T
  refine ⟨H, q, semisimplicityOfForm (H := H) (H₀ := W.G) a.symm hW,
    geometricSimpleConnectednessOfForm (H := H) (H₀ := W.G) a.symm hWsc, ?_, ?_⟩
  · rw [hq, ← Category.assoc]
    exact centralIsogeny_postIso j (centralIsogeny_preIso a.symm hpE)
  · refine ⟨V, r, hsT, maximalTransport a T hmT, ?_, hr.2⟩
    have hleft : (r ≫ S₀.inclusion) ≫ j.hom = r ≫ S.inclusion := by
      change (r ≫ (S.inclusion ≫ j.inv)) ≫ j.hom = r ≫ S.inclusion
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hright : (T.inclusion ≫ a.hom) ≫ F.map q =
        (T.inclusion ≫ F.map p) ≫ j.hom := by
      simpa only [Category.assoc] using congrArg (fun v => T.inclusion ≫ v) ha
    exact hleft.symm.trans ((congrArg (fun v => v ≫ j.hom) hr.1).trans hright.symm)


open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Specs.AutomorphismSequence
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria

private theorem finiteSchemeDiscrete {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsFinite f] : DiscreteTopology X := by
  letI : IsAffine X := isAffine_of_isAffineHom f
  let R := Γ(X, ⊤)
  let e := Scheme.ΓSpecIso (CommRingCat.of k)
  let g : CommRingCat.of k ⟶ R := e.inv ≫ f.appTop
  have hfin : g.hom.Finite := (f.finite_appTop).comp
    (RingHom.Finite.of_surjective _ e.commRingCatIsoToRingEquiv.symm.surjective)
  letI : Algebra k R := g.hom.toAlgebra
  letI : Module.Finite k R := hfin
  letI : IsArtinianRing R := isArtinian_of_tower k inferInstance
  letI : IsLocallyArtinian (Spec R) := Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  exact X.isoSpec.hom.homeomorph.symm.discreteTopology

set_option backward.isDefEq.respectTransparency false in
private theorem finiteTargetRigidity {G N : GroupScheme k}
    [IsReduced G.X.left] [ConnectedSpace G.X.left] [IsFinite N.X.hom]
    (f : G.X ⟶ N.X) (hf : η[G.X] ≫ f = η[N.X]) : f = 1 := by
  letI : DiscreteTopology N.X.left := finiteSchemeDiscrete N.X.hom
  letI : IsAffine N.X.left := isAffine_of_isAffineHom N.X.hom
  let e : (𝟙_ (SchemeOver k)) ⟶ N.X := η[N.X]
  let eG : (𝟙_ (SchemeOver k)) ⟶ G.X := η[G.X]
  let t : (𝟙_ (SchemeOver k)).left := IsLocalRing.closedPoint k
  have hpoint (x : G.X.left) : f.left x = e.left t := by
    have h := (isPreconnected_univ.image f.left f.left.continuous.continuousOn).subsingleton
    exact (h ⟨x, Set.mem_univ _, rfl⟩ ⟨eG.left t, Set.mem_univ _, rfl⟩).trans
      (congrArg (fun z : (𝟙_ (SchemeOver k)) ⟶ N.X => z.left t) hf)
  apply Over.OverMorphism.ext
  change f.left = G.X.hom ≫ e.left
  apply (cancel_mono N.X.left.isoSpec.hom).mp
  simp only [Scheme.isoSpec, asIso_hom, Scheme.toSpecΓ_naturality]
  congr 1
  suffices h : f.left.appTop = (G.X.hom ≫ e.left).appTop by rw [h]
  apply CommRingCat.hom_ext
  ext a
  let a₀ := a - N.X.hom.appTop (e.left.appTop a)
  have hw : e.left ≫ N.X.hom = 𝟙 _ := e.w
  have hzero : e.left.appTop a₀ = 0 := by
    have h := congrArg (fun v => Scheme.Hom.appTop v (e.left.appTop a)) hw
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop, CommRingCat.comp_apply,
      CommRingCat.id_apply] at h
    change e.left.appTop (a - N.X.hom.appTop (e.left.appTop a)) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr h.symm
  have hbot : G.X.left.basicOpen (f.left.appTop a₀) = ⊥ := by
    rw [← Scheme.preimage_basicOpen_top]
    apply le_antisymm _ bot_le
    intro x hx
    change f.left x ∈ N.X.left.basicOpen a₀ at hx
    rw [hpoint] at hx
    have ht : t ∈ e.left ⁻¹ᵁ N.X.left.basicOpen a₀ := hx
    rw [Scheme.preimage_basicOpen_top, hzero, Scheme.basicOpen_zero] at ht
    exact ht.elim
  have hz := eq_zero_of_basicOpen_eq_bot _ hbot
  have hwf : f.left ≫ N.X.hom = G.X.hom := f.w
  have hc := congrArg (fun v => Scheme.Hom.appTop v (e.left.appTop a)) hwf
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at hc
  change f.left.appTop (a - N.X.hom.appTop (e.left.appTop a)) = 0 at hz
  rw [map_sub] at hz
  change f.left.appTop a = (G.X.hom ≫ e.left).appTop a
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  exact (sub_eq_zero.mp hz).trans hc

set_option backward.isDefEq.respectTransparency false in
private theorem lift_unique {H : AffineAlgebraicGroup k} (hH : IsSemisimple H)
    {G : GroupScheme k} {q : H.val ⟶ G} (hq : IsCentralIsogeny q)
    {a b : H.val ⟶ H.val} (hab : a ≫ q = b ≫ q) : a = b := by
  letI := hH.1
  letI := hH.2.1
  letI : IsReduced H.val.X.left := isReduced_of_smooth_over_field H.val.X.hom
  letI : ConnectedSpace H.val.X.left := GeometricallyConnected.connectedSpace_of_subsingleton H.val.X.hom
  obtain ⟨hfin, _, _, N, hN, _⟩ := hq
  have hpb := (Over.forget (Spec (CommRingCat.of k))).map_isPullback hN
  letI : IsFinite N.group.X.hom := MorphismProperty.of_isPullback hpb hfin
  have heq : a.hom.hom ≫ q.hom.hom = b.hom.hom ≫ q.hom.hom :=
    congrArg (fun c : H.val ⟶ G => c.hom.hom) hab
  have hdiff : (a.hom.hom⁻¹ * b.hom.hom) ≫ q.hom.hom = 1 := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, heq, inv_mul_cancel]
  obtain ⟨d, hd⟩ := (schemeKernel_sections hN _).mpr hdiff
  change d ≫ N.inclusion.hom.hom = a.hom.hom⁻¹ * b.hom.hom at hd
  letI := N.isClosedImmersion
  letI : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
  have hd1 : η[H.val.X] ≫ d = η[N.group.X] := by
    apply (cancel_mono N.inclusion.hom.hom).mp
    rw [Category.assoc, hd, MonObj.comp_mul, GrpObj.comp_inv]
    rw [IsMonHom.one_hom, IsMonHom.one_hom, IsMonHom.one_hom]
    exact inv_mul_cancel _
  have e := finiteTargetRigidity d hd1
  apply Grp.hom_ext
  have hz : a.hom.hom⁻¹ * b.hom.hom = 1 := by rw [← hd, e, MonObj.one_comp]
  exact inv_mul_eq_one.mp hz

set_option maxHeartbeats 550000 in
set_option backward.isDefEq.respectTransparency false in
theorem splitCoverAutomorphismLifting_of_parts
    (liftInner : Specs.CentralCoverInnerLift.InnerAutomorphismLifting.{u})
    (liftPinned : Specs.CentralCoverPinnedLift.PinnedAutomorphismLifting.{u}) :
    SplitCoverAutomorphismLifting.{u} := by
  intro k _ H G hH hG hsc T S hsT hmT hsS hmS q qT hq hqT b
  let R := splitBorelPair G (reductive_of_semisimple G hG) S hsS hmS
  let A := Classification.Pinning.standardAdditiveLine k
  obtain ⟨U, ⟨pin⟩⟩ := Classification.Pinning.pinningsExist A R
  let P : PinnedGroup A := ⟨R, U, pin⟩
  obtain ⟨D, l, Q, F, _, _⟩ := Descent.AutomorphismSequence.automorphismSequence P
  let I := 𝟙_ (SchemeOver k)
  let Y := yonedaGrp ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.forget I).op
  let p : Aut P.pair.G.val →* (automorphisms P.pair.G.val).obj (op I) := Y.mapAut P.pair.G.val
  let o := (F.toExactSequence.outer.app (op I)).hom.comp p
  let x := o b
  let t : I.left := IsLocalRing.closedPoint k
  let d : Aut D.toBased := x.down t
  haveI : PreconnectedSpace I.left := inferInstanceAs (PreconnectedSpace (PrimeSpectrum k))
  have hd : x = ⟨LocallyConstant.const _ d⟩ := ULift.ext (x.down.eq_const t)
  let aP := l d
  let a : Aut P.pair.G.val := forgetPinning.mapAut P aP
  have ha : o a = o b := by
    let D₀ : (constantGroup (Aut D.toBased)).obj (op I) := ⟨LocallyConstant.const _ d⟩
    have hr : F.toExactSequence.outer.app (op I) (F.sectionMap.app (op I) D₀) = D₀ :=
      ConcreteCategory.congr_hom (congrArg (fun v => v.app (op I)) F.rightInverse) D₀
    have he : F.sectionMap.app (op I) D₀ = scalarAut a I :=
      F.sectionOnConstants I d
    exact (congrArg (fun v => F.toExactSequence.outer.app (op I) v) he.symm).trans
      (hr.trans hd.symm)
  let b' : Aut P.pair.G.val := b
  let c := b' * a⁻¹
  have hc : o c = 1 := by
    change o (b' * a⁻¹) = 1
    rw [map_mul, map_inv, ha, mul_inv_cancel]
  obtain ⟨z, hz⟩ := (F.toExactSequence.exact (op I) (scalarAut c I)).mp hc
  obtain ⟨C, hC⟩ := liftInner H G hH hG T S hsT hmT hsS hmS q qT hq hqT
    Q F.toExactSequence.inner F.toExactSequence.onLift z c hz.symm
  obtain ⟨B, hB⟩ := liftPinned H P hH hG hsc T hsT hmT q qT hq hqT aP
  have hca : c * a = b' := inv_mul_cancel_right b' a
  have hBa : B.asIso.hom ≫ q = q ≫ a.asIso.hom := hB
  have hcomp : (C * B).asIso.hom ≫ q = q ≫ (c * a).asIso.hom := by
    change (B.asIso.hom ≫ C.asIso.hom) ≫ q = q ≫ a.asIso.hom ≫ c.asIso.hom
    rw [Category.assoc, hC, ← Category.assoc, hBa, Category.assoc]
  have hCB : (C * B).asIso.hom ≫ q = q ≫ b.asIso.hom :=
    hcomp.trans (congrArg (fun z : Aut P.pair.G.val => q ≫ z.asIso.hom) hca)
  refine ⟨C * B, hCB, fun j hj => ?_⟩
  apply Aut.ext
  apply Iso.ext
  exact lift_unique hH hq (hj.trans hCB.symm)

/-- The simply connected central cover descends through the prescribed finite
Galois extension with a split maximal torus over the marked target torus. -/
theorem coverDescent : Specs.CentralCoverDescent.CoverDescent.{u} :=
  coverDescent_of_automorphismLifting
    (splitCoverAutomorphismLifting_of_parts
      CentralCoverInnerLift.innerAutomorphismLifting
      CentralCoverPinnedLift.pinnedAutomorphismLifting)

end

end LinearAlgebraicGroups.Arithmetic.CentralCoverDescent
