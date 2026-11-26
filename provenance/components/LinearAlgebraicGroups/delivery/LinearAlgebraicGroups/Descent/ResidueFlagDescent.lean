import Specs.LinearAlgebraicGroups.Descent.ResidueFlagDescent
import LinearAlgebraicGroups.Descent.AffineGroups
import LinearAlgebraicGroups.Descent.FiniteFieldFlags
import LinearAlgebraicGroups.Descent.PinnedPairDescent
import LinearAlgebraicGroups.RootData.BorelNormalizer
import LinearAlgebraicGroups.Flag.HomogeneousQuotient
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace LinearAlgebraicGroups.Descent.ResidueFlagDescent

open _root_.LinearAlgebraicGroups.Specs
open Specs.ResidueFlagDescent
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open Specs.GeometricRadicals (IsReductive GeometricGroup)
open Specs.GeometricBorelConjugacy (IsKBorel IsBorel ConjugatesSubgroups)
open Specs.QuotientEmbedding (Presentation)

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option linter.style.haveILetI false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private abbrev schemeOfGroup (k : Type u) [Field k] : GroupScheme k ⥤ SchemeOver k :=
  Grp.forget _

private abbrev underlying (k : Type u) [Field k] : GroupScheme k ⥤ Scheme :=
  schemeOfGroup k ⋙ Over.forget _

open private smooth_of_iso connected_of_iso reductive_of_geometric_iso borel_of_square
  from LinearAlgebraicGroups.Descent.PinnedPairDescent
open private smooth_baseChange_iff connected_baseChange_iff transportSubgroup
  from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private geometricallyConnected_of_connected from LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private extendSubgroup conjugates_extend conjugates_descend conjugates_inverse
  conjugates_of_normalizes from LinearAlgebraicGroups.RootData.BorelNormalizer
open private conjugationIso comp_conjugation conjugates_iff_iso conjugation_mul
  twist twistGroups twistGroupBaseChangeIso twistBaseChangeIso twistedSections
  twist_conjugation lang_on_geometricSections inverseFrobenius inverseFrobenius_fixed
  geometricSectionsEquiv geometricSectionsEquiv_left
  from LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private coefficientMap_spec from LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private projection_eq_iff represent_of_fppf from LinearAlgebraicGroups.Flag.QuotientEmbedding
open private LinearAlgebraicGroups.extendedSpecIso from LinearAlgebraicGroups.Affine.ClosedSubgroups

private theorem reductive_descends {H₀ : AffineAlgebraicGroup k} {H : AffineAlgebraicGroup K}
    (e : (groupBaseChange k K).obj H₀.val ≅ H.val) (h : IsReductive H) : IsReductive H₀ := by
  have hs : Smooth H₀.val.X.hom :=
    (smooth_baseChange_iff (K := K) H₀.val.X).mp (smooth_of_iso e.symm h.1)
  haveI : GeometricallyConnected H.val.X.hom := h.2.1
  have hc : ConnectedSpace H.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton H.val.X.hom
  haveI : ConnectedSpace H₀.val.X.left :=
    (connected_baseChange_iff (K := K) H₀).mp (connected_of_iso e.symm hc)
  have hc₀ := geometricallyConnected_of_connected H₀
  exact (Reductive.RadicalBaseChange.reductiveFieldExtension H₀ hs hc₀).mp
    (reductive_of_geometric_iso (G := H) (H := baseChangedAlgebraicGroup K H₀)
      ((groupBaseChange K (AlgebraicClosure K)).mapIso e.symm) h)

private def descendedGroup {H : AffineAlgebraicGroup K}
    {D : HopfDescentDatum k (AdjointCocharacters.coordinateHopf H)} (J : HopfDescent D) :
    AffineAlgebraicGroup k := by
  let e := AdjointCocharacters.coordinateHopfIso H
  have hft : LocallyOfFiniteType (specGroup (AdjointCocharacters.coordinateHopf H)).X.hom := by
    let f := (underlying K).map e.hom
    letI : IsIso f := (underlying K).map_isIso e.hom
    rw [← Over.w e.hom.hom.hom]
    haveI : LocallyOfFiniteType H.val.X.hom := H.property.2.1
    exact inferInstanceAs (LocallyOfFiniteType (f ≫ H.val.X.hom))
  exact ⟨specGroup J.algebra, by
    change IsAffine (Spec (CommRingCat.of J.algebra))
    infer_instance, (affineGroupDescentProperties J).1 hft⟩

private theorem group_operator_comparison {H : AffineAlgebraicGroup K}
    {D : HopfDescentDatum k (AdjointCocharacters.coordinateHopf H)} (J : HopfDescent D)
    (hJ : (SemilinearAction.scalarExtension (K := K) D.fixed).Equivariant D.action
        J.iso.hom.hom.toLinearMap) (σ : Gal(K/k)) :
    let e := (groupDescentComparison J).symm ≪≫ AdjointCocharacters.coordinateHopfIso H
    e.hom.hom.hom.left ≫ schemeOperator H D σ =
      coefficientMap σ (specGroup J.algebra).X ≫ e.hom.hom.hom.left := by
  let A := AdjointCocharacters.coordinateHopf H
  let i := (AdjointCocharacters.coordinateHopfIso H)
  let d := (groupDescentComparison J).hom.hom.hom.left
  let j := (LinearAlgebraicGroups.extendedSpecIso K J.algebra).hom.left
  let f := CommRingCat.ofHom J.iso.hom.hom.toAlgHom.toRingHom
  have hd : d = Spec.map f ≫ j := rfl
  let m := CommRingCat.ofHom (coordinateOperator D σ)
  let t := CommRingCat.ofHom
    (Algebra.TensorProduct.map (σ⁻¹ : Gal(K/k)).toAlgHom (AlgHom.id k J.algebra)).toRingHom
  have hn : t ≫ f = f ≫ m := by
    apply CommRingCat.hom_ext
    apply DFunLike.ext
    intro x
    exact hJ σ⁻¹ x
  have ht : j ≫ coefficientMap σ (specGroup J.algebra).X = Spec.map t ≫ j := by
    exact coefficientMap_spec σ⁻¹ J.algebra
  have hw : Spec.map m ≫ d = d ≫ coefficientMap σ (specGroup J.algebra).X := by
    rw [hd, Category.assoc, ht, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
      ← Spec.map_comp, hn]
  let e := (groupDescentComparison J).symm ≪≫ i
  let E := (underlying K).mapIso e
  let I := (underlying K).mapIso i
  change E.hom ≫ I.inv ≫ Spec.map m ≫ I.hom = _
  apply (cancel_epi E.inv).mp
  simp only [Iso.inv_hom_id_assoc]
  have hE : E.inv = I.inv ≫ d := rfl
  change I.inv ≫ Spec.map m ≫ I.hom = E.inv ≫ coefficientMap σ (specGroup J.algebra).X ≫ E.hom
  rw [hE]
  simp only [Category.assoc]
  have hh : d ≫ E.hom = I.hom := by
    change (underlying K).map (groupDescentComparison J).hom ≫ (underlying K).map e.hom = _
    rw [← Functor.map_comp]
    simp [e]
    rfl
  calc
    I.inv ≫ Spec.map m ≫ I.hom = I.inv ≫ (Spec.map m ≫ d) ≫ E.hom := by
      simp only [Category.assoc, hh]
    _ = I.inv ≫ (d ≫ coefficientMap σ (specGroup J.algebra).X) ≫ E.hom :=
      congrArg (fun f ↦ I.inv ≫ f ≫ E.hom) hw
    _ = _ := by simp only [Category.assoc]

private theorem coefficientPoint_natural (σ : Gal(K/k)) {X Y : SchemeOver k}
    (f : X ⟶ Y) (p : RationalPoint ((baseChange k K).obj X)) :
    coefficientPoint σ Y (p ≫ (baseChange k K).map f) =
      coefficientPoint σ X p ≫ (baseChange k K).map f := by
  apply Over.OverMorphism.ext
  change scalarMap σ ≫ (p.left ≫ ((baseChange k K).map f).left) ≫ coefficientMap σ Y =
    (scalarMap σ ≫ p.left ≫ coefficientMap σ X) ≫ ((baseChange k K).map f).left
  have h := congrArg Over.Hom.left
    ((twistBaseChangeIso (k := k) (K := K) σ⁻¹).hom.naturality f)
  change ((baseChange k K).map f).left ≫ coefficientMap σ Y =
    coefficientMap σ X ≫ ((baseChange k K).map f).left at h
  simpa only [Category.assoc] using congrArg (fun g ↦ scalarMap σ ≫ p.left ≫ g) h

section Borels

open Specs.SchemeDerivedGroup (IsSubgroupOf)
open private groupObjectsFunctor_isEquivalence closedImmersion_of_extend_iso
  extendRationalEquiv smoothConnectedSolvable_of_iso smooth_extend_iff connected_extend_iso_iff reductive_geometric
  isKBorel_iff_of_isAlgClosed from LinearAlgebraicGroups.RootData.BorelNormalizer
open private solvable_iff_sections from LinearAlgebraicGroups.Reductive.GeometricRadicals
open private groupBaseChangeTower from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private conjugates_trans normalizes_of_conjugates_self conjugates_preserves_borel
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate

private theorem solvable_after_isomorphic_extension [IsAlgClosed k] [IsAlgClosed K]
    [IsIso (fieldSpecMap k K)] (A : AffineAlgebraicGroup k)
    (hs : Smooth A.val.X.hom) (hc : ConnectedSpace A.val.X.left) :
    Specs.SchemeDerivedGroup.IsSolvable (baseChangedAlgebraicGroup K A).val ↔
      Specs.SchemeDerivedGroup.IsSolvable A.val := by
  rw [solvable_iff_sections A hs hc, solvable_iff_sections (baseChangedAlgebraicGroup K A)
    ((smooth_extend_iff K _).mpr hs) ((connected_extend_iso_iff K _).mpr hc)]
  let e := extendRationalEquiv K A.val
  constructor
  · intro h
    letI : Group.IsSolvable (RationalPoint ((groupBaseChange k K).obj A.val).X) := h
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  · intro h
    letI : Group.IsSolvable (RationalPoint A.val.X) := h
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

private theorem borel_after_isomorphic_extension [IsAlgClosed k] [IsAlgClosed K]
    [IsIso (fieldSpecMap k K)] (A : AffineAlgebraicGroup k) (B : ClosedSubgroup A.val)
    (hB : IsBorel B) : IsBorel (extendSubgroup K B) := by
  let F := groupBaseChange k K
  letI : (baseChange k K).IsEquivalence :=
    (Over.mapPullbackAdj (fieldSpecMap k K)).isEquivalence_right_of_isEquivalence_left
  letI : F.IsEquivalence := groupObjectsFunctor_isEquivalence (baseChange k K)
  have extend (D : ClosedSubgroup A.val) :
      GeometricBorelConjugacy.IsSmoothConnectedSolvable (extendSubgroup K D) ↔
        GeometricBorelConjugacy.IsSmoothConnectedSolvable D := by
    constructor
    · rintro ⟨hs, hc, hv⟩
      have hs' := (smooth_extend_iff K D.group.X).mp hs
      have hc' := (connected_extend_iso_iff K D.group.X).mp hc
      exact ⟨hs', hc', (solvable_after_isomorphic_extension (closedSubgroupAlgebraicGroup D)
        hs' hc').mp hv⟩
    · rintro ⟨hs, hc, hv⟩
      exact ⟨(smooth_extend_iff K D.group.X).mpr hs, (connected_extend_iso_iff K D.group.X).mpr hc,
        (solvable_after_isomorphic_extension (closedSubgroupAlgebraicGroup D) hs hc).mpr hv⟩
  refine ⟨(extend B).mpr hB.1, ?_⟩
  rintro N hN ⟨a, ha⟩
  let I := F.asEquivalence.inverse.obj N.group
  let e : F.obj I ≅ N.group := F.asEquivalence.counitIso.app N.group
  let i : I ⟶ A.val := F.preimage (e.hom ≫ N.inclusion)
  have hi : F.map i = e.hom ≫ N.inclusion := F.map_preimage _
  have hc : IsClosedImmersion i.hom.hom.left := by
    apply closedImmersion_of_extend_iso K
    change IsClosedImmersion ((underlying K).map (F.map i))
    rw [hi, Functor.map_comp]
    haveI : IsClosedImmersion ((underlying K).map N.inclusion) := N.isClosedImmersion
    haveI := (underlying K).map_isIso e.hom
    exact IsClosedImmersion.comp _ _
  let D : ClosedSubgroup A.val := ⟨I, i, hc⟩
  have hD' : GeometricBorelConjugacy.IsSmoothConnectedSolvable (extendSubgroup K D) :=
    smoothConnectedSolvable_of_iso
      (closedSubgroupAlgebraicGroup (G := baseChangedAlgebraicGroup K A) N)
      (closedSubgroupAlgebraicGroup (G := baseChangedAlgebraicGroup K A) (extendSubgroup K D)) e.symm hN
  let j : B.group ⟶ D.group := F.preimage (a ≫ e.inv)
  have hj : F.map j = a ≫ e.inv := F.map_preimage _
  have hji : j ≫ D.inclusion = B.inclusion := by
    apply F.map_injective
    change F.map (j ≫ i) = F.map B.inclusion
    rw [F.map_comp, hj, hi, Category.assoc, Iso.inv_hom_id_assoc]
    exact ha
  obtain ⟨b, hb⟩ := hB.2 D ((extend D).mp hD') ⟨j, hji⟩
  refine ⟨e.inv ≫ F.map b, ?_⟩
  change (e.inv ≫ F.map b) ≫ F.map B.inclusion = N.inclusion
  rw [Category.assoc, ← F.map_comp, hb]
  change e.inv ≫ F.map i = _
  rw [hi, Iso.inv_hom_id_assoc]

private theorem borel_after_field_extension [FiniteDimensional k K]
    {H₀ : AffineAlgebraicGroup k} {H : AffineAlgebraicGroup K}
    (e : (groupBaseChange k K).obj H₀.val ≅ H.val) (B₀ : ClosedSubgroup H₀.val)
    (hB₀ : IsKBorel B₀) :
    IsKBorel (transportSubgroup e (extendSubgroup K B₀)) := by
  let F := AlgebraicClosure k
  let L := AlgebraicClosure K
  let f : F →ₐ[k] L := IsAlgClosed.lift
  letI : Algebra F L := f.toRingHom.toAlgebra
  letI : IsScalarTower k F L := IsScalarTower.of_algebraMap_eq fun a ↦ (f.commutes a).symm
  letI : Algebra.IsAlgebraic k L := Algebra.IsAlgebraic.trans k K L
  letI : Algebra.IsAlgebraic F L := Algebra.IsAlgebraic.tower_top (K := k) F
  letI : IsIso (fieldSpecMap F L) := by
    let g := CommRingCat.ofHom (algebraMap F L)
    haveI : IsIso g := (ConcreteCategory.isIso_iff_bijective g).mpr
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    exact inferInstanceAs (IsIso (Spec.map g))
  let P := groupBaseChange k F ⋙ groupBaseChange F L
  let P' := groupBaseChange k K ⋙ groupBaseChange K L
  let t : P ≅ P' := (groupBaseChangeTower (k := k) (K := F) L).symm ≪≫
    (groupBaseChangeTower (k := k) (K := K) L)
  let C := transportSubgroup e (extendSubgroup K B₀)
  let X := baseChangedAlgebraicGroup L (GeometricGroup H₀)
  let Y := GeometricGroup H
  let E : X.val ≅ Y.val := (t.app H₀.val) ≪≫ (groupBaseChange K L).mapIso e
  let D : ClosedSubgroup (GeometricGroup H₀).val := extendSubgroup F B₀
  let DL : ClosedSubgroup X.val := extendSubgroup L D
  let CL : ClosedSubgroup Y.val := extendSubgroup L C
  obtain ⟨_, hD : IsBorel D⟩ := hB₀
  have hDL : IsBorel DL :=
    borel_after_isomorphic_extension (k := F) (K := L) (GeometricGroup H₀) D hD
  let d : DL.group ≅ CL.group := t.app B₀.group
  have hd : d.hom ≫ CL.inclusion = DL.inclusion ≫ E.hom := by
    let f := (groupBaseChange K L).map e.hom
    have ht : P.map B₀.inclusion ≫ t.hom.app H₀.val =
        t.hom.app B₀.group ≫ P'.map B₀.inclusion := t.hom.naturality _
    change t.hom.app B₀.group ≫ (groupBaseChange K L).map
      ((groupBaseChange k K).map B₀.inclusion ≫ e.hom) =
        P.map B₀.inclusion ≫ t.hom.app H₀.val ≫ f
    have hf : (groupBaseChange K L).map
        ((groupBaseChange k K).map B₀.inclusion ≫ e.hom) = P'.map B₀.inclusion ≫ f :=
      (groupBaseChange K L).map_comp _ _
    calc
      t.hom.app B₀.group ≫ (groupBaseChange K L).map
          ((groupBaseChange k K).map B₀.inclusion ≫ e.hom) =
          t.hom.app B₀.group ≫ P'.map B₀.inclusion ≫ f :=
        congrArg (t.hom.app B₀.group ≫ ·) hf
      _ = P.map B₀.inclusion ≫ t.hom.app H₀.val ≫ f :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ f) ht.symm).trans (Category.assoc _ _ _))
  have hCL : IsBorel CL := borel_of_square (k := L) (X := X) (Y := Y) E DL CL d hd hDL
  exact ⟨CL.isClosedImmersion, hCL⟩

private theorem twisted_conjugates {G : GroupScheme k} {B C : ClosedSubgroup G}
    (σ : Gal(K/k)) {g : RationalPoint ((groupBaseChange k K).obj G).X}
    (hg : ConjugatesSubgroups g (extendSubgroup K B) (extendSubgroup K C)) :
    ConjugatesSubgroups (twistedSections σ G g) (extendSubgroup K B) (extendSubgroup K C) := by
  let F := twistGroups σ
  let n := (twistGroupBaseChangeIso σ).hom
  let B' := extendSubgroup K B
  let C' := extendSubgroup K C
  obtain ⟨d, hd⟩ := (conjugates_iff_iso g B' C').mp hg
  apply (conjugates_iff_iso _ B' C').mpr
  refine ⟨((twistGroupBaseChangeIso σ).app B.group).symm ≪≫ F.mapIso d ≪≫
    (twistGroupBaseChangeIso σ).app C.group, ?_⟩
  change ((twistGroupBaseChangeIso σ).app B.group).inv ≫
      (F.map d.hom ≫ n.app C.group) ≫ C'.inclusion =
    B'.inclusion ≫ (conjugationIso (twistedSections σ G g)).hom
  have hB : F.map B'.inclusion ≫ n.app G = n.app B.group ≫ B'.inclusion :=
    n.naturality B.inclusion
  have hC : F.map C'.inclusion ≫ n.app G = n.app C.group ≫ C'.inclusion :=
    n.naturality C.inclusion
  simp only [Category.assoc, ← hC]
  have ht : F.map (conjugationIso g).hom ≫ n.app G =
      n.app G ≫ (conjugationIso (twistedSections σ G g)).hom := twist_conjugation σ G g
  rw [← Category.assoc (F.map d.hom), ← F.map_comp, hd, F.map_comp,
    Category.assoc (F.map B'.inclusion), ht, ← Category.assoc (F.map B'.inclusion),
    hB]
  change ((twistGroupBaseChangeIso σ).app B.group).inv ≫
      ((twistGroupBaseChangeIso σ).app B.group).hom ≫
        B'.inclusion ≫ (conjugationIso (twistedSections σ G g)).hom = _
  rw [Iso.inv_hom_id_assoc]

private theorem extendedPoint_left {L : Type u} [Field L] [Algebra k L] {X : SchemeOver k}
    (p : RationalPoint X) :
    (scalarExtendedRationalPoint L p).left ≫ pullback.fst X.hom (fieldSpecMap k L) =
      fieldSpecMap k L ≫ p.left := by
  let a := Functor.LaxMonoidal.ε (baseChange k L)
  let b := pullback.fst (𝟙_ (SchemeOver k)).hom (fieldSpecMap k L)
  have ha : a.left ≫ b = fieldSpecMap k L := by
    have h := pullback.condition (f := (𝟙_ (SchemeOver k)).hom) (g := fieldSpecMap k L)
    change b ≫ 𝟙 _ = ((baseChange k L).obj (𝟙_ (SchemeOver k))).hom ≫ fieldSpecMap k L at h
    rw [Category.comp_id] at h
    rw [h, ← Category.assoc, Over.w a]
    exact Category.id_comp _
  have hh : ((baseChange k L).map p).left ≫ pullback.fst X.hom (fieldSpecMap k L) =
      b ≫ p.left := by
    change pullback.lift _ _ _ ≫ _ = _
    exact pullback.lift_fst _ _ _
  change (a.left ≫ ((baseChange k L).map p).left) ≫
    pullback.fst X.hom (fieldSpecMap k L) = _
  rw [Category.assoc, hh, ← Category.assoc, ha]

open private testUnitIso frobenius_on_geometricSections
  from LinearAlgebraicGroups.Descent.FiniteFieldFlags

private theorem geometricSectionsEquiv_extendedPoint {L : Type u} [Field L] [Algebra k L]
    (G : GroupScheme k) (p : Points G.X (CommAlgCat.of k k)) :
    geometricSectionsEquiv L G (scalarExtendedRationalPoint L ((testUnitIso k).inv ≫ p)) =
      extendRationalPoint (K := L) p := by
  let c : RationalPoint G.X := (testUnitIso k).inv ≫ p
  apply Over.OverMorphism.ext
  change (geometricSectionsEquiv L G (scalarExtendedRationalPoint L c)).left = _
  refine (geometricSectionsEquiv_left (K := L) G (scalarExtendedRationalPoint L c)).trans ?_
  refine (extendedPoint_left (L := L) c).trans ?_
  change fieldSpecMap k L ≫ (𝟙 _ ≫ p.left) = fieldSpecMap k L ≫ p.left
  rw [Category.id_comp]

private theorem section_descends [Fintype k] (G : GroupScheme k)
    (g : RationalPoint ((groupBaseChange k (AlgebraicClosure k)).obj G).X)
    (hg : twistedSections inverseFrobenius G g = g) :
    ∃ c : RationalPoint G.X, scalarExtendedRationalPoint (AlgebraicClosure k) c = g := by
  let L := AlgebraicClosure k
  let e := geometricSectionsEquiv L G
  let z := e g
  have hz : frobeniusOnPoints _ z = z :=
    (frobenius_on_geometricSections G g).symm.trans (congrArg e hg)
  obtain ⟨p, hp⟩ := (frobeniusFixedPoints k L G.X z).mp hz
  let c : RationalPoint G.X := (testUnitIso k).inv ≫ p
  have hn : e (scalarExtendedRationalPoint L c) = extendRationalPoint (K := L) p :=
    geometricSectionsEquiv_extendedPoint (L := L) G p
  exact ⟨c, e.injective (hn.trans hp)⟩

private theorem twistedSections_natural (σ : Gal(K/k)) {G H : GroupScheme k}
    (i : G ⟶ H) (t : RationalPoint ((groupBaseChange k K).obj G).X) :
    (twistedSections σ H) (t ≫ ((groupBaseChange k K).map i).hom.hom) =
      (twistedSections σ G t) ≫ ((groupBaseChange k K).map i).hom.hom := by
  let n := (twistGroupBaseChangeIso σ).hom
  let T := twist σ
  let d := ((groupBaseChange k K).map i).hom.hom
  let a := (n.app G).hom.hom
  let b := (n.app H).hom.hom
  let e := (Functor.Monoidal.εIso T).hom
  have h : T.map d ≫ b = a ≫ d := by
    have hi := congrArg (schemeOfGroup K).map (n.naturality i)
    rw [Functor.map_comp, Functor.map_comp] at hi
    exact hi
  change e ≫ T.map (t ≫ d) ≫ b = (e ≫ T.map t ≫ a) ≫ d
  rw [T.map_comp]
  simp only [Category.assoc, h]

private theorem lang_correction {A T : Type*} [Group A] [Group T]
    (F : A ≃* A) (m : T →* A) (g : A) (b t t' : T)
    (hb : m b = g⁻¹ * F g) (ht : t' * t⁻¹ = b⁻¹) (hFt : F (m t) = m t') :
    F (g * m t) = g * m t := by
  have hh := congrArg m ht
  rw [map_mul, map_inv, map_inv, ← hFt, hb, mul_inv_rev, inv_inv] at hh
  have hmt := (mul_inv_eq_iff_eq_mul).mp hh
  rw [map_mul, hmt]
  group

private theorem rational_borel_conjugacy [Fintype k] (H : AffineAlgebraicGroup k)
    (hH : IsReductive H) (B C : ClosedSubgroup H.val) (hB : IsKBorel B) (hC : IsKBorel C) :
    ∃ c : RationalPoint H.val.X, ConjugatesSubgroups c B C := by
  let L := AlgebraicClosure k
  let H' := GeometricGroup H
  let B' := extendSubgroup L B
  let C' := extendSubgroup L C
  obtain ⟨_, hB' : IsBorel B'⟩ := hB
  obtain ⟨_, hC' : IsBorel C'⟩ := hC
  have hH' : IsReductive H' := reductive_geometric H hH
  letI : GeometricallyConnected H'.val.X.hom := hH'.2.1
  obtain ⟨g, hg⟩ := GeometricBorelConjugacy.borelsConjugate H' hH'.1
    (GeometricallyConnected.connectedSpace_of_subsingleton H'.val.X.hom) B' C' hB' hC'
  change RationalPoint H'.val.X at g
  let σ := inverseFrobenius (k := k)
  let F : RationalPoint H'.val.X ≃* RationalPoint H'.val.X := twistedSections σ H.val
  have hFg : ConjugatesSubgroups (F g) B' C' := twisted_conjugates σ hg
  have hn := normalizes_of_conjugates_self B' (conjugates_trans hFg (conjugates_inverse hg))
  obtain ⟨b, hb⟩ := (RootData.BorelNormalizer.groundFieldBorelNormalizer H' hH' B'
    ((isKBorel_iff_of_isAlgClosed H' B').mpr hB') _ _).mp hn
  let A := closedSubgroupAlgebraicGroup (G := H) B
  have hs : Smooth A.val.X.hom := (smooth_baseChange_iff (K := L) A.val.X).mp hB'.1.1
  have hc : ConnectedSpace A.val.X.left := (connected_baseChange_iff (K := L) A).mp hB'.1.2.1
  obtain ⟨t, ht⟩ := lang_on_geometricSections A hs hc b⁻¹
  change RationalPoint B'.group.X at t
  let t' : RationalPoint B'.group.X := twistedSections σ B.group t
  have hlang : t' * t⁻¹ = b⁻¹ := ht
  let m : (RationalPoint B'.group.X) →* RationalPoint H'.val.X :=
    ((yonedaGrp.map B'.inclusion).app (op (𝟙_ (SchemeOver L)))).hom
  have hFt : F (m t) = m t' := twistedSections_natural σ B.inclusion t
  have hb' : m b = g⁻¹ * F g := hb
  have hgt : F (g * m t) = g * m t := lang_correction F m g b t t' hb' hlang hFt
  obtain ⟨c, hc⟩ := section_descends H.val (g * m t) hgt
  refine ⟨c, conjugates_descend L (g := c) ?_⟩
  rw [hc]
  exact conjugates_trans (conjugates_preserves_borel B' t) hg

end Borels

section QuotientComparison

open private baseChangeMapIsPullback baseChangeQuotientPullback projection_eq_iff_of_pullback
  from LinearAlgebraicGroups.Flag.HomogeneousQuotient

private abbrev translation {G : GroupScheme K} (c : RationalPoint G.X) : G.X ⟶ G.X :=
  rightTranslate (𝟙 G.X) c

private theorem constant_natural {G : GroupScheme K} {S T : SchemeOver K}
    (g : S ⟶ T) (c : RationalPoint G.X) : g ≫ toUnit T ≫ c = toUnit S ≫ c := by
  rw [← Category.assoc, (isTerminalTensorUnit (C := SchemeOver K)).hom_ext
    (g ≫ toUnit T) (toUnit S)]

private theorem comp_translation {G : GroupScheme K} {S : SchemeOver K}
    (g : S ⟶ G.X) (c : RationalPoint G.X) : g ≫ translation c = rightTranslate g c := by
  simp only [translation, rightTranslate, MonObj.comp_mul, Category.comp_id, constant_natural]

private def translationIso {G : GroupScheme K} (c : RationalPoint G.X) : G.X ≅ G.X where
  hom := translation c
  inv := translation c⁻¹
  hom_inv_id := by
    rw [comp_translation]
    simp only [rightTranslate, GrpObj.comp_inv, mul_inv_cancel, mul_assoc, mul_one]
  inv_hom_id := by
    rw [comp_translation]
    simp only [rightTranslate, GrpObj.comp_inv, inv_mul_cancel, mul_assoc, mul_one]

private theorem projection_comparison {H₀ : AffineAlgebraicGroup k} {H : AffineAlgebraicGroup K}
    {B₀ : ClosedSubgroup H₀.val} {B : ClosedSubgroup H.val}
    (Q₀ : Presentation B₀) (Q : Presentation B)
    (e : (groupBaseChange k K).obj H₀.val ≅ H.val) (c : RationalPoint H.val.X)
    (hc : ConjugatesSubgroups c B (transportSubgroup e (extendSubgroup K B₀))) :
    ∃ j : (baseChange k K).obj Q₀.scheme ≅ Q.scheme,
      ∀ (S : SchemeOver K) (g : S ⟶ ((groupBaseChange k K).obj H₀.val).X),
        g ≫ (baseChange k K).map Q₀.projection ≫ j.hom =
          rightTranslate (g ≫ e.hom.hom.hom) c ≫ Q.projection := by
  let F := baseChange k K
  let C := extendSubgroup K B₀
  let E := (schemeOfGroup K).mapIso e
  let a := E ≪≫ translationIso c
  let p := F.map Q₀.projection
  let q := a.inv ≫ p
  have hp := baseChangeMapIsPullback K Q₀.projection
  letI : Flat p.left := MorphismProperty.of_isPullback hp.flip Q₀.flat
  letI : Surjective p.left := MorphismProperty.of_isPullback hp.flip Q₀.surjective
  letI : LocallyOfFinitePresentation p.left := MorphismProperty.of_isPullback hp.flip Q₀.finitePresentation
  letI : IsIso a.inv.left := (Over.forget _).map_isIso a.inv
  letI : Flat q.left := by dsimp only [q, Over.comp_left]; infer_instance
  letI : Surjective q.left := by dsimp only [q, Over.comp_left]; infer_instance
  letI : LocallyOfFinitePresentation q.left := by dsimp only [q, Over.comp_left]; infer_instance
  obtain ⟨d, hd⟩ := (conjugates_iff_iso c B _).mp hc
  have hconj (S : SchemeOver K) (b : S ⟶ B.group.X) :
      (b ≫ d.hom.hom.hom ≫ C.inclusion.hom.hom) ≫ E.hom =
        (toUnit S ≫ c) * (b ≫ B.inclusion.hom.hom) * (toUnit S ≫ c)⁻¹ := by
    have h := congrArg ((schemeOfGroup K).map) hd
    change (schemeOfGroup K).map (d.hom ≫ C.inclusion ≫ e.hom) =
      (schemeOfGroup K).map (B.inclusion ≫ (conjugationIso c).hom) at h
    simp only [Functor.map_comp] at h
    change d.hom.hom.hom ≫ C.inclusion.hom.hom ≫ E.hom =
      B.inclusion.hom.hom ≫ (conjugationIso c).hom.hom.hom at h
    simp only [Category.assoc, h]
    exact (Category.assoc b B.inclusion.hom.hom (conjugationIso c).hom.hom.hom).symm.trans
      (comp_conjugation c (b ≫ B.inclusion.hom.hom))
  have hq : ∀ (S : SchemeOver K) (g h : S ⟶ H.val.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ SubgroupSections B S := by
    intro S g h
    change (g ≫ a.inv) ≫ p = (h ≫ a.inv) ≫ p ↔ _
    let aInv : H.val.X ⟶ ((groupBaseChange k K).obj H₀.val).X := a.inv
    change ((g ≫ aInv) ≫ p = (h ≫ aInv) ≫ p) ↔ _
    have hbc : ((g ≫ aInv) ≫ p = (h ≫ aInv) ≫ p) ↔
        ∃ r : S ⟶ C.group.X, r ≫ C.inclusion.hom.hom = (g ≫ aInv)⁻¹ * (h ≫ aInv) :=
      projection_eq_iff_of_pullback p
        (baseChangeQuotientPullback K Q₀ C.isClosedImmersion) S (g ≫ aInv) (h ≫ aInv)
    rw [hbc]
    let v := toUnit S ≫ c
    let m : (S ⟶ ((groupBaseChange k K).obj H₀.val).X) ≃* (S ⟶ H.val.X) :=
      ((yonedaGrp.mapIso e).app (op S)).groupIsoToMulEquiv
    have ha (x : S ⟶ H.val.X) : m (x ≫ aInv) = x * v⁻¹ := by
      change (x ≫ (translationIso c).inv ≫ E.inv) ≫ E.hom = _
      rw [Category.assoc, Category.assoc, E.inv_hom_id]
      change x ≫ translation c⁻¹ ≫ 𝟙 H.val.X = _
      rw [Category.comp_id, comp_translation]
      simp only [rightTranslate, GrpObj.comp_inv, v]
    have hdiff : m ((g ≫ aInv)⁻¹ * (h ≫ aInv)) = v * (g⁻¹ * h) * v⁻¹ := by
      rw [map_mul, map_inv, ha, ha]
      group
    constructor
    · rintro ⟨r, hr⟩
      change r ≫ C.inclusion.hom.hom = _ at hr
      let b := r ≫ d.inv.hom.hom
      refine ⟨b, ?_⟩
      have hs := hconj S b
      have hb : b ≫ d.hom.hom.hom = r := by
        change (r ≫ ((schemeOfGroup K).mapIso d).inv) ≫
          ((schemeOfGroup K).mapIso d).hom = r
        let i := (schemeOfGroup K).mapIso d
        calc
          (r ≫ i.inv) ≫ i.hom = r ≫ (i.inv ≫ i.hom) := Category.assoc _ _ _
          _ = r := (congrArg (r ≫ ·) i.inv_hom_id).trans (Category.comp_id r)
      rw [← Category.assoc b, hb, hr] at hs
      change m _ = v * (b ≫ B.inclusion.hom.hom) * v⁻¹ at hs
      rw [hdiff] at hs
      exact mul_left_cancel (mul_right_cancel hs.symm)
    · rintro ⟨b, hb⟩
      refine ⟨b ≫ d.hom.hom.hom, m.injective ?_⟩
      rw [hdiff]
      change ((b ≫ d.hom.hom.hom) ≫ C.inclusion.hom.hom) ≫ E.hom = _
      rw [Category.assoc b, hconj S b]
      exact congrArg (fun z ↦ v * z * v⁻¹) hb
  obtain ⟨j', hj'⟩ := represent_of_fppf B q hq
  let j := (fppfOver K).fullyFaithfulUliftYoneda.preimageIso (Q.quotientIso.symm ≪≫ j')
  have hj : Q.projection ≫ j.hom = q := by
    apply (fppfOver K).uliftYoneda.map_injective
    rw [Functor.map_comp, Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage,
      ← Q.quotientProjection]
    simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] using hj'
  refine ⟨j.symm, fun S g ↦ ?_⟩
  apply (cancel_mono j.hom).mp
  simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, hj]
  rw [← comp_translation]
  change g ≫ p = ((g ≫ E.hom) ≫ (translationIso c).hom) ≫ q
  rw [Category.assoc g E.hom, ← Iso.trans_hom]
  change g ≫ p = (g ≫ a.hom) ≫ a.inv ≫ p
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end QuotientComparison

section FlagAction

open private isMonHom_of_factor from LinearAlgebraicGroups.Solvable.FiniteWordClosure
open private conjugates_trans normalizes_of_conjugates_self
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private conjugation from LinearAlgebraicGroups.Descent.FiniteFieldFlags

private theorem coefficientPoint_eq_twisted (σ : Gal(K/k)) (G : GroupScheme k)
    (g : RationalPoint ((groupBaseChange k K).obj G).X) :
    coefficientPoint σ G.X g = twistedSections σ⁻¹ G g := by
  let e := (Functor.Monoidal.εIso (twist σ⁻¹)).hom
  have he : e.left = scalarMap σ := by
    have hw := Over.w e
    change e.left ≫ (𝟙 _ ≫ scalarMap σ⁻¹) = 𝟙 _ at hw
    rw [Category.id_comp] at hw
    haveI : IsIso (scalarMap σ⁻¹) := by
      change IsIso (Spec.map (CommRingCat.ofHom (σ⁻¹ : Gal(K/k)).toRingHom))
      haveI : IsIso (CommRingCat.ofHom (σ⁻¹ : Gal(K/k)).toRingHom) :=
        (ConcreteCategory.isIso_iff_bijective _).mpr (σ⁻¹ : Gal(K/k)).bijective
      infer_instance
    exact (cancel_mono (scalarMap σ⁻¹)).mp (hw.trans (scalarMap_comp_inverse σ).symm)
  apply Over.OverMorphism.ext
  change scalarMap σ ≫ g.left ≫ coefficientMap σ G.X =
    e.left ≫ g.left ≫ coefficientMap σ G.X
  rw [he]

private theorem conjugation_natural {A G : GroupScheme K} (f : A ⟶ G)
    (p : RationalPoint A.X) :
    f.hom.hom ≫ conjugation (p ≫ f.hom.hom) = conjugation p ≫ f.hom.hom := by
  rw [comp_conjugation]
  change _ = ((toUnit A.X ≫ p) * 𝟙 A.X * (toUnit A.X ≫ p)⁻¹) ≫ f.hom.hom
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, Category.id_comp]
  simp only [Category.assoc]

private theorem subgroupConjugates_of_raw {G : GroupScheme K} {B C : ClosedSubgroup G}
    (g : RationalPoint G.X) (i : B.group.X.left ≅ C.group.X.left)
    (hi : i.hom ≫ C.inclusion.hom.hom.left =
      B.inclusion.hom.hom.left ≫ (conjugation g).left) : ConjugatesSubgroups g B C := by
  have hw : i.hom ≫ C.group.X.hom = B.group.X.hom := by
    rw [← Over.w C.inclusion.hom.hom, ← Category.assoc, hi]
    simp only [Category.assoc, Over.w]
  let j : B.group.X ≅ C.group.X := Over.isoMk i hw
  have hj : j.hom ≫ C.inclusion.hom.hom =
      (B.inclusion ≫ (conjugationIso g).hom).hom.hom := Over.OverMorphism.ext hi
  letI : IsClosedImmersion C.inclusion.hom.hom.left := C.isClosedImmersion
  haveI : Mono C.inclusion.hom.hom := Over.mono_of_mono_left _
  letI := isMonHom_of_factor (B.inclusion ≫ (conjugationIso g).hom) C.inclusion j.hom hj
  exact (conjugates_iff_iso g B C).mpr ⟨Grp.mkIso' j, Grp.hom_ext _ _ hj⟩

private theorem operated_conjugates {H₀ : AffineAlgebraicGroup k} {H : AffineAlgebraicGroup K}
    {B₀ : ClosedSubgroup H₀.val} {B : ClosedSubgroup H.val}
    (e : (groupBaseChange k K).obj H₀.val ≅ H.val)
    (D : HopfDescentDatum k (AdjointCocharacters.coordinateHopf H))
    (σ : Gal(K/k)) {c u : RationalPoint H.val.X}
    (hw : e.hom.hom.hom.left ≫ schemeOperator H D σ =
      coefficientMap σ H₀.val.X ≫ e.hom.hom.hom.left)
    (hc : ConjugatesSubgroups c B (transportSubgroup e (extendSubgroup K B₀)))
    (hu : MovesBorel D B σ u) :
    ConjugatesSubgroups (groupPointOperator H D σ c * u) B
      (transportSubgroup e (extendSubgroup K B₀)) := by
  let X := ((groupBaseChange k K).obj H₀.val).X
  let E := (schemeOfGroup K).mapIso e
  let E' := (Over.forget _).mapIso E
  let C := transportSubgroup e (extendSubgroup K B₀)
  let a := schemeOperator H D σ
  let b := coefficientMap σ H₀.val.X
  let p : RationalPoint X := c ≫ E.inv
  let q := twistedSections σ⁻¹ H₀.val p
  let z := groupPointOperator H D σ c
  have hp : p ≫ E.hom = c := by simp [p]
  have hz : q ≫ E.hom = z := by
    change twistedSections σ⁻¹ H₀.val p ≫ E.hom = z
    rw [← coefficientPoint_eq_twisted]
    apply Over.OverMorphism.ext
    change (scalarMap σ ≫ p.left ≫ b) ≫ E'.hom = scalarMap σ ≫ c.left ≫ a
    have hp' : p.left ≫ E'.hom = c.left := congrArg Over.Hom.left hp
    change E'.hom ≫ a = b ≫ E'.hom at hw
    rw [← hp']
    simpa only [Category.assoc] using congrArg (fun f ↦ scalarMap σ ≫ p.left ≫ f) hw.symm
  have ht : (conjugation p).left ≫ b = b ≫ (conjugation q).left := by
    have h := congrArg ((underlying K).map) (twist_conjugation σ⁻¹ H₀.val p)
    rw [Functor.map_comp] at h
    exact h
  have he₁ : E'.hom ≫ (conjugation c).left = (conjugation p).left ≫ E'.hom := by
    have h : E.hom ≫ conjugation (p ≫ E.hom) = conjugation p ≫ E.hom :=
      conjugation_natural e.hom p
    rw [hp] at h
    exact congrArg Over.Hom.left h
  have he₂ : E'.hom ≫ (conjugation z).left = (conjugation q).left ≫ E'.hom := by
    have h : E.hom ≫ conjugation (q ≫ E.hom) = conjugation q ≫ E.hom :=
      conjugation_natural e.hom q
    rw [hz] at h
    exact congrArg Over.Hom.left h
  have ha : (conjugation c).left ≫ a = a ≫ (conjugation z).left := by
    apply (cancel_epi E'.hom).mp
    change E'.hom ≫ a = b ≫ E'.hom at hw
    calc
      E'.hom ≫ (conjugation c).left ≫ a =
          (conjugation p).left ≫ E'.hom ≫ a := by
        rw [← Category.assoc, he₁, Category.assoc]
      _ = (conjugation p).left ≫ b ≫ E'.hom := by rw [hw]
      _ = b ≫ (conjugation q).left ≫ E'.hom := by
        rw [← Category.assoc, ht, Category.assoc]
      _ = b ≫ E'.hom ≫ (conjugation z).left := by rw [← he₂]
      _ = E'.hom ≫ a ≫ (conjugation z).left := by
        rw [← Category.assoc, ← hw, Category.assoc]
  have hC : C.inclusion.hom.hom.left ≫ a =
      coefficientMap σ B₀.group.X ≫ C.inclusion.hom.hom.left := by
    have h := congrArg Over.Hom.left
      ((twistBaseChangeIso (k := k) (K := K) σ⁻¹).hom.naturality B₀.inclusion.hom.hom)
    let f := ((baseChange k K).map B₀.inclusion.hom.hom).left
    change f ≫ b = coefficientMap σ B₀.group.X ≫ f at h
    change E'.hom ≫ a = b ≫ E'.hom at hw
    change (f ≫ E'.hom) ≫ a = coefficientMap σ B₀.group.X ≫ (f ≫ E'.hom)
    rw [Category.assoc, hw, ← Category.assoc f, h, Category.assoc]
  obtain ⟨d, hd⟩ := (conjugates_iff_iso c B C).mp hc
  let d' := (underlying K).mapIso d
  have hd' : d'.hom ≫ C.inclusion.hom.hom.left =
      B.inclusion.hom.hom.left ≫ (conjugation c).left := by
    have h := congrArg (fun f ↦ (underlying K).map f) hd
    rw [Functor.map_comp, Functor.map_comp] at h
    exact h
  obtain ⟨v, hv⟩ := hu
  have hv' : v.hom ≫ B.inclusion.hom.hom.left ≫ (conjugation u).left =
      B.inclusion.hom.hom.left ≫ a := by
    have h : B.inclusion.hom.hom ≫ conjugation u =
       (toUnit B.group.X ≫ u) * B.inclusion.hom.hom * (toUnit B.group.X ≫ u)⁻¹ :=
      comp_conjugation u _
    have h' := congrArg Over.Hom.left h
    change B.inclusion.hom.hom.left ≫ (conjugation u).left = _ at h'
    rw [h']
    exact hv
  let w : C.group.X.left ≅ C.group.X.left :=
    (Over.forget _).mapIso ((twistBaseChangeIso σ⁻¹).app B₀.group.X)
  have hm : (conjugation u).left ≫ (conjugation z).left = (conjugation (z * u)).left := by
    have h := congrArg (fun f ↦ (underlying K).map f) (conjugation_mul z u)
    rw [Functor.map_comp] at h
    exact h
  apply subgroupConjugates_of_raw (z * u) (v.symm ≪≫ d' ≪≫ w)
  change (v.inv ≫ d'.hom ≫ coefficientMap σ B₀.group.X) ≫ C.inclusion.hom.hom.left =
    B.inclusion.hom.hom.left ≫ (conjugation (z * u)).left
  rw [← hm]
  simp only [Category.assoc]
  rw [← hC, ← Category.assoc d'.hom, hd', Category.assoc, ha]
  rw [← (Category.assoc B.inclusion.hom.hom.left a _), ← hv']
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem flagAction {H₀ : AffineAlgebraicGroup k} {H : AffineAlgebraicGroup K}
    {B₀ : ClosedSubgroup H₀.val} {B : ClosedSubgroup H.val}
    (Q₀ : Presentation B₀) (Q : Presentation B) (hH : IsReductive H) (hB : IsKBorel B)
    (D : HopfDescentDatum k (AdjointCocharacters.coordinateHopf H))
    (e : (groupBaseChange k K).obj H₀.val ≅ H.val)
    (j : (baseChange k K).obj Q₀.scheme ≅ Q.scheme) (c : RationalPoint H.val.X)
    (hc : ConjugatesSubgroups c B (transportSubgroup e (extendSubgroup K B₀)))
    (hj : ∀ (S : SchemeOver K) (g : S ⟶ ((groupBaseChange k K).obj H₀.val).X),
      g ≫ (baseChange k K).map Q₀.projection ≫ j.hom =
        rightTranslate (g ≫ e.hom.hom.hom) c ≫ Q.projection)
    (σ : Gal(K/k)) (u : RationalPoint H.val.X)
    (he : e.hom.hom.hom.left ≫ schemeOperator H D σ =
      coefficientMap σ H₀.val.X ≫ e.hom.hom.hom.left)
    (hu : MovesBorel D B σ u)
    (g : RationalPoint H.val.X) :
    coefficientPoint σ Q₀.scheme (g ≫ Q.projection ≫ j.inv) ≫ j.hom =
      rightTranslate (groupPointOperator H D σ g) u ≫ Q.projection := by
  let F := twistedSections σ⁻¹ H₀.val
  let A := groupPointOperator H D σ
  let m : RationalPoint ((groupBaseChange k K).obj H₀.val).X ≃* RationalPoint H.val.X :=
    ((yonedaGrp.mapIso e).app (op (𝟙_ (SchemeOver K)))).groupIsoToMulEquiv
  have hm (x : RationalPoint ((groupBaseChange k K).obj H₀.val).X) : m (F x) = A (m x) := by
    let f := e.hom.hom.hom
    change twistedSections σ⁻¹ _ x ≫ f = A (x ≫ f)
    rw [← coefficientPoint_eq_twisted]
    apply Over.OverMorphism.ext
    change (scalarMap σ ≫ x.left ≫ coefficientMap σ H₀.val.X) ≫ f.left =
      scalarMap σ ≫ (x.left ≫ f.left) ≫ schemeOperator H D σ
    simpa only [Category.assoc] using congrArg (fun a ↦ scalarMap σ ≫ x.left ≫ a) he.symm
  have hmul (x y : RationalPoint H.val.X) : A (x * y) = A x * A y := by
    obtain ⟨a, rfl⟩ := m.surjective x
    obtain ⟨b, rfl⟩ := m.surjective y
    rw [← map_mul, ← hm, map_mul, map_mul, hm, hm]
  have hr (x y : RationalPoint H.val.X) : rightTranslate x y = x * y := by
    have h : toUnit (𝟙_ (SchemeOver K)) = 𝟙 (𝟙_ (SchemeOver K)) :=
      (isTerminalTensorUnit (C := SchemeOver K)).hom_ext _ _
    simp only [rightTranslate, h, Category.id_comp]
  let x := m.symm (g * c⁻¹)
  have hx : m x = g * c⁻¹ := m.apply_symm_apply _
  have hq : x ≫ (baseChange k K).map Q₀.projection = g ≫ Q.projection ≫ j.inv := by
    apply (cancel_mono j.hom).mp
    calc
      (x ≫ (baseChange k K).map Q₀.projection) ≫ j.hom =
          rightTranslate (x ≫ e.hom.hom.hom) c ≫ Q.projection :=
        (Category.assoc _ _ _).trans (hj _ x)
      _ = g ≫ Q.projection := by
        rw [hr]
        change (m x * c) ≫ Q.projection = _
        rw [hx, inv_mul_cancel_right]
      _ = (g ≫ Q.projection ≫ j.inv) ≫ j.hom := by
        simp only [Category.assoc, j.inv_hom_id, Category.comp_id]
  rw [← hq, coefficientPoint_natural]
  have hh := (Category.assoc (coefficientPoint σ H₀.val.X x)
    ((baseChange k K).map Q₀.projection) j.hom).trans (hj _ (coefficientPoint σ H₀.val.X x))
  rw [hh, hr, hr]
  rw [coefficientPoint_eq_twisted]
  change (m (F x) * c) ≫ Q.projection = (A g * u) ≫ Q.projection
  apply (projection_eq_iff Q _ _).mpr
  have hn := normalizes_of_conjugates_self B (conjugates_trans
    (operated_conjugates e D σ he hc hu) (conjugates_inverse hc))
  obtain ⟨s, hs⟩ := (RootData.BorelNormalizer.groundFieldBorelNormalizer H hH B hB _ _).mp hn
  refine ⟨s, ?_⟩
  change s ≫ B.inclusion.hom.hom = (m (F x) * c)⁻¹ * (A g * u)
  rw [hs, hm]
  have hx' : m x * c = g := by rw [hx, inv_mul_cancel_right]
  have hAg : A (m x) * A c = A g := by rw [← hmul, hx']
  rw [← hAg]
  change c⁻¹ * (A c * u) = (A (m x) * c)⁻¹ * (A (m x) * A c * u)
  group

end FlagAction

theorem finiteFieldFlagDescent : FiniteFieldFlagDescent.{u} := by
  intro k K _ _ _ _ _ _ _ H B Q hH hB D u hu
  obtain ⟨J, hJ⟩ := affineHopfDescent D
  let H₀ := descendedGroup J
  let e : (groupBaseChange k K).obj H₀.val ≅ H.val :=
    (groupDescentComparison J).symm ≪≫ AdjointCocharacters.coordinateHopfIso H
  have hr : IsReductive H₀ := reductive_descends e hH
  have he (σ : Gal(K/k)) : e.hom.hom.hom.left ≫ schemeOperator H D σ =
      coefficientMap σ H₀.val.X ≫ e.hom.hom.hom.left := group_operator_comparison J hJ σ
  obtain ⟨_, B₀, hB₀⟩ := FiniteFieldFlags.reductiveQuasiSplit H₀ hr
  obtain ⟨Q₀⟩ := QuotientEmbedding.quotientEmbedding k H₀ B₀
  obtain ⟨c, hc⟩ := rational_borel_conjugacy H hH B _
    hB (borel_after_field_extension e B₀ hB₀)
  obtain ⟨j, hj⟩ := projection_comparison Q₀ Q e c hc
  refine ⟨H₀, B₀, Q₀, e, j, c, hr, hB₀, ?_, hj, ?_, ⟨1 ≫ Q₀.projection⟩⟩
  · intro σ g
    apply Over.OverMorphism.ext
    change (scalarMap σ ≫ g.left ≫ coefficientMap σ H₀.val.X) ≫ e.hom.hom.hom.left =
      scalarMap σ ≫ (g.left ≫ e.hom.hom.hom.left) ≫ schemeOperator H D σ
    simpa only [Category.assoc] using congrArg (fun f ↦ scalarMap σ ≫ g.left ≫ f) (he σ).symm
  · intro σ g
    exact flagAction Q₀ Q hH hB D e j c hc hj σ (u σ) (he σ) (hu σ) g

end

end LinearAlgebraicGroups.Descent.ResidueFlagDescent
