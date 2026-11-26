import Specs.LinearAlgebraicGroups.Classification.PinnedEquivalence
import Specs.LinearAlgebraicGroups.Classification.IntegralRealization
import LinearAlgebraicGroups.Classification.OrdinaryCentralLifting
import LinearAlgebraicGroups.Classification.PinnedUniqueness
import LinearAlgebraicGroups.Reductive.SplitToriConjugacy
import LinearAlgebraicGroups.RootData.BorelPositivity
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.Classification.IntegralRealization
open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

universe u

namespace LinearAlgebraicGroups.Classification.PinnedEquivalence

open _root_.LinearAlgebraicGroups.Specs
open Specs.PinnedEquivalence
open Specs.AbstractPairing (Root)
open Specs.BorelsAndChambers (subgroupRoots IsPositiveSystem)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (pairing)
open Specs.CellHomomorphism (pullbackCharacters)
open Specs.Pinning (AttachedDatum BasedIso BasedRootDatum PinnedGroup PinnedIso
  SplitBorelPair SimpleRoot transportCharacter)
open Specs.GeometricBorelConjugacy (IsBorel IsKBorel)
open Specs.GeometricRadicals (baseChangedSubgroup)
open Specs.RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.RootGroups (AdditiveLine)
open LinearAlgebraicGroups.Classification.Pinning
  (attachedDatum basedDatumFunctor inducedBasedIso pinningsExist standardAdditiveLine)
open private transportSubgroup maximal_of_square conjugationIso
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private closedSubgroup_eq from LinearAlgebraicGroups.RootData.BorelPositivity
open private inclusion_mono subgroupIso from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private extendSubgroup extend_subgroupOf subgroupOf_of_extend
  from LinearAlgebraicGroups.RootData.RankOneFlag
open private rootsOfIso weightSpace_le_lieImage_iff conjugatesSubgroups_square
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private charactersOfIso from LinearAlgebraicGroups.RootData.CharacterPairing

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {A : AdditiveLine k}

private theorem pushBorel {G H : GroupScheme k} (f : G ≅ H)
    {B : ClosedSubgroup G} (hB : IsBorel B) : IsBorel (transportSubgroup f B) := by
  refine ⟨hB.1, ?_⟩
  rintro C hC ⟨i, hi⟩
  have hi' : i ≫ (transportSubgroup f.symm C).inclusion = B.inclusion := by
    change i ≫ C.inclusion ≫ f.inv = B.inclusion
    rw [← Category.assoc, hi]
    change (B.inclusion ≫ f.hom) ≫ f.inv = B.inclusion
    simp
  obtain ⟨j, hj⟩ := hB.2 (transportSubgroup f.symm C) hC ⟨i, hi'⟩
  refine ⟨j, ?_⟩
  change j ≫ B.inclusion ≫ f.hom = C.inclusion
  rw [← Category.assoc, hj]
  change (C.inclusion ≫ f.inv) ≫ f.hom = C.inclusion
  simp

private theorem pushKBorel {G H : GroupScheme k} (f : G ≅ H)
    {B : ClosedSubgroup G} (hB : IsKBorel B) : IsKBorel (transportSubgroup f B) := by
  obtain ⟨h, hB⟩ := hB
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  have hcomp : F.map (transportSubgroup f B).inclusion = F.map B.inclusion ≫ F.map f.hom :=
    F.map_comp B.inclusion f.hom
  have hEq : (F.map (transportSubgroup f B).inclusion).hom.hom.left =
      (transportSubgroup (F.mapIso f) (Specs.GeometricRadicals.baseChangedSubgroup K B h)).inclusion.hom.hom.left :=
    congrArg (fun g => g.hom.hom.left) hcomp
  let C := transportSubgroup (F.mapIso f) (Specs.GeometricRadicals.baseChangedSubgroup K B h)
  have hclosed : IsClosedImmersion (F.map (transportSubgroup f B).inclusion).hom.hom.left :=
    hEq.symm ▸ C.isClosedImmersion
  refine ⟨hclosed, ?_⟩
  have he : Specs.GeometricRadicals.baseChangedSubgroup K (transportSubgroup f B) hclosed = C :=
    closedSubgroup_eq hcomp
  exact he.symm ▸ pushBorel (F.mapIso f) hB

private theorem maximalTransport {G H : GroupScheme k} (f : G ≅ H)
    (T : ClosedSubgroup G) (hT : IsGeometricallyMaximal T) :
    IsGeometricallyMaximal (transportSubgroup f T) := by
  obtain ⟨h, hT⟩ := hT
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let V := transportSubgroup (F.mapIso f) (baseChangedSubgroup K T h)
  have he : F.map (transportSubgroup f T).inclusion = V.inclusion :=
    F.map_comp T.inclusion f.hom
  have hc : IsClosedImmersion (F.map (transportSubgroup f T).inclusion).hom.hom.left :=
    he.symm ▸ V.isClosedImmersion
  refine ⟨hc, ?_⟩
  have hv : baseChangedSubgroup K (transportSubgroup f T) hc = V := closedSubgroup_eq he
  rw [hv]
  exact maximal_of_square (F.mapIso f) (baseChangedSubgroup K T h) V (Iso.refl _) (by
    change 𝟙 _ ≫ _ = _
    rw [Category.id_comp] <;> rfl) hT

private theorem isIso_torus_restriction {G H : GroupScheme k} (f : G ≅ H)
    {S : ClosedSubgroup G} {T : ClosedSubgroup H}
    (hS : IsGeometricallyMaximal S) (hT : IsGeometricallyMaximal T)
    (τ : S.group ⟶ T.group) (h : S.inclusion ≫ f.hom = τ ≫ T.inclusion) : IsIso τ := by
  let V := transportSubgroup f S
  let K := AlgebraicClosure k
  obtain ⟨_, hVmax⟩ := maximalTransport f S hS
  obtain ⟨_, hTmax⟩ := hT
  have hVT : IsSubgroupOf V T := ⟨τ, h.symm⟩
  have hTV : IsSubgroupOf T V := subgroupOf_of_extend (K := K)
    (hVmax.2 (extendSubgroup K T) hTmax.1 (extend_subgroupOf (K := K) hVT))
  let e := subgroupIso (A := V) (B := T) ⟨hVT, hTV⟩
  letI := inclusion_mono T
  have he : e.val.hom = τ := (cancel_mono T.inclusion).mp (e.property.trans h)
  exact he ▸ (inferInstance : IsIso e.val.hom)

private theorem base_isPos_iff_subgroupRoots {P : SplitBorelPair k} (D : AttachedDatum P)
    (h : IsPositiveSystem P.T (subgroupRoots P.T P.B)) :
    letI := D.comm
    ∀ i, D.base.IsPos i ↔ i ∈ subgroupRoots P.T P.B := by
  classical
  letI := D.comm
  letI := D.datum.finiteRoots
  obtain ⟨l, _, hsign⟩ := h
  have hmem (i : Root P.T) :
      i ∈ subgroupRoots P.T P.B ↔ 0 < l (D.datum.rootDatum.root i) := by
    simp only [hsign, D.datum.root_eq, Set.mem_ofPred_eq]
  have hsimple (i : Root P.T) (hi : i ∈ D.base.support) :
      0 < l (D.datum.rootDatum.root i) := (hmem i).mp ((D.simple_iff i).mp hi).1
  have hpositive (i : Root P.T) (hi : D.base.IsPos i) : 0 < l (D.datum.rootDatum.root i) := by
    refine hi.induction_on_add hsimple ?_
    intro j l' m hm hj hl'
    rw [hm, map_add]
    exact add_pos hj (hsimple l' hl')
  intro i
  rw [hmem]
  refine ⟨hpositive i, fun hi => ?_⟩
  by_contra hn
  let j := D.datum.rootDatum.reflectionPerm i i
  have hj : D.base.IsPos j := (RootPairing.Base.IsPos.neg_iff_not D.base i).mpr hn
  have hneg := hpositive j hj
  have he : D.datum.rootDatum.root j = -D.datum.rootDatum.root i :=
    D.datum.rootDatum.root_eq_neg_iff.mpr rfl
  rw [he, map_neg] at hneg
  exact (not_lt_of_ge hi.le) (neg_pos.mp hneg)

private theorem basedIso_base_iff {D E : BasedRootDatum.{u}} (e : BasedIso D E) (i : D.I) :
    i ∈ D.base.support ↔ e.val.indexEquiv i ∈ E.base.support := by
  have he := congrArg (fun S : Set E.I => e.val.indexEquiv i ∈ S) e.property
  constructor
  · intro h
    exact Eq.mp he ⟨i, h, rfl⟩
  · intro h
    obtain ⟨j, hj, eq⟩ := Eq.mpr he h
    exact e.val.indexEquiv.injective eq ▸ hj

private theorem basedIso_pos {D E : BasedRootDatum.{u}} (e : BasedIso D E) (i : D.I) :
    D.base.IsPos i → E.base.IsPos (e.val.indexEquiv i) := by
  letI := D.finiteRoots
  letI := D.reduced
  intro hi
  refine hi.induction_on_add (fun j hj => E.base.isPos_of_mem_support ((basedIso_base_iff e j).mp hj)) ?_
  intro j l m hm hj hl
  apply RootPairing.Base.IsPos.add hj (E.base.isPos_of_mem_support ((basedIso_base_iff e l).mp hl))
  have h (a : D.I) : e.val.weightMap (D.datum.root a) = E.datum.root (e.val.indexEquiv a) :=
    e.val.toHom.root_weightMap_apply D.datum E.datum a
  rw [← h m, hm, map_add, h j, h l]

private def liftCharacters {P Q : PinnedGroup A} {D : AttachedDatum P.pair}
    {E : AttachedDatum Q.pair} (e : BasedIso D.toBased E.toBased) :
    Character Q.pair.T.group ≃* Character P.pair.T.group :=
  e.val.weightEquiv.symm.toAddEquiv.toMultiplicative

private theorem character_transport_of_pullback {P Q : PinnedGroup A}
    {D : AttachedDatum P.pair} {E : AttachedDatum Q.pair}
    (e : BasedIso D.toBased E.toBased) (t : P.pair.T.group ≅ Q.pair.T.group)
    (ht : pullbackCharacters t.hom = (liftCharacters e).toMonoidHom)
    (χ : Character P.pair.T.group) :
    Additive.ofMul (transportCharacter t χ) = e.val.weightEquiv (Additive.ofMul χ) := by
  apply e.val.weightEquiv.symm.injective
  have hpull : liftCharacters e (t.inv ≫ χ) = χ :=
    (DFunLike.congr_fun ht (t.inv ≫ χ)).symm.trans (t.hom_inv_id_assoc χ)
  change Additive.ofMul (liftCharacters e (t.inv ≫ χ)) =
    e.val.weightEquiv.symm (e.val.weightEquiv (Additive.ofMul χ))
  exact (congrArg Additive.ofMul hpull).trans
    (e.val.weightEquiv.symm_apply_apply (Additive.ofMul χ)).symm

private theorem basedIso_pos_iff {D E : BasedRootDatum.{u}} (e : BasedIso D E) (i : D.I) :
    D.base.IsPos i ↔ E.base.IsPos (e.val.indexEquiv i) := by
  refine ⟨basedIso_pos e i, fun h => ?_⟩
  have he := basedIso_pos (Groupoid.inv (show D ⟶ E from e)) (e.val.indexEquiv i) h
  change D.base.IsPos (e.val.indexEquiv.symm (e.val.indexEquiv i)) at he
  simpa only [Equiv.symm_apply_apply] using he

private theorem basedIso_ext_weight {D E : BasedRootDatum.{u}} (e e' : BasedIso D E)
    (h : ∀ x, e.val.weightEquiv x = e'.val.weightEquiv x) : e = e' := by
  apply Subtype.ext
  apply RootPairing.Equiv.ext
  · ext x
    exact h x
  · ext y
    apply D.datum.flip.toPerfPair.injective
    ext x
    have h₁ := DFunLike.congr_fun (e.val.toHom.weight_coweight_transpose_apply D.datum E.datum y) x
    have h₂ := DFunLike.congr_fun (e'.val.toHom.weight_coweight_transpose_apply D.datum E.datum y) x
    change E.datum.toLinearMap (e.val.weightEquiv x) y =
      D.datum.toLinearMap x (e.val.coweightEquiv y) at h₁
    change E.datum.toLinearMap (e'.val.weightEquiv x) y =
      D.datum.toLinearMap x (e'.val.coweightEquiv y) at h₂
    exact h₁.symm.trans ((congrArg (fun z => E.datum.toLinearMap z y) (h x)).trans h₂)
  · ext i
    apply E.datum.root.injective
    have h₁ := e.val.toHom.root_weightMap_apply D.datum E.datum i
    have h₂ := e'.val.toHom.root_weightMap_apply D.datum E.datum i
    exact h₁.symm.trans ((h (D.datum.root i)).trans h₂)

private theorem pinnedLift
    (P Q : PinnedGroup A) (D : AttachedDatum P.pair) (E : AttachedDatum Q.pair)
    (e : BasedIso D.toBased E.toBased) :
    ∃ f : PinnedIso P Q, inducedBasedIso f D E = e := by
  classical
  letI := D.comm
  letI := E.comm
  let d : Root P.pair.T ≃ Root Q.pair.T := e.val.indexEquiv
  -- The prescribed covariant character equivalence gives the lift's inverse pullback.
  let h := liftCharacters e
  have root (α : Root P.pair.T) : h (d α).val = α.val := by
    have hr := e.val.toHom.root_weightMap_apply D.toBased.datum E.toBased.datum α
    change e.val.weightEquiv (D.datum.rootDatum.root α) = E.datum.rootDatum.root (d α) at hr
    rw [D.datum.root_eq, E.datum.root_eq] at hr
    exact congrArg Additive.toMul ((e.val.weightEquiv.symm_apply_eq).2 hr.symm)
  have dual (α : Root P.pair.T) (χ : Character Q.pair.T.group) :
      pairing P.pair.T.group (h χ) (Additive.toMul (D.datum.rootDatum.coroot α)) =
        pairing Q.pair.T.group χ (Additive.toMul (E.datum.rootDatum.coroot (d α))) := by
    rw [← D.datum.pairing_eq, ← E.datum.pairing_eq]
    have hc := e.val.toHom.coroot_coweightMap_apply D.toBased.datum E.toBased.datum (d α)
    change e.val.coweightEquiv (E.datum.rootDatum.coroot (d α)) =
      D.datum.rootDatum.coroot (d.symm (d α)) at hc
    rw [Equiv.symm_apply_apply] at hc
    rw [← hc]
    have ht := DFunLike.congr_fun (e.val.toHom.weight_coweight_transpose_apply
      D.toBased.datum E.toBased.datum (E.datum.rootDatum.coroot (d α)))
      (e.val.weightEquiv.symm (Additive.ofMul χ))
    change E.datum.rootDatum.toLinearMap
        (e.val.weightEquiv (e.val.weightEquiv.symm (Additive.ofMul χ))) _ =
      D.datum.rootDatum.toLinearMap (e.val.weightEquiv.symm (Additive.ofMul χ)) _ at ht
    rw [LinearEquiv.apply_symm_apply] at ht
    exact ht.symm
  have hfinite : Finite (Character P.pair.T.group ⧸ h.toMonoidHom.range) := by
    rw [MonoidHom.range_eq_top.mpr h.surjective]
    letI := QuotientGroup.subsingleton_quotient_top (G := Character P.pair.T.group)
    infer_instance
  obtain ⟨τ, f, hτ, hp, _, _, _, _, hIso, _⟩ :=
    OrdinaryCentralLifting.ordinaryCentralLifting P Q D E d h.toMonoidHom h.injective
      hfinite root dual (basedIso_base_iff e)
  letI : IsIso f := hIso h.surjective
  let F := asIso f
  letI : IsIso τ := isIso_torus_restriction F P.pair.maximal Q.pair.maximal τ hp.1
  let t := asIso τ
  have ht (χ : Character P.pair.T.group) :
      Additive.ofMul (transportCharacter t χ) = e.val.weightEquiv (Additive.ofMul χ) :=
    character_transport_of_pullback e t hτ χ
  have label (α : Root P.pair.T) : t.inv ≫ α.val = (d α).val := by
    have he : τ ≫ (d α).val = α.val := (DFunLike.congr_fun hτ (d α).val).trans (root α)
    rw [← he]
    exact t.inv_hom_id_assoc _
  let B := transportSubgroup F P.pair.B
  have hTB : Specs.SchemeDerivedGroup.IsSubgroupOf Q.pair.T B := by
    obtain ⟨j, hj⟩ := P.pair.containsTorus
    refine ⟨t.inv ≫ j, ?_⟩
    change (t.inv ≫ j) ≫ P.pair.B.inclusion ≫ f = Q.pair.T.inclusion
    simp only [Category.assoc, reassoc_of% hj, hp.1]
    exact t.inv_hom_id_assoc _
  obtain ⟨_, _, _, hCorr, _, _, _⟩ :=
    RootData.BorelPositivity.borelPositivity Q.pair.G Q.pair.reductive Q.pair.T Q.pair.split Q.pair.maximal
  obtain ⟨_, _, _, hCorrP, _, _, _⟩ :=
    RootData.BorelPositivity.borelPositivity P.pair.G P.pair.reductive P.pair.T P.pair.split P.pair.maximal
  have hPosP := base_isPos_iff_subgroupRoots D (hCorrP.1 P.pair.B P.pair.borel P.pair.containsTorus)
  have hPosQ := base_isPos_iff_subgroupRoots E (hCorr.1 Q.pair.B Q.pair.borel Q.pair.containsTorus)
  -- The transported Borel has the target's positive system because the lattice map is based.
  have hB : SameSubgroup B Q.pair.B := (hCorr.2.2 B Q.pair.B
    (pushKBorel F P.pair.borel) Q.pair.borel hTB Q.pair.containsTorus).mp (by
    ext β
    obtain ⟨α, rfl⟩ := d.surjective β
    have hpos := (hPosP α).symm.trans ((basedIso_pos_iff e α).trans (hPosQ (d α)))
    have hw := weightSpace_le_lieImage_iff F t hp.1
      (B := P.pair.B) (C := B) (Iso.refl _) (by simp [B, transportSubgroup]) (d α).val
    have hlabel : t.hom ≫ (d α).val = α.val :=
      (DFunLike.congr_fun hτ (d α).val).trans (root α)
    rw [hlabel] at hw
    exact hw.symm.trans hpos)
  let b := subgroupIso hB
  let pinIso : PinnedIso P Q :=
    { group := F, torus := t, borel := b.val, torus_comm := hp.1,
      borel_comm := b.property.symm,
      pin_comm := by
        ext z
        constructor
        · rintro ⟨_, ⟨α, rfl⟩, rfl⟩
          let β : SimpleRoot Q.pair := ⟨d α.val,
            (E.simple_iff _).mp ((basedIso_base_iff e α.val).mp ((D.simple_iff _).mpr α.property))⟩
          exact ⟨β, Prod.ext (label α.val).symm (hp.2 α β rfl).symm⟩
        · rintro ⟨β, rfl⟩
          let α : SimpleRoot P.pair := ⟨d.symm β.val, (D.simple_iff _).mp
            ((basedIso_base_iff e (d.symm β.val)).mpr
              (by
                change d (d.symm β.val) ∈ E.base.support
                rw [d.apply_symm_apply]
                exact (E.simple_iff _).mpr β.property))⟩
          have he : d α.val = β.val := d.apply_symm_apply _
          refine ⟨_, ⟨α, rfl⟩, Prod.ext ?_ (hp.2 α β he)⟩
          exact (label α.val).trans (congrArg Subtype.val he) }
  refine ⟨pinIso, basedIso_ext_weight _ _ ?_⟩
  intro x
  exact ht (Additive.toMul x)

private theorem realizePinned (realize : Specs.IntegralRealization.Statement.{u})
    (D : BasedRootDatum.{u}) (A : AdditiveLine k) :
    ∃ (P : PinnedGroup A) (E : AttachedDatum P.pair), Nonempty (BasedIso D E.toBased) := by
  obtain ⟨M⟩ := realize D
  obtain ⟨_, R, _⟩ := M.fieldFibre k
  -- Pin the same Borel pair using the additive line of the source groupoid.
  obtain ⟨U, ⟨pin⟩⟩ := pinningsExist A R.pinned.pair
  exact ⟨⟨R.pinned.pair, U, pin⟩, R.attached, ⟨R.datumIso⟩⟩

private theorem pinnedClassification (realize : Specs.IntegralRealization.Statement.{u}) :
    PinnedClassification.{u} := by
  intro k _ A
  let F := basedDatumFunctor A
  have faithful : F.Faithful := PinnedUniqueness.faithfulBasedDatumFunctor A
  have unique (P Q : PinnedGroup A) (e : F.obj P ⟶ F.obj Q) :
      ∃! f : P ⟶ Q, F.map f = e := by
    obtain ⟨f, hf⟩ := pinnedLift P Q (attachedDatum P.pair) (attachedDatum Q.pair) e
    exact ⟨f, hf, fun g hg => faithful.map_injective (hg.trans hf.symm)⟩
  refine ⟨fun P => attachedDatum P.pair, F, fun _ => rfl,
    fun _ _ _ => ⟨fun _ => rfl, fun _ => rfl⟩, ⟨faithful, ⟨fun e => (unique _ _ e).exists⟩, ?_⟩, unique⟩
  constructor
  intro D
  obtain ⟨P, E, ⟨e⟩⟩ := realizePinned realize D A
  let j := inducedBasedIso (PinnedIso.refl P) E (attachedDatum P.pair)
  exact ⟨P, ⟨(asIso (show D ⟶ F.obj P from e ≫ j)).symm⟩⟩

open Specs.AdjointRepresentation (GroupPoints)
open Specs.RootGroups (HasScalarAction IsRootSubgroup rootPoint)
open Specs.CharacterPairing (characterValue)
open Specs.Pinning (IsSimple RootCoordinate)
open private subgroupRootsOfIso exists_avoiding_zero_forms
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private normalizes_of_scalarAction from LinearAlgebraicGroups.Classification.PinnedUniqueness
open private tangent_weight_of_scalarAction rootPoint_comp
  from LinearAlgebraicGroups.RootData.RootGroups

/-- Align the split tori by rational conjugacy and then the two positive systems
by a rational representative of the Weyl action on the common torus. -/
private theorem alignPairs (P Q : SplitBorelPair k) (f : P.G.val ≅ Q.G.val) :
    ∃ (F : P.G.val ≅ Q.G.val) (t : P.T.group ≅ Q.T.group) (b : P.B.group ≅ Q.B.group),
      P.T.inclusion ≫ F.hom = t.hom ≫ Q.T.inclusion ∧
      P.B.inclusion ≫ F.hom = b.hom ≫ Q.B.inclusion := by
  let S := transportSubgroup f P.T
  obtain ⟨g, t, ht⟩ := Reductive.SplitToriConjugacy.splitToriConjugacy Q.G
    ⟨Q.reductive, Q.T, Q.split, Q.maximal⟩ S Q.T P.split Q.split (maximalTransport f P.T P.maximal)
    Q.maximal
  let F := f ≪≫ conjugationIso g
  have ht' : P.T.inclusion ≫ F.hom = t.hom ≫ Q.T.inclusion := by
    rw [Iso.trans_hom, ← Category.assoc]
    exact conjugatesSubgroups_square g t ht
  let B := transportSubgroup F P.B
  have hB := pushKBorel F P.borel
  have hTB : Specs.SchemeDerivedGroup.IsSubgroupOf Q.T B := by
    obtain ⟨j, hj⟩ := P.containsTorus
    refine ⟨t.inv ≫ j, ?_⟩
    change (t.inv ≫ j) ≫ P.B.inclusion ≫ F.hom = Q.T.inclusion
    simp only [Category.assoc, reassoc_of% hj, ht', Iso.inv_hom_id_assoc]
  obtain ⟨_, _, _, hCorr, _, _, _⟩ :=
    RootData.BorelPositivity.borelPositivity Q.G Q.reductive Q.T Q.split Q.maximal
  have hPositive := RootData.BorelNormalizer.weylSimplyTransitiveOnPositiveSystems
    Q.G Q.reductive Q.T Q.split Q.maximal
  obtain ⟨n, c, _, hc, hImage, _⟩ := hPositive.2.2 _ _
    (hCorr.1 B hB hTB) (hCorr.1 Q.B Q.borel Q.containsTorus)
  let N := conjugationIso n
  have hc' : Q.T.inclusion ≫ N.hom = c.hom ≫ Q.T.inclusion :=
    conjugatesSubgroups_square n c hc
  let C := transportSubgroup N B
  have hTC : Specs.SchemeDerivedGroup.IsSubgroupOf Q.T C := by
    obtain ⟨j, hj⟩ := hTB
    refine ⟨c.inv ≫ j, ?_⟩
    change (c.inv ≫ j) ≫ B.inclusion ≫ N.hom = Q.T.inclusion
    simp only [Category.assoc, reassoc_of% hj, hc', Iso.inv_hom_id_assoc]
  have hRoots := subgroupRootsOfIso N c hc' (B := B) (C := C) (Iso.refl _)
    (by
      change _ = 𝟙 _ ≫ _
      rw [Category.id_comp] <;> rfl)
  have hS : subgroupRoots Q.T C = subgroupRoots Q.T Q.B := by
    apply (Set.image_injective.mpr Subtype.val_injective)
    simp only [← hRoots, ← hImage, Set.image_image]
  let b := subgroupIso ((hCorr.2.2 C Q.B (pushKBorel N hB) Q.borel hTC Q.containsTorus).mp hS)
  refine ⟨F ≪≫ N, t ≪≫ c, b.val, ?_, ?_⟩
  · simp only [Iso.trans_hom, ← Category.assoc P.T.inclusion, ht', Category.assoc, hc']
  · change P.B.inclusion ≫ (F.hom ≫ N.hom) = _
    rw [← Category.assoc]
    exact b.property.symm

private theorem simple_iff_of_roots {P Q : SplitBorelPair k}
    (d : Root P.T ≃ Root Q.T) (c : Character P.T.group ≃* Character Q.T.group)
    (hlabel : ∀ i, (d i).val = c i.val)
    (hpos : ∀ i, i ∈ subgroupRoots P.T P.B ↔ d i ∈ subgroupRoots Q.T Q.B)
    (i : Root P.T) : IsSimple P i ↔ IsSimple Q (d i) := by
  constructor
  · rintro ⟨hi, hs⟩
    refine ⟨(hpos i).mp hi, ?_⟩
    intro j hj l hl he
    obtain ⟨j, rfl⟩ := d.surjective j
    obtain ⟨l, rfl⟩ := d.surjective l
    rw [hlabel, hlabel, hlabel, ← map_mul] at he
    exact hs j ((hpos j).mpr hj) l ((hpos l).mpr hl) (c.injective he)
  · rintro ⟨hi, hs⟩
    refine ⟨(hpos i).mpr hi, ?_⟩
    intro j hj l hl he
    apply hs (d j) ((hpos j).mp hj) (d l) ((hpos l).mp hl)
    rw [hlabel, hlabel, hlabel, ← map_mul, he]

private def rootsEquivOfIso {P Q : SplitBorelPair k}
    (F : P.G.val ≅ Q.G.val) (t : P.T.group ≅ Q.T.group)
    (ht : P.T.inclusion ≫ F.hom = t.hom ≫ Q.T.inclusion) : Root P.T ≃ Root Q.T := by
  have hr (χ : Character P.T.group) :
      χ ∈ Specs.CharacterPairing.absoluteRoots P.T ↔
        t.inv ≫ χ ∈ Specs.CharacterPairing.absoluteRoots Q.T := by
    have h := rootsOfIso F t ht (t.inv ≫ χ)
    rwa [Iso.hom_inv_id_assoc] at h
  exact (charactersOfIso t).toEquiv.subtypeEquiv hr

private theorem transportedPositives {P Q : SplitBorelPair k}
    (F : P.G.val ≅ Q.G.val) (t : P.T.group ≅ Q.T.group)
    (ht : P.T.inclusion ≫ F.hom = t.hom ≫ Q.T.inclusion)
    (b : P.B.group ≅ Q.B.group) (hb : P.B.inclusion ≫ F.hom = b.hom ≫ Q.B.inclusion)
    (i : Root P.T) :
    i ∈ subgroupRoots P.T P.B ↔ rootsEquivOfIso F t ht i ∈ subgroupRoots Q.T Q.B := by
  have h := weightSpace_le_lieImage_iff F t ht b hb (t.inv ≫ i.val)
  rw [Iso.hom_inv_id_assoc] at h
  exact h

private theorem pushScalarAction {P Q : SplitBorelPair k}
    (F : P.G.val ≅ Q.G.val) (t : P.T.group ≅ Q.T.group)
    (ht : P.T.inclusion ≫ F.hom = t.hom ≫ Q.T.inclusion)
    (χ : Character P.T.group) (x : A.group ⟶ P.G.val) (hx : HasScalarAction P.T χ x) :
    HasScalarAction Q.T (t.inv ≫ χ) (x ≫ F.hom) := by
  intro R r a
  let s : GroupPoints P.T.group R := r ≫ t.inv.hom.hom
  have he : characterValue (t.inv ≫ χ) R r = characterValue χ R s := rfl
  have hs : (s ≫ P.T.inclusion.hom.hom) ≫ F.hom.hom.hom = r ≫ Q.T.inclusion.hom.hom := by
    have h := congrArg (fun j : P.T.group ⟶ Q.G.val => s ≫ j.hom.hom) ht
    have hi := ((Grp.forget (SchemeOver k)).mapIso t).inv_hom_id
    change t.inv.hom.hom ≫ t.hom.hom.hom = 𝟙 _ at hi
    have h' : (s ≫ P.T.inclusion.hom.hom) ≫ F.hom.hom.hom =
        r ≫ (t.inv.hom.hom ≫ t.hom.hom.hom) ≫ Q.T.inclusion.hom.hom := by
      simpa only [Grp.comp_hom_hom, Category.assoc, s] using h
    rw [hi, Category.id_comp] at h'
    exact h'
  have h := congrArg (fun p => p ≫ F.hom.hom.hom) (hx R s a)
  dsimp only at h ⊢
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hs, ← rootPoint_comp,
    ← rootPoint_comp, ← he] at h
  exact h

private theorem pinAlignedPairs (P Q : SplitBorelPair k) (A : AdditiveLine k)
    (F : P.G.val ≅ Q.G.val) (t : P.T.group ≅ Q.T.group)
    (ht : P.T.inclusion ≫ F.hom = t.hom ≫ Q.T.inclusion)
    (b : P.B.group ≅ Q.B.group) (hb : P.B.inclusion ≫ F.hom = b.hom ≫ Q.B.inclusion) :
    ∃ (P' Q' : PinnedGroup A), ∃ (_ : P'.pair = P) (_ : Q'.pair = Q),
      Nonempty (PinnedIso P' Q') := by
  classical
  obtain ⟨U, ⟨p⟩⟩ := pinningsExist A P
  obtain ⟨V, _⟩ := pinningsExist A Q
  let d := rootsEquivOfIso F t ht
  let i : SimpleRoot P ≃ SimpleRoot Q := d.subtypeEquiv
    (simple_iff_of_roots d (charactersOfIso t) (fun _ => rfl)
      (transportedPositives F t ht b hb))
  let x (α : SimpleRoot P) := (p α).val.hom ≫ (U α.val).val.inclusion
  have h₁ (β : SimpleRoot Q) : HasScalarAction Q.T β.val.val (x (i.symm β) ≫ F.hom) := by
    have h := pushScalarAction F t ht _ _ (p (i.symm β)).property
    have he := congrArg (fun j : SimpleRoot Q => j.val.val) (i.apply_symm_apply β)
    change t.inv ≫ (i.symm β).val.val = β.val.val at he
    rwa [he] at h
  let W (β : SimpleRoot Q) := transportSubgroup F (U (i.symm β).val).val
  have hW (β : SimpleRoot Q) : IsRootSubgroup Q.T (W β) β.val.val := by
    have h : HasScalarAction Q.T β.val.val ((p (i.symm β)).val.hom ≫ (W β).inclusion) := by
      simpa only [W, transportSubgroup, ← Category.assoc] using h₁ β
    exact ⟨(U (i.symm β).val).property.1, (U (i.symm β).val).property.2.1,
      normalizes_of_scalarAction Q.G.property.1 (p (i.symm β)).val h,
      tangent_weight_of_scalarAction Q.T (W β) β.val.val A (p (i.symm β)).val h⟩
  have sameRootSubgroup (β : SimpleRoot Q) : SameSubgroup (W β) (V β.val).val := by
    obtain ⟨_, _, _, _, _, hu⟩ :=
      ((RootData.RootGroups.rootSubgroups Q.G Q.reductive Q.T Q.split
        Q.maximal).2 β.val.val β.val.property).2.2
    obtain ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩ := hu _ (hW β)
    obtain ⟨⟨c, hc⟩, ⟨c', hc'⟩⟩ := hu _ (V β.val).property
    exact ⟨⟨a' ≫ c, by rw [Category.assoc, hc, ha']⟩,
      ⟨c' ≫ a, by rw [Category.assoc, ha, hc']⟩⟩
  let z (β : SimpleRoot Q) := subgroupIso (sameRootSubgroup β)
  have hz (β : SimpleRoot Q) :
      ((p (i.symm β)).val ≪≫ (z β).val).hom ≫ (V β.val).val.inclusion =
        x (i.symm β) ≫ F.hom := by
    rw [Iso.trans_hom, Category.assoc, (z β).property]
    exact (Category.assoc _ _ _).symm
  let q (β : SimpleRoot Q) : RootCoordinate A Q.T (V β.val).val β.val.val :=
    ⟨(p (i.symm β)).val ≪≫ (z β).val, (hz β).symm ▸ h₁ β⟩
  refine ⟨⟨P, U, p⟩, ⟨Q, V, q⟩, rfl, rfl, ⟨⟨F, t, b, ht, hb, ?_⟩⟩⟩
  ext v
  constructor
  · rintro ⟨_, ⟨α, rfl⟩, rfl⟩
    refine ⟨i α, Prod.ext rfl ?_⟩
    exact (hz (i α)).trans (by rw [i.symm_apply_apply])
  · rintro ⟨β, rfl⟩
    refine ⟨_, ⟨i.symm β, rfl⟩, Prod.ext ?_ (hz β).symm⟩
    exact congrArg (fun j : SimpleRoot Q => j.val.val) (i.apply_symm_apply β)

private theorem forgetClassification_forward (P Q : SplitBorelPair k)
    (D : AttachedDatum P) (E : AttachedDatum Q) (f : P.G.val ≅ Q.G.val) :
    Nonempty (D.toBased.datum.Equiv E.toBased.datum) := by
  obtain ⟨F, t, b, ht, hb⟩ := alignPairs P Q f
  obtain ⟨P', Q', hP, hQ, ⟨j⟩⟩ :=
    pinAlignedPairs P Q (standardAdditiveLine k) F t ht b hb
  subst P
  subst Q
  exact ⟨(inducedBasedIso j D E).val⟩

private theorem forgetClassification_reverse
    (P Q : SplitBorelPair k) (D : AttachedDatum P) (E : AttachedDatum Q)
    (e : D.toBased.datum.Equiv E.toBased.datum) : Nonempty (P.G.val ≅ Q.G.val) := by
  classical
  letI := D.comm
  letI := E.comm
  let d : Root P.T ≃ Root Q.T := e.indexEquiv
  let c : Character P.T.group ≃* Character Q.T.group :=
    e.weightEquiv.toAddEquiv.toMultiplicative
  have hlabel (i : Root P.T) : (d i).val = c i.val := by
    have h := e.toHom.root_weightMap_apply D.toBased.datum E.toBased.datum i
    change e.weightEquiv (D.datum.rootDatum.root i) = E.datum.rootDatum.root (d i) at h
    rw [D.datum.root_eq, E.datum.root_eq] at h
    exact congrArg Additive.toMul h.symm
  obtain ⟨_, _, _, hP, _, _, _⟩ :=
    RootData.BorelPositivity.borelPositivity P.G P.reductive P.T P.split P.maximal
  obtain ⟨_, _, _, hQ, _, _, _⟩ :=
    RootData.BorelPositivity.borelPositivity Q.G Q.reductive Q.T Q.split Q.maximal
  let S := d '' subgroupRoots P.T P.B
  have hS (i : Root P.T) : d i ∈ S ↔ i ∈ subgroupRoots P.T P.B :=
    ⟨fun ⟨j, hj, he⟩ => d.injective he ▸ hj, fun h => ⟨i, h, rfl⟩⟩
  obtain ⟨l, hreg, hsign⟩ := hP.1 P.B P.borel P.containsTorus
  let l' : Additive (Character Q.T.group) →ₗ[ℤ] ℝ := l.comp e.weightEquiv.symm.toLinearMap
  have heval (i : Root P.T) : l' (Additive.ofMul (d i).val) = l (Additive.ofMul i.val) := by
    rw [hlabel]
    exact congrArg l (e.weightEquiv.symm_apply_apply (Additive.ofMul i.val))
  have hpos : IsPositiveSystem Q.T S := by
    refine ⟨l', ?_, ?_⟩
    · intro j
      obtain ⟨i, rfl⟩ := d.surjective j
      exact (heval i).symm ▸ hreg i
    · ext j
      obtain ⟨i, rfl⟩ := d.surjective j
      change d i ∈ S ↔
        0 < l' (Additive.ofMul (d i).val)
      simp only [hS, heval, hsign, Set.mem_ofPred_eq]
  obtain ⟨B, hB, hTB, hBS⟩ := hQ.2.1 S hpos
  let Q' : SplitBorelPair k := { Q with B := B, borel := hB, containsTorus := hTB }
  have simple (i : Root P.T) : IsSimple P i ↔ IsSimple Q' (d i) :=
    simple_iff_of_roots (P := P) (Q := Q') d c hlabel (fun j => by
      change _ ↔ d j ∈ subgroupRoots Q.T B
      rw [hBS, hS]) i
  let base : E.datum.rootDatum.Base := D.base.map e
  have hbase : (base.support : Set (Root Q.T)) = d '' (D.base.support : Set (Root P.T)) := by
    rw [RootPairing.Base.support_map_eq, Finset.coe_image]
  let E' : AttachedDatum Q' := ⟨E.comm, E.datum, base, fun j => by
    obtain ⟨i, rfl⟩ := d.surjective j
    change d i ∈ base.support ↔ IsSimple Q' (d i)
    rw [← Finset.mem_coe, hbase]
    exact ⟨fun ⟨a, ha, eq⟩ => (simple i).mp ((D.simple_iff i).mp (d.injective eq ▸ ha)),
      fun h => ⟨i, (D.simple_iff i).mpr ((simple i).mpr h), rfl⟩⟩⟩
  let A := standardAdditiveLine k
  obtain ⟨U, ⟨p⟩⟩ := pinningsExist A P
  obtain ⟨V, ⟨q⟩⟩ := pinningsExist A Q'
  let P' : PinnedGroup A := ⟨P, U, p⟩
  let Q'' : PinnedGroup A := ⟨Q', V, q⟩
  obtain ⟨f, _⟩ := pinnedLift P' Q'' D E' ⟨e, hbase.symm⟩
  exact ⟨f.group⟩

private theorem reducedDatum_hasBase (D : ReducedRootDatum.{u}) :
    ∃ E : BasedRootDatum.{u}, forgetBase E = D := by
  classical
  letI := D.finiteRoots
  letI := D.freeX
  letI := D.finiteX
  letI := D.reduced
  obtain ⟨y, hy⟩ := exists_avoiding_zero_forms (fun i => D.datum.toLinearMap (D.datum.root i))
    (fun i => ⟨D.datum.coroot i, by
      simpa only [RootPairing.root_coroot_eq_pairing, RootPairing.pairing_same]
        using (show (2 : ℤ) ≠ 0 by decide)⟩)
  obtain ⟨b, _⟩ := RootData.SimpleRoots.baseFor D.datum (D.datum.toLinearMap.flip y) hy
  exact ⟨{
    I := D.I, X := D.X, Y := D.Y, addX := D.addX, addY := D.addY,
    finiteRoots := D.finiteRoots, freeX := D.freeX, freeY := D.freeY,
    finiteX := D.finiteX, finiteY := D.finiteY, datum := D.datum,
    reduced := D.reduced, base := b }, by cases D; rfl⟩

private theorem unpinnedClassification (realize : Specs.IntegralRealization.Statement.{u}) :
    UnpinnedClassification.{u} := by
  intro k _
  refine ⟨?_, ?_, ?_⟩
  · rintro G ⟨hG, T, hT, hm⟩
    obtain ⟨_, _, _, hCorr, hW, _, _⟩ := RootData.BorelPositivity.borelPositivity G hG T hT hm
    obtain ⟨S, hS⟩ := hW.1
    obtain ⟨B, hB, hTB, _⟩ := hCorr.2.1 S hS
    exact ⟨⟨G, hG, T, hT, hm, B, hB, hTB⟩, rfl⟩
  · intro P Q D E
    exact ⟨fun ⟨f⟩ => forgetClassification_forward P Q D E f,
      fun ⟨e⟩ => forgetClassification_reverse P Q D E e⟩
  · intro D
    obtain ⟨E, rfl⟩ := reducedDatum_hasBase D
    obtain ⟨P, D', ⟨e⟩⟩ := realizePinned realize E (standardAdditiveLine k)
    exact ⟨P.pair, D', ⟨e.val⟩⟩

/-- Pinned and unpinned classification, conditional on integral realization. -/
theorem pinnedEquivalence_conditional.{v} (realize : Specs.IntegralRealization.Statement.{v}) :
    Statement.{v} :=
  ⟨pinnedClassification realize, unpinnedClassification realize⟩

end

end LinearAlgebraicGroups.Classification.PinnedEquivalence

universe v8_closure_d34767e9c58b5f88_u0
theorem _root_.«LinearAlgebraicGroups».«Classification».«PinnedEquivalence».«pinnedEquivalence» : _root_.«LinearAlgebraicGroups».«Specs».«PinnedEquivalence».«Statement».{v8_closure_d34767e9c58b5f88_u0} :=
  @_root_.«LinearAlgebraicGroups».«Classification».«PinnedEquivalence».«pinnedEquivalence_conditional».{v8_closure_d34767e9c58b5f88_u0} (@_root_.«LinearAlgebraicGroups».«Classification».«IntegralRealization».«integralRealization».{v8_closure_d34767e9c58b5f88_u0})
