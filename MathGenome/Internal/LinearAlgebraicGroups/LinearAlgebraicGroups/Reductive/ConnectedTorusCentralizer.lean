import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.ConnectedTorusCentralizer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterOpenCell
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj BigOperators

universe u

namespace LinearAlgebraicGroups.CocharacterDynamics

open LinearAlgebraicGroups.Specs (GroupScheme ClosedSubgroup AffineAlgebraicGroup)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open Specs.DiagonalizableGroups (IntegerCharacters groupAlgebra)
open LinearAlgebraicGroups.StandardGroups (multiplicativePowerGroupPointsIso)
open private centralizes_iff comp_conjugateFamily mono_over
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private overCoverObj overCoverMap from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.FixedPointSchemes
open private unitEquiv unitPointHom_apply subgroupInclusionFactors
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private group_geometricallyIrreducible from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterOpenCell

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

variable {k : Type u} [Field k] {G H : GroupScheme k}

private abbrev multiplicativeGroup (k : Type u) [Field k] : GroupScheme k :=
  specGroup (groupAlgebra k IntegerCharacters)

private abbrev onPoints {J L : GroupScheme k} (f : J ⟶ L) (R : TestAlgebra k) :=
  ((groupPointsFunctor k).map f).app R |>.hom

private theorem centralizes_iff_affine (i : H ⟶ G) {T : SchemeOver k} (g : T ⟶ G.X) :
    Centralizes i g ↔ ∀ (R : TestAlgebra k) (t : Points T R) (h : GroupPoints H R),
      Commute (t ≫ g) (onPoints i R h) := by
  refine ⟨fun hc R t h ↦ (centralizes_iff i g).mp hc _ t h, ?_⟩
  intro hc
  unfold Centralizes
  let X := H.X ⊗ T
  let A := X.left.affineOpenCover.openCover
  apply Over.OverMorphism.ext
  apply A.hom_ext
  intro j
  let U := overCoverObj (k := k) (T := X) A j
  let a := overCoverMap (k := k) (T := X) A j
  have hU : IsAffine U.left := inferInstanceAs (IsAffine (Spec (X.left.affineOpenCover.X j)))
  obtain ⟨B, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr hU
  let p := e.hom ≫ a
  have hp : p ≫ conjugateFamily i g = p ≫ fst H.X T ≫ i.hom.hom := by
    rw [comp_conjugateFamily]
    exact mul_inv_eq_iff_eq_mul.mpr (hc B.unop (p ≫ snd H.X T) (p ≫ fst H.X T)).eq
  have ha : a ≫ conjugateFamily i g = a ≫ fst H.X T ≫ i.hom.hom := by
    simpa only [p, Category.assoc, Iso.inv_hom_id_assoc] using congrArg (e.inv ≫ ·) hp
  exact congrArg (fun f ↦ f.left) ha

private abbrev torusPower (k : Type u) [Field k] (I : Type u) [Fintype I] :=
  (Specs.StandardGroups.multiplicativePowerGroup k I).val

private def torusPointEquiv (I : Type u) [Fintype I] [DecidableEq I] (R : TestAlgebra k) :
    GroupPoints (torusPower k I) R ≃* (I → Rˣ) :=
  ((multiplicativePowerGroupPointsIso k I).app R).groupIsoToMulEquiv

private theorem unitEquiv_naturality {R S : TestAlgebra k} (a : R ⟶ S)
    (p : GroupPoints (multiplicativeGroup k) R) :
    unitEquiv S (mapPoints a p) = Units.map a.hom.toMonoidHom (unitEquiv R p) := by
  obtain ⟨s, rfl⟩ := (unitEquiv R).symm.surjective p
  rw [(unitEquiv R).apply_symm_apply, show (unitEquiv R).symm s = unitPoint R s from
    unitPointHom_apply R s, mapPoints_unitPoint]
  rw [← unitPointHom_apply]
  exact (unitEquiv S).apply_symm_apply _

private theorem torusPointEquiv_naturality {I : Type u} [Fintype I] [DecidableEq I]
    {R S : TestAlgebra k} (a : R ⟶ S) (p : GroupPoints (torusPower k I) R) :
    torusPointEquiv I S (mapPoints a p) = fun j ↦
      Units.map a.hom.toMonoidHom (torusPointEquiv I R p j) := by
  exact DFunLike.congr_fun
    (congrArg GrpCat.Hom.hom ((multiplicativePowerGroupPointsIso k I).hom.naturality a)) p

private theorem exists_coordinateCocharacter {I : Type u} [Fintype I] [DecidableEq I] (j : I) :
    ∃ c : Cocharacter (torusPower k I), ∀ (R : TestAlgebra k)
      (p : GroupPoints (multiplicativeGroup k) R),
      torusPointEquiv I R (onPoints c R p) = Pi.mulSingle j (unitEquiv R p) := by
  let α : (groupPointsFunctor k).obj (multiplicativeGroup k) ⟶
      (groupPointsFunctor k).obj (torusPower k I) :=
    { app := fun R ↦ GrpCat.ofHom ((torusPointEquiv I R).symm.toMonoidHom.comp
        ((MonoidHom.mulSingle _ j).comp (unitEquiv R).toMonoidHom))
      naturality := by
        intro R S a
        apply GrpCat.ext
        intro p
        apply (torusPointEquiv I S).injective
        change (torusPointEquiv I S) ((torusPointEquiv I S).symm
          (Pi.mulSingle j (unitEquiv S (mapPoints a p)))) =
          torusPointEquiv I S (mapPoints a ((torusPointEquiv I R).symm
            (Pi.mulSingle j (unitEquiv R p))))
        rw [(torusPointEquiv I S).apply_symm_apply, unitEquiv_naturality, torusPointEquiv_naturality,
          (torusPointEquiv I R).apply_symm_apply]
        ext l
        by_cases e : l = j
        · subst l
          simp
        · simp [Pi.mulSingle_eq_of_ne e] }
  have ha : IsAffine (multiplicativeGroup k).X.left := inferInstanceAs
    (IsAffine (Spec (CommRingCat.of (MonoidAlgebra k IntegerCharacters))))
  obtain ⟨c, hc⟩ := (groupHomComparison k (multiplicativeGroup k) (torusPower k I) ha).2 α
  refine ⟨c, fun R p ↦ ?_⟩
  change (groupPointsFunctor k).map c = α at hc
  unfold onPoints
  rw [hc]
  exact (torusPointEquiv I R).apply_symm_apply _

/-- Centralizing the split power is equivalent to centralizing its coordinate factors. -/
private theorem centralizes_split_power {I : Type u} [Fintype I] [DecidableEq I]
    (i : torusPower k I ⟶ G) (c : I → Cocharacter (torusPower k I))
    (hc : ∀ j R p, torusPointEquiv I R (onPoints (c j) R p) = Pi.mulSingle j (unitEquiv R p))
    {T : SchemeOver k} (g : T ⟶ G.X) :
    Centralizes i g ↔ ∀ j, Centralizes (c j ≫ i) g := by
  constructor
  · intro h j
    rw [centralizes_iff_affine]
    intro R t p
    exact (centralizes_iff_affine i g).mp h R t (onPoints (c j) R p)
  · intro h
    rw [centralizes_iff_affine]
    intro R t p
    let f := (onPoints i R).comp (torusPointEquiv I R).symm.toMonoidHom
    let C := (Subgroup.centralizer {t ≫ g}).comap f
    have hmem : ∀ j, Pi.mulSingle j (torusPointEquiv I R p j) ∈ C := by
      intro j
      let s := (unitEquiv R).symm (torusPointEquiv I R p j)
      have he : Pi.mulSingle j (torusPointEquiv I R p j) =
          torusPointEquiv I R (onPoints (c j) R s) := by
        rw [hc, MulEquiv.apply_symm_apply]
      rw [he]
      change f (torusPointEquiv I R (onPoints (c j) R s)) ∈ Subgroup.centralizer {t ≫ g}
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have he' : a = t ≫ g := Set.mem_singleton_iff.mp ha
      subst a
      have hcomm := (centralizes_iff_affine (c j ≫ i) g).mp (h j) R t s
      simp only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      exact hcomm.eq
    have hp : torusPointEquiv I R p ∈ C := by
      rw [← Finset.univ_prod_mulSingle (torusPointEquiv I R p)]
      exact C.prod_mem fun j _ ↦ hmem j
    change f (torusPointEquiv I R p) ∈ Subgroup.centralizer {t ≫ g} at hp
    have he := (Subgroup.mem_centralizer_iff.mp hp) (t ≫ g) (Set.mem_singleton _)
    simp only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at he
    exact he

private theorem centralizes_precomp_iso {J : GroupScheme k} (e : J ≅ H) (i : H ⟶ G)
    {T : SchemeOver k} (g : T ⟶ G.X) : Centralizes (e.hom ≫ i) g ↔ Centralizes i g := by
  simp only [centralizes_iff_affine]
  refine ⟨fun h R t p ↦ ?_, fun h R t p ↦ h R t (onPoints e.hom R p)⟩
  have he : onPoints e.hom R (onPoints e.inv R p) = p := by
    change (p ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = p
    change p ≫ (e.inv ≫ e.hom).hom.hom = p
    simp
  have hp := h R t (onPoints e.inv R p)
  change Commute (t ≫ g) (onPoints i R (onPoints e.hom R (onPoints e.inv R p))) at hp
  simpa only [he] using hp

private theorem centralizes_through_subgroup (D : ClosedSubgroup G) (c : Cocharacter D.group)
    {T : SchemeOver k} (z : T ⟶ D.group.X) :
    Centralizes c z ↔ Centralizes (c ≫ D.inclusion) (z ≫ D.inclusion.hom.hom) := by
  simp only [centralizes_iff_affine]
  have : Mono D.inclusion.hom.hom := mono_over _ D.isClosedImmersion
  constructor
  · intro h R t p
    exact (h R t p).map (onPoints D.inclusion R)
  · intro h R t p
    have he := (h R t p).eq
    change onPoints D.inclusion R (t ≫ z) * onPoints D.inclusion R (onPoints c R p) =
      onPoints D.inclusion R (onPoints c R p) * onPoints D.inclusion R (t ≫ z) at he
    rw [← map_mul, ← map_mul] at he
    exact (cancel_mono D.inclusion.hom.hom).mp he

private def composeClosedSubgroups (D : ClosedSubgroup G) (E : ClosedSubgroup D.group) :
    ClosedSubgroup G :=
  ⟨E.group, E.inclusion ≫ D.inclusion,
    by
      let := E.isClosedImmersion
      let := D.isClosedImmersion
      exact IsClosedImmersion.comp E.inclusion.hom.hom.left D.inclusion.hom.hom.left⟩

/-- Centralize one cocharacter at a time. The other cocharacters factor through
each intermediate centralizer because their images commute. -/
private theorem represents_cocharacter_centralizers (G : AffineAlgebraicGroup k)
    [Smooth G.val.X.hom] [ConnectedSpace G.val.X.left] (cs : List (Cocharacter G.val))
    (hcomm : ∀ c ∈ cs, ∀ d ∈ cs, ∀ (R : TestAlgebra k)
      (p q : GroupPoints (multiplicativeGroup k) R),
      Commute (onPoints c R p) (onPoints d R q)) :
    ∃ C : ClosedSubgroup G.val,
      RepresentsSubgroup C (fun _ g ↦ ∀ c ∈ cs, Centralizes c g) ∧
      Smooth C.group.X.hom ∧ GeometricallyConnected C.group.X.hom := by
  generalize hn : cs.length = n
  induction n generalizing G cs with
  | zero =>
    have : cs = [] := List.length_eq_zero_iff.mp hn
    subst cs
    refine ⟨⟨G.val, 𝟙 _, by change IsClosedImmersion (𝟙 G.val.X.left); infer_instance⟩,
      fun T g ↦ ?_, inferInstance, ?_⟩
    · simp
    · let := group_geometricallyIrreducible G
      exact ⟨fun K _ z X fst snd pb ↦ by
        let := GeometricallyIrreducible.geometrically_irreducibleSpace z fst snd pb
        infer_instance⟩
  | succ n ih =>
    cases cs with
    | nil => simp at hn
    | cons c cs =>
      have hn' : cs.length = n := by simpa using hn
      obtain ⟨D⟩ := existsLimitDecomposition G c
      let Z := D.centralizer
      have hZ := D.centralizer_points
      let L := affineAlgebraicSubgroup Z G.property.1 G.property.2.1 G.property.2.2
      let : Smooth L.val.X.hom := (limitSubgroupsSmooth G c D).2.2
      let : GeometricallyConnected L.val.X.hom := (geometricallyConnectedLimitSubgroups G c D).2.2
      let : ConnectedSpace L.val.X.left :=
        GeometricallyConnected.connectedSpace_of_subsingleton L.val.X.hom
      have hlift (d : Cocharacter G.val) (hd : d ∈ cs) : ∃ b : Cocharacter L.val, b ≫ Z.inclusion = d := by
        have ha : IsAffine (multiplicativeGroup k).X.left := inferInstanceAs
          (IsAffine (Spec (CommRingCat.of (MonoidAlgebra k IntegerCharacters))))
        refine subgroupInclusionFactors ha Z d (fun R p ↦ (hZ _ _).mp ?_)
        change Centralizes c (p ≫ d.hom.hom)
        rw [centralizes_iff_affine]
        intro S t q
        rw [← Category.assoc]
        exact hcomm d (List.mem_cons_of_mem _ hd) c List.mem_cons_self S (t ≫ p) q
      classical
      let liftCochar (d : {d // d ∈ cs}) := (hlift d.val d.property).choose
      have hl (d : {d // d ∈ cs}) : liftCochar d ≫ Z.inclusion = d.val :=
        (hlift d.val d.property).choose_spec
      obtain ⟨E, hE, hEs, hEc⟩ := ih L (cs.attach.map liftCochar) (by
        intro a ha b hb R p q
        obtain ⟨d, _, rfl⟩ := List.mem_map.mp ha
        obtain ⟨e, _, rfl⟩ := List.mem_map.mp hb
        have : Mono Z.inclusion.hom.hom := mono_over _ Z.isClosedImmersion
        apply (cancel_mono Z.inclusion.hom.hom).mp
        change onPoints Z.inclusion R (onPoints (liftCochar d) R p * onPoints (liftCochar e) R q) =
          onPoints Z.inclusion R (onPoints (liftCochar e) R q * onPoints (liftCochar d) R p)
        simp only [map_mul]
        change onPoints (liftCochar d ≫ Z.inclusion) R p * onPoints (liftCochar e ≫ Z.inclusion) R q =
          onPoints (liftCochar e ≫ Z.inclusion) R q * onPoints (liftCochar d ≫ Z.inclusion) R p
        rw [hl, hl]
        exact (hcomm d.val (List.mem_cons_of_mem _ d.property)
          e.val (List.mem_cons_of_mem _ e.property) R p q).eq) (by simpa using hn')
      refine ⟨composeClosedSubgroups Z E, ?_, hEs, hEc⟩
      intro T g
      constructor
      · intro hg
        obtain ⟨z, hz⟩ := (hZ T g).mp (hg c List.mem_cons_self)
        obtain ⟨x, hx⟩ := (hE T z).mp (by
          intro b hb
          obtain ⟨d, _, rfl⟩ := List.mem_map.mp hb
          apply (centralizes_through_subgroup Z (liftCochar d) z).mpr
          rw [hl, hz]
          exact hg d.val (List.mem_cons_of_mem _ d.property))
        refine ⟨x, ?_⟩
        change x ≫ E.inclusion.hom.hom ≫ Z.inclusion.hom.hom = g
        rw [← Category.assoc, hx, hz]
      · rintro ⟨x, hx⟩ d hd
        let z := x ≫ E.inclusion.hom.hom
        have hz : z ≫ Z.inclusion.hom.hom = g := by
          simpa [z, composeClosedSubgroups, Category.assoc] using hx
        rcases List.mem_cons.mp hd with rfl | hd
        · exact (hZ T g).mpr ⟨z, hz⟩
        · let d' : {d // d ∈ cs} := ⟨d, hd⟩
          have hb : liftCochar d' ∈ cs.attach.map liftCochar :=
            List.mem_map.mpr ⟨d', List.mem_attach _ _, rfl⟩
          have he := (hE T z).mpr ⟨x, rfl⟩ (liftCochar d') hb
          have hc := (centralizes_through_subgroup Z (liftCochar d') z).mp he
          rwa [hl, hz] at hc

private theorem split_torus_centralizer (G : AffineAlgebraicGroup k) [Smooth G.val.X.hom]
    [ConnectedSpace G.val.X.left] {I : Type u} [Fintype I] (i : torusPower k I ⟶ G.val) :
    ∃ C : ClosedSubgroup G.val, RepresentsSubgroup C (fun _ g ↦ Centralizes i g) ∧
      Smooth C.group.X.hom ∧ GeometricallyConnected C.group.X.hom := by
  classical
  choose c hc using (fun j : I ↦ exists_coordinateCocharacter (k := k) j)
  let cs := (Finset.univ : Finset I).toList.map (fun j ↦ c j ≫ i)
  have hpair : ∀ a ∈ cs, ∀ b ∈ cs, ∀ (R : TestAlgebra k)
      (p q : GroupPoints (multiplicativeGroup k) R),
      Commute (onPoints a R p) (onPoints b R q) := by
    intro a ha b hb R p q
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨l, _, rfl⟩ := List.mem_map.mp hb
    have h : Commute (onPoints (c j) R p) (onPoints (c l) R q) := by
      apply (torusPointEquiv I R).injective
      rw [map_mul, map_mul, mul_comm]
    exact h.map (onPoints i R)
  obtain ⟨C, hC, hs, hg⟩ := represents_cocharacter_centralizers G cs hpair
  refine ⟨C, fun T g ↦ ?_, hs, hg⟩
  rw [← hC T g]
  change Centralizes i g ↔ ∀ a ∈ cs, Centralizes a g
  rw [centralizes_split_power i c hc]
  simp [cs]

private theorem iso_of_same_subgroup {P : ∀ T : SchemeOver k, (T ⟶ G.X) → Prop}
    (C D : ClosedSubgroup G) (hC : RepresentsSubgroup C P) (hD : RepresentsSubgroup D P) :
    Nonempty (C.group.X ≅ D.group.X) := by
  let f := C.inclusion.hom.hom
  let g := D.inclusion.hom.hom
  have : Mono f := mono_over _ C.isClosedImmersion
  have : Mono g := mono_over _ D.isClosedImmersion
  obtain ⟨a, ha⟩ := (hD _ f).mp ((hC _ f).mpr ⟨𝟙 _, by simp [f]⟩)
  obtain ⟨b, hb⟩ := (hC _ g).mp ((hD _ g).mpr ⟨𝟙 _, by simp [g]⟩)
  change a ≫ g = f at ha
  change b ≫ f = g at hb
  exact ⟨⟨a, b, (cancel_mono f).mp (by simp [Category.assoc, ha, hb]),
    (cancel_mono g).mp (by simp [Category.assoc, ha, hb])⟩⟩

private theorem fieldSpec_surjective {K L : Type u} [Field K] [Field L]
    (f : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of L)) : Surjective f :=
  ⟨fun x ↦ ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ x⟩⟩

private theorem geometricallyConnected_of_fieldExtension {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (K : Type u) [Field K] [Algebra k K]
    (h : GeometricallyConnected (pullback.snd f (fieldSpecMap k K))) :
    GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun M _ g ↦ ?_⟩
  let b := fieldSpecMap k K
  -- A residue field of the fibre product is a common extension of the two fields.
  let W := pullback b g
  obtain ⟨w, _, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := b) (g := g) (IsLocalRing.closedPoint K) (IsLocalRing.closedPoint M) (Subsingleton.elim _ _)
  let φ := W.fromSpecResidueField w ≫ pullback.fst b g
  let ψ := W.fromSpecResidueField w ≫ pullback.snd b g
  have eq : φ ≫ b = ψ ≫ g := by simp only [φ, ψ, Category.assoc, pullback.condition]
  let p := pullback.snd f b
  have hc : ConnectedSpace (pullback p φ : Scheme) :=
    pullback_of_geometrically h.geometrically_connectedSpace _ φ
  have outer : IsPullback (pullback.fst p φ ≫ pullback.fst f b) (pullback.snd p φ) f
      (ψ ≫ g) := by
    rw [← eq]
    exact (IsPullback.of_hasPullback p φ).paste_horiz (IsPullback.of_hasPullback f b)
  have inner := IsPullback.of_bot' outer.flip (IsPullback.of_hasPullback f g).flip
  have hs := MorphismProperty.of_isPullback inner (fieldSpec_surjective ψ)
  exact hs.surj.connectedSpace (Scheme.Hom.continuous _)

theorem connectedTorusCentralizer : Specs.CocharacterDynamics.ConnectedTorusCentralizer.{u} := by
  intro k _ G _ _ S hS
  obtain ⟨K, _, _, _, r, ⟨e⟩⟩ := hS
  obtain ⟨C, hC⟩ := centralizerScheme k G S
  let b := fieldSpecMap k K
  let G' := (groupBaseChange k K).obj G.val
  have pb := IsPullback.of_hasPullback G.val.X.hom b
  let Gₖ : AffineAlgebraicGroup K :=
    ⟨G', by
      let := G.property.1
      exact IsAffine.of_isPullback pb,
      MorphismProperty.of_isPullback pb G.property.2.1,
      MorphismProperty.of_isPullback pb G.property.2.2⟩
  let : Smooth Gₖ.val.X.hom := MorphismProperty.of_isPullback pb (inferInstance : Smooth G.val.X.hom)
  let : ConnectedSpace Gₖ.val.X.left := by
    have hg := group_geometricallyIrreducible G
    have : IrreducibleSpace Gₖ.val.X.left :=
      pullback_of_geometrically hg.geometrically_irreducibleSpace K b
    infer_instance
  let i := (groupBaseChange k K).map S.inclusion
  obtain ⟨D, hD, hDs, hDc⟩ := split_torus_centralizer Gₖ (e.inv ≫ i)
  have hD' : RepresentsSubgroup D (fun _ g ↦ Centralizes i g) :=
    fun T g ↦ (centralizes_precomp_iso e.symm i g).symm.trans (hD T g)
  obtain ⟨hm, hCₖ⟩ := centralizerSchemeBaseChange k K S.inclusion C hC
  let Cₖ := scalarExtendedSubgroup K C hm
  obtain ⟨j⟩ := iso_of_same_subgroup Cₖ D hCₖ hD'
  let j' := (Over.forget (Spec (CommRingCat.of K))).mapIso j
  have eq : j'.hom ≫ D.group.X.hom = Cₖ.group.X.hom := Over.w j.hom
  have hs : Smooth Cₖ.group.X.hom := by
    rw [← eq, MorphismProperty.cancel_left_of_respectsIso (P := @Smooth)]
    exact hDs
  have hc : GeometricallyConnected Cₖ.group.X.hom := by
    rw [← eq, MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyConnected)]
    exact hDc
  refine ⟨C, hC, ?_, geometricallyConnected_of_fieldExtension C.group.X.hom K hc⟩
  apply MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Smooth)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (g := b)
  · exact ⟨⟨fieldSpec_surjective b, inferInstance⟩, inferInstance⟩
  · exact hs

end
end LinearAlgebraicGroups.CocharacterDynamics
