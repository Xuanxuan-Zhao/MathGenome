import Specs.LinearAlgebraicGroups.Arithmetic.SplitLocalGeneration
import LinearAlgebraicGroups.Classification.CentralIsogenies
import LinearAlgebraicGroups.Flag.BruhatCells
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.SplitLocalGeneration

open LinearAlgebraicGroups.Specs
open Specs.AbstractPairing (Datum Root)
open Specs.CharacterDescent (Cocharacter)
open Specs.DatumAndWeyl (Identification)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.OrderedRootProducts (RootSubgroupFamily)
open Specs.RootGroups (AdditiveLine IsRootSubgroup rankOneWord rootPoint)
open Specs.BruhatOrbitParametrization (IsRepresentative)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint multiplyFactors)

open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies
open private pointHom
  from LinearAlgebraicGroups.Flag.BruhatCells
open private coroot_reflection_is_representative
  opposite_root from LinearAlgebraicGroups.Flag.SimpleParabolicProduct
open private torusPointEquiv exists_coordinateCocharacter
  from LinearAlgebraicGroups.Reductive.ConnectedTorusCentralizer
open private unitEquiv unitEquiv_unitPoint from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

private abbrev R := CommAlgCat.of k k
private abbrev Y (k : Type u) [Field k] := (testSpec k).obj (op (CommAlgCat.of k k))

private def ContainsRootPoints (T : ClosedSubgroup G.val) (J : Subgroup (Y k ⟶ G.val.X)) :
    Prop :=
  ∀ (α : CharacterDescent.Character T.group), α ∈ CharacterPairing.absoluteRoots T →
    ∀ U : ClosedSubgroup G.val, IsRootSubgroup T U α →
      ∀ p : Y k ⟶ U.group.X, p ≫ U.inclusion.hom.hom ∈ J

private theorem lift_rationalPoint {X Z : SchemeOver k} (i : X ⟶ Z) [IsImmersion i.left]
    (g : Y k ⟶ Z) (hg : g.left (IsLocalRing.closedPoint k) ∈ Set.range i.left) :
    ∃ p : Y k ⟶ X, p ≫ i = g := by
  let S := Spec (CommRingCat.of k)
  let : Subsingleton S := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let : T1Space S := inferInstanceAs (T1Space (PrimeSpectrum k))
  let : IsReduced S := inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
  let f : pullback g.left i.left ⟶ S := pullback.fst g.left i.left
  let : IsImmersion f := IsImmersion.isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback g.left i.left).flip ‹IsImmersion i.left›
  have hf : (Set.range f).Subsingleton := Set.subsingleton_of_subsingleton
  let : IsClosedImmersion f := .of_isPreimmersion _ (Set.Subsingleton.isClosed hf)
  let : Surjective f := ⟨fun s ↦ by
    have hs : s = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    rw [hs]
    obtain ⟨y, hy⟩ := hg
    have he : g.left.base (IsLocalRing.closedPoint k) = i.left.base y := hy.symm
    obtain ⟨x, hx, _⟩ := Scheme.exists_preimage_of_isPullback
      (IsPullback.of_hasPullback g.left i.left) _ y he
    exact ⟨x, hx⟩⟩
  let : IsIso f := isIso_of_isClosedImmersion_of_surjective f
  let p := inv f ≫ pullback.snd g.left i.left
  have hp : p ≫ i.left = g.left := by
    calc
      p ≫ i.left = inv f ≫ (pullback.snd g.left i.left ≫ i.left) := Category.assoc ..
      _ = inv f ≫ f ≫ g.left := congrArg (inv f ≫ ·) pullback.condition.symm
      _ = g.left := IsIso.inv_hom_id_assoc f _
  exact ⟨Over.homMk p (by rw [← Over.w i, ← Category.assoc, hp, Over.w g]),
    Over.OverMorphism.ext hp⟩

private theorem rootProduct_mem {T : ClosedSubgroup G.val} {J : Subgroup (Y k ⟶ G.val.X)}
    (hJ : ContainsRootPoints T J) (U : RootSubgroupFamily T) (l : List (Root T))
    (p : Y k ⟶ OrderedRootProducts.product (fun α ↦ (U α).val.group.X) l) :
    p ≫ OrderedRootProducts.rootProduct U l ∈ J := by
  induction l with
  | nil =>
    simpa only [OrderedRootProducts.rootProduct, MonObj.comp_one] using J.one_mem
  | cons α l ih =>
    change p ≫ ((fst _ _ ≫ (U α).val.inclusion.hom.hom) *
      (snd _ _ ≫ OrderedRootProducts.rootProduct U l)) ∈ J
    rw [MonObj.comp_mul]
    simpa only [Category.assoc] using
      J.mul_mem (hJ α.val α.property (U α).val (U α).property (p ≫ fst _ _))
        (ih (p ≫ snd _ _))

private theorem attached_points {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {J : Subgroup (Y k ⟶ G.val.X)} (hJ : ContainsRootPoints T J)
    (D : Datum T) (I : Identification D) (α : Root T) :
    (∀ b : (R (k := k))ˣ,
      cocharacterPoint (Additive.toMul (D.rootDatum.coroot α)) _ b ≫ T.inclusion.hom.hom ∈ J) ∧
    ∃ n, IsRepresentative I (RootPairing.weylGroup.ofIdx D.rootDatum α) n ∧
      toUnit (Y k) ≫ n ≫ I.normalizer.inclusion.hom.hom ∈ J := by
  obtain ⟨C, c, _, _, Dpos, Dneg, _, Q, F, P, A, p, n, hp, hn, h⟩ := D.attached α
  dsimp only at h
  obtain ⟨_, _, r, hr⟩ := h
  let xpos := p.root.hom ≫ Dpos.contracting.inclusion ≫ C.subgroup.inclusion
  let xneg := n.root.hom ≫ Dneg.contracting.inclusion ≫ C.subgroup.inclusion
  have hpos (a : k) : rootPoint xpos (R (k := k)) a ∈ J := by
    exact hJ α.val α.property _ hp (rootPoint p.root.hom (R (k := k)) a)
  have hneg (a : k) : rootPoint xneg (R (k := k)) a ∈ J := by
    have hroot : α.val⁻¹ ∈ CharacterPairing.absoluteRoots T :=
      opposite_root D α ▸ (D.rootDatum.reflectionPerm α α).property
    exact hJ α.val⁻¹ hroot _ hn (rootPoint n.root.hom (R (k := k)) a)
  have hword (b : (R (k := k))ˣ) : rankOneWord xpos xneg (R (k := k)) b ∈ J :=
    J.mul_mem (J.mul_mem (hpos b) (hneg (-(↑b⁻¹ : k)))) (hpos b)
  refine ⟨fun b ↦ ?_, ?_⟩
  · rw [← hr, r.coroot_word]
    exact J.mul_mem (hword b) (J.inv_mem (hword 1))
  · obtain ⟨m, hm, he⟩ := coroot_reflection_is_representative I α r hr
    refine ⟨m, hm, ?_⟩
    rw [he]
    have hrep : toUnit (Y k) ≫ r.representative = rankOneWord xpos xneg (R (k := k)) 1 :=
      r.representative_word
    rw [hrep]
    exact hword 1


private def evaluateCocharacter {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    (b : (R (k := k))ˣ) : Cocharacter T.group →* (Y k ⟶ G.val.X) where
  toFun c := cocharacterPoint c _ b ≫ T.inclusion.hom.hom
  map_one' := by
    change pointHom T.inclusion (Y k)
      (CocharacterDynamics.unitPoint (R (k := k)) b ≫ (1 : _ ⟶ T.group.X)) = 1
    rw [MonObj.comp_one, map_one]
  map_mul' c d := by
    let p : Y k ⟶ _ := CocharacterDynamics.unitPoint (R (k := k)) b
    change pointHom T.inclusion (Y k) (p ≫ (c.hom.hom * d.hom.hom)) =
      pointHom T.inclusion (Y k) (p ≫ c.hom.hom) * pointHom T.inclusion (Y k) (p ≫ d.hom.hom)
    rw [MonObj.comp_mul, map_mul]

private theorem cocharacter_mem {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {J : Subgroup (Y k ⟶ G.val.X)} (D : Datum T)
    (hD : SimplyConnectedLattice.corootLatticeOf D = ⊤)
    (hcoroot : ∀ α (b : (R (k := k))ˣ),
      evaluateCocharacter b (Additive.toMul (D.rootDatum.coroot α)) ∈ J)
    (c : Cocharacter T.group) (b : (R (k := k))ˣ) : evaluateCocharacter b c ∈ J := by
  let L := (J.comap (evaluateCocharacter (T := T) b)).toAddSubgroup.toIntSubmodule
  have hle : SimplyConnectedLattice.corootLatticeOf D ≤ L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨α, rfl⟩
    exact hcoroot α b
  have hc : Additive.ofMul c ∈ SimplyConnectedLattice.corootLatticeOf D := hD ▸ Submodule.mem_top
  exact hle hc

private theorem torus_mem {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {J : Subgroup (Y k ⟶ G.val.X)} (hT : IsSplitTorus T.group)
    (hc : ∀ (c : Cocharacter T.group) (b : (R (k := k))ˣ), evaluateCocharacter b c ∈ J)
    (t : Y k ⟶ T.group.X) : t ≫ T.inclusion.hom.hom ∈ J := by
  classical
  obtain ⟨r, ⟨e⟩⟩ := hT
  let F := (StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin r))).val
  let E : (Y k ⟶ F.X) ≃* (ULift.{u} (Fin r) → (R (k := k))ˣ) :=
    torusPointEquiv (ULift.{u} (Fin r)) (R (k := k))
  let f := (pointHom (e.inv ≫ T.inclusion) (Y k)).comp E.symm.toMonoidHom
  let p := pointHom e.hom (Y k) t
  have hcoords (j : ULift.{u} (Fin r)) : Pi.mulSingle j (E p j) ∈ J.comap f := by
    obtain ⟨c, h⟩ := exists_coordinateCocharacter (k := k) j
    let b := E p j
    let q := (unitEquiv (R (k := k))).symm b
    have hq : q = CocharacterDynamics.unitPoint _ b :=
      (unitEquiv _).symm_apply_eq.mpr (unitEquiv_unitPoint _ _).symm
    have he : E ((q ≫ c.hom.hom) : Y k ⟶ F.X) = Pi.mulSingle j b :=
      (h (R (k := k)) q).trans (congrArg (Pi.mulSingle j) ((unitEquiv _).apply_symm_apply b))
    rw [← he]
    change f (E (q ≫ c.hom.hom)) ∈ J
    have hf := E.symm_apply_apply ((q ≫ c.hom.hom) : Y k ⟶ F.X)
    change pointHom (e.inv ≫ T.inclusion) (Y k) (E.symm (E (q ≫ c.hom.hom))) ∈ J
    rw [hf]
    change (q ≫ c.hom.hom) ≫ (e.inv ≫ T.inclusion).hom.hom ∈ J
    rw [hq]
    have hm := hc (c ≫ e.inv) b
    change (CocharacterDynamics.unitPoint (R (k := k)) b ≫ (c ≫ e.inv).hom.hom) ≫
      T.inclusion.hom.hom ∈ J at hm
    simpa only [Grp.comp_hom_hom, Category.assoc] using hm
  have hp : E p ∈ J.comap f := by
    rw [← Finset.univ_prod_mulSingle (E p)]
    exact (J.comap f).prod_mem (fun j _ ↦ hcoords j)
  change pointHom (e.inv ≫ T.inclusion) (Y k) (E.symm (E p)) ∈ J at hp
  rw [E.symm_apply_apply] at hp
  change (t ≫ e.hom.hom.hom) ≫ (e.inv ≫ T.inclusion).hom.hom ∈ J at hp
  have he : e.hom ≫ (e.inv ≫ T.inclusion) = T.inclusion := e.hom_inv_id_assoc _
  rw [Category.assoc, ← Grp.comp_hom_hom e.hom (e.inv ≫ T.inclusion), he] at hp
  exact hp

private theorem lifts_of_generators {M N P K H : Type*} [Group M] [Group N] [Group P] [Group H]
    (s : K → N) (hgen : Subgroup.closure (Set.range s) = ⊤)
    (J : Subgroup H) (i : M →* H) (f : M →* P) (g : N →* P)
    (hlift : ∀ a, ∃ m, f m = g (s a) ∧ i m ∈ J) :
    ∀ w, ∃ m, f m = g w ∧ i m ∈ J := by
  let L := J.comap i
  have hle : Subgroup.closure (Set.range s) ≤ (L.map f).comap g := by
    apply (Subgroup.closure_le _).2
    rintro _ ⟨a, rfl⟩
    obtain ⟨m, hf, hi⟩ := hlift a
    exact ⟨m, hi, hf⟩
  rw [hgen] at hle
  intro w
  obtain ⟨m, hi, hf⟩ := hle (Subgroup.mem_top w)
  exact ⟨m, hf, hi⟩

private def includeRationalPoint {N : GroupScheme k} (i : N ⟶ G.val) (Z : SchemeOver k) :
    (𝟙_ (SchemeOver k) ⟶ N.X) →* (Z ⟶ G.val.X) where
  toFun n := toUnit Z ≫ n ≫ i.hom.hom
  map_one' := by rw [MonObj.one_comp, MonObj.comp_one]
  map_mul' n m := by rw [MonObj.mul_comp, MonObj.comp_mul]

private theorem borel_mem {T B : ClosedSubgroup G.val} {J : Subgroup (Y k ⟶ G.val.X)}
    (hJ : ContainsRootPoints T J) (U : RootSubgroupFamily T) [Finite (Root T)]
    (hB : BorelPositivity.RadicalDecomposition T B)
    (ht : ∀ t : Y k ⟶ T.group.X, t ≫ T.inclusion.hom.hom ∈ J)
    (b : Y k ⟶ B.group.X) : b ≫ B.inclusion.hom.hom ∈ J := by
  classical
  obtain ⟨V, j, q, _, _, hj, _, _, hi, hprod⟩ := hB
  let := hi
  let m := multiplyFactors j V.inclusion
  let p := b ≫ inv m
  have hp : p ≫ m = b := by
    rw [show p = b ≫ inv m from rfl, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  let S := BorelsAndChambers.subgroupRoots T B
  let l := S.toFinite.toFinset.toList
  have hEnum : OrderedRootProducts.Enumerates l S := by
    refine ⟨Finset.nodup_toList _, ?_⟩
    intro i
    simp [l]
  obtain ⟨e, he⟩ := hprod U l hEnum
  let t := p ≫ fst T.group.X V.group.X
  let v := p ≫ snd T.group.X V.group.X
  have hV : v ≫ V.inclusion.hom.hom ≫ B.inclusion.hom.hom ∈ J := by
    have h := rootProduct_mem hJ U l (v ≫ e.inv)
    rwa [← he, Category.assoc, Iso.inv_hom_id_assoc] at h
  have hT : t ≫ j.hom.hom ≫ B.inclusion.hom.hom ∈ J := by
    rw [← Grp.comp_hom_hom j B.inclusion, hj]
    exact ht t
  have hmul : b = (t ≫ j.hom.hom) * (v ≫ V.inclusion.hom.hom) := by
    rw [← hp, show m = multiplyFactors j V.inclusion from rfl, multiplyFactors, MonObj.comp_mul]
    simp only [t, v, Category.assoc]
  change pointHom B.inclusion (Y k) b ∈ J
  rw [hmul, map_mul]
  apply J.mul_mem
  · change (t ≫ j.hom.hom) ≫ B.inclusion.hom.hom ∈ J
    rwa [Category.assoc]
  · change (v ≫ V.inclusion.hom.hom) ≫ B.inclusion.hom.hom ∈ J
    rwa [Category.assoc]

private theorem eq_top_of_bruhatCover {T B : ClosedSubgroup G.val}
    {Q : QuotientEmbedding.Presentation B} {a : ModObj G.val.X Q.scheme}
    {J : Subgroup (Y k ⟶ G.val.X)} {W : Type u}
    (n : W → (𝟙_ (SchemeOver k) ⟶ G.val.X))
    (A : W → ClosedSubgroup G.val)
    (C : ∀ w, BruhatOrbitParametrization.Cell (T := T) Q a (n w) (A w))
    (hcover : (⋃ w, Set.range (C w).doubleOrbitInclusion.left) = Set.univ)
    (hB : ∀ b : Y k ⟶ B.group.X, b ≫ B.inclusion.hom.hom ∈ J)
    (hn : ∀ w, toUnit (Y k) ≫ n w ∈ J) : J = ⊤ := by
  apply top_unique
  intro g _
  have hg : g.left (IsLocalRing.closedPoint k) ∈ ⋃ w, Set.range (C w).doubleOrbitInclusion.left :=
    hcover.symm ▸ Set.mem_univ _
  obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hg
  let := (C w).doubleOrbitImmersion
  obtain ⟨p, hp⟩ := lift_rationalPoint (C w).doubleOrbitInclusion g hw
  obtain ⟨b₁, b₂, h⟩ := ((C w).doubleOrbitSections (Y k) g).mp ⟨p, hp⟩
  rw [← h]
  exact J.mul_mem (J.mul_mem (hB b₁) (hn w)) (hB b₂)

/-- Root generation over the ground field, conditional on the simply connected lattice results. -/
theorem splitLocalGeneration_conditional
    (_adjointForm : SimplyConnectedLattice.AdjointForm.{u})
    (latticeCriterion : SimplyConnectedLattice.LatticeCriterion.{u})
    (_splitCover : SimplyConnectedLattice.SplitCover.{u}) : Specs.SplitLocalGeneration.Statement.{u} := by
  classical
  intro k _ G hG hsc T hs hm
  let J : Subgroup (Y k ⟶ G.val.X) := Subgroup.closure
    {g | ∃ α ∈ CharacterPairing.absoluteRoots T, ∃ U : ClosedSubgroup G.val, IsRootSubgroup T U α ∧
      ∃ p : Y k ⟶ U.group.X, p ≫ U.inclusion.hom.hom = g}
  change J = ⊤
  have hJ : ContainsRootPoints T J := fun α hα U hU p ↦
    Subgroup.subset_closure ⟨α, hα, U, hU, p, rfl⟩
  have hr := reductive_of_semisimple G hG
  obtain ⟨_, _, _, hBorel, hWeyl, _, hrad⟩ :=
    RootData.BorelPositivity.borelPositivity G hr T hs hm
  obtain ⟨S, hS⟩ := hWeyl.1
  obtain ⟨B, hB, hTB, _⟩ := hBorel.2.1 S hS
  obtain ⟨comm, D, I, U, _, _, _, _, b,
    _, _, _, _, _, _, _, hb, _, ⟨Q⟩, hcells⟩ :=
    Flag.BruhatCells.bruhatCells G hr T B hs hm hB hTB
  let := comm
  let := D.finiteRoots
  have hD := (latticeCriterion G hG T hs hm D).mp hsc
  have ha := attached_points hJ D I
  have ht := torus_mem hs (cocharacter_mem D hD (fun α ↦ (ha α).1))
  have hBmem := borel_mem hJ U (hrad B hB hTB) ht
  let s := I.image.constantGroup.sectionPoint.comp I.labelEquiv.toMonoidHom
  let r : b.support → D.rootDatum.weylGroup := fun α ↦ RootPairing.weylGroup.ofIdx D.rootDatum α.val
  have hrep := lifts_of_generators r hb.generates J (includeRationalPoint I.normalizer.inclusion (Y k))
    (pointHom I.quotient (𝟙_ (SchemeOver k))) s (fun α ↦ (ha α.val).2)
  let n := fun w ↦ Classical.choose (hrep w)
  have hn (w) : IsRepresentative I w (n w) := (Classical.choose_spec (hrep w)).1
  have hnJ (w) : toUnit (Y k) ≫ n w ≫ I.normalizer.inclusion.hom.hom ∈ J :=
    (Classical.choose_spec (hrep w)).2
  obtain ⟨a, _, hstrata⟩ := hcells Q
  obtain ⟨A, C, _, _, hcover, _⟩ := hstrata n hn
  exact eq_top_of_bruhatCover _ A C hcover hBmem hnJ

end

end LinearAlgebraicGroups.Arithmetic.SplitLocalGeneration

universe v8_closure_595ac6d9ccf48b2b_u0
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«SplitLocalGeneration».«splitLocalGeneration» : _root_.«LinearAlgebraicGroups».«Specs».«SplitLocalGeneration».«Statement».{v8_closure_595ac6d9ccf48b2b_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«SplitLocalGeneration».«splitLocalGeneration_conditional».{v8_closure_595ac6d9ccf48b2b_u0} (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«adjointForm».{v8_closure_595ac6d9ccf48b2b_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«latticeCriterion».{v8_closure_595ac6d9ccf48b2b_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«splitCover».{v8_closure_595ac6d9ccf48b2b_u0})
