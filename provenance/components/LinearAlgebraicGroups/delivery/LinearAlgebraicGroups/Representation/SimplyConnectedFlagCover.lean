import Specs.LinearAlgebraicGroups.Representation.SimplyConnectedFlagCover
import LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import LinearAlgebraicGroups.Flag.OpenCell
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Representation.SimplyConnectedFlagCover

open _root_.LinearAlgebraicGroups.Specs
open AbstractPairing (Datum Root)
open BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open CentralIsogenies (IsCentralIsogeny IsTorusRestriction characterPullback)
open CharacterDescent (Cocharacter)
open CharacterPairing (absoluteRoots pairing)
open CocharacterDynamics (LimitDecomposition multiplyFactors oppositeCocharacter)
open FlagLineBundle (OppositeBorelPair)
open IsogenyFlagComparison (Restrictions)
open LinearAlgebraicGroups.Specs.Pinning (AttachedDatum SplitBorelPair)
open OrderedRootProducts (Enumerates RootSubgroupFamily product rootProduct Parametrizes)
open RankOneFlag (SameSubgroup)
open SimplyConnectedLattice (corootLattice)

open private pairing_pushforward sameSubgroupIso
  from LinearAlgebraicGroups.Classification.CentralIsogenies
open private semisimple_iff_corootFullRank
  from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private oppositeCocharacter_eq_inv oppositePositiveRoots existsEnumeration
  from LinearAlgebraicGroups.Flag.OpenCell
open private tensor_property from LinearAlgebraicGroups.Classification.CellHomomorphism
open private isMonHom_of_comp_closed from LinearAlgebraicGroups.Affine.SchemeImageQuotient

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {k : Type u} [Field k]
variable {H G : AffineAlgebraicGroup k}

/-- Passing to the finite-index coroot lattice preserves a cocharacter's
chamber after multiplication by its positive index. -/
private theorem liftRegularCocharacter (P S : SplitBorelPair k)
    (D : AttachedDatum P) (E : AttachedDatum S) (hP : Specs.GeometricRadicals.IsSemisimple P.G)
    (τ : S.T.group ⟶ P.T.group)
    (e : letI := D.comm; letI := E.comm
      Additive (Cocharacter S.T.group) ≃ₗ[ℤ] corootLattice D)
    (he : ∀ c : Cocharacter S.T.group,
        (e (Additive.ofMul c)).val = Additive.ofMul (c ≫ τ))
    (c : Cocharacter P.T.group) :
    ∃ (c' : Cocharacter S.T.group) (n : ℕ), 0 < n ∧
      ∀ β, pairing S.T.group (characterPullback τ β) c' =
        (n : ℤ) * pairing P.T.group β c := by
  letI := D.comm
  letI := E.comm
  letI := D.datum.freeCocharacters
  letI := D.datum.finiteCocharacters
  let L := corootLattice D
  haveI : Finite (Additive (Cocharacter P.T.group) ⧸ L) :=
    (Submodule.finiteQuotient_iff L).mpr ((semisimple_iff_corootFullRank P D).mp hP)
  let n := L.toAddSubgroup.index
  have hn : 0 < n := Nat.card_pos (α := Additive (Cocharacter P.T.group) ⧸ L)
  have hx : n • Additive.ofMul c ∈ L :=
    AddSubgroup.nsmul_index_mem L.toAddSubgroup _
  let y : L := ⟨n • Additive.ofMul c, hx⟩
  let c' := (e.symm y).toMul
  refine ⟨c', n, hn, fun β => ?_⟩
  have hval : Additive.ofMul (c' ≫ τ) = n • Additive.ofMul c := by
    rw [← he c']
    exact congrArg Subtype.val (e.apply_symm_apply y)
  rw [← pairing_pushforward, ← D.datum.pairing_eq, ← D.datum.pairing_eq, hval,
    map_nsmul, nsmul_eq_mul]

private theorem rootProductComparison {T : ClosedSubgroup G.val} {S : ClosedSubgroup H.val}
    (U : RootSubgroupFamily T) (V : RootSubgroupFamily S)
    (d : Root T → Root S) (f : H.val ⟶ G.val)
    (h : ∀ β, ∃ e : (V (d β)).val.group ≅ (U β).val.group,
      e.hom ≫ (U β).val.inclusion = (V (d β)).val.inclusion ≫ f)
    (l : List (Root T)) :
    ∃ e : product (fun α => (V α).val.group.X) (l.map d) ≅
        product (fun β => (U β).val.group.X) l,
      rootProduct V (l.map d) ≫ f.hom.hom = e.hom ≫ rootProduct U l := by
  induction l with
  | nil =>
    refine ⟨Iso.refl _, ?_⟩
    change (1 : 𝟙_ (SchemeOver k) ⟶ H.val.X) ≫ f.hom.hom = (𝟙 _) ≫ 1
    rw [MonObj.one_comp, Category.id_comp]
  | cons β l ih =>
    obtain ⟨e, he⟩ := h β
    obtain ⟨q, hq⟩ := ih
    let a : (V (d β)).val.group.X ≅ (U β).val.group.X :=
      (Grp.forget (SchemeOver k)).mapIso e
    have hroot : a.hom ≫ (U β).val.inclusion.hom.hom =
        (V (d β)).val.inclusion.hom.hom ≫ f.hom.hom :=
      congrArg (fun p : (V (d β)).val.group ⟶ G.val => p.hom.hom) he
    refine ⟨tensorIso a q, ?_⟩
    change ((fst _ _ ≫ (V (d β)).val.inclusion.hom.hom) *
        (snd _ _ ≫ rootProduct V (l.map d))) ≫ f.hom.hom =
      (a.hom ⊗ₘ q.hom) ≫
        ((fst _ _ ≫ (U β).val.inclusion.hom.hom) * (snd _ _ ≫ rootProduct U l))
    simp only [MonObj.mul_comp, MonObj.comp_mul, Category.assoc, tensorHom_fst_assoc,
      tensorHom_snd_assoc, hroot, hq]

/-- The chart uses the actual torus and its ordered contracting root groups,
with the specified Borel embedded in the ambient group. -/
private theorem limitBorelChart {T B : ClosedSubgroup G.val} {c : Cocharacter T.group}
    (D : LimitDecomposition (c ≫ T.inclusion))
    (hT : SameSubgroup D.centralizer T) (hB : SameSubgroup D.parabolic B)
    (U : RootSubgroupFamily T) (l : List (Root T))
    (hu : Parametrizes U l D.contracting.inclusion.hom.hom) :
    ∃ a : T.group.X ⊗ product (fun β => (U β).val.group.X) l ≅ B.group.X,
      a.hom ≫ B.inclusion.hom.hom =
        (fst _ _ ≫ T.inclusion.hom.hom) * (snd _ _ ≫ rootProduct U l) := by
  obtain ⟨t, ht⟩ := sameSubgroupIso ⟨hT.2, hT.1⟩
  obtain ⟨b, hb⟩ := sameSubgroupIso hB
  obtain ⟨v, hv⟩ := hu
  let F := Grp.forget (SchemeOver k)
  haveI : IsIso (multiplyFactors D.sectionMap D.contractingToParabolic) := D.product_iso
  refine ⟨tensorIso (F.mapIso t) v ≪≫
      asIso (multiplyFactors D.sectionMap D.contractingToParabolic) ≪≫ F.mapIso b, ?_⟩
  have ht' := congrArg (fun p : T.group ⟶ G.val => p.hom.hom) ht
  have hb' := congrArg (fun p : D.parabolic.group ⟶ G.val => p.hom.hom) hb
  have hs := congrArg (fun p : D.centralizer.group ⟶ G.val => p.hom.hom) D.section_in_G
  have hu' := congrArg (fun p : D.contracting.group ⟶ G.val => p.hom.hom) D.contracting_in_G
  change (t.hom.hom.hom ⊗ₘ v.hom) ≫
      (multiplyFactors D.sectionMap D.contractingToParabolic ≫ b.hom.hom.hom) ≫
        B.inclusion.hom.hom = _
  simp only [Grp.comp_hom_hom] at ht' hb' hs hu'
  simp only [Category.assoc, hb', multiplyFactors, MonObj.comp_mul, MonObj.mul_comp,
    tensorHom_fst_assoc, tensorHom_snd_assoc, hs, hu', ht', hv]

private theorem surjectiveBorelRestriction
    {T B : ClosedSubgroup G.val} {S C : ClosedSubgroup H.val}
    (f : H.val ⟶ G.val) (τ : S.group ⟶ T.group) (hτ : IsTorusRestriction f τ)
    {X Y : SchemeOver k} (u : Y ⟶ H.val.X) (v : X ⟶ G.val.X)
    (e : Y ≅ X) (he : u ≫ f.hom.hom = e.hom ≫ v)
    (a : T.group.X ⊗ X ≅ B.group.X) (b : S.group.X ⊗ Y ≅ C.group.X)
    (ha : a.hom ≫ B.inclusion.hom.hom =
      (fst _ _ ≫ T.inclusion.hom.hom) * (snd _ _ ≫ v))
    (hb : b.hom ≫ C.inclusion.hom.hom =
      (fst _ _ ≫ S.inclusion.hom.hom) * (snd _ _ ≫ u)) :
    ∃ j : C.group ⟶ B.group, j ≫ B.inclusion = C.inclusion ≫ f ∧
      Surjective j.hom.hom.left := by
  let w := τ.hom.hom ⊗ₘ e.hom
  let j₀ := b.inv ≫ w ≫ a.hom
  have ht : S.inclusion.hom.hom ≫ f.hom.hom =
      τ.hom.hom ≫ T.inclusion.hom.hom :=
    congrArg (fun p : S.group ⟶ G.val => p.hom.hom) hτ.1.symm
  have hcomm : j₀ ≫ B.inclusion.hom.hom = (C.inclusion ≫ f).hom.hom := by
    apply (cancel_epi b.hom).mp
    simp only [j₀, Iso.hom_inv_id_assoc, Category.assoc, ha,
      Grp.comp_hom_hom, ← Category.assoc b.hom C.inclusion.hom.hom, hb,
      w, MonObj.comp_mul, MonObj.mul_comp, tensorHom_fst_assoc, tensorHom_snd_assoc,
      Category.assoc, ht, he]
  letI := B.isClosedImmersion
  haveI := isMonHom_of_comp_closed j₀ (C.inclusion ≫ f) B.inclusion hcomm
  let j : C.group ⟶ B.group := Grp.homMk j₀
  refine ⟨j, Grp.hom_ext _ _ hcomm, ?_⟩
  haveI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  haveI : IsIso a.hom.left := (Over.forget _).map_isIso a.hom
  haveI : IsIso b.inv.left := (Over.forget _).map_isIso b.inv
  haveI : Surjective w.left := tensor_property @Surjective τ.hom.hom e.hom hτ.2.2 inferInstance
  change Surjective (b.inv.left ≫ w.left ≫ a.hom.left)
  infer_instance

/-- The central cover carries an opposite pair matching the marked target
pair, even when its finite kernel is non-smooth. -/
theorem simplyConnectedFlagCover : Specs.SimplyConnectedFlagCover.Statement.{u} := by
  classical
  intro k _ _ G hG P
  let Q : SplitBorelPair k :=
    ⟨G, P.reductive, P.torus, P.split, P.maximal, P.negative, P.negativeBorel, P.inNegative⟩
  let D := Classification.Pinning.attachedDatum Q
  letI := D.comm
  obtain ⟨S, E, f, τ, hS, hSC, hf, hτ, _, e, he⟩ :=
    Classification.SimplyConnectedLattice.splitCover G hG P.torus P.split P.maximal D.datum
  letI := E.comm
  obtain ⟨c, Dc, hc, hsame, hnegative⟩ :=
    (RootData.BorelsAndChambers.borelsThroughT G P.reductive P.torus P.split P.maximal).1
      P.negative P.negativeBorel P.inNegative
  obtain ⟨c', n, hn, hpair⟩ := liftRegularCocharacter Q S D E hG τ e he c
  obtain ⟨hinj, _, hroots, hgroups⟩ :=
    Classification.CentralIsogenies.centralIsogenyComparison S.G G S.reductive P.reductive
      S.T P.torus S.split S.maximal P.split P.maximal f τ hf hτ.1 hτ.2.2
  let pullRoot (β : Root P.torus) : Root S.T := ⟨characterPullback τ β.val, hroots.1 β.prop⟩
  let d : Root P.torus ≃ Root S.T := Equiv.ofBijective pullRoot
    ⟨fun _ _ h => Subtype.ext (hinj (congrArg Subtype.val h)), by
      intro α
      obtain ⟨β, hb, heq⟩ := hroots.2.2 α.prop
      exact ⟨⟨β, hb⟩, Subtype.ext heq⟩⟩
  have hp (β : Root P.torus) :
      pairing S.T.group (d β).val c' = (n : ℤ) * pairing P.torus.group β.val c :=
    hpair β.val
  have hn' : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  have hc' : IsRegular S.T c' := by
    intro α
    obtain ⟨β, rfl⟩ := d.surjective α
    exact (hp β).symm ▸ mul_ne_zero hn'.ne' (hc β)
  have hcop : IsRegular S.T (oppositeCocharacter c') := by
    intro α
    rw [oppositeCocharacter_eq_inv, ← E.datum.pairing_eq]
    change E.datum.rootDatum.toLinearMap (Additive.ofMul α.val) (-(Additive.ofMul c')) ≠ 0
    rw [map_neg, neg_ne_zero, E.datum.pairing_eq]
    exact hc' α
  obtain ⟨hfin, ⟨U⟩, hprod⟩ :=
    RootData.OrderedRootProducts.contractingProduct G P.reductive P.torus P.split P.maximal
  obtain ⟨_, ⟨V⟩, hprod'⟩ :=
    RootData.OrderedRootProducts.contractingProduct S.G S.reductive S.T S.split S.maximal
  obtain ⟨Dn⟩ := (hprod' c').1
  obtain ⟨Dp⟩ := (hprod' (oppositeCocharacter c')).1
  obtain ⟨hct, _, _, _, _, _⟩ :=
    RootData.BorelsAndChambers.regularCocharacterBorel G P.reductive P.torus
      P.split P.maximal c hc Dc
  obtain ⟨hct', hBn, hTn, hRn, _, _⟩ :=
    RootData.BorelsAndChambers.regularCocharacterBorel S.G S.reductive S.T
      S.split S.maximal c' hc' Dn
  obtain ⟨_, hBp, hTp, hRp, _, _⟩ :=
    RootData.BorelsAndChambers.regularCocharacterBorel S.G S.reductive S.T
      S.split S.maximal (oppositeCocharacter c') hcop Dp
  have hcompl : subgroupRoots S.T Dp.parabolic = (subgroupRoots S.T Dn.parabolic)ᶜ := by
    rw [hRp, hRn, oppositePositiveRoots E.datum hc']
  let P' : OppositeBorelPair S.G :=
    ⟨S.T, Dp.parabolic, Dn.parabolic, S.reductive, S.split, S.maximal, hBp, hBn, hTp, hTn,
      by simp only [Specs.OpenCell.AreOpposite, hcompl, compl_compl]⟩
  have hsign (β : Root P.torus) :
      d β ∈ positiveRoots S.T c' ↔ β ∈ positiveRoots P.torus c := by
    change 0 < pairing S.T.group (d β).val c' ↔ 0 < pairing P.torus.group β.val c
    rw [hp]
    exact mul_pos_iff_of_pos_left hn'
  letI : Finite (Root P.torus) := hfin
  obtain ⟨l, hl⟩ := existsEnumeration (positiveRoots P.torus c)
  have hl' : Enumerates (l.map d) (positiveRoots S.T c') := by
    refine ⟨hl.1.map d.injective, ?_⟩
    intro α
    obtain ⟨β, rfl⟩ := d.surjective α
    rw [List.mem_map_of_injective d.injective, hl.2 β, hsign β]
  obtain ⟨a, ha⟩ := limitBorelChart Dc hct ⟨hsame.2, hsame.1⟩ U l
    ((hprod c).2 Dc U l hl)
  obtain ⟨b, hb⟩ := limitBorelChart Dn hct' ⟨⟨𝟙 _, by simp⟩, ⟨𝟙 _, by simp⟩⟩
    V (l.map d) ((hprod' c').2 Dn V (l.map d) hl')
  obtain ⟨q, hq⟩ := rootProductComparison U V d f (fun β =>
    (hgroups β.val β.prop (d β).prop).1 _ _ (V (d β)).prop (U β).prop) l
  obtain ⟨j, hj, hjs⟩ := surjectiveBorelRestriction f τ hτ _ _ q hq a b ha hb
  let r : Restrictions f P' P := ⟨τ, j, hτ.1, hj, hτ.2.2, hjs⟩
  refine ⟨S.G, P', f, hS, hSC, hf, r, fun β => (d β).prop, fun β hβ => ?_⟩
  change d β ∈ subgroupRoots S.T Dp.parabolic ↔ β ∈ subgroupRoots P.torus P.positive
  rw [hcompl, hRn]
  change (¬ d β ∈ positiveRoots S.T c') ↔ _
  rw [hsign, ← hnegative, P.opposite]
  simp

end

end LinearAlgebraicGroups.Representation.SimplyConnectedFlagCover
