import Specs.LinearAlgebraicGroups.Arithmetic.CentralCoverPinnedLift
import LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import LinearAlgebraicGroups.Classification.PinnedUniqueness
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.CentralCoverPinnedLift

open _root_.LinearAlgebraicGroups.Specs
open AbstractPairing (Root)
open AdjointRepresentation (GroupPoints)
open BorelsAndChambers (IsRegular subgroupRoots)
open CentralIsogenies (IsCentralIsogeny IsTorusRestriction characterPullback)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (pairing)
open Specs.GeometricRadicals (IsSemisimple IsSplitTorus)
open Pinning (AttachedDatum IsSimple PinnedGroup PinnedIso SimpleRoot SplitBorelPair)
open RankOneFlag (IsGeometricallyMaximal)
open RootGroups (AdditiveLine HasScalarAction rootPoint)
open SimplyConnectedLattice (corootLattice corootLatticeOf)

open private pushCocharacters splitBorelPair semisimple_iff_corootFullRank
  finiteMultiplicativeQuotient_iff restrictionCharacters_eq
  from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private reductive_of_semisimple pairing_pushforward
  from LinearAlgebraicGroups.Classification.CentralIsogenies

noncomputable section

variable {k : Type u} [Field k] {A : AdditiveLine k}

private theorem compareRoots (S P : SplitBorelPair k)
    (q : S.G.val ⟶ P.G.val) (qT : S.T.group ⟶ P.T.group)
    (hq : IsCentralIsogeny q) (hqT : IsTorusRestriction q qT) :
    ∃ d : Root S.T ≃ Root P.T, ∀ α, characterPullback qT (d α).val = α.val := by
  have h := (Classification.CentralIsogenies.centralIsogenyComparison S.G P.G
    S.reductive P.reductive S.T P.T S.split S.maximal P.split P.maximal
    q qT hq hqT.1 hqT.2.2).2.2.1
  let e : Root P.T ≃ Root S.T := h.equiv (characterPullback qT)
  refine ⟨e.symm, fun α => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply α)

private theorem coroot_pushforward {S P : SplitBorelPair k}
    (D : AttachedDatum S) (E : AttachedDatum P)
    (q : S.G.val ⟶ P.G.val) (qT : S.T.group ⟶ P.T.group)
    (hq : IsCentralIsogeny q) (hqT : IsTorusRestriction q qT)
    (d : Root S.T ≃ Root P.T) (hd : ∀ α, characterPullback qT (d α).val = α.val) :
    letI := D.comm
    letI := E.comm
    ∀ α, pushCocharacters qT (D.datum.rootDatum.coroot α) = E.datum.rootDatum.coroot (d α) := by
  let := D.comm
  let := E.comm
  have h := (Classification.CentralIsogenies.centralIsogenyComparison S.G P.G
    S.reductive P.reductive S.T P.T S.split S.maximal P.split P.maximal
    q qT hq hqT.1 hqT.2.2).2.2.2
  intro α
  have hr : (characterPullback qT (d α).val) ∈ CharacterPairing.absoluteRoots S.T :=
    hd α ▸ α.property
  have he : (⟨characterPullback qT (d α).val, hr⟩ : Root S.T) = α := Subtype.ext (hd α)
  exact congrArg Additive.ofMul ((h _ (d α).property hr).2 _ _
    (he.symm ▸ D.datum.attached α) (E.datum.attached (d α)))

private theorem map_corootLattice {S P : SplitBorelPair k}
    (D : AttachedDatum S) (E : AttachedDatum P)
    (q : S.G.val ⟶ P.G.val) (qT : S.T.group ⟶ P.T.group)
    (hq : IsCentralIsogeny q) (hqT : IsTorusRestriction q qT)
    (d : Root S.T ≃ Root P.T) (hd : ∀ α, characterPullback qT (d α).val = α.val) :
    letI := D.comm
    letI := E.comm
    (corootLattice D).map (pushCocharacters qT) = corootLattice E := by
  let := D.comm
  let := E.comm
  unfold corootLattice corootLatticeOf
  rw [Submodule.map_span]
  congr 1
  rw [← Set.range_comp]
  simp only [Function.comp_def, coroot_pushforward D E q qT hq hqT d hd]
  exact d.surjective.range_comp _

private theorem pushCocharacters_injective {S P : SplitBorelPair k}
    (D : AttachedDatum S) (E : AttachedDatum P)
    (q : S.G.val ⟶ P.G.val) (qT : S.T.group ⟶ P.T.group)
    (hq : IsCentralIsogeny q) (hqT : IsTorusRestriction q qT) :
    letI := D.comm
    letI := E.comm
    Function.Injective (pushCocharacters qT) := by
  let := D.comm
  let := E.comm
  have hfin := (Classification.CentralIsogenies.centralIsogenyComparison S.G P.G
    S.reductive P.reductive S.T P.T S.split S.maximal P.split P.maximal
    q qT hq hqT.1 hqT.2.2).2.1
  let h := (characterPullback qT).toAdditive.toIntLinearMap
  have hr : (characterPullback qT).range.toAddSubgroup.toIntSubmodule = LinearMap.range h := by
    ext x
    rfl
  have : Finite (Additive (Character S.T.group) ⧸ LinearMap.range h) := by
    rw [← hr]
    exact (finiteMultiplicativeQuotient_iff _).mp hfin
  let n := (LinearMap.range h).toAddSubgroup.index
  have hn : (n : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Additive (Character S.T.group) ⧸ LinearMap.range h)).ne'
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro y hy
  apply D.datum.rootDatum.toLinearMap.flip.toPerfPair.injective
  ext χ
  change D.datum.rootDatum.toLinearMap χ y = D.datum.rootDatum.toLinearMap χ 0
  rw [map_zero]
  obtain ⟨z, hz⟩ : n • χ ∈ LinearMap.range h :=
    AddSubgroup.nsmul_index_mem (LinearMap.range h).toAddSubgroup χ
  have hz' : D.datum.rootDatum.toLinearMap (h z) y = 0 := by
    change D.datum.rootDatum.toLinearMap (Additive.ofMul (characterPullback qT z.toMul))
      (Additive.ofMul y.toMul) = 0
    rw [D.datum.pairing_eq, ← pairing_pushforward,
      ← E.datum.pairing_eq]
    change E.datum.rootDatum.toLinearMap z (pushCocharacters qT y) = _
    rw [hy, map_zero]
  rw [hz, map_nsmul, LinearMap.coe_smul, Pi.smul_apply, nsmul_eq_mul] at hz'
  exact (mul_eq_zero.mp hz').resolve_left hn

private theorem compatibleBorel (S P : SplitBorelPair k) (hP : IsSemisimple P.G)
    (q : S.G.val ⟶ P.G.val) (qT : S.T.group ⟶ P.T.group)
    (hq : IsCentralIsogeny q) (hqT : IsTorusRestriction q qT)
    (d : Root S.T ≃ Root P.T) (hd : ∀ α, characterPullback qT (d α).val = α.val) :
    ∃ B : ClosedSubgroup S.G.val, GeometricBorelConjugacy.IsKBorel B ∧
      SchemeDerivedGroup.IsSubgroupOf S.T B ∧
      ∀ α, α ∈ subgroupRoots S.T B ↔ d α ∈ subgroupRoots P.T P.B := by
  let D := Classification.Pinning.attachedDatum S
  let E := Classification.Pinning.attachedDatum P
  let := D.comm
  let := E.comm
  let := E.datum.freeCocharacters
  let := E.datum.finiteCocharacters
  let g := pushCocharacters qT
  let C := corootLattice E
  have : Finite (Additive (Cocharacter P.T.group) ⧸ C) :=
    (Submodule.finiteQuotient_iff C).mpr ((semisimple_iff_corootFullRank P E).mp hP)
  obtain ⟨c, _, hc, _, hpos⟩ :=
    (RootData.BorelsAndChambers.borelsThroughT P.G P.reductive P.T P.split P.maximal).1
      P.B P.borel P.containsTorus
  -- A positive multiple of the target cocharacter lies in the source image.
  let n := C.toAddSubgroup.index
  have hn : 0 < (n : ℤ) := by
    exact_mod_cast (Nat.card_pos (α := Additive (Cocharacter P.T.group) ⧸ C))
  have hm : n • Additive.ofMul c ∈ C :=
    AddSubgroup.nsmul_index_mem C.toAddSubgroup _
  change n • Additive.ofMul c ∈ corootLattice E at hm
  rw [← map_corootLattice D E q qT hq hqT d hd] at hm
  obtain ⟨z, _, hz⟩ := hm
  let cS : Cocharacter S.T.group := z.toMul
  have hp (α : Root S.T) :
      pairing S.T.group α.val cS = (n : ℤ) * pairing P.T.group (d α).val c := by
    rw [← hd α, ← pairing_pushforward, ← E.datum.pairing_eq]
    change E.datum.rootDatum.toLinearMap (Additive.ofMul (d α).val) (g z) = _
    rw [hz, map_nsmul, nsmul_eq_mul, E.datum.pairing_eq]
  have hS : IsRegular S.T cS := fun α => by
    rw [hp]
    exact mul_ne_zero hn.ne' (hc (d α))
  obtain ⟨L⟩ := LinearAlgebraicGroups.CocharacterDynamics.existsLimitDecomposition S.G
    (cS ≫ S.T.inclusion)
  obtain ⟨_, hb, ht, hroots, _⟩ := RootData.BorelsAndChambers.regularCocharacterBorel
    S.G S.reductive S.T S.split S.maximal cS hS L
  refine ⟨L.parabolic, hb, ht, fun α => ?_⟩
  rw [hroots, hpos]
  change 0 < pairing S.T.group α.val cS ↔ 0 < pairing P.T.group (d α).val c
  rw [hp, mul_pos_iff_of_pos_left hn]

private theorem simple_iff_of_comparison {S P : SplitBorelPair k}
    (qT : S.T.group ⟶ P.T.group)
    (hi : Function.Injective (characterPullback qT))
    (d : Root S.T ≃ Root P.T) (hd : ∀ α, characterPullback qT (d α).val = α.val)
    (hpos : ∀ α, α ∈ subgroupRoots S.T S.B ↔ d α ∈ subgroupRoots P.T P.B)
    (α : Root S.T) : IsSimple S α ↔ IsSimple P (d α) := by
  constructor
  · rintro ⟨ha, hn⟩
    refine ⟨(hpos α).mp ha, ?_⟩
    intro β hb δ hg he
    obtain ⟨β', rfl⟩ := d.surjective β
    obtain ⟨δ', rfl⟩ := d.surjective δ
    apply hn β' ((hpos _).mpr hb) δ' ((hpos _).mpr hg)
    simpa only [map_mul, hd] using congrArg (characterPullback qT) he
  · rintro ⟨ha, hn⟩
    refine ⟨(hpos α).mpr ha, ?_⟩
    intro β hb δ hg he
    apply hn (d β) ((hpos _).mp hb) (d δ) ((hpos _).mp hg)
    apply hi
    simpa only [map_mul, hd] using he

open private characterValue_pullback from LinearAlgebraicGroups.Classification.CentralIsogenies
open private conjugateLe_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private rootPoint_comp hom_ext_on_affine_tests from LinearAlgebraicGroups.RootData.RootGroups

private abbrev pinMap (P : PinnedGroup A) (α : SimpleRoot P.pair) :
    A.group ⟶ P.pair.G.val :=
  (P.pin α).val.hom ≫ (P.roots α.val).val.inclusion

set_option backward.isDefEq.respectTransparency false in
private theorem pullbackRootCoordinate {S P : SplitBorelPair k}
    {q : S.G.val ⟶ P.G.val} {qT : S.T.group ⟶ P.T.group}
    (hqT : IsTorusRestriction q qT)
    {U : ClosedSubgroup S.G.val} {V : ClosedSubgroup P.G.val}
    {β : Character P.T.group} (hU : RootGroups.IsRootSubgroup S.T U (characterPullback qT β))
    (e : U.group ≅ V.group) (he : e.hom ≫ V.inclusion = U.inclusion ≫ q)
    (x : Pinning.RootCoordinate A P.T V β) :
    HasScalarAction S.T (characterPullback qT β) ((x.val ≪≫ e.symm).hom ≫ U.inclusion) := by
  intro R t a
  let i := U.inclusion
  let j := V.inclusion
  let xU := (x.val ≪≫ e.symm).hom
  let g : GroupPoints S.G.val R := t ≫ S.T.inclusion.hom.hom
  let s : GroupPoints P.T.group R := t ≫ qT.hom.hom
  let w : GroupPoints U.group R := rootPoint xU R a
  let a' := CharacterPairing.characterValue (characterPullback qT β) R t * a
  let w' : GroupPoints U.group R := rootPoint xU R a'
  have hnorm := ((LinearAlgebraicGroups.normalizesIff k i U.isClosedImmersion S.T.group.X
    S.T.inclusion.hom.hom).mp hU.2.2.1).1
  obtain ⟨z, hz⟩ := (conjugateLe_iff i S.T.inclusion.hom.hom).mp hnorm _ t w
  change g * rootPoint (xU ≫ i) R a * g⁻¹ = rootPoint (xU ≫ i) R a'
  rw [rootPoint_comp, rootPoint_comp]
  let wi : GroupPoints S.G.val R := w ≫ i.hom.hom
  change g * wi * g⁻¹ = w' ≫ i.hom.hom
  rw [← show z ≫ i.hom.hom = g * wi * g⁻¹ from hz]
  have : IsClosedImmersion j.hom.hom.left := V.isClosedImmersion
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have : IsIso e.hom.hom.hom := (Grp.forget (SchemeOver k)).map_isIso e.hom
  suffices h : z ≫ (e.hom ≫ j).hom.hom = w' ≫ (e.hom ≫ j).hom.hom by
    rw [Grp.comp_hom_hom] at h
    rw [(cancel_mono (e.hom.hom.hom ≫ j.hom.hom)).mp h]
  have htorus : g ≫ q.hom.hom = s ≫ P.T.inclusion.hom.hom := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f : S.T.group ⟶ P.G.val => t ≫ f.hom.hom) hqT.1.symm).trans
        (Category.assoc _ _ _).symm)
  have hxq : xU ≫ i ≫ q = x.val.hom ≫ j := by
    rw [← he]
    change (x.val.hom ≫ e.inv) ≫ e.hom ≫ j = _
    simp
  rw [he, Grp.comp_hom_hom, ← Category.assoc, hz, MonObj.mul_comp, MonObj.mul_comp,
    GrpObj.inv_comp, htorus]
  have hroot (b : R) : (rootPoint xU R b ≫ i.hom.hom) ≫ q.hom.hom =
      rootPoint (x.val.hom ≫ j) R b := by
    rw [← rootPoint_comp, ← rootPoint_comp]
    exact congrArg (fun f : A.group ⟶ P.G.val => rootPoint f R b)
      ((Category.assoc _ _ _).trans hxq)
  have hh : w' ≫ i.hom.hom ≫ q.hom.hom = rootPoint (x.val.hom ≫ j) R a' :=
    (Category.assoc _ _ _).symm.trans (hroot a')
  have ha' : a' = CharacterPairing.characterValue β R s * a :=
    congrArg (· * a) (characterValue_pullback qT β R t)
  rw [hroot a, hh, ha']
  exact x.property R s a

private theorem pinSource {S : SplitBorelPair k} (P : PinnedGroup A)
    (q : S.G.val ⟶ P.pair.G.val) (qT : S.T.group ⟶ P.pair.T.group)
    (hq : IsCentralIsogeny q) (hqT : IsTorusRestriction q qT)
    (d : Root S.T ≃ Root P.pair.T) (hd : ∀ α, characterPullback qT (d α).val = α.val)
    (hs : ∀ α, IsSimple S α ↔ IsSimple P.pair (d α)) :
    ∃ (U : OrderedRootProducts.RootSubgroupFamily S.T) (pin : Pinning.Pinning A S U),
      ∀ (α : SimpleRoot S) (β : SimpleRoot P.pair), d α.val = β.val →
        pinMap (⟨S, U, pin⟩ : PinnedGroup A) α ≫ q = pinMap P β := by
  classical
  have hU (α : Root S.T) :
      ∃ U : ClosedSubgroup S.G.val, RootGroups.IsRootSubgroup S.T U α.val := by
    obtain ⟨_, _, U, hr, _⟩ := (RootData.RootGroups.rootSubgroups S.G S.reductive
      S.T S.split S.maximal).2 α.val α.property
    exact ⟨U, hr⟩
  let U : OrderedRootProducts.RootSubgroupFamily S.T := fun α =>
    ⟨(hU α).choose, (hU α).choose_spec⟩
  have hroot := (Classification.CentralIsogenies.centralIsogenyComparison S.G P.pair.G
    S.reductive P.pair.reductive S.T P.pair.T S.split S.maximal P.pair.split P.pair.maximal
    q qT hq hqT.1 hqT.2.2).2.2.2
  have hIso (α : Root S.T) :
      ∃ e : (U α).val.group ≅ (P.roots (d α)).val.group,
        e.hom ≫ (P.roots (d α)).val.inclusion = (U α).val.inclusion ≫ q := by
    have hr : RootGroups.IsRootSubgroup S.T (U α).val (characterPullback qT (d α).val) :=
      Eq.mpr (congrArg (RootGroups.IsRootSubgroup S.T (U α).val) (hd α)) (U α).property
    exact (hroot _ (d α).property (hd α ▸ α.property)).1 _ _ hr (P.roots (d α)).property
  let e (α : Root S.T) := (hIso α).choose
  have he (α : Root S.T) := (hIso α).choose_spec
  let simple (α : SimpleRoot S) : SimpleRoot P.pair :=
    ⟨d α.val, (hs α.val).mp α.property⟩
  let pin : Pinning.Pinning A S U := fun α =>
    ⟨(P.pin (simple α)).val ≪≫ (e α.val).symm, by
      let β := (d α.val).val
      have hr : RootGroups.IsRootSubgroup S.T (U α.val).val (characterPullback qT β) :=
        Eq.mpr (congrArg (RootGroups.IsRootSubgroup S.T (U α.val).val) (hd α.val))
          (U α.val).property
      have h := pullbackRootCoordinate hqT hr (e α.val) (he α.val) (P.pin (simple α))
      exact Eq.mp (congrArg (fun χ => HasScalarAction S.T χ
        (((P.pin (simple α)).val ≪≫ (e α.val).symm).hom ≫ (U α.val).val.inclusion)) (hd α.val)) h⟩
  refine ⟨U, pin, fun α β hβ => ?_⟩
  have h : simple α = β := Subtype.ext hβ
  subst β
  change ((P.pin (simple α)).val.hom ≫ (e α.val).inv) ≫ (U α.val).val.inclusion ≫ q =
    (P.pin (simple α)).val.hom ≫ (P.roots (d α.val)).val.inclusion
  rw [← he α.val]
  simp

open private coweightEquiv coroot_transport rootEquiv rootEquiv_simple
  from LinearAlgebraicGroups.Classification.Pinning

private def sourceRootPermutation {S : SplitBorelPair k} {Q : PinnedGroup A}
    (d : Root S.T ≃ Root Q.pair.T) (b : PinnedIso Q Q) : Root S.T ≃ Root S.T :=
  d.trans ((rootEquiv b).trans d.symm)

private theorem sourceRootPermutation_simple {S : SplitBorelPair k} {P : PinnedGroup A}
    (d : Root S.T ≃ Root P.pair.T) (b : PinnedIso P P)
    (hs : ∀ α, IsSimple S α ↔ IsSimple P.pair (d α)) (α : Root S.T) :
    IsSimple S α ↔ IsSimple S (sourceRootPermutation d b α) := by
  have hd : d (sourceRootPermutation d b α) = rootEquiv b (d α) := d.apply_symm_apply _
  rw [hs α, hs (sourceRootPermutation d b α), hd]
  constructor
  · exact rootEquiv_simple b (d α)
  · intro h
    have h' := rootEquiv_simple b.symm _ h
    change IsSimple P.pair ((rootEquiv b).symm (rootEquiv b (d α))) at h'
    simpa only [Equiv.symm_apply_apply] using h'

private theorem characters_detect_hom {T U : GroupScheme k} (hU : IsSplitTorus U)
    {f g : T ⟶ U} (h : ∀ χ : Character U, f ≫ χ = g ≫ χ) : f = g := by
  apply Grp.hom_ext
  apply hom_ext_on_affine_tests
  intro R t
  apply Classification.PinnedUniqueness.charactersSeparatePoints hU
  intro χ
  simpa only [Grp.comp_hom_hom, Category.assoc] using
    congrArg (fun a : Character T => t ≫ a.hom.hom) (h χ)

private theorem liftOnPinnedSource (Q P : PinnedGroup A)
    (D : AttachedDatum Q.pair) (E : AttachedDatum P.pair)
    (hD : corootLattice D = ⊤)
    (q : Q.pair.G.val ⟶ P.pair.G.val) (qT : Q.pair.T.group ⟶ P.pair.T.group)
    (hq : IsCentralIsogeny q) (hqT : IsTorusRestriction q qT)
    (d : Root Q.pair.T ≃ Root P.pair.T) (hd : ∀ α, characterPullback qT (d α).val = α.val)
    (hs : ∀ α, IsSimple Q.pair α ↔ IsSimple P.pair (d α))
    (b : PinnedIso P P) :
    ∃ (τ : Q.pair.T.group ⟶ Q.pair.T.group) (f : Q.pair.G.val ⟶ Q.pair.G.val),
      IsIso f ∧ τ ≫ qT = qT ≫ b.torus.hom ∧
      RankTwoLifting.MatchesPinning (sourceRootPermutation d b) τ f := by
  classical
  let := D.comm
  let := E.comm
  let g := pushCocharacters qT
  let C := corootLattice E
  have hC : LinearMap.range g = C := by
    have h := map_corootLattice D E q qT hq hqT d hd
    rw [hD, Submodule.map_top] at h
    exact h
  let e : Additive (Cocharacter Q.pair.T.group) ≃ₗ[ℤ] C :=
    (LinearEquiv.ofInjective g (pushCocharacters_injective D E q qT hq hqT)).trans
      (LinearEquiv.ofEq _ _ hC)
  have he (y : Additive (Cocharacter Q.pair.T.group)) : (e y).val = g y := rfl
  let j := (coweightEquiv b E E).symm
  have hj (y : Additive (Cocharacter P.pair.T.group)) :
      j y = Additive.ofMul (y.toMul ≫ b.torus.hom) := rfl
  have hb (α : Root P.pair.T) :
      j (E.datum.rootDatum.coroot α) = E.datum.rootDatum.coroot (rootEquiv b α) :=
    (j.toEquiv.eq_symm_apply).mp (coroot_transport b E E α).symm
  have hmap : C.map j.toLinearMap = C := by
    change (Submodule.span ℤ (Set.range E.datum.rootDatum.coroot)).map j.toLinearMap = _
    rw [Submodule.map_span]
    change Submodule.span ℤ (j '' Set.range E.datum.rootDatum.coroot) =
      Submodule.span ℤ (Set.range E.datum.rootDatum.coroot)
    congr 1
    rw [← Set.range_comp]
    simp only [Function.comp_def, hb]
    exact (rootEquiv b).surjective.range_comp _
  -- Restrict to the coroot span and take the dual on characters.
  let m := (e.trans (j.ofSubmodules C C hmap)).trans e.symm
  have hm (y : Additive (Cocharacter Q.pair.T.group)) : g (m y) = j (g y) := by
    rw [← he, ← he]
    change (e (e.symm (j.ofSubmodules C C hmap (e y)))).val = _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.ofSubmodules_apply]
  let pp := D.datum.rootDatum.toLinearMap.toPerfPair
  let l := (pp.trans m.dualMap).trans pp.symm
  let h : Character Q.pair.T.group ≃* Character Q.pair.T.group :=
    l.toAddEquiv.toMultiplicative
  have hpair (χ : Character Q.pair.T.group) (y : Additive (Cocharacter Q.pair.T.group)) :
      pairing Q.pair.T.group (h χ) y.toMul = pairing Q.pair.T.group χ (m y).toMul := by
    rw [← D.datum.pairing_eq, ← D.datum.pairing_eq]
    change pp (l (Additive.ofMul χ)) y = pp (Additive.ofMul χ) (m y)
    change pp (pp.symm (m.dualMap (pp (Additive.ofMul χ)))) y = _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.dualMap_apply]
  have hcomm (χ : Character P.pair.T.group) :
      h (characterPullback qT χ) = characterPullback qT (b.torus.hom ≫ χ) := by
    apply Additive.ofMul.injective
    apply pp.injective
    ext y
    change D.datum.rootDatum.toLinearMap (Additive.ofMul (h (characterPullback qT χ))) y =
      D.datum.rootDatum.toLinearMap (Additive.ofMul (characterPullback qT (b.torus.hom ≫ χ))) y
    have hy : (m y).toMul ≫ qT = (y.toMul ≫ qT) ≫ b.torus.hom :=
      congrArg Additive.toMul ((hm y).trans (hj (g y)))
    calc
      _ = pairing Q.pair.T.group (h (characterPullback qT χ)) y.toMul :=
        D.datum.pairing_eq _ _
      _ = pairing Q.pair.T.group (characterPullback qT χ) (m y).toMul := hpair _ _
      _ = pairing P.pair.T.group χ ((m y).toMul ≫ qT) :=
        (pairing_pushforward qT χ _).symm
      _ = pairing P.pair.T.group (b.torus.hom ≫ χ) (y.toMul ≫ qT) := by
        rw [hy]
        exact pairing_pushforward b.torus.hom χ _
      _ = pairing Q.pair.T.group (characterPullback qT (b.torus.hom ≫ χ)) y.toMul :=
        pairing_pushforward qT _ _
      _ = _ := (D.datum.pairing_eq _ _).symm
  let p := sourceRootPermutation d b
  have hp (α : Root Q.pair.T) : d (p α) = rootEquiv b (d α) := d.apply_symm_apply _
  have hroot (α : Root Q.pair.T) : h (p α).val = α.val := by
    rw [← hd (p α), hcomm, hp]
    change characterPullback qT (b.torus.hom ≫ b.torus.inv ≫ (d α).val) = α.val
    rw [b.torus.hom_inv_id_assoc, hd]
  have hc (α : Root Q.pair.T) :
      m (D.datum.rootDatum.coroot α) = D.datum.rootDatum.coroot (p α) := by
    apply pushCocharacters_injective D E q qT hq hqT
    change g (m (D.datum.rootDatum.coroot α)) = g (D.datum.rootDatum.coroot (p α))
    rw [hm, coroot_pushforward D E q qT hq hqT d hd,
      coroot_pushforward D E q qT hq hqT d hd, hb, hp]
  have hcoroot (α : Root Q.pair.T) (χ : Character Q.pair.T.group) :
      pairing Q.pair.T.group (h χ) (D.datum.rootDatum.coroot α).toMul =
        pairing Q.pair.T.group χ (D.datum.rootDatum.coroot (p α)).toMul := by
    rw [hpair, hc]
  have hbase (α : Root Q.pair.T) : α ∈ D.base.support ↔ p α ∈ D.base.support :=
    (D.simple_iff _).trans ((sourceRootPermutation_simple d b hs α).trans (D.simple_iff _).symm)
  have hfin : Finite (Character Q.pair.T.group ⧸ h.toMonoidHom.range) := by
    rw [MonoidHom.range_eq_top.mpr h.surjective]
    let := QuotientGroup.subsingleton_quotient_top (G := Character Q.pair.T.group)
    infer_instance
  obtain ⟨τ, f, hτ, hpin, _, _, _, _, hiso, _⟩ :=
    Classification.OrdinaryCentralLifting.ordinaryCentralLifting Q Q D D p h.toMonoidHom
      h.injective hfin hroot hcoroot hbase
  rw [restrictionCharacters_eq] at hτ
  refine ⟨τ, f, hiso h.surjective, ?_, hpin⟩
  apply characters_detect_hom P.pair.split
  intro χ
  simp only [Category.assoc]
  exact (DFunLike.congr_fun hτ (characterPullback qT χ)).trans (hcomm χ)

open Specs.SchemeDerivedGroup (RepresentsQuotient)
open Specs.PinnedUniqueness (scalarGroupPoints)
open private quotient_desc from LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
open private fppfYoneda_locallySurjective quotientRepresentsImage schemeKernel_sections
  from LinearAlgebraicGroups.Affine.SchemeImageQuotient

private theorem pinnedMap_comp {P : PinnedGroup A} (b : PinnedIso P P)
    (α β : SimpleRoot P.pair) (h : rootEquiv b α.val = β.val) :
    pinMap P α ≫ b.group.hom = pinMap P β := by
  have hp : (Pinning.transportCharacter b.torus α.val.val,
      pinMap P α ≫ b.group.hom) ∈ Pinning.pinGraph P := by
    rw [← b.pin_comm]
    exact ⟨_, ⟨α, rfl⟩, rfl⟩
  obtain ⟨β', hβ'⟩ := hp
  have h' : β'.val = rootEquiv b α.val := Subtype.ext (congrArg Prod.fst hβ')
  have he : β' = β := Subtype.ext (h'.trans h)
  have hm : pinMap P β' = pinMap P α ≫ b.group.hom := congrArg Prod.snd hβ'
  exact hm.symm.trans (congrArg (pinMap P) he)

private theorem endomorphism_eq_id_of_pins {P : PinnedGroup A}
    (a : P.pair.G.val ⟶ P.pair.G.val) (hT : P.pair.T.inclusion ≫ a = P.pair.T.inclusion)
    (hP : ∀ α, pinMap P α ≫ a = pinMap P α) : a = 𝟙 _ := by
  let R := CommAlgCat.of k k
  let m : scalarGroupPoints R P.pair.G.val ⟶ scalarGroupPoints R P.pair.G.val :=
    Functor.whiskerLeft (Under.forget R) ((groupPointsFunctor k).map a)
  have hm := Classification.PinnedUniqueness.scalarRigidity P R m
    (fun S t => by
      change (t ≫ P.pair.T.inclusion.hom.hom) ≫ a.hom.hom = t ≫ P.pair.T.inclusion.hom.hom
      exact (Category.assoc _ _ _).trans
        (congrArg (fun f : P.pair.T.group ⟶ P.pair.G.val => t ≫ f.hom.hom) hT))
    (fun S α x => by
      change rootPoint (pinMap P α) S.right x ≫ a.hom.hom = rootPoint (pinMap P α) S.right x
      rw [← rootPoint_comp, hP])
  apply Grp.hom_ext
  apply hom_ext_on_affine_tests
  intro S p
  let z : Under R := Under.mk (CommAlgCat.ofHom (Algebra.ofId k S))
  exact DFunLike.congr_fun (congrArg GrpCat.Hom.hom (NatTrans.congr_app hm z)) p

private theorem cancel_faithfully_flat {G H J : GroupScheme k}
    {q : G ⟶ H} (hflat : Flat q.hom.hom.left) (hsurj : Surjective q.hom.hom.left)
    {f g : H ⟶ J} (h : q ≫ f = q ≫ g) : f = g := by
  let := hflat
  let := hsurj
  let : Epi q.hom.hom.left := Flat.epi_of_flat_of_surjective _
  let : Epi q.hom.hom := Over.epi_of_epi_left _
  apply Grp.hom_ext
  apply (cancel_epi q.hom.hom).mp
  exact (Grp.forget (SchemeOver k)).congr_map h

private theorem descendPinnedLift (Q P : PinnedGroup A)
    (q : Q.pair.G.val ⟶ P.pair.G.val) (qT : Q.pair.T.group ⟶ P.pair.T.group)
    (hq : IsCentralIsogeny q) (hqT : IsTorusRestriction q qT)
    (d : Root Q.pair.T ≃ Root P.pair.T)
    (hs : ∀ α, IsSimple Q.pair α ↔ IsSimple P.pair (d α))
    (hp : ∀ (α : SimpleRoot Q.pair) (β : SimpleRoot P.pair), d α.val = β.val →
      pinMap Q α ≫ q = pinMap P β)
    (b : PinnedIso P P) (τ : Q.pair.T.group ⟶ Q.pair.T.group)
    (f : Q.pair.G.val ⟶ Q.pair.G.val)
    (hτ : τ ≫ qT = qT ≫ b.torus.hom)
    (hf : RankTwoLifting.MatchesPinning (sourceRootPermutation d b) τ f) :
    f ≫ q = q ≫ b.group.hom := by
  let F := f ≫ q ≫ b.group.inv
  have hTF : Q.pair.T.inclusion ≫ F = qT ≫ P.pair.T.inclusion := by
    calc
      _ = (Q.pair.T.inclusion ≫ f) ≫ q ≫ b.group.inv := (Category.assoc _ _ _).symm
      _ = τ ≫ (Q.pair.T.inclusion ≫ q) ≫ b.group.inv := by
        rw [hf.1]
        simp only [Category.assoc]
      _ = (τ ≫ qT) ≫ P.pair.T.inclusion ≫ b.group.inv := by
        rw [← hqT.1]
        simp only [Category.assoc]
      _ = qT ≫ P.pair.T.inclusion := by
        rw [hτ]
        simp only [Category.assoc, ← reassoc_of% b.torus_comm, b.group.hom_inv_id, Category.comp_id]
  obtain ⟨hfinite, hflat, hsurj, N, hN, hbN⟩ := hq
  obtain ⟨i, hi⟩ := Classification.CentralIsogenies.kernel_le_maximalTorus
    RootData.SchemeCentre.schemeCentre Q.pair.G Q.pair.reductive Q.pair.T Q.pair.split
    Q.pair.maximal N hbN
  have hz : N.inclusion ≫ q = 0 := by
    apply Grp.hom_ext
    apply (schemeKernel_sections hN N.inclusion.hom.hom).mp
    change ∃ n : N.group.X ⟶ N.group.X, n ≫ N.inclusion.hom.hom = N.inclusion.hom.hom
    exact ⟨𝟙 _, Category.id_comp _⟩
  have hiq : i ≫ qT = 0 := by
    let : IsClosedImmersion P.pair.T.inclusion.hom.hom.left := P.pair.T.isClosedImmersion
    have hmono : Mono P.pair.T.inclusion.hom.hom := Over.mono_of_mono_left _
    let : Mono P.pair.T.inclusion :=
      (Grp.forget (SchemeOver k)).mono_of_mono_map (f := P.pair.T.inclusion) hmono
    apply (cancel_mono P.pair.T.inclusion).mp
    rw [Category.assoc, hqT.1, ← Category.assoc, hi, hz, zero_comp]
  -- The torus identity kills the full scheme kernel.
  have hk : N.inclusion ≫ F = 0 := by
    rw [← hi, Category.assoc, hTF, ← Category.assoc, hiq, zero_comp]
  let := hfinite
  let := hflat
  let := hsurj
  let := P.pair.G.property.2.1
  let := LocallyOfFiniteType.isLocallyNoetherian P.pair.G.val.X.hom
  have hrep : RepresentsQuotient N q :=
    quotientRepresentsImage (i := 𝟙 P.pair.G.val)
      ⟨Category.comp_id q, hflat, hsurj, inferInstance, inferInstance,
        inferInstanceAs (IsClosedImmersion (𝟙 P.pair.G.val.X.left))⟩ hN
  obtain ⟨a, ha, _⟩ := quotient_desc P.pair.G N q hrep
    (fppfYoneda_locallySurjective q.hom.hom) F (by
      intro X x hx
      change ∃ z : X ⟶ N.group.X, z ≫ N.inclusion.hom.hom = x at hx
      obtain ⟨z, rfl⟩ := hx
      change (z ≫ N.inclusion.hom.hom) ≫ F.hom.hom = 1
      rw [Category.assoc, ← Grp.comp_hom_hom, hk]
      exact MonObj.comp_one z)
  have haT : P.pair.T.inclusion ≫ a = P.pair.T.inclusion := by
    apply cancel_faithfully_flat hqT.2.1 hqT.2.2
    calc
      qT ≫ P.pair.T.inclusion ≫ a = Q.pair.T.inclusion ≫ q ≫ a := by
        rw [← Category.assoc, hqT.1, Category.assoc]
      _ = Q.pair.T.inclusion ≫ F := by rw [ha]
      _ = qT ≫ P.pair.T.inclusion := hTF
  have haP (β : SimpleRoot P.pair) : pinMap P β ≫ a = pinMap P β := by
    let α : SimpleRoot Q.pair :=
      ⟨d.symm β.val, (hs _).mpr (by simpa only [Equiv.apply_symm_apply] using β.property)⟩
    have hα : d α.val = β.val := d.apply_symm_apply _
    let p := sourceRootPermutation d b
    let α' : SimpleRoot Q.pair := ⟨p α.val, (sourceRootPermutation_simple d b hs _).mp α.property⟩
    let β' : SimpleRoot P.pair := ⟨d α'.val, (hs _).mp α'.property⟩
    have hβ' : rootEquiv b β.val = β'.val := by
      change rootEquiv b β.val = d (d.symm (rootEquiv b (d α.val)))
      rw [Equiv.apply_symm_apply, hα]
    calc
      pinMap P β ≫ a = pinMap Q α ≫ q ≫ a := by rw [← Category.assoc, hp α β hα]
      _ = pinMap Q α ≫ F := by rw [ha]
      _ = pinMap Q α' ≫ q ≫ b.group.inv := by
        dsimp only [F]
        rw [← Category.assoc, hf.2 α α' rfl]
      _ = pinMap P β' ≫ b.group.inv := by rw [← Category.assoc, hp α' β' rfl]
      _ = pinMap P β := by rw [← pinnedMap_comp b β β' hβ', Category.assoc,
          b.group.hom_inv_id, Category.comp_id]
  rw [endomorphism_eq_id_of_pins a haT haP, Category.comp_id] at ha
  calc
    f ≫ q = F ≫ b.group.hom := by simp [F]
    _ = q ≫ b.group.hom := by rw [← ha]

/-- Lift the pinned automorphism through the specified central isogeny. -/
theorem pinnedAutomorphismLifting :
    Specs.CentralCoverPinnedLift.PinnedAutomorphismLifting.{u} := by
  intro k _ A H P hH hP hsc T hsplit hmax q qT hq hqT b
  let S₀ := splitBorelPair H (reductive_of_semisimple H hH) T hsplit hmax
  obtain ⟨d, hd⟩ := compareRoots S₀ P.pair q qT hq hqT
  obtain ⟨B, hB, hTB, hpos⟩ := compatibleBorel S₀ P.pair hP q qT hq hqT d hd
  let S : SplitBorelPair k := { S₀ with B := B, borel := hB, containsTorus := hTB }
  have hs (α : Root S.T) : IsSimple S α ↔ IsSimple P.pair (d α) :=
    simple_iff_of_comparison (S := S) qT
      (Classification.CentralIsogenies.characterPullback_injective qT hqT.2.1 hqT.2.2) d hd hpos α
  obtain ⟨U, pin, hpin⟩ := pinSource (S := S) P q qT hq hqT d hd hs
  let Q : PinnedGroup A := ⟨S, U, pin⟩
  let D := Classification.Pinning.attachedDatum Q.pair
  let E := Classification.Pinning.attachedDatum P.pair
  let : IsCommMonObj T.group.X := D.comm
  have hD : corootLattice D = ⊤ :=
    (Classification.SimplyConnectedLattice.latticeCriterion H hH T hsplit hmax D.datum).mp hsc
  let BAut : PinnedIso P P := b.asIso.hom
  obtain ⟨τ, f, hiso, hτ, hf⟩ := liftOnPinnedSource Q P D E hD q qT hq hqT d hd hs BAut
  let c : Aut Q.pair.G.val := Aut.of (@asIso _ _ _ _ f hiso)
  refine ⟨c, ?_⟩
  exact descendPinnedLift Q P q qT hq hqT d hs hpin BAut τ f hτ hf

end

end LinearAlgebraicGroups.Arithmetic.CentralCoverPinnedLift
