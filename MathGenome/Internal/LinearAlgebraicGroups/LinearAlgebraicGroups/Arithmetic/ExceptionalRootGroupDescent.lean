import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalRootGroupDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.SplitContractingRadical
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RelativeReflections
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.TensorProduct.MvPolynomial

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Matrix

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalRootGroupDescent

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup GroupScheme)
open Specs.AbstractPairing (Root)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character Cocharacter compositionPairing)
open Specs.CharacterPairing (absoluteRoots characterValue pairing)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Specs.ExceptionalRootGroupDescent
open Specs.GeometricRadicals (IsReductive IsSplitTorus baseChangedSubgroup)
open Specs.Relative.RelativeChambers (relativeRoots)
open Specs.RootGroups (AdditiveLine HasScalarAction IsRootSubgroup rootPoint)
open Specs.Relative.RelativeReflections (RootCentralizer)
open private precomposeCharacter powerMorphism_eq_zpow
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RelativeReflections
open private rootsOfIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private baseChange_map_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private inclusion_mono from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate

noncomputable section

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F}

local notation "Fsep" => SeparableClosure F
local notation "Gm[" K "]" => specGroup (groupAlgebra K IntegerCharacters)

private abbrev MultiplicativeComparison (F : Type u) [Field F] :=
  Gm[SeparableClosure F] ≅ (groupBaseChange F (SeparableClosure F)).obj Gm[F]

private def PreservesUnits (e : MultiplicativeComparison F) : Prop :=
  ∀ (R : TestAlgebra Fsep) (t : Rˣ),
    baseChangePoint F Fsep Gm[F].X R (CocharacterDynamics.unitPoint R t ≫ e.hom.hom.hom) =
      CocharacterDynamics.unitPoint ((restrictTestAlgebra F Fsep).obj R) t

private def extendCharacter (e : MultiplicativeComparison F) (T : GroupScheme F) :
    Character T →* Character ((groupBaseChange F Fsep).obj T) where
  toFun a := (groupBaseChange F Fsep).map a ≫ e.inv
  map_one' := by
    apply Grp.hom_ext
    change (baseChange F Fsep).map (1 : T.X ⟶ Gm[F].X) ≫ e.inv.hom.hom = 1
    rw [(baseChange F Fsep).map_one]
    exact (IsMonHom.monoidHom e.inv.hom.hom _).map_one
  map_mul' a b := by
    apply Grp.hom_ext
    change (baseChange F Fsep).map (a.hom.hom * b.hom.hom) ≫ e.inv.hom.hom =
      ((baseChange F Fsep).map a.hom.hom ≫ e.inv.hom.hom) * ((baseChange F Fsep).map b.hom.hom ≫ e.inv.hom.hom)
    rw [(baseChange F Fsep).map_mul]
    exact (IsMonHom.monoidHom e.inv.hom.hom _).map_mul _ _

private theorem extendCharacter_injective (e : MultiplicativeComparison F) (T : GroupScheme F) :
    Function.Injective (extendCharacter e T) := by
  intro a b hab
  change (groupBaseChange F Fsep).map a ≫ e.inv = (groupBaseChange F Fsep).map b ≫ e.inv at hab
  exact Grp.hom_ext _ _ (baseChange_map_injective Fsep
    ((Grp.forget _).congr_map ((cancel_mono e.inv).mp hab)))

private abbrev extendCocharacter (e : MultiplicativeComparison F) {T : GroupScheme F}
    (c : Cocharacter T) : Cocharacter ((groupBaseChange F Fsep).obj T) :=
  e.hom ≫ (groupBaseChange F Fsep).map c

/-- The pairing of an extended character with an extended cocharacter retains
the same integer exponent. -/
private theorem pairing_extend (e : MultiplicativeComparison F) {T : GroupScheme F}
    (a : Character T) (c : Cocharacter T) :
    pairing ((groupBaseChange F Fsep).obj T) (extendCharacter e T a) (extendCocharacter e c) =
      pairing T a c := by
  let E := groupBaseChange F Fsep
  let n := pairing T a c
  have h : c ≫ a = (𝟙 Gm[F] : Character Gm[F]) ^ n := by
    rw [← powerMorphism_eq_zpow]
    exact ((RootData.CharacterPairing.characterPairingComposition T a c).1 n).2 rfl
  apply ((RootData.CharacterPairing.characterPairingComposition _ _ _).1 n).1
  rw [powerMorphism_eq_zpow]
  change (e.hom ≫ E.map c) ≫ E.map a ≫ e.inv = _
  rw [Category.assoc, ← Category.assoc (E.map c), ← E.map_comp, h]
  change precomposeCharacter e.hom (extendCharacter e Gm[F]
    ((𝟙 Gm[F] : Character Gm[F]) ^ n)) = _
  rw [map_zpow, map_zpow]
  change (e.hom ≫ E.map (𝟙 Gm[F]) ≫ e.inv) ^ n = _
  rw [E.map_id, Category.id_comp, e.hom_inv_id]

/-- The geometric restriction of the marked root is the extension of an
actual relative root, with the comparison of split multiplicative groups
inducing the identity on units of each test algebra. -/
private theorem relativeRootOfRestriction (A : MarkedTori G) (α : Root A.P.T)
    (hne : A.restrict α.val ≠ 1) :
    ∃ (e : MultiplicativeComparison F) (a : relativeRoots A.S),
      PreservesUnits e ∧
      (extendCharacter e A.S.group) '' relativeRoots A.S =
        {χ | χ ≠ 1 ∧ ∃ β : Root A.P.T, A.restrict β.val = χ} ∧
      extendCharacter e A.S.group a.val = A.restrict α.val := by
  let E := groupBaseChange F Fsep
  have hT : IsClosedImmersion (E.map A.T.inclusion).hom.hom.left := by
    letI := A.P.T.isClosedImmersion
    haveI : IsIso A.torus.hom.hom.hom.left :=
      (Grp.forget _ ⋙ Over.forget _).map_isIso A.torus.hom
    haveI : IsIso A.ambient.hom.hom.hom.left :=
      (Grp.forget _ ⋙ Over.forget _).map_isIso A.ambient.hom
    rw [← A.torus_eq]
    change IsClosedImmersion (A.torus.hom.hom.hom.left ≫
      A.P.T.inclusion.hom.hom.left ≫ A.ambient.hom.hom.hom.left)
    infer_instance
  let T' := baseChangedSubgroup Fsep A.T hT
  have hs : IsSplitTorus (E.obj A.T.group) := by
    obtain ⟨r, ⟨i⟩⟩ := A.P.split
    exact ⟨r, ⟨A.torus ≪≫ i⟩⟩
  obtain ⟨e, he, _, hr⟩ := Relative.RelativeChambers.relativeRootsByRestriction
    G A.S A.T A.intoTorus A.intoTorus_eq A.maximalSplit.1 hT hs
  have hsq : T'.inclusion ≫ A.ambient.inv = A.torus.hom ≫ A.P.T.inclusion := by
    change E.map A.T.inclusion ≫ A.ambient.inv = _
    rw [← A.torus_eq, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hRoots : (extendCharacter e A.S.group) '' relativeRoots A.S =
      {χ | χ ≠ 1 ∧ ∃ β : Root A.P.T, A.restrict β.val = χ} := by
    rw [show (extendCharacter e A.S.group) '' relativeRoots A.S = _ from hr]
    ext χ
    constructor
    · rintro ⟨⟨b, hb, rfl⟩, hn⟩
      have hβ : A.torus.inv ≫ b ∈ absoluteRoots A.P.T := by
        apply (rootsOfIso A.ambient.symm (T := T') (S := A.P.T) A.torus hsq _).mp
        simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hb
      exact ⟨hn, ⟨⟨_, hβ⟩, by simp [MarkedTori.restrict, MarkedTori.splitInAbsolute]⟩⟩
    · rintro ⟨hn, β, rfl⟩
      refine ⟨⟨A.torus.hom ≫ β.val, ?_, (Category.assoc _ _ _).symm⟩, hn⟩
      exact (rootsOfIso A.ambient.symm (T := T') (S := A.P.T) A.torus hsq _).mpr β.property
  obtain ⟨a, ha, hEq⟩ := (Set.ext_iff.mp hRoots _).mpr ⟨hne, α, rfl⟩
  exact ⟨e, ⟨a, ha⟩, he, hRoots, hEq⟩


section ContractingRootProduct

open scoped TensorProduct
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.OrderedRootProducts (Enumerates RootSubgroupFamily rootProduct)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.BorelsAndChambers (positiveRoots)
open CocharacterDynamics (HasLimit LimitDecomposition)
open private RootCoordinate RootCoordinate.iso RootCoordinate.scalar
  rootCoordinate_exists productPoint productPoint_surjective
  productPoint_mul productPoint_map productPoint_eq_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private characterValue_natural characterValue_composition onPoints_mapPoints
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.ReductiveLieCentralizers
open private trivial_character_of_values from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RelativeReflections
open private centralizes_iff_affine from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.ConnectedTorusCentralizer
open private rootPoint_zero from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups

variable {k : Type u} [Field k]

/-- A scalar fixed by a nontrivial affine group character, over all scalar
extensions of the test algebra, vanishes. -/
private theorem fixedScalar_eq_zero {J : GroupScheme k} (hJ : IsAffine J.X.left)
    {χ : Character J} (hχ : χ ≠ 1) (R : TestAlgebra k) (r : R)
    (h : ∀ (S : TestAlgebra k) (f : R ⟶ S) (p : GroupPoints J S),
      characterValue χ S p * f.hom r = f.hom r) : r = 0 := by
  classical
  by_contra hn
  have hc : ∃ (B : TestAlgebra k) (p : GroupPoints J B), characterValue χ B p ≠ 1 := by
    by_contra! ht
    exact hχ (trivial_character_of_values hJ χ ht)
  obtain ⟨B, p, hp⟩ := hc
  let S := CommAlgCat.of k (R ⊗[k] B)
  let i : R ⟶ S := CommAlgCat.ofHom (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] B)
  let j : B ⟶ S := CommAlgCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[k] R ⊗[k] B)
  have he := h S i (mapPoints j p)
  rw [characterValue_natural χ j p] at he
  change (1 ⊗ₜ[k] characterValue χ B p) * (r ⊗ₜ[k] (1 : B)) = r ⊗ₜ[k] (1 : B) at he
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one] at he
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one k hn
  have hlin := congrArg (TensorProduct.map l (LinearMap.id : B →ₗ[k] B)) he
  have hs := congrArg (TensorProduct.lid k B) hlin
  exact hp (by simpa only [TensorProduct.map_tmul, LinearMap.id_apply, hl,
    TensorProduct.lid_tmul, one_smul] using hs)

set_option maxHeartbeats 1300000 in
/-- The points which contract along the specified cocharacter and commute
with a subgroup of the torus have only the root coordinates fixed by that
subgroup. When there is one such positive root, its root group contains all
these points, including over test algebras with nilpotents. -/
private theorem contractingCentralizer_singleRoot (P : AffineAlgebraicGroup k)
    (hP : IsReductive P) (T : ClosedSubgroup P.val) (hT : IsSplitTorus T.group)
    (hmax : IsGeometricallyMaximal T) (c : Cocharacter T.group)
    {J : GroupScheme k} (hJ : IsAffine J.X.left) (j : J ⟶ T.group)
    (α : Root T) (hα : 0 < pairing T.group α.val c)
    (honly : ∀ β : Root T, 0 < pairing T.group β.val c → j ≫ β.val = 1 → β = α)
    (U : RootSubgroupFamily T) (R : TestAlgebra k) (g : GroupPoints P.val R)
    (hc : HasLimit (c ≫ T.inclusion) g 1)
    (hj : Centralizes (j ≫ T.inclusion) g) :
    ∃ q : GroupPoints (U α).val.group R, q ≫ (U α).val.inclusion.hom.hom = g := by
  classical
  obtain ⟨hfin, _, h⟩ := RootData.OrderedRootProducts.contractingProduct P hP T hT hmax
  obtain ⟨⟨D⟩, hD⟩ := h c
  let roots : Finset (Root T) :=
    ((hfin.preimage Subtype.val_injective.injOn).subset
      (show positiveRoots T c ⊆ Subtype.val ⁻¹' absoluteRoots T from fun β _ ↦ β.property)).toFinset
  let l := roots.toList
  have hl : Enumerates l (positiveRoots T c) := by
    refine ⟨Finset.nodup_toList _, ?_⟩
    intro β
    simp [l, roots]
  let x (β : Root T) := (rootCoordinate_exists RootData.RootGroups.rootSubgroups P hP T hT hmax U β).some
  obtain ⟨e, he⟩ := hD D U l hl
  letI : Mono (rootProduct U l) := by
    rw [← he]
    letI : Mono D.contracting.inclusion := inclusion_mono D.contracting
    letI : Mono D.contracting.inclusion.hom.hom :=
      (Grp.forget (SchemeOver k)).map_mono D.contracting.inclusion
    infer_instance
  obtain ⟨p, hp⟩ := (D.contracting_points R g).mp hc
  obtain ⟨a, ha⟩ := productPoint_surjective x R l hl.1 (p ≫ e.inv)
  change productPoint x R a l = p ≫ e.inv at ha
  change p ≫ D.contracting.inclusion.hom.hom = g at hp
  have hprod : productPoint x R a l ≫ rootProduct U l = g := by
    rw [ha, ← he, Category.assoc, e.inv_hom_id_assoc, hp]
  have hkill (β : Root T) (hβ : β ∈ l) (hn : j ≫ β.val ≠ 1) : a β = 0 := by
    apply fixedScalar_eq_zero hJ hn R (a β)
    intro S f t
    let z : GroupPoints T.group S := t ≫ j.hom.hom
    let w : GroupPoints P.val S := z ≫ T.inclusion.hom.hom
    let conj := MulAut.conj w
    let b : Root T → S := fun ξ ↦ f.hom (a ξ)
    let d : Root T → S := fun ξ ↦ characterValue ξ.val S z * b ξ
    let y : GroupPoints P.val S := mapPoints f g
    have hmap : productPoint x S b l ≫ rootProduct U l = y := by
      change productPoint x S (fun ξ ↦ f.hom (a ξ)) l ≫ rootProduct U l = mapPoints f g
      rw [← productPoint_map x f, ← hprod, mapPoints]
      exact Category.assoc _ _ _
    have hcomm : Commute y w := by
      exact (centralizes_iff_affine _ _).mp hj S ((testSpec k).map f.op) t
    have hfix : conj y = y := by
      change w * y * w⁻¹ = _
      rw [hcomm.symm.eq, mul_inv_cancel_right]
    have hconj : conj (productPoint x S b l ≫ rootProduct U l) =
        productPoint x S d l ≫ rootProduct U l := by
      rw [productPoint_mul x S b l, productPoint_mul x S d l, map_list_prod conj, List.map_map]
      apply congrArg List.prod
      apply List.map_congr_left
      intro ξ _
      exact RootCoordinate.scalar (x ξ) S z (b ξ)
    have heq := (cancel_mono (rootProduct U l)).mp
      (hconj.symm.trans ((congrArg conj hmap).trans (hfix.trans hmap.symm)))
    have hb := (productPoint_eq_iff x S d b l).mp heq β hβ
    exact (characterValue_composition β.val j S t).symm ▸ hb
  let v := fun β ↦ rootPoint ((RootCoordinate.iso (x β)).hom ≫ (U β).val.inclusion) R (a β)
  have hones : ∀ β, β ≠ α → β ∈ l → v β = 1 := by
    intro β hn hβ
    have hk := hkill β hβ (fun hz ↦ hn (honly β ((hl.2 β).mp hβ) hz))
    change rootPoint ((RootCoordinate.iso (x β)).hom ≫ (U β).val.inclusion) R (a β) = 1
    rw [hk, rootPoint_zero]
  letI : BEq (Root T) := instBEqOfDecidableEq
  have hcount : l.count α = 1 :=
    List.count_eq_one_of_mem hl.1 ((hl.2 α).mpr hα)
  refine ⟨rootPoint (RootCoordinate.iso (x α)).hom R (a α), ?_⟩
  have hv : g = v α := by
    rw [← hprod, productPoint_mul]
    change (l.map v).prod = v α
    rw [List.prod_map_eq_pow_single α v hones, hcount, pow_one]
  rw [hv]
  rfl

end ContractingRootProduct

section RelativeContracting

open CocharacterDynamics (HasLimit LimitDecomposition cocharacterPoint orbit unitPoint)
open Specs.Relative.RelativeReflections (CharacterKernel)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open private pairing_inv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private pairing_trivial from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private unitEquiv unitEquiv_unitPoint from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private Unipotent.group_hom_ext from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries

/-- A comparison preserving the unit parameter is determined by it. -/
private theorem multiplicativeComparison_unique (e e' : MultiplicativeComparison F)
    (h : PreservesUnits e) (h' : PreservesUnits e') : e = e' := by
  apply Iso.ext
  apply Unipotent.group_hom_ext (inferInstanceAs (IsAffine (Spec (CommRingCat.of (groupAlgebra Fsep IntegerCharacters)))))
  intro R x
  let t := unitEquiv R x
  have hx : unitPoint R t = x := (unitEquiv R).symm_apply_apply x
  change x ≫ e.hom.hom.hom = x ≫ e'.hom.hom.hom
  rw [← hx]
  apply (baseChangePointsEquiv Fsep Gm[F].X R).injective
  exact (h R t).trans (h' R t).symm

private theorem pairing_restriction (A : MarkedTori G) (e : MultiplicativeComparison F)
    (β : Character A.P.T.group) (c : Cocharacter A.S.group) :
    pairing A.P.T.group β (extendCocharacter e c ≫ A.splitInAbsolute) =
      pairing ((groupBaseChange F Fsep).obj A.S.group) (A.restrict β) (extendCocharacter e c) := by
  unfold pairing compositionPairing
  rw [Category.assoc]

/-- Positivity distinguishes the two signs of the singleton line. The
kernel here is the entire scheme kernel of the relative character. -/
private theorem isolatedPositiveRoot (A : MarkedTori G) (α : Root A.P.T)
    (h : HasSingletonRootLine A α) (e : MultiplicativeComparison F) (a : relativeRoots A.S)
    (hRoots : (extendCharacter e A.S.group) '' relativeRoots A.S =
      {χ | χ ≠ 1 ∧ ∃ β : Root A.P.T, A.restrict β.val = χ})
    (ha : extendCharacter e A.S.group a.val = A.restrict α.val)
    (D : CharacterKernel a.val) (c : Cocharacter A.S.group) (hc : 0 < pairing A.S.group a.val c) :
    let j := (groupBaseChange F Fsep).map D.subgroup.inclusion ≫ A.splitInAbsolute
    let d := extendCocharacter e c ≫ A.splitInAbsolute
    0 < pairing A.P.T.group α.val d ∧ j ≫ α.val = 1 ∧
      ∀ β : Root A.P.T, 0 < pairing A.P.T.group β.val d → j ≫ β.val = 1 → β = α := by
  let E := groupBaseChange F Fsep
  let j := E.map D.subgroup.inclusion ≫ A.splitInAbsolute
  let d := extendCocharacter e c ≫ A.splitInAbsolute
  have hres (β : Root A.P.T) (b : Character A.S.group)
      (hb : extendCharacter e A.S.group b = A.restrict β.val) :
      j ≫ β.val = extendCharacter e D.subgroup.group (D.subgroup.inclusion ≫ b) := by
    change (E.map D.subgroup.inclusion ≫ A.splitInAbsolute) ≫ β.val =
      E.map (D.subgroup.inclusion ≫ b) ≫ e.inv
    rw [E.map_comp, Category.assoc, Category.assoc]
    exact congrArg (E.map D.subgroup.inclusion ≫ ·) hb.symm
  have hpa : 0 < pairing A.P.T.group α.val d := by
    change 0 < pairing A.P.T.group α.val (extendCocharacter e c ≫ A.splitInAbsolute)
    rw [pairing_restriction, ← ha, pairing_extend]
    exact hc
  refine ⟨hpa, ?_, ?_⟩
  · rw [hres α a.val ha, (D.trivialRestrict_iff a.val).mpr ⟨1, (zpow_one _).symm⟩, map_one]
  · intro β hb hβ
    have hn : A.restrict β.val ≠ 1 := by
      intro hz
      change 0 < pairing A.P.T.group β.val (extendCocharacter e c ≫ A.splitInAbsolute) at hb
      rw [pairing_restriction, hz, pairing_trivial] at hb
      exact (lt_irrefl _ hb)
    obtain ⟨b, hbrel, hbval⟩ := (Set.ext_iff.mp hRoots _).mpr ⟨hn, β, rfl⟩
    have hker : D.subgroup.inclusion ≫ b = 1 := by
      apply extendCharacter_injective e D.subgroup.group
      rw [map_one, ← hres β b hbval]
      exact hβ
    obtain ⟨n, hbn⟩ := (D.trivialRestrict_iff b).mp hker
    have hpow : A.restrict β.val = (A.restrict α.val) ^ n := by
      rw [← hbval, hbn, map_zpow, ha]
    have hn₀ : n ≠ 0 := by
      intro hn₀
      rw [hn₀, zpow_zero] at hpow
      exact hn hpow
    obtain he | he := h.2 β hn ⟨n, 1, hn₀, one_ne_zero, by simpa using hpow.symm⟩
    · exact Subtype.ext he
    · have hh := pairing_inv A.P.T.group A.P.split α.val d
      rw [he, hh] at hb
      exact (not_lt_of_ge (neg_nonpos.mpr hpa.le) hb).elim

section LimitTransport

open CocharacterDynamics (laurentAlgebra laurentConstants laurentParameter polynomialAlgebra
  polynomialEvaluate polynomialToLaurent)
open private polynomial_factorsThrough from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterSmoothAndUnipotent
open private cocharacterPoint_postcompose from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private Unipotent.onPoints from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries
open private onPoints_mapPoints from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.ReductiveLieCentralizers

variable {k : Type u} [Field k] {X Y : GroupScheme k}

private theorem orbit_postcompose (f : X ⟶ Y) (c : Cocharacter X)
    (R : TestAlgebra k) (x : GroupPoints X R) :
    orbit (c ≫ f) (x ≫ f.hom.hom) = orbit c x ≫ f.hom.hom := by
  let S := laurentAlgebra R
  let t := cocharacterPoint c S (laurentParameter R)
  let q : GroupPoints X S := mapPoints (laurentConstants R) x
  let m := IsMonHom.monoidHom f.hom.hom ((testSpec k).obj (op S))
  have hnat : (mapPoints (laurentConstants R) (x ≫ f.hom.hom) : GroupPoints Y S) = m q := by
    change (testSpec k).map (laurentConstants R).op ≫ x ≫ f.hom.hom =
      (((testSpec k).map (laurentConstants R).op) ≫ x) ≫ f.hom.hom
    exact (Category.assoc _ _ _).symm
  unfold orbit
  rw [cocharacterPoint_postcompose, hnat]
  change m t * m q * (m t)⁻¹ = m (t * q * t⁻¹)
  rw [map_mul, map_mul, map_inv]

/-- A group morphism transports polynomial limits of the conjugation orbit. -/
private theorem hasLimit_postcompose (f : X ⟶ Y) {c : Cocharacter X}
    {R : TestAlgebra k} {x : GroupPoints X R} (h : HasLimit c x 1) :
    HasLimit (c ≫ f) (x ≫ f.hom.hom) 1 := by
  obtain ⟨p, hp, hz⟩ := h
  refine ⟨p ≫ f.hom.hom, ?_, ?_⟩
  · rw [orbit_postcompose, ← hp]
    exact (Category.assoc ((testSpec k).map (polynomialToLaurent R).op) p f.hom.hom).symm
  · have hmap : (1 : GroupPoints X R) ≫ f.hom.hom = (1 : GroupPoints Y R) :=
      (IsMonHom.monoidHom f.hom.hom ((testSpec k).obj (op R))).map_one
    calc
      mapPoints (polynomialEvaluate R 0) (p ≫ f.hom.hom) =
          mapPoints (polynomialEvaluate R 0) p ≫ f.hom.hom :=
        (Category.assoc ((testSpec k).map (polynomialEvaluate R 0).op) p f.hom.hom).symm
      _ = (1 : GroupPoints X R) ≫ f.hom.hom := congrArg (· ≫ f.hom.hom) hz
      _ = 1 := hmap

/-- The Laurent orbit lies in the source of a closed group inclusion. Its
polynomial extension then also lies there by injectivity of the localization. -/
private theorem hasLimit_of_closed_postcompose (f : X ⟶ Y) (hY : IsAffine Y.X.left)
    (hf : IsClosedImmersion f.hom.hom.left) {c : Cocharacter X}
    {R : TestAlgebra k} {x : GroupPoints X R}
    (h : HasLimit (c ≫ f) (x ≫ f.hom.hom) 1) : HasLimit c x 1 := by
  obtain ⟨p, hp, hz⟩ := h
  rw [orbit_postcompose] at hp
  obtain ⟨q, hq⟩ := polynomial_factorsThrough hY f.hom.hom hf p ⟨orbit c x, hp.symm⟩
  letI := hf
  letI : Mono f.hom.hom := Over.mono_of_mono_left _
  refine ⟨q, (cancel_mono f.hom.hom).mp ?_, (cancel_mono f.hom.hom).mp ?_⟩
  · exact ((Category.assoc _ _ _).trans
      ((congrArg (mapPoints (polynomialToLaurent R)) hq).trans hp))
  · have hmap : (1 : GroupPoints X R) ≫ f.hom.hom = 1 :=
      (IsMonHom.monoidHom f.hom.hom ((testSpec k).obj (op R))).map_one
    exact ((Category.assoc _ _ _).trans
      ((congrArg (mapPoints (polynomialEvaluate R 0)) hq).trans (hz.trans hmap.symm)))

end LimitTransport

open Specs.GeometricBorelConjugacy (IsReducedIdentityComponent)
open Specs.OrderedRootProducts (RootSubgroupFamily)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open CocharacterDynamics (RepresentsOnAlgebras)
open private subgroupInclusionFactors from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private subgroupIso_of_same from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private additive_root_in_centralizer_component from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RelativeReflections
open private rootPoint_hasLimit rootPoint_surjective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private rootPoint_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups

set_option maxHeartbeats 1300000 in
/-- In the connected kernel centralizer, the contraction for the isolated
positive root is the chosen absolute root subgroup. -/
private theorem compareContractingComponent {k : Type u} [Field k]
    (P : AffineAlgebraicGroup k) (hP : IsReductive P) (T : ClosedSubgroup P.val)
    (hT : IsSplitTorus T.group) (hmax : Specs.RankOneFlag.IsGeometricallyMaximal T)
    {J : GroupScheme k} (hJ : IsAffine J.X.left) (j : J ⟶ T.group)
    (C : ClosedSubgroup P.val) (H : ClosedSubgroup C.group) (hH : IsReducedIdentityComponent H)
    (hC : RepresentsSubgroup C (fun _ g ↦ Centralizes (j ≫ T.inclusion) g))
    (c : Cocharacter T.group) (d : Cocharacter H.group)
    (hd : d ≫ (subgroupOfSubgroup C H).inclusion = c ≫ T.inclusion)
    (W : ClosedSubgroup H.group) (hW : RepresentsOnAlgebras W (fun _ g ↦ HasLimit d g 1))
    (α : Root T) (hα : 0 < pairing T.group α.val c) (hker : j ≫ α.val = 1)
    (honly : ∀ β : Root T, 0 < pairing T.group β.val c → j ≫ β.val = 1 → β = α)
    (U : ClosedSubgroup P.val) (hU : IsRootSubgroup T U α.val) {L : AdditiveLine k}
    (x : L.group ≅ U.group) (hx : HasScalarAction T α.val (x.hom ≫ U.inclusion)) :
    ∃ s : W.group ≅ U.group,
      s.hom ≫ U.inclusion = W.inclusion ≫ H.inclusion ≫ C.inclusion := by
  classical
  let H' := subgroupOfSubgroup C H
  let W' := subgroupOfSubgroup H' W
  have hU' : IsSubgroupOf U H' :=
    additive_root_in_centralizer_component T j C H hH hC U α.val hker hU x hx
  let fam (β : Root T) : {U : ClosedSubgroup P.val // IsRootSubgroup T U β.val} :=
    if h : β = α then h.symm ▸ ⟨U, hU⟩ else
      let r := ((RootData.RootGroups.rootSubgroups P hP T hT hmax).2 β.val β.property).2.2
      ⟨r.choose, r.choose_spec.1⟩
  have hfam : (fam α).val = U := by simp [fam]
  have hin : IsSubgroupOf W' U := by
    apply subgroupInclusionFactors
      (Specs.Unipotent.closedSubgroupAlgebraicGroup (G := P) W').property.1
    intro R p
    let q : GroupPoints H.group R := p ≫ W.inclusion.hom.hom
    let g : GroupPoints P.val R := q ≫ H'.inclusion.hom.hom
    have hq : HasLimit d q 1 := (hW R q).mpr ⟨p, rfl⟩
    have hg : HasLimit (c ≫ T.inclusion) g 1 := by
      rw [← hd]
      exact hasLimit_postcompose H'.inclusion hq
    have hcen : Centralizes (j ≫ T.inclusion) g :=
      (hC _ g).mpr ⟨q ≫ H.inclusion.hom.hom, Category.assoc _ _ _⟩
    have hp := contractingCentralizer_singleRoot P hP T hT hmax c hJ j α hα honly fam R g hg hcen
    rw [hfam] at hp
    exact hp
  have hout : IsSubgroupOf U W' := by
    obtain ⟨m, hm⟩ := hU'
    have he : m.hom.hom ≫ H'.inclusion.hom.hom = U.inclusion.hom.hom :=
      congrArg (Grp.forget (SchemeOver k)).map hm
    obtain ⟨s, hs⟩ := subgroupInclusionFactors
      (Specs.Unipotent.closedSubgroupAlgebraicGroup (G := P) U).property.1 W m (by
        intro R p
        obtain ⟨a, rfl⟩ := rootPoint_surjective x R p
        apply (hW R _).mp
        apply hasLimit_of_closed_postcompose H'.inclusion P.property.1 H'.isClosedImmersion
        rw [hd]
        have hpt : (rootPoint x.hom R a ≫ m.hom.hom) ≫ H'.inclusion.hom.hom =
            rootPoint (x.hom ≫ U.inclusion) R a := by
          rw [Category.assoc, he, rootPoint_comp]
        change HasLimit (c ≫ T.inclusion)
          ((rootPoint x.hom R a ≫ m.hom.hom) ≫ H'.inclusion.hom.hom) 1
        rw [hpt]
        exact rootPoint_hasLimit hx c hα R a)
    refine ⟨s, ?_⟩
    change s ≫ W.inclusion ≫ H'.inclusion = U.inclusion
    rw [← Category.assoc, hs, hm]
  exact subgroupIso_of_same ⟨hin, hout⟩

open Specs.Unipotent (closedSubgroupAlgebraicGroup baseChangedAlgebraicGroup)
open private extendSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private reducedIdentityComponent_of_open_closed
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.ReductiveLieCentralizers
open private connected_of_geometricallyConnected
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private transportSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate

private theorem centralizes_postcomposeIso {k : Type u} [Field k] {D X Y : GroupScheme k}
    (e : X ≅ Y) (j : D ⟶ X) {S : SchemeOver k} (g : S ⟶ X.X) :
    Centralizes j g ↔ Centralizes (j ≫ e.hom) (g ≫ e.hom.hom.hom) := by
  let h := e.hom.hom.hom
  haveI : IsIso h := (Grp.forget (SchemeOver k)).map_isIso e.hom
  have hc : conjugateFamily j g ≫ h = conjugateFamily (j ≫ e.hom) (g ≫ h) := by
    unfold conjugateFamily
    simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, Grp.comp_hom_hom, h]
  change (conjugateFamily j g = fst D.X S ≫ j.hom.hom) ↔
    (conjugateFamily (j ≫ e.hom) (g ≫ h) = fst D.X S ≫ (j ≫ e.hom).hom.hom)
  rw [← hc]
  change _ ↔ (conjugateFamily j g ≫ h = fst D.X S ≫ j.hom.hom ≫ h)
  rw [← Category.assoc (fst D.X S), cancel_mono]

open private baseChangeMapPullback from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components

set_option maxHeartbeats 1700000 in
/-- The rational contracting subgroup in the full kernel centralizer
base changes to the isolated absolute root subgroup, with its ambient inclusion. -/
private theorem absoluteComparisonOfContracting (A : MarkedTori G)
    (e : MultiplicativeComparison F) (he : PreservesUnits e)
    (a : relativeRoots A.S) (C : RootCentralizer A.S a) (c : Cocharacter A.S.group)
    (α : Root A.P.T)
    (hα : 0 < pairing A.P.T.group α.val (extendCocharacter e c ≫ A.splitInAbsolute))
    (hker : ((groupBaseChange F Fsep).map C.kernel.subgroup.inclusion ≫ A.splitInAbsolute) ≫ α.val = 1)
    (honly : ∀ β : Root A.P.T, 0 < pairing A.P.T.group β.val (extendCocharacter e c ≫ A.splitInAbsolute) →
      ((groupBaseChange F Fsep).map C.kernel.subgroup.inclusion ≫ A.splitInAbsolute) ≫ β.val = 1 → β = α)
    (W : LimitDecomposition (c ≫ C.torusIso.hom ≫ C.torus.inclusion))
    (U : ClosedSubgroup A.P.G.val) (hU : IsRootSubgroup A.P.T U α.val) {L : AdditiveLine Fsep}
    (x : L.group ≅ U.group) (hx : HasScalarAction A.P.T α.val (x.hom ≫ U.inclusion)) :
    ∃ s : (groupBaseChange F Fsep).obj W.contracting.group ≅ U.group,
      s.hom ≫ U.inclusion ≫ A.ambient.hom =
        (groupBaseChange F Fsep).map (W.contracting.inclusion ≫ C.component.inclusion ≫ C.centralizer.inclusion) := by
  let E := groupBaseChange F Fsep
  let H := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup C.centralizer) C.component
  let d := c ≫ C.torusIso.hom ≫ C.torus.inclusion
  let j := E.map C.kernel.subgroup.inclusion ≫ A.splitInAbsolute
  let m := C.kernel.subgroup.inclusion ≫ A.S.inclusion
  obtain ⟨hZcl, hZ⟩ := centralizerSchemeBaseChange F Fsep m C.centralizer C.represents
  let Z := baseChangedSubgroup Fsep C.centralizer hZcl
  let Z' := transportSubgroup A.ambient.symm Z
  let H' := extendSubgroup Fsep C.component
  have hj : (j ≫ A.P.T.inclusion) ≫ A.ambient.hom = E.map m := by
    change ((E.map C.kernel.subgroup.inclusion ≫ E.map A.intoTorus ≫ A.torus.hom) ≫
      A.P.T.inclusion) ≫ A.ambient.hom = E.map (C.kernel.subgroup.inclusion ≫ A.S.inclusion)
    have ht : A.torus.hom ≫ A.P.T.inclusion ≫ A.ambient.hom = E.map A.T.inclusion := A.torus_eq
    simp only [Category.assoc, ht, ← E.map_comp, A.intoTorus_eq]
  have hZi : Z'.inclusion ≫ A.ambient.hom = Z.inclusion := by
    change (Z.inclusion ≫ A.ambient.inv) ≫ A.ambient.hom = Z.inclusion
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hZ' : RepresentsSubgroup Z' (fun _ g ↦ Centralizes (j ≫ A.P.T.inclusion) g) := by
    intro S g
    have hZi' := congrArg (Grp.forget (SchemeOver Fsep)).map hZi
    change Z'.inclusion.hom.hom ≫ A.ambient.hom.hom.hom = Z.inclusion.hom.hom at hZi'
    have htest (p : S ⟶ Z'.group.X) :
        p ≫ Z'.inclusion.hom.hom = g ↔ p ≫ Z.inclusion.hom.hom = g ≫ A.ambient.hom.hom.hom := by
      haveI : IsIso A.ambient.hom.hom.hom := (Grp.forget (SchemeOver Fsep)).map_isIso A.ambient.hom
      exact (cancel_mono A.ambient.hom.hom.hom).symm.trans (by rw [Category.assoc, hZi'])
    change Centralizes (j ≫ A.P.T.inclusion) g ↔ ∃ p : S ⟶ Z'.group.X, p ≫ Z'.inclusion.hom.hom = g
    rw [centralizes_postcomposeIso A.ambient, hj]
    have hz := hZ S (g ≫ A.ambient.hom.hom.hom)
    refine hz.trans ?_
    exact exists_congr (fun p => (htest p).symm)
  have hHopen : IsOpenImmersion H'.inclusion.hom.hom.left :=
    MorphismProperty.of_isPullback (baseChangeMapPullback (K := Fsep) C.component.inclusion.hom.hom).flip C.isOpen
  have hpb : IsPullback (pullback.fst H.val.X.hom (fieldSpecMap F Fsep))
      H'.group.X.hom H.val.X.hom (fieldSpecMap F Fsep) := IsPullback.of_hasPullback _ _
  have hHred : IsReducedIdentityComponent H' :=
    reducedIdentityComponent_of_open_closed H' hHopen
      (MorphismProperty.of_isPullback hpb C.reductive.1)
      (connected_of_geometricallyConnected (MorphismProperty.of_isPullback hpb C.reductive.2.1))
  obtain ⟨e', he', _, hWcl, _, _, hW, _, _⟩ :=
    CocharacterDynamics.limitSubgroupsBaseChange (K := Fsep) H d W
  have heq := multiplicativeComparison_unique e' e he' he
  subst e'
  let w := baseChangedSubgroup Fsep W.contracting hWcl
  have hd : extendCocharacter e d ≫ (subgroupOfSubgroup Z' H').inclusion =
      (extendCocharacter e c ≫ A.splitInAbsolute) ≫ A.P.T.inclusion := by
    apply (cancel_mono A.ambient.hom).mp
    change (e.hom ≫ E.map d ≫ E.map C.component.inclusion ≫ E.map C.centralizer.inclusion ≫
      A.ambient.inv) ≫ A.ambient.hom =
      ((e.hom ≫ E.map c) ≫ (E.map A.intoTorus ≫ A.torus.hom)) ≫
        A.P.T.inclusion ≫ A.ambient.hom
    have ht : A.torus.hom ≫ A.P.T.inclusion ≫ A.ambient.hom = E.map A.T.inclusion := A.torus_eq
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, ht, ← E.map_comp]
    change e.hom ≫ E.map (d ≫ C.component.inclusion ≫ C.centralizer.inclusion) =
      e.hom ≫ E.map (c ≫ A.intoTorus ≫ A.T.inclusion)
    simp only [d, Category.assoc, C.torusInclusion, A.intoTorus_eq]
  obtain ⟨s, hs⟩ := compareContractingComponent A.P.G A.P.reductive A.P.T A.P.split A.P.maximal
    (closedSubgroupAlgebraicGroup (G := baseChangedAlgebraicGroup Fsep G)
      (extendSubgroup Fsep (subgroupOfSubgroup A.S C.kernel.subgroup))).property.1
    j Z' H' hHred hZ' (extendCocharacter e c ≫ A.splitInAbsolute) (extendCocharacter e d) hd
    w hW α hα hker honly U hU x hx
  refine ⟨s, ?_⟩
  calc
    s.hom ≫ U.inclusion ≫ A.ambient.hom =
        (s.hom ≫ U.inclusion) ≫ A.ambient.hom := (Category.assoc _ _ _).symm
    _ = (w.inclusion ≫ H'.inclusion ≫ Z'.inclusion) ≫ A.ambient.hom :=
      congrArg (· ≫ A.ambient.hom) hs
    _ = w.inclusion ≫ H'.inclusion ≫ Z.inclusion := by
      simp only [Category.assoc, hZi]
    _ = E.map (W.contracting.inclusion ≫ C.component.inclusion ≫ C.centralizer.inclusion) := by
      change E.map W.contracting.inclusion ≫ E.map C.component.inclusion ≫
        E.map C.centralizer.inclusion = _
      simp only [E.map_comp]


end RelativeContracting

section AdditiveCoordinate

open scoped TensorProduct
open CocharacterDynamics (LimitDecomposition)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private groupPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private extendedSpecIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private split_additive_of_coordinate from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private affinePointEquiv affinePointEquiv_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterSmoothAndUnipotent

/-- The number of polynomial coordinates of a contracting subgroup whose
scalar extension is an additive line is one. -/
private theorem polynomialCoordinates_of_geometricLine
    {k K : Type u} [Field k] [Field K] [Algebra k K] (A : HopfAlgebraCategory k)
    (n : ℕ) (coordinates : MvPolynomial (Fin n) k ≃ₐ[k] A) (L : AdditiveLine K)
    (s : (groupBaseChange k K).obj (specGroup A) ≅ L.group) :
    n = 1 := by
  let sX := (Grp.forget (SchemeOver K)).mapIso s
  let chart := extendedSpecIso K A ≪≫ sX
  let E : Polynomial K ≃ₐ[K] K ⊗[k] A :=
    CommAlgCat.isoEquivAlgEquiv
      ((algSpec.fullyFaithful (R := CommRingCat.of K)).preimageIso chart).unop
  let tensored : K ⊗[k] MvPolynomial (Fin n) k ≃ₐ[K] K ⊗[k] A :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) coordinates
  let e := (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) k K).symm.trans
    (tensored.trans E.symm)
  have hc := e.trdeg_eq
  rw [MvPolynomial.trdeg_of_isDomain, Polynomial.trdeg_of_isDomain, Cardinal.mk_fin,
    Cardinal.lift_natCast] at hc
  exact Nat.cast_inj.mp (hc.trans (Nat.cast_one : ((1 : ℕ) : Cardinal) = 1).symm)

set_option maxHeartbeats 900000 in
private theorem splitAdditive_of_polynomialChart {k : Type u} [Field k]
    (U : GroupScheme k) (hU : IsAffine U.X.left)
    (e : (testSpec k).obj (op (CommAlgCat.of k (Polynomial k))) ≅ U.X) :
    Specs.RankOneFlag.IsSplitAdditive U := by
  let coord (R : TestAlgebra k) : GroupPoints U R ≃ R :=
    (affinePointEquiv e R).symm.trans (Polynomial.aevalEquiv k R).symm
  have hcoord {R S : TestAlgebra k} (f : R ⟶ S) (p : GroupPoints U R) :
      coord S (mapPoints f p) = f.hom (coord R p) := by
    obtain ⟨a, rfl⟩ := (affinePointEquiv e R).surjective p
    rw [← affinePointEquiv_natural e f a]
    change (((affinePointEquiv e S).symm (affinePointEquiv e S (f.hom.comp a))) Polynomial.X) =
      f.hom (((affinePointEquiv e R).symm (affinePointEquiv e R a)) Polynomial.X)
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rfl
  let translated (R : TestAlgebra k) : R ≃ R :=
    { toFun := fun x => x - coord R 1
      invFun := fun x => x + coord R 1
      left_inv := fun _ => sub_add_cancel _ _
      right_inv := fun _ => add_sub_cancel_right _ _ }
  refine split_additive_of_coordinate hU (fun R => (coord R).trans (translated R)) ?_ ?_
  · intro R S f p
    have hone : (mapPoints f (1 : GroupPoints U R) : GroupPoints U S) = 1 :=
      (((groupPointsFunctor k).obj U).map f).hom.map_one
    change coord S (mapPoints f p) - coord S 1 = f.hom (coord R p - coord R 1)
    rw [hcoord f p, map_sub, ← hcoord f (1 : GroupPoints U R), hone]
  · intro R
    exact sub_self (coord R 1)

set_option maxHeartbeats 1600000 in
private theorem contractingSplitAdditive {k K : Type u} [Field k] [Field K] [Algebra k K]
    (H : AffineAlgebraicGroup k) (hH : IsReductive H)
    (c : Cocharacter H.val) (D : LimitDecomposition c) (L : AdditiveLine K)
    (s : (groupBaseChange k K).obj D.contracting.group ≅ L.group) :
    Specs.RankOneFlag.IsSplitAdditive D.contracting.group := by
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation (closedSubgroupAlgebraicGroup (G := H) D.contracting)
  obtain ⟨n, _, coordinates, _, _, _, _⟩ :=
    Relative.SplitContractingRadical.contractingPolynomialCoordinates H hH c D A e
  have hn := polynomialCoordinates_of_geometricLine A n coordinates L
    ((groupBaseChange k K).mapIso e ≪≫ s)
  subst n
  let equiv := (MvPolynomial.uniqueAlgEquiv k (Fin 1)).symm.trans coordinates
  let e' : CommAlgCat.of k (Polynomial k) ≅ CommAlgCat.of k A := CommAlgCat.isoMk equiv
  let chart := (testSpec k).mapIso e'.symm.op ≪≫ (Grp.forget (SchemeOver k)).mapIso e
  exact splitAdditive_of_polynomialChart D.contracting.group
    (closedSubgroupAlgebraicGroup (G := H) D.contracting).property.1 chart

end AdditiveCoordinate

open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)

set_option maxHeartbeats 1800000 in
/-- The isolated absolute root group is the scalar extension of a split
additive closed subgroup of the original reductive group. -/
theorem rootGroupDescent : RootGroupDescent.{u} := by
  intro F _ G hG A α h U hU L x hx
  obtain ⟨e, a, he, hRoots, ha⟩ := relativeRootOfRestriction A α h.1
  obtain ⟨C⟩ := Relative.RelativeReflections.rootCentralizers G hG A.S A.maximalSplit a
  obtain ⟨c, hc⟩ := RankOneFlag.exists_positive_cocharacter A.maximalSplit.1 a.property.1
  obtain ⟨hα, hker, honly⟩ := isolatedPositiveRoot A α h e a hRoots ha C.kernel c hc
  let H := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup C.centralizer) C.component
  let d : Cocharacter H.val := c ≫ C.torusIso.hom ≫ C.torus.inclusion
  obtain ⟨W⟩ := CocharacterDynamics.existsLimitDecomposition H d
  obtain ⟨s, hs⟩ := absoluteComparisonOfContracting A e he a C c α hα hker honly W U hU x hx
  obtain ⟨ops, hδ, hε, hi, ⟨i⟩⟩ := contractingSplitAdditive H C.reductive d W L (s ≪≫ x.symm)
  let U₀ := subgroupOfSubgroup (subgroupOfSubgroup C.centralizer C.component) W.contracting
  exact ⟨U₀, ⟨ops, hδ, hε, hi⟩, i.symm, s, hs⟩

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalRootGroupDescent
