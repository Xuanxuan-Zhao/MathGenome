import Specs.LinearAlgebraicGroups.Flag.BruhatOrbitParametrization
import LinearAlgebraicGroups.Flag.HomogeneousQuotient
import LinearAlgebraicGroups.Flag.SmoothOrbit
import LinearAlgebraicGroups.Reductive.WeylScheme
import LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
import LinearAlgebraicGroups.Reductive.BorelProper
import Batteries.Tactic.OpenPrivate
import Mathlib.Topology.Algebra.Order.Archimedean

import LinearAlgebraicGroups.RootData.BorelPositivity
import LinearAlgebraicGroups.RootData.OrderedRootProducts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Flag.BruhatOrbitParametrization

noncomputable section

set_option backward.isDefEq.respectTransparency false

open _root_.LinearAlgebraicGroups.Specs
open Specs.AbstractPairing (Datum Root)
open Specs.BorelsAndChambers (IsPositiveSystem IsRegular positiveRoots subgroupRoots)
open Specs.BorelPositivity (BorelCorrespondence)
open Specs.BruhatOrbitParametrization
open Specs.CharacterDescent (Character Cocharacter)
open Specs.DatumAndWeyl (Identification)
open Specs.GeometricBorelConjugacy (IsKBorel subgroupOfSubgroup)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open Specs.OrderedRootProducts (Enumerates Parametrizes RootSubgroupFamily)
open Specs.QuotientEmbedding (Presentation)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

private theorem oppositePositiveSystem {T : ClosedSubgroup G.val}
    {S : Set (Root T)} (hS : IsPositiveSystem T S) : IsPositiveSystem T Sᶜ := by
  obtain ⟨f, hf, rfl⟩ := hS
  refine ⟨-f, fun α ↦ neg_ne_zero.mpr (hf α), ?_⟩
  ext α
  change ¬ 0 < f (Additive.ofMul α.val) ↔ 0 < -f (Additive.ofMul α.val)
  constructor
  · intro h
    exact neg_pos.mpr ((le_of_not_gt h).lt_of_ne (hf α))
  · intro h
    exact not_lt_of_ge (neg_pos.mp h).le

private theorem integralChamber {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    (D : Datum T) {S : Set (Root T)} (hS : IsPositiveSystem T S) :
    ∃ cochar : Cocharacter T.group, IsRegular T cochar ∧ positiveRoots T cochar = S := by
  classical
  obtain ⟨f, hf, rfl⟩ := hS
  let X := Additive (Character T.group)
  let : Module.Free ℤ X := D.freeCharacters
  let : Module.Finite ℤ X := D.finiteCharacters
  let : Finite (Root T) := D.finiteRoots
  let Idx := Module.Free.ChooseBasisIndex ℤ X
  let : Fintype Idx := Fintype.ofFinite Idx
  let b : Module.Basis Idx ℤ X := Module.Free.chooseBasis ℤ X
  let r : Root T → X := fun α ↦ Additive.ofMul α.val
  let ev (a : Idx → ℝ) (α : Root T) : ℝ := ∑ i, (b.repr (r α) i : ℝ) * a i
  let a₀ : Idx → ℝ := fun i ↦ f (b i)
  have ha₀ (α : Root T) : ev a₀ α = f (r α) := by
    have h := congrArg f (b.sum_repr (r α))
    simpa only [ev, a₀, map_sum, LinearMap.map_smul, zsmul_eq_mul] using h
  let O : Set (Idx → ℝ) := ⋂ α : Root T, {a | 0 < f (r α) * ev a α}
  have ho : IsOpen O := by
    apply isOpen_iInter_of_finite
    intro α
    have he : Continuous (fun a : Idx → ℝ ↦ ev a α) := by
      unfold ev
      fun_prop
    exact isOpen_lt continuous_const (continuous_const.mul he)
  have ha₀' : a₀ ∈ O := by
    apply Set.mem_iInter.mpr
    intro α
    change 0 < f (r α) * ev a₀ α
    rw [ha₀]
    exact mul_self_pos.mpr (hf α)
  let cast : (Idx → ℚ) → (Idx → ℝ) := fun a i ↦ (a i : ℝ)
  have hd : DenseRange cast :=
    DenseRange.piMap (fun _ ↦ (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)))
  obtain ⟨q, hq⟩ := hd.exists_mem_open ho ⟨a₀, ha₀'⟩
  let m : ℕ := ∏ i, (q i).den
  have hm : 0 < m := Finset.prod_pos (fun i _ ↦ (q i).den_pos)
  let z (i : Idx) : ℤ := (q i).num * (∏ j ∈ Finset.univ.erase i, (q j).den : ℕ)
  have hz (i : Idx) : (z i : ℝ) = (m : ℝ) * cast q i := by
    have hi : i ∈ (Finset.univ : Finset Idx) := Finset.mem_univ _
    have hprod := Finset.mul_prod_erase Finset.univ (fun j ↦ (q j).den) hi
    change (z i : ℝ) = (m : ℝ) * (q i : ℝ)
    rw [show m = (q i).den * (∏ j ∈ Finset.univ.erase i, (q j).den) from hprod.symm]
    simp only [z, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, Rat.cast_def]
    have hden : ((q i).den : ℝ) ≠ 0 := by exact_mod_cast (q i).den_ne_zero
    field_simp
  let L : X →ₗ[ℤ] ℤ := b.constr ℤ z
  have hL (α : Root T) : (L (r α) : ℝ) = (m : ℝ) * ev (cast q) α := by
    rw [show L (r α) = ∑ i, b.repr (r α) i • z i from b.constr_apply_fintype ℤ z (r α)]
    simp only [Int.cast_sum, zsmul_eq_mul, Int.cast_mul, hz, ev, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ ↦ by push_cast; ring)
  let cochar : Cocharacter T.group := Additive.toMul (D.rootDatum.toLinearMap.flip.toPerfPair.symm L)
  have hpair (α : Root T) : CharacterPairing.pairing T.group α.val cochar = L (r α) := by
    rw [← D.pairing_eq]
    exact D.rootDatum.toLinearMap.apply_toPerfPair_flip L (r α)
  have hsign (α : Root T) : 0 < f (r α) * (CharacterPairing.pairing T.group α.val cochar : ℝ) := by
    rw [hpair, hL, ← mul_left_comm (m : ℝ)]
    exact mul_pos (by exact_mod_cast hm) (Set.mem_iInter.mp hq α)
  refine ⟨cochar, fun α hzero ↦ ?_, ?_⟩
  · simpa [hzero] using hsign α
  · ext α
    change 0 < CharacterPairing.pairing T.group α.val cochar ↔ 0 < f (r α)
    have hh := hsign α
    constructor
    · intro hp
      have hp' : 0 < (CharacterPairing.pairing T.group α.val cochar : ℝ) := by exact_mod_cast hp
      exact pos_of_mul_pos_left hh hp'.le
    · intro hp
      have hp' := pos_of_mul_pos_right hh hp.le
      exact_mod_cast hp'

private theorem conjugateChamber {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D : Datum T} (I : Identification D) (w : D.rootDatum.weylGroup)
    (cochar : Cocharacter T.group) :
    let cochar' := cochar ≫ (I.image.conjugation (I.labelEquiv w)).hom
    ∀ α : Root T,
      Specs.CharacterPairing.pairing T.group (D.rootDatum.weylGroupToPerm w α).val cochar' =
        Specs.CharacterPairing.pairing T.group α.val cochar := by
  dsimp only
  intro α
  rw [← D.pairing_eq, ← D.pairing_eq, ← D.root_eq, ← D.root_eq, ← I.cocharacterAction]
  change D.rootDatum.toLinearMap (D.rootDatum.root (w.val.indexEquiv α))
      (w.val.coweightEquiv.symm (Additive.ofMul cochar)) = _
  rw [← w.val.root_weightMap_apply]
  change D.rootDatum.toLinearMap (w.val.weightEquiv (D.rootDatum.root α)) _ = _
  rw [w.val.toLinearMap_weightEquiv, LinearEquiv.apply_symm_apply]

private theorem positiveRoots_conjugate {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D : Datum T} (I : Identification D) (w : D.rootDatum.weylGroup)
    (cochar : Cocharacter T.group) :
    positiveRoots T (cochar ≫ (I.image.conjugation (I.labelEquiv w)).hom) =
      D.rootDatum.weylGroupToPerm w '' positiveRoots T cochar := by
  ext α
  let p := D.rootDatum.weylGroupToPerm w
  have h := conjugateChamber I w cochar (p.symm α)
  change Specs.CharacterPairing.pairing T.group (p (p.symm α)).val _ = _ at h
  rw [Equiv.apply_symm_apply] at h
  constructor
  · intro hα
    refine ⟨p.symm α, ?_, p.apply_symm_apply α⟩
    change 0 < Specs.CharacterPairing.pairing T.group (p.symm α).val cochar
    rw [← h]
    exact hα
  · rintro ⟨β, hβ, rfl⟩
    change 0 < Specs.CharacterPairing.pairing T.group (p β).val _
    rw [conjugateChamber I w cochar β]
    exact hβ

open Specs.OrderedRootProducts (product rootProduct)
open LinearAlgebraicGroups.CocharacterDynamics (multiplyFactors)

private theorem monoSubgroup {M : GroupScheme k} (H : ClosedSubgroup M) :
    Mono H.inclusion.hom.hom := by
  let := H.isClosedImmersion
  exact Over.mono_of_mono_left _

private theorem memSubgroup_comp {M : GroupScheme k} {H : ClosedSubgroup M}
    {X Y : SchemeOver k} (f : X ⟶ Y) {g : Y ⟶ M.X} (hg : g ∈ SubgroupSections H Y) :
    f ≫ g ∈ SubgroupSections H X := by
  obtain ⟨h, hh⟩ := hg
  exact ⟨f ≫ h, (Category.assoc _ _ _).trans (congrArg (f ≫ ·) hh)⟩

private theorem subgroupFactorThrough {M : GroupScheme k} (A B : ClosedSubgroup M)
    (h : A.inclusion.hom.hom ∈ SubgroupSections B A.group.X) :
    IsSubgroupOf A B := by
  change (∃ f : A.group.X ⟶ B.group.X, f ≫ B.inclusion.hom.hom =
    A.inclusion.hom.hom) at h
  obtain ⟨f, hf⟩ := h
  have := monoSubgroup B
  have h1 : η[A.group.X] ≫ f = η[B.group.X] := by
    apply (cancel_mono B.inclusion.hom.hom).mp
    rw [Category.assoc, hf, IsMonHom.one_hom, IsMonHom.one_hom]
  have hm : μ[A.group.X] ≫ f = (f ⊗ₘ f) ≫ μ[B.group.X] := by
    apply (cancel_mono B.inclusion.hom.hom).mp
    rw [Category.assoc, hf, Category.assoc, IsMonHom.mul_hom B.inclusion.hom.hom,
      ← Category.assoc, tensorHom_comp_tensorHom, hf, IsMonHom.mul_hom A.inclusion.hom.hom]
  exact ⟨Grp.homMk'' f h1 hm, Grp.hom_ext _ _ hf⟩

private def subgroupPullback {M : GroupScheme k} (A B : ClosedSubgroup M) :
    ClosedSubgroup A.group := by
  let j := (pullback.fst A.inclusion B.inclusion : pullback A.inclusion B.inclusion ⟶ A.group)
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  have h := (IsPullback.of_hasPullback A.inclusion B.inclusion).map F
  exact ⟨_, j, MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip
    B.isClosedImmersion⟩

private theorem subgroupPullback_sections {M : GroupScheme k} (A B : ClosedSubgroup M)
    {Y : SchemeOver k} (a : Y ⟶ A.group.X) :
    a ∈ SubgroupSections (subgroupPullback A B) Y ↔
      a ≫ A.inclusion.hom.hom ∈ SubgroupSections B Y := by
  let h := (IsPullback.of_hasPullback A.inclusion B.inclusion).map (Grp.forget (SchemeOver k))
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c ≫ (pullback.snd A.inclusion B.inclusion).hom.hom, ?_⟩
    exact (Category.assoc _ _ _).trans (congrArg (c ≫ ·) h.w.symm) |>.trans
      (Category.assoc _ _ _).symm
  · rintro ⟨b, hb⟩
    exact ⟨h.lift a b hb.symm, h.lift_fst _ _ _⟩

private theorem subgroupIntersection_sections {M : GroupScheme k} (A B : ClosedSubgroup M)
    {Y : SchemeOver k} (g : Y ⟶ M.X) :
    g ∈ SubgroupSections (subgroupOfSubgroup A (subgroupPullback A B)) Y ↔
      g ∈ SubgroupSections A Y ∧ g ∈ SubgroupSections B Y := by
  constructor
  · intro hg
    change (∃ c : Y ⟶ (subgroupPullback A B).group.X,
      c ≫ (subgroupOfSubgroup A (subgroupPullback A B)).inclusion.hom.hom = g) at hg
    obtain ⟨c, rfl⟩ := hg
    let a := c ≫ (subgroupPullback A B).inclusion.hom.hom
    have ha : a ∈ SubgroupSections (subgroupPullback A B) Y := ⟨c, rfl⟩
    have hc : c ≫ (subgroupOfSubgroup A (subgroupPullback A B)).inclusion.hom.hom =
        a ≫ A.inclusion.hom.hom := (Category.assoc _ _ _).symm
    rw [hc]
    exact ⟨⟨a, rfl⟩, (subgroupPullback_sections A B a).mp ha⟩
  · rintro ⟨ha, hb⟩
    change (∃ a : Y ⟶ A.group.X, a ≫ A.inclusion.hom.hom = g) at ha
    obtain ⟨a, ha⟩ := ha
    have hab := (subgroupPullback_sections A B a).mpr (ha ▸ hb)
    change (∃ c : Y ⟶ (subgroupPullback A B).group.X,
      c ≫ (subgroupPullback A B).inclusion.hom.hom = a) at hab
    obtain ⟨c, hc⟩ := hab
    exact ⟨c, by
      change c ≫ (subgroupPullback A B).inclusion.hom.hom ≫ A.inclusion.hom.hom = g
      rw [← Category.assoc, hc, ha]⟩

private def appendCoordinates {T : ClosedSubgroup G.val} (U : RootSubgroupFamily T) :
    (l m : List (Root T)) →
    product (fun α ↦ (U α).val.group.X) l ⊗ product (fun α ↦ (U α).val.group.X) m ≅
    product (fun α ↦ (U α).val.group.X) (l ++ m)
  | [], _m => λ_ _
  | _α :: l, m => (α_ _ _ _) ≪≫ (Iso.refl _ ⊗ᵢ appendCoordinates U l m)

private theorem appendCoordinates_rootProduct {T : ClosedSubgroup G.val} (U : RootSubgroupFamily T)
    (l m : List (Root T)) :
    (appendCoordinates U l m).hom ≫ rootProduct U (l ++ m) =
      (fst _ _ ≫ rootProduct U l) * (snd _ _ ≫ rootProduct U m) := by
  induction l with
  | nil =>
    simp only [List.nil_append, appendCoordinates, rootProduct, product, leftUnitor_hom,
      MonObj.comp_one, one_mul]
  | cons α l ih =>
    let X := (U α).val.group.X
    let L := product (fun β ↦ (U β).val.group.X) l
    let M := product (fun β ↦ (U β).val.group.X) m
    let LM := product (fun β ↦ (U β).val.group.X) (l ++ m)
    let j : L ⊗ M ⟶ LM := (appendCoordinates U l m).hom
    change ((α_ X L M).hom ≫ (𝟙 X ⊗ₘ j)) ≫
        ((fst X LM ≫ (U α).val.inclusion.hom.hom) * (snd X LM ≫ rootProduct U (l ++ m))) =
      (fst (X ⊗ L) M ≫
        ((fst X L ≫ (U α).val.inclusion.hom.hom) * (snd X L ≫ rootProduct U l))) *
        (snd (X ⊗ L) M ≫ rootProduct U m)
    simp only [MonObj.comp_mul, Category.assoc, tensorHom_fst_assoc, tensorHom_snd_assoc,
      Category.id_comp, associator_hom_fst_assoc]
    rw [show j ≫ rootProduct U (l ++ m) =
      (fst L M ≫ rootProduct U l) * (snd L M ≫ rootProduct U m) from ih]
    simp only [MonObj.comp_mul, associator_hom_snd_fst_assoc, associator_hom_snd_snd_assoc, mul_assoc]

private theorem enumeratesAppend {I : Type u} {l m : List I} {S S' : Set I}
    (hl : Enumerates l S) (hm : Enumerates m S') (h : Disjoint S S') :
    Enumerates (l ++ m) (S ∪ S') := by
  constructor
  · rw [List.nodup_append]
    exact ⟨hl.1, hm.1, fun a ha b hb hab ↦
      Set.disjoint_left.mp h ((hl.2 a).mp ha) (hab ▸ (hm.2 b).mp hb)⟩
  · intro a
    simp only [List.mem_append, Set.mem_union, hl.2 a, hm.2 a]

private theorem existsEnumeration {I : Type u} [Finite I] (S : Set I) :
    ∃ l : List I, Enumerates l S := by
  classical
  let F := (Set.toFinite S).toFinset
  exact ⟨F.toList, F.nodup_toList, fun a ↦ (Finset.mem_toList).trans (Set.Finite.mem_toFinset _)⟩

private abbrev RootCoordinates {T : ClosedSubgroup G.val} (U : RootSubgroupFamily T)
    (l : List (Root T)) := product (fun α ↦ (U α).val.group.X) l

private def identityCoordinates {T : ClosedSubgroup G.val} (U : RootSubgroupFamily T)
    (Y : SchemeOver k) : (l : List (Root T)) → (Y ⟶ RootCoordinates U l)
  | [] => toUnit Y
  | α :: l => lift (1 : Y ⟶ (U α).val.group.X) (identityCoordinates U Y l)

private theorem identityCoordinates_mul {T : ClosedSubgroup G.val} (U : RootSubgroupFamily T)
    (Y : SchemeOver k) (l : List (Root T)) :
    identityCoordinates U Y l ≫ rootProduct U l = 1 := by
  induction l with
  | nil =>
    change toUnit Y ≫ (1 : 𝟙_ (SchemeOver k) ⟶ G.val.X) = 1
    exact MonObj.comp_one _
  | cons α l ih =>
    simp only [identityCoordinates, rootProduct, MonObj.comp_mul, lift_fst_assoc,
      lift_snd_assoc, MonObj.one_comp, ih, mul_one]

private theorem rootCoordinatesRange {T : ClosedSubgroup G.val} {U : RootSubgroupFamily T}
    {l : List (Root T)} {H : ClosedSubgroup G.val}
    (h : Parametrizes U l H.inclusion.hom.hom) (Y : SchemeOver k) (g : Y ⟶ G.val.X) :
    (∃ x : Y ⟶ RootCoordinates U l, x ≫ rootProduct U l = g) ↔
      g ∈ SubgroupSections H Y := by
  obtain ⟨e, he⟩ := h
  change _ ↔ ∃ b : Y ⟶ H.group.X, b ≫ H.inclusion.hom.hom = g
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x ≫ e.hom, by rw [Category.assoc, he, hx]⟩
  · rintro ⟨b, hb⟩
    exact ⟨b ≫ e.inv, by rw [Category.assoc, ← he, e.inv_hom_id_assoc, hb]⟩

private theorem orderedProductMono {T : ClosedSubgroup G.val} {U : RootSubgroupFamily T}
    {l : List (Root T)} {H : ClosedSubgroup G.val}
    (h : Parametrizes U l H.inclusion.hom.hom) : Mono (rootProduct U l) := by
  obtain ⟨e, he⟩ := h
  rw [← he]
  have := monoSubgroup H
  infer_instance

private theorem rootProductSubset {T : ClosedSubgroup G.val} [Finite (Root T)]
    {U : RootSubgroupFamily T} {l : List (Root T)} {S S' : Set (Root T)}
    {H : ClosedSubgroup G.val} (hl : Enumerates l S) (hs : S ⊆ S')
    (hp : OrderedParametrization U S' H) :
    rootProduct U l ∈ SubgroupSections H (RootCoordinates U l) := by
  obtain ⟨m, hm⟩ := existsEnumeration (S' \ S)
  have hd : Disjoint S (S' \ S) := Set.disjoint_left.mpr (fun _ ha hb ↦ hb.2 ha)
  have hu : S ∪ (S' \ S) = S' := by
    ext α
    constructor
    · rintro (h | h)
      · exact hs h
      · exact h.1
    · intro h
      by_cases ha : α ∈ S
      · exact Or.inl ha
      · exact Or.inr ⟨h, ha⟩
  have h := hp (l ++ m) (hu ▸ enumeratesAppend hl hm hd)
  apply (rootCoordinatesRange h _ _).mp
  refine ⟨lift (𝟙 _) (identityCoordinates U _ m) ≫ (appendCoordinates U l m).hom, ?_⟩
  simp only [Category.assoc, appendCoordinates_rootProduct, MonObj.comp_mul, lift_fst_assoc,
    lift_snd_assoc, Category.id_comp, identityCoordinates_mul, mul_one]

private theorem parametrizes_of_range {T : ClosedSubgroup G.val}
    {U : RootSubgroupFamily T} (l : List (Root T)) (H : ClosedSubgroup G.val)
    (hm : Mono (rootProduct U l))
    (hr : ∀ (Y : SchemeOver k) (g : Y ⟶ G.val.X),
      (∃ x : Y ⟶ RootCoordinates U l, x ≫ rootProduct U l = g) ↔
        g ∈ SubgroupSections H Y) :
    Parametrizes U l H.inclusion.hom.hom := by
  have h := (hr _ _).mp ⟨𝟙 _, Category.id_comp _⟩
  change ∃ r : RootCoordinates U l ⟶ H.group.X,
    r ≫ H.inclusion.hom.hom = rootProduct U l at h
  obtain ⟨r, hr'⟩ := h
  have hi := monoSubgroup H
  have : IsIso r := by
    apply isIso_of_yoneda_map_bijective
    intro Y
    constructor
    · intro x x' hx
      exact (cancel_mono (rootProduct U l)).mp (by
        simpa only [← hr', ← Category.assoc] using congrArg (· ≫ H.inclusion.hom.hom) hx)
    · intro b
      obtain ⟨x, hx⟩ := (hr Y (b ≫ H.inclusion.hom.hom)).mpr ⟨b, rfl⟩
      exact ⟨x, (cancel_mono H.inclusion.hom.hom).mp (by rwa [Category.assoc, hr'])⟩
  exact ⟨asIso r, hr'⟩

section GroupFactors

variable {M : Type*} [Group M]

/-- A factor in the opposite radical cannot occur in the positive parabolic.
The uniqueness hypothesis comes from the multiplication chart. -/
private theorem rootSliceIntersection (N L P R : Subgroup M) (A V : Set M)
    (ha : A ⊆ N) (hv : V ⊆ P)
    (hrad : ∀ g : M, g ∈ R ↔ ∃ a ∈ A, ∃ v ∈ V, a * v = g)
    (ha1 : (1 : M) ∈ A) (hv1 : (1 : M) ∈ V)
    (hu : ∀ (n t p n' t' p' : M), n ∈ N → t ∈ L → p ∈ P →
      n' ∈ N → t' ∈ L → p' ∈ P → n * (t * p) = n' * (t' * p') →
      n = n' ∧ t = t' ∧ p = p') :
    (∀ g : M, g ∈ A ↔ g ∈ R ∧ g ∈ N) ∧
      (∀ g : M, g ∈ V ↔ g ∈ R ∧ g ∈ P) := by
  constructor
  · intro g
    constructor
    · intro hg
      exact ⟨(hrad g).mpr ⟨g, hg, 1, hv1, mul_one _⟩, ha hg⟩
    · rintro ⟨hr, hn⟩
      obtain ⟨a, hA, v, hV, h⟩ := (hrad g).mp hr
      exact (hu a 1 v g 1 1 (ha hA) L.one_mem (hv hV) hn L.one_mem P.one_mem (by simpa)).1 ▸ hA
  · intro g
    constructor
    · intro hg
      exact ⟨(hrad g).mpr ⟨1, ha1, g, hg, one_mul _⟩, hv hg⟩
    · rintro ⟨hr, hp⟩
      obtain ⟨a, hA, v, hV, h⟩ := (hrad g).mp hr
      exact (hu a 1 v 1 1 g (ha hA) L.one_mem (hv hV) N.one_mem L.one_mem hp (by simpa)).2.2 ▸ hV

private theorem borelSliceIntersection (N L P R B B' : Subgroup M) (A V : Set M)
    (ha : A ⊆ N) (hv : V ⊆ P) (ha1 : (1 : M) ∈ A)
    (hn : ∀ t ∈ L, ∀ n ∈ N, t * n * t⁻¹ ∈ N)
    (hrad : ∀ g : M, g ∈ R ↔ ∃ a ∈ A, ∃ v ∈ V, a * v = g)
    (hb : ∀ g : M, g ∈ B ↔ ∃ t ∈ L, ∃ r ∈ R, t * r = g)
    (hb' : ∀ g : M, g ∈ B' ↔ ∃ t ∈ L, ∃ p ∈ P, t * p = g)
    (hu : ∀ (n t p n' t' p' : M), n ∈ N → t ∈ L → p ∈ P →
      n' ∈ N → t' ∈ L → p' ∈ P → n * (t * p) = n' * (t' * p') →
      n = n' ∧ t = t' ∧ p = p') :
    ∀ g : M, (g ∈ B ∧ g ∈ B') ↔ ∃ t ∈ L, ∃ v ∈ V, t * v = g := by
  intro g
  constructor
  · rintro ⟨hg, hg'⟩
    obtain ⟨t, ht, r, hr, hr'⟩ := (hb g).mp hg
    obtain ⟨a, hA, v, hV, hv'⟩ := (hrad r).mp hr
    obtain ⟨t', ht', p, hp, hp'⟩ := (hb' g).mp hg'
    have h : (t * a * t⁻¹) * (t * v) = 1 * (t' * p) := by
      rw [one_mul, hp', ← hr', ← hv']
      group
    have ha' : t * a * t⁻¹ = 1 :=
      (hu _ _ _ _ _ _ (hn t ht a (ha hA)) ht (hv hV) N.one_mem ht' hp h).1
    rw [ha', one_mul, hp'] at h
    exact ⟨t, ht, v, hV, by simpa only [one_mul] using h⟩
  · rintro ⟨t, ht, v, hV, rfl⟩
    exact ⟨(hb _).mpr ⟨t, ht, v, (hrad _).mpr ⟨1, ha1, v, hV, one_mul _⟩, rfl⟩,
      (hb' _).mpr ⟨t, ht, v, hv hV, rfl⟩⟩

end GroupFactors

private def rootProductRange {T : ClosedSubgroup G.val} (U : RootSubgroupFamily T)
    (l : List (Root T)) (Y : SchemeOver k) : Set (Y ⟶ G.val.X) :=
  Set.range (fun x : Y ⟶ RootCoordinates U l ↦ x ≫ rootProduct U l)

private theorem mul_rootProductRange {T : ClosedSubgroup G.val} {U : RootSubgroupFamily T}
    {l m : List (Root T)} {H : ClosedSubgroup G.val}
    (h : Parametrizes U (l ++ m) H.inclusion.hom.hom) (Y : SchemeOver k) (g : Y ⟶ G.val.X) :
    g ∈ SubgroupSections H Y ↔
      ∃ a ∈ rootProductRange U l Y, ∃ v ∈ rootProductRange U m Y, a * v = g := by
  rw [← rootCoordinatesRange h]
  constructor
  · rintro ⟨y, hy⟩
    let x := y ≫ (appendCoordinates U l m).inv
    refine ⟨x ≫ fst _ _ ≫ rootProduct U l, ⟨x ≫ fst _ _, Category.assoc _ _ _⟩,
      x ≫ snd _ _ ≫ rootProduct U m, ⟨x ≫ snd _ _, Category.assoc _ _ _⟩, ?_⟩
    have hx : x ≫ (appendCoordinates U l m).hom ≫ rootProduct U (l ++ m) = g := by
      dsimp only [x]
      rw [Category.assoc, Iso.inv_hom_id_assoc, hy]
    simpa only [appendCoordinates_rootProduct, MonObj.comp_mul] using hx
  · rintro ⟨_, ⟨a, rfl⟩, _, ⟨v, rfl⟩, hmul⟩
    refine ⟨lift a v ≫ (appendCoordinates U l m).hom, ?_⟩
    simpa only [Category.assoc, appendCoordinates_rootProduct, MonObj.comp_mul, lift_fst_assoc,
      lift_snd_assoc] using hmul

private theorem rootProductRange_mono {T : ClosedSubgroup G.val} {U : RootSubgroupFamily T}
    {l m : List (Root T)} (h : Mono (rootProduct U (l ++ m))) :
    Mono (rootProduct U l) ∧ Mono (rootProduct U m) := by
  constructor
  · constructor
    intro Y a b eq
    let N := identityCoordinates U Y m
    have hc : (lift a N ≫ (appendCoordinates U l m).hom) ≫ rootProduct U (l ++ m) =
        (lift b N ≫ (appendCoordinates U l m).hom) ≫ rootProduct U (l ++ m) := by
      simpa only [Category.assoc, appendCoordinates_rootProduct, MonObj.comp_mul, lift_fst_assoc,
        lift_snd_assoc, N, identityCoordinates_mul, mul_one] using eq
    have he := (cancel_mono (appendCoordinates U l m).hom).mp
      ((cancel_mono (rootProduct U (l ++ m))).mp hc)
    simpa only [lift_fst] using congrArg (· ≫ fst _ _) he
  · constructor
    intro Y a b eq
    let N := identityCoordinates U Y l
    have hc : (lift N a ≫ (appendCoordinates U l m).hom) ≫ rootProduct U (l ++ m) =
        (lift N b ≫ (appendCoordinates U l m).hom) ≫ rootProduct U (l ++ m) := by
      simpa only [Category.assoc, appendCoordinates_rootProduct, MonObj.comp_mul, lift_fst_assoc,
        lift_snd_assoc, N, identityCoordinates_mul, one_mul] using eq
    have he := (cancel_mono (appendCoordinates U l m).hom).mp
      ((cancel_mono (rootProduct U (l ++ m))).mp hc)
    simpa only [lift_snd] using congrArg (· ≫ snd _ _) he

private theorem rootCell_unique {T : ClosedSubgroup G.val} {U : RootSubgroupFamily T}
    (l m : List (Root T)) (N P : ClosedSubgroup G.val)
    (hN : Parametrizes U l N.inclusion.hom.hom) (hP : Parametrizes U m P.inclusion.hom.hom)
    (hm : Mono (OrderedRootProducts.rootCellMap T U l m)) (Y : SchemeOver k)
    (n t p n' t' p' : Y ⟶ G.val.X)
    (hn : n ∈ SubgroupSections N Y) (ht : t ∈ SubgroupSections T Y)
    (hp : p ∈ SubgroupSections P Y) (hn' : n' ∈ SubgroupSections N Y)
    (ht' : t' ∈ SubgroupSections T Y) (hp' : p' ∈ SubgroupSections P Y)
    (he : n * (t * p) = n' * (t' * p')) :
    n = n' ∧ t = t' ∧ p = p' := by
  obtain ⟨a, ha⟩ := (rootCoordinatesRange hN Y n).mpr hn
  obtain ⟨a', ha'⟩ := (rootCoordinatesRange hN Y n').mpr hn'
  obtain ⟨b, hb⟩ := (rootCoordinatesRange hP Y p).mpr hp
  obtain ⟨b', hb'⟩ := (rootCoordinatesRange hP Y p').mpr hp'
  change (∃ s : Y ⟶ T.group.X, s ≫ T.inclusion.hom.hom = t) at ht
  change (∃ s : Y ⟶ T.group.X, s ≫ T.inclusion.hom.hom = t') at ht'
  obtain ⟨s, hs⟩ := ht
  obtain ⟨s', hs'⟩ := ht'
  have e : lift a (lift s b) = lift a' (lift s' b') := by
    apply (cancel_mono (OrderedRootProducts.rootCellMap T U l m)).mp
    simpa only [OrderedRootProducts.rootCellMap, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
      ha, ha', hb, hb', hs, hs'] using he
  have ea : a = a' := by simpa only [lift_fst] using congrArg (· ≫ fst _ _) e
  have esb : lift s b = lift s' b' := by simpa only [lift_snd] using congrArg (· ≫ snd _ _) e
  have es : s = s' := by simpa only [lift_fst] using congrArg (· ≫ fst _ _) esb
  have eb : b = b' := by simpa only [lift_snd] using congrArg (· ≫ snd _ _) esb
  exact ⟨ha.symm.trans (ea ▸ ha'), hs.symm.trans (es ▸ hs'), hb.symm.trans (eb ▸ hb')⟩

open Specs.AdjointRepresentation (GroupPoints)
open LinearAlgebraicGroups.CocharacterDynamics
  (HasLimit LimitDecomposition RepresentsOnAlgebras cocharacterPoint oppositeCocharacter
    polynomialAlgebra polynomialToLaurent polynomialEvaluate laurentAlgebra laurentParameter
    laurentConstants orbit unitPoint)

private theorem cocharacterPoint_comp {H M : GroupScheme k} (c : Cocharacter H)
    (f : H ⟶ M) (R : TestAlgebra k) (s : Rˣ) :
    cocharacterPoint (c ≫ f) R s = cocharacterPoint c R s ≫ f.hom.hom := by
  change (unitPoint R s ≫ c.hom.hom ≫ f.hom.hom) =
    (unitPoint R s ≫ c.hom.hom) ≫ f.hom.hom
  exact (Category.assoc _ _ _).symm

private theorem mapPoints_hom {H M : GroupScheme k} (f : H ⟶ M)
    {R S : TestAlgebra k} (a : R ⟶ S) (g : GroupPoints H R) :
    mapPoints a (g ≫ f.hom.hom) = (mapPoints a g) ≫ f.hom.hom :=
  (Category.assoc _ _ _).symm

private theorem hasLimit_hom {H M : GroupScheme k} (f : H ⟶ M) {c : Cocharacter H}
    {R : TestAlgebra k} {g z : GroupPoints H R} (h : HasLimit c g z) :
    HasLimit (c ≫ f) (g ≫ f.hom.hom) (z ≫ f.hom.hom) := by
  obtain ⟨a, ha, hz⟩ := h
  refine ⟨a ≫ f.hom.hom, ?_, ?_⟩
  · rw [mapPoints_hom, ha]
    simp only [orbit, cocharacterPoint_comp, mapPoints_hom]
    let t : Points H.X (laurentAlgebra R) :=
      cocharacterPoint c (laurentAlgebra R) (laurentParameter R)
    let p : Points H.X (laurentAlgebra R) := mapPoints (laurentConstants R) g
    change (t * p * t⁻¹) ≫ f.hom.hom =
      (t ≫ f.hom.hom) * (p ≫ f.hom.hom) * (t ≫ f.hom.hom)⁻¹
    simp only [MonObj.mul_comp, GrpObj.inv_comp]
  · rw [mapPoints_hom, hz]

private theorem hasLimit_iso {H M : GroupScheme k} (e : H ≅ M) (c : Cocharacter H)
    {R : TestAlgebra k} (g : GroupPoints H R) :
    HasLimit (c ≫ e.hom) (g ≫ e.hom.hom.hom) 1 ↔ HasLimit c g 1 := by
  constructor
  · intro h
    have hh := hasLimit_hom e.inv h
    have hh₁ : (c ≫ e.hom) ≫ e.inv = c := by simp
    have hh₂ : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 H.X :=
      congrArg (Grp.forget (SchemeOver k)).map e.hom_inv_id
    simpa only [hh₁, Category.assoc, hh₂, Category.comp_id, MonObj.one_comp] using hh
  · intro h
    simpa only [MonObj.one_comp] using hasLimit_hom e.hom h

private theorem splitRadicalByChambers {T : ClosedSubgroup G.val} [Finite (Root T)]
    (U : RootSubgroupFamily T) (R N P : ClosedSubgroup G.val)
    (S Sneg Spos : Set (Root T)) (hcover : Sneg ∪ Spos = Set.univ)
    (hdisjoint : Disjoint Sneg Spos)
    (hR : OrderedParametrization U S R) (hN : OrderedParametrization U Sneg N)
    (hP : OrderedParametrization U Spos P)
    (hchart : ∀ l m, Enumerates l Sneg → Enumerates m Spos →
      Mono (OrderedRootProducts.rootCellMap T U l m)) :
    OrderedParametrization U (S ∩ Sneg) (subgroupOfSubgroup R (subgroupPullback R N)) ∧
    OrderedParametrization U (S ∩ Spos) (subgroupOfSubgroup R (subgroupPullback R P)) := by
  obtain ⟨neg, hneg⟩ := existsEnumeration Sneg
  obtain ⟨pos, hpos⟩ := existsEnumeration Spos
  have hu := rootCell_unique neg pos N P (hN neg hneg) (hP pos hpos)
    (hchart neg pos hneg hpos)
  have hp {l m} (hl : Enumerates l (S ∩ Sneg)) (hm : Enumerates m (S ∩ Spos)) :
      Mono (rootProduct U l) ∧ Mono (rootProduct U m) ∧
      ∀ Y : SchemeOver k,
        (∀ g : Y ⟶ G.val.X, g ∈ rootProductRange U l Y ↔
          g ∈ SubgroupSections R Y ∧ g ∈ SubgroupSections N Y) ∧
        (∀ g : Y ⟶ G.val.X, g ∈ rootProductRange U m Y ↔
          g ∈ SubgroupSections R Y ∧ g ∈ SubgroupSections P Y) := by
    have hd : Disjoint (S ∩ Sneg) (S ∩ Spos) :=
      Set.disjoint_left.mpr (fun _ h₁ h₂ ↦ Set.disjoint_left.mp hdisjoint h₁.2 h₂.2)
    have hS : (S ∩ Sneg) ∪ (S ∩ Spos) = S := by
      rw [← Set.inter_union_distrib_left, hcover, Set.inter_univ]
    have hprod := hR (l ++ m) (hS ▸ enumeratesAppend hl hm hd)
    have hmono := rootProductRange_mono (orderedProductMono hprod)
    refine ⟨hmono.1, hmono.2, fun Y ↦ ?_⟩
    apply rootSliceIntersection (SubgroupSections N Y) (SubgroupSections T Y)
      (SubgroupSections P Y) (SubgroupSections R Y)
      (rootProductRange U l Y) (rootProductRange U m Y)
    · rintro _ ⟨x, rfl⟩
      exact memSubgroup_comp x (rootProductSubset hl Set.inter_subset_right hN)
    · rintro _ ⟨x, rfl⟩
      exact memSubgroup_comp x (rootProductSubset hm Set.inter_subset_right hP)
    · exact mul_rootProductRange hprod Y
    · exact ⟨identityCoordinates U Y l, identityCoordinates_mul U Y l⟩
    · exact ⟨identityCoordinates U Y m, identityCoordinates_mul U Y m⟩
    · exact hu Y
  constructor
  · intro l hl
    obtain ⟨m, hm⟩ := existsEnumeration (S ∩ Spos)
    obtain ⟨hmono, _, hr⟩ := hp hl hm
    apply parametrizes_of_range l _ hmono
    intro Y g
    exact ((hr Y).1 g).trans (subgroupIntersection_sections R N g).symm
  · intro m hm
    obtain ⟨l, hl⟩ := existsEnumeration (S ∩ Sneg)
    obtain ⟨_, hmono, hr⟩ := hp hl hm
    apply parametrizes_of_range m _ hmono
    intro Y g
    exact ((hr Y).2 g).trans (subgroupIntersection_sections R P g).symm

private theorem multiplySlices {T : ClosedSubgroup G.val}
    {U : RootSubgroupFamily T} {R N P : ClosedSubgroup G.val} {l m : List (Root T)}
    (hR : Parametrizes U (l ++ m) R.inclusion.hom.hom)
    (hN : Parametrizes U l
      (subgroupOfSubgroup R (subgroupPullback R N)).inclusion.hom.hom)
    (hP : Parametrizes U m
      (subgroupOfSubgroup R (subgroupPullback R P)).inclusion.hom.hom) :
    IsIso (multiplyFactors (subgroupPullback R N).inclusion (subgroupPullback R P).inclusion) := by
  let i := (subgroupPullback R N).inclusion
  let j := (subgroupPullback R P).inclusion
  change (∃ e : RootCoordinates U l ≅ (subgroupPullback R N).group.X,
    e.hom ≫ i.hom.hom ≫ R.inclusion.hom.hom = rootProduct U l) at hN
  change (∃ e : RootCoordinates U m ≅ (subgroupPullback R P).group.X,
    e.hom ≫ j.hom.hom ≫ R.inclusion.hom.hom = rootProduct U m) at hP
  obtain ⟨e, he⟩ := hR
  obtain ⟨eN, heN⟩ := hN
  obtain ⟨eP, heP⟩ := hP
  let f := multiplyFactors i j
  have hi := monoSubgroup R
  have hE : (eN ⊗ᵢ eP).hom ≫ f = ((appendCoordinates U l m) ≪≫ e).hom := by
    apply (cancel_mono R.inclusion.hom.hom).mp
    change (eN.hom ⊗ₘ eP.hom) ≫ ((fst _ _ ≫ i.hom.hom) * (snd _ _ ≫ j.hom.hom)) ≫
      R.inclusion.hom.hom = (appendCoordinates U l m).hom ≫ e.hom ≫ R.inclusion.hom.hom
    simp only [Category.assoc, MonObj.mul_comp, MonObj.comp_mul, tensorHom_fst_assoc,
      tensorHom_snd_assoc, heN, heP, he, appendCoordinates_rootProduct]
  have : IsIso ((eN ⊗ᵢ eP).hom ≫ f) := by rw [hE]; infer_instance
  exact IsIso.of_isIso_comp_left (eN ⊗ᵢ eP).hom f


open Specs.GeometricRadicals (IsUnipotentRadical)
open Specs.RankOneFlag (SameSubgroup)

private theorem sameSubgroup_of_sections {M : GroupScheme k} (A B : ClosedSubgroup M)
    (h : ∀ (Y : SchemeOver k) (g : Y ⟶ M.X),
      g ∈ SubgroupSections A Y ↔ g ∈ SubgroupSections B Y) :
    SameSubgroup A B := by
  constructor
  · apply subgroupFactorThrough
    apply (h _ _).mp
    change ∃ f : A.group.X ⟶ A.group.X, f ≫ A.inclusion.hom.hom = A.inclusion.hom.hom
    exact ⟨𝟙 _, Category.id_comp _⟩
  · apply subgroupFactorThrough
    apply (h _ _).mpr
    change ∃ f : B.group.X ⟶ B.group.X, f ≫ B.inclusion.hom.hom = B.inclusion.hom.hom
    exact ⟨𝟙 _, Category.id_comp _⟩

private theorem regularBorelContracting
    (hContract : Specs.OrderedRootProducts.ContractingProduct.{u})
    (hG : IsReductive G) {T B : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    (D : Datum T) (hT : IsSplitTorus T.group) (hmax : IsGeometricallyMaximal T)
    (U : RootSubgroupFamily T) (R : ClosedSubgroup B.group)
    (hR : OrderedParametrization U (subgroupRoots T B) (subgroupOfSubgroup B R))
    (hpos : IsPositiveSystem T (subgroupRoots T B)) :
    ∃ (c : Cocharacter T.group) (L : LimitDecomposition (c ≫ T.inclusion)),
      IsRegular T c ∧ positiveRoots T c = subgroupRoots T B ∧
      SameSubgroup (subgroupOfSubgroup B R) L.contracting := by
  have : Finite (Root T) := D.finiteRoots
  obtain ⟨c, hc, hchamber⟩ := integralChamber D hpos
  obtain ⟨⟨L⟩, hL⟩ := (hContract G hG T hT hmax).2.2 c
  obtain ⟨l, hl⟩ := existsEnumeration (subgroupRoots T B)
  refine ⟨c, L, hc, hchamber, sameSubgroup_of_sections _ _ ?_⟩
  intro Y g
  exact (rootCoordinatesRange (hR l hl) Y g).symm.trans
    (rootCoordinatesRange (hL L U l (hchamber.symm ▸ hl)) Y g)

private theorem existsOppositeBorel {T B : ClosedSubgroup G.val}
    (hB : IsKBorel B) (hTB : IsSubgroupOf T B) (hCorr : BorelCorrespondence T) :
    ∃ Bneg : ClosedSubgroup G.val, IsKBorel Bneg ∧ IsSubgroupOf T Bneg ∧
      subgroupRoots T Bneg = (subgroupRoots T B)ᶜ :=
  hCorr.2.1 _ (oppositePositiveSystem (hCorr.1 B hB hTB))

open private opposite_point unitEquiv unitPointHom_apply
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

private theorem oppositeCocharacter_eq_inv {M : GroupScheme k} [IsCommMonObj M.X]
    (c : Cocharacter M) : oppositeCocharacter c = c⁻¹ := by
  apply (groupHomComparison k _ _
    (inferInstanceAs (IsAffine (Spec (CommRingCat.of
      (MonoidAlgebra k DiagonalizableGroups.IntegerCharacters)))))).1
  ext R p
  have hp : unitPoint R (unitEquiv R p) = p := by
    rw [← unitPointHom_apply]
    exact (unitEquiv R).symm_apply_apply p
  change p ≫ (oppositeCocharacter c).hom.hom = p ≫ (c⁻¹).hom.hom
  rw [← hp]
  change cocharacterPoint (oppositeCocharacter c) R (unitEquiv R p) = _
  rw [opposite_point, Grp.Hom.hom_hom_inv, GrpObj.comp_inv]
  have hu : unitPoint R (unitEquiv R p)⁻¹ = (unitPoint R (unitEquiv R p))⁻¹ := by
    simp only [← unitPointHom_apply, map_inv]
  change unitPoint R (unitEquiv R p)⁻¹ ≫ c.hom.hom =
    (unitPoint R (unitEquiv R p) ≫ c.hom.hom)⁻¹
  rw [hu, GrpObj.inv_comp]

private theorem positiveRoots_opposite {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    (D : Datum T) {c : Cocharacter T.group} (hc : IsRegular T c) :
    positiveRoots T (oppositeCocharacter c) = (positiveRoots T c)ᶜ := by
  ext α
  change 0 < CharacterPairing.pairing T.group α.val (oppositeCocharacter c) ↔
    ¬ 0 < CharacterPairing.pairing T.group α.val c
  have h : CharacterPairing.pairing T.group α.val (oppositeCocharacter c) =
      -CharacterPairing.pairing T.group α.val c := by
    rw [← D.pairing_eq, ← D.pairing_eq, oppositeCocharacter_eq_inv]
    change D.rootDatum.toLinearMap (Additive.ofMul α.val) (-Additive.ofMul c) = _
    exact map_neg _ _
  rw [h, neg_pos, not_lt]
  exact (lt_iff_le_and_ne).trans ⟨And.left, fun h ↦ ⟨h, hc α⟩⟩

private theorem productSections {M : GroupScheme k} {A H B : ClosedSubgroup M}
    (i : A.group ⟶ B.group) (j : H.group ⟶ B.group)
    (hi : i ≫ B.inclusion = A.inclusion) (hj : j ≫ B.inclusion = H.inclusion)
    (h : IsIso (multiplyFactors i j))
    (Y : SchemeOver k) (g : Y ⟶ M.X) :
    g ∈ SubgroupSections B Y ↔
      ∃ a ∈ SubgroupSections A Y, ∃ s ∈ SubgroupSections H Y, a * s = g := by
  let f := multiplyFactors i j
  have hi' := congrArg (Grp.forget (SchemeOver k)).map hi
  have hj' := congrArg (Grp.forget (SchemeOver k)).map hj
  have hmul (x : Y ⟶ A.group.X ⊗ H.group.X) :
      x ≫ f ≫ B.inclusion.hom.hom =
        (x ≫ fst _ _ ≫ A.inclusion.hom.hom) * (x ≫ snd _ _ ≫ H.inclusion.hom.hom) := by
    change i.hom.hom ≫ B.inclusion.hom.hom = A.inclusion.hom.hom at hi'
    change j.hom.hom ≫ B.inclusion.hom.hom = H.inclusion.hom.hom at hj'
    simp only [f, multiplyFactors, MonObj.comp_mul, MonObj.mul_comp, Category.assoc, hi', hj']
  constructor
  · intro hg
    change (∃ b : Y ⟶ B.group.X, b ≫ B.inclusion.hom.hom = g) at hg
    obtain ⟨b, hb⟩ := hg
    let x := b ≫ inv f
    refine ⟨x ≫ fst _ _ ≫ A.inclusion.hom.hom, ⟨x ≫ fst _ _, ?_⟩,
      x ≫ snd _ _ ≫ H.inclusion.hom.hom, ⟨x ≫ snd _ _, ?_⟩, ?_⟩
    · change (x ≫ fst _ _) ≫ A.inclusion.hom.hom = _
      exact Category.assoc _ _ _
    · change (x ≫ snd _ _) ≫ H.inclusion.hom.hom = _
      exact Category.assoc _ _ _
    · rw [← hmul]
      change (b ≫ inv f) ≫ f ≫ B.inclusion.hom.hom = g
      rw [Category.assoc, IsIso.inv_hom_id_assoc, hb]
  · rintro ⟨t, ht, r, hr, rfl⟩
    change (∃ a : Y ⟶ A.group.X, a ≫ A.inclusion.hom.hom = t) at ht
    change (∃ b : Y ⟶ H.group.X, b ≫ H.inclusion.hom.hom = r) at hr
    obtain ⟨a, rfl⟩ := ht
    obtain ⟨b, rfl⟩ := hr
    refine ⟨lift a b ≫ f, ?_⟩
    change (lift a b ≫ f) ≫ B.inclusion.hom.hom = _
    rw [Category.assoc, hmul, lift_fst_assoc, lift_snd_assoc]

private theorem borelSections {T B : ClosedSubgroup G.val} (R : ClosedSubgroup B.group)
    (j : T.group ⟶ B.group) (hj : j ≫ B.inclusion = T.inclusion)
    (h : IsIso (multiplyFactors j R.inclusion))
    (Y : SchemeOver k) (g : Y ⟶ G.val.X) :
    g ∈ SubgroupSections B Y ↔
      ∃ t ∈ SubgroupSections T Y, ∃ r ∈ SubgroupSections (subgroupOfSubgroup B R) Y,
        t * r = g :=
  productSections (B := B) (A := T) (H := subgroupOfSubgroup B R) j R.inclusion hj rfl h Y g

section BorelSections

variable {M : Type*} [Group M]

private theorem uniqueMul_of_trivialIntersection (A H : Subgroup M)
    (h : ∀ x ∈ A, x ∈ H → x = 1)
    {a a' s s' : M} (ha : a ∈ A) (ha' : a' ∈ A) (hs : s ∈ H) (hs' : s' ∈ H)
    (he : a * s = a' * s') : a = a' ∧ s = s' := by
  have hh : a'⁻¹ * a = s' * s⁻¹ := by
    calc
      a'⁻¹ * a = a'⁻¹ * (a * s) * s⁻¹ := by group
      _ = s' * s⁻¹ := by rw [he, inv_mul_cancel_left]
  have h1 := h _ (A.mul_mem (A.inv_mem ha') ha) (hh.symm ▸ H.mul_mem hs' (H.inv_mem hs))
  have he' : a = a' := (inv_mul_eq_one.mp h1).symm
  exact ⟨he', mul_left_cancel (he' ▸ he)⟩

private theorem borelOrbitFactors (A V L R B H : Subgroup M)
    (hB : ∀ b ∈ B, ∃ t ∈ L, ∃ r ∈ R, t * r = b)
    (hR : ∀ r ∈ R, ∃ a ∈ A, ∃ v ∈ V, a * v = r)
    (hH : ∀ t ∈ L, ∀ v ∈ V, t * v ∈ H)
    (hN : ∀ t ∈ L, ∀ a ∈ A, t * a * t⁻¹ ∈ A) :
    ∀ b ∈ B, ∃ a ∈ A, ∃ h ∈ H, a * h = b := by
  intro b hb
  obtain ⟨t, ht, r, hr, htr⟩ := hB b hb
  obtain ⟨a, ha, v, hv, hav⟩ := hR r hr
  refine ⟨t * a * t⁻¹, hN t ht a ha, t * v, hH t ht v hv, ?_⟩
  rw [← htr, ← hav]
  group

private theorem torusFactor_normalCoordinates (N L P R B H A V : Subgroup M)
    (hneg : A ≤ N) (hpos : V ≤ P)
    (hrad : ∀ g : M, g ∈ R ↔ ∃ a ∈ A, ∃ v ∈ V, a * v = g)
    (hH : ∀ g : M, g ∈ H ↔ ∃ t ∈ L, ∃ v ∈ V, t * v = g)
    (hB : H ≤ B) (hnorm : ∀ b ∈ B, ∀ r ∈ R, b * r * b⁻¹ ∈ R)
    (hu : ∀ (n t p n' t' p' : M), n ∈ N → t ∈ L → p ∈ P →
      n' ∈ N → t' ∈ L → p' ∈ P → n * (t * p) = n' * (t' * p') →
      n = n' ∧ t = t' ∧ p = p') :
    (∀ a ∈ A, a ∈ H → a = 1) ∧ (∀ h ∈ H, ∀ v ∈ V, h * v * h⁻¹ ∈ V) := by
  constructor
  · intro a ha hh
    obtain ⟨t, ht, v, hv, rfl⟩ := (hH a).mp hh
    exact (hu (t * v) 1 1 1 t v (hneg ha) L.one_mem P.one_mem N.one_mem ht (hpos hv)
      (by simp)).1
  · intro h hh v hv
    have hvR : v ∈ R := (hrad v).mpr ⟨1, A.one_mem, v, hv, one_mul _⟩
    have hvH : v ∈ H := (hH v).mpr ⟨1, L.one_mem, v, hv, one_mul _⟩
    have h' := H.mul_mem (H.mul_mem hh hvH) (H.inv_mem hh)
    have h'' := hnorm h (hB hh) v hvR
    obtain ⟨t, ht, u, huV, htu⟩ := (hH _).mp h'
    obtain ⟨a, ha, v', hv', hav⟩ := (hrad _).mp h''
    have e : a * (1 * v') = 1 * (t * u) := by simpa only [one_mul] using hav.trans htu.symm
    have hT := (hu a 1 v' 1 t u (hneg ha) L.one_mem (hpos hv') N.one_mem ht (hpos huV) e).2.1
    rwa [← htu, ← hT, one_mul]

end BorelSections

private theorem isIso_multiplyFactors_of_sections {A H M : GroupScheme k}
    (i : A ⟶ M) (j : H ⟶ M)
    (hinj : ∀ (Y : SchemeOver k) (a a' : Y ⟶ A.X) (h h' : Y ⟶ H.X),
      (a ≫ i.hom.hom) * (h ≫ j.hom.hom) = (a' ≫ i.hom.hom) * (h' ≫ j.hom.hom) →
        a = a' ∧ h = h')
    (hsurj : ∀ (Y : SchemeOver k) (g : Y ⟶ M.X),
      ∃ (a : Y ⟶ A.X) (h : Y ⟶ H.X), (a ≫ i.hom.hom) * (h ≫ j.hom.hom) = g) :
    IsIso (multiplyFactors i j) := by
  apply isIso_of_yoneda_map_bijective
  intro Y
  constructor
  · intro a b hab
    have he := hinj Y (a ≫ fst _ _) (b ≫ fst _ _) (a ≫ snd _ _) (b ≫ snd _ _)
      (by simpa only [multiplyFactors, MonObj.comp_mul, Category.assoc] using hab)
    exact CartesianMonoidalCategory.hom_ext _ _ he.1 he.2
  · intro g
    obtain ⟨a, h, hg⟩ := hsurj Y g
    exact ⟨lift a h, by
      simpa only [multiplyFactors, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc] using hg⟩

private theorem sectionProductIso {M : GroupScheme k} {A H B : ClosedSubgroup M}
    (i : A.group ⟶ B.group) (j : H.group ⟶ B.group)
    (hi : i ≫ B.inclusion = A.inclusion) (hj : j ≫ B.inclusion = H.inclusion)
    (hunique : ∀ (Y : SchemeOver k) (a a' h h' : Y ⟶ M.X),
      a ∈ SubgroupSections A Y → a' ∈ SubgroupSections A Y →
      h ∈ SubgroupSections H Y → h' ∈ SubgroupSections H Y →
      a * h = a' * h' → a = a' ∧ h = h')
    (hproduct : ∀ (Y : SchemeOver k) (g : Y ⟶ M.X), g ∈ SubgroupSections B Y →
      ∃ a ∈ SubgroupSections A Y, ∃ h ∈ SubgroupSections H Y, a * h = g) :
    IsIso (multiplyFactors i j) := by
  have hi' : i.hom.hom ≫ B.inclusion.hom.hom = A.inclusion.hom.hom :=
    congrArg (Grp.forget (SchemeOver k)).map hi
  have hj' : j.hom.hom ≫ B.inclusion.hom.hom = H.inclusion.hom.hom :=
    congrArg (Grp.forget (SchemeOver k)).map hj
  have hmul {Y : SchemeOver k} (a : Y ⟶ A.group.X) (h : Y ⟶ H.group.X) :
      ((a ≫ i.hom.hom) * (h ≫ j.hom.hom)) ≫ B.inclusion.hom.hom =
        (a ≫ A.inclusion.hom.hom) * (h ≫ H.inclusion.hom.hom) := by
    simp only [MonObj.mul_comp, Category.assoc, hi', hj']
  have := monoSubgroup A
  have := monoSubgroup H
  have := monoSubgroup B
  apply isIso_multiplyFactors_of_sections i j
  · intro Y a a' h h' hmulEq
    have he := congrArg (· ≫ B.inclusion.hom.hom) hmulEq
    rw [hmul, hmul] at he
    have hEq := hunique Y _ _ _ _ ⟨a, rfl⟩ ⟨a', rfl⟩ ⟨h, rfl⟩ ⟨h', rfl⟩ he
    exact ⟨(cancel_mono _).mp hEq.1, (cancel_mono _).mp hEq.2⟩
  · intro Y g
    obtain ⟨_, ⟨a, rfl⟩, _, ⟨h, rfl⟩, hh⟩ := hproduct Y _ ⟨g, rfl⟩
    exact ⟨a, h, (cancel_mono B.inclusion.hom.hom).mp ((hmul _ _).trans hh)⟩

private theorem section_mem_of_le {M : GroupScheme k} {A B : ClosedSubgroup M}
    (h : IsSubgroupOf A B) {Y : SchemeOver k} {g : Y ⟶ M.X}
    (hg : g ∈ SubgroupSections A Y) : g ∈ SubgroupSections B Y := by
  obtain ⟨j, hj⟩ := h
  change (∃ a : Y ⟶ A.group.X, a ≫ A.inclusion.hom.hom = g) at hg
  obtain ⟨a, ha⟩ := hg
  have hj' : j.hom.hom ≫ B.inclusion.hom.hom = A.inclusion.hom.hom :=
    congrArg (Grp.forget (SchemeOver k)).map hj
  refine ⟨a ≫ j.hom.hom, ?_⟩
  change (a ≫ j.hom.hom) ≫ B.inclusion.hom.hom = g
  rw [Category.assoc, hj', ha]

private theorem inclusion_mem_sections {M : GroupScheme k} (H : ClosedSubgroup M) :
    H.inclusion.hom.hom ∈ SubgroupSections H H.group.X := by
  change ∃ h : H.group.X ⟶ H.group.X, h ≫ H.inclusion.hom.hom = H.inclusion.hom.hom
  exact ⟨𝟙 _, Category.id_comp _⟩

private theorem radicalSections_normal {B : ClosedSubgroup G.val} (R : ClosedSubgroup B.group)
    (hR : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) R) {Y : SchemeOver k}
    {b r : Y ⟶ G.val.X} (hb : b ∈ SubgroupSections B Y)
    (hr : r ∈ SubgroupSections (subgroupOfSubgroup B R) Y) :
    b * r * b⁻¹ ∈ SubgroupSections (subgroupOfSubgroup B R) Y := by
  obtain ⟨b, rfl⟩ := hb
  obtain ⟨r, rfl⟩ := hr
  obtain ⟨s, hs⟩ := normalSubgroup_conjugate_sections hR.1.2.2 b r
  refine ⟨s, ?_⟩
  change s ≫ R.inclusion.hom.hom ≫ B.inclusion.hom.hom =
    (b ≫ B.inclusion.hom.hom) * (r ≫ R.inclusion.hom.hom ≫ B.inclusion.hom.hom) *
      (b ≫ B.inclusion.hom.hom)⁻¹
  rw [← Category.assoc, hs]
  simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]

private theorem comp_constant {Y Z X : SchemeOver k} (f : Y ⟶ Z)
    (x : 𝟙_ (SchemeOver k) ⟶ X) :
    f ≫ toUnit Z ≫ x = toUnit Y ≫ x := by
  rw [← Category.assoc, comp_toUnit]


open private conjugation conjugation_apply conjugationIso conjugate conjugate_inclusion
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private subgroupSections_of_affine from LinearAlgebraicGroups.Flag.QuotientEmbedding

private theorem conjugatePoint_cancel (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) {Y : SchemeOver k}
    (g : Y ⟶ G.val.X) :
    conjugatePoint n (conjugatePoint n⁻¹ g) = g := by
  unfold conjugatePoint
  rw [GrpObj.comp_inv]
  group

private theorem conjugateSections (n : 𝟙_ (SchemeOver k) ⟶ G.val.X)
    (H : ClosedSubgroup G.val) {Y : SchemeOver k} (g : Y ⟶ G.val.X) :
    g ∈ SubgroupSections (conjugate n H) Y ↔
      conjugatePoint n⁻¹ g ∈ SubgroupSections H Y := by
  change (∃ p : Y ⟶ H.group.X, p ≫ (conjugate n H).inclusion.hom.hom = g) ↔
    ∃ p : Y ⟶ H.group.X, p ≫ H.inclusion.hom.hom = conjugatePoint n⁻¹ g
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨p, ?_⟩
    rw [conjugate_inclusion]
    change _ = conjugatePoint n⁻¹ ((p ≫ H.inclusion.hom.hom) ≫ (conjugation n).hom.hom)
    rw [conjugation_apply]
    change _ = conjugatePoint n⁻¹ (conjugatePoint n (p ≫ H.inclusion.hom.hom))
    simpa only [inv_inv] using (conjugatePoint_cancel n⁻¹ (p ≫ H.inclusion.hom.hom)).symm
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_⟩
    rw [conjugate_inclusion]
    change (p ≫ H.inclusion.hom.hom) ≫ (conjugation n).hom.hom = _
    rw [conjugation_apply]
    change conjugatePoint n (p ≫ H.inclusion.hom.hom) = _
    rw [hp, conjugatePoint_cancel]

private theorem conjugatedContracting {c c' : Cocharacter G.val}
    (L : LimitDecomposition c) (L' : LimitDecomposition c')
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) (hc : c ≫ (conjugationIso n).hom = c') :
    SameSubgroup (conjugate n L.contracting) L'.contracting := by
  apply sameSubgroup_of_sections
  apply subgroupSections_of_affine G.property.1
  intro R g
  rw [conjugateSections]
  let h : GroupPoints G.val R := conjugatePoint n⁻¹ g
  have hg : h ≫ (conjugationIso n).hom.hom.hom = g := by
    change h ≫ (conjugation n).hom.hom = g
    rw [conjugation_apply]
    exact conjugatePoint_cancel n g
  have he : HasLimit c h 1 ↔ HasLimit c' g 1 := by
    simpa only [hc, hg] using (hasLimit_iso (conjugationIso n) c h).symm
  exact (L.contracting_points R h).symm.trans (he.trans (L'.contracting_points R g))

private theorem subgroupSections_of_sameSubgroup {M : GroupScheme k}
    {A B : ClosedSubgroup M} (h : SameSubgroup A B) {Y : SchemeOver k}
    (g : Y ⟶ M.X) : g ∈ SubgroupSections A Y ↔ g ∈ SubgroupSections B Y := by
  have go {H J : ClosedSubgroup M} (hHJ : IsSubgroupOf H J)
      (hg : g ∈ SubgroupSections H Y) : g ∈ SubgroupSections J Y := by
    obtain ⟨f, hf⟩ := hHJ
    change (∃ p : Y ⟶ H.group.X, p ≫ H.inclusion.hom.hom = g) at hg
    obtain ⟨p, hp⟩ := hg
    refine ⟨p ≫ f.hom.hom, ?_⟩
    change (p ≫ f.hom.hom) ≫ J.inclusion.hom.hom = g
    have hh := congrArg (fun a : H.group ⟶ M ↦ a.hom.hom) hf
    change f.hom.hom ≫ J.inclusion.hom.hom = H.inclusion.hom.hom at hh
    rw [Category.assoc, hh, hp]
  exact ⟨go h.1, go h.2⟩

private theorem conjugateContractingSections {c c' : Cocharacter G.val}
    (L : LimitDecomposition c) (L' : LimitDecomposition c')
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) (hc : c ≫ (conjugationIso n).hom = c')
    (H : ClosedSubgroup G.val) (hH : SameSubgroup H L.contracting)
    (Y : SchemeOver k) (g : Y ⟶ G.val.X) :
    g ∈ SubgroupSections L'.contracting Y ↔ conjugatePoint n⁻¹ g ∈ SubgroupSections H Y := by
  exact (subgroupSections_of_sameSubgroup (conjugatedContracting L L' n hc) g).symm.trans
    ((conjugateSections n L.contracting g).trans
      (subgroupSections_of_sameSubgroup hH _).symm)

private theorem conjugatePoint_mul (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) {Y : SchemeOver k}
    (x y : Y ⟶ G.val.X) :
    conjugatePoint n (x * y) = conjugatePoint n x * conjugatePoint n y := by
  unfold conjugatePoint
  group

private theorem conjugatePoint_inv (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) {Y : SchemeOver k}
    (x : Y ⟶ G.val.X) : conjugatePoint n x⁻¹ = (conjugatePoint n x)⁻¹ := by
  unfold conjugatePoint
  group

private theorem conjugatePoint_in_torus {T : ClosedSubgroup G.val}
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) (e : T.group ≅ T.group)
    (hn : (e.hom ≫ T.inclusion).hom.hom = conjugatePoint n T.inclusion.hom.hom)
    {Y : SchemeOver k} (x : Y ⟶ G.val.X) :
    conjugatePoint n x ∈ SubgroupSections T Y ↔ x ∈ SubgroupSections T Y := by
  have h (t : Y ⟶ T.group.X) :
      conjugatePoint n (t ≫ T.inclusion.hom.hom) =
        t ≫ e.hom.hom.hom ≫ T.inclusion.hom.hom := by
    change _ = t ≫ (e.hom ≫ T.inclusion).hom.hom
    rw [hn]
    simp only [conjugatePoint, MonObj.comp_mul, GrpObj.comp_inv, comp_constant]
  constructor
  · intro hx
    change (∃ t : Y ⟶ T.group.X, t ≫ T.inclusion.hom.hom = conjugatePoint n x) at hx
    obtain ⟨t, ht⟩ := hx
    refine ⟨t ≫ e.inv.hom.hom, ?_⟩
    have hi : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ :=
      congrArg (Grp.forget (SchemeOver k)).map e.inv_hom_id
    change (t ≫ e.inv.hom.hom) ≫ T.inclusion.hom.hom = x
    have hi' : e.inv.hom.hom ≫ e.hom.hom.hom ≫ T.inclusion.hom.hom = T.inclusion.hom.hom := by
      rw [← Category.assoc, hi, Category.id_comp]
    have hh : conjugatePoint n ((t ≫ e.inv.hom.hom) ≫ T.inclusion.hom.hom) =
        conjugatePoint n x := by
      rw [h, Category.assoc, hi', ht]
    have eq := congrArg (conjugatePoint n⁻¹) hh
    have hn' (z : Y ⟶ G.val.X) : conjugatePoint n⁻¹ (conjugatePoint n z) = z := by
      simpa only [inv_inv] using conjugatePoint_cancel n⁻¹ z
    simpa only [hn'] using eq
  · intro hx
    change (∃ t : Y ⟶ T.group.X, t ≫ T.inclusion.hom.hom = x) at hx
    obtain ⟨t, rfl⟩ := hx
    refine ⟨t ≫ e.hom.hom.hom, ?_⟩
    change (t ≫ e.hom.hom.hom) ≫ T.inclusion.hom.hom = _
    rw [Category.assoc, h]

private theorem conjugateInverse_mem_torus {T : ClosedSubgroup G.val}
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) (e : T.group ≅ T.group)
    (hn : (e.hom ≫ T.inclusion).hom.hom = conjugatePoint n T.inclusion.hom.hom)
    {Y : SchemeOver k} {t : Y ⟶ G.val.X} (ht : t ∈ SubgroupSections T Y) :
    conjugatePoint n⁻¹ t ∈ SubgroupSections T Y := by
  apply (conjugatePoint_in_torus n e hn _).mp
  rwa [conjugatePoint_cancel]

private theorem conjugatedBorelSections {T B : ClosedSubgroup G.val}
    (R : ClosedSubgroup B.group) (j : T.group ⟶ B.group)
    (hj : j ≫ B.inclusion = T.inclusion) (h : IsIso (multiplyFactors j R.inclusion))
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) (e : T.group ≅ T.group)
    (hn : (e.hom ≫ T.inclusion).hom.hom = conjugatePoint n T.inclusion.hom.hom)
    (Y : SchemeOver k) (g : Y ⟶ G.val.X) :
    g ∈ SubgroupSections (conjugate n B) Y ↔
      ∃ t ∈ SubgroupSections T Y,
        ∃ r ∈ SubgroupSections (conjugate n (subgroupOfSubgroup B R)) Y, t * r = g := by
  have hc (z : Y ⟶ G.val.X) : conjugatePoint n⁻¹ (conjugatePoint n z) = z := by
    simpa only [inv_inv] using conjugatePoint_cancel n⁻¹ z
  rw [conjugateSections, borelSections R j hj h]
  constructor
  · rintro ⟨t, ht, a, ha, he⟩
    exact ⟨conjugatePoint n t, (conjugatePoint_in_torus n e hn t).2 ht, conjugatePoint n a,
      (conjugateSections n _ _).2 (by rwa [hc]), by
        rw [← conjugatePoint_mul, he, conjugatePoint_cancel]⟩
  · rintro ⟨t, ht, a, ha, rfl⟩
    exact ⟨conjugatePoint n⁻¹ t, (conjugatePoint_in_torus n e hn _).1 (by rwa [conjugatePoint_cancel]),
      conjugatePoint n⁻¹ a, (conjugateSections n _ _).1 ha, (conjugatePoint_mul n⁻¹ _ _).symm⟩

private theorem conjugatedRadicalSections_normal {B : ClosedSubgroup G.val}
    (R : ClosedSubgroup B.group) (hR : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) R)
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) {Y : SchemeOver k} {b r : Y ⟶ G.val.X}
    (hb : conjugatePoint n⁻¹ b ∈ SubgroupSections B Y)
    (hr : r ∈ SubgroupSections (conjugate n (subgroupOfSubgroup B R)) Y) :
    b * r * b⁻¹ ∈ SubgroupSections (conjugate n (subgroupOfSubgroup B R)) Y := by
  apply (conjugateSections n _ _).mpr
  rw [conjugatePoint_mul, conjugatePoint_mul, conjugatePoint_inv]
  exact radicalSections_normal R hR hb ((conjugateSections n _ _).mp hr)

open private projection_eq_iff from LinearAlgebraicGroups.Flag.QuotientEmbedding


private theorem actionOnQuotient {B : ClosedSubgroup G.val} (Q : Presentation B)
    (a : ModObj G.val.X Q.scheme)
    (ha : lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ Q.projection) ≫ a.smul =
      μ[G.val.X] ≫ Q.projection)
    {Y : SchemeOver k} (b g : Y ⟶ G.val.X) :
    lift b (g ≫ Q.projection) ≫ a.smul = (b * g) ≫ Q.projection := by
  have h := congrArg (lift b g ≫ ·) ha
  have hm : lift b g ≫ μ[G.val.X] ≫ Q.projection = (b * g) ≫ Q.projection := by
    rw [← Category.assoc]
    rfl
  simpa only [comp_lift_assoc, Category.assoc, lift_fst, lift_snd_assoc, hm] using h

private theorem quotient_rightMul {M : GroupScheme k} {B : ClosedSubgroup M}
    (Q : Presentation B) {Y : SchemeOver k} (g : Y ⟶ M.X) (b : Y ⟶ B.group.X) :
    (g * (b ≫ B.inclusion.hom.hom)) ≫ Q.projection = g ≫ Q.projection := by
  symm
  apply (projection_eq_iff Q _ _).mpr
  rw [inv_mul_cancel_left]
  exact ⟨b, rfl⟩

private theorem doubleOrbitPullback {B A : ClosedSubgroup G.val} (Q : Presentation B)
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) {O : SchemeOver k} (i : O ⟶ Q.scheme)
    (e : A.group.X ≅ O)
    (h : e.hom ≫ i = (A.inclusion.hom.hom * (toUnit A.group.X ≫ n)) ≫ Q.projection) :
    let D := A.group.X ⊗ B.group.X
    let m : D ⟶ G.val.X := (fst _ _ ≫ A.inclusion.hom.hom) *
      (toUnit D ≫ n) * (snd _ _ ≫ B.inclusion.hom.hom)
    IsPullback m (fst _ _ ≫ e.hom) Q.projection i := by
  dsimp only
  let D := A.group.X ⊗ B.group.X
  let f := (fst A.group.X B.group.X ≫ A.inclusion.hom.hom) * (toUnit D ≫ n)
  let m := f * (snd A.group.X B.group.X ≫ B.inclusion.hom.hom)
  have he (Y : SchemeOver k) (a : Y ⟶ A.group.X) :
      a ≫ e.hom ≫ i = ((a ≫ A.inclusion.hom.hom) * (toUnit Y ≫ n)) ≫ Q.projection := by
    rw [h, ← Category.assoc, MonObj.comp_mul, comp_constant]
  have comm : m ≫ Q.projection = (fst _ _ ≫ e.hom) ≫ i := by
    change (f * (snd _ _ ≫ B.inclusion.hom.hom)) ≫ Q.projection = _
    rw [quotient_rightMul]
    exact (he _ (fst _ _)).symm.trans (Category.assoc _ _ _).symm
  have lifts (s : PullbackCone Q.projection i) :
      ∃ a : s.pt ⟶ A.group.X, ∃ b : s.pt ⟶ B.group.X,
        ((a ≫ A.inclusion.hom.hom) * (toUnit s.pt ≫ n)) * (b ≫ B.inclusion.hom.hom) =
          s.fst ∧ a ≫ e.hom = s.snd := by
    let a := s.snd ≫ e.inv
    have ha : a ≫ e.hom = s.snd := by simp [a]
    let g := (a ≫ A.inclusion.hom.hom) * (toUnit s.pt ≫ n)
    have hg : g ≫ Q.projection = s.fst ≫ Q.projection := by
      rw [← he, ← Category.assoc, ha, s.condition]
    have hb := (projection_eq_iff Q _ _).mp hg
    change ∃ b : s.pt ⟶ B.group.X, b ≫ B.inclusion.hom.hom = g⁻¹ * s.fst at hb
    obtain ⟨b, hb⟩ := hb
    refine ⟨a, b, ?_, ha⟩
    change g * (b ≫ B.inclusion.hom.hom) = s.fst
    rw [hb, mul_inv_cancel_left]
  choose a b hab ha using lifts
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk comm (fun s ↦ lift (a s) (b s)) ?_ ?_ ?_)
  · intro s
    have hc : (lift (a s) (b s) : s.pt ⟶ D) ≫ toUnit D ≫ n = toUnit s.pt ≫ n :=
      comp_constant _ _
    simp only [m, f, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, hc]
    exact hab s
  · intro s
    simpa only [lift_fst_assoc] using ha s
  · intro s p hp₁ hp₂
    have ep : p ≫ fst _ _ = a s := (cancel_mono e.hom).mp (by
      rw [Category.assoc, hp₂, ha])
    have hbp : (p ≫ snd _ _) ≫ B.inclusion.hom.hom = b s ≫ B.inclusion.hom.hom := by
      have hh : ((p ≫ fst _ _ ≫ A.inclusion.hom.hom) * (toUnit s.pt ≫ n)) *
          (p ≫ snd _ _ ≫ B.inclusion.hom.hom) = s.fst := by
        change s.pt ⟶ D at p
        change p ≫ m = s.fst at hp₁
        have hc : p ≫ toUnit D ≫ n = toUnit s.pt ≫ n := comp_constant _ _
        have hmul : ((p ≫ fst _ _ ≫ A.inclusion.hom.hom) * (p ≫ toUnit D ≫ n)) *
            (p ≫ snd _ _ ≫ B.inclusion.hom.hom) = s.fst := by
          simpa only [m, f, MonObj.comp_mul, Category.assoc] using hp₁
        rw [hc] at hmul
        exact hmul
      rw [← Category.assoc p (fst _ _) A.inclusion.hom.hom, ep, ← hab s] at hh
      exact (Category.assoc _ _ _).trans (mul_left_cancel hh)
    have := monoSubgroup B
    apply CartesianMonoidalCategory.hom_ext
    · rwa [lift_fst]
    · rw [lift_snd]
      exact (cancel_mono B.inclusion.hom.hom).mp hbp

private theorem doubleOrbitSections_of_pullback {A B : ClosedSubgroup G.val}
    (Q : Presentation B) (a : ModObj G.val.X Q.scheme)
    (ha : lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ Q.projection) ≫ a.smul =
      μ[G.val.X] ≫ Q.projection)
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X)
    (hAB : IsSubgroupOf A B)
    {O : SchemeOver k} (i : O ⟶ Q.scheme) (q : B.group.X ⟶ O)
    (hq : q ≫ i =
      lift B.inclusion.hom.hom (toUnit B.group.X ≫ n ≫ Q.projection) ≫ a.smul)
    (e : A.group.X ≅ O)
    (he : e.hom ≫ i = (A.inclusion.hom.hom * (toUnit A.group.X ≫ n)) ≫ Q.projection)
    (Y : SchemeOver k) (g : Y ⟶ G.val.X) :
    let D := A.group.X ⊗ B.group.X
    let m : D ⟶ G.val.X := (fst _ _ ≫ A.inclusion.hom.hom) *
      (toUnit D ≫ n) * (snd _ _ ≫ B.inclusion.hom.hom)
    (∃ p : Y ⟶ D, p ≫ m = g) ↔
      ∃ b₁ b₂ : Y ⟶ B.group.X,
        (b₁ ≫ B.inclusion.hom.hom) * (toUnit Y ≫ n) * (b₂ ≫ B.inclusion.hom.hom) = g := by
  dsimp only
  let D := A.group.X ⊗ B.group.X
  let m : D ⟶ G.val.X := (fst _ _ ≫ A.inclusion.hom.hom) *
    (toUnit D ≫ n) * (snd _ _ ≫ B.inclusion.hom.hom)
  have hm (p : Y ⟶ D) : p ≫ m =
      (p ≫ fst _ _ ≫ A.inclusion.hom.hom) * (toUnit Y ≫ n) *
        (p ≫ snd _ _ ≫ B.inclusion.hom.hom) := by
    simp only [m, MonObj.comp_mul, comp_constant]
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨j, hj⟩ := hAB
    refine ⟨p ≫ fst _ _ ≫ j.hom.hom, p ≫ snd _ _, ?_⟩
    have hj' : j.hom.hom ≫ B.inclusion.hom.hom = A.inclusion.hom.hom :=
      congrArg (Grp.forget (SchemeOver k)).map hj
    rw [Category.assoc, Category.assoc, hj']
    simpa only [Category.assoc] using (hm p).symm.trans hp
  · rintro ⟨b₁, b₂, rfl⟩
    let z := (b₁ ≫ B.inclusion.hom.hom) * (toUnit Y ≫ n)
    have hz : (z * (b₂ ≫ B.inclusion.hom.hom)) ≫ Q.projection = (b₁ ≫ q) ≫ i := by
      rw [quotient_rightMul, Category.assoc, hq, comp_lift_assoc]
      have hc : b₁ ≫ (toUnit B.group.X ≫ n ≫ Q.projection) =
          (toUnit Y ≫ n) ≫ Q.projection := by
        simp only [comp_constant, Category.assoc]
      rw [hc, actionOnQuotient Q a ha]
    let Dp := doubleOrbitPullback Q n i e he
    exact ⟨Dp.lift _ _ hz, Dp.lift_fst _ _ _⟩

open private centralizes_hasLimit from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

private theorem fixedOver_sections {T : ClosedSubgroup G.val} {X Y : SchemeOver k}
    (a : ModObj G.val.X X) (y : Y ⟶ X) :
    FixedOver (T := T) a y ↔ ∀ (Z : SchemeOver k) (t : Z ⟶ T.group.X) (z : Z ⟶ Y),
      lift (t ≫ T.inclusion.hom.hom) (z ≫ y) ≫ a.smul = z ≫ y := by
  constructor
  · intro h Z t z
    have ht := congrArg (lift t z ≫ ·) h
    simpa only [FixedOver, comp_lift_assoc, Category.assoc, lift_fst_assoc, lift_snd_assoc] using ht
  · intro h
    exact h _ (fst _ _) (snd _ _)

private theorem torus_translate_coset {T B : ClosedSubgroup G.val}
    (Q : Presentation B) (n : 𝟙_ (SchemeOver k) ⟶ G.val.X)
    (hT : ∀ (Y : SchemeOver k) (t : Y ⟶ T.group.X),
      conjugatePoint n⁻¹ (t ≫ T.inclusion.hom.hom) ∈ SubgroupSections B Y)
    {Y : SchemeOver k} (t : Y ⟶ T.group.X) (u : Y ⟶ G.val.X) :
    ((t ≫ T.inclusion.hom.hom) * u * (toUnit Y ≫ n)) ≫ Q.projection =
      ((t ≫ T.inclusion.hom.hom) * u * (t ≫ T.inclusion.hom.hom)⁻¹ *
        (toUnit Y ≫ n)) ≫ Q.projection := by
  symm
  apply (projection_eq_iff Q _ _).mpr
  let s := t ≫ T.inclusion.hom.hom
  let r := toUnit Y ≫ n
  change (s * u * s⁻¹ * r)⁻¹ * (s * u * r) ∈ SubgroupSections B Y
  have hh : (s * u * s⁻¹ * r)⁻¹ * (s * u * r) = conjugatePoint n⁻¹ s := by
    unfold conjugatePoint
    rw [GrpObj.comp_inv, ← show r = toUnit Y ≫ n from rfl]
    group
  rw [hh]
  exact hT Y t

set_option maxHeartbeats 750000 in
private theorem fixedInContractingOrbit {T B A : ClosedSubgroup G.val}
    (Q : Presentation B) (a : ModObj G.val.X Q.scheme)
    (ha : lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ Q.projection) ≫ a.smul =
      μ[G.val.X] ≫ Q.projection)
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X)
    (hT : ∀ (Y : SchemeOver k) (t : Y ⟶ T.group.X),
      conjugatePoint n⁻¹ (t ≫ T.inclusion.hom.hom) ∈ SubgroupSections B Y)
    (hN : ∀ (Y : SchemeOver k) (t : Y ⟶ T.group.X) (u : Y ⟶ A.group.X),
      let s := t ≫ T.inclusion.hom.hom
      s * (u ≫ A.inclusion.hom.hom) * s⁻¹ ∈ SubgroupSections A Y)
    (hf : Mono ((A.inclusion.hom.hom * (toUnit A.group.X ≫ n)) ≫ Q.projection))
    (c : Cocharacter T.group) (L : LimitDecomposition (c ≫ T.inclusion))
    (hA : IsSubgroupOf A L.contracting)
    (R : TestAlgebra k) (u : (testSpec k).obj (.op R) ⟶ A.group.X) :
    FixedOver (T := T) a ((u ≫ A.inclusion.hom.hom * (toUnit _ ≫ n)) ≫ Q.projection) ↔
      ((u ≫ A.inclusion.hom.hom * (toUnit _ ≫ n)) ≫ Q.projection) = toUnit _ ≫ n ≫ Q.projection := by
  let Y := (testSpec k).obj (.op R)
  let v : Y ⟶ G.val.X := u ≫ A.inclusion.hom.hom
  let y : Y ⟶ Q.scheme := (v * (toUnit Y ≫ n)) ≫ Q.projection
  have hcomp {Z : SchemeOver k} (z : Z ⟶ Y) :
      z ≫ y = ((z ≫ u ≫ A.inclusion.hom.hom) * (toUnit Z ≫ n)) ≫ Q.projection := by
    simp only [y, v, MonObj.comp_mul_assoc, comp_constant]
  constructor
  · intro h
    have ht (Z : SchemeOver k) (t : Z ⟶ T.group.X) (z : Z ⟶ Y) :
        let s := t ≫ T.inclusion.hom.hom
        s * (z ≫ u ≫ A.inclusion.hom.hom) * s⁻¹ = z ≫ u ≫ A.inclusion.hom.hom := by
      dsimp only
      have hfix := (fixedOver_sections a y).mp h Z t z
      rw [hcomp, actionOnQuotient Q a ha, ← mul_assoc] at hfix
      rw [torus_translate_coset Q n hT] at hfix
      let s := t ≫ T.inclusion.hom.hom
      have hz := hN Z t (z ≫ u)
      change (∃ w : Z ⟶ A.group.X,
        w ≫ A.inclusion.hom.hom = s * (z ≫ u ≫ A.inclusion.hom.hom) * s⁻¹) at hz
      obtain ⟨w, hw⟩ := hz
      have he : w = z ≫ u := (cancel_mono
        ((A.inclusion.hom.hom * (toUnit A.group.X ≫ n)) ≫ Q.projection)).mp (by
          simp only [Category.assoc, ← Category.assoc _ (_ * _) Q.projection, MonObj.comp_mul,
            Category.assoc, comp_constant, hw, ← hcomp z]
          exact hfix.trans (hcomp z).symm)
      rw [← hw, he, Category.assoc]
    have hcent : Centralizes (c ≫ T.inclusion) v := by
      let M := (specGroup (DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters)).X
      let Z := M ⊗ Y
      let t : Z ⟶ T.group.X := fst _ _ ≫ c.hom.hom
      let z : Z ⟶ Y := snd _ _
      have hh := ht Z t z
      dsimp only at hh
      unfold Centralizes conjugateFamily
      change (z ≫ v) * (t ≫ T.inclusion.hom.hom) * (z ≫ v)⁻¹ = t ≫ T.inclusion.hom.hom
      have hh' : (t ≫ T.inclusion.hom.hom) * (z ≫ v) * (t ≫ T.inclusion.hom.hom)⁻¹ =
          z ≫ v := hh
      have hcomm := (mul_inv_eq_iff_eq_mul.mp hh').symm
      exact mul_inv_eq_iff_eq_mul.mpr hcomm
    have hv := centralizes_hasLimit (c ≫ T.inclusion) hcent
    obtain ⟨j, hj⟩ := hA
    have hv' : HasLimit (c ≫ T.inclusion) v 1 := (L.contracting_points R v).mpr
      ⟨u ≫ j.hom.hom, by
        have hh := congrArg (Grp.forget (SchemeOver k)).map hj
        change j.hom.hom ≫ L.contracting.inclusion.hom.hom = A.inclusion.hom.hom at hh
        change (u ≫ j.hom.hom) ≫ L.contracting.inclusion.hom.hom = u ≫ A.inclusion.hom.hom
        rw [Category.assoc, hh]⟩
    let : IsAffine G.val.X.left := G.property.1
    have he : v = 1 := LinearAlgebraicGroups.CocharacterDynamics.limitIsUnique (c ≫ T.inclusion) hv hv'
    change (v * (toUnit Y ≫ n)) ≫ Q.projection = _
    rw [he, one_mul, Category.assoc]
  · intro h
    change y = _ at h
    change FixedOver (T := T) a y
    rw [h, fixedOver_sections]
    intro Z t z
    rw [comp_constant]
    change lift (t ≫ T.inclusion.hom.hom) ((toUnit Z ≫ n) ≫ Q.projection) ≫ a.smul =
      (toUnit Z ≫ n) ≫ Q.projection
    rw [actionOnQuotient Q a ha]
    have hh := torus_translate_coset Q n hT t (1 : Z ⟶ G.val.X)
    simpa only [mul_one, mul_inv_cancel, one_mul] using hh

open private restrictGroupAction restrictGroupAction_smul from LinearAlgebraicGroups.Flag.SmoothOrbit

private theorem restrictQuotientAction {B : ClosedSubgroup G.val} (Q : Presentation B)
    (a : ModObj G.val.X Q.scheme)
    (ha : lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ Q.projection) ≫ a.smul =
      μ[G.val.X] ≫ Q.projection)
    {Y : SchemeOver k} (b : Y ⟶ B.group.X) (g : Y ⟶ G.val.X) :
    lift b (g ≫ Q.projection) ≫ (restrictGroupAction B.inclusion a).smul =
      ((b ≫ B.inclusion.hom.hom) * g) ≫ Q.projection := by
  rw [restrictGroupAction_smul, lift_map_assoc, Category.comp_id]
  exact actionOnQuotient Q a ha _ _

private theorem stabilizer_isConjugateIntersection {B : ClosedSubgroup G.val}
    (Q : Presentation B) (a : ModObj G.val.X Q.scheme)
    (ha : lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ Q.projection) ≫ a.smul =
      μ[G.val.X] ≫ Q.projection)
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X)
    (S : ClosedSubgroup B.group)
    (hS : RepresentsSubgroup S (fun _ b ↦
      Stabilizes (restrictGroupAction B.inclusion a).smul (n ≫ Q.projection) b)) :
    IsConjugateIntersection B B (subgroupOfSubgroup B S) n := by
  have h (Y : SchemeOver k) (b : Y ⟶ B.group.X) :
      b ∈ SubgroupSections S Y ↔
        conjugatePoint n⁻¹ (b ≫ B.inclusion.hom.hom) ∈ SubgroupSections B Y := by
    change (∃ s : Y ⟶ S.group.X, s ≫ S.inclusion.hom.hom = b) ↔ _
    rw [← hS Y b]
    change (lift b ((toUnit Y ≫ n) ≫ Q.projection) ≫ (restrictGroupAction B.inclusion a).smul =
      (toUnit Y ≫ n) ≫ Q.projection) ↔ _
    rw [restrictQuotientAction Q a ha, eq_comm, projection_eq_iff Q]
    have hg : (toUnit Y ≫ n)⁻¹ * ((b ≫ B.inclusion.hom.hom) * (toUnit Y ≫ n)) =
        conjugatePoint n⁻¹ (b ≫ B.inclusion.hom.hom) := by
      rw [conjugatePoint, GrpObj.comp_inv, inv_inv, mul_assoc]
    rw [hg]
  intro Y g
  change (∃ s : Y ⟶ S.group.X, s ≫ S.inclusion.hom.hom ≫ B.inclusion.hom.hom = g) ↔ _
  constructor
  · rintro ⟨s, rfl⟩
    let b := s ≫ S.inclusion.hom.hom
    refine ⟨⟨b, ?_⟩, (h Y b).mp ⟨s, rfl⟩⟩
    change (s ≫ S.inclusion.hom.hom) ≫ B.inclusion.hom.hom = _
    exact Category.assoc _ _ _
  · rintro ⟨hb, hconj⟩
    change (∃ b : Y ⟶ B.group.X, b ≫ B.inclusion.hom.hom = g) at hb
    obtain ⟨b, hb⟩ := hb
    have hs := (h Y b).mpr (hb ▸ hconj)
    change ∃ s : Y ⟶ S.group.X, s ≫ S.inclusion.hom.hom = b at hs
    obtain ⟨s, hs⟩ := hs
    exact ⟨s, by rw [← Category.assoc, hs, hb]⟩

open private same_orbit_lift_iff from LinearAlgebraicGroups.Flag.SmoothOrbit

private theorem orbitProjection_eq {M : GroupScheme k} {X : SchemeOver k}
    {a : ModObj M.X X} {x : 𝟙_ (SchemeOver k) ⟶ X} (P : SmoothOrbit.Presentation a x) :
    P.projection ≫ P.openInClosure ≫ SmoothOrbit.closureInclusion a x =
      SmoothOrbit.orbitMap a x := by
  apply Over.OverMorphism.ext
  change P.projection.left ≫ P.openInClosure.left ≫ (SmoothOrbit.orbitMap a x).left.imageι = _
  rw [← Category.assoc, P.factors, Scheme.Hom.toImage_imageι]

private theorem sameOrbitProjection {M : GroupScheme k} {X : SchemeOver k}
    {a : ModObj M.X X} {x : 𝟙_ (SchemeOver k) ⟶ X} (P : SmoothOrbit.Presentation a x)
    {Y : SchemeOver k} (g h : Y ⟶ M.X) :
    g ≫ P.projection = h ≫ P.projection ↔ g⁻¹ * h ∈ SubgroupSections P.stabilizer Y := by
  let i := P.openInClosure ≫ SmoothOrbit.closureInclusion a x
  have := P.isOpen
  have : Mono i.left := inferInstanceAs (Mono (P.openInClosure.left ≫
    (SmoothOrbit.orbitMap a x).left.imageι))
  have : Mono i := Over.mono_of_mono_left i
  exact same_orbit_lift_iff a x i P.projection (orbitProjection_eq P)
    P.stabilizer P.representsStabilizer g h

private theorem projection_mul_stabilizer {M : GroupScheme k} {X : SchemeOver k}
    {a : ModObj M.X X} {x : 𝟙_ (SchemeOver k) ⟶ X} (P : SmoothOrbit.Presentation a x)
    {Y : SchemeOver k} (g : Y ⟶ M.X) (h : Y ⟶ P.stabilizer.group.X) :
    (g * (h ≫ P.stabilizer.inclusion.hom.hom)) ≫ P.projection = g ≫ P.projection := by
  symm
  apply (sameOrbitProjection P _ _).mpr
  rw [inv_mul_cancel_left]
  exact ⟨h, rfl⟩

private theorem orbitFactorCoordinate {M A : GroupScheme k} (H : ClosedSubgroup M)
    (j : A ⟶ M) [IsIso (multiplyFactors j H.inclusion)]
    {Y : SchemeOver k} (b : Y ⟶ M.X) (h : Y ⟶ H.group.X) :
    let f := multiplyFactors j H.inclusion
    let p := inv f ≫ fst _ _
    (b * (h ≫ H.inclusion.hom.hom)) ≫ p = b ≫ p := by
  dsimp only
  let f := multiplyFactors j H.inclusion
  let a := b ≫ inv f ≫ fst _ _
  let c := b ≫ inv f ≫ snd _ _
  have hb : (a ≫ j.hom.hom) * (c ≫ H.inclusion.hom.hom) = b := by
    have he : (b ≫ inv f) ≫ f = b := by simp
    simpa only [f, multiplyFactors, MonObj.comp_mul, Category.assoc, a, c] using he
  have hf : lift a (c * h) ≫ f = b * (h ≫ H.inclusion.hom.hom) := by
    simp only [f, multiplyFactors, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
      MonObj.mul_comp, mul_assoc, ← hb]
  change (b * (h ≫ H.inclusion.hom.hom)) ≫ inv f ≫ fst _ _ = b ≫ inv f ≫ fst _ _
  rw [← hf]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc, lift_fst, a]

open private descends from LinearAlgebraicGroups.Reductive.BorelProper

private theorem orbitIso_of_factorization {M A : GroupScheme k} {X : SchemeOver k}
    {a : ModObj M.X X} {x : 𝟙_ (SchemeOver k) ⟶ X} (P : SmoothOrbit.Presentation a x)
    (j : A ⟶ M) [IsIso (multiplyFactors j P.stabilizer.inclusion)] :
    IsIso (j.hom.hom ≫ P.projection) := by
  let H := P.stabilizer
  let f := multiplyFactors j H.inclusion
  let p : M.X ⟶ A.X := inv f ≫ fst _ _
  let i := j.hom.hom ≫ P.projection
  have : Flat P.projection.left := P.flat
  have : Surjective P.projection.left := P.surjective
  have : LocallyOfFinitePresentation P.projection.left := P.finitePresentation
  have hfiber (Y : SchemeOver k) (a b : Y ⟶ M.X)
      (hab : a ≫ P.projection = b ≫ P.projection) : a ≫ p = b ≫ p := by
    have hh := (sameOrbitProjection P _ _).mp hab
    change ∃ h : Y ⟶ H.group.X, h ≫ H.inclusion.hom.hom = a⁻¹ * b at hh
    obtain ⟨h, hh⟩ := hh
    have hmul : a * (h ≫ H.inclusion.hom.hom) = b := by rw [hh, mul_inv_cancel_left]
    exact (orbitFactorCoordinate H j a h).symm.trans (congrArg (· ≫ p) hmul)
  obtain ⟨d, hd⟩ := descends P.projection p hfiber
  have hid : i ≫ d = 𝟙 A.X := by
    rw [show i = j.hom.hom ≫ P.projection from rfl, Category.assoc, hd]
    have hj : lift (𝟙 A.X) (1 : A.X ⟶ H.group.X) ≫ f = j.hom.hom := by
      simp only [f, multiplyFactors, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
        Category.id_comp, MonObj.one_comp, mul_one]
    rw [← hj]
    simp only [p, Category.assoc, IsIso.hom_inv_id_assoc, lift_fst]
  have hdi : d ≫ i = 𝟙 P.orbit := by
    have : Epi P.projection := Over.epi_of_epi_left P.projection
    apply (cancel_epi P.projection).mp
    rw [← Category.assoc, hd, Category.comp_id]
    let a₀ : M.X ⟶ A.X := inv f ≫ fst _ _
    let b₀ : M.X ⟶ H.group.X := inv f ≫ snd _ _
    have hb : (a₀ ≫ j.hom.hom) * (b₀ ≫ H.inclusion.hom.hom) = 𝟙 M.X := by
      have h := IsIso.inv_hom_id f
      simpa only [f, a₀, b₀, multiplyFactors, MonObj.comp_mul, Category.assoc] using h
    have hq := projection_mul_stabilizer P (a₀ ≫ j.hom.hom) b₀
    rw [hb, Category.id_comp] at hq
    exact hq.symm
  exact ⟨d, hid, hdi⟩

open private fibreTorsor splitFibrePoint from LinearAlgebraicGroups.Reductive.WeylScheme

private theorem representativeExists {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D : Datum T} (I : Identification D) (hT : IsSplitTorus T.group)
    (w : D.rootDatum.weylGroup) :
    ∃ n, IsRepresentative I w n := by
  let S : ClosedSubgroup I.normalizer.group := ⟨T.group, I.torusInclusion, I.torusClosed⟩
  let x := I.image.constantGroup.sectionPoint (I.labelEquiv w)
  have h := fibreTorsor (G := closedSubgroupAlgebraicGroup I.normalizer)
    (W := I.scheme) S I.quotient I.isQuotient x
  exact splitFibrePoint (G := closedSubgroupAlgebraicGroup I.normalizer)
    (W := I.scheme) S hT I.quotient x h

private theorem representativeConjugation {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D : Datum T} (I : Identification D) {w : D.rootDatum.weylGroup}
    {n : 𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X} (hn : IsRepresentative I w n) :
    ((I.image.conjugation (I.labelEquiv w)).hom ≫ T.inclusion).hom.hom =
      conjugatePoint (n ≫ I.normalizer.inclusion.hom.hom) T.inclusion.hom.hom := by
  have hunit : toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ := Subsingleton.elim _ _
  have hn' : n ≫ I.quotient.hom.hom =
      toUnit _ ≫ I.image.constantGroup.sectionPoint (I.labelEquiv w) := by
    rw [hunit, Category.id_comp]
    exact hn
  have h := congrArg (fun f => lift (𝟙 T.group.X) (toUnit T.group.X) ≫ f)
    (I.image.conjugates _ n _ hn')
  simpa only [conjugatePoint, conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc,
    lift_fst_assoc, lift_snd_assoc, Category.id_comp] using h.symm

private theorem sameSubgroup_of_rootParametrization {T : ClosedSubgroup G.val}
    {U : RootSubgroupFamily T} {l : List (Root T)} {A B : ClosedSubgroup G.val}
    (ha : Parametrizes U l A.inclusion.hom.hom)
    (hb : Parametrizes U l B.inclusion.hom.hom) : SameSubgroup A B := by
  apply sameSubgroup_of_sections
  intro Y g
  exact (rootCoordinatesRange ha Y g).symm.trans (rootCoordinatesRange hb Y g)

private theorem translatingCocharacter {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D : Datum T} (I : Identification D) {w : D.rootDatum.weylGroup}
    {n : 𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X} (hn : IsRepresentative I w n)
    (c : Cocharacter T.group) :
    (c ≫ T.inclusion) ≫ (conjugationIso (n ≫ I.normalizer.inclusion.hom.hom)).hom =
      (c ≫ (I.image.conjugation (I.labelEquiv w)).hom) ≫ T.inclusion := by
  have h : T.inclusion ≫ (conjugationIso (n ≫ I.normalizer.inclusion.hom.hom)).hom =
      (I.image.conjugation (I.labelEquiv w)).hom ≫ T.inclusion := by
    apply Grp.hom_ext
    change T.inclusion.hom.hom ≫ (conjugation (n ≫ I.normalizer.inclusion.hom.hom)).hom.hom = _
    rw [conjugation_apply]
    exact (representativeConjugation I hn).symm
  simp only [Category.assoc, h]

private def UniqueCellProducts (N T P : ClosedSubgroup G.val) : Prop :=
  ∀ (Y : SchemeOver k) (n t p n' t' p' : Y ⟶ G.val.X),
    n ∈ SubgroupSections N Y → t ∈ SubgroupSections T Y → p ∈ SubgroupSections P Y →
    n' ∈ SubgroupSections N Y → t' ∈ SubgroupSections T Y → p' ∈ SubgroupSections P Y →
    n * (t * p) = n' * (t' * p') → n = n' ∧ t = t' ∧ p = p'

private theorem translatedRadicalProducts
    (hContract : Specs.OrderedRootProducts.ContractingProduct.{u})
    (hCell : Specs.OrderedRootProducts.RegularRootCell.{u})
    (hG : IsReductive G) {T B : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D : Datum T} (I : Identification D) (hT : IsSplitTorus T.group)
    (hmax : IsGeometricallyMaximal T) (U : RootSubgroupFamily T) (R : ClosedSubgroup B.group)
    (Rneg : ClosedSubgroup G.val)
    (hR : OrderedParametrization U (subgroupRoots T B) (subgroupOfSubgroup B R))
    (hRneg : OrderedParametrization U (subgroupRoots T B)ᶜ Rneg)
    (hpos : IsPositiveSystem T (subgroupRoots T B))
    (w : D.rootDatum.weylGroup) (n : 𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X)
    (hn : IsRepresentative I w n) :
    let g := n ≫ I.normalizer.inclusion.hom.hom
    let P := subgroupRoots T B
    let p := D.rootDatum.weylGroupToPerm w
    ∃ A V : ClosedSubgroup G.val,
      IsConjugateIntersection (subgroupOfSubgroup B R) Rneg A g ∧
      IsConjugateIntersection (subgroupOfSubgroup B R) (subgroupOfSubgroup B R) V g ∧
      OrderedParametrization U (P ∩ p '' Pᶜ) A ∧
      OrderedParametrization U (P ∩ p '' P) V ∧
      (∃ (i : A.group ⟶ R.group) (j : V.group ⟶ R.group),
        i ≫ R.inclusion ≫ B.inclusion = A.inclusion ∧
        j ≫ R.inclusion ≫ B.inclusion = V.inclusion ∧ IsIso (multiplyFactors i j)) ∧
      UniqueCellProducts (conjugate g Rneg) T (conjugate g (subgroupOfSubgroup B R)) := by
  classical
  dsimp only
  let g := n ≫ I.normalizer.inclusion.hom.hom
  let P := subgroupRoots T B
  let p := D.rootDatum.weylGroupToPerm w
  let E := I.image.conjugation (I.labelEquiv w)
  have : Finite (Root T) := D.finiteRoots
  obtain ⟨c, L, hc, hcP, hL⟩ := regularBorelContracting hContract hG D hT hmax U R hR hpos
  let d := c ≫ E.hom
  have hd : IsRegular T d := by
    intro β hzero
    have h := conjugateChamber I w c (p.symm β)
    change CharacterPairing.pairing T.group (p (p.symm β)).val d = _ at h
    rw [Equiv.apply_symm_apply, hzero] at h
    exact hc _ h.symm
  have hdP : positiveRoots T d = p '' P :=
    (positiveRoots_conjugate I w c).trans (congrArg (p '' ·) hcP)
  have hnegc : positiveRoots T (oppositeCocharacter c) = Pᶜ :=
    (positiveRoots_opposite D hc).trans (congrArg (·ᶜ) hcP)
  have hopd : oppositeCocharacter d = oppositeCocharacter c ≫ E.hom := by
    unfold d oppositeCocharacter
    rw [Category.assoc]
  have hnegd : positiveRoots T (oppositeCocharacter d) = p '' Pᶜ := by
    rw [hopd, positiveRoots_conjugate I w (oppositeCocharacter c), hnegc]
  obtain ⟨⟨Lcneg⟩, hLcneg⟩ := (hContract G hG T hT hmax).2.2 (oppositeCocharacter c)
  obtain ⟨lneg, hlneg⟩ := existsEnumeration Pᶜ
  have hcneg : SameSubgroup Rneg Lcneg.contracting :=
    sameSubgroup_of_rootParametrization (hRneg lneg hlneg) (hLcneg Lcneg U lneg (hnegc.symm ▸ hlneg))
  obtain ⟨⟨Ld⟩, hLd⟩ := (hContract G hG T hT hmax).2.2 d
  obtain ⟨⟨Ldneg⟩, hLdneg⟩ := (hContract G hG T hT hmax).2.2 (oppositeCocharacter d)
  have hdSections := conjugateContractingSections L Ld g (translatingCocharacter I hn c)
    (subgroupOfSubgroup B R) hL
  have hdnegSections := conjugateContractingSections Lcneg Ldneg g
    ((translatingCocharacter I hn (oppositeCocharacter c)).trans
      (congrArg (· ≫ T.inclusion) hopd.symm)) Rneg hcneg
  let N := Ldneg.contracting
  let H := Ld.contracting
  let R₀ := subgroupOfSubgroup B R
  let X := subgroupPullback R₀ N
  let Y := subgroupPullback R₀ H
  have hnegPos : p '' Pᶜ = (p '' P)ᶜ := by
    rw [← hnegd, ← hdP]
    exact positiveRoots_opposite D hd
  have hcover : p '' Pᶜ ∪ p '' P = Set.univ := by
    rw [hnegPos, Set.compl_union_self]
  have hdis : Disjoint (p '' Pᶜ) (p '' P) := by
    rw [hnegPos]
    exact disjoint_compl_left
  have hchart (l m : List (Root T)) (hl : Enumerates l (p '' Pᶜ))
      (hm : Enumerates m (p '' P)) :
      Mono (OrderedRootProducts.rootCellMap T U l m) := by
    have := hCell G hG T hT hmax d hd U l m (hnegd.symm ▸ hl) (hdP.symm ▸ hm)
    exact Over.mono_of_mono_left _
  obtain ⟨hA, hV⟩ := splitRadicalByChambers U R₀ N H P (p '' Pᶜ) (p '' P) hcover hdis hR
    (fun l h ↦ hLdneg _ U l (hnegd.symm ▸ h)) (fun l h ↦ hLd _ U l (hdP.symm ▸ h)) hchart
  refine ⟨subgroupOfSubgroup R₀ X, subgroupOfSubgroup R₀ Y, ?_, ?_, hA, hV,
    ⟨X.inclusion, Y.inclusion, rfl, rfl, ?_⟩, ?_⟩
  · intro Z z
    exact (subgroupIntersection_sections R₀ N z).trans (and_congr_right fun _ ↦ hdnegSections Z z)
  · intro Z z
    exact (subgroupIntersection_sections R₀ H z).trans (and_congr_right fun _ ↦ hdSections Z z)
  · obtain ⟨l, hl⟩ := existsEnumeration (P ∩ (p '' Pᶜ))
    obtain ⟨m, hm⟩ := existsEnumeration (P ∩ (p '' P))
    have hg : (P ∩ p '' Pᶜ) ∪ (P ∩ p '' P) = P := by
      rw [← Set.inter_union_distrib_left, hcover, Set.inter_univ]
    have hdi := Set.disjoint_left.mpr (fun _
      (h₁ : _ ∈ P ∩ p '' Pᶜ) (h₂ : _ ∈ P ∩ p '' P) ↦ Set.disjoint_left.mp hdis h₁.2 h₂.2)
    have hlm : Enumerates (l ++ m) P := hg ▸ enumeratesAppend hl hm hdi
    exact multiplySlices (hR (l ++ m) hlm) (hA l hl) (hV m hm)
  · obtain ⟨l, hl⟩ := existsEnumeration (p '' Pᶜ)
    obtain ⟨m, hm⟩ := existsEnumeration (p '' P)
    intro Z x t y x' t' y' hx ht hy hx' ht' hy' he
    have hN (z : Z ⟶ G.val.X) := (conjugateSections g Rneg z).trans (hdnegSections Z z).symm
    have hP (z : Z ⟶ G.val.X) := (conjugateSections g R₀ z).trans (hdSections Z z).symm
    exact rootCell_unique l m N H (hLdneg _ U l (hnegd.symm ▸ hl))
      (hLd _ U m (hdP.symm ▸ hm)) (hchart l m hl hm) Z x t y x' t' y'
      ((hN _).mp hx) ht ((hP _).mp hy) ((hN _).mp hx') ht' ((hP _).mp hy') he

/-- The root subgroup factors and their scheme intersections for every rational
Weyl representative. This is the radical portion of the Bruhat cell construction. -/
theorem bruhatRadicalFactors
    (hPos : Specs.BorelPositivity.Statement.{u})
    (hBorel : Specs.OrderedRootProducts.BorelRadicalProduct.{u})
    (hContract : Specs.OrderedRootProducts.ContractingProduct.{u})
    (hCell : Specs.OrderedRootProducts.RegularRootCell.{u})
    (hG : IsReductive G) (T B : ClosedSubgroup G.val) (hT : IsSplitTorus T.group)
    (hmax : IsGeometricallyMaximal T) (hB : IsKBorel B) (hTB : IsSubgroupOf T B) :
    ∃ h : IsCommMonObj T.group.X, letI := h
      ∃ (D : Datum T) (I : Identification D) (U : RootSubgroupFamily T)
        (Bneg : ClosedSubgroup G.val) (R : ClosedSubgroup B.group)
        (Rneg : ClosedSubgroup Bneg.group),
        IsKBorel Bneg ∧ IsSubgroupOf T Bneg ∧
        subgroupRoots T Bneg = (subgroupRoots T B)ᶜ ∧
        IsUnipotentRadical (closedSubgroupAlgebraicGroup B) R ∧
        IsUnipotentRadical (closedSubgroupAlgebraicGroup Bneg) Rneg ∧
        ∀ w : D.rootDatum.weylGroup,
          (∃ n, IsRepresentative I w n) ∧
          ∀ n, IsRepresentative I w n →
            let g := n ≫ I.normalizer.inclusion.hom.hom
            let p := D.rootDatum.weylGroupToPerm w
            ∃ A V : ClosedSubgroup G.val,
              IsConjugateIntersection (subgroupOfSubgroup B R) (subgroupOfSubgroup Bneg Rneg) A g ∧
              IsConjugateIntersection (subgroupOfSubgroup B R) (subgroupOfSubgroup B R) V g ∧
              OrderedParametrization U (subgroupRoots T B ∩ p '' subgroupRoots T Bneg) A ∧
              OrderedParametrization U (subgroupRoots T B ∩ p '' subgroupRoots T B) V ∧
              ∃ (i : A.group ⟶ R.group) (j : V.group ⟶ R.group),
                i ≫ R.inclusion ≫ B.inclusion = A.inclusion ∧
                j ≫ R.inclusion ≫ B.inclusion = V.inclusion ∧ IsIso (multiplyFactors i j) := by
  obtain ⟨hcomm, hdata⟩ := hPos G hG T hT hmax
  let := hcomm
  obtain ⟨D, ⟨I⟩, hCorr, _, ⟨U⟩, _⟩ := hdata
  obtain ⟨Bneg, hBneg, hTBneg, hneg⟩ := existsOppositeBorel hB hTB hCorr
  obtain ⟨R, hR, hp⟩ := hBorel G hG T hT hmax B hB hTB
  obtain ⟨Rneg, hRneg, hpneg⟩ := hBorel G hG T hT hmax Bneg hBneg hTBneg
  have hprod : OrderedParametrization U (subgroupRoots T B) (subgroupOfSubgroup B R) :=
    fun l hl ↦ hp U l hl
  have hprodneg : OrderedParametrization U (subgroupRoots T B)ᶜ (subgroupOfSubgroup Bneg Rneg) :=
    fun l hl ↦ hpneg U l (hneg.symm ▸ hl)
  refine ⟨hcomm, D, I, U, Bneg, R, Rneg, hBneg, hTBneg, hneg, hR, hRneg, fun w ↦ ⟨?_, ?_⟩⟩
  · exact representativeExists I hT w
  · intro n hn
    rw [hneg]
    obtain ⟨A, V, hA, hV, hAp, hVp, hmul, _⟩ := translatedRadicalProducts hContract hCell hG I hT
      hmax U R (subgroupOfSubgroup Bneg Rneg) hprod hprodneg (hCorr.1 B hB hTB) w n hn
    exact ⟨A, V, hA, hV, hAp, hVp, hmul⟩


private theorem torus_normalizes_slice {T B Bneg A : ClosedSubgroup G.val}
    {R : ClosedSubgroup B.group} {Rneg : ClosedSubgroup Bneg.group}
    (hR : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) R)
    (hRneg : IsUnipotentRadical (closedSubgroupAlgebraicGroup Bneg) Rneg)
    (hTB : IsSubgroupOf T B) (hTBneg : IsSubgroupOf T Bneg)
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) (e : T.group ≅ T.group)
    (he : (e.hom ≫ T.inclusion).hom.hom = conjugatePoint n T.inclusion.hom.hom)
    (hA : IsConjugateIntersection (subgroupOfSubgroup B R) (subgroupOfSubgroup Bneg Rneg) A n)
    (Y : SchemeOver k) {t x : Y ⟶ G.val.X} (ht : t ∈ SubgroupSections T Y)
    (hx : x ∈ SubgroupSections A Y) :
    t * x * t⁻¹ ∈ SubgroupSections A Y := by
  obtain ⟨hxR, hxneg⟩ := (hA Y x).mp hx
  refine (hA Y _).mpr ⟨radicalSections_normal R hR (section_mem_of_le hTB ht) hxR, ?_⟩
  rw [conjugatePoint_mul, conjugatePoint_mul, conjugatePoint_inv]
  exact radicalSections_normal Rneg hRneg (section_mem_of_le hTBneg
    (conjugateInverse_mem_torus n e he ht)) hxneg

private theorem bruhatStabilizerProducts {T B Bneg A V : ClosedSubgroup G.val}
    {R : ClosedSubgroup B.group} {Rneg : ClosedSubgroup Bneg.group}
    (hR : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) R)
    (hRneg : IsUnipotentRadical (closedSubgroupAlgebraicGroup Bneg) Rneg)
    (hTBneg : IsSubgroupOf T Bneg)
    (j : T.group ⟶ B.group) (hj : j ≫ B.inclusion = T.inclusion)
    (hjR : IsIso (multiplyFactors j R.inclusion))
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) (e : T.group ≅ T.group)
    (he : (e.hom ≫ T.inclusion).hom.hom = conjugatePoint n T.inclusion.hom.hom)
    (hA : IsConjugateIntersection (subgroupOfSubgroup B R) (subgroupOfSubgroup Bneg Rneg) A n)
    (hV : IsConjugateIntersection (subgroupOfSubgroup B R) (subgroupOfSubgroup B R) V n)
    (i : A.group ⟶ R.group) (v₀ : V.group ⟶ R.group)
    (hi : i ≫ R.inclusion ≫ B.inclusion = A.inclusion)
    (hv₀ : v₀ ≫ R.inclusion ≫ B.inclusion = V.inclusion)
    (hiV : IsIso (multiplyFactors i v₀))
    (H : ClosedSubgroup B.group) (hH : IsConjugateIntersection B B (subgroupOfSubgroup B H) n)
    (hunique : UniqueCellProducts (conjugate n (subgroupOfSubgroup Bneg Rneg)) T
      (conjugate n (subgroupOfSubgroup B R))) :
    ∃ (s : T.group ⟶ H.group) (v : V.group ⟶ H.group) (a : A.group ⟶ B.group),
      s ≫ H.inclusion ≫ B.inclusion = T.inclusion ∧
      v ≫ H.inclusion ≫ B.inclusion = V.inclusion ∧
      a ≫ B.inclusion = A.inclusion ∧ IsNormalSubgroup v ∧
      IsIso (multiplyFactors s v) ∧ IsIso (multiplyFactors a H.inclusion) := by
  let R₀ := subgroupOfSubgroup B R
  let N := conjugate n (subgroupOfSubgroup Bneg Rneg)
  let P := conjugate n R₀
  let S := subgroupOfSubgroup B H
  have hTB : IsSubgroupOf T B := ⟨j, hj⟩
  have hrad := productSections (B := R₀) i v₀ hi hv₀ hiV
  have hAneg (Y : SchemeOver k) : SubgroupSections A Y ≤ SubgroupSections N Y := by
    intro x hx
    exact (conjugateSections n _ x).mpr ((hA Y x).mp hx).2
  have hVpos (Y : SchemeOver k) : SubgroupSections V Y ≤ SubgroupSections P Y := by
    intro x hx
    exact (conjugateSections n _ x).mpr ((hV Y x).mp hx).2
  have hSB : IsSubgroupOf S B := ⟨H.inclusion, rfl⟩
  have hstabilizer (Y : SchemeOver k) (g : Y ⟶ G.val.X) :
      g ∈ SubgroupSections S Y ↔
        ∃ t ∈ SubgroupSections T Y, ∃ v ∈ SubgroupSections V Y, t * v = g := by
    rw [hH Y, ← conjugateSections]
    apply borelSliceIntersection (SubgroupSections N Y) (SubgroupSections T Y)
      (SubgroupSections P Y) (SubgroupSections R₀ Y) (SubgroupSections B Y)
      (SubgroupSections (conjugate n B) Y) (SubgroupSections A Y) (SubgroupSections V Y)
      (hAneg Y) (hVpos Y) (SubgroupSections A Y).one_mem
    · intro t ht x hx
      exact conjugatedRadicalSections_normal Rneg hRneg n
        (section_mem_of_le hTBneg (conjugateInverse_mem_torus n e he ht)) hx
    · exact hrad Y
    · exact borelSections R j hj hjR Y
    · exact conjugatedBorelSections R j hj hjR n e he Y
    · exact hunique Y
  have hTS : IsSubgroupOf T S := by
    apply subgroupFactorThrough
    exact (hstabilizer _ _).mpr ⟨_, inclusion_mem_sections T, 1,
      (SubgroupSections V _).one_mem, mul_one _⟩
  have hVS : IsSubgroupOf V S := by
    apply subgroupFactorThrough
    exact (hstabilizer _ _).mpr ⟨1, (SubgroupSections T _).one_mem,
      _, inclusion_mem_sections V, one_mul _⟩
  obtain ⟨s, hs⟩ := hTS
  obtain ⟨v, hv⟩ := hVS
  let a : A.group ⟶ B.group := i ≫ R.inclusion
  have ha : a ≫ B.inclusion = A.inclusion := (Category.assoc _ _ _).trans hi
  have hcoords (Y : SchemeOver k) := torusFactor_normalCoordinates
    (SubgroupSections N Y) (SubgroupSections T Y) (SubgroupSections P Y)
    (SubgroupSections R₀ Y) (SubgroupSections B Y) (SubgroupSections S Y)
    (SubgroupSections A Y) (SubgroupSections V Y) (hAneg Y) (hVpos Y)
    (hrad Y) (hstabilizer Y) (fun _ hx ↦ section_mem_of_le hSB hx)
    (fun _ hb _ hx ↦ radicalSections_normal R hR hb hx) (hunique Y)
  refine ⟨s, v, a, hs, hv, ha, ?_, ?_, ?_⟩
  · let Y := H.group.X ⊗ V.group.X
    let b : Y ⟶ G.val.X := fst _ _ ≫ S.inclusion.hom.hom
    let z : Y ⟶ G.val.X := snd _ _ ≫ V.inclusion.hom.hom
    have hx := (hcoords Y).2 b ⟨fst _ _, rfl⟩ z ⟨snd _ _, rfl⟩
    change (∃ d : Y ⟶ V.group.X, d ≫ V.inclusion.hom.hom = b * z * b⁻¹) at hx
    obtain ⟨d, hd⟩ := hx
    have hv' : v.hom.hom ≫ S.inclusion.hom.hom = V.inclusion.hom.hom :=
      congrArg (Grp.forget (SchemeOver k)).map hv
    have := monoSubgroup S
    refine ⟨d, (cancel_mono S.inclusion.hom.hom).mp ?_⟩
    simpa only [subgroupConjugation, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc,
      hv', b, z] using hd
  · apply sectionProductIso (B := S) s v hs hv
    · intro Y t t' x x' ht ht' hx hx' heq
      exact (hunique Y 1 t x 1 t' x' (SubgroupSections N Y).one_mem ht (hVpos Y hx)
        (SubgroupSections N Y).one_mem ht' (hVpos Y hx') (by simpa only [one_mul] using heq)).2
    · exact fun Y g ↦ (hstabilizer Y g).mp
  · apply sectionProductIso (H := S) (B := B) a H.inclusion ha rfl
    · intro Y _ _ _ _ ha₁ ha₂ hh₁ hh₂ heq
      exact uniqueMul_of_trivialIntersection (SubgroupSections A Y) (SubgroupSections S Y)
        (hcoords Y).1 ha₁ ha₂ hh₁ hh₂ heq
    · intro Y
      apply borelOrbitFactors (SubgroupSections A Y) (SubgroupSections V Y)
        (SubgroupSections T Y) (SubgroupSections R₀ Y) (SubgroupSections B Y) (SubgroupSections S Y)
      · exact fun g ↦ (borelSections R j hj hjR Y g).mp
      · exact fun g ↦ (hrad Y g).mp
      · exact fun t ht x hx ↦ (hstabilizer Y _).mpr ⟨t, ht, x, hx, rfl⟩
      · exact fun _ ht _ hx ↦ torus_normalizes_slice hR hRneg hTB hTBneg n e he hA Y ht hx

open private splitTorusSmooth from LinearAlgebraicGroups.Reductive.WeylScheme
open private quotientSeparatedFiniteType quotientAct_projection
  from LinearAlgebraicGroups.Reductive.BorelProper
open private quotientAction quotientAction_eval from LinearAlgebraicGroups.Reductive.NormalizerLatticeAction

private theorem smoothBorel_of_product {T B : ClosedSubgroup G.val}
    (hT : IsSplitTorus T.group) (R : ClosedSubgroup B.group)
    (hR : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) R)
    (j : T.group ⟶ B.group) (h : IsIso (multiplyFactors j R.inclusion)) :
    Smooth B.group.X.hom := by
  let : Smooth T.group.X.hom := splitTorusSmooth hT
  let : Smooth R.group.X.hom := hR.1.1
  let : Smooth (T.group.X ⊗ R.group.X).hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  rw [← Over.w (inv (multiplyFactors j R.inclusion))]
  infer_instance

private theorem quotientAction_mul {B : ClosedSubgroup G.val} (Q : Presentation B) :
    lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ Q.projection) ≫ (quotientAction Q).smul =
      μ[G.val.X] ≫ Q.projection := by
  simp only [quotientAction_eval, quotientAct_projection, MonObj.mul_eq_mul]

set_option maxHeartbeats 1000000 in
private def cellOfOrbit {T B A : ClosedSubgroup G.val} (Q : Presentation B)
    (a : ModObj G.val.X Q.scheme)
    (ha : lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ Q.projection) ≫ a.smul =
      μ[G.val.X] ≫ Q.projection)
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X)
    (P : SmoothOrbit.Presentation (restrictGroupAction B.inclusion a) (n ≫ Q.projection))
    (j : A.group ⟶ B.group) (hj : j ≫ B.inclusion = A.inclusion)
    [IsIso (multiplyFactors j P.stabilizer.inclusion)]
    (ht : ∀ (Y : SchemeOver k) (t : Y ⟶ T.group.X),
      conjugatePoint n⁻¹ (t ≫ T.inclusion.hom.hom) ∈ SubgroupSections B Y)
    (htA : ∀ (Y : SchemeOver k) (t : Y ⟶ T.group.X) (x : Y ⟶ A.group.X),
      let s := t ≫ T.inclusion.hom.hom
      s * (x ≫ A.inclusion.hom.hom) * s⁻¹ ∈ SubgroupSections A Y)
    (c : Cocharacter T.group) (L : LimitDecomposition (c ≫ T.inclusion))
    (hA : IsSubgroupOf A L.contracting) : Cell (T := T) Q a n A := by
  let i := P.openInClosure ≫ SmoothOrbit.closureInclusion _ _
  letI : IsOpenImmersion P.openInClosure.left := P.isOpen
  have hi : IsImmersion i.left := by
    change IsImmersion (P.openInClosure.left ≫
      (SmoothOrbit.orbitMap (restrictGroupAction B.inclusion a) (n ≫ Q.projection)).left.imageι)
    infer_instance
  letI : Mono i := Over.mono_of_mono_left i
  have hq : P.projection ≫ i =
      lift B.inclusion.hom.hom (toUnit B.group.X ≫ n ≫ Q.projection) ≫ a.smul := by
    rw [orbitProjection_eq P, SmoothOrbit.orbitMap, restrictGroupAction_smul,
      lift_map_assoc, Category.comp_id, Category.id_comp]
  letI := orbitIso_of_factorization P j
  let e : A.group.X ≅ P.orbit := asIso (j.hom.hom ≫ P.projection)
  have he : e.hom ≫ i = (A.inclusion.hom.hom * (toUnit A.group.X ≫ n)) ≫ Q.projection := by
    have hj' : j.hom.hom ≫ B.inclusion.hom.hom = A.inclusion.hom.hom :=
      congrArg (Grp.forget (SchemeOver k)).map hj
    have hc : j.hom.hom ≫ (toUnit B.group.X ≫ n ≫ Q.projection) =
        (toUnit A.group.X ≫ n) ≫ Q.projection := by
      simp only [Category.assoc, comp_constant]
    change (j.hom.hom ≫ P.projection) ≫ i = _
    rw [Category.assoc, hq, comp_lift_assoc, hj', hc]
    exact actionOnQuotient Q a ha A.inclusion.hom.hom (toUnit A.group.X ≫ n)
  let D := A.group.X ⊗ B.group.X
  let m : D ⟶ G.val.X := (fst _ _ ≫ A.inclusion.hom.hom) * (toUnit D ≫ n) *
    (snd _ _ ≫ B.inclusion.hom.hom)
  have hp := doubleOrbitPullback Q n i e he
  have hm : IsImmersion m.left :=
    MorphismProperty.of_isPullback (P := @IsImmersion) ((hp.map (Over.forget _)).flip) hi
  refine {
    orbit := P.orbit
    orbitInclusion := i
    orbitImmersion := hi
    projection := P.projection
    projection_eq := hq
    orbitSurjective := P.surjective
    orbitIso := e
    orbitIso_eq := he
    stabilizer := P.stabilizer
    representsStabilizer := ?_
    quotientIso := P.quotientIso
    quotientProjection := P.quotientProjection
    doubleOrbit := D
    doubleOrbitInclusion := m
    doubleOrbitImmersion := hm
    toOrbit := fst _ _ ≫ e.hom
    isInverseImage := hp
    doubleOrbitIso := Iso.refl D
    doubleOrbitIso_eq := Category.id_comp _
    doubleOrbitSections := doubleOrbitSections_of_pullback Q a ha n ⟨j, hj⟩ i P.projection hq e he
    uniqueGeometricFixedPoint := ?_
  }
  · intro Y b
    simpa only [Stabilizes, restrictGroupAction_smul, lift_map_assoc, Category.comp_id] using
      P.representsStabilizer Y b
  · intro K _ _ _ y
    let u := y ≫ e.inv
    have hu : y ≫ i = ((u ≫ A.inclusion.hom.hom) * (toUnit _ ≫ n)) ≫ Q.projection := by
      calc
        y ≫ i = u ≫ e.hom ≫ i := by simp [u]
        _ = _ := by rw [he, ← Category.assoc, MonObj.comp_mul, comp_constant]
    rw [hu]
    have hf : Mono ((A.inclusion.hom.hom * (toUnit A.group.X ≫ n)) ≫ Q.projection) :=
      he ▸ (inferInstance : Mono (e.hom ≫ i))
    exact fixedInContractingOrbit Q a ha n ht htA hf c L hA (CommAlgCat.of k K) u

private theorem normalizerBorelCentralizes {T B : ClosedSubgroup G.val}
    [IsCommMonObj T.group.X] (j : T.group ⟶ B.group) (q : B.group ⟶ T.group)
    (hj : j ≫ B.inclusion = T.inclusion) (hq : j ≫ q = 𝟙 T.group)
    {Y : SchemeOver k} {g : Y ⟶ G.val.X} (hn : Normalizes T.inclusion g)
    (hb : g ∈ SubgroupSections B Y) : Centralizes T.inclusion g := by
  have := monoSubgroup B
  change (∃ b : Y ⟶ B.group.X, b ≫ B.inclusion.hom.hom = g) at hb
  obtain ⟨b, hb⟩ := hb
  obtain ⟨e, _, he⟩ := hn
  let Z := T.group.X ⊗ Y
  let s : Z ⟶ B.group.X := snd _ _ ≫ b
  let t : Z ⟶ T.group.X := fst _ _
  let t' : Z ⟶ T.group.X := e.hom ≫ t
  have hs : s ≫ B.inclusion.hom.hom = snd _ _ ≫ g := by
    rw [show s = snd _ _ ≫ b from rfl, Category.assoc, hb]
  have hj' : j.hom.hom ≫ B.inclusion.hom.hom = T.inclusion.hom.hom :=
    congrArg (Grp.forget (SchemeOver k)).map hj
  have hconj : s * (t ≫ j.hom.hom) * s⁻¹ = t' ≫ j.hom.hom := by
    apply (cancel_mono B.inclusion.hom.hom).mp
    simpa only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hj', hs, t, t',
      conjugateFamily] using he.symm
  have hq' : j.hom.hom ≫ q.hom.hom = 𝟙 T.group.X :=
    congrArg (Grp.forget (SchemeOver k)).map hq
  have ht : t = t' := by
    have h := congrArg (fun f : Z ⟶ B.group.X ↦ f ≫ q.hom.hom) hconj
    simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hq', Category.comp_id] at h
    rw [mul_comm (s ≫ q.hom.hom) t, mul_inv_cancel_right] at h
    exact h
  change conjugateFamily T.inclusion g = t ≫ T.inclusion.hom.hom
  rw [← he]
  change t' ≫ T.inclusion.hom.hom = t ≫ T.inclusion.hom.hom
  rw [← ht]

open private isTorus_iff_coordinates from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private torus_of_split from LinearAlgebraicGroups.Solvable.GeometricTorusSplitting

private theorem distinctRepresentativeCosets {T B : ClosedSubgroup G.val}
    [IsCommMonObj T.group.X] {D : Datum T} (I : Identification D)
    (hG : IsReductive G) (hT : IsSplitTorus T.group) (hmax : IsGeometricallyMaximal T)
    (j : T.group ⟶ B.group) (q : B.group ⟶ T.group)
    (hj : j ≫ B.inclusion = T.inclusion) (hq : j ≫ q = 𝟙 T.group)
    (Q : Presentation B)
    (n : D.rootDatum.weylGroup → (𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X))
    (hn : ∀ w, IsRepresentative I w (n w)) {Y : SchemeOver k} (y : Y.left)
    (w v : D.rootDatum.weylGroup)
    (heq : toUnit Y ≫ (n w ≫ I.normalizer.inclusion.hom.hom) ≫ Q.projection =
      toUnit Y ≫ (n v ≫ I.normalizer.inclusion.hom.hom) ≫ Q.projection) : w = v := by
  let p := fun w ↦ toUnit Y ≫ n w
  let d := (p w)⁻¹ * p v
  have hb : d ≫ I.normalizer.inclusion.hom.hom ∈ SubgroupSections B Y := by
    have h := (projection_eq_iff Q (p w ≫ I.normalizer.inclusion.hom.hom)
      (p v ≫ I.normalizer.inclusion.hom.hom)).mp (by simpa only [p, Category.assoc] using heq)
    simpa only [d, MonObj.mul_comp, GrpObj.inv_comp] using h
  have hnorm : Normalizes T.inclusion (d ≫ I.normalizer.inclusion.hom.hom) :=
    (I.representsNormalizer Y _).mpr ⟨d, rfl⟩
  have hcent := normalizerBorelCentralizes j q hj hq hnorm hb
  have ht := (isTorus_iff_coordinates (closedSubgroupAlgebraicGroup T)).mpr (torus_of_split hT)
  have hCT := Reductive.TorusCentralizer.maximalTorusCentralizer G hG T ht hmax
  obtain ⟨t, ht⟩ := (hCT Y _).mp hcent
  have hinc : I.torusInclusion.hom.hom ≫ I.normalizer.inclusion.hom.hom = T.inclusion.hom.hom :=
    congrArg (Grp.forget (SchemeOver k)).map I.inclusion_eq
  have := monoSubgroup I.normalizer
  have hd : d = t ≫ I.torusInclusion.hom.hom := (cancel_mono I.normalizer.inclusion.hom.hom).mp
    (by rw [Category.assoc, hinc, ht])
  have hker : I.torusInclusion.hom.hom ≫ I.quotient.hom.hom = toUnit T.group.X ≫ η[I.scheme.val.X] :=
    I.isQuotient.1.w
  have hquot : d ≫ I.quotient.hom.hom = 1 := by
    rw [hd, Category.assoc, hker, ← Category.assoc, toUnit_unique (t ≫ toUnit _) (toUnit Y)]
    rfl
  have h := inv_mul_eq_one.mp (by simpa only [d, MonObj.mul_comp, GrpObj.inv_comp] using hquot :
    (p w ≫ I.quotient.hom.hom)⁻¹ * (p v ≫ I.quotient.hom.hom) = 1)
  have hp (a : D.rootDatum.weylGroup) : p a ≫ I.quotient.hom.hom =
      toUnit Y ≫ I.image.constantGroup.sectionPoint (I.labelEquiv a) := by
    rw [show p a = toUnit Y ≫ n a from rfl, Category.assoc, hn a]
  have hs := congrArg (fun f ↦ I.image.constantGroup.families Y f) h
  rw [hp w, hp v, I.image.constantGroup.constant, I.image.constantGroup.constant] at hs
  exact I.labelEquiv.injective (congrArg (fun f : LocallyConstant Y.left I.image.labels ↦ f y) hs)

open private exists_field_point from LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus

private theorem geometricPoint_of_commonImage {X Y S : SchemeOver k} (f : X ⟶ S) (g : Y ⟶ S)
    (x : X.left) (y : Y.left) (h : f.left x = g.left y) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : IsAlgClosed K)
      (p : Over.mk (fieldSpecMap k K) ⟶ X) (q : Over.mk (fieldSpecMap k K) ⟶ Y), p ≫ f = q ≫ g := by
  let F := pullback f g
  have hp := (IsPullback.of_hasPullback f g).map (Over.forget _)
  obtain ⟨z, _, _⟩ := Scheme.exists_preimage_of_isPullback hp x y h
  obtain ⟨L, _, _, r, _⟩ := exists_field_point F z
  let K := AlgebraicClosure L
  let φ := (algebraMap L K).comp (algebraMap k L)
  let : Algebra k K := φ.toAlgebra
  let e : Over.mk (fieldSpecMap k K) ⟶ (testSpec k).obj (.op (CommAlgCat.of k L)) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap L K))) (by
      exact (Spec.map_comp (CommRingCat.ofHom (algebraMap k L))
        (CommRingCat.ofHom (algebraMap L K))).symm)
  refine ⟨K, inferInstance, inferInstance, inferInstance, (e ≫ r) ≫ pullback.fst f g,
    (e ≫ r) ≫ pullback.snd f g, ?_⟩
  simp only [Category.assoc, pullback.condition]

private theorem cellProjection_formula {T B A : ClosedSubgroup G.val} (Q : Presentation B)
    (a : ModObj G.val.X Q.scheme)
    (ha : lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ Q.projection) ≫ a.smul =
      μ[G.val.X] ≫ Q.projection)
    {n : 𝟙_ (SchemeOver k) ⟶ G.val.X}
    (C : Cell (T := T) Q a n A) {Y : SchemeOver k} (b : Y ⟶ B.group.X) :
    (b ≫ C.projection) ≫ C.orbitInclusion =
      ((b ≫ B.inclusion.hom.hom) * (toUnit Y ≫ n)) ≫ Q.projection := by
  rw [Category.assoc, C.projection_eq, comp_lift_assoc]
  have h : b ≫ (toUnit B.group.X ≫ n ≫ Q.projection) = (toUnit Y ≫ n) ≫ Q.projection := by
    simp only [Category.assoc, comp_constant]
  rw [h, actionOnQuotient Q a ha]

private theorem cellPoint_lifts {T B A : ClosedSubgroup G.val} (Q : Presentation B)
    (a : ModObj G.val.X Q.scheme)
    (ha : lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ Q.projection) ≫ a.smul =
      μ[G.val.X] ≫ Q.projection)
    {n : 𝟙_ (SchemeOver k) ⟶ G.val.X}
    (C : Cell (T := T) Q a n A) (hAB : IsSubgroupOf A B)
    {Y : SchemeOver k} (y : Y ⟶ C.orbit) : ∃ b : Y ⟶ B.group.X, b ≫ C.projection = y := by
  obtain ⟨j, hj⟩ := hAB
  let z := y ≫ C.orbitIso.inv
  have hj' : j.hom.hom ≫ B.inclusion.hom.hom = A.inclusion.hom.hom :=
    congrArg (Grp.forget (SchemeOver k)).map hj
  have : IsImmersion C.orbitInclusion.left := C.orbitImmersion
  have : Mono C.orbitInclusion := Over.mono_of_mono_left _
  refine ⟨z ≫ j.hom.hom, (cancel_mono C.orbitInclusion).mp ?_⟩
  rw [cellProjection_formula Q a ha, Category.assoc, hj']
  calc
    _ = z ≫ (C.orbitIso.hom ≫ C.orbitInclusion) := by
      rw [C.orbitIso_eq, ← Category.assoc, MonObj.comp_mul, comp_constant]
    _ = y ≫ C.orbitInclusion := by simp [z]

private theorem markedCoset_of_meetingCells {T B A A' : ClosedSubgroup G.val} (Q : Presentation B)
    (a : ModObj G.val.X Q.scheme)
    (ha : lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ Q.projection) ≫ a.smul =
      μ[G.val.X] ≫ Q.projection)
    {n n' : 𝟙_ (SchemeOver k) ⟶ G.val.X}
    (C : Cell (T := T) Q a n A) (C' : Cell (T := T) Q a n' A')
    (hAB : IsSubgroupOf A B) (hA'B : IsSubgroupOf A' B)
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K]
    (y : Over.mk (fieldSpecMap k K) ⟶ C.orbit) (y' : Over.mk (fieldSpecMap k K) ⟶ C'.orbit)
    (hy : y ≫ C.orbitInclusion = y' ≫ C'.orbitInclusion) :
    toUnit (Over.mk (fieldSpecMap k K)) ≫ n ≫ Q.projection =
      toUnit (Over.mk (fieldSpecMap k K)) ≫ n' ≫ Q.projection := by
  let Y := Over.mk (fieldSpecMap k K)
  obtain ⟨b, hb⟩ := cellPoint_lifts Q a ha C hAB y
  obtain ⟨b', hb'⟩ := cellPoint_lifts Q a ha C' hA'B y'
  rw [← hb, ← hb', cellProjection_formula Q a ha, cellProjection_formula Q a ha] at hy
  let z := (b⁻¹ * b') ≫ C'.projection
  have hz : z ≫ C'.orbitInclusion = toUnit Y ≫ n ≫ Q.projection := by
    have h := congrArg (fun s ↦ lift (b ≫ B.inclusion.hom.hom)⁻¹ s ≫ a.smul) hy
    simp only [actionOnQuotient Q a ha, ← mul_assoc, inv_mul_cancel, one_mul] at h
    simpa only [z, cellProjection_formula Q a ha, MonObj.mul_comp, GrpObj.inv_comp,
      Category.assoc] using h.symm
  let e : Y ⟶ C.orbit := (1 : Y ⟶ B.group.X) ≫ C.projection
  have he : e ≫ C.orbitInclusion = toUnit Y ≫ n ≫ Q.projection := by
    simp only [e, cellProjection_formula Q a ha, MonObj.one_comp, one_mul, Category.assoc]
  have hf := (C.uniqueGeometricFixedPoint K e).mpr he
  have hf' : FixedOver (T := T) a (z ≫ C'.orbitInclusion) := (he.trans hz.symm) ▸ hf
  exact hz.symm.trans ((C'.uniqueGeometricFixedPoint K z).mp hf')

private theorem doubleOrbit_disjoint {T B A A' : ClosedSubgroup G.val} {Q : Presentation B}
    {a : ModObj G.val.X Q.scheme} {n n' : 𝟙_ (SchemeOver k) ⟶ G.val.X}
    (C : Cell (T := T) Q a n A) (C' : Cell (T := T) Q a n' A')
    (h : Disjoint (Set.range C.orbitInclusion.left) (Set.range C'.orbitInclusion.left)) :
    Disjoint (Set.range C.doubleOrbitInclusion.left) (Set.range C'.doubleOrbitInclusion.left) := by
  apply Set.disjoint_left.mpr
  rintro g ⟨x, hx⟩ ⟨y, hy⟩
  have eq := congrArg (fun f : C.doubleOrbit ⟶ Q.scheme ↦ f.left x) C.isInverseImage.w
  have eq' := congrArg (fun f : C'.doubleOrbit ⟶ Q.scheme ↦ f.left y) C'.isInverseImage.w
  change Q.projection.left (C.doubleOrbitInclusion.left x) =
    C.orbitInclusion.left (C.toOrbit.left x) at eq
  change Q.projection.left (C'.doubleOrbitInclusion.left y) =
    C'.orbitInclusion.left (C'.toOrbit.left y) at eq'
  rw [hx] at eq
  rw [hy] at eq'
  exact Set.disjoint_left.mp h ⟨C.toOrbit.left x, eq.symm⟩ ⟨C'.toOrbit.left y, eq'.symm⟩

set_option maxHeartbeats 2000000 in
/-- The split Bruhat orbit parametrization follows from Borel positivity and the
ordered root product theorems, with the four premises in the assigned order. -/
theorem bruhatOrbitParametrization_conditional.{v}
    (borelPositivity : Specs.BorelPositivity.Statement.{v})
    (borelRadicalProduct : Specs.OrderedRootProducts.BorelRadicalProduct.{v})
    (contractingProduct : Specs.OrderedRootProducts.ContractingProduct.{v})
    (regularRootCell : Specs.OrderedRootProducts.RegularRootCell.{v}) :
    Specs.BruhatOrbitParametrization.Statement.{v} := by
  classical
  intro k _ G hG T B hT hmax hB hTB
  obtain ⟨hcomm, hdata⟩ := borelPositivity G hG T hT hmax
  let := hcomm
  obtain ⟨D, ⟨I⟩, hCorr, _, ⟨U⟩, hdecomp⟩ := hdata
  obtain ⟨Bneg, hBneg, hTBneg, hneg⟩ := existsOppositeBorel hB hTB hCorr
  obtain ⟨R, j, q, hR, _, hj, hjq, _, hjR, hp⟩ := hdecomp B hB hTB
  obtain ⟨Rneg, hRneg, hpneg⟩ := borelRadicalProduct G hG T hT hmax Bneg hBneg hTBneg
  have hprod : OrderedParametrization U (subgroupRoots T B) (subgroupOfSubgroup B R) :=
    hp U
  have hprodneg : OrderedParametrization U (subgroupRoots T B)ᶜ (subgroupOfSubgroup Bneg Rneg) :=
    fun l hl ↦ hpneg U l (hneg.symm ▸ hl)
  have hpos := hCorr.1 B hB hTB
  obtain ⟨c, L, _, _, hL⟩ := regularBorelContracting contractingProduct hG D hT hmax U R hprod hpos
  refine ⟨hcomm, D, I, U, Bneg, R, Rneg, hBneg, hTBneg, hneg, hR, hRneg,
    representativeExists I hT, (HomogeneousQuotient.homogeneousQuotient k G B).1, ?_⟩
  intro Q
  let a := quotientAction Q
  have ha := quotientAction_mul Q
  have ⟨hsep, hft⟩ := quotientSeparatedFiniteType Q
  have hqc : QuasiCompact Q.scheme.hom := by
    let : IsAffine G.val.X.left := G.property.1
    let : CompactSpace Q.scheme.left :=
      Function.Surjective.compactSpace Q.projection.left.continuous Q.surjective.1
    exact (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance
  have hsB := smoothBorel_of_product hT R hR j hjR
  refine ⟨a, ha, ?_⟩
  intro n hn
  dsimp only
  let g := fun w ↦ n w ≫ I.normalizer.inclusion.hom.hom
  let perm := D.rootDatum.weylGroupToPerm
  have cells (w : D.rootDatum.weylGroup) :
      ∃ (A V : ClosedSubgroup G.val) (C : Cell (T := T) Q a (g w) A),
        RootFactors U R (subgroupOfSubgroup Bneg Rneg) (g w)
          (subgroupRoots T B ∩ (perm w '' subgroupRoots T Bneg))
          (subgroupRoots T B ∩ (perm w '' subgroupRoots T B))
          A V C.stabilizer ∧ IsSubgroupOf A B := by
    obtain ⟨A, V, hA, hV, hAp, hVp, hmul, hU⟩ :=
      translatedRadicalProducts contractingProduct regularRootCell hG I hT hmax U R
        (subgroupOfSubgroup Bneg Rneg) hprod hprodneg hpos w (n w) (hn w)
    obtain ⟨P⟩ := _root_.LinearAlgebraicGroups.SmoothOrbit.schemeOrbit k
      (closedSubgroupAlgebraicGroup B) Q.scheme (restrictGroupAction B.inclusion a)
      (g w ≫ Q.projection) hsB hsep hft hqc
    have hS := stabilizer_isConjugateIntersection Q a ha (g w) P.stabilizer P.representsStabilizer
    let e := I.image.conjugation (I.labelEquiv w)
    have he := representativeConjugation I (hn w)
    obtain ⟨i, v₀, hi, hv₀, hiV⟩ := hmul
    obtain ⟨s, v, jA, hs, hv, hjA, hvNormal, hsv, hjAStab⟩ :=
      bruhatStabilizerProducts hR hRneg hTBneg j hj hjR (g w) e he
        hA hV i v₀ hi hv₀ hiV P.stabilizer hS hU
    let := hjAStab
    have hAc : IsSubgroupOf A L.contracting := by
      apply subgroupFactorThrough
      apply (subgroupSections_of_sameSubgroup hL _).mp
      exact ((hA _ _).mp (inclusion_mem_sections A)).1
    let C : Cell (T := T) Q a (g w) A := cellOfOrbit Q a ha (g w) P jA hjA
      (fun Y t ↦ section_mem_of_le hTB (conjugateInverse_mem_torus (g w) e he (Y := Y) ⟨t, rfl⟩))
      (fun Y t z ↦ torus_normalizes_slice hR hRneg hTB hTBneg (g w) e he hA Y ⟨t, rfl⟩ ⟨z, rfl⟩)
      c L hAc
    refine ⟨A, V, C, ?_, ⟨jA, hjA⟩⟩
    change RootFactors U R (subgroupOfSubgroup Bneg Rneg) (g w)
      (subgroupRoots T B ∩ (perm w '' subgroupRoots T Bneg))
      (subgroupRoots T B ∩ (perm w '' subgroupRoots T B)) A V P.stabilizer
    refine ⟨hA, hV, ?_, hVp, ⟨i, v₀, hi, hv₀, hiV⟩, hS, s, v, hs, hv, hvNormal, hsv⟩
    rw [hneg]
    exact hAp
  choose A V C hC using cells
  refine ⟨A, V, C, fun w ↦ (hC w).1, ?_⟩
  intro w v hne
  have hdis : Disjoint (Set.range (C w).orbitInclusion.left)
      (Set.range (C v).orbitInclusion.left) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    obtain ⟨K, _, _, _, x', y', hx'y'⟩ :=
      geometricPoint_of_commonImage (C w).orbitInclusion (C v).orbitInclusion x y hy.symm
    have heq := markedCoset_of_meetingCells Q a ha (C w) (C v) (hC w).2 (hC v).2 K x' y' hx'y'
    exact hne (distinctRepresentativeCosets I hG hT hmax j q hj hjq Q n hn
      (IsLocalRing.closedPoint K) w v heq)
  exact ⟨hdis, doubleOrbit_disjoint (C w) (C v) hdis⟩


end

end LinearAlgebraicGroups.Flag.BruhatOrbitParametrization

universe v8_closure_5aa2b27e544d8cef_u0
theorem _root_.«LinearAlgebraicGroups».«Flag».«BruhatOrbitParametrization».«bruhatOrbitParametrization» : _root_.«LinearAlgebraicGroups».«Specs».«BruhatOrbitParametrization».«Statement».{v8_closure_5aa2b27e544d8cef_u0} :=
  @_root_.«LinearAlgebraicGroups».«Flag».«BruhatOrbitParametrization».«bruhatOrbitParametrization_conditional».{v8_closure_5aa2b27e544d8cef_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«BorelPositivity».«borelPositivity».{v8_closure_5aa2b27e544d8cef_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«OrderedRootProducts».«borelRadicalProduct».{v8_closure_5aa2b27e544d8cef_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«OrderedRootProducts».«contractingProduct».{v8_closure_5aa2b27e544d8cef_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«OrderedRootProducts».«regularRootCell».{v8_closure_5aa2b27e544d8cef_u0})
