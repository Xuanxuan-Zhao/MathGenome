import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.SimpleParabolicProduct
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.RightQuotientSheaf
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Group

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.BruhatOrbitParametrization
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SimpleRoots
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj Pointwise

universe u

namespace LinearAlgebraicGroups.Flag.SimpleParabolicProduct

open LinearAlgebraicGroups.Specs
open Specs.SimpleParabolicProduct
open Specs.AbstractPairing (Datum Root)
open Specs.BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open Specs.BruhatOrbitParametrization (IsRepresentative)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (absoluteRoots adjointWeightSpace adjointWeightVectors pairing)
open Specs.DatumAndWeyl (Identification)
open Specs.GeometricBorelConjugacy (IsKBorel subgroupOfSubgroup)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open Specs.OrderedRootProducts (Enumerates Parametrizes RootSubgroupFamily)
open Specs.QuotientEmbedding (Presentation)
open Specs.RankOneFlag (Centralizer IsGeometricallyMaximal SameSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition lieImage multiplyFactors)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option linter.style.haveILetI false

section DoubleCosets

variable {M : Type*} [Group M]

private theorem doubleCoset_mul_rule {W : Type*} [Group W] (B P U : Subgroup M)
    (n : W → M) (s : W) (pos : W → Prop)
    (hs : s * s = 1) (hpos : ∀ v, ¬ pos v → pos (v * s))
    (hP : (P : Set M) = (B : Set M) ∪ ((B : Set M) * {n s} * (B : Set M)))
    (hU : (B : Set M) * {n s} * (B : Set M) = (U : Set M) * {n s} * (B : Set M))
    (hslide : ∀ v, pos v → ∀ a ∈ U, n v * a * (n v)⁻¹ ∈ B)
    (hmul : ∀ v, ∃ b ∈ B, n v * n s = n (v * s) * b) :
    let C := fun v ↦ (B : Set M) * {n v} * (B : Set M)
    ∀ v, C v * (P : Set M) = C v ∪ C (v * s) ∧
      (pos v → C v * C s = C (v * s)) := by
  classical
  let D := fun x : M ↦ (B : Set M) * {x} * (B : Set M)
  have hBB : (B : Set M) * (B : Set M) = B := by
    ext a
    constructor
    · intro ha
      obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp ha
      exact B.mul_mem hx hy
    · intro ha
      exact Set.mem_mul.mpr ⟨a, ha, 1, B.one_mem, mul_one a⟩
  have memD {x z : M} : z ∈ D x ↔ ∃ a ∈ B, ∃ b ∈ B, a * x * b = z := by
    constructor
    · intro h
      obtain ⟨_, hd, b, hb, rfl⟩ := Set.mem_mul.mp h
      obtain ⟨a, ha, y, hy, rfl⟩ := Set.mem_mul.mp hd
      exact ⟨a, ha, b, hb, by rw [Set.mem_singleton_iff.mp hy]⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact Set.mem_mul.mpr ⟨_, Set.mem_mul.mpr ⟨a, ha, x, rfl, rfl⟩, b, hb, rfl⟩
  have hright (x : M) {b : M} (hb : b ∈ B) : D (x * b) = D x := by
    ext z
    constructor
    · intro h
      obtain ⟨a, ha, c, hc, rfl⟩ := memD.mp h
      exact memD.mpr ⟨a, ha, b * c, B.mul_mem hb hc, by group⟩
    · intro h
      obtain ⟨a, ha, c, hc, rfl⟩ := memD.mp h
      exact memD.mpr ⟨a, ha, b⁻¹ * c, B.mul_mem (B.inv_mem hb) hc, by group⟩
  have hstep (v : W) (hv : pos v) : D (n v) * D (n s) = D (n (v * s)) := by
    obtain ⟨b, hb, hbmul⟩ := hmul v
    rw [← hright (n (v * s)) hb, ← hbmul]
    have hrewrite : D (n v) * D (n s) =
        ((B : Set M) * {n v}) * ((U : Set M) * {n s} * (B : Set M)) := by
      change (((B : Set M) * {n v}) * (B : Set M)) *
        (((B : Set M) * {n s}) * (B : Set M)) = _
      simp only [mul_assoc, ← hU]
      rw [← mul_assoc (B : Set M) (B : Set M), hBB]
    rw [hrewrite]
    ext z
    constructor
    · intro h
      obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp h
      obtain ⟨a, ha, xv, hxv, rfl⟩ := Set.mem_mul.mp hx
      obtain ⟨q, hq, c, hc, rfl⟩ := Set.mem_mul.mp hy
      obtain ⟨z, hz, xs, hxs, rfl⟩ := Set.mem_mul.mp hq
      rw [Set.mem_singleton_iff.mp hxv, Set.mem_singleton_iff.mp hxs]
      exact memD.mpr ⟨a * (n v * z * (n v)⁻¹), B.mul_mem ha (hslide v hv z hz),
        c, hc, by group⟩
    · intro h
      obtain ⟨a, ha, c, hc, rfl⟩ := memD.mp h
      exact Set.mem_mul.mpr ⟨a * n v, Set.mem_mul.mpr ⟨a, ha, n v, rfl, rfl⟩,
        (1 * n s) * c, Set.mem_mul.mpr
          ⟨_, Set.mem_mul.mpr ⟨1, U.one_mem, n s, rfl, rfl⟩, c, hc, rfl⟩, by group⟩
  have hBP : B ≤ P := fun _ h => show _ ∈ (P : Set M) from hP.symm ▸ Or.inl h
  have hsP : n s ∈ (P : Set M) := hP.symm ▸ Or.inr
    (memD.mpr ⟨1, B.one_mem, 1, B.one_mem, by simp⟩)
  have hDmulB (v : W) : D (n v) * (B : Set M) = D (n v) := by
    unfold D
    rw [mul_assoc, hBB]
  have hplus (v : W) (hv : pos v) :
      D (n v) * (P : Set M) = D (n v) ∪ D (n (v * s)) := by
    rw [hP, Set.mul_union, hstep v hv, hDmulB]
  change ∀ v, D (n v) * (P : Set M) = D (n v) ∪ D (n (v * s)) ∧ _
  intro v
  refine ⟨?_, hstep v⟩
  by_cases hv : pos v
  · exact hplus v hv
  have hvs : v * s * s = v := by rw [mul_assoc, hs, mul_one]
  have hprev := hplus (v * s) (hpos v hv)
  rw [hvs, Set.union_comm] at hprev
  apply le_antisymm
  · rw [← hprev]
    intro z hz
    obtain ⟨a, ha, p, hp, rfl⟩ := Set.mem_mul.mp hz
    obtain ⟨x, hx, q, hq, hxa⟩ : ∃ x ∈ D (n (v * s)), ∃ q ∈ P, x * q = a :=
      Set.mem_mul.mp (hprev.symm ▸ Or.inl ha)
    exact Set.mem_mul.mpr ⟨x, hx, q * p, P.mul_mem hq hp, by rw [← mul_assoc, hxa]⟩
  · intro z hz
    rcases hz with hz | hz
    · exact Set.mem_mul.mpr ⟨z, hz, 1, P.one_mem, mul_one _⟩
    · obtain ⟨a, ha, b, hb, rfl⟩ := memD.mp hz
      obtain ⟨c, hc, hnc⟩ := hmul v
      refine Set.mem_mul.mpr ⟨a * n v, memD.mpr ⟨a, ha, 1, B.one_mem, mul_one _⟩,
        n s * c⁻¹ * b, P.mul_mem (P.mul_mem hsP (P.inv_mem (hBP hc))) (hBP hb), ?_⟩
      calc
        a * n v * (n s * c⁻¹ * b) = a * (n v * n s) * c⁻¹ * b := by group
        _ = _ := by rw [hnc]; group

private theorem doubleCoset_disjoint (B : Subgroup M) (n : M) (hn : n ∉ B) :
    Disjoint (B : Set M) ((B : Set M) * {n} * (B : Set M)) := by
  apply Set.disjoint_left.mpr
  intro x hx hd
  obtain ⟨_, hab, b, hb, rfl⟩ := Set.mem_mul.mp hd
  obtain ⟨a, ha, y, hy, rfl⟩ := Set.mem_mul.mp hab
  rw [Set.mem_singleton_iff.mp hy] at hx
  apply hn
  have hh := B.mul_mem (B.inv_mem ha) (B.mul_mem hx (B.inv_mem hb))
  convert hh using 1
  group

private theorem doubleCoset_of_rank_one_decomposition (B P U : Subgroup M)
    (n : M) (hU : U ≤ B) (hn : n ∉ B)
    (hP : (P : Set M) = (B : Set M) ∪ ((U : Set M) * {n} * (B : Set M))) :
    (P : Set M) = (B : Set M) ∪ ((B : Set M) * {n} * (B : Set M)) ∧
    Disjoint (B : Set M) ((B : Set M) * {n} * (B : Set M)) ∧
    (B : Set M) * {n} * (B : Set M) = (U : Set M) * {n} * (B : Set M) := by
  have hdis := doubleCoset_disjoint B n hn
  have heq : (B : Set M) * {n} * (B : Set M) = (U : Set M) * {n} * (B : Set M) := by
    refine le_antisymm ?_ (Set.mul_subset_mul_right (Set.mul_subset_mul_right hU))
    have hBP : B ≤ P := fun _ hx =>
      show _ ∈ (P : Set M) from hP.symm ▸ Or.inl hx
    have hnP : n ∈ (P : Set M) := hP.symm ▸ Or.inr (Set.mem_mul.mpr
      ⟨1 * n, Set.mem_mul.mpr ⟨1, U.one_mem, n, rfl, rfl⟩, 1, B.one_mem, by simp⟩)
    intro x hx
    have hxP : x ∈ (P : Set M) := by
      obtain ⟨_, hab, b, hb, rfl⟩ := Set.mem_mul.mp hx
      obtain ⟨a, ha, y, hy, rfl⟩ := Set.mem_mul.mp hab
      rw [Set.mem_singleton_iff.mp hy]
      exact P.mul_mem (P.mul_mem (hBP ha) hnP) (hBP hb)
    rcases (hP ▸ hxP) with hxB | hxU
    · exact (Set.disjoint_left.mp hdis hxB hx).elim
    · exact hxU
  exact ⟨by rw [heq, hP], hdis, heq⟩

end DoubleCosets

section Wall

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
  {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]

private theorem evaluate_root (D : Datum T) (c : Cocharacter T.group) (α : Root T) :
    SimpleRoots.evaluate D c (D.rootDatum.root α) = pairing T.group α.val c := by
  rw [D.root_eq]
  exact D.pairing_eq _ _

private theorem reflection_square (D : Datum T) (α : Root T) :
    RootPairing.weylGroup.ofIdx D.rootDatum α * RootPairing.weylGroup.ofIdx D.rootDatum α = 1 := by
  apply Subtype.ext
  let r := RootPairing.Equiv.reflection D.rootDatum α
  change r * r = 1
  calc
    r * r = r⁻¹ * r := congrArg (· * r) (RootPairing.Equiv.reflection_inv D.rootDatum α).symm
    _ = 1 := inv_mul_cancel r

private theorem opposite_root (D : Datum T) (α : Root T) :
    (D.rootDatum.reflectionPerm α α).val = α.val⁻¹ := by
  have he := (D.rootDatum.root_reflectionPerm α α).trans (D.rootDatum.reflection_apply_self α)
  rw [D.root_eq, D.root_eq] at he
  exact he

private theorem pairing_opposite (D : Datum T) (c : Cocharacter T.group) (α : Root T) :
    pairing T.group (D.rootDatum.reflectionPerm α α).val c = -pairing T.group α.val c := by
  rw [← evaluate_root D c (D.rootDatum.reflectionPerm α α),
    D.rootDatum.root_reflectionPerm, D.rootDatum.reflection_apply_self, map_neg, evaluate_root]

private theorem wall_of_simple (D : Datum T) {B : ClosedSubgroup G.val}
    {c : Cocharacter T.group} (hc : IsRegular T c) (hB : positiveRoots T c = subgroupRoots T B)
    {α : Root T} (wall : Cocharacter T.group)
    (hwall : SimpleRoots.realFunctional (SimpleRoots.evaluate D wall) ∈
      SimpleRoots.wallInterior D.rootDatum (SimpleRoots.evaluate D c) α)
    (hα : α ∈ subgroupRoots T B) : IsWallCocharacter T B α wall := by
  obtain ⟨hz, hp⟩ := hwall
  have hz' : pairing T.group α.val wall = 0 := by
    have e : (pairing T.group α.val wall : ℝ) = 0 := by
      change ((SimpleRoots.evaluate D wall (D.rootDatum.root α)) : ℝ) = 0 at hz
      rwa [evaluate_root] at hz
    exact_mod_cast e
  have he (β : Root T) (hβ : β ∈ subgroupRoots T B) (hne : β ≠ α) :
      0 < pairing T.group β.val wall := by
    have hβ' : β ∈ SimpleRoots.positive D.rootDatum (SimpleRoots.evaluate D c) := by
      change 0 < SimpleRoots.evaluate D c (D.rootDatum.root β)
      rw [evaluate_root]
      exact show β ∈ positiveRoots T c from hB.symm ▸ hβ
    have e : (0 : ℝ) < (pairing T.group β.val wall : ℝ) := by
      have hh := hp β hβ' hne
      change (0 : ℝ) < ((SimpleRoots.evaluate D wall (D.rootDatum.root β)) : ℝ) at hh
      rwa [evaluate_root] at hh
    exact_mod_cast e
  have hpos (β : Root T) : β ∈ subgroupRoots T B ↔ 0 < pairing T.group β.val c := by
    rw [← hB]
    rfl
  have hn (β : Root T) (hb : β ∉ subgroupRoots T B) :
      0 < pairing T.group (D.rootDatum.reflectionPerm β β).val c := by
    rw [pairing_opposite]
    exact neg_pos.mpr (lt_of_le_of_ne
      (le_of_not_gt (fun h => hb ((hpos β).mpr h))) (hc β))
  have hop (β : Root T) : D.rootDatum.reflectionPerm β β = α ↔ β.val = α.val⁻¹ := by
    constructor
    · intro h
      rw [← h, opposite_root, inv_inv]
    · intro h
      exact Subtype.ext (by rw [opposite_root, h, inv_inv])
  constructor
  · intro β
    constructor
    · intro h
      by_cases hb : β ∈ subgroupRoots T B
      · exact Or.inl (by_contra fun hne => (he β hb hne).ne' h)
      · refine Or.inr ((hop β).mp (by_contra fun hne => ?_))
        have hh := he _ ((hpos _).mpr (hn β hb)) hne
        rw [pairing_opposite, h, neg_zero] at hh
        exact (lt_irrefl _ hh)
    · rintro (rfl | hh)
      · exact hz'
      · have e := pairing_opposite D wall α
        rwa [opposite_root, ← hh, hz', neg_zero] at e
  · ext β
    change 0 < pairing T.group β.val wall ↔ β ∈ subgroupRoots T B ∧ β ≠ α
    refine ⟨fun h => ⟨?_, fun h' => h.ne' (h' ▸ hz')⟩, fun h => he β h.1 h.2⟩
    by_contra hb
    by_cases h' : D.rootDatum.reflectionPerm β β = α
    · have e := pairing_opposite D wall β
      rw [h', hz'] at e
      omega
    · have e := he _ ((hpos _).mpr (hn β hb)) h'
      rw [pairing_opposite] at e
      omega

private theorem increasing_after_reflection (D : Datum T) {B : ClosedSubgroup G.val}
    {c : Cocharacter T.group} (hc : IsRegular T c) (hB : positiveRoots T c = subgroupRoots T B)
    (α : Root T) (v : D.rootDatum.weylGroup)
    (h : D.rootDatum.weylGroupToPerm v α ∉ subgroupRoots T B) :
    D.rootDatum.weylGroupToPerm (v * RootPairing.weylGroup.ofIdx D.rootDatum α) α ∈
      subgroupRoots T B := by
  let s := RootPairing.weylGroup.ofIdx D.rootDatum α
  have he : D.rootDatum.root (D.rootDatum.weylGroupToPerm (v * s) α) =
      -D.rootDatum.root (D.rootDatum.weylGroupToPerm v α) := by
    rw [map_mul, Equiv.Perm.mul_apply]
    rw [← D.rootDatum.weylGroup_apply_root v, ← D.rootDatum.weylGroup_apply_root v]
    change v.val.weightEquiv (D.rootDatum.root (D.rootDatum.reflectionPerm α α)) =
      -v.val.weightEquiv (D.rootDatum.root α)
    rw [D.rootDatum.root_reflectionPerm, D.rootDatum.reflection_apply_self]
    exact v.val.weightEquiv.toLinearMap.map_neg _
  rw [← hB] at h ⊢
  change ¬ 0 < pairing T.group (D.rootDatum.weylGroupToPerm v α).val c at h
  change 0 < pairing T.group (D.rootDatum.weylGroupToPerm (v * s) α).val c
  rw [← evaluate_root, he, map_neg, evaluate_root]
  exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt h) (hc _))

end Wall

section Factors

open LinearAlgebraicGroups.CocharacterDynamics (multiplyFactors)
open Specs.OrderedRootProducts (product rootProduct)

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

private theorem mem_sections_of_subgroupOf {F : GroupScheme k} {A B : ClosedSubgroup F}
    (h : IsSubgroupOf A B) {Y : SchemeOver k} :
    SubgroupSections A Y ≤ SubgroupSections B Y := by
  obtain ⟨f, hf⟩ := h
  rintro _ ⟨x, rfl⟩
  change Y ⟶ A.group.X at x
  refine ⟨x ≫ f.hom.hom, ?_⟩
  change (x ≫ f.hom.hom) ≫ B.inclusion.hom.hom = x ≫ A.inclusion.hom.hom
  rw [Category.assoc]
  exact congrArg (fun h : A.group ⟶ F => x ≫ h.hom.hom) hf

private theorem section_mem_of_same {F : GroupScheme k} {A B : ClosedSubgroup F} (h : SameSubgroup A B)
    {Y : SchemeOver k} {p : Y ⟶ F.X} : p ∈ SubgroupSections A Y ↔ p ∈ SubgroupSections B Y :=
  ⟨fun hp => mem_sections_of_subgroupOf (Y := Y) h.1 hp,
    fun hp => mem_sections_of_subgroupOf (Y := Y) h.2 hp⟩

private theorem inclusion_mem_sections {F : GroupScheme k} (B : ClosedSubgroup F) :
    B.inclusion.hom.hom ∈ SubgroupSections B B.group.X := by
  refine ⟨𝟙 _, ?_⟩
  change 𝟙 _ ≫ B.inclusion.hom.hom = B.inclusion.hom.hom
  exact Category.id_comp _

private theorem factors_of_iso {F H J : GroupScheme k} (f : F ⟶ J) (g : H ⟶ J)
    [IsIso (multiplyFactors f g)] {Y : SchemeOver k} (p : Y ⟶ J.X) :
    ∃ (x : Y ⟶ F.X) (y : Y ⟶ H.X), (x ≫ f.hom.hom) * (y ≫ g.hom.hom) = p := by
  let l := p ≫ inv (multiplyFactors f g)
  refine ⟨l ≫ fst _ _, l ≫ snd _ _, ?_⟩
  have he : l ≫ multiplyFactors f g = p := by simp [l]
  simpa only [multiplyFactors, MonObj.comp_mul, Category.assoc] using he

private theorem mem_limit_parabolic {F : GroupScheme k} {cochar : Cocharacter F} (P : LimitDecomposition cochar)
    {Y : SchemeOver k} {p : Y ⟶ F.X} :
    p ∈ SubgroupSections P.parabolic Y ↔
      ∃ (x : Y ⟶ P.centralizer.group.X) (y : Y ⟶ P.contracting.group.X),
        (x ≫ P.centralizer.inclusion.hom.hom) * (y ≫ P.contracting.inclusion.hom.hom) = p := by
  letI := P.product_iso
  have apply_mul (x : Y ⟶ P.centralizer.group.X) (y : Y ⟶ P.contracting.group.X) :
      ((x ≫ P.sectionMap.hom.hom) * (y ≫ P.contractingToParabolic.hom.hom)) ≫
        P.parabolic.inclusion.hom.hom =
      (x ≫ P.centralizer.inclusion.hom.hom) * (y ≫ P.contracting.inclusion.hom.hom) := by
    rw [MonObj.mul_comp, Category.assoc, Category.assoc]
    exact congrArg₂ (· * ·)
      (congrArg (fun f : P.centralizer.group ⟶ F => x ≫ f.hom.hom) P.section_in_G)
      (congrArg (fun f : P.contracting.group ⟶ F => y ≫ f.hom.hom) P.contracting_in_G)
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨x, y, h⟩ := factors_of_iso P.sectionMap P.contractingToParabolic q
    exact ⟨x, y, (apply_mul x y).symm.trans (congrArg (· ≫ P.parabolic.inclusion.hom.hom) h)⟩
  · rintro ⟨x, y, rfl⟩
    exact ⟨_, apply_mul x y⟩

private theorem has_enumeration {I : Type u} [Finite I] (S : Set I) :
    ∃ l : List I, Enumerates l S := by
  classical
  let F := S.toFinite.toFinset
  exact ⟨F.toList, Finset.nodup_toList _, by simp [F]⟩

private theorem factors_of_root_products
    {T : ClosedSubgroup G.val} (U : RootSubgroupFamily T) (α : Root T) (l : List (Root T))
    {F H : SchemeOver k} (f : F ⟶ G.val.X) (g : H ⟶ G.val.X)
    (hF : Parametrizes U (α :: l) f) (hH : Parametrizes U l g)
    {Y : SchemeOver k} {p : Y ⟶ G.val.X} :
    (∃ q : Y ⟶ F, q ≫ f = p) ↔
      ∃ (x : Y ⟶ (U α).val.group.X) (y : Y ⟶ H),
        (x ≫ (U α).val.inclusion.hom.hom) * (y ≫ g) = p := by
  obtain ⟨e, he⟩ := hF
  obtain ⟨d, hd⟩ := hH
  constructor
  · rintro ⟨q, rfl⟩
    let h := q ≫ e.inv
    refine ⟨h ≫ fst _ _, h ≫ snd _ _ ≫ d.hom, ?_⟩
    have hh : h ≫ rootProduct U (α :: l) = q ≫ f := by rw [← he]; simp [h]
    rw [← hh]
    change _ = h ≫ (((fst _ _) ≫ _) * ((snd _ _) ≫ rootProduct U l))
    rw [MonObj.comp_mul, ← hd]
    simp only [Category.assoc]
  · rintro ⟨x, y, rfl⟩
    let h := lift x (y ≫ d.inv)
    refine ⟨h ≫ e.hom, ?_⟩
    rw [Category.assoc, he]
    change h ≫ (((fst _ _) ≫ _) * ((snd _ _) ≫ rootProduct U l)) = _
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, lift_fst, lift_snd, ← hd]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem borel_sections
    {T B : ClosedSubgroup G.val} (c wall : Cocharacter T.group)
    (E : LimitDecomposition (c ≫ T.inclusion)) (P : LimitDecomposition (wall ≫ T.inclusion))
    (hB : SameSubgroup B E.parabolic) (hT : SameSubgroup E.centralizer T)
    (U : RootSubgroupFamily T) (α : Root T) (l : List (Root T))
    (hE : Parametrizes U (α :: l) E.contracting.inclusion.hom.hom)
    (hP : Parametrizes U l P.contracting.inclusion.hom.hom)
    {Y : SchemeOver k} {p : Y ⟶ G.val.X} :
    p ∈ SubgroupSections B Y ↔
      ∃ (x : Y ⟶ T.group.X) (y : Y ⟶ (U α).val.group.X)
        (z : Y ⟶ P.contracting.group.X),
        (x ≫ T.inclusion.hom.hom) * (y ≫ (U α).val.inclusion.hom.hom) *
          (z ≫ P.contracting.inclusion.hom.hom) = p := by
  obtain ⟨f, hf⟩ := hT.1
  obtain ⟨g, hg⟩ := hT.2
  have h₁ : f.hom.hom ≫ T.inclusion.hom.hom = E.centralizer.inclusion.hom.hom := congrArg (fun h : E.centralizer.group ⟶ G.val => h.hom.hom) hf
  have h₂ : g.hom.hom ≫ E.centralizer.inclusion.hom.hom = T.inclusion.hom.hom := congrArg (fun h : T.group ⟶ G.val => h.hom.hom) hg
  rw [section_mem_of_same hB, mem_limit_parabolic E]
  constructor
  · rintro ⟨a, b, rfl⟩
    obtain ⟨x, y, hxy⟩ := (factors_of_root_products U α l _ _ hE hP).mp
      ⟨b, rfl⟩
    exact ⟨a ≫ f.hom.hom, x, y, by rw [Category.assoc, h₁, mul_assoc, hxy]⟩
  · rintro ⟨a, x, y, rfl⟩
    obtain ⟨b, hb⟩ := (factors_of_root_products U α l _ _ hE hP).mpr
      ⟨x, y, rfl⟩
    exact ⟨a ≫ g.hom.hom, b, by rw [Category.assoc, h₂, hb, mul_assoc]⟩

end Factors

section Quotient

variable {k : Type u} [Field k] {P H : GroupScheme k}
  {B : ClosedSubgroup P} {A : ClosedSubgroup H}

private theorem split_preimage_quotient
    (q : P ⟶ H) (i : H ⟶ P) (hi : i ≫ q = 𝟙 H)
    (r : B.group ⟶ A.group)
    (hr : IsPullback B.inclusion.hom.hom r.hom.hom q.hom.hom A.inclusion.hom.hom)
    (t : A.group ⟶ B.group) (ht : A.inclusion ≫ i = t ≫ B.inclusion)
    (Q : Presentation B) (QH : Presentation A) :
    ∃ e : Q.scheme ≅ QH.scheme, Q.projection ≫ e.hom = q.hom.hom ≫ QH.projection := by
  let q₀ := q.hom.hom
  let i₀ := i.hom.hom
  have h₀ : i₀ ≫ q₀ = 𝟙 H.X := congrArg (fun f : H ⟶ H => f.hom.hom) hi
  have hr' : B.inclusion ≫ q = r ≫ A.inclusion := Grp.hom_ext _ _ hr.w
  let f := rightCosetMap q r hr'
  let g := rightCosetMap i t ht
  let e : rightCosetPresheaf B ≅ rightCosetPresheaf A :=
    ⟨f, g, by
      ext Y ⟨x⟩
      induction x using QuotientGroup.induction_on with
      | H x =>
        change ULift.up (QuotientGroup.mk (s := SubgroupSections B Y.unop)
          ((x ≫ q₀) ≫ i₀)) = ULift.up (QuotientGroup.mk x)
        apply congrArg ULift.up
        apply QuotientGroup.eq.mpr
        let d := ((x ≫ q₀) ≫ i₀)⁻¹ * x
        have hd : d ≫ q₀ = (1 : Y.unop ⟶ A.group.X) ≫ A.inclusion.hom.hom := by
          dsimp only [d]
          rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc _ i₀, h₀,
            Category.comp_id, inv_mul_cancel, MonObj.one_comp]
        exact ⟨hr.lift d 1 hd, hr.lift_fst _ _ _⟩,
      by
        ext Y ⟨x⟩
        induction x using QuotientGroup.induction_on with
        | H x =>
          change ULift.up (QuotientGroup.mk (s := SubgroupSections A Y.unop)
            ((x ≫ i₀) ≫ q₀)) = ULift.up (QuotientGroup.mk x)
          rw [Category.assoc, h₀, Category.comp_id]⟩
  let F := (fppfOver k).fullyFaithfulUliftYoneda
  let e' := (presheafToSheaf (fppfOver k) _).mapIso e
  let e'' := Q.quotientIso.symm ≪≫ e' ≪≫ QH.quotientIso
  refine ⟨F.preimageIso e'', ?_⟩
  apply F.map_injective
  rw [Functor.map_comp, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, ← Q.quotientProjection,
    Functor.map_comp, ← QH.quotientProjection]
  have hmap : rightQuotientProjection B ≫ e'.hom =
      (fppfOver k).uliftYoneda.map q₀ ≫ rightQuotientProjection A := by
    ext Y ⟨x⟩
    exact rightQuotientMapOnLifts q r hr' x
  simp only [e'', Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, hmap, Category.assoc]

end Quotient

section Representatives

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
  {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X] {D : Datum T}

private theorem normalizer_ratio_mem_torus (I : Identification D) {Y : SchemeOver k}
    {p q : Y ⟶ I.normalizer.group.X} (h : p ≫ I.quotient.hom.hom = q ≫ I.quotient.hom.hom) :
    (p ≫ I.normalizer.inclusion.hom.hom)⁻¹ * (q ≫ I.normalizer.inclusion.hom.hom) ∈
      SubgroupSections T Y := by
  let d := p⁻¹ * q
  have hd : d ≫ I.quotient.hom.hom = toUnit Y ≫ η[I.scheme.val.X] := by
    dsimp only [d]
    rw [MonObj.mul_comp, GrpObj.inv_comp, h, inv_mul_cancel]
    rfl
  let t := I.isQuotient.1.lift d (toUnit Y) hd
  have ht : t ≫ I.torusInclusion.hom.hom = d := I.isQuotient.1.lift_fst _ _ _
  refine ⟨t, ?_⟩
  change t ≫ T.inclusion.hom.hom = _
  rw [← I.inclusion_eq]
  change t ≫ I.torusInclusion.hom.hom ≫ I.normalizer.inclusion.hom.hom = _
  rw [← Category.assoc, ht]
  simp only [d, MonObj.mul_comp, GrpObj.inv_comp]

private theorem representative_product (I : Identification D)
    (n : D.rootDatum.weylGroup → (𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X))
    (hn : ∀ w, IsRepresentative I w (n w)) (Y : SchemeOver k) (v s : D.rootDatum.weylGroup) :
    let g := fun w ↦ toUnit Y ≫ n w ≫ I.normalizer.inclusion.hom.hom
    ∃ t ∈ SubgroupSections T Y, g v * g s = g (v * s) * t := by
  let p := fun w ↦ toUnit Y ≫ n w
  let a := I.normalizer.inclusion.hom.hom
  let g := fun w ↦ p w ≫ a
  have hp (w) : p w ≫ I.quotient.hom.hom =
      toUnit Y ≫ I.image.constantGroup.sectionPoint (I.labelEquiv w) := by
    dsimp only [p]
    rw [Category.assoc, hn w]
  have hq : p (v * s) ≫ I.quotient.hom.hom = (p v * p s) ≫ I.quotient.hom.hom := by
    rw [MonObj.mul_comp, hp, hp, hp, map_mul, map_mul, MonObj.comp_mul]
  have ht := normalizer_ratio_mem_torus I hq
  change (g (v * s))⁻¹ * ((p v * p s) ≫ a) ∈ SubgroupSections T Y at ht
  rw [MonObj.mul_comp] at ht
  change (g (v * s))⁻¹ * (g v * g s) ∈ SubgroupSections T Y at ht
  change ∃ t ∈ SubgroupSections T Y, g v * g s = g (v * s) * t
  exact ⟨_, ht, (mul_inv_cancel_left _ _).symm⟩

end Representatives

section RepresentativeLabel

open Specs.RootGroups (AdditiveLine CorootReflection)
open Specs.BruhatOrbitParametrization (conjugatePoint)

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
  {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X] {D : Datum T}

private theorem some_representative_label (I : Identification D)
    (n : 𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X) :
    ∃ w, IsRepresentative I w n := by
  let F := I.image.constantGroup
  let w := F.families _ (n ≫ I.quotient.hom.hom) (IsLocalRing.closedPoint k)
  refine ⟨I.labelEquiv.symm w, ?_⟩
  change n ≫ I.quotient.hom.hom = F.sectionPoint (I.labelEquiv (I.labelEquiv.symm w))
  have he : toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ := Subsingleton.elim _ _
  rw [MulEquiv.apply_symm_apply, ← Category.id_comp (F.sectionPoint w), ← he]
  apply (F.families _).injective
  rw [F.constant]
  apply LocallyConstant.ext
  intro x
  exact congrArg (fun x => F.families _ (n ≫ I.quotient.hom.hom) x)
    (Subsingleton.elim (α := PrimeSpectrum k) x (IsLocalRing.closedPoint k))

private theorem representative_conjugates_torus (I : Identification D)
    {w : D.rootDatum.weylGroup} {n : 𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X}
    (hn : IsRepresentative I w n) :
    ((I.image.conjugation (I.labelEquiv w)).hom ≫ T.inclusion).hom.hom =
      conjugatePoint (n ≫ I.normalizer.inclusion.hom.hom) T.inclusion.hom.hom := by
  have he : toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ := Subsingleton.elim _ _
  have hn' : n ≫ I.quotient.hom.hom = I.image.constantGroup.sectionPoint (I.labelEquiv w) := hn
  have h := I.image.conjugates _ n (I.labelEquiv w) (by simpa only [he, Category.id_comp] using hn')
  have h' := congrArg (fun f => lift (𝟙 T.group.X) (toUnit T.group.X) ≫ f) h
  simpa only [conjugateFamily, conjugatePoint, MonObj.comp_mul, GrpObj.comp_inv,
    Category.assoc, lift_snd_assoc, lift_fst_assoc, Category.id_comp] using h'.symm

private theorem coroot_reflection_is_representative (I : Identification D) (α : Root T)
    {A : AdditiveLine k} {xpos xneg : A.group ⟶ G.val}
    (r : CorootReflection T α.val xpos xneg)
    (hr : r.coroot = Additive.toMul (D.rootDatum.coroot α)) :
    ∃ n, IsRepresentative I (RootPairing.weylGroup.ofIdx D.rootDatum α) n ∧
      n ≫ I.normalizer.inclusion.hom.hom = r.representative := by
  obtain ⟨n, hn⟩ := (I.representsNormalizer _ _).mp r.normalizes
  obtain ⟨w, hw⟩ := some_representative_label I n
  have hcomp := representative_conjugates_torus I hw
  rw [hn] at hcomp
  have hinc : Mono T.inclusion.hom.hom := by
    letI := T.isClosedImmersion
    exact Over.mono_of_mono_left _
  have hsame : I.image.conjugation (I.labelEquiv w) = r.conjugation := by
    apply Iso.ext
    apply Grp.hom_ext
    apply (cancel_mono T.inclusion.hom.hom).mp
    exact hcomp.trans r.conjugates.symm
  let s := RootPairing.weylGroup.ofIdx D.rootDatum α
  have heq : I.labelEquiv w = I.labelEquiv s := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro χ
    rw [I.image.characterAction, hsame, r.reflection]
    apply Additive.ofMul.injective
    rw [← I.characterAction]
    change Additive.ofMul (χ * α.val ^ (-pairing T.group χ r.coroot)) =
      (RootPairing.Equiv.reflection D.rootDatum α).weightEquiv (Additive.ofMul χ)
    rw [RootPairing.Equiv.reflection_weightEquiv, RootPairing.reflection_apply, D.root_eq]
    have he : D.rootDatum.coroot' α (Additive.ofMul χ) = pairing T.group χ r.coroot := by
      rw [hr, ← D.pairing_eq]
      rfl
    rw [he, sub_eq_add_neg, ← neg_zsmul]
    rfl
  have hws : w = s := I.labelEquiv.injective heq
  refine ⟨n, ?_, hn⟩
  change IsRepresentative I s n
  rw [← hws]
  exact hw

end RepresentativeLabel

section RankOneChart

variable {k : Type u} [Field k] {H : GroupScheme k}

private theorem closed_factor_of_range {X Y Z : SchemeOver k} [IsReduced Y.left]
    (p : Y ⟶ X) (f : Z ⟶ X) (hf : IsClosedImmersion f.left)
    (h : Set.range p.left ⊆ Set.range f.left) : ∃ g : Y ⟶ Z, g ≫ f = p := by
  let π := pullback.fst p.left f.left
  let q := pullback.snd p.left f.left
  letI := hf
  letI : IsClosedImmersion π := MorphismProperty.pullback_fst _ _ inferInstance
  letI : Surjective π := ⟨fun x => by
    change x ∈ Set.range π
    rw [Scheme.Pullback.range_fst]
    exact h ⟨x, rfl⟩⟩
  letI := isIso_of_isClosedImmersion_of_surjective π
  let g := inv π ≫ q
  have hg : g ≫ f.left = p.left := by
    rw [show g = inv π ≫ q from rfl, Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  have hbase : g ≫ Z.hom = Y.hom := by
    rw [← Over.w f, ← Category.assoc, hg, Over.w p]
  exact ⟨Over.homMk g hbase, by apply Over.OverMorphism.ext; exact hg⟩

private theorem factor_through_rank_one_chart {K : Type u} [Field K] [Algebra k K]
    {X Z : SchemeOver k} (p : Over.mk (fieldSpecMap k K) ⟶ X) (f : Z ⟶ X)
    (n : 𝟙_ (SchemeOver k) ⟶ X) (hn : IsClosedImmersion n.left)
    (hf : IsOpenImmersion f.left) (h : Set.range f.left = (Set.range n.left)ᶜ) :
    (∃ x : Over.mk (fieldSpecMap k K) ⟶ Z, x ≫ f = p) ∨
      p = toUnit _ ≫ n := by
  let Y := Over.mk (fieldSpecMap k K)
  have overLift {S : SchemeOver k} {j : S ⟶ X} (g : Y.left ⟶ S.left)
      (hg : g ≫ j.left = p.left) : ∃ x : Y ⟶ S, x ≫ j = p := by
    have hbase : g ≫ S.hom = Y.hom := by
      rw [← Over.w j, ← Category.assoc, hg, Over.w p]
    refine ⟨Over.homMk g hbase, ?_⟩
    apply Over.OverMorphism.ext
    exact hg
  let a : Y.left := IsLocalRing.closedPoint K
  letI : Subsingleton Y.left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have same (x : Y.left) : x = a := Subsingleton.elim _ _
  by_cases he : p.left a ∈ Set.range n.left
  · right
    letI : IsReduced Y.left := inferInstanceAs (IsReduced (Spec (CommRingCat.of K)))
    obtain ⟨x, hx⟩ := closed_factor_of_range p n hn (by
      rintro _ ⟨z, rfl⟩
      rw [same z]
      exact he)
    rw [show x = toUnit Y from Subsingleton.elim _ _] at hx
    exact hx.symm
  · left
    letI := hf
    have hr : Set.range p.left ⊆ Set.range f.left := by
      rintro _ ⟨x, rfl⟩
      rw [same x, h]
      exact he
    exact overLift (IsOpenImmersion.lift f.left p.left hr) (IsOpenImmersion.lift_fac _ _ _)

end RankOneChart

section RankOneSections

variable {k : Type u} [Field k] {H : GroupScheme k}

private theorem projection_eq_sections {B : ClosedSubgroup H} (Q : Presentation B)
    {Y : SchemeOver k} {x y : Y ⟶ H.X} :
    x ≫ Q.projection = y ≫ Q.projection ↔ x⁻¹ * y ∈ SubgroupSections B Y := by
  have projection (g : Y ⟶ H.X) :
      Q.quotientIso.hom.hom.app (op Y) (projectSection B g) = ⟨g ≫ Q.projection⟩ := by
    exact congrArg (fun f => f.hom.app (op Y) (ULift.up g)) Q.quotientProjection
  constructor
  · intro h
    apply (rightQuotientProjectionEquality B x y).mp
    have he : Function.Injective (Q.quotientIso.hom.hom.app (op Y)) := by
      intro p q hpq
      have leftInv (a : (rightQuotientSheaf B).obj.obj (op Y)) :
          Q.quotientIso.inv.hom.app (op Y) (Q.quotientIso.hom.hom.app (op Y) a) = a :=
        congrArg (fun f => f.hom.app (op Y) a) Q.quotientIso.hom_inv_id
      exact (leftInv p).symm.trans
        ((congrArg (Q.quotientIso.inv.hom.app (op Y)) hpq).trans (leftInv q))
    apply he
    rw [projection, projection, h]
  · intro h
    have he := (rightQuotientProjectionEquality B x y).mpr h
    apply ULift.up.inj
    rw [← projection, ← projection, he]

private theorem rank_one_sections {K : Type u} [Field K] [Algebra k K]
    {B V : ClosedSubgroup H} (Q : Presentation B)
    (m n : 𝟙_ (SchemeOver k) ⟶ H.X)
    (hclosed : IsClosedImmersion (m ≫ Q.projection).left)
    (hopen : IsOpenImmersion (V.inclusion.hom.hom ≫ Q.projection).left)
    (hrange : Set.range (V.inclusion.hom.hom ≫ Q.projection).left =
      (Set.range (m ≫ Q.projection).left)ᶜ)
    (hm : let Y := Over.mk (fieldSpecMap k K)
      ((toUnit Y ≫ n) * (toUnit Y ≫ m)) ≫ Q.projection =
        (1 : Y ⟶ H.X) ≫ Q.projection)
    (p : Over.mk (fieldSpecMap k K) ⟶ H.X) :
    p ∈ SubgroupSections B _ ∨
      ∃ (v : Over.mk (fieldSpecMap k K) ⟶ V.group.X) (b : Over.mk (fieldSpecMap k K) ⟶ B.group.X),
        (toUnit _ ≫ n) * (v ≫ V.inclusion.hom.hom) * (b ≫ B.inclusion.hom.hom) = p := by
  let Y := Over.mk (fieldSpecMap k K)
  let z : Y ⟶ H.X := (toUnit Y ≫ n)⁻¹ * p
  rcases factor_through_rank_one_chart (z ≫ Q.projection) _ _ hclosed hopen hrange with ⟨v, hv⟩ | hv
  · right
    have he : (v ≫ V.inclusion.hom.hom)⁻¹ * z ∈ SubgroupSections B Y :=
      (projection_eq_sections Q).mp (by rw [Category.assoc]; exact hv)
    obtain ⟨b, hb⟩ := he
    change b ≫ B.inclusion.hom.hom = _ at hb
    refine ⟨v, b, ?_⟩
    rw [hb]
    change (toUnit Y ≫ n) * (v ≫ V.inclusion.hom.hom) *
      ((v ≫ V.inclusion.hom.hom)⁻¹ * ((toUnit Y ≫ n)⁻¹ * p)) = p
    group
  · left
    have he : (toUnit Y ≫ m)⁻¹ * z ∈ SubgroupSections B Y :=
      (projection_eq_sections Q).mp (by rw [Category.assoc]; exact hv.symm)
    have he' : ((toUnit Y ≫ n) * (toUnit Y ≫ m)) ∈ SubgroupSections B Y := by
      have h := (projection_eq_sections Q).mp hm.symm
      simpa only [inv_one, one_mul] using h
    have hp := (SubgroupSections B Y).mul_mem he' he
    convert hp using 1
    dsimp only [z]
    group

end RankOneSections

section WallLevi

open Specs.DiagonalizableGroups (IntegerCharacters diagonalClosedInclusion groupAlgebra groupAlgebraMap)
open Specs.CharacterDescent (StandardLattice)
open Specs.CharacterPairing (powerMorphism)
open CocharacterDynamics (geometricallyConnectedLimitSubgroups limitSubgroupsSmooth)
open private splitPresentation latticeCoordinates from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private splitGroupHomEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private kernel_subtorus_in_splitPresentation latticeCharacter latticeCharacter_comp
  latticeMap_comp saturatedProjection saturatedProjection_ker_le subgroupIso_of_same
  integerCharacters_hasUniqueRoots
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private factor_group_through_subgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private connected_of_geometricallyConnected lieImage_mono limitLie_weightSpans
  subgroupOf_of_lieImage from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

private theorem cocharacter_factors_through_kernel_torus {T : GroupScheme k}
    (hT : IsSplitTorus T) (χ : Character T) {S : ClosedSubgroup T}
    (hS : Specs.RankOneFlag.IsKernelSubtorus χ S) (c : Cocharacter T)
    (hc : pairing T χ c = 0) : ∃ d : Cocharacter S.group, d ≫ S.inclusion = c := by
  obtain ⟨r, ⟨i⟩⟩ := splitPresentation hT
  let M := StandardLattice.{u} r
  letI : Module.Finite ℤ (Additive M) := Module.Finite.equiv (latticeCoordinates r).symm
  letI : Group.FG M := GroupFG.iff_add_fg.mpr (Module.Finite.iff_addGroup_fg.mp inferInstance)
  obtain ⟨x, hx⟩ := (latticeCharacter (k := k) M).surjective (i.hom ≫ χ)
  obtain ⟨f, hf⟩ := (splitGroupHomEquiv (k := k) M IntegerCharacters).surjective (c ≫ i.inv)
  change specGroupMap (groupAlgebraMap k f) = c ≫ i.inv at hf
  have hf' : specGroupMap (groupAlgebraMap k f) ≫ i.hom = c := by
    rw [hf, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hc' := (RootData.CharacterPairing.characterPairingComposition T χ c).1 0 |>.mpr hc
  change c ≫ χ = powerMorphism 0 at hc'
  have hone : latticeCharacter (k := k) IntegerCharacters 1 = powerMorphism 0 := by
    rw [powerMorphism, zpow_zero]
    rfl
  have hfx : f x = 1 := (latticeCharacter (k := k) IntegerCharacters).injective (by
    rw [← latticeCharacter_comp, hx, ← Category.assoc, hf', hc', hone])
  let N := (saturatedProjection x).ker
  let m := QuotientGroup.mk' N
  letI : HasUniqueRoots IntegerCharacters.{u} := integerCharacters_hasUniqueRoots
  let g := QuotientGroup.lift N f (saturatedProjection_ker_le x f hfx)
  obtain ⟨S', hS', e, he⟩ := kernel_subtorus_in_splitPresentation i χ x hx
  obtain ⟨j, hj⟩ := hS.2.2 S' hS'.1 hS'.2.1
  refine ⟨specGroupMap (groupAlgebraMap k g) ≫ e.hom ≫ j, ?_⟩
  rw [Category.assoc, Category.assoc, hj, he, ← Category.assoc]
  change (specGroupMap (groupAlgebraMap k g) ≫ specGroupMap (groupAlgebraMap k m)) ≫ i.hom = c
  rw [latticeMap_comp, show g.comp m = f from MonoidHom.ext (fun _ => rfl), hf']

private theorem rank_one_le_wall {T : ClosedSubgroup G.val} {α : Character T.group}
    (hT : IsSplitTorus T.group) (c : Cocharacter T.group) (hc : pairing T.group α c = 0)
    (P : LimitDecomposition (c ≫ T.inclusion)) (H : Centralizer T α) :
    IsSubgroupOf H.subgroup P.centralizer := by
  obtain ⟨d, hd⟩ := cocharacter_factors_through_kernel_torus hT α H.kernelTorus_largest c hc
  have h : Centralizes (c ≫ T.inclusion) H.subgroup.inclusion.hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro Y p a
    have hh := (centralizes_iff _ _).mp
      ((H.centralizes _ _).mpr ⟨𝟙 H.subgroup.group.X, Category.id_comp _⟩)
      Y p (a ≫ d.hom.hom)
    change Commute (p ≫ H.subgroup.inclusion.hom.hom)
      ((a ≫ d.hom.hom) ≫ H.kernelTorus.inclusion.hom.hom ≫ T.inclusion.hom.hom) at hh
    rw [Category.assoc a, ← Category.assoc d.hom.hom, ← show
      c.hom.hom = d.hom.hom ≫ H.kernelTorus.inclusion.hom.hom from
        (congrArg (fun f : Cocharacter T.group => f.hom.hom) hd).symm] at hh
    exact hh
  obtain ⟨j, hj⟩ := (P.centralizer_points _ _).mp h
  exact factor_group_through_subgroup P.centralizer H.subgroup.inclusion j hj

private theorem wall_levi {T B : ClosedSubgroup G.val} {α : Root T}
    (hG : IsReductive G) (hT : IsSplitTorus T.group) (hTm : IsGeometricallyMaximal T)
    (c : Cocharacter T.group) (hc : IsWallCocharacter T B α c)
    (P : LimitDecomposition (c ≫ T.inclusion)) (H : Centralizer T α.val)
    (hH : IsReductive (closedSubgroupAlgebraicGroup H.subgroup))
    (hα : adjointWeightVectors T α.val ⊆ lieImage H.subgroup)
    (hneg : adjointWeightVectors T α.val⁻¹ ⊆ lieImage H.subgroup) :
    ∃ e : P.centralizer.group ≅ H.subgroup.group,
      e.hom ≫ H.subgroup.inclusion = P.centralizer.inclusion := by
  letI := hG.1
  letI : ConnectedSpace G.val.X.left := connected_of_geometricallyConnected hG.2.1
  have hsub := rank_one_le_wall hT c ((hc.1 α).mpr (Or.inl rfl)) P H
  have hTH : IsSubgroupOf T H.subgroup :=
    ⟨H.torusIso.hom ≫ H.torus.inclusion, H.torus_inclusion⟩
  let s := identityLieStructure G
  let sH : IdentityLieStructure H.subgroup.group :=
    identityLieStructure (closedSubgroupAlgebraicGroup H.subgroup)
  letI := G.property.1
  letI : IsAffine H.subgroup.group.X.left := (closedSubgroupAlgebraicGroup H.subgroup).property.1
  letI := s.lieRing
  letI := s.lieAlgebra
  letI : LieRing (Lie k H.subgroup.group) := sH.lieRing
  letI : LieAlgebra k (Lie k H.subgroup.group) := sH.lieAlgebra
  obtain ⟨d, hd⟩ := identityDifferentialLieHom k H.subgroup.group G.val H.subgroup.inclusion sH s
  have hrange : (LinearMap.range d.toLinearMap : Set (Lie k G.val)) = lieImage H.subgroup :=
    congrArg Set.range (funext hd)
  have hLie : lieImage P.centralizer ⊆ lieImage H.subgroup := by
    rw [(limitLie_weightSpans G T hT c P s).2, ← hrange]
    change (⨆ χ : {χ : Character T.group // pairing T.group χ c = 0},
      adjointWeightSpace T χ.val s) ≤ LinearMap.range d.toLinearMap
    apply iSup_le
    rintro ⟨χ, hχ⟩
    change adjointWeightSpace T χ s ≤ LinearMap.range d.toLinearMap
    by_cases h₁ : χ = 1
    · subst χ
      change (adjointWeightSpace T 1 s : Set (Lie k G.val)) ⊆ _
      rw [(RootData.CharacterPairing.zeroWeightSpace G hG T hT hTm s).2, hrange]
      exact lieImage_mono hTH
    by_cases hz : adjointWeightSpace T χ s = ⊥
    · rw [hz]; exact bot_le
    have hroot := (RootData.CharacterPairing.absoluteRootWeights T s χ).mpr ⟨h₁, hz⟩
    have hwall := (hc.1 ⟨χ, hroot⟩).mp hχ
    change (adjointWeightSpace T χ s : Set (Lie k G.val)) ⊆ _
    rw [RootData.CharacterPairing.adjointWeightSpaceVectors G T s χ, hrange]
    rcases hwall with h | h
    · have he : χ = α.val := congrArg (fun β : Root T => β.val) h
      rw [he]
      exact hα
    · change χ = α.val⁻¹ at h
      rw [h]
      exact hneg
  have hrev := subgroupOf_of_lieImage (A := G) hsub hH.1
    (connected_of_geometricallyConnected hH.2.1) (limitSubgroupsSmooth G _ P).2.2
    (connected_of_geometricallyConnected (geometricallyConnectedLimitSubgroups G _ P).2.2) hLie
  exact subgroupIso_of_same ⟨hrev, hsub⟩

end WallLevi

section BorelPullback

open private subgroupIso_of_same from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private factor_group_through_subgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private factor_closed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

private theorem rank_one_borel_sections {T : ClosedSubgroup G.val} {α : Root T}
    (H : Centralizer T α.val) {c : Cocharacter H.subgroup.group} (L : LimitDecomposition c)
    (hT : SameSubgroup L.centralizer H.torus) (U : ClosedSubgroup G.val)
    (hU : SameSubgroup (subgroupOfSubgroup H.subgroup L.contracting) U)
    {Y : SchemeOver k} {p : Y ⟶ G.val.X} :
    (∃ a : Y ⟶ L.parabolic.group.X,
      a ≫ L.parabolic.inclusion.hom.hom ≫ H.subgroup.inclusion.hom.hom = p) ↔
    ∃ (x : Y ⟶ T.group.X) (y : Y ⟶ U.group.X),
      (x ≫ T.inclusion.hom.hom) * (y ≫ U.inclusion.hom.hom) = p := by
  obtain ⟨e, he⟩ := subgroupIso_of_same hT
  obtain ⟨d, hd⟩ := subgroupIso_of_same hU
  change d.hom ≫ U.inclusion = L.contracting.inclusion ≫ H.subgroup.inclusion at hd
  let f := e ≪≫ H.torusIso.symm
  have hf : f.hom ≫ T.inclusion = L.centralizer.inclusion ≫ H.subgroup.inclusion := by
    rw [← H.torus_inclusion]
    simp only [f, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc, ← he]
  have mapT (x : Y ⟶ L.centralizer.group.X) :
      (x ≫ f.hom.hom.hom) ≫ T.inclusion.hom.hom =
        (x ≫ L.centralizer.inclusion.hom.hom) ≫ H.subgroup.inclusion.hom.hom := by
    have hw := congrArg (fun j : L.centralizer.group ⟶ G.val => x ≫ j.hom.hom) hf
    change x ≫ f.hom.hom.hom ≫ T.inclusion.hom.hom =
      x ≫ L.centralizer.inclusion.hom.hom ≫ H.subgroup.inclusion.hom.hom at hw
    simpa only [Category.assoc] using hw
  have mapU (y : Y ⟶ L.contracting.group.X) :
      (y ≫ d.hom.hom.hom) ≫ U.inclusion.hom.hom =
        (y ≫ L.contracting.inclusion.hom.hom) ≫ H.subgroup.inclusion.hom.hom := by
    have hw := congrArg (fun j : L.contracting.group ⟶ G.val => y ≫ j.hom.hom) hd
    change y ≫ d.hom.hom.hom ≫ U.inclusion.hom.hom =
      y ≫ L.contracting.inclusion.hom.hom ≫ H.subgroup.inclusion.hom.hom at hw
    simpa only [Category.assoc] using hw
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨x, y, h⟩ := (mem_limit_parabolic (F := H.subgroup.group) L).mp
      ⟨a, rfl⟩
    refine ⟨x ≫ f.hom.hom.hom, y ≫ d.hom.hom.hom, ?_⟩
    change (x ≫ L.centralizer.inclusion.hom.hom) * (y ≫ L.contracting.inclusion.hom.hom) =
      a ≫ L.parabolic.inclusion.hom.hom at h
    rw [mapT, mapU, ← MonObj.mul_comp, h, Category.assoc]
  · rintro ⟨x, y, rfl⟩
    let x' := x ≫ f.inv.hom.hom
    let y' := y ≫ d.inv.hom.hom
    obtain ⟨a, ha⟩ := (mem_limit_parabolic (F := H.subgroup.group) L).mpr
      ⟨x', y', rfl⟩
    have h₁ : x' ≫ f.hom.hom.hom = x := by
      change x ≫ f.inv.hom.hom ≫ f.hom.hom.hom = x
      have hi : f.inv.hom.hom ≫ f.hom.hom.hom = 𝟙 _ :=
        (Grp.forget _).congr_map f.inv_hom_id
      rw [hi, Category.comp_id]
    have h₂ : y' ≫ d.hom.hom.hom = y := by
      change y ≫ d.inv.hom.hom ≫ d.hom.hom.hom = y
      have hi : d.inv.hom.hom ≫ d.hom.hom.hom = 𝟙 _ :=
        (Grp.forget _).congr_map d.inv_hom_id
      rw [hi, Category.comp_id]
    refine ⟨a, ?_⟩
    change a ≫ L.parabolic.inclusion.hom.hom = _ at ha
    rw [← Category.assoc, ha, MonObj.mul_comp, ← mapT, ← mapU, h₁, h₂]

private theorem limit_product {c : Cocharacter G.val} (P : LimitDecomposition c)
    {H : ClosedSubgroup G.val} (e : P.centralizer.group ≅ H.group)
    (he : e.hom ≫ H.inclusion = P.centralizer.inclusion)
    {Y : SchemeOver k} (h : Y ⟶ H.group.X) (u' : Y ⟶ P.contracting.group.X) :
    let x := (h ≫ (e.inv ≫ P.sectionMap).hom.hom) * (u' ≫ P.contractingToParabolic.hom.hom)
    x ≫ P.parabolic.inclusion.hom.hom =
      (h ≫ H.inclusion.hom.hom) * (u' ≫ P.contracting.inclusion.hom.hom) ∧
    x ≫ (P.limit ≫ e.hom).hom.hom = h := by
  have hs : (e.inv ≫ P.sectionMap) ≫ P.parabolic.inclusion = H.inclusion := by
    rw [Category.assoc, P.section_in_G, ← he, e.inv_hom_id_assoc]
  have hq : (e.inv ≫ P.sectionMap) ≫ (P.limit ≫ e.hom) = 𝟙 H.group := by
    rw [Category.assoc, ← Category.assoc P.sectionMap, P.section_limit, Category.id_comp,
      e.inv_hom_id]
  dsimp only
  constructor
  · rw [MonObj.mul_comp, Category.assoc, Category.assoc]
    exact congrArg₂ (· * ·)
      (congrArg (fun f : H.group ⟶ G.val => h ≫ f.hom.hom) hs)
      (congrArg (fun f : P.contracting.group ⟶ G.val => u' ≫ f.hom.hom) P.contracting_in_G)
  · have hq₀ := congrArg (fun f : H.group ⟶ H.group => f.hom.hom) hq
    change (e.inv ≫ P.sectionMap).hom.hom ≫ (P.limit ≫ e.hom).hom.hom = 𝟙 _ at hq₀
    have hk : P.contractingToParabolic.hom.hom ≫ (P.limit ≫ e.hom).hom.hom = 1 := by
      change P.contractingToParabolic.hom.hom ≫ P.limit.hom.hom ≫ e.hom.hom.hom = _
      rw [← Category.assoc, P.isKernel.w, Category.assoc, IsMonHom.one_hom]
      rfl
    rw [MonObj.mul_comp, Category.assoc h, hq₀, Category.comp_id, Category.assoc u',
      hk, MonObj.comp_one, mul_one]

private theorem limit_factors {c : Cocharacter G.val} (P : LimitDecomposition c)
    {H : ClosedSubgroup G.val} (e : P.centralizer.group ≅ H.group)
    (he : e.hom ≫ H.inclusion = P.centralizer.inclusion)
    {Y : SchemeOver k} (p : Y ⟶ P.parabolic.group.X) :
    ∃ u' : Y ⟶ P.contracting.group.X,
      ((p ≫ (P.limit ≫ e.hom).hom.hom) ≫ H.inclusion.hom.hom) *
        (u' ≫ P.contracting.inclusion.hom.hom) = p ≫ P.parabolic.inclusion.hom.hom := by
  letI := P.product_iso
  obtain ⟨x, u', hx⟩ := factors_of_iso P.sectionMap P.contractingToParabolic p
  have hx' : (x ≫ e.hom.hom.hom) ≫ (e.inv ≫ P.sectionMap).hom.hom = x ≫ P.sectionMap.hom.hom := by
    have h' := congrArg (fun f : P.centralizer.group ⟶ P.parabolic.group => f.hom.hom)
      (e.hom_inv_id_assoc P.sectionMap)
    change e.hom.hom.hom ≫ (e.inv ≫ P.sectionMap).hom.hom = P.sectionMap.hom.hom at h'
    rw [Category.assoc, h']
  obtain ⟨h₁, h₂⟩ := limit_product P e he (x ≫ e.hom.hom.hom) u'
  rw [hx', hx] at h₁ h₂
  refine ⟨u', ?_⟩
  rw [h₂]
  exact h₁.symm

private theorem borel_pullback {c : Cocharacter G.val} (P : LimitDecomposition c)
    {H B : ClosedSubgroup G.val} (e : P.centralizer.group ≅ H.group)
    (he : e.hom ≫ H.inclusion = P.centralizer.inclusion) (A : ClosedSubgroup H.group)
    (hB : ∀ {Y : SchemeOver k} (p : Y ⟶ G.val.X), p ∈ SubgroupSections B Y ↔
      ∃ (a : Y ⟶ A.group.X) (u' : Y ⟶ P.contracting.group.X),
        (a ≫ A.inclusion.hom.hom ≫ H.inclusion.hom.hom) *
          (u' ≫ P.contracting.inclusion.hom.hom) = p) :
    ∃ (j : B.group ⟶ P.parabolic.group) (r : B.group ⟶ A.group) (t : A.group ⟶ B.group),
      j ≫ P.parabolic.inclusion = B.inclusion ∧
      IsPullback j.hom.hom r.hom.hom (P.limit ≫ e.hom).hom.hom A.inclusion.hom.hom ∧
      A.inclusion ≫ (e.inv ≫ P.sectionMap) = t ≫ j ∧
      ∀ {Y : SchemeOver k} (p : Y ⟶ P.parabolic.group.X),
        p ≫ P.parabolic.inclusion.hom.hom ∈ SubgroupSections B Y ↔
          p ≫ (P.limit ≫ e.hom).hom.hom ∈ SubgroupSections A Y := by
  let q := P.limit ≫ e.hom
  let i := e.inv ≫ P.sectionMap
  letI := P.parabolic.isClosedImmersion
  letI : Mono P.parabolic.inclusion.hom.hom := Over.mono_of_mono_left _
  have hBP : IsSubgroupOf B P.parabolic := by
    obtain ⟨a, u', h⟩ := (hB B.inclusion.hom.hom).mp (inclusion_mem_sections B)
    exact factor_group_through_subgroup P.parabolic B.inclusion _
      ((limit_product P e he (a ≫ A.inclusion.hom.hom) u').1.trans h)
  obtain ⟨j, hj⟩ := hBP
  have hj₀ : j.hom.hom ≫ P.parabolic.inclusion.hom.hom = B.inclusion.hom.hom :=
    congrArg (fun f : B.group ⟶ G.val => f.hom.hom) hj
  have hmem {Y : SchemeOver k} (p : Y ⟶ P.parabolic.group.X) :
      p ≫ P.parabolic.inclusion.hom.hom ∈ SubgroupSections B Y ↔
        p ≫ q.hom.hom ∈ SubgroupSections A Y := by
    rw [hB]
    constructor
    · rintro ⟨a, u', ha⟩
      let h := a ≫ A.inclusion.hom.hom
      let x := (h ≫ i.hom.hom) * (u' ≫ P.contractingToParabolic.hom.hom)
      obtain ⟨hx, hq⟩ := limit_product P e he h u'
      have hp : x = p := (cancel_mono P.parabolic.inclusion.hom.hom).mp (hx.trans ha)
      change x ≫ q.hom.hom = h at hq
      refine ⟨a, ?_⟩
      change h = p ≫ q.hom.hom
      rw [← hp]
      exact hq.symm
    · rintro ⟨a, ha⟩
      obtain ⟨u', hu⟩ := limit_factors P e he p
      change a ≫ A.inclusion.hom.hom = p ≫ q.hom.hom at ha
      exact ⟨a, u', by rw [← Category.assoc, ha]; exact hu⟩
  obtain ⟨r₀, hr₀⟩ := (hmem j.hom.hom).mp (hj₀.symm ▸ inclusion_mem_sections B)
  change r₀ ≫ A.inclusion.hom.hom = (j ≫ q).hom.hom at hr₀
  obtain ⟨r, hr⟩ := factor_group_through_subgroup A (j ≫ q) r₀ hr₀
  have hr' : j.hom.hom ≫ q.hom.hom = r.hom.hom ≫ A.inclusion.hom.hom :=
    (congrArg (fun f : B.group ⟶ H.group => f.hom.hom) hr).symm
  have hiq : i ≫ q = 𝟙 H.group := by
    dsimp only [i, q]
    rw [Category.assoc, ← Category.assoc P.sectionMap, P.section_limit, Category.id_comp,
      e.inv_hom_id]
  have hA : ((A.inclusion ≫ i).hom.hom ≫ q.hom.hom) ∈ SubgroupSections A A.group.X := by
    refine ⟨𝟙 _, ?_⟩
    change 𝟙 _ ≫ A.inclusion.hom.hom = ((A.inclusion ≫ i) ≫ q).hom.hom
    rw [Category.assoc, hiq, Category.comp_id, Category.id_comp]
  obtain ⟨t₀, ht₀⟩ := (hmem (A.inclusion ≫ i).hom.hom).mpr hA
  change t₀ ≫ B.inclusion.hom.hom = ((A.inclusion ≫ i) ≫ P.parabolic.inclusion).hom.hom at ht₀
  obtain ⟨t, ht⟩ := factor_group_through_subgroup B ((A.inclusion ≫ i) ≫ P.parabolic.inclusion) t₀ ht₀
  have ht' : A.inclusion ≫ i = t ≫ j := by
    apply Grp.hom_ext
    apply (cancel_mono P.parabolic.inclusion.hom.hom).mp
    change ((A.inclusion ≫ i) ≫ P.parabolic.inclusion).hom.hom =
      ((t ≫ j) ≫ P.parabolic.inclusion).hom.hom
    rw [← ht, Category.assoc t j, hj]
  refine ⟨j, r, t, hj, ?_, ht', hmem⟩
  letI := A.isClosedImmersion
  letI : Mono A.inclusion.hom.hom := Over.mono_of_mono_left _
  letI := factor_closed hj
  letI : Mono j.hom.hom := Over.mono_of_mono_left _
  have hex (s : PullbackCone q.hom.hom A.inclusion.hom.hom) :
      ∃ v : s.pt ⟶ B.group.X, v ≫ B.inclusion.hom.hom = s.fst ≫ P.parabolic.inclusion.hom.hom :=
    (hmem s.fst).mpr ⟨s.snd, s.condition.symm⟩
  choose v hv using hex
  have hfst (s : PullbackCone q.hom.hom A.inclusion.hom.hom) : v s ≫ j.hom.hom = s.fst := by
    apply (cancel_mono P.parabolic.inclusion.hom.hom).mp
    rw [Category.assoc, hj₀, hv]
  refine IsPullback.of_isLimit' ⟨hr'⟩ (PullbackCone.IsLimit.mk hr' v hfst ?_ ?_)
  · intro s
    apply (cancel_mono A.inclusion.hom.hom).mp
    rw [Category.assoc, ← hr', ← Category.assoc, hfst, s.condition]
  · intro s m hm _
    apply (cancel_mono j.hom.hom).mp
    rw [hm, hfst]

end BorelPullback

section RootConjugation

open Specs.BruhatOrbitParametrization (conjugatePoint)
open Specs.RootGroups (IsRootSubgroup)
open Specs.AdjointRepresentation (GroupPoints)
open private fibreTorsor splitFibrePoint from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.WeylScheme
open private innerMap innerIso comp_innerMap transportSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper
open private conjugateLe_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private normalizes_of_point_conjugation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private differential_comp map_weightVector from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
  {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X] {D : Datum T}

private theorem representative_exists (I : Identification D) (hT : IsSplitTorus T.group)
    (w : D.rootDatum.weylGroup) : ∃ n, IsRepresentative I w n := by
  let T' : ClosedSubgroup I.normalizer.group := ⟨T.group, I.torusInclusion, I.torusClosed⟩
  let z := I.image.constantGroup.sectionPoint (I.labelEquiv w)
  exact splitFibrePoint (G := closedSubgroupAlgebraicGroup I.normalizer) (W := I.scheme)
    T' hT I.quotient z (fibreTorsor (G := closedSubgroupAlgebraicGroup I.normalizer)
      (W := I.scheme) T' I.quotient I.isQuotient z)

private theorem representative_ratio (I : Identification D) {w : D.rootDatum.weylGroup}
    {n n' : 𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X}
    (hn : IsRepresentative I w n) (hn' : IsRepresentative I w n') (Y : SchemeOver k) :
    ∃ t ∈ SubgroupSections T Y,
      toUnit Y ≫ n' ≫ I.normalizer.inclusion.hom.hom =
        (toUnit Y ≫ n ≫ I.normalizer.inclusion.hom.hom) * t := by
  have h := normalizer_ratio_mem_torus I (Y := Y) (p := toUnit Y ≫ n) (q := toUnit Y ≫ n') (by
    rw [Category.assoc, Category.assoc, hn, hn'])
  exact ⟨_, by simpa only [Category.assoc] using h, (mul_inv_cancel_left _ _).symm⟩

private theorem representative_transports_root (I : Identification D)
    {w : D.rootDatum.weylGroup} {n : 𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X}
    (hn : IsRepresentative I w n) (β : Root T) {S : ClosedSubgroup G.val}
    (hS : IsRootSubgroup T S β.val) :
    IsRootSubgroup T (transportSubgroup S (innerIso (n ≫ I.normalizer.inclusion.hom.hom)))
      (D.rootDatum.weylGroupToPerm w β).val := by
  let g := n ≫ I.normalizer.inclusion.hom.hom
  let a := I.image.conjugation (I.labelEquiv w)
  let e := innerIso g
  have ha₀ : T.inclusion.hom.hom ≫ e.hom.hom.hom = a.hom.hom.hom ≫ T.inclusion.hom.hom := by
    rw [show e.hom = innerMap g from rfl, comp_innerMap]
    exact (representative_conjugates_torus I hn).symm
  have ha : T.inclusion ≫ e.hom = a.hom ≫ T.inclusion := Grp.hom_ext _ _ ha₀
  have hchar : (D.rootDatum.weylGroupToPerm w β).val = a.inv ≫ β.val := by
    apply Additive.ofMul.injective
    calc
      Additive.ofMul (D.rootDatum.weylGroupToPerm w β).val =
          D.rootDatum.root (D.rootDatum.weylGroupToPerm w β) := (D.root_eq _).symm
      _ = w.val.weightEquiv (D.rootDatum.root β) := (D.rootDatum.weylGroup_apply_root w β).symm
      _ = Additive.ofMul (a.inv ≫ β.val) := by
        rw [D.root_eq, I.characterAction, I.image.characterAction]
  refine ⟨hS.1, hS.2.1, ?_, ?_⟩
  · apply normalizes_of_point_conjugation
    intro R t p
    change (testSpec k).obj (op R) ⟶ T.group.X at t
    change (testSpec k).obj (op R) ⟶ S.group.X at p
    let q : (testSpec k).obj (op R) ⟶ T.group.X := t ≫ a.inv.hom.hom
    have hc := ((normalizesIff k S.inclusion S.isClosedImmersion _ _).mp hS.2.2.1).1
    obtain ⟨z, hz⟩ := (conjugateLe_iff _ _).mp hc _ q p
    refine ⟨z, ?_⟩
    have hq : (q ≫ T.inclusion.hom.hom) ≫ e.hom.hom.hom = t ≫ T.inclusion.hom.hom := by
      rw [Category.assoc, ha₀]
      have hi : a.inv.hom.hom ≫ a.hom.hom.hom ≫ T.inclusion.hom.hom = T.inclusion.hom.hom :=
        (Grp.forget _).congr_map (a.inv_hom_id_assoc T.inclusion)
      change (t ≫ a.inv.hom.hom) ≫ a.hom.hom.hom ≫ T.inclusion.hom.hom = _
      rw [Category.assoc, hi]
    change (z ≫ S.inclusion.hom.hom) ≫ e.hom.hom.hom =
      (t ≫ T.inclusion.hom.hom) * ((p ≫ S.inclusion.hom.hom) ≫ e.hom.hom.hom) *
        (t ≫ T.inclusion.hom.hom)⁻¹
    rw [hz, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hq]
  · rintro _ ⟨x, rfl⟩
    change mapPointKernel (S.inclusion ≫ e.hom) x ∈
      adjointWeightVectors T (D.rootDatum.weylGroupToPerm w β).val
    rw [differential_comp]
    apply map_weightVector e.hom a ha
    rw [hchar, Iso.hom_inv_id_assoc]
    exact hS.2.2.2 ⟨x, rfl⟩

private theorem representative_conjugates_root_sections
    (hG : IsReductive G) (hT : IsSplitTorus T.group) (hTm : IsGeometricallyMaximal T)
    (I : Identification D) {w : D.rootDatum.weylGroup}
    {n : 𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X} (hn : IsRepresentative I w n)
    (β : Root T) {S V : ClosedSubgroup G.val} (hS : IsRootSubgroup T S β.val)
    (hV : IsRootSubgroup T V (D.rootDatum.weylGroupToPerm w β).val)
    {Y : SchemeOver k} {p : Y ⟶ G.val.X} (hp : p ∈ SubgroupSections S Y) :
    conjugatePoint (n ≫ I.normalizer.inclusion.hom.hom) p ∈ SubgroupSections V Y := by
  let g := n ≫ I.normalizer.inclusion.hom.hom
  let S' := transportSubgroup S (innerIso g)
  have hS' : IsRootSubgroup T S' (D.rootDatum.weylGroupToPerm w β).val :=
    representative_transports_root I hn β hS
  let imageRoot := D.rootDatum.weylGroupToPerm w β
  obtain ⟨_, _, W, _, _, _, _, hW⟩ := (RootData.RootGroups.rootSubgroups G hG T hT hTm).2 imageRoot.val imageRoot.property
  apply mem_sections_of_subgroupOf (hW V hV).1
  apply mem_sections_of_subgroupOf (hW S' hS').2
  obtain ⟨z, rfl⟩ := hp
  refine ⟨z, ?_⟩
  change z ≫ S.inclusion.hom.hom ≫ (innerMap g).hom.hom = conjugatePoint g _
  rw [← Category.assoc, comp_innerMap]
  rfl

end RootConjugation

section RankOneWord

open Specs.RankOneFlag (FlagIdentification Index)
open Specs.RootGroups (AdditiveLine ProjectiveAction TransvectionParametrization rankOneWord)
open Specs.AdjointRepresentation (GroupPoints)
open private basePoint_closed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.QuotientEmbedding
open private rankOneRepresentative rankOneRepresentative_point rankOneWord_comp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups

variable {k : Type u} [Field k] {H : GroupScheme k}

private theorem ambient_rank_one_word {A : AdditiveLine k} (x y : A.group ⟶ H)
    {G : GroupScheme k} (i : H ⟶ G) (n : 𝟙_ (SchemeOver k) ⟶ G.X)
    (hn : toUnit _ ≫ n = rankOneWord (x ≫ i) (y ≫ i) (CommAlgCat.of k k) 1) :
    rankOneRepresentative x y ≫ i.hom.hom = n := by
  let Y := (testSpec k).obj (op (CommAlgCat.of k k))
  have ho : (toUnit Y).left = 𝟙 _ := by
    change Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 _
    rw [show CommRingCat.ofHom (algebraMap k k) = 𝟙 _ from CommRingCat.hom_ext (by simp)]
    exact Scheme.Spec.map_id _
  haveI : IsIso ((Over.forget (Spec (CommRingCat.of k))).map (toUnit Y)) := by
    change IsIso ((toUnit Y).left)
    rw [ho]
    infer_instance
  letI : IsIso (toUnit Y) := isIso_of_reflects_iso _ (Over.forget _)
  apply (cancel_epi (toUnit Y)).mp
  change toUnit Y ≫ (rankOneRepresentative x y ≫ i.hom.hom) = toUnit Y ≫ n
  change toUnit Y ≫ n = rankOneWord (x ≫ i) (y ≫ i) (CommAlgCat.of k k) 1 at hn
  have hword : toUnit Y ≫ rankOneRepresentative x y = rankOneWord x y (CommAlgCat.of k k) 1 :=
    rankOneRepresentative_point x y (CommAlgCat.of k k)
  calc
    toUnit Y ≫ (rankOneRepresentative x y ≫ i.hom.hom) =
        (toUnit Y ≫ rankOneRepresentative x y) ≫ i.hom.hom := (Category.assoc _ _ _).symm
    _ = rankOneWord x y (CommAlgCat.of k k) 1 ≫ i.hom.hom :=
      congrArg (fun f : Y ⟶ H.X => f ≫ i.hom.hom) hword
    _ = rankOneWord (x ≫ i) (y ≫ i) (CommAlgCat.of k k) 1 :=
      (rankOneWord_comp x y i (CommAlgCat.of k k) 1).symm
    _ = toUnit Y ≫ n := hn.symm

private theorem rank_one_word_sections {K : Type u} [Field K] [Algebra k K]
    {T B Bneg U V : ClosedSubgroup H} {Q : Presentation B}
    (F : FlagIdentification T B Bneg V Q)
    (P : ProjectiveAction F.action (η[H.X] ≫ Q.projection)
      (F.normalizerPoint ≫ Q.projection)) (A : AdditiveLine k)
    (p : TransvectionParametrization P A U ⟨0⟩ ⟨1⟩ (by decide))
    (n : TransvectionParametrization P A V ⟨1⟩ ⟨0⟩ (by decide)) :
    let Y := Over.mk (fieldSpecMap k K)
    let rep := rankOneRepresentative (p.root.hom ≫ U.inclusion) (n.root.hom ≫ V.inclusion)
    (toUnit Y ≫ rep) ∉ SubgroupSections B Y ∧
    ∀ h : Y ⟶ H.X, h ∈ SubgroupSections B Y ∨
      ∃ (v : Y ⟶ V.group.X) (b : Y ⟶ B.group.X),
        (toUnit Y ≫ rep) * (v ≫ V.inclusion.hom.hom) * (b ≫ B.inclusion.hom.hom) = h := by
  let Y := Over.mk (fieldSpecMap k K)
  let x := p.root.hom ≫ U.inclusion
  let y := n.root.hom ≫ V.inclusion
  let rep := rankOneRepresentative x y
  let m := F.normalizerPoint
  have equivariance (a b : Y ⟶ H.X) :
      lift a (b ≫ Q.projection) ≫ F.action.smul = (a * b) ≫ Q.projection := by
    have h := congrArg (fun f => lift a b ≫ f) F.quotientEquivariance
    simpa only [← Category.assoc, lift_map, Category.comp_id, MonObj.mul_eq_mul,
      MonObj.comp_mul, lift_fst, lift_snd] using h
  have hswap := RootData.RootGroups.rankOneWord_swaps_marks P A U V p n (CommAlgCat.of k K) 1
  have hword : toUnit Y ≫ rep = rankOneWord x y (CommAlgCat.of k K) 1 :=
    rankOneRepresentative_point x y (CommAlgCat.of k K)
  have hswap₁ : (toUnit Y ≫ rep) ≫ Q.projection = toUnit Y ≫ (m ≫ Q.projection) := by
    have h := hswap.1
    change lift (rankOneWord x y (CommAlgCat.of k K) 1)
      ((toUnit Y ≫ η[H.X]) ≫ Q.projection) ≫ F.action.smul = toUnit Y ≫ (m ≫ Q.projection) at h
    rw [← hword, equivariance, MonObj.one_eq_one, MonObj.comp_one, mul_one] at h
    exact h
  have hswap₂ : ((toUnit Y ≫ rep) * (toUnit Y ≫ m)) ≫ Q.projection =
      (1 : Y ⟶ H.X) ≫ Q.projection := by
    have h := hswap.2
    change lift (rankOneWord x y (CommAlgCat.of k K) 1)
      ((toUnit Y ≫ m) ≫ Q.projection) ≫ F.action.smul = toUnit Y ≫ (η[H.X] ≫ Q.projection) at h
    rw [← hword, equivariance, ← Category.assoc (toUnit Y) η[H.X], MonObj.one_eq_one,
      MonObj.comp_one] at h
    exact h
  have hm := basePoint_closed Q.quasiProjective (m ≫ Q.projection)
  refine ⟨?_, fun h => rank_one_sections Q m rep hm F.openCell F.openCellRange hswap₂ h⟩
  intro h
  have h' : (1 : Y ⟶ H.X) ≫ Q.projection = (toUnit Y ≫ rep) ≫ Q.projection :=
    (projection_eq_sections Q).mpr (by simpa only [inv_one, one_mul] using h)
  have hneq : toUnit Y ≫ (η[H.X] ≫ Q.projection) = toUnit Y ≫ (m ≫ Q.projection) := by
    rw [← Category.assoc, MonObj.one_eq_one, MonObj.comp_one, h', hswap₁]
  apply F.distinct
  let z : Y.left := IsLocalRing.closedPoint K
  have hr : Set.range (η[H.X] ≫ Q.projection).left ⊆ Set.range (m ≫ Q.projection).left := by
    rintro _ ⟨a, rfl⟩
    have he := congrArg (fun f : Y ⟶ Q.scheme => f.left z) hneq
    change (η[H.X] ≫ Q.projection).left ((toUnit Y).left z) =
      (m ≫ Q.projection).left ((toUnit Y).left z) at he
    have ha : (toUnit Y).left z = a := Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [ha] at he
    exact ⟨a, he.symm⟩
  letI : IsReduced (𝟙_ (SchemeOver k)).left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
  obtain ⟨f, hf⟩ := closed_factor_of_range _ _ hm hr
  have hf' : f = 𝟙 _ := Subsingleton.elim _ _
  rw [hf', Category.id_comp] at hf
  exact hf.symm

end RankOneWord

/-- The simple wall of a regular positive system is integral, and the
contracting subgroup has the ordered coordinates of the other positive roots. -/
theorem wallContractingProduct_conditional
    (contractingProduct : Specs.OrderedRootProducts.ContractingProduct.{u})
    (simpleRoots : Specs.SimpleRoots.Statement.{u})
    {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T B : ClosedSubgroup G.val) (hT : IsSplitTorus T.group)
    (hTm : IsGeometricallyMaximal T) (c : Cocharacter T.group)
    (hc : IsRegular T c) (hB : positiveRoots T c = subgroupRoots T B) :
    ∃ h : IsCommMonObj T.group.X, letI := h
      ∃ (D : Datum T) (_I : Identification D) (U : RootSubgroupFamily T) (b : D.rootDatum.Base),
        SimpleRoots.IsBaseFor D.rootDatum (SimpleRoots.evaluate D c) b ∧
        ∀ α ∈ b.support,
          ∃ (wall : Cocharacter T.group) (P : LimitDecomposition (wall ≫ T.inclusion)),
            IsWallCocharacter T B α wall ∧
            ∀ l, Enumerates l (subgroupRoots T B \ {α}) →
              Parametrizes U l P.contracting.inclusion.hom.hom := by
  obtain ⟨hcomm, D, I, hbase⟩ := simpleRoots G hG T hT hTm
  letI := hcomm
  obtain ⟨b, hb, hw, _⟩ := hbase c hc
  obtain ⟨_, ⟨U⟩, hproduct⟩ := contractingProduct G hG T hT hTm
  refine ⟨hcomm, D, I, U, b, hb, ?_⟩
  intro α hα
  obtain ⟨wall, hwall⟩ := hw α hα
  have hα' : α ∈ subgroupRoots T B := by
    rw [← hB]
    change 0 < pairing T.group α.val c
    have h := (hb.simple_iff α).mp hα |>.1
    change 0 < SimpleRoots.evaluate D c (D.rootDatum.root α) at h
    rwa [evaluate_root] at h
  have hW := wall_of_simple D hc hB wall hwall hα'
  obtain ⟨⟨P⟩, hP⟩ := hproduct wall
  exact ⟨wall, P, hW, fun l hl => hP P U l (hW.2.symm ▸ hl)⟩

section SimpleParabolic

open Specs.BruhatOrbitParametrization (conjugatePoint)
open Specs.RootGroups (IsRootSubgroup)
open CocharacterDynamics (limitSubgroupsSmooth)
open private factor_closed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private subgroupOf_trans from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private extend_subgroupOf from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private kBorel_smooth_connected rootContainment_iff lieImage_eq_of_same lieImage_mono
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private rankOneRepresentative from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

private theorem root_comparison (hG : IsReductive G) {T : ClosedSubgroup G.val}
    (hT : IsSplitTorus T.group) (hTm : IsGeometricallyMaximal T)
    (β : Root T) {U V : ClosedSubgroup G.val} (hU : IsRootSubgroup T U β.val)
    (hV : IsRootSubgroup T V β.val) :
    SameSubgroup V U ∧ lieImage V = adjointWeightVectors T β.val := by
  obtain ⟨_, _, S, _, _, hS, _, hunique⟩ :=
    (RootData.RootGroups.rootSubgroups G hG T hT hTm).2 β.val β.property
  exact ⟨⟨subgroupOf_trans (hunique V hV).2 (hunique U hU).1,
    subgroupOf_trans (hunique U hU).2 (hunique V hV).1⟩,
    (lieImage_eq_of_same (hunique V hV)).symm.trans hS⟩

private theorem translate_singleton_mul_subgroup {M : Type*} [Group M]
    (B : Subgroup M) (L : Set M) (g : M) {t : M} (ht : t ∈ B) :
    L * {g * t} * (B : Set M) = L * {g} * (B : Set M) := by
  have h : ({g * t} : Set M) * (B : Set M) = {g} * (B : Set M) := by
    ext x
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      rw [Set.mem_singleton_iff.mp ha]
      exact Set.mem_mul.mpr ⟨g, rfl, t * b, B.mul_mem ht hb, (mul_assoc _ _ _).symm⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      rw [Set.mem_singleton_iff.mp ha]
      exact Set.mem_mul.mpr ⟨g * t, rfl, t⁻¹ * b, B.mul_mem (B.inv_mem ht) hb, by group⟩
  rw [mul_assoc, h, ← mul_assoc]

/-- The elementary wall parabolic and its double-coset products, under the
ordered upstream hypotheses of the conditional proof contract. -/
theorem simpleParabolicProduct_conditional
    (_bruhatOrbitParametrization : Specs.BruhatOrbitParametrization.Statement.{u})
    (_borelRadicalProduct : Specs.OrderedRootProducts.BorelRadicalProduct.{u})
    (contractingProduct : Specs.OrderedRootProducts.ContractingProduct.{u})
    (_regularRootCell : Specs.OrderedRootProducts.RegularRootCell.{u})
    (simpleRoots : Specs.SimpleRoots.Statement.{u}) : Specs.SimpleParabolicProduct.Statement.{u} := by
  classical
  intro k _ G hG T B hT hTm hB hTB
  letI := hG.1
  obtain ⟨c, E, hc, hBE, hpos⟩ := (RootData.BorelsAndChambers.borelsThroughT G hG T hT hTm).1 B hB hTB
  have hTc := (RootData.BorelsAndChambers.regularCocharacterBorel G hG T hT hTm c hc E).1
  have hBs := kBorel_smooth_connected G B hB
  obtain ⟨hcomm, D, I, U, b, hb, hw⟩ :=
    wallContractingProduct_conditional contractingProduct simpleRoots G hG T B hT hTm c hc hpos.symm
  letI := hcomm
  letI := D.finiteRoots
  obtain ⟨_, _, hproduct⟩ := contractingProduct G hG T hT hTm
  refine ⟨hcomm, D, I, U, c, b, hc, hpos.symm, hb, representative_exists I hT, ?_⟩
  intro α hα
  dsimp only
  let s := RootPairing.weylGroup.ofIdx D.rootDatum α
  let β := D.rootDatum.reflectionPerm α α
  have hβ : β.val = α.val⁻¹ := opposite_root D α
  have hsβ : D.rootDatum.weylGroupToPerm s β = α := D.rootDatum.reflectionPerm_self α α
  have hαB : α ∈ subgroupRoots T B := by
    have h := (hb.simple_iff α).mp hα |>.1
    change 0 < SimpleRoots.evaluate D c (D.rootDatum.root α) at h
    rw [evaluate_root] at h
    exact hpos.symm ▸ (show α ∈ positiveRoots T c from h)
  obtain ⟨wall, P, hW, hP'⟩ := hw α hα
  obtain ⟨l, hl⟩ := has_enumeration (subgroupRoots T B \ {α})
  have hαl : Enumerates (α :: l) (positiveRoots T c) := by
    rw [← hpos]
    refine ⟨List.nodup_cons.mpr ⟨fun h => ((hl.2 α).mp h).2 rfl, hl.1⟩, ?_⟩
    intro δ
    rw [List.mem_cons, hl.2]
    constructor
    · rintro (rfl | h)
      · exact hαB
      · exact h.1
    · intro h
      by_cases he : δ = α
      · exact Or.inl he
      · exact Or.inr ⟨h, he⟩
  have hE := (hproduct c).2 E U (α :: l) hαl
  obtain ⟨H, cH, hH, _, L, M, hpair, QH, F, a, A0, xpos, xneg,
    hUpos, hUneg, _, _, rα, hrα⟩ := D.attached α
  let A := L.parabolic
  let Vpos := subgroupOfSubgroup H.subgroup L.contracting
  let Vneg := subgroupOfSubgroup H.subgroup M.contracting
  have hVneg : IsRootSubgroup T Vneg β.val := by
    rw [hβ]
    exact hUneg
  obtain ⟨hRoot, hLie⟩ := root_comparison hG hT hTm α (U α).property hUpos
  obtain ⟨_, hLieNeg⟩ := root_comparison hG hT hTm β (U β).property hVneg
  have hL : adjointWeightVectors T α.val ⊆ lieImage H.subgroup := by
    rw [← hLie]
    exact lieImage_mono (show IsSubgroupOf Vpos H.subgroup from ⟨L.contracting.inclusion, rfl⟩)
  have hM : adjointWeightVectors T α.val⁻¹ ⊆ lieImage H.subgroup := by
    rw [← hβ, ← hLieNeg]
    exact lieImage_mono (show IsSubgroupOf Vneg H.subgroup from ⟨M.contracting.inclusion, rfl⟩)
  obtain ⟨e, he⟩ := wall_levi hG hT hTm wall hW P H hH hL hM
  have hBfactor {Y : SchemeOver k} (p : Y ⟶ G.val.X) : p ∈ SubgroupSections B Y ↔
      ∃ (a : Y ⟶ A.group.X) (u' : Y ⟶ P.contracting.group.X),
        (a ≫ A.inclusion.hom.hom ≫ H.subgroup.inclusion.hom.hom) *
          (u' ≫ P.contracting.inclusion.hom.hom) = p := by
    rw [borel_sections c wall E P hBE hTc U α l hE (hP' l hl)]
    constructor
    · rintro ⟨t, x, u', rfl⟩
      obtain ⟨z, hz⟩ := (rank_one_borel_sections H L hpair.1 (U α).val hRoot).mpr ⟨t, x, rfl⟩
      exact ⟨z, u', by rw [hz]⟩
    · rintro ⟨z, u', rfl⟩
      obtain ⟨t, x, hx⟩ := (rank_one_borel_sections H L hpair.1 (U α).val hRoot).mp ⟨z, rfl⟩
      exact ⟨t, x, u', by rw [hx]⟩
  obtain ⟨j, r, t, hj, hpb, ht, hpre⟩ := borel_pullback P e he A hBfactor
  have hj' := factor_closed hj
  let B' : ClosedSubgroup P.parabolic.group := ⟨B.group, j, hj'⟩
  have hparabolic : BorelProper.IsParabolic G P.parabolic := by
    obtain ⟨hclosed, hgeom⟩ := hB
    let K := AlgebraicClosure k
    have hc' := baseChangeClosedSubgroup k K P.parabolic.inclusion P.parabolic.isClosedImmersion
    exact ⟨hG, (limitSubgroupsSmooth G _ P).1, hc', _, hgeom,
      extend_subgroupOf (K := K) ⟨j, hj⟩⟩
  have hi : (e.inv ≫ P.sectionMap) ≫ (P.limit ≫ e.hom) = 𝟙 _ := by
    rw [Category.assoc, ← Category.assoc P.sectionMap, P.section_limit, Category.id_comp,
      e.inv_hom_id]
  refine ⟨wall, P, H, hW, hparabolic, hP', e, j, A, r, hj', he, hj, hpair.2.2.1.1,
    hpb, (HomogeneousQuotient.homogeneousQuotient k (closedSubgroupAlgebraicGroup P.parabolic) B').1,
    ⟨QH⟩, ?_, ?_⟩
  · intro Q Q'
    obtain ⟨f, hf⟩ := split_preimage_quotient _ _ hi r hpb t ht Q Q'
    obtain ⟨g, _, _⟩ := HomogeneousQuotient.quotientUniqueness Q' QH
    exact ⟨f, hf, ⟨g ≪≫ F.iso⟩⟩
  · intro n hn K _ _ _
    let Y := Over.mk (fieldSpecMap k K)
    let rep := rankOneRepresentative (xpos.root.hom ≫ L.contracting.inclusion)
      (xneg.root.hom ≫ M.contracting.inclusion)
    have ha0 : rep ≫ H.subgroup.inclusion.hom.hom = rα.representative := by
      apply ambient_rank_one_word
      simpa only [Category.assoc] using rα.representative_word
    obtain ⟨m, hm, hmG⟩ := coroot_reflection_is_representative I α rα hrα
    have hrep : toUnit Y ≫ rep ≫ H.subgroup.inclusion.hom.hom =
        toUnit Y ≫ m ≫ I.normalizer.inclusion.hom.hom := by rw [ha0, hmG]
    let mY := toUnit Y ≫ m ≫ I.normalizer.inclusion.hom.hom
    let Bsec := SubgroupSections B Y
    let Psec := SubgroupSections P.parabolic Y
    let Usec := SubgroupSections (U α).val Y
    let q := P.limit ≫ e.hom
    obtain ⟨hrepA, hcells⟩ := rank_one_word_sections (K := K) F a A0 xpos xneg
    have hmY : mY ∈ Psec ∧ mY ∉ Bsec := by
      let x := (toUnit Y ≫ rep) ≫ (e.inv ≫ P.sectionMap).hom.hom
      have hx : x ≫ P.parabolic.inclusion.hom.hom = mY := by
        have h := (limit_product P e he (toUnit Y ≫ rep) (1 : Y ⟶ P.contracting.group.X)).1
        simpa only [MonObj.one_comp, mul_one, Category.assoc, hrep, x, mY] using h
      have hxq : x ≫ q.hom.hom = toUnit Y ≫ rep := by
        have h := (limit_product P e he (toUnit Y ≫ rep) (1 : Y ⟶ P.contracting.group.X)).2
        simpa only [MonObj.one_comp, mul_one, x, q] using h
      refine ⟨⟨x, hx⟩, fun h => hrepA ?_⟩
      rw [← hxq]
      exact (hpre x).mp (hx.symm ▸ h)
    have hUle : Usec ≤ Bsec := mem_sections_of_subgroupOf
      ((rootContainment_iff G hG T B hT hTm hBs.1 hBs.2 hTB α _ (U α).property).mp hαB)
    have hPsplit : (Psec : Set (Y ⟶ G.val.X)) = (Bsec : Set (Y ⟶ G.val.X)) ∪ ((Usec : Set (Y ⟶ G.val.X)) * {mY} * (Bsec : Set (Y ⟶ G.val.X))) := by
      ext g
      constructor
      · rintro ⟨p, rfl⟩
        change Y ⟶ P.parabolic.group.X at p
        obtain ⟨u', hu⟩ := limit_factors P e he p
        rcases hcells (p ≫ q.hom.hom) with h | ⟨z, b', h⟩
        · exact Or.inl ((hpre p).mpr h)
        · right
          let zG := z ≫ M.contracting.inclusion.hom.hom ≫ H.subgroup.inclusion.hom.hom
          have hS := representative_conjugates_root_sections hG hT hTm I hm β hVneg
            (show IsRootSubgroup T (U α).val (D.rootDatum.weylGroupToPerm s β).val from
              by rw [hsβ]; exact (U α).property) (Y := Y) (p := zG) ⟨z, rfl⟩
          let bG := b' ≫ A.inclusion.hom.hom ≫ H.subgroup.inclusion.hom.hom
          let uG := u' ≫ P.contracting.inclusion.hom.hom
          have hbG : bG * uG ∈ Bsec := (hBfactor _).mpr ⟨b', u', rfl⟩
          have hh := congrArg (fun f : Y ⟶ H.subgroup.group.X => f ≫ H.subgroup.inclusion.hom.hom) h
          simp only [MonObj.mul_comp, Category.assoc] at hh
          change (toUnit Y ≫ rep ≫ H.subgroup.inclusion.hom.hom) * zG * bG =
            p ≫ q.hom.hom ≫ H.subgroup.inclusion.hom.hom at hh
          rw [hrep] at hh
          refine Set.mem_mul.mpr ⟨(mY * zG * mY⁻¹) * mY,
            Set.mem_mul.mpr ⟨_, hS, mY, rfl, rfl⟩, bG * uG, hbG, ?_⟩
          change _ = p ≫ P.parabolic.inclusion.hom.hom
          rw [← hu, Category.assoc p, ← hh]
          change _ = mY * zG * bG * uG
          group
      · have hBP : Bsec ≤ Psec := mem_sections_of_subgroupOf ⟨j, hj⟩
        rintro (h | h)
        · exact hBP h
        · obtain ⟨_, hdr, b', hb', rfl⟩ := Set.mem_mul.mp h
          obtain ⟨z, hz, a', ha', rfl⟩ := Set.mem_mul.mp hdr
          rw [Set.mem_singleton_iff.mp ha']
          exact Psec.mul_mem (Psec.mul_mem (hBP (hUle hz)) hmY.1) (hBP hb')
    let g := fun w ↦ toUnit Y ≫ n w ≫ I.normalizer.inclusion.hom.hom
    let C := fun w ↦ (Bsec : Set (Y ⟶ G.val.X)) * {g w} * (Bsec : Set (Y ⟶ G.val.X))
    obtain ⟨d, hd, hratio⟩ := representative_ratio I hm (hn s) Y
    have hdB : d ∈ Bsec := mem_sections_of_subgroupOf hTB hd
    change g s = mY * d at hratio
    have hC : C s = (Bsec : Set (Y ⟶ G.val.X)) * {mY} * (Bsec : Set (Y ⟶ G.val.X)) := by
      dsimp only [C]
      rw [hratio, translate_singleton_mul_subgroup Bsec _ mY hdB]
    have hCU : (Usec : Set (Y ⟶ G.val.X)) * {g s} * (Bsec : Set (Y ⟶ G.val.X)) = (Usec : Set (Y ⟶ G.val.X)) * {mY} * (Bsec : Set (Y ⟶ G.val.X)) := by
      rw [hratio, translate_singleton_mul_subgroup Bsec _ mY hdB]
    obtain ⟨hPP, hdis, hcell⟩ := doubleCoset_of_rank_one_decomposition Bsec Psec Usec mY hUle hmY.2 hPsplit
    rw [← hC] at hPP hdis hcell
    rw [← hCU] at hcell
    change (Psec : Set (Y ⟶ G.val.X)) = (Bsec : Set (Y ⟶ G.val.X)) ∪ C s ∧ Disjoint (Bsec : Set (Y ⟶ G.val.X)) (C s) ∧
      C s = (Usec : Set (Y ⟶ G.val.X)) * {g s} * (Bsec : Set (Y ⟶ G.val.X)) ∧
      ∀ v, C v * (Psec : Set (Y ⟶ G.val.X)) = C v ∪ C (v * s) ∧
        (D.rootDatum.weylGroupToPerm v α ∈ subgroupRoots T B → C v * C s = C (v * s))
    refine ⟨hPP, hdis, hcell, ?_⟩
    apply doubleCoset_mul_rule Bsec Psec Usec g s
      (fun v => D.rootDatum.weylGroupToPerm v α ∈ subgroupRoots T B)
      (reflection_square D α) (fun v => increasing_after_reflection D hc hpos.symm α v) hPP hcell
    · intro v hv a' ha'
      let imageRoot := D.rootDatum.weylGroupToPerm v α
      have hconjugate := representative_conjugates_root_sections hG hT hTm I (hn v) α (U α).property (U imageRoot).property ha'
      have himageRootB := (rootContainment_iff G hG T B hT hTm hBs.1 hBs.2 hTB imageRoot _ (U imageRoot).property).mp hv
      exact mem_sections_of_subgroupOf himageRootB hconjugate
    · intro v
      obtain ⟨z, hz, he'⟩ := representative_product I n hn Y v s
      exact ⟨z, mem_sections_of_subgroupOf hTB hz, he'⟩

end SimpleParabolic

end

end LinearAlgebraicGroups.Flag.SimpleParabolicProduct

universe v8_closure_ea75a870c24e1151_u0
theorem _root_.«LinearAlgebraicGroups».«Flag».«SimpleParabolicProduct».«simpleParabolicProduct» : _root_.«LinearAlgebraicGroups».«Specs».«SimpleParabolicProduct».«Statement».{v8_closure_ea75a870c24e1151_u0} :=
  @_root_.«LinearAlgebraicGroups».«Flag».«SimpleParabolicProduct».«simpleParabolicProduct_conditional».{v8_closure_ea75a870c24e1151_u0} (@_root_.«LinearAlgebraicGroups».«Flag».«BruhatOrbitParametrization».«bruhatOrbitParametrization».{v8_closure_ea75a870c24e1151_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«OrderedRootProducts».«borelRadicalProduct».{v8_closure_ea75a870c24e1151_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«OrderedRootProducts».«contractingProduct».{v8_closure_ea75a870c24e1151_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«OrderedRootProducts».«regularRootCell».{v8_closure_ea75a870c24e1151_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«SimpleRoots».«simpleRoots».{v8_closure_ea75a870c24e1151_u0})
