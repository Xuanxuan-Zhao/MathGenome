import Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitOppositeBorelUniqueness
import LinearAlgebraicGroups.Classification.PinnedEquivalence
import LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.QuasiSplitOppositeBorelUniqueness

open _root_.LinearAlgebraicGroups.Specs
open Specs.BorelsAndChambers (IsPositiveSystem subgroupRoots)
open Specs.CharacterPairing (absoluteRoots adjointWeightVectors)
open Specs.GeometricBorelConjugacy (IsKBorel)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open Specs.RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open Specs.UnipotentRadicalIntersection (IsSchemeIntersection)
open CocharacterDynamics (lieImage)

open private pushKBorel from LinearAlgebraicGroups.Classification.PinnedEquivalence
open private transportSubgroup from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private subgroup_of_intersection from LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
open private inclusion_mono subgroupIso from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private root_weight_unique from LinearAlgebraicGroups.RootData.RootGroups

noncomputable section

variable {k : Type u} [Field k]

private theorem pair_sections {G : GroupScheme k} {M N : ClosedSubgroup G}
    {Y : SchemeOver k} {p : Y ⟶ G.X} :
    (∀ S ∈ ({M, N} : Set (ClosedSubgroup G)), p ∈ SubgroupSections S Y) ↔
      p ∈ SubgroupSections M Y ∧ p ∈ SubgroupSections N Y := by
  constructor
  · intro h
    exact ⟨h M (by simp), h N (by simp)⟩
  · rintro ⟨hM, hN⟩ S hS
    have he : S = M ∨ S = N := by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hS
    rcases he with rfl | rfl
    · exact hM
    · exact hN

/-- Taking identity tangent vectors preserves the intersection of two subgroups. -/
private theorem lie_mem_intersection {G : GroupScheme k} {T B C : ClosedSubgroup G}
    (h : IsSchemeIntersection {B, C} T) {v : Lie k G}
    (hvB : v ∈ lieImage B) (hvC : v ∈ lieImage C) : v ∈ lieImage T := by
  let R := CommAlgCat.of k (DualNumber k)
  have section_of_tangent {S : ClosedSubgroup G} (hv : v ∈ lieImage S) :
      v.toMul.val ∈ SubgroupSections S ((testSpec k).obj (Opposite.op R)) := by
    obtain ⟨w, hw⟩ := hv
    exact ⟨w.toMul.val, congrArg (fun p : Lie k G ↦ p.toMul.val) hw⟩
  obtain ⟨q, hq⟩ := (h _ v.toMul.val).mpr
    (pair_sections.mpr ⟨section_of_tangent hvB, section_of_tangent hvC⟩)
  change Points T.group.X R at q
  change q ≫ T.inclusion.hom.hom = v.toMul.val at hq
  have hred : mapPoints (dualReduction k) q = 1 := by
    have := T.isClosedImmersion
    have : Mono T.inclusion.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono T.inclusion.hom.hom).mp
    change ((testSpec k).map (dualReduction k).op ≫ q) ≫ T.inclusion.hom.hom =
      1 ≫ T.inclusion.hom.hom
    rw [Category.assoc, hq]
    have hv : mapPoints (dualReduction k) v.toMul.val = 1 := v.toMul.property
    rw [show (testSpec k).map (dualReduction k).op ≫ v.toMul.val = 1 from hv]
    exact (MonObj.one_comp T.inclusion.hom.hom).symm
  exact ⟨⟨q, hred⟩, Subtype.ext hq⟩

/-- The common torus has zero weight only, so the two root sets are disjoint. -/
private theorem no_common_root (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T B C : ClosedSubgroup G.val) (hT : IsSplitTorus T.group)
    (hTm : IsGeometricallyMaximal T) (h : IsSchemeIntersection {B, C} T)
    (α : ↥(absoluteRoots T)) (hB : α ∈ subgroupRoots T B) (hC : α ∈ subgroupRoots T C) :
    False := by
  obtain ⟨hne, v, hv, hv0⟩ := α.property
  have hvT := lie_mem_intersection h (hB hv) (hC hv)
  change v ∈ Set.range (mapPointKernel T.inclusion) at hvT
  rw [(RootData.RootGroups.rootSubgroups G hG T hT hTm).1.2] at hvT
  exact hne (root_weight_unique G T hT hv0 hv hvT)

private theorem opposite_positive_system {G : GroupScheme k} {T : ClosedSubgroup G}
    {S : Set ↥(absoluteRoots T)} (hS : IsPositiveSystem T S)
    {α β : ↥(absoluteRoots T)} (hβ : β.val = α.val⁻¹) :
    β ∈ S ↔ α ∉ S := by
  obtain ⟨f, hf, rfl⟩ := hS
  change 0 < f (Additive.ofMul β.val) ↔ ¬ 0 < f (Additive.ofMul α.val)
  rw [hβ, show Additive.ofMul (α.val⁻¹) = -(Additive.ofMul α.val) from rfl, map_neg]
  have hn := hf α
  constructor
  · intro h
    exact not_lt_of_ge (neg_pos.mp h).le
  · intro h
    exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt h) hn)

private theorem same_opposite (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T B C D : ClosedSubgroup G.val) (hT : IsSplitTorus T.group)
    (hTm : IsGeometricallyMaximal T) (hB : IsKBorel B) (hC : IsKBorel C) (hD : IsKBorel D)
    (hBC : IsSchemeIntersection {B, C} T) (hBD : IsSchemeIntersection {B, D} T) :
    SameSubgroup C D := by
  have hTB := (subgroup_of_intersection (H := T) hBC).mp ⟨𝟙 _, Category.id_comp _⟩ B (by simp)
  have hTC := (subgroup_of_intersection (H := T) hBC).mp ⟨𝟙 _, Category.id_comp _⟩ C (by simp)
  have hTD := (subgroup_of_intersection (H := T) hBD).mp ⟨𝟙 _, Category.id_comp _⟩ D (by simp)
  obtain ⟨_, _, _, corr, _, _⟩ := RootData.BorelPositivity.borelPositivity G hG T hT hTm
  have posB := corr.1 B hB hTB
  have roots_complement (E : ClosedSubgroup G.val)
      (posE : IsPositiveSystem T (subgroupRoots T E)) (hBE : IsSchemeIntersection {B, E} T)
      (α : ↥(absoluteRoots T)) : α ∈ subgroupRoots T E ↔ α ∉ subgroupRoots T B := by
    have hroot := (RootData.RootGroups.rootSubgroups G hG T hT hTm).2 α.val α.property
    let β : ↥(absoluteRoots T) := ⟨α.val⁻¹, ((hroot.2.1 _).mpr (Or.inr rfl)).1⟩
    constructor
    · intro hα hαB
      exact no_common_root G hG T B E hT hTm hBE α hαB hα
    · intro hα
      have hβ := (opposite_positive_system posB (β := β) rfl).mpr hα
      by_contra hn
      exact no_common_root G hG T B E hT hTm hBE β hβ
        ((opposite_positive_system posE (β := β) rfl).mpr hn)
  -- The argument for individual roots also applies when the root set is empty.
  apply (corr.2.2 C D hC hD hTC hTD).mp
  ext α
  exact (roots_complement C (corr.1 C hC hTC) hBC α).trans
    (roots_complement D (corr.1 D hD hTD) hBD α).symm

private theorem sections_iff_of_square {G H : GroupScheme k} {S : ClosedSubgroup G}
    {S' : ClosedSubgroup H} (e : G ≅ H) (a : S.group ≅ S'.group)
    (ha : S.inclusion ≫ e.hom = a.hom ≫ S'.inclusion)
    (Y : SchemeOver k) (y : Y ⟶ G.X) :
    y ∈ SubgroupSections S Y ↔ y ≫ e.hom.hom.hom ∈ SubgroupSections S' Y := by
  let g : G.X ≅ H.X := (Grp.forget (SchemeOver k)).mapIso e
  let i : S.group.X ≅ S'.group.X := (Grp.forget (SchemeOver k)).mapIso a
  have hsq : S.inclusion.hom.hom ≫ g.hom = i.hom ≫ S'.inclusion.hom.hom :=
    congrArg (fun m : S.group ⟶ H ↦ m.hom.hom) ha
  change (∃ s : Y ⟶ S.group.X, s ≫ S.inclusion.hom.hom = y) ↔
    ∃ s' : Y ⟶ S'.group.X, s' ≫ S'.inclusion.hom.hom = y ≫ g.hom
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s ≫ i.hom, by simp only [Category.assoc, hsq]⟩
  · rintro ⟨s', hs'⟩
    refine ⟨s' ≫ i.inv, (cancel_mono g.hom).mp ?_⟩
    rw [Category.assoc, Category.assoc, hsq, i.inv_hom_id_assoc]
    exact hs'

private theorem transport_intersection {G H : GroupScheme k}
    {T B C : ClosedSubgroup G} {T' B' C' : ClosedSubgroup H}
    (e : G ≅ H) (t : T.group ≅ T'.group) (b : B.group ≅ B'.group)
    (c : C.group ≅ C'.group)
    (ht : T.inclusion ≫ e.hom = t.hom ≫ T'.inclusion)
    (hb : B.inclusion ≫ e.hom = b.hom ≫ B'.inclusion)
    (hc : C.inclusion ≫ e.hom = c.hom ≫ C'.inclusion)
    (hBC : IsSchemeIntersection {B, C} T) :
    IsSchemeIntersection {B', C'} T' := by
  intro Y z
  let f : G.X ≅ H.X := (Grp.forget (SchemeOver k)).mapIso e
  let y : Y ⟶ G.X := z ≫ f.inv
  have hz : y ≫ e.hom.hom.hom = z := by
    change (z ≫ f.inv) ≫ f.hom = z
    rw [Category.assoc, f.inv_hom_id, Category.comp_id]
  have h₁ := sections_iff_of_square e t ht Y y
  have h₂ := sections_iff_of_square e b hb Y y
  have h₃ := sections_iff_of_square e c hc Y y
  rw [hz] at h₁ h₂ h₃
  calc
    z ∈ SubgroupSections T' Y ↔ y ∈ SubgroupSections T Y := h₁.symm
    _ ↔ y ∈ SubgroupSections B Y ∧ y ∈ SubgroupSections C Y :=
      (hBC Y y).trans pair_sections
    _ ↔ z ∈ SubgroupSections B' Y ∧ z ∈ SubgroupSections C' Y := and_congr h₂ h₃
    _ ↔ _ := pair_sections.symm

/-- Any comparison of the positive Borel and torus identifies the prescribed
opposite Borel by a unique commuting isomorphism. -/
theorem oppositeUniqueness : Specs.QuasiSplitOppositeBorelUniqueness.OppositeUniqueness := by
  intro k _ G H hG hH T B C T' B' C' hT hT' hTm hTm' hB hC hB' hC' hBC hBC' e t b ht hb
  let V := transportSubgroup e C
  have hV : IsKBorel V := pushKBorel e hC
  have hc : C.inclusion ≫ e.hom = (Iso.refl _).hom ≫ V.inclusion := by
    change C.inclusion ≫ e.hom = 𝟙 C.group ≫ (C.inclusion ≫ e.hom)
    rw [Category.id_comp]
  have hBV : IsSchemeIntersection {B', V} T' :=
    transport_intersection e t b (Iso.refl C.group) ht hb hc hBC
  obtain ⟨c, hc'⟩ := subgroupIso (same_opposite H hH T' B' V C' hT' hTm' hB' hV hC' hBV hBC')
  have hcomm : C.inclusion ≫ e.hom = c.hom ≫ C'.inclusion := hc'.symm
  refine ⟨c, hcomm, ?_⟩
  intro d hd
  apply Iso.ext
  have := inclusion_mono C'
  exact (cancel_mono C'.inclusion).mp (hd.symm.trans hcomm)

end

end LinearAlgebraicGroups.Arithmetic.QuasiSplitOppositeBorelUniqueness
