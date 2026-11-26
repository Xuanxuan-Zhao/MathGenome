import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.StandardParabolics
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.SchubertClosures
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.DatumAndWeyl
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SimpleRoots
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SchubertClosures
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.StandardParabolicLevi
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Flag.StandardParabolics

open _root_.LinearAlgebraicGroups.Specs
open Specs.AbstractPairing (Datum Root)
open Specs.BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open Specs.BorelProper (IsParabolic)
open Specs.GeometricBorelConjugacy (ConjugatesSubgroups subgroupOfSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics
open Specs.BruhatOrbitParametrization (Cell IsRepresentative)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (pairing)
open Specs.DatumAndWeyl (Identification)
open Specs.GeometricBorelConjugacy (IsBorel IsKBorel)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open Specs.QuotientEmbedding (Presentation)
open Specs.RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf FactorsThrough)
open Specs.SimpleRoots (IsBaseFor evaluate wordProduct wordLength)
open Specs.StandardParabolicLevi (StandardParabolic parabolicWeylGroup)
open Specs.StandardParabolics
open RootPairing (weylGroup)

open private rationalSectionsEquiv labelConjugation inducedConjugation_unique
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.DatumAndWeyl
open private root_determines_coroot from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.AbstractPairing
open private schemeKernel_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private subgroup_trans factor_trans subgroup_normalizes normalizes_iff_sections
  connected_of_reductive
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer

open private subgroupOf_mutual_iso factor_group_through_subgroup
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private factors_of_range_subset from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SubtorusCentralizer
open private exists_field_point from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private multiply_isOpenImmersion group_geometricallyIrreducible
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterOpenCell
open private opposite_point from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private laurentParameter_zpow from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLieWeights
open private exists_shortest_word from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SimpleRoots

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
  {T B : ClosedSubgroup G.val} [IsCommMonObj T.group.X]

private theorem exists_representative_label {D : Datum T} (W : Identification D)
    (n : 𝟙_ (SchemeOver k) ⟶ W.normalizer.group.X) :
    ∃ w, IsRepresentative W w n := by
  obtain ⟨e, he⟩ := rationalSectionsEquiv W.image.constantGroup
  refine ⟨W.labelEquiv.symm (e.symm (n ≫ W.quotient.hom.hom)), ?_⟩
  simp only [IsRepresentative, MulEquiv.apply_symm_apply, ← he]

private theorem same_label_action {D E : Datum T} (W : Identification D) (V : Identification E)
    {w v} {n : 𝟙_ (SchemeOver k) ⟶ W.normalizer.group.X}
    {m : 𝟙_ (SchemeOver k) ⟶ V.normalizer.group.X}
    (hn : IsRepresentative W w n) (hm : IsRepresentative V v m)
    (h : n ≫ W.normalizer.inclusion.hom.hom = m ≫ V.normalizer.inclusion.hom.hom) :
    (W.labelEquiv w).val = (V.labelEquiv v).val := by
  have h₁ := labelConjugation W.image (W.labelEquiv w) n hn
  have h₂ := labelConjugation V.image (V.labelEquiv v) m hm
  rw [← h] at h₂
  have he := inducedConjugation_unique h₁ h₂
  ext χ
  rw [W.image.characterAction, V.image.characterAction, he]

private theorem transport_representative {D E : Datum T} (W : Identification D)
    (V : Identification E) {w} {n : 𝟙_ (SchemeOver k) ⟶ W.normalizer.group.X}
    (hn : IsRepresentative W w n) :
    ∃ (v : E.rootDatum.weylGroup) (m : 𝟙_ (SchemeOver k) ⟶ V.normalizer.group.X),
      IsRepresentative V v m ∧
        n ≫ W.normalizer.inclusion.hom.hom = m ≫ V.normalizer.inclusion.hom.hom ∧
        (W.labelEquiv w).val = (V.labelEquiv v).val := by
  let g := n ≫ W.normalizer.inclusion.hom.hom
  have hg := (W.representsNormalizer _ g).mpr ⟨n, rfl⟩
  obtain ⟨m, hm⟩ := (V.representsNormalizer _ g).mp hg
  obtain ⟨v, hv⟩ := exists_representative_label V m
  exact ⟨v, m, hv, hm.symm, same_label_action W V hn hv hm.symm⟩

private theorem datum_eq {D E : Datum T} (W : Identification D) (V : Identification E)
    (hV : ∀ v, ∃ m, IsRepresentative V v m) : D = E := by
  have hpair : D.rootDatum.toLinearMap = E.rootDatum.toLinearMap := by
    ext x y
    exact (D.pairing_eq (Additive.toMul x) (Additive.toMul y)).trans
      (E.pairing_eq (Additive.toMul x) (Additive.toMul y)).symm
  have hroot : D.rootDatum.root = E.rootDatum.root :=
    Function.Embedding.ext fun i ↦ (D.root_eq i).trans (E.root_eq i).symm
  have hcoroot : D.rootDatum.coroot = E.rootDatum.coroot := by
    apply Function.Embedding.ext
    intro i
    -- Compare both reflections inside the first finite Weyl group.
    obtain ⟨m, hm⟩ := hV (weylGroup.ofIdx E.rootDatum i)
    obtain ⟨v, _, _, _, hl⟩ := transport_representative V W hm
    letI : Finite W.image.labels := W.image.finite
    letI : Finite D.rootDatum.weylGroup := Finite.of_injective _ W.labelEquiv.injective
    letI := D.freeCharacters
    let ρ := (RootPairing.Equiv.weightHom D.rootDatum).comp D.rootDatum.weylGroup.subtype
    apply root_determines_coroot ρ D.rootDatum.toLinearMap
      (s := weylGroup.ofIdx D.rootDatum i) (t := v)
    · exact D.rootDatum.root_coroot_two i
    · rw [hpair, hroot]
      exact E.rootDatum.root_coroot_two i
    · exact D.rootDatum.reflection_apply i
    · intro x
      have hv : v.val.weightEquiv x = E.rootDatum.reflection i x := by
        change v.val.weightEquiv (Additive.ofMul (Additive.toMul x)) =
          (weylGroup.ofIdx E.rootDatum i).val.weightEquiv (Additive.ofMul (Additive.toMul x))
        rw [W.characterAction, V.characterAction, hl]
      change v.val.weightEquiv x =
        x - D.rootDatum.toLinearMap x (E.rootDatum.coroot i) • D.rootDatum.root i
      rw [hv, hpair, hroot]
      rfl
  letI := D.finiteRoots
  have hdata : D.rootDatum = E.rootDatum := by
    apply RootPairing.ext hpair hroot
    rw [hcoroot]
  cases D
  cases E
  cases hdata
  rfl

private theorem base_eq {D : Datum T} {c d : Cocharacter T.group} {b b' : D.rootDatum.Base}
    (hc : positiveRoots T c = subgroupRoots T B) (hd : positiveRoots T d = subgroupRoots T B)
    (hb : IsBaseFor D.rootDatum (evaluate D c) b)
    (hb' : IsBaseFor D.rootDatum (evaluate D d) b') : b = b' := by
  have pos (e : Cocharacter T.group) :
      Specs.SimpleRoots.positive D.rootDatum (evaluate D e) = positiveRoots T e := by
    ext i
    change 0 < D.rootDatum.toLinearMap (D.rootDatum.root i) (Additive.ofMul e) ↔
      0 < pairing T.group i.val e
    rw [D.root_eq, D.pairing_eq]
  have hp := (pos c).trans (hc.trans (hd.symm.trans (pos d).symm))
  have h : b.support = b'.support := by
    ext i
    rw [hb.simple_iff, hb'.simple_iff, hp]
  cases b
  cases b'
  cases h
  rfl

private theorem sections_precompose {H : ClosedSubgroup G.val} {X Y : SchemeOver k}
    (f : X ⟶ Y) {g : Y ⟶ G.val.X} (hg : FactorsThrough H g) :
    FactorsThrough H (f ≫ g) := by
  obtain ⟨a, ha⟩ := hg
  change a ≫ H.inclusion.hom.hom = g at ha
  refine ⟨f ≫ a, ?_⟩
  change (f ≫ a) ≫ H.inclusion.hom.hom = f ≫ g
  rw [Category.assoc, ha]

private theorem representative_membership {D : Datum T} (W : Identification D)
    {H : ClosedSubgroup G.val} (hTH : IsSubgroupOf T H) {w}
    {n m : 𝟙_ (SchemeOver k) ⟶ W.normalizer.group.X}
    (hn : IsRepresentative W w n) (hm : IsRepresentative W w m) :
    FactorsThrough H (n ≫ W.normalizer.inclusion.hom.hom) ↔
      FactorsThrough H (m ≫ W.normalizer.inclusion.hom.hom) := by
  have hq : n ≫ W.quotient.hom.hom = m ≫ W.quotient.hom.hom := by
    unfold IsRepresentative at hn hm
    exact hn.trans hm.symm
  have he : (n⁻¹ * m) ≫ W.quotient.hom.hom = 1 := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hq, inv_mul_cancel]
  obtain ⟨t, ht⟩ := (schemeKernel_sections W.isQuotient.1 (n⁻¹ * m)).mpr he
  change t ≫ W.torusInclusion.hom.hom = n⁻¹ * m at ht
  have ht' : t ≫ T.inclusion.hom.hom =
      (n ≫ W.normalizer.inclusion.hom.hom)⁻¹ * (m ≫ W.normalizer.inclusion.hom.hom) := by
    rw [← W.inclusion_eq]
    change t ≫ W.torusInclusion.hom.hom ≫ W.normalizer.inclusion.hom.hom = _
    rw [← Category.assoc, ht, MonObj.mul_comp, GrpObj.inv_comp]
  have hh := factor_trans (B := T) ⟨t, ht'⟩ hTH
  let a := n ≫ W.normalizer.inclusion.hom.hom
  let b := m ≫ W.normalizer.inclusion.hom.hom
  change a⁻¹ * b ∈ SubgroupSections H _ at hh
  change a ∈ SubgroupSections H _ ↔ b ∈ SubgroupSections H _
  constructor
  · intro ha
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using (SubgroupSections H _).mul_mem ha hh
  · intro hb
    have h := (SubgroupSections H _).mul_mem hb ((SubgroupSections H _).inv_mem hh)
    convert h using 1
    group

omit [IsCommMonObj T.group.X] in
private theorem double_cell_range_eq {Q : Presentation B}
    {a a' : ModObj G.val.X Q.scheme} {g g' : 𝟙_ (SchemeOver k) ⟶ G.val.X}
    {A A' : ClosedSubgroup G.val} (C : Cell (T := T) Q a g A)
    (C' : Cell (T := T) Q a' g' A') (h : g = g') :
    Set.range C.doubleOrbitInclusion.left = Set.range C'.doubleOrbitInclusion.left := by
  subst g'
  have incl {a₁ a₂ : ModObj G.val.X Q.scheme} {A₁ A₂ : ClosedSubgroup G.val}
      (C₁ : Cell (T := T) Q a₁ g A₁) (C₂ : Cell (T := T) Q a₂ g A₂) :
      Set.range C₁.doubleOrbitInclusion.left ⊆ Set.range C₂.doubleOrbitInclusion.left := by
    obtain ⟨f, hf⟩ := (C₂.doubleOrbitSections _ _).mpr
      ((C₁.doubleOrbitSections _ _).mp ⟨𝟙 _, Category.id_comp _⟩)
    rintro _ ⟨x, rfl⟩
    exact ⟨f.left x, congrArg (fun p : C₁.doubleOrbit ⟶ G.val.X ↦ p.left x) hf⟩
  exact Set.Subset.antisymm (incl C C') (incl C' C)

omit [IsCommMonObj T.group.X] in
private theorem cell_range_subset {Q : Presentation B}
    {a : ModObj G.val.X Q.scheme} {g : 𝟙_ (SchemeOver k) ⟶ G.val.X}
    {A H : ClosedSubgroup G.val} (C : Cell (T := T) Q a g A)
    (hBH : IsSubgroupOf B H) (hg : FactorsThrough H g) :
    Set.range C.doubleOrbitInclusion.left ⊆ Set.range H.inclusion.hom.hom.left := by
  obtain ⟨b₁, b₂, hb⟩ := (C.doubleOrbitSections _ _).mp ⟨𝟙 _, Category.id_comp _⟩
  have h₁ : b₁ ≫ B.inclusion.hom.hom ∈ SubgroupSections H _ := factor_trans ⟨b₁, rfl⟩ hBH
  have h₂ : b₂ ≫ B.inclusion.hom.hom ∈ SubgroupSections H _ := factor_trans ⟨b₂, rfl⟩ hBH
  obtain ⟨z, hz⟩ := (SubgroupSections H _).mul_mem
    ((SubgroupSections H _).mul_mem h₁ (sections_precompose _ hg)) h₂
  have he : z ≫ H.inclusion.hom.hom = C.doubleOrbitInclusion := hz.trans hb
  rintro _ ⟨x, rfl⟩
  exact ⟨z.left x, congrArg (fun p : C.doubleOrbit ⟶ G.val.X ↦ p.left x) he⟩

omit [IsCommMonObj T.group.X] in
private theorem cell_meets_subgroup {Q : Presentation B}
    {a : ModObj G.val.X Q.scheme} {g : 𝟙_ (SchemeOver k) ⟶ G.val.X}
    {A H : ClosedSubgroup G.val} (C : Cell (T := T) Q a g A)
    (hBH : IsSubgroupOf B H) (x : C.doubleOrbit.left)
    (hx : C.doubleOrbitInclusion.left x ∈ Set.range H.inclusion.hom.hom.left) :
    FactorsThrough H g := by
  obtain ⟨K, _, _, p, hp⟩ := exists_field_point C.doubleOrbit x
  -- Test the intersection at the residue field of the given point.
  let Y := (testSpec k).obj (Opposite.op (CommAlgCat.of k K))
  change Y ⟶ C.doubleOrbit at p
  letI : IsReduced Y.left := by
    change IsReduced (Spec (CommRingCat.of K))
    infer_instance
  have hpoint : Set.range (p ≫ C.doubleOrbitInclusion).left ⊆
      Set.range H.inclusion.hom.hom.left := by
    rintro _ ⟨z, rfl⟩
    have hz : z = IsLocalRing.closedPoint K := @Subsingleton.elim (Spec (CommRingCat.of K)) _ _ _
    exact (show C.doubleOrbitInclusion.left (p.left z) ∈ _ from by rw [hz, hp]; exact hx)
  obtain ⟨v, hv⟩ := factors_of_range_subset (p ≫ C.doubleOrbitInclusion) _
    H.isClosedImmersion hpoint
  obtain ⟨b₁, b₂, hb⟩ := (C.doubleOrbitSections _ _).mp ⟨p, rfl⟩
  have h₁ : b₁ ≫ B.inclusion.hom.hom ∈ SubgroupSections H Y := factor_trans ⟨b₁, rfl⟩ hBH
  have h₂ : b₂ ≫ B.inclusion.hom.hom ∈ SubgroupSections H Y := factor_trans ⟨b₂, rfl⟩ hBH
  have h : p ≫ C.doubleOrbitInclusion ∈ SubgroupSections H Y := ⟨v, hv⟩
  obtain ⟨z, hz⟩ : toUnit Y ≫ g ∈ SubgroupSections H Y := by
    have hh := (SubgroupSections H Y).mul_mem
      ((SubgroupSections H Y).mul_mem ((SubgroupSections H Y).inv_mem h₁) h)
      ((SubgroupSections H Y).inv_mem h₂)
    convert hh using 1
    rw [← hb]
    group
  letI : IsReduced (𝟙_ (SchemeOver k)).left := by
    change IsReduced (Spec (CommRingCat.of k))
    infer_instance
  apply factors_of_range_subset g _ H.isClosedImmersion
  rintro _ ⟨t, rfl⟩
  let y : Y.left := IsLocalRing.closedPoint K
  have hy : (toUnit Y).left y = t := @Subsingleton.elim (Spec (CommRingCat.of k)) _ _ _
  exact ⟨z.left y, (congrArg (fun f : Y ⟶ G.val.X ↦ f.left y) hz).trans (congrArg g.left hy)⟩

private theorem conjugate_subgroup_le {H A C : ClosedSubgroup G.val}
    (hAH : IsSubgroupOf A H) {g : 𝟙_ (SchemeOver k) ⟶ G.val.X} (hg : Normalizes H.inclusion g)
    (h : ConjugatesSubgroups g A C) : IsSubgroupOf C H := by
  obtain ⟨j, hj⟩ := hAH
  obtain ⟨e, he⟩ := h
  have hf : (e.hom ≫ C.inclusion).hom.hom ∈ SubgroupSections H A.group.X := by
    have h' := ((normalizes_iff_sections H g).mp hg A.group.X (toUnit _) j.hom.hom).1
    change FactorsThrough H ((toUnit A.group.X ≫ g) * (j ≫ H.inclusion).hom.hom *
      (toUnit A.group.X ≫ g)⁻¹) at h'
    rw [hj] at h'
    exact he.symm ▸ h'
  obtain ⟨f, hf⟩ := hf
  obtain ⟨j', hj'⟩ := factor_group_through_subgroup H (e.hom ≫ C.inclusion) f hf
  exact ⟨e.inv ≫ j', by rw [Category.assoc, hj', Iso.inv_hom_id_assoc]⟩

omit [IsCommMonObj T.group.X] in
private theorem opposite_regular {c : Cocharacter T.group}
    (hc : IsRegular T c) : IsRegular T (oppositeCocharacter c) := by
  intro α h
  let R := laurentAlgebra (CommAlgCat.of k k)
  let t := laurentParameter (CommAlgCat.of k k)
  have h₁ := (RootData.CharacterPairing.characterPairingComposition T.group α.val
    (oppositeCocharacter c)).2 R t
  have h₂ := (RootData.CharacterPairing.characterPairingComposition T.group α.val c).2 R t⁻¹
  rw [opposite_point, h, zpow_zero] at h₁
  rw [h₁, inv_zpow] at h₂
  have hv : t ^ pairing T.group α.val c = 1 := by
    apply inv_injective
    apply Units.ext
    exact h₂.symm
  have ht : (LaurentPolynomial.T (pairing T.group α.val c) : LaurentPolynomial k) =
      LaurentPolynomial.T (0 : ℤ) := by
    calc
      _ = (↑(t ^ pairing T.group α.val c) : LaurentPolynomial k) :=
        (laurentParameter_zpow (CommAlgCat.of k k) _).symm
      _ = 1 := congrArg (fun u : Rˣ ↦ (u : R)) hv
      _ = _ := LaurentPolynomial.T_zero.symm
  apply hc α
  by_contra hn
  have hz := congrArg (fun f : LaurentPolynomial k ↦ f.coeff 0) ht
  exact (zero_ne_one : (0 : k) ≠ 1) (by simpa only [LaurentPolynomial.T_apply, hn, ite_false, ite_true] using hz)

private theorem full_support_covers {D : Datum T} (W : Identification D)
    (hG : IsReductive G) (hT : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T)
    (hB : IsKBorel B) (hTB : IsSubgroupOf T B) (H : ClosedSubgroup G.val)
    (hBH : IsSubgroupOf B H)
    (hn : ∀ n : 𝟙_ (SchemeOver k) ⟶ W.normalizer.group.X,
      FactorsThrough H (n ≫ W.normalizer.inclusion.hom.hom)) :
    Set.range H.inclusion.hom.hom.left = Set.univ := by
  obtain ⟨c, L, hc, hBL, -⟩ :=
    (LinearAlgebraicGroups.RootData.BorelsAndChambers.borelsThroughT G hG T hT hm).1 B hB hTB
  let d := c ≫ T.inclusion
  obtain ⟨E⟩ := existsLimitDecomposition G (oppositeCocharacter d)
  have hopp : oppositeCocharacter d = oppositeCocharacter c ≫ T.inclusion :=
    (Category.assoc _ _ _).symm
  have hE := LinearAlgebraicGroups.RootData.BorelsAndChambers.regularCocharacterBorel
    G hG T hT hm (oppositeCocharacter c) (opposite_regular hc) (hopp ▸ E)
  obtain ⟨g, hg, hconj, -⟩ :=
    (LinearAlgebraicGroups.RootData.BorelNormalizer.weylSimplyTransitiveOnBorels
      G hG T hT hm).2 B E.parabolic hB hE.2.1 hTB hE.2.2.1
  obtain ⟨n, hn'⟩ := (W.representsNormalizer _ _).mp hg
  have hgH : FactorsThrough H g := hn' ▸ hn n
  have hEH := conjugate_subgroup_le hBH (subgroup_normalizes H hgH) hconj
  have h₁ : FactorsThrough H E.contracting.inclusion.hom.hom :=
    factor_trans ⟨E.contractingToParabolic.hom.hom,
      congrArg (fun f : E.contracting.group ⟶ G.val ↦ f.hom.hom) E.contracting_in_G⟩ hEH
  obtain ⟨a, ha⟩ := subgroup_trans hBL.2 hBH
  have h₂ : FactorsThrough H L.parabolic.inclusion.hom.hom :=
    ⟨a.hom.hom, congrArg (fun f : L.parabolic.group ⟶ G.val ↦ f.hom.hom) ha⟩
  let m := multiplyFactors E.contracting.inclusion L.parabolic.inclusion
  letI := hG.1
  letI := connected_of_reductive G hG
  letI := group_geometricallyIrreducible G
  letI : IrreducibleSpace G.val.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton G.val.X.hom
  letI : IsOpenImmersion m.left := multiply_isOpenImmersion G d L E
  have hd : Dense (Set.range m.left) :=
    m.left.isOpenEmbedding.isOpen_range.dense ⟨m.left
      ((lift η[E.contracting.group.X] η[L.parabolic.group.X]).left (IsLocalRing.closedPoint k)), _, rfl⟩
  obtain ⟨j, hj⟩ := (SubgroupSections H _).mul_mem
    (sections_precompose (fst _ _) h₁) (sections_precompose (snd _ _) h₂)
  have hj' : j ≫ H.inclusion.hom.hom = m := hj
  letI := H.isClosedImmersion
  apply Set.eq_univ_of_univ_subset
  rw [← hd.closure_eq]
  apply closure_minimal _ H.inclusion.hom.hom.left.isClosedEmbedding.isClosed_range
  rintro _ ⟨x, rfl⟩
  exact ⟨j.left x, congrArg (fun f : _ ⟶ G.val.X ↦ f.left x) hj'⟩

private theorem indices_subgroup {D : Datum T} (W : Identification D)
    {H : ClosedSubgroup G.val} (hTH : IsSubgroupOf T H)
    (n : D.rootDatum.weylGroup → (𝟙_ (SchemeOver k) ⟶ W.normalizer.group.X))
    (hn : ∀ w, IsRepresentative W w (n w)) :
    ∃ S : Subgroup D.rootDatum.weylGroup, ∀ w,
      w ∈ S ↔ FactorsThrough H (n w ≫ W.normalizer.inclusion.hom.hom) := by
  obtain ⟨e, he⟩ := rationalSectionsEquiv W.image.constantGroup
  let mapQ := ((yonedaGrp.map W.quotient).app (Opposite.op (𝟙_ (SchemeOver k)))).hom
  let mapN := ((yonedaGrp.map W.normalizer.inclusion).app (Opposite.op (𝟙_ (SchemeOver k)))).hom
  let f := W.labelEquiv.symm.toMonoidHom.comp (e.symm.toMonoidHom.comp mapQ)
  have hf (w : D.rootDatum.weylGroup) (m : 𝟙_ (SchemeOver k) ⟶ W.normalizer.group.X) :
      f m = w ↔ IsRepresentative W w m := by
    change W.labelEquiv.symm (e.symm (m ≫ W.quotient.hom.hom)) = w ↔ _
    rw [MulEquiv.symm_apply_eq, MulEquiv.symm_apply_eq, he]
    rfl
  refine ⟨((SubgroupSections H _).comap mapN).map f, ?_⟩
  intro w
  constructor
  · rintro ⟨m, hm, hw⟩
    exact (representative_membership W hTH ((hf w m).mp hw) (hn w)).mp hm
  · intro hw
    exact ⟨n w, hw, (hf w _).mpr (hn w)⟩

private theorem simple_in_parabolicWeylGroup {D : Datum T} {b : D.rootDatum.Base}
    {I : Set (Root T)} {c : Cocharacter T.group} (hface : Specs.StandardParabolicLevi.HasFace b I c)
    {i : Root T} (hi : i ∈ b.support) :
    weylGroup.ofIdx D.rootDatum i ∈ parabolicWeylGroup D I ↔ i ∈ I := by
  let f := evaluate D c
  have hf (j : Root T) : f (D.rootDatum.root j) = pairing T.group j.val c := by
    dsimp [f, evaluate]
    rw [D.root_eq, D.pairing_eq]
  let F : Subgroup D.rootDatum.weylGroup :=
    { carrier := {w | ∀ x, f (w.val.weightEquiv x) = f x}
      one_mem' := fun _ ↦ rfl
      mul_mem' := fun ha hb x ↦ (ha _).trans (hb _)
      inv_mem' := by
        intro w hw x
        change f (w.val.weightEquiv.symm x) = f x
        simpa only [LinearEquiv.apply_symm_apply] using (hw (w.val.weightEquiv.symm x)).symm }
  have hF : parabolicWeylGroup D I ≤ F := by
    rw [parabolicWeylGroup, Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩ x
    change f (D.rootDatum.reflection j x) = f x
    rw [D.rootDatum.reflection_apply, map_sub, map_smul, hf, hface.1 j hj, smul_zero, sub_zero]
  constructor
  · intro h
    by_contra hn
    have hp := hface.2 i ⟨hi, hn⟩
    have he := hF h (D.rootDatum.root i)
    change f (D.rootDatum.reflection i (D.rootDatum.root i)) = _ at he
    rw [D.rootDatum.reflection_apply_self, map_neg, hf] at he
    omega
  · intro h
    exact Subgroup.subset_closure ⟨i, h, rfl⟩

private theorem subgroup_of_range {H J : ClosedSubgroup G.val} (hH : Smooth H.group.X.hom)
    (hr : Set.range H.inclusion.hom.hom.left ⊆ Set.range J.inclusion.hom.hom.left) :
    IsSubgroupOf H J := by
  letI := hH
  letI := isReduced_of_smooth_over_field H.group.X.hom
  obtain ⟨z, hz⟩ := factors_of_range_subset H.inclusion.hom.hom J.inclusion.hom.hom
    J.isClosedImmersion hr
  exact factor_group_through_subgroup J H.inclusion z hz

/-- The standard parabolics are determined by their actual torus-normalizer indices. -/
theorem standardParabolicClassification_conditional.{v}
    (schubert : Specs.SchubertClosures.Statement.{v})
    (levi : Specs.StandardParabolicLevi.Statement.{v}) :
    StandardParabolicClassification.{v} := by
  classical
  intro k _ G hG T B hT hm hB hTB
  obtain ⟨h, D, W, U, c, b, hc, hcB, hb, hP⟩ := levi G hG T B hT hm hB hTB
  letI := h
  obtain ⟨h', E, V, d, b', hd, hdB, hb', hV, _, hC⟩ := schubert G hG T B hT hm hB hTB
  have hh : h' = h := Subsingleton.elim _ _
  subst h'
  have hDE := datum_eq W V hV
  subst E
  have hbb := base_eq hcB hdB hb hb'
  subst b'
  choose P hW hQ hcells using fun I : SimpleSubset b ↦ hP I.val I.property
  let Iall : SimpleSubset b := ⟨b.support, Set.Subset.rfl⟩
  let Q := (hQ Iall).some
  choose n hn using hW Iall
  have htransport (w : D.rootDatum.weylGroup) :
      ∃ m : 𝟙_ (SchemeOver k) ⟶ V.normalizer.group.X, IsRepresentative V w m ∧
        m ≫ V.normalizer.inclusion.hom.hom = n w ≫ W.normalizer.inclusion.hom.hom := by
    obtain ⟨v, m, hm, he, hl⟩ := transport_representative W V (hn w)
    have hv : w = v := by
      apply Subtype.ext
      apply RootPairing.Equiv.weightHom_injective D.rootDatum
      apply LinearEquiv.ext
      intro x
      change w.val.weightEquiv (Additive.ofMul (Additive.toMul x)) =
        v.val.weightEquiv (Additive.ofMul (Additive.toMul x))
      rw [W.characterAction, V.characterAction, hl]
    exact ⟨m, hv.symm ▸ hm, he.symm⟩
  choose m hm' hnm using htransport
  obtain ⟨a, _, hCQ⟩ := hC Q
  obtain ⟨A, C', _, _, hclosure⟩ := hCQ m hm'
  let g := fun w ↦ n w ≫ W.normalizer.inclusion.hom.hom
  have cells (I : SimpleSubset b) :
      (∀ w, FactorsThrough (P I).limitGroups.parabolic (g w) ↔ w ∈ parabolicWeylGroup D I.val) ∧
      (⋃ w : parabolicWeylGroup D I.val, Set.range (C' w.val).doubleOrbitInclusion.left) =
        Set.range (P I).limitGroups.parabolic.inclusion.hom.hom.left := by
    obtain ⟨a', A', C, _, hmem, hr⟩ := hcells I Q n hn
    refine ⟨hmem, ?_⟩
    rw [← hr]
    congr 1
    funext w
    exact double_cell_range_eq (C' w.val) (C w.val) (hnm w.val)
  have hindices (I : SimpleSubset b) :
      HasWeylIndices W (P I).limitGroups.parabolic (parabolicWeylGroup D I.val) := by
    intro w r hr
    exact (representative_membership W (subgroup_trans hTB (P I).containsBorel) hr (hn w)).trans
      ((cells I).1 w)
  refine ⟨h, D, W, U, c, b, hc, hcB, hb, hW Iall, P, hindices, ?_⟩
  -- The full-support parabolic contains the opposite open cell and hence covers G.
  have hall : parabolicWeylGroup D Iall.val = ⊤ := by
    unfold parabolicWeylGroup
    rw [← hb.generates]
    congr 1
    ext w
    exact ⟨fun ⟨i, hi, hw⟩ ↦ ⟨⟨i, hi⟩, hw⟩, fun ⟨i, hi⟩ ↦ ⟨i.val, i.property, hi⟩⟩
  have hcover : Set.range (P Iall).limitGroups.parabolic.inclusion.hom.hom.left = Set.univ :=
    full_support_covers W hG hT hm hB hTB _ (P Iall).containsBorel (fun r ↦ by
      obtain ⟨w, hw⟩ := exists_representative_label W r
      exact (hindices Iall w r hw).mpr (by rw [hall]; trivial))
  have hcovers (x : G.val.X.left) :
      ∃ w : D.rootDatum.weylGroup, x ∈ Set.range (C' w).doubleOrbitInclusion.left := by
    have hx : x ∈ Set.range (P Iall).limitGroups.parabolic.inclusion.hom.hom.left := by
      rw [hcover]
      trivial
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp ((cells Iall).2.symm ▸ hx)
    exact ⟨w.val, hw⟩
  intro H hH hBH
  obtain ⟨S, hS⟩ := indices_subgroup W (subgroup_trans hTB hBH) n hn
  let I : SimpleSubset b := ⟨{i | i ∈ b.support ∧ weylGroup.ofIdx D.rootDatum i ∈ S},
    fun _ hi ↦ hi.1⟩
  have hSmem (w : D.rootDatum.weylGroup) :
      w ∈ S ↔ FactorsThrough H (m w ≫ V.normalizer.inclusion.hom.hom) :=
    (hS w).trans (by rw [hnm])
  have hSI : S = parabolicWeylGroup D I.val := by
    apply le_antisymm
    · intro w hw
      obtain ⟨l, hl, hlen, _⟩ := exists_shortest_word D.rootDatum b hb.generates w
      have hred : Specs.GallerySubwords.IsReduced D.rootDatum b l := by
        change wordLength D.rootDatum b (wordProduct D.rootDatum b l) = l.length
        rw [hl, hlen]
      have hrange := cell_range_subset (C' w) hBH ((hSmem w).mp hw)
      have hclos : closure (Set.range (C' w).doubleOrbitInclusion.left) ⊆
          Set.range H.inclusion.hom.hom.left := by
        letI := H.isClosedImmersion
        exact closure_minimal hrange H.inclusion.hom.hom.left.isClosedEmbedding.isClosed_range
      have hv (j : b.support) (hj : j ∈ l) : weylGroup.ofIdx D.rootDatum j.val ∈ parabolicWeylGroup D I.val := by
        let v := weylGroup.ofIdx D.rootDatum j.val
        have hsub : v ∈ Specs.SchubertClosures.subwordProducts D.rootDatum b l :=
          ⟨[j], List.singleton_sublist.mpr hj, by simp [wordProduct, v]⟩
        have hs : Set.range (C' v).doubleOrbitInclusion.left ⊆
            Set.range H.inclusion.hom.hom.left := by
          intro x hx
          apply hclos
          have hcl := (hclosure l hred).2.2
          change Set.range (Specs.SchubertClosures.closureIdeal
            (C' (wordProduct D.rootDatum b l)).doubleOrbitInclusion.left).subschemeι = _ at hcl
          rw [← hl]
          have hx' : x ∈ ⋃ v ∈ Specs.SchubertClosures.subwordProducts D.rootDatum b l,
              Set.range (C' v).doubleOrbitInclusion.left :=
            Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨hsub, hx⟩⟩
          rw [← hcl] at hx'
          simpa only [Specs.SchubertClosures.closureIdeal, Scheme.IdealSheafData.range_subschemeι,
            Scheme.IdealSheafData.coe_support_vanishingIdeal, TopologicalSpace.Closeds.coe_closure] using hx'
        let x : (C' v).doubleOrbit.left :=
          (lift η[(A v).group.X] η[B.group.X] ≫ (C' v).doubleOrbitIso.hom).left
            (IsLocalRing.closedPoint k)
        have hvs : v ∈ S := (hSmem _).mpr (cell_meets_subgroup (C' v) hBH x
          (hs (Set.mem_range_self x)))
        exact Subgroup.subset_closure ⟨j.val, ⟨j.property, hvs⟩, rfl⟩
      rw [← hl]
      change (l.map (fun i : b.support ↦ weylGroup.ofIdx D.rootDatum i.val)).prod ∈ _
      apply Subgroup.list_prod_mem
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      exact hv j hj
    · rw [parabolicWeylGroup, Subgroup.closure_le]
      rintro _ ⟨i, hi, rfl⟩
      exact hi.2
  have hmem (J : SimpleSubset b) :
      HasWeylIndices W H (parabolicWeylGroup D J.val) ↔ S = parabolicWeylGroup D J.val := by
    constructor
    · intro hh
      ext w
      exact (hS w).trans (hh w _ (hn w))
    · intro hh w r hr
      exact (representative_membership W (subgroup_trans hTB hBH) hr (hn w)).trans
        ((hS w).symm.trans (by rw [hh]; rfl))
  have unique (J : SimpleSubset b) (hJ : S = parabolicWeylGroup D J.val) : J = I := by
    apply Subtype.ext
    ext i
    constructor
    · intro hi
      have his := J.property hi
      exact ⟨his, hJ.symm ▸ (simple_in_parabolicWeylGroup (P J).face his).mpr hi⟩
    · rintro ⟨hi, hS'⟩
      exact (simple_in_parabolicWeylGroup (P J).face hi).mp (hJ ▸ hS')
  refine ⟨⟨I, (hmem I).mpr hSI, fun J hJ ↦ unique J ((hmem J).mp hJ)⟩, ?_⟩
  intro J
  constructor
  · intro hJ
    have hr : Set.range H.inclusion.hom.hom.left =
        Set.range (P J).limitGroups.parabolic.inclusion.hom.hom.left := by
      rw [← (cells J).2]
      apply Set.Subset.antisymm
      · rintro x hx
        obtain ⟨w, y, rfl⟩ := hcovers x
        have hw := (hSmem w).mpr (cell_meets_subgroup (C' w) hBH y hx)
        have hw' := (hmem J).mp hJ ▸ hw
        exact Set.mem_iUnion.mpr ⟨⟨w, hw'⟩, y, rfl⟩
      · intro x hx
        obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hx
        exact cell_range_subset (C' w.val) hBH
          ((hSmem _).mp (((hmem J).mp hJ).symm ▸ w.property)) hw
    exact ⟨subgroup_of_range hH.2.1 hr.le, subgroup_of_range (P J).parabolic.2.1 hr.ge⟩
  · intro hSame w r hr
    exact (Iff.intro (fun hp ↦ factor_trans hp hSame.1)
      (fun hp ↦ factor_trans hp hSame.2)).trans (hindices J w r hr)

open private maximal_torus_in_borel split_of_maximal geometricMaximal_of_maximal isKBorel_iff_of_isAlgClosed
  conjugates_of_normalizes conjugates_transport_ambient conjugates_same_target isBorel_of_same
  factors_from_big_cell reductive_geometric subgroup_descend extendSubgroup smooth_extend_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
open private normalizes_of_conjugates_self conjugates_trans conjugates_transport conjugates_in_ambient
  transportSubgroup conjugationIso inclusion_mono
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private borel_transport from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper
open private sectionOfClosedPoint sectionOfClosedPoint_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry

private theorem borel_in_subgroup {P : ClosedSubgroup G.val} (S : ClosedSubgroup P.group)
    (hS : IsBorel (subgroupOfSubgroup P S)) : IsBorel S := by
  refine ⟨hS.1, ?_⟩
  intro A hA hSA
  obtain ⟨a, ha⟩ := hSA
  have hSA' : IsSubgroupOf (subgroupOfSubgroup P S) (subgroupOfSubgroup P A) :=
    ⟨a, by change a ≫ A.inclusion ≫ P.inclusion = S.inclusion ≫ P.inclusion
           rw [← Category.assoc, ha]⟩
  obtain ⟨f, hf⟩ := hS.2 _ hA hSA'
  letI := inclusion_mono P
  refine ⟨f, (cancel_mono P.inclusion).mp ?_⟩
  change f ≫ S.inclusion ≫ P.inclusion = A.inclusion ≫ P.inclusion at hf
  simpa only [Category.assoc] using hf

private theorem rational_parabolic_normalizer_factors [IsAlgClosed k] (hG : IsReductive G)
    (P B : ClosedSubgroup G.val) (hP : Smooth P.group.X.hom)
    (hconn : ConnectedSpace P.group.X.left) (hB : IsBorel B) (hBP : IsSubgroupOf B P)
    (g : 𝟙_ (SchemeOver k) ⟶ G.val.X) (hg : Normalizes P.inclusion g) :
    FactorsThrough P g := by
  obtain ⟨j, hj⟩ := hBP
  have hjc : IsClosedImmersion j.hom.hom.left := by
    letI := P.isClosedImmersion
    haveI : IsClosedImmersion (j.hom.hom.left ≫ P.inclusion.hom.hom.left) := by
      change IsClosedImmersion (j ≫ P.inclusion).hom.hom.left
      rw [hj]
      exact B.isClosedImmersion
    exact IsClosedImmersion.of_comp_isClosedImmersion _ P.inclusion.hom.hom.left
  let S : ClosedSubgroup P.group := ⟨B.group, j, hjc⟩
  have hS : SameSubgroup B (subgroupOfSubgroup P S) :=
    ⟨⟨𝟙 _, (Category.id_comp _).trans hj⟩, ⟨𝟙 _, (Category.id_comp _).trans hj.symm⟩⟩
  obtain ⟨e, he⟩ := conjugates_of_normalizes P hg
  let S' := transportSubgroup e S
  have hconj : ConjugatesSubgroups g (subgroupOfSubgroup P S) (subgroupOfSubgroup P S') :=
    conjugates_transport e he S
  have hSg : IsBorel (transportSubgroup (conjugationIso g) (subgroupOfSubgroup P S)) :=
    borel_transport (isBorel_of_same hS hB) (conjugationIso g)
  have hS' : IsBorel (subgroupOfSubgroup P S') :=
    isBorel_of_same
      (conjugates_same_target (conjugates_transport_ambient (subgroupOfSubgroup P S) g) hconj) hSg
  obtain ⟨b, hb⟩ := LinearAlgebraicGroups.GeometricBorelConjugacy.borelsConjugate
    (closedSubgroupAlgebraicGroup P) hP hconn S' S
    (borel_in_subgroup S' hS') (borel_in_subgroup S (isBorel_of_same hS hB))
  let t := b ≫ P.inclusion.hom.hom
  have hb' : ConjugatesSubgroups (t * g) (subgroupOfSubgroup P S) (subgroupOfSubgroup P S) :=
    conjugates_trans hconj (conjugates_in_ambient P hb)
  have hn : Normalizes (subgroupOfSubgroup P S).inclusion (t * g) :=
    normalizes_of_conjugates_self _ hb'
  change Normalizes (j ≫ P.inclusion) (t * g) at hn
  rw [hj] at hn
  have htg := (LinearAlgebraicGroups.RootData.BorelNormalizer.groundFieldBorelNormalizer G hG B
    ((isKBorel_iff_of_isAlgClosed G B).mpr hB) _ _).mp hn
  have ht : t ∈ SubgroupSections P _ := ⟨b, rfl⟩
  have hh : t * g ∈ SubgroupSections P _ := factor_trans htg ⟨j, hj⟩
  have h := (SubgroupSections P _).mul_mem ((SubgroupSections P _).inv_mem ht) hh
  change g ∈ SubgroupSections P (𝟙_ (SchemeOver k))
  simpa only [← mul_assoc, inv_mul_cancel, one_mul] using h

/-- A geometric parabolic represents its own scheme normalizer. -/
theorem geometricParabolicNormalizer_conditional.{v}
    (schubert : Specs.SchubertClosures.Statement.{v})
    (levi : Specs.StandardParabolicLevi.Statement.{v}) :
    GeometricParabolicNormalizer.{v} := by
  intro k _ _ G hG P hP h
  obtain ⟨B, hB, hBP⟩ := h
  obtain ⟨S, _, hT⟩ := maximal_torus_in_borel G hG B hB
  let T := subgroupOfSubgroup B S
  have hTB : IsSubgroupOf T B := ⟨S.inclusion, rfl⟩
  have hTP := subgroup_trans hTB hBP
  have hP' : IsParabolic G P := by
    refine ⟨hG, hP, ?_⟩
    obtain ⟨hBc, hBc'⟩ := (isKBorel_iff_of_isAlgClosed G B).mpr hB
    refine ⟨baseChangeClosedSubgroup k (AlgebraicClosure k) P.inclusion P.isClosedImmersion,
      Specs.GeometricRadicals.baseChangedSubgroup (AlgebraicClosure k) B hBc, hBc', ?_⟩
    obtain ⟨i, hi⟩ := hBP
    exact ⟨(groupBaseChange k (AlgebraicClosure k)).map i, by
      change _ ≫ (groupBaseChange k (AlgebraicClosure k)).map P.inclusion = _
      rw [← Functor.map_comp, hi]
      rfl⟩
  obtain ⟨_, D, W, U, c, b, _, _, _, _, J, _, hJ⟩ :=
    standardParabolicClassification_conditional schubert levi G hG T B (split_of_maximal hT)
      (geometricMaximal_of_maximal G T hT) ((isKBorel_iff_of_isAlgClosed G B).mpr hB) hTB
  obtain ⟨⟨I, hI, _⟩, hchar⟩ := hJ P hP' hBP
  have hsame := (hchar I).mp hI
  letI := hG.1
  letI := connected_of_reductive G hG
  let cochar := (J I).cocharacter
  let L := (J I).limitGroups
  obtain ⟨E⟩ := existsLimitDecomposition G (oppositeCocharacter (cochar ≫ T.inclusion))
  obtain ⟨e, he⟩ := subgroupOf_mutual_iso hsame.1 hsame.2
  have hconn : ConnectedSpace P.group.X.left := by
    letI := (geometricallyConnectedLimitSubgroups G (cochar ≫ T.inclusion) L).1
    let i := (Grp.forget (SchemeOver k) ⋙ Over.forget _).mapIso e
    exact i.hom.homeomorph.connectedSpace_iff.mpr
      (GeometricallyConnected.connectedSpace_of_subsingleton L.parabolic.group.X.hom)
  let m := multiplyFactors E.contracting.inclusion P.inclusion
  haveI : IsOpenImmersion m.left := by
    let a : P.group.X ⟶ L.parabolic.group.X := e.hom.hom.hom
    let l := lift (fst E.contracting.group.X P.group.X) (snd _ _ ≫ a)
    have he' : a ≫ L.parabolic.inclusion.hom.hom = P.inclusion.hom.hom :=
      congrArg (fun f : P.group ⟶ G.val ↦ f.hom.hom) he
    have hl : m = l ≫ multiplyFactors E.contracting.inclusion L.parabolic.inclusion := by
      simp only [m, l, multiplyFactors, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, Category.assoc, he']
    rw [hl, Over.comp_left]
    haveI : IsOpenImmersion (multiplyFactors E.contracting.inclusion L.parabolic.inclusion).left :=
      multiply_isOpenImmersion G (cochar ≫ T.inclusion) L E
    haveI : IsIso a := (Grp.forget (SchemeOver k)).map_isIso e.hom
    haveI : IsIso l := by
      change IsIso (E.contracting.group.X ◁ a)
      infer_instance
    haveI : IsIso l.left := (Over.forget _).map_isIso l
    infer_instance
  obtain ⟨N, hN⟩ := normalizerScheme k G P
  -- Closed points put the normalizer inside the open cell. Its contracting
  -- factor can then be tested over arbitrary algebras.
  have hNP : FactorsThrough P N.inclusion.hom.hom := by
    let V : Set N.group.X.left := N.inclusion.hom.hom.left ⁻¹' Set.range m.left
    have hV : IsOpen V := m.left.isOpenEmbedding.isOpen_range.preimage N.inclusion.hom.hom.left.continuous
    letI : LocallyOfFiniteType N.group.X.hom := (closedSubgroupAlgebraicGroup N).property.2.1
    letI : JacobsonSpace N.group.X.left := LocallyOfFiniteType.jacobsonSpace N.group.X.hom
    have hclosed : closedPoints N.group.X.left ⊆ V := by
      intro x hx
      let p := sectionOfClosedPoint N.group.X x hx
      have hn := (hN _ (p ≫ N.inclusion.hom.hom)).mpr ⟨p, rfl⟩
      obtain ⟨r, hr⟩ := rational_parabolic_normalizer_factors hG P B hP hconn hB hBP _ hn
      change r ≫ P.inclusion.hom.hom = p ≫ N.inclusion.hom.hom at hr
      have hh : lift (1 : 𝟙_ (SchemeOver k) ⟶ E.contracting.group.X) r ≫ m =
          p ≫ N.inclusion.hom.hom := by
        simp only [m, multiplyFactors, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, hr,
          MonObj.one_comp, one_mul]
      refine ⟨(lift (1 : 𝟙_ (SchemeOver k) ⟶ E.contracting.group.X) r).left (IsLocalRing.closedPoint k), ?_⟩
      have hh' := congrArg (fun f : 𝟙_ (SchemeOver k) ⟶ G.val.X ↦ f.left (IsLocalRing.closedPoint k)) hh
      simpa only [Over.comp_left, Scheme.Hom.comp_apply, p, sectionOfClosedPoint_apply] using hh'
    have hVall : V = Set.univ := by
      by_contra h
      obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints
        (Z := Vᶜ) (Set.nonempty_compl.mpr h) hV.isClosed_compl.isLocallyClosed
      exact hx (hclosed hxc)
    have hrange : Set.range N.inclusion.hom.hom.left ⊆ Set.range m.left := by
      rintro x ⟨y, rfl⟩
      change y ∈ V
      rw [hVall]
      trivial
    let l := IsOpenImmersion.lift m.left N.inclusion.hom.hom.left hrange
    have hl : l ≫ m.left = N.inclusion.hom.hom.left := IsOpenImmersion.lift_fac _ _ _
    let p : N.group.X ⟶ E.contracting.group.X ⊗ P.group.X := Over.homMk l (by
      rw [← Over.w m, ← Category.assoc, hl, Over.w])
    have hcomp : p ≫ m = N.inclusion.hom.hom := Over.OverMorphism.ext hl
    rw [← hcomp]
    exact factors_from_big_cell G P T hTP cochar E p
      (hcomp.symm ▸ (hN _ _).mpr ⟨𝟙 _, Category.id_comp _⟩)
  obtain ⟨f, hf⟩ := hNP
  have hsub := factor_group_through_subgroup P N.inclusion f hf
  intro X g
  exact ⟨fun h ↦ factor_trans ((hN X g).mp h) hsub, subgroup_normalizes P⟩

/-- The geometric scheme normalizer equality descends to the ground field. -/
theorem groundFieldParabolicNormalizer_conditional.{v}
    (schubert : Specs.SchubertClosures.Statement.{v})
    (levi : Specs.StandardParabolicLevi.Statement.{v}) :
    GroundFieldParabolicNormalizer.{v} := by
  intro k _ G P hP
  let K := AlgebraicClosure k
  obtain ⟨N, hN⟩ := normalizerScheme k G P
  obtain ⟨_, hNK : RepresentsSubgroup (extendSubgroup K N) (fun _ g ↦
    Normalizes (extendSubgroup K P).inclusion g)⟩ :=
    normalizerSchemeBaseChange k K P.inclusion N P.isClosedImmersion hN
  obtain ⟨_, B, hB, hBP⟩ := hP.2.2
  have hgeom := geometricParabolicNormalizer_conditional schubert levi
    (Specs.GeometricRadicals.GeometricGroup G) (reductive_geometric G hP.1) (extendSubgroup K P)
    ((smooth_extend_iff K P.group.X).mpr hP.2.1) ⟨B, hB, hBP⟩
  have hN' : IsSubgroupOf (extendSubgroup K N) (extendSubgroup K P) := by
    obtain ⟨f, hf⟩ := (hgeom _ _).mp ((hNK _ _).mpr ⟨𝟙 _, Category.id_comp _⟩)
    exact factor_group_through_subgroup _ _ f hf
  intro X g
  exact ⟨fun h ↦ factor_trans ((hN X g).mp h) (subgroup_descend K hN'), subgroup_normalizes P⟩

end

end LinearAlgebraicGroups.Flag.StandardParabolics

universe v8_closure_072746863f5df45a_u0
theorem _root_.«LinearAlgebraicGroups».«Flag».«StandardParabolics».«geometricParabolicNormalizer» : _root_.«LinearAlgebraicGroups».«Specs».«StandardParabolics».«GeometricParabolicNormalizer».{v8_closure_072746863f5df45a_u0} :=
  @_root_.«LinearAlgebraicGroups».«Flag».«StandardParabolics».«geometricParabolicNormalizer_conditional».{v8_closure_072746863f5df45a_u0} (@_root_.«LinearAlgebraicGroups».«Flag».«SchubertClosures».«schubertClosures».{v8_closure_072746863f5df45a_u0}) (@_root_.«LinearAlgebraicGroups».«Flag».«StandardParabolicLevi».«standardParabolicLevi».{v8_closure_072746863f5df45a_u0})
theorem _root_.«LinearAlgebraicGroups».«Flag».«StandardParabolics».«groundFieldParabolicNormalizer» : _root_.«LinearAlgebraicGroups».«Specs».«StandardParabolics».«GroundFieldParabolicNormalizer».{v8_closure_072746863f5df45a_u0} :=
  @_root_.«LinearAlgebraicGroups».«Flag».«StandardParabolics».«groundFieldParabolicNormalizer_conditional».{v8_closure_072746863f5df45a_u0} (@_root_.«LinearAlgebraicGroups».«Flag».«SchubertClosures».«schubertClosures».{v8_closure_072746863f5df45a_u0}) (@_root_.«LinearAlgebraicGroups».«Flag».«StandardParabolicLevi».«standardParabolicLevi».{v8_closure_072746863f5df45a_u0})
theorem _root_.«LinearAlgebraicGroups».«Flag».«StandardParabolics».«standardParabolicClassification» : _root_.«LinearAlgebraicGroups».«Specs».«StandardParabolics».«StandardParabolicClassification».{v8_closure_072746863f5df45a_u0} :=
  @_root_.«LinearAlgebraicGroups».«Flag».«StandardParabolics».«standardParabolicClassification_conditional».{v8_closure_072746863f5df45a_u0} (@_root_.«LinearAlgebraicGroups».«Flag».«SchubertClosures».«schubertClosures».{v8_closure_072746863f5df45a_u0}) (@_root_.«LinearAlgebraicGroups».«Flag».«StandardParabolicLevi».«standardParabolicLevi».{v8_closure_072746863f5df45a_u0})
