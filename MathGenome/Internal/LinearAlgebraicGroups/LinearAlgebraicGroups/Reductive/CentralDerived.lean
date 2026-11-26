import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CentralDerived
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SchemeCentre
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralTorus
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.Finiteness.Finsupp
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SchemeCentre
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Topology TopologicalSpace
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Reductive.CentralDerived

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open _root_.LinearAlgebraicGroups.Specs
open Specs.CentralDerived
open Specs.CentralTorus (IsSchemeCentre IsLargestTorus)
open Specs.GeometricRadicals (IsReductive IsSemisimple IsTorus GeometricGroup baseChangedSubgroup)
open Specs.SchemeDerivedGroup (IsDerivedSubgroup IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup baseChangedAlgebraicGroup)
open Specs.SchemeCentre (CentreFormula)

theorem centralTorusExists_conditional :
    CentreFormula.{u} →
    CentralTorusExists.{u} := by
  intro _ k _ G hG
  obtain ⟨Z, hZ, _⟩ := LinearAlgebraicGroups.CentralTorus.centreMultiplicativeType G hG
  obtain ⟨T, hT, hbase⟩ := LinearAlgebraicGroups.CentralTorus.largestCentralTorus G hG Z hZ
  exact ⟨Z, hZ, T, hT, hbase⟩

open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private commute_from_centre from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralTorus
open private schemeKernel_exists schemeKernel_sections isMonHom_of_comp_closed
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient

variable {k : Type u} [Field k]

private theorem homOfSectionLaws {A B : GroupScheme k} (f : A.X ⟶ B.X)
    (hone : ∀ Y : SchemeOver k, (1 : Y ⟶ A.X) ≫ f = 1)
    (hmul : ∀ (Y : SchemeOver k) (x y : Y ⟶ A.X),
      (x * y) ≫ f = (x ≫ f) * (y ≫ f)) :
    IsMonHom f := by
  constructor
  · simpa only [MonObj.one_eq_one, toUnit_unit, Category.id_comp] using
      hone (𝟙_ (SchemeOver k))
  · simpa only [Hom.mul_def, ← lift_map_assoc, lift_fst_snd, Category.id_comp] using
      hmul _ (fst A.X A.X) (snd A.X A.X)

private theorem postMul {A B : GroupScheme k} (f : A ⟶ B) {Y : SchemeOver k}
    (x y : Y ⟶ A.X) :
    (x * y) ≫ f.hom.hom = (x ≫ f.hom.hom) * (y ≫ f.hom.hom) :=
  (IsMonHom.monoidHom f.hom.hom Y).map_mul x y

private theorem postInv {A B : GroupScheme k} (f : A ⟶ B) {Y : SchemeOver k}
    (x : Y ⟶ A.X) :
    x⁻¹ ≫ f.hom.hom = (x ≫ f.hom.hom)⁻¹ :=
  map_inv (IsMonHom.monoidHom f.hom.hom Y) x

private theorem mulMap {A B G : GroupScheme k} (a : A ⟶ G) (b : B ⟶ G)
    (ha : Centralizes (𝟙 G) a.hom.hom) :
    ∃ m : (A ⊗ B) ⟶ G,
      m.hom.hom = (fst A B ≫ a).hom.hom * (snd A B ≫ b).hom.hom := by
  let P : GroupScheme k := A ⊗ B
  let f : P ⟶ G := fst A B ≫ a
  let g : P ⟶ G := snd A B ≫ b
  let v : P.X ⟶ G.X := f.hom.hom * g.hom.hom
  have hv := homOfSectionLaws (A := P) (B := G) v
    (fun Y ↦ by simp [v, MonObj.comp_mul]) (fun Y x y ↦ by
      simp only [v, MonObj.comp_mul, postMul]
      have hc : Commute (y ≫ f.hom.hom) (x ≫ g.hom.hom) := by
        change Commute (y ≫ fst A.X B.X ≫ a.hom.hom) (x ≫ g.hom.hom)
        simpa only [Category.assoc] using
          commute_from_centre ha (y ≫ fst A.X B.X) (x ≫ g.hom.hom)
      let xf := x ≫ f.hom.hom
      let yf := y ≫ f.hom.hom
      let xg := x ≫ g.hom.hom
      let yg := y ≫ g.hom.hom
      change (xf * yf) * (xg * yg) = (xf * xg) * (yf * yg)
      calc
        _ = xf * ((yf * xg) * yg) := by simp only [mul_assoc]
        _ = xf * ((xg * yf) * yg) := congrArg (fun z ↦ xf * (z * yg)) hc.eq
        _ = _ := by simp only [mul_assoc])
  exact ⟨Grp.homMk'' v hv.1 hv.2, rfl⟩

private theorem inverseMap {A B G : GroupScheme k} (q : A ⟶ B) (i : B ⟶ G)
    (hi : IsClosedImmersion i.hom.hom.left)
    (hq : Centralizes (𝟙 G) (q ≫ i).hom.hom) :
    ∃ f : A ⟶ B, f.hom.hom = q.hom.hom⁻¹ := by
  letI := hi
  letI : Mono i.hom.hom := Over.mono_of_mono_left _
  let f := q.hom.hom⁻¹
  haveI : IsMonHom f := homOfSectionLaws f
    (fun Y ↦ by simp [f, GrpObj.comp_inv]) (fun Y x y ↦ by
      simp only [f, GrpObj.comp_inv, postMul, mul_inv_rev]
      apply (cancel_mono i.hom.hom).mp
      simp only [postMul, postInv, Category.assoc]
      exact (commute_from_centre hq y (x ≫ q.hom.hom ≫ i.hom.hom)).inv_inv.eq)
  exact ⟨Grp.homMk f, rfl⟩

private theorem centralInclusion {G : GroupScheme k} {Z : ClosedSubgroup G}
    (hZ : IsSchemeCentre Z) (T : ClosedSubgroup Z.group) :
    Centralizes (𝟙 G) (T.inclusion ≫ Z.inclusion).hom.hom :=
  (hZ _ _).mpr ⟨T.inclusion.hom.hom, rfl⟩

private theorem identifyCentralProductKernel {G : AffineAlgebraicGroup k}
    {Z : ClosedSubgroup G.val} (hZ : IsSchemeCentre Z)
    (T : ClosedSubgroup Z.group) (D : ClosedSubgroup G.val)
    (I : GroupScheme k) (p : I ⟶ T.group) (q : I ⟶ D.group)
    (hI : IsPullback p q (T.inclusion ≫ Z.inclusion) D.inclusion) (hfinite : IsFinite I.X.hom)
    (m : (T.group ⊗ D.group) ⟶ G.val) (hm : IsCentralProduct T D m) :
    HasCentralProductKernel m := by
  let a := T.inclusion ≫ Z.inclusion
  let b := D.inclusion
  let P := T.group ⊗ D.group
  let s : P ⟶ T.group := firstProjection _ _
  let t : P ⟶ D.group := secondProjection _ _
  let F := Grp.forget (SchemeOver k)
  letI := G.property.1
  letI := T.isClosedImmersion
  letI := Z.isClosedImmersion
  letI := D.isClosedImmersion
  have ha : IsClosedImmersion a.hom.hom.left := by
    change IsClosedImmersion (T.inclusion.hom.hom.left ≫ Z.inclusion.hom.hom.left)
    infer_instance
  letI := ha
  letI : Mono a.hom.hom := Over.mono_of_mono_left _
  letI : Mono b.hom.hom := Over.mono_of_mono_left _
  have hc := centralInclusion hZ T
  have hqc : Centralizes (𝟙 G.val) (q ≫ b).hom.hom :=
    (hZ _ _).mpr ⟨(p ≫ T.inclusion).hom.hom,
      congrArg F.map hI.w⟩
  obtain ⟨q', hq'⟩ := inverseMap q b D.isClosedImmersion hqc
  let j : I ⟶ P := lift p q'
  have js : j ≫ s = p := lift_fst _ _
  have jt : j ≫ t = q' := lift_snd _ _
  have eval {Y : SchemeOver k} (x : Y ⟶ P.X) :
      x ≫ m.hom.hom =
        (x ≫ s.hom.hom ≫ a.hom.hom) * (x ≫ t.hom.hom ≫ b.hom.hom) := by
    rw [hm, MonObj.comp_mul]
    rfl
  obtain ⟨J, hJ⟩ := schemeKernel_exists m
  have hjm : j.hom.hom ≫ m.hom.hom = 1 := by
    rw [eval]
    change (j ≫ s ≫ a).hom.hom * (j ≫ t ≫ b).hom.hom = 1
    rw [← Category.assoc j s a, js, ← Category.assoc j t b, jt]
    change (p ≫ a).hom.hom * (q'.hom.hom ≫ b.hom.hom) = 1
    rw [hq', postInv, show p ≫ a = q ≫ b from hI.w]
    exact mul_inv_cancel (q ≫ b).hom.hom
  obtain ⟨e₀, he₀⟩ := (schemeKernel_sections hJ j.hom.hom).mpr hjm
  letI := J.isClosedImmersion
  letI : IsMonHom e₀ := isMonHom_of_comp_closed e₀ j J.inclusion he₀
  let e₁ : I ⟶ J.group := Grp.homMk e₀
  have he : e₁ ≫ J.inclusion = j := Grp.hom_ext _ _ he₀
  have he_s : e₁ ≫ J.inclusion ≫ s = p := by rw [← Category.assoc, he, js]
  have he_t : e₁ ≫ J.inclusion ≫ t = q' := by rw [← Category.assoc, he, jt]
  let pJ := J.inclusion ≫ s
  let qJ := J.inclusion ≫ t
  have hpqJ : (pJ ≫ a).hom.hom * (qJ ≫ b).hom.hom = 1 :=
    (eval J.inclusion.hom.hom).symm.trans
      ((schemeKernel_sections hJ J.inclusion.hom.hom).mp ⟨𝟙 _, by
        change 𝟙 _ ≫ J.inclusion.hom.hom = _
        simp⟩)
  have hqJc : Centralizes (𝟙 G.val) (qJ ≫ b).hom.hom := by
    rw [← inv_eq_of_mul_eq_one_right hpqJ]
    apply (centralizes_iff _ _).mpr
    intro Y x y
    rw [GrpObj.comp_inv]
    exact Commute.inv_left_iff.mpr (commute_from_centre hc (x ≫ pJ.hom.hom) y)
  obtain ⟨r, hr⟩ := inverseMap qJ b D.isClosedImmersion hqJc
  have hw : pJ ≫ a = r ≫ b := by
    apply Grp.hom_ext
    change (pJ ≫ a).hom.hom = r.hom.hom ≫ b.hom.hom
    rw [hr, postInv]
    exact mul_eq_one_iff_eq_inv.mp hpqJ
  let e₂ := hI.lift pJ r hw
  have e₂p : e₂ ≫ p = pJ := hI.lift_fst _ _ _
  have e₂q : e₂ ≫ q = r := hI.lift_snd _ _ _
  have er : e₁ ≫ r = q := by
    apply Grp.hom_ext
    change e₁.hom.hom ≫ r.hom.hom = q.hom.hom
    rw [hr, GrpObj.comp_inv, ← Grp.comp_hom_hom, show e₁ ≫ qJ = q' from he_t, hq', inv_inv]
  have hr' : e₂ ≫ q' = qJ := by
    apply Grp.hom_ext
    change e₂.hom.hom ≫ q'.hom.hom = qJ.hom.hom
    rw [hq', GrpObj.comp_inv, ← Grp.comp_hom_hom, e₂q, hr, inv_inv]
  let e : I ≅ J.group := ⟨e₁, e₂, by
    apply hI.hom_ext
    · rw [Category.assoc, e₂p, Category.id_comp]
      exact he_s
    · rw [Category.assoc, e₂q, er, Category.id_comp], by
    haveI : Mono J.inclusion := F.mono_of_mono_map
      (show Mono J.inclusion.hom.hom from Over.mono_of_mono_left _)
    apply (cancel_mono J.inclusion).mp
    apply CartesianMonoidalCategory.hom_ext
    · change ((e₂ ≫ e₁) ≫ J.inclusion) ≫ s = (𝟙 J.group ≫ J.inclusion) ≫ s
      rw [Category.assoc, Category.assoc, he_s, e₂p, Category.id_comp]
    · change ((e₂ ≫ e₁) ≫ J.inclusion) ≫ t = (𝟙 J.group ≫ J.inclusion) ≫ t
      rw [Category.assoc, Category.assoc, he_t, hr', Category.id_comp]⟩
  refine ⟨I, p, q, J, hI, hfinite, e, he_s, ?_, hJ, ?_⟩
  · exact (congrArg F.map he_t).trans hq'
  · intro Y g
    apply (centralizes_iff _ _).mpr
    intro X y x
    let ji : J.group ⟶ P := J.inclusion
    let v : X ⟶ P.X := x ≫ ji.hom.hom
    let w : X ⟶ P.X := y ≫ g
    change Commute w v
    apply Commute.symm
    show v * w = w * v
    have hv₁ : v ≫ s.hom.hom = x ≫ pJ.hom.hom := Category.assoc _ _ _
    have hv₂ : v ≫ t.hom.hom = x ≫ qJ.hom.hom := Category.assoc _ _ _
    apply CartesianMonoidalCategory.hom_ext
    · change (v * w) ≫ s.hom.hom = (w * v) ≫ s.hom.hom
      rw [postMul, postMul, hv₁]
      apply (cancel_mono a.hom.hom).mp
      rw [postMul, postMul, Category.assoc, Category.assoc]
      exact (commute_from_centre hc (x ≫ pJ.hom.hom) (w ≫ s.hom.hom ≫ a.hom.hom)).eq
    · change (v * w) ≫ t.hom.hom = (w * v) ≫ t.hom.hom
      rw [postMul, postMul, hv₂]
      apply (cancel_mono b.hom.hom).mp
      rw [postMul, postMul, Category.assoc, Category.assoc]
      exact (commute_from_centre hqJc x (w ≫ t.hom.hom ≫ b.hom.hom)).eq

theorem centralProductKernel_conditional :
    CentreFormula.{u} →
    CentralProductKernel.{u} := by
  intro _ k _ G hG Z hZ T hT D hD
  obtain ⟨I, p, q, hI, hfinite⟩ :=
    LinearAlgebraicGroups.CentralTorus.centralTorusDerivedIntersectionFinite G hG Z hZ T hT D hD
  obtain ⟨m, hm⟩ := mulMap (T.inclusion ≫ Z.inclusion) D.inclusion (centralInclusion hZ T)
  exact ⟨m, hm, identifyCentralProductKernel hZ T D I p q hI hfinite m hm⟩

open Specs.GeometricRadicals (IsRadical IsSmoothConnectedNormal IsSolvableRadical
  IsTrivialSubgroup IsUnipotentRadical geometricSolvableRadical geometricUnipotentRadical)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.SchemeDerivedGroup (IsSolvable)
open Specs.Unipotent (IsUnipotent)

open private inclusion_mono from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private conjugate conjugationIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private conjugate_le_of_normal normal_of_rational_conjugation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
open private factor_closed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private radical_transport unipotent_of_iso solvable_of_iso trivial_baseChange_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private torus_smooth_connected_solvable
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private isIso_of_trivial_kernel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
open private torus_of_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private torus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private isTorus_iff_coordinates from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private isLargest_transport finite_of_finite_group_baseChange
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralTorus

private theorem subgroupIso {G : GroupScheme k} {A B : ClosedSubgroup G}
    (hab : IsSubgroupOf A B) (hba : IsSubgroupOf B A) :
    ∃ e : A.group ≅ B.group, e.hom ≫ B.inclusion = A.inclusion := by
  obtain ⟨f, hf⟩ := hab
  obtain ⟨g, hg⟩ := hba
  letI := inclusion_mono A
  letI := inclusion_mono B
  exact ⟨⟨f, g, (cancel_mono A.inclusion).mp (by simp [hg, hf]),
    (cancel_mono B.inclusion).mp (by simp [hf, hg])⟩, hf⟩

private theorem trivialOfSubgroup {G : GroupScheme k} {A B : ClosedSubgroup G}
    (h : IsSubgroupOf A B) (hB : IsTrivialSubgroup B) : IsTrivialSubgroup A := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨e⟩ := hB
  letI := inclusion_mono A
  haveI : Mono f := mono_of_mono_fac hf
  have hzero : f = 0 := IsZero.eq_of_tgt ((Grp.isZero_trivial _).of_iso e) _ _
  exact ⟨(IsZero.of_mono_eq_zero f hzero).iso (Grp.isZero_trivial _)⟩

private theorem normalRadicalOfNormal [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (D : ClosedSubgroup G.val) (hn : IsNormalSubgroup D.inclusion)
    (P : AffineAlgebraicGroup k → Prop)
    (hP : ∀ {A B : AffineAlgebraicGroup k}, (A.val ≅ B.val) →
      Smooth A.val.X.hom → ConnectedSpace A.val.X.left →
      Smooth B.val.X.hom → ConnectedSpace B.val.X.left → (P A ↔ P B))
    (N : ClosedSubgroup D.group) (hN : IsRadical (closedSubgroupAlgebraicGroup D) P N) :
    IsNormalSubgroup (subgroupOfSubgroup D N).inclusion := by
  apply normal_of_rational_conjugation G hs _ hN.1.1
  intro g
  obtain ⟨f, hf⟩ := conjugate_le_of_normal hn g
  obtain ⟨i, hi⟩ := conjugate_le_of_normal hn g⁻¹
  change f ≫ D.inclusion = D.inclusion ≫ (conjugationIso g).hom at hf
  change i ≫ D.inclusion = D.inclusion ≫ (conjugationIso g).inv at hi
  letI := inclusion_mono D
  let e : D.group ≅ D.group := ⟨f, i,
    (cancel_mono D.inclusion).mp (by
      rw [Category.assoc, hi, ← Category.assoc, hf, Category.assoc,
        (conjugationIso g).hom_inv_id, Category.comp_id, Category.id_comp]),
    (cancel_mono D.inclusion).mp (by
      rw [Category.assoc, hf, ← Category.assoc, hi, Category.assoc,
        (conjugationIso g).inv_hom_id, Category.comp_id, Category.id_comp])⟩
  let A := closedSubgroupAlgebraicGroup D
  have hN' := radical_transport (G := A) (G' := A) e P
    (fun iso ha hb ↦ hP iso ha.1 ha.2.1 hb.1 hb.2.1) N hN
  obtain ⟨j, hj⟩ := hN.2.2 _ hN'.1 hN'.2.1
  change j ≫ N.inclusion = N.inclusion ≫ f at hj
  refine ⟨j, ?_⟩
  change j ≫ (N.inclusion ≫ D.inclusion) =
    (N.inclusion ≫ D.inclusion) ≫ (conjugationIso g).hom
  rw [← Category.assoc, hj, Category.assoc, hf, Category.assoc]

private theorem trivialNormalUnipotent [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (hG : IsReductive G) (U : ClosedSubgroup G.val) (hU : IsSmoothConnectedNormal U)
    (hu : IsUnipotent (closedSubgroupAlgebraicGroup U)) : IsTrivialSubgroup U := by
  obtain ⟨N, hN, e, _⟩ := RadicalBaseChange.unipotentRadicalPerfectDescent G hG.1 hG.2.1
  obtain ⟨d⟩ := hG.2.2
  have hn : IsTrivialSubgroup N :=
    (trivial_baseChange_iff (K := AlgebraicClosure k) N.group).mp ⟨e ≪≫ d⟩
  exact trivialOfSubgroup (hN.2.2 U hU hu) hn

private theorem normalSolvableTorus [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (hG : IsReductive G) (D : ClosedSubgroup G.val) (hD : IsSmoothConnectedNormal D)
    (hd : IsSolvable D.group) : IsTorus D.group := by
  let A := closedSubgroupAlgebraicGroup D
  obtain ⟨U, Q, q, hU, hq, hsplit, _⟩ :=
    GeometricTorusSplitting.splitting A hD.1 hD.2.1 hd
  obtain ⟨hs, hc, hn, hu, hmax⟩ := hU
  have hrad : IsUnipotentRadical A U := ⟨⟨hs, hc, hn⟩, hu, fun V _ hV ↦ hmax V hV⟩
  have hUn := normalRadicalOfNormal G hG.1 D hD.2.2 IsUnipotent
    (fun e _ _ _ _ ↦ unipotent_of_iso e) U hrad
  letI : IsIso q := isIso_of_trivial_kernel q U hq
    (trivialNormalUnipotent G hG (subgroupOfSubgroup D U) ⟨hs, hc, hUn⟩ hu)
  exact torus_of_iso (asIso q).symm ((isTorus_iff_coordinates Q).mpr (torus_of_split hsplit))

private theorem connectedOfGeometricallyConnected (G : AffineAlgebraicGroup k)
    (h : GeometricallyConnected G.val.X.hom) : ConnectedSpace G.val.X.left := by
  letI := h
  exact GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom

private theorem factorCentralTorus (G : AffineAlgebraicGroup k) {Z : ClosedSubgroup G.val}
    (hZ : IsSchemeCentre Z) {T : ClosedSubgroup Z.group} (hT : IsLargestTorus T)
    (S : ClosedSubgroup G.val) (ht : IsTorus S.group)
    (hc : Centralizes (𝟙 G.val) S.inclusion.hom.hom) :
    IsSubgroupOf S (subgroupOfSubgroup Z T) := by
  obtain ⟨f, hf⟩ := (hZ _ _).mp hc
  letI := Z.isClosedImmersion
  letI : IsMonHom f := isMonHom_of_comp_closed f S.inclusion Z.inclusion hf
  let j : S.group ⟶ Z.group := Grp.homMk f
  have hj : j ≫ Z.inclusion = S.inclusion := Grp.hom_ext _ _ hf
  let M : ClosedSubgroup Z.group := ⟨_, j, factor_closed hj⟩
  obtain ⟨p, hp⟩ := hT.2 M ht
  refine ⟨p, ?_⟩
  change p ≫ T.inclusion ≫ Z.inclusion = S.inclusion
  rw [← Category.assoc, show p ≫ T.inclusion = j from hp, hj]

private theorem centralizesOfNormalTorus (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (S : ClosedSubgroup G.val) (ht : IsTorus S.group) (hn : IsNormalSubgroup S.inclusion) :
    Centralizes (𝟙 G.val) S.inclusion.hom.hom := by
  apply (centralizes_iff _ _).mpr
  intro Y x y
  have h := LinearAlgebraicGroups.NormalizerLatticeAction.normalTorusCentral G hs hc S ht hn
  simpa using ((centralizes_iff S.inclusion y).mp (h Y y) Y (𝟙 Y) x).symm

private theorem normalOfCentral {G : GroupScheme k} (S : ClosedSubgroup G)
    (hc : Centralizes (𝟙 G) S.inclusion.hom.hom) : IsNormalSubgroup S.inclusion := by
  refine ⟨snd G.X S.group.X, ?_⟩
  let x := fst G.X S.group.X
  let y := snd G.X S.group.X ≫ S.inclusion.hom.hom
  change y = x * y * x⁻¹
  rw [← (commute_from_centre hc (snd G.X S.group.X) x).eq, mul_inv_cancel_right]

private theorem centralTorusBaseChange (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    {Z : ClosedSubgroup G.val} (hZ : IsSchemeCentre Z)
    {T : ClosedSubgroup Z.group} (hT : IsLargestTorus T) (K : Type u) [Field K] [Algebra k K] :
    ∃ (hZ' : IsClosedImmersion ((groupBaseChange k K).map Z.inclusion).hom.hom.left)
      (hT' : IsClosedImmersion ((groupBaseChange k K).map T.inclusion).hom.hom.left),
      IsSchemeCentre (baseChangedSubgroup K Z hZ') ∧ IsLargestTorus (baseChangedSubgroup K T hT') := by
  obtain ⟨T₀, hT₀, hb⟩ := LinearAlgebraicGroups.CentralTorus.largestCentralTorus G hG Z hZ
  obtain ⟨e, he⟩ := subgroupIso (hT₀.2 T hT.1) (hT.2 T₀ hT₀.1)
  obtain ⟨hz, ht₀, hc, ht⟩ := hb K
  let F := groupBaseChange k K
  let htk := baseChangeClosedSubgroup k K T.inclusion T.isClosedImmersion
  refine ⟨hz, htk, hc, isLargest_transport _ _ ht (F.mapIso e) ?_⟩
  show F.map e.hom ≫ F.map T₀.inclusion = F.map T.inclusion
  rw [← Functor.map_comp, he]

private theorem radicalEqualsCentralTorus :
    GeometricSolvableRadical.{u} := by
  intro k _ G hG Z hZ T hT
  let K := AlgebraicClosure k
  let H := GeometricGroup G
  let R := geometricSolvableRadical G
  have hH := (RadicalBaseChange.reductiveFieldExtension (K := K) G hG.1 hG.2.1).mpr hG
  have hR := GeometricRadicals.geometricSolvableRadicalLargest G
  have hr := normalSolvableTorus H hH R hR.1 hR.2.1
  obtain ⟨hz, ht, hzk, htk⟩ := centralTorusBaseChange G hG hZ hT K
  let C := baseChangedSubgroup K Z hz
  let S := baseChangedSubgroup K T ht
  have hRS := factorCentralTorus H hzk htk R hr
    (centralizesOfNormalTorus H hH.1 (connectedOfGeometricallyConnected H hH.2.1) R hr hR.1.2.2)
  have hcent := centralInclusion hzk S
  let SC := subgroupOfSubgroup C S
  obtain ⟨hs, hconn, hsol⟩ :=
    torus_smooth_connected_solvable (closedSubgroupAlgebraicGroup (G := H) SC) htk.1
  have hSR := hR.2.2 SC ⟨hs, hconn, normalOfCentral SC hcent⟩ hsol
  obtain ⟨e, he⟩ := subgroupIso hRS hSR
  exact ⟨e, by rw [Functor.map_comp]; exact he⟩

theorem geometricSolvableRadical_conditional :
    CentreFormula.{u} →
    GeometricSolvableRadical.{u} :=
  fun _ ↦ radicalEqualsCentralTorus

open private isIso_of_schemeIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private finite_structure_of_finite_hopf from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralTorus
open private splitGroupHomEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent

private theorem trivialOfFiniteSmoothConnected (A : AffineAlgebraicGroup k)
    (hs : Smooth A.val.X.hom) (hc : ConnectedSpace A.val.X.left) (hf : IsFinite A.val.X.hom) :
    Nonempty (A.val ≅ Grp.trivial (SchemeOver k)) := by
  letI := hs
  letI := hc
  letI := hf
  letI : IsLocallyArtinian (Spec (CommRingCat.of k)) :=
    Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  letI : IsLocallyArtinian A.val.X.left := .of_locallyQuasiFinite A.val.X.hom
  haveI : Subsingleton A.val.X.left := subsingleton_of_preconnected_totallyDisconnected
  haveI : IsReduced A.val.X.left := isReduced_of_smooth_over_field A.val.X.hom
  let N := Specs.GeometricRadicals.identitySubgroup A
  haveI := N.isClosedImmersion
  haveI : Surjective N.inclusion.hom.hom.left :=
    ⟨fun x ↦ ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩⟩
  haveI := isIso_of_isClosedImmersion_of_surjective N.inclusion.hom.hom.left
  letI := isIso_of_schemeIso N.inclusion
  exact ⟨(asIso N.inclusion).symm⟩

private theorem finiteOfIso {A B : GroupScheme k} (e : A ≅ B)
    (hb : IsFinite B.X.hom) : IsFinite A.X.hom := by
  letI := hb
  letI : IsIso e.hom.hom.hom.left :=
    (Grp.forget (SchemeOver k) ⋙ Over.forget _).map_isIso e.hom
  rw [← e.hom.hom.hom.w]
  infer_instance

private theorem finiteCentreOfTrivialLargestTorus (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (Z : ClosedSubgroup G.val) (hZ : IsSchemeCentre Z)
    (T : ClosedSubgroup Z.group) (hT : IsLargestTorus T) (ht : IsTrivialSubgroup T) :
    IsFinite Z.group.X.hom := by
  obtain ⟨Z₀, hZ₀, E, _, _, _, M, ⟨d⟩⟩ :=
    LinearAlgebraicGroups.CentralTorus.centreMultiplicativeType G hG
  have inclusion {A B : ClosedSubgroup G.val} (ha : IsSchemeCentre A) (hb : IsSchemeCentre B) :
      IsSubgroupOf A B := by
    obtain ⟨f, hf⟩ := (hb _ _).mp ((ha _ _).mpr ⟨𝟙 _, Category.id_comp _⟩)
    letI := B.isClosedImmersion
    letI := isMonHom_of_comp_closed f A.inclusion B.inclusion hf
    exact ⟨Grp.homMk f, Grp.hom_ext _ _ hf⟩
  obtain ⟨c, _⟩ := subgroupIso (inclusion hZ hZ₀) (inclusion hZ₀ hZ)
  let F := groupBaseChange k E
  let e := F.mapIso c ≪≫ d
  have hGE := (RadicalBaseChange.reductiveFieldExtension (K := E) G hG.1 hG.2.1).mpr hG
  obtain ⟨hz, hte, hze, hTE⟩ := centralTorusBaseChange G hG hZ hT E
  obtain ⟨j, _⟩ := LinearAlgebraicGroups.CentralTorus.splitCentralTorus
    (baseChangedAlgebraicGroup E G) hGE (baseChangedSubgroup E Z hz) hze
    (baseChangedSubgroup E T hte) hTE M e
  obtain ⟨t⟩ := (trivial_baseChange_iff (K := E) T.group).mpr ht
  let B := M.obj ⧸ CommGroup.torsion M.obj
  have hzero : IsZero (specGroup (Specs.DiagonalizableGroups.groupAlgebra E B)) :=
    (Grp.isZero_trivial (SchemeOver E)).of_iso (j.symm ≪≫ t)
  let b := splitGroupHomEquiv (k := E) B B
  have hb : MonoidHom.id B = 1 := b.injective (hzero.eq_of_src _ _)
  have hM : IsMulTorsion M.obj := by
    intro x
    have hq : (QuotientGroup.mk' (CommGroup.torsion M.obj)) x = 1 :=
      DFunLike.congr_fun hb _
    exact (QuotientGroup.eq_one_iff x).mp hq
  letI := M.property
  letI : Finite M.obj := CommGroup.finite_of_fg_isMulTorsion M.obj hM
  have hfinite :=
    finite_structure_of_finite_hopf (Specs.DiagonalizableGroups.groupAlgebra E M.obj)
  haveI := G.property.1
  letI := Z.isClosedImmersion
  exact finite_of_finite_group_baseChange E Z.group
    (isAffine_of_isAffineHom Z.inclusion.hom.hom.left) (finiteOfIso e hfinite)

theorem semisimpleIffFiniteCentre_conditional :
    CentreFormula.{u} →
    SemisimpleIffFiniteCentre.{u} := by
  intro _ k _ G hG Z hZ
  obtain ⟨T, hT, _⟩ := LinearAlgebraicGroups.CentralTorus.largestCentralTorus G hG Z hZ
  obtain ⟨e, _⟩ := radicalEqualsCentralTorus G hG Z hZ T hT
  let K := AlgebraicClosure k
  constructor
  · intro h
    obtain ⟨t⟩ := h.2.2
    exact finiteCentreOfTrivialLargestTorus G hG Z hZ T hT
      ((trivial_baseChange_iff (K := K) T.group).mp ⟨e.symm ≪≫ t⟩)
  · intro h
    obtain ⟨hz, ht, _, htk⟩ := centralTorusBaseChange G hG hZ hT K
    let S := subgroupOfSubgroup (baseChangedSubgroup K Z hz) (baseChangedSubgroup K T ht)
    let A := closedSubgroupAlgebraicGroup (G := GeometricGroup G) S
    obtain ⟨hs, hc, _⟩ := torus_smooth_connected_solvable A htk.1
    haveI : IsFinite ((groupBaseChange k K).obj Z.group).X.hom :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback Z.group.X.hom (fieldSpecMap k K)) h
    letI := ht
    have hf : IsFinite A.val.X.hom := by
      let i := (groupBaseChange k K).map T.inclusion
      change IsFinite ((groupBaseChange k K).obj T.group).X.hom
      rw [← i.hom.hom.w]
      exact inferInstanceAs (IsFinite (i.hom.hom.left ≫ ((groupBaseChange k K).obj Z.group).X.hom))
    obtain ⟨t⟩ := trivialOfFiniteSmoothConnected A hs hc hf
    exact ⟨hG.1, hG.2.1, ⟨e ≪≫ t⟩⟩

private theorem semisimpleDerivedOverAlgClosed [IsAlgClosed k]
    (G : AffineAlgebraicGroup k) (hg : IsReductive G) (D : ClosedSubgroup G.val)
    (hd : IsDerivedSubgroup D) : IsSemisimple (closedSubgroupAlgebraicGroup D) := by
  let A := closedSubgroupAlgebraicGroup D
  obtain ⟨hs, hgc⟩ := DerivedSubgroup.derivedSubgroupGeometry G D hd hg.1 hg.2.1
  obtain ⟨R, hR, e, _⟩ := RadicalBaseChange.solvableRadicalPerfectDescent A hs hgc
  let S := subgroupOfSubgroup D R
  have hn : IsNormalSubgroup S.inclusion :=
    normalRadicalOfNormal G hg.1 D hd.1 (fun H ↦ IsSolvable H.val)
      (fun d ha hb hc he ↦ solvable_of_iso d ha hb hc he) R hR
  have ht := normalSolvableTorus G hg S ⟨hR.1.1, hR.1.2.1, hn⟩ hR.2.1
  have hc := centralizesOfNormalTorus G hg.1 (connectedOfGeometricallyConnected G hg.2.1) S ht hn
  obtain ⟨Z, hZ, _⟩ := LinearAlgebraicGroups.CentralTorus.centreMultiplicativeType G hg
  obtain ⟨T, hT, _⟩ := LinearAlgebraicGroups.CentralTorus.largestCentralTorus G hg Z hZ
  obtain ⟨f, hf⟩ := factorCentralTorus G hZ hT S ht hc
  obtain ⟨I, p, q, hI, hfinite⟩ :=
    LinearAlgebraicGroups.CentralTorus.centralTorusDerivedIntersectionFinite G hg Z hZ T hT D hd
  let j : R.group ⟶ I := hI.lift f R.inclusion hf
  have hjq : j ≫ q = R.inclusion := hI.lift_snd _ _ _
  haveI : IsClosedImmersion (j.hom.hom.left ≫ q.hom.hom.left) := by
    change IsClosedImmersion (j ≫ q).hom.hom.left
    rw [hjq]
    exact R.isClosedImmersion
  haveI : IsClosedImmersion q.hom.hom.left := by
    let i := T.inclusion ≫ Z.inclusion
    letI := T.isClosedImmersion
    letI := Z.isClosedImmersion
    have hi : IsClosedImmersion i.hom.hom.left := by
      change IsClosedImmersion (T.inclusion.hom.hom.left ≫ Z.inclusion.hom.hom.left)
      infer_instance
    let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
    have pb : IsPullback p.hom.hom.left q.hom.hom.left i.hom.hom.left D.inclusion.hom.hom.left :=
      F.map_isPullback hI
    exact MorphismProperty.of_isPullback pb hi
  haveI : IsClosedImmersion j.hom.hom.left :=
    IsClosedImmersion.of_comp_isClosedImmersion _ q.hom.hom.left
  have hfin : IsFinite R.group.X.hom := by
    letI := hfinite
    rw [← j.hom.hom.w]
    exact inferInstanceAs (IsFinite (j.hom.hom.left ≫ I.X.hom))
  obtain ⟨d⟩ := trivialOfFiniteSmoothConnected (closedSubgroupAlgebraicGroup R)
    hR.1.1 hR.1.2.1 hfin
  obtain ⟨v⟩ := (trivial_baseChange_iff (K := AlgebraicClosure k) R.group).mpr ⟨d⟩
  exact ⟨hs, hgc, ⟨e.symm ≪≫ v⟩⟩

theorem derivedSemisimple_conditional :
    CentreFormula.{u} →
    DerivedSemisimple.{u} := by
  intro _ k _ G hG D hD
  let K := AlgebraicClosure k
  have hH := (RadicalBaseChange.reductiveFieldExtension (K := K) G hG.1 hG.2.1).mpr hG
  obtain ⟨hd, hd', _⟩ := DerivedSubgroup.derivedSubgroupBaseChange K G D hD hG.1 hG.2.1
  obtain ⟨hs, hc⟩ := DerivedSubgroup.derivedSubgroupGeometry G D hD hG.1 hG.2.1
  exact (RadicalBaseChange.semisimpleFieldExtension (K := K)
    (closedSubgroupAlgebraicGroup D) hs hc).mp
    (semisimpleDerivedOverAlgClosed (GeometricGroup G) hH (baseChangedSubgroup K D hd) hd')

open scoped BigOperators
open Opposite
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.SchemeDerivedGroup (IsCommutative RepresentsQuotient)
open Specs.NormalizerLatticeAction (SplitImage ConstantGroup FaithfulWeights)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (absoluteRoots)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.AdjointRepresentation (GroupPoints)
open LinearAlgebraicGroups.CocharacterDynamics
  (LimitDecomposition existsLimitDecomposition oppositeCocharacter bigCell bigCellMap
    multiplyFactors HasLimit orbit polynomialFamily_injective polynomialToLaurent
    polynomialEvaluate laurentConstants mapPoints_comp factorsThroughClosed_iff)

open private factors_through_closed_of_rational_points subgroup_of_sections
  cocharacter_detects_centralizer from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
open private comp_conjugateFamily from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private polynomialConstants polynomialConstants_laurent polynomialConstants_zero
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private group_hom_ext from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries
open private exists_section_lift sectionOfClosedPoint sectionOfClosedPoint_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private affineBaseTerminal from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SplitFixedPoint
open private image_of_geometric_torus torus_descends_from_algebraic_closure
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriExist
open private torus_commutative from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private split_of_torus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private baseChangeMapPullback from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components
open private fieldSpecMap_fpqc from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private affine_tensor from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.FiniteWordClosure
open private prodComparison_inv_fst prodComparison_inv_snd
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

private theorem contractingKilled {G Q : AffineAlgebraicGroup k}
    (q : G.val ⟶ Q.val) (hq : IsCommutative Q.val) {c : Cocharacter G.val}
    (L : LimitDecomposition c) :
    L.contracting.inclusion ≫ q = 0 := by
  apply group_hom_ext (closedSubgroupAlgebraicGroup L.contracting).property.1
  intro R t
  let g : GroupPoints G.val R := t ≫ L.contracting.inclusion.hom.hom
  obtain ⟨f, hf, hzero⟩ := (L.contracting_points R g).mpr ⟨t, rfl⟩
  have hc : mapPoints (polynomialToLaurent R) (f ≫ q.hom.hom) =
      mapPoints (laurentConstants R) (g ≫ q.hom.hom) := by
    have h := congrArg (· ≫ q.hom.hom) hf
    change mapPoints (polynomialToLaurent R) f ≫ q.hom.hom = orbit c g ≫ q.hom.hom at h
    rw [orbit, postMul, postMul, postInv] at h
    rw [hq _ (_ ≫ q.hom.hom) (mapPoints (laurentConstants R) g ≫ q.hom.hom),
      mul_assoc, mul_inv_cancel, mul_one] at h
    simpa only [mapPoints, Category.assoc] using h
  have he : f ≫ q.hom.hom = mapPoints (polynomialConstants R) (g ≫ q.hom.hom) := by
    apply polynomialFamily_injective Q.property.1 R
    rw [← mapPoints_comp, polynomialConstants_laurent, hc]
  have hz := congrArg (mapPoints (polynomialEvaluate R 0)) he
  rw [← mapPoints_comp, polynomialConstants_zero] at hz
  have hh : (g ≫ q.hom.hom) = 1 := by
    have hzero' := congrArg (· ≫ q.hom.hom) hzero
    simpa [mapPoints, Category.assoc] using hz.symm.trans (by
      simpa only [mapPoints, Category.assoc, MonObj.one_comp] using hzero')
  change (g ≫ q.hom.hom) = t ≫ (1 : L.contracting.group.X ⟶ Q.val.X)
  rw [MonObj.comp_one]
  exact hh

private theorem surjectiveOnSections [IsAlgClosed k] {G Q : AffineAlgebraicGroup k}
    (q : G.val ⟶ Q.val) (hs : Surjective q.hom.hom.left)
    (x : 𝟙_ (SchemeOver k) ⟶ Q.val.X) :
    ∃ y : 𝟙_ (SchemeOver k) ⟶ G.val.X, y ≫ q.hom.hom = x := by
  letI := G.property.2.1
  letI := Q.property.2.1
  exact exists_section_lift q.hom.hom x (hs.1 _)

private theorem closedSurjectiveSections [IsAlgClosed k] {G Q : AffineAlgebraicGroup k}
    (f : G.val ⟶ Q.val) (hf : IsClosedImmersion f.hom.hom.left)
    (h : ∀ x : 𝟙_ (SchemeOver k) ⟶ Q.val.X,
      ∃ y : 𝟙_ (SchemeOver k) ⟶ G.val.X, y ≫ f.hom.hom = x) :
    Surjective f.hom.hom.left := by
  letI := Q.property.2.1
  letI : JacobsonSpace Q.val.X.left := LocallyOfFiniteType.jacobsonSpace Q.val.X.hom
  have hclosed : closedPoints Q.val.X.left ⊆ Set.range f.hom.hom.left := by
    intro x hx
    obtain ⟨y, hy⟩ := h (sectionOfClosedPoint Q.val.X x hx)
    refine ⟨y.left (IsLocalRing.closedPoint k), ?_⟩
    exact (congrArg (fun z : 𝟙_ (SchemeOver k) ⟶ Q.val.X ↦
      z.left (IsLocalRing.closedPoint k)) hy).trans (sectionOfClosedPoint_apply _ _ _)
  have hall := hf.isClosedEmbedding.isClosed_range.closure_subset_iff.mpr hclosed
  rw [closure_closedPoints] at hall
  exact ⟨fun x ↦ hall (Set.mem_univ x)⟩

private theorem torusImageOfBigCell [IsAlgClosed k] (G Q : AffineAlgebraicGroup k)
    (hG : IsReductive G) (q : G.val ⟶ Q.val) (hq : IsCommutative Q.val)
    (hqs : Surjective q.hom.hom.left) (T : ClosedSubgroup G.val) {c : Cocharacter G.val}
    (P : LimitDecomposition c) (M : LimitDecomposition (oppositeCocharacter c))
    (hCT : IsSubgroupOf P.centralizer T) :
    Surjective (T.inclusion ≫ q).hom.hom.left := by
  letI := hG.1
  haveI : IsIntegral G.val.X.left := WordDomainGeometry.smoothConnectedGroupIntegral G hG.1
    (connectedOfGeometricallyConnected G hG.2.1)
  let C := P.centralizer
  obtain ⟨j, hj⟩ := hCT
  obtain ⟨I, p, i, hI, _, _⟩ :=
    schemeImageFactorization (closedSubgroupAlgebraicGroup T) Q (T.inclusion ≫ q)
  have hp := contractingKilled q hq P
  have hm := contractingKilled q hq M
  have hp' : P.contracting.inclusion.hom.hom ≫ q.hom.hom = 1 :=
    congrArg (Grp.forget (SchemeOver k)).map hp
  have hm' : M.contracting.inclusion.hom.hom ≫ q.hom.hom = 1 :=
    congrArg (Grp.forget (SchemeOver k)).map hm
  have hcq : P.centralizer.inclusion ≫ q = j ≫ p ≫ i := by
    rw [hI.1, ← Category.assoc j T.inclusion q, hj]
  have hj' : P.centralizer.inclusion.hom.hom ≫ q.hom.hom =
      j.hom.hom ≫ p.hom.hom ≫ i.hom.hom :=
    congrArg (Grp.forget (SchemeOver k)).map hcq
  have hcell : bigCellMap P M ≫ q.hom.hom =
      (snd _ _ ≫ fst C.group.X P.contracting.group.X ≫ j.hom.hom ≫ p.hom.hom) ≫ i.hom.hom := by
    simp only [bigCellMap, multiplyFactors, MonObj.comp_mul, MonObj.mul_comp, Category.assoc,
      hp', hm', hj', MonObj.comp_one, one_mul, mul_one, C]
  haveI : IsOpenImmersion (bigCellMap P M).left := bigCell G _ P M
  have hne : (Set.range (bigCellMap P M).left).Nonempty :=
    ⟨_, (lift η[M.contracting.group.X] (lift η[C.group.X] η[P.contracting.group.X])).left
      (IsLocalRing.closedPoint k), rfl⟩
  have hd : DenseRange (bigCellMap P M).left :=
    (bigCellMap P M).left.isOpenEmbedding.isOpen_range.dense hne
  have hr : Set.range (bigCellMap P M).left ⊆ q.hom.hom.left ⁻¹' Set.range i.hom.hom.left := by
    rintro _ ⟨x, rfl⟩
    have he := congrArg (fun f : _ ⟶ Q.val.X ↦ f.left x) hcell
    exact ⟨(snd _ _ ≫ fst C.group.X P.contracting.group.X ≫ j.hom.hom ≫ p.hom.hom).left x, he.symm⟩
  have hf : IsClosed (q.hom.hom.left ⁻¹' Set.range i.hom.hom.left) :=
    hI.2.2.2.2.2.isClosedEmbedding.isClosed_range.preimage q.hom.hom.left.continuous
  have hall := hf.closure_subset_iff.mpr hr
  rw [hd.closure_range] at hall
  haveI : Surjective i.hom.hom.left := ⟨fun x ↦ by
    obtain ⟨y, rfl⟩ := hqs.1 x
    exact hall (Set.mem_univ y)⟩
  haveI := hI.2.2.1
  rw [← hI.1]
  exact inferInstanceAs (Surjective (p.hom.hom.left ≫ i.hom.hom.left))

private theorem maximalTorusSurjects [IsAlgClosed k] (G Q : AffineAlgebraicGroup k)
    (hG : IsReductive G) (q : G.val ⟶ Q.val) (hq : IsCommutative Q.val)
    (hqs : Surjective q.hom.hom.left) (T : ClosedSubgroup G.val)
    (hT : IsTorus T.group) (hTs : IsSplitTorus T.group) (hmax : IsGeometricallyMaximal T)
    {weights : Set (Character T.group)} (hw : FaithfulWeights T.inclusion weights) :
    Surjective (T.inclusion ≫ q).hom.hom.left := by
  letI := hG.1
  have ht := (torus_smooth_connected_solvable (closedSubgroupAlgebraicGroup T) hT).1
  obtain ⟨c, hc⟩ := cocharacter_detects_centralizer G T hTs ht hw
  obtain ⟨P⟩ := existsLimitDecomposition G (c ≫ T.inclusion)
  obtain ⟨M⟩ := existsLimitDecomposition G (oppositeCocharacter (c ≫ T.inclusion))
  let C := P.centralizer
  have hcent := TorusCentralizer.maximalTorusCentralizer G hG T hT hmax
  have hCT : IsSubgroupOf C T := by
    apply subgroup_of_sections
    have hsm := (LinearAlgebraicGroups.CocharacterDynamics.limitSubgroupsSmooth G _ P).2.2
    letI : Smooth C.group.X.hom := hsm
    haveI : IsReduced C.group.X.left := isReduced_of_smooth_over_field C.group.X.hom
    letI := (closedSubgroupAlgebraicGroup C).property.2.1
    apply factors_through_closed_of_rational_points T.inclusion.hom.hom T.isClosedImmersion
      C.inclusion.hom.hom
    intro t
    exact (hcent _ _).mp (hc _ ((P.centralizer_points _ _).mpr ⟨t, rfl⟩))
  exact torusImageOfBigCell G Q hG q hq hqs T P M hCT

private theorem splitTorusPowerSurjective [IsAlgClosed k] {T : GroupScheme k}
    (hT : IsSplitTorus T) {n : ℕ} (hn : 0 < n) :
    Function.Surjective (fun x : (𝟙_ (SchemeOver k) ⟶ T.X) ↦ x ^ n) := by
  obtain ⟨r, ⟨e⟩⟩ := hT
  let R := CommAlgCat.of k k
  let U := (testSpec k).obj (op R)
  let a : U ≅ 𝟙_ (SchemeOver k) :=
    (affineBaseTerminal k).uniqueUpToIso (isTerminalTensorUnit (C := SchemeOver k))
  let b := (((groupPointsFunctor k).mapIso e) ≪≫
    StandardGroups.multiplicativePowerGroupPointsIso k (ULift.{u} (Fin r))).app R
  let F : (𝟙_ (SchemeOver k) ⟶ T.X) →* (ULift.{u} (Fin r) → Rˣ) := b.hom.hom.comp
    { toFun := (a.hom ≫ ·)
      map_one' := MonObj.comp_one _
      map_mul' := MonObj.comp_mul _ }
  have hb := ConcreteCategory.bijective_of_isIso b.hom
  have hF : Function.Bijective F := hb.comp
    ⟨fun _ _ h ↦ (cancel_epi a.hom).mp h, fun p ↦ ⟨a.inv ≫ p, by simp⟩⟩
  intro x
  have hp (i : ULift.{u} (Fin r)) : ∃ y : Rˣ, y ^ n = F x i := by
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq ((F x i : Rˣ) : k) hn
    have hz : y ≠ 0 := by
      intro h
      subst y
      exact (F x i).ne_zero (hy.symm.trans (zero_pow (Nat.ne_of_gt hn)))
    exact ⟨Units.mk0 y hz, Units.ext hy⟩
  choose y hy using hp
  obtain ⟨z, hz⟩ := hF.2 y
  refine ⟨z, hF.1 ?_⟩
  rw [map_pow, hz]
  exact funext hy

private def postcompose
    {A B C : GroupScheme k} [IsCommMonObj B.X] [IsCommMonObj C.X] (f : B ⟶ C) :
    (A ⟶ B) →* (A ⟶ C) where
  toFun g := g ≫ f
  map_one' := by apply Grp.hom_ext; exact MonObj.one_comp _
  map_mul' g h := by apply Grp.hom_ext; exact postMul f g.hom.hom h.hom.hom

private theorem hasConstantLabel {Q : GroupScheme k} {W : Type u} [Group W]
    (C : ConstantGroup Q W) (q : 𝟙_ (SchemeOver k) ⟶ Q.X) :
    ∃ w, q = toUnit (𝟙_ (SchemeOver k)) ≫ C.sectionPoint w := by
  let w := C.families _ q (IsLocalRing.closedPoint k)
  refine ⟨w, (C.families _).injective ?_⟩
  rw [C.constant]
  ext x
  change C.families _ q x = w
  rw [show x = IsLocalRing.closedPoint k from Subsingleton.elim (α := Spec (CommRingCat.of k)) _ _]

private theorem conjugationForLabel {G S N Q : GroupScheme k}
    {i : S ⟶ G} {j : N ⟶ G} {q : N ⟶ Q} (W : SplitImage i j q)
    {n : 𝟙_ (SchemeOver k) ⟶ N.X} {w : W.labels}
    (hw : n ≫ q.hom.hom = toUnit _ ≫ W.constantGroup.sectionPoint w) :
    ((W.conjugation w).hom ≫ i).hom.hom =
      (toUnit S.X ≫ n ≫ j.hom.hom) * i.hom.hom *
        (toUnit S.X ≫ n ≫ j.hom.hom)⁻¹ := by
  have h := congrArg (lift (𝟙 S.X) (toUnit S.X) ≫ ·) (W.conjugates _ n w hw)
  simp only [comp_conjugateFamily, lift_snd_assoc, lift_fst_assoc, Category.id_comp] at h
  exact h.symm

private theorem normKillsRoot {X : Type*} [CommGroup X] [IsMulTorsionFree X]
    (W : Subgroup (MulAut X)) [Fintype W] (a : X) (s : W) (hs : s.val a = a⁻¹) :
    ∏ w : W, w.val a = 1 := by
  have he := Equiv.prod_comp (Equiv.mulRight s) (fun w : W ↦ w.val a)
  change (∏ w : W, (w * s).val a) = ∏ w : W, w.val a at he
  have hmm (w : W) : (w * s).val a = (w.val a)⁻¹ := by
    change w.val (s.val a) = _
    rw [hs, map_inv]
  simp only [hmm, Finset.prod_inv_distrib] at he
  apply (pow_eq_one_iff_left (n := 2) (by decide)).mp
  rw [pow_two]
  calc
    _ = (∏ w : W, w.val a)⁻¹ * (∏ w : W, w.val a) := congrArg (· * _) he.symm
    _ = _ := inv_mul_cancel _

private theorem normIntoCentralTorus [IsAlgClosed k]
    (centre : CentreFormula.{u})
    (G Q : AffineAlgebraicGroup k) (hG : IsReductive G)
    (Z : ClosedSubgroup G.val) (hZ : IsSchemeCentre Z)
    (S : ClosedSubgroup Z.group) (hS : IsLargestTorus S)
    (T : ClosedSubgroup G.val) (hT : IsTorus T.group) (hTs : IsSplitTorus T.group)
    (hmax : IsGeometricallyMaximal T) (q : G.val ⟶ Q.val) (hqc : IsCommutative Q.val)
    (N : ClosedSubgroup G.val) (V : AffineAlgebraicGroup k) (p : N.group ⟶ V.val)
    (hN : RepresentsSubgroup N (fun _ n ↦ Normalizes T.inclusion n))
    (hp : Surjective p.hom.hom.left) (W : SplitImage T.inclusion N.inclusion p) :
    ∃ (a : T.group ⟶ S.group) (n : ℕ), 0 < n ∧
      ∀ x : 𝟙_ (SchemeOver k) ⟶ T.group.X,
        x ≫ (a ≫ S.inclusion ≫ Z.inclusion ≫ q).hom.hom =
          (x ≫ (T.inclusion ≫ q).hom.hom) ^ n := by
  classical
  letI := W.finite
  letI : Fintype W.labels := Fintype.ofFinite _
  letI : IsCommMonObj T.group.X := torus_commutative (closedSubgroupAlgebraicGroup T) hT
  letI : IsCommMonObj Q.val.X := (isCommMonObj_iff_isMulCommutative _).mpr
    (fun X ↦ ⟨⟨hqc X⟩⟩)
  let f : T.group ⟶ T.group := ∏ w : W.labels, (W.conjugation w).inv
  obtain ⟨_, hfree, _, _, _, _⟩ :=
    LinearAlgebraicGroups.RootData.CharacterPairing.perfectCharacterPairing T.group hTs
  letI := hfree
  have htorsion : ∀ (a : Additive (Character T.group)) (m : ℤ), m ≠ 0 → m • a = 0 → a = 0 := by
    intro a m hm he
    exact (smul_eq_zero.mp he).resolve_left hm
  letI : IsMulTorsionFree (Character T.group) := ⟨by
    intro n hn a b _ he
    have hd : (a / b) ^ n = 1 := by rw [div_pow, he, div_self']
    exact div_eq_one.mp (htorsion (Additive.ofMul (a / b)) (n : ℤ) (by exact_mod_cast hn) (by
      rw [natCast_zsmul]
      exact hd))⟩
  have hf (α : Character T.group) (hα : α ∈ absoluteRoots T) : f ≫ α = 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨r⟩⟩ :=
      LinearAlgebraicGroups.RootData.RootGroups.rankOneRootGroups G hG T hTs hmax α hα
    obtain ⟨t, ht⟩ := (hN _ _).mp r.normalizes
    obtain ⟨w, hw⟩ := hasConstantLabel W.constantGroup (t ≫ p.hom.hom)
    have e : (W.conjugation w).hom = r.conjugation.hom := by
      letI := inclusion_mono T
      apply (cancel_mono T.inclusion).mp
      apply Grp.hom_ext
      rw [conjugationForLabel W hw, r.conjugates, ht]
    have ei : (W.conjugation w).inv = r.conjugation.inv :=
      congrArg Iso.inv (Iso.ext e)
    have hwα : w.val α = α⁻¹ := by
      rw [W.characterAction, ei, r.reflection, r.root_pairing]
      group
    change postcompose α f = 1
    rw [show f = ∏ w : W.labels, (W.conjugation w).inv from rfl, map_prod]
    change (∏ w : W.labels, (W.conjugation w).inv ≫ α) = 1
    simp_rw [← W.characterAction]
    exact normKillsRoot W.labels α w hwα
  obtain ⟨_, _, _, _, _, hroots⟩ := centre G hG T hTs hmax
  let m := f ≫ T.inclusion
  obtain ⟨u, hu⟩ := (factorsThroughClosed_iff Z.inclusion.hom.hom Z.isClosedImmersion m.hom.hom).mpr
    (fun R x ↦ (hZ _ _).mp ((hroots R (x ≫ f.hom.hom)).mpr fun α hα ↦ by
      change (x ≫ f.hom.hom) ≫ α.hom.hom = 1
      rw [Category.assoc, ← Grp.comp_hom_hom, hf α hα, Grp.Hom.hom_one]
      exact MonObj.comp_one _))
  letI := Z.isClosedImmersion
  letI : IsMonHom u := isMonHom_of_comp_closed u m Z.inclusion hu
  let v : T.group ⟶ Z.group := Grp.homMk u
  have hv : v ≫ Z.inclusion = m := Grp.hom_ext _ _ hu
  obtain ⟨I, b, htI, hb⟩ := image_of_geometric_torus
    (G := closedSubgroupAlgebraicGroup T) (Q := closedSubgroupAlgebraicGroup Z) v hT
  obtain ⟨l, hl⟩ := hS.2 I htI
  let a := b ≫ l
  have haS : a ≫ S.inclusion = v := by
    change (b ≫ l) ≫ S.inclusion = v
    rw [Category.assoc, hl, hb]
  have ha : a ≫ S.inclusion ≫ Z.inclusion = f ≫ T.inclusion := by
    rw [← Category.assoc a S.inclusion Z.inclusion, haS, hv]
  have hfix (w : W.labels) :
      (W.conjugation w).inv ≫ T.inclusion ≫ q = T.inclusion ≫ q := by
    let hw' : 𝟙_ (SchemeOver k) ⟶ V.val.X := toUnit _ ≫ W.constantGroup.sectionPoint w
    obtain ⟨t, ht⟩ := surjectiveOnSections (G := closedSubgroupAlgebraicGroup N) p hp hw'
    change t ≫ p.hom.hom = toUnit (𝟙_ (SchemeOver k)) ≫ W.constantGroup.sectionPoint w at ht
    have h : (W.conjugation w).hom ≫ T.inclusion ≫ q = T.inclusion ≫ q := by
      apply Grp.hom_ext
      rw [← Category.assoc, Grp.comp_hom_hom, conjugationForLabel W (w := w) ht, postMul, postMul, postInv]
      rw [hqc _ (_ ≫ q.hom.hom) (T.inclusion.hom.hom ≫ q.hom.hom), mul_assoc, mul_inv_cancel, mul_one]
      rfl
    calc
      (W.conjugation w).inv ≫ T.inclusion ≫ q =
          (W.conjugation w).inv ≫ ((W.conjugation w).hom ≫ T.inclusion ≫ q) := by rw [h]
      _ = _ := Iso.inv_hom_id_assoc _ _
  refine ⟨a, Fintype.card W.labels, Fintype.card_pos, fun x ↦ ?_⟩
  have hq : f ≫ T.inclusion ≫ q = (T.inclusion ≫ q) ^ Fintype.card W.labels := by
    change postcompose (T.inclusion ≫ q) f = _
    rw [show f = ∏ w : W.labels, (W.conjugation w).inv from rfl, map_prod]
    change (∏ w : W.labels, (W.conjugation w).inv ≫ T.inclusion ≫ q) = _
    simp [hfix]
  have haQ : a ≫ S.inclusion ≫ Z.inclusion ≫ q = f ≫ T.inclusion ≫ q := by
    calc
      _ = (a ≫ S.inclusion ≫ Z.inclusion) ≫ q := by simp only [Category.assoc]
      _ = _ := by rw [ha, Category.assoc]
  rw [haQ, hq]
  let eval : (T.group ⟶ Q.val) →* (𝟙_ (SchemeOver k) ⟶ Q.val.X) :=
    { toFun := fun g ↦ x ≫ g.hom.hom
      map_one' := MonObj.comp_one _
      map_mul' := fun _ _ ↦ MonObj.comp_mul _ _ _ }
  exact map_pow eval _ _

private def productAlgebraicGroup (A B : AffineAlgebraicGroup k) : AffineAlgebraicGroup k := by
  letI := A.property.1
  letI := B.property.1
  letI := A.property.2.1
  letI := B.property.2.1
  letI := A.property.2.2
  letI := B.property.2.2
  refine ⟨A.val ⊗ B.val, affine_tensor, ?_, ?_⟩
  · change LocallyOfFiniteType (pullback.fst A.val.X.hom B.val.X.hom ≫ A.val.X.hom)
    infer_instance
  · change QuasiCompact (pullback.fst A.val.X.hom B.val.X.hom ≫ A.val.X.hom)
    infer_instance

private theorem surjectiveOfRationalLift [IsAlgClosed k] {A B : AffineAlgebraicGroup k}
    (f : A.val ⟶ B.val) (h : ∀ x : 𝟙_ (SchemeOver k) ⟶ B.val.X,
      ∃ y : 𝟙_ (SchemeOver k) ⟶ A.val.X, y ≫ f.hom.hom = x) :
    Surjective f.hom.hom.left := by
  obtain ⟨I, p, i, hI, _, _⟩ := schemeImageFactorization A B f
  haveI : Surjective i.hom.hom.left := closedSurjectiveSections i hI.2.2.2.2.2 (by
    intro x
    obtain ⟨y, hy⟩ := h x
    refine ⟨y ≫ p.hom.hom, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, hI.1, hy])
  letI := hI.2.2.1
  rw [← hI.1]
  exact inferInstanceAs (Surjective (p.hom.hom.left ≫ i.hom.hom.left))

private theorem geometricCentralProductSurjective [IsAlgClosed k]
    (centre : CentreFormula.{u})
    (G : AffineAlgebraicGroup k) (hG : IsReductive G) (Z : ClosedSubgroup G.val)
    (hZ : IsSchemeCentre Z) (S : ClosedSubgroup Z.group) (hS : IsLargestTorus S)
    (D : ClosedSubgroup G.val) (hD : IsDerivedSubgroup D)
    (m : (S.group ⊗ D.group) ⟶ G.val) (hm : IsCentralProduct S D m) :
    Surjective m.hom.hom.left := by
  have hc := connectedOfGeometricallyConnected G hG.2.1
  obtain ⟨_, _, Q, q, _, _, hker, hfac, _, hquot⟩ := normalAffineQuotient G D hD.1
  have hqc := (DerivedSubgroup.commutativeQuotientIff D q hker hquot).mpr hD.2.1
  obtain ⟨T, ht, hmax⟩ := MaximalToriExist.geometricallyMaximalTorusExists G hG.1 hc
  have hts := split_of_torus ((isTorus_iff_coordinates (closedSubgroupAlgebraicGroup T)).mp ht)
  obtain ⟨N, _, _, _, V, p, hN, _, _, hp, _, _, _, hW, _⟩ :=
    LinearAlgebraicGroups.NormalizerLatticeAction.quotientByCentralizer G hG.1 hc T ht
  obtain ⟨W⟩ := hW hts
  have hTQ := maximalTorusSurjects G Q hG q hqc hfac.2.2.1 T ht hts hmax W.faithfulWeights
  obtain ⟨a, n, hn, ha⟩ :=
    normIntoCentralTorus centre G Q hG Z hZ S hS T ht hts hmax q hqc N V p hN hp.2.2.1 W
  apply surjectiveOfRationalLift
    (A := productAlgebraicGroup (closedSubgroupAlgebraicGroup (subgroupOfSubgroup Z S))
      (closedSubgroupAlgebraicGroup D)) (B := G) m
  intro g
  have hlift : ∃ t : 𝟙_ (SchemeOver k) ⟶ T.group.X,
      t ≫ (T.inclusion ≫ q).hom.hom = g ≫ q.hom.hom :=
    surjectiveOnSections (G := closedSubgroupAlgebraicGroup T)
      (T.inclusion ≫ q) hTQ (g ≫ q.hom.hom)
  obtain ⟨t, htq⟩ := hlift
  obtain ⟨x, hx⟩ := splitTorusPowerSurjective (T := T.group) hts hn t
  let z := x ≫ a.hom.hom
  let i := S.inclusion ≫ Z.inclusion
  have hz : (z ≫ i.hom.hom) ≫ q.hom.hom = g ≫ q.hom.hom := by
    have he := ha x
    change x ≫ a.hom.hom ≫ i.hom.hom ≫ q.hom.hom =
      (x ≫ (T.inclusion ≫ q).hom.hom) ^ n at he
    change (x ≫ a.hom.hom ≫ i.hom.hom ≫ q.hom.hom) = g ≫ q.hom.hom
    rw [he]
    let φ := IsMonHom.monoidHom (T.inclusion ≫ q).hom.hom (𝟙_ (SchemeOver k))
    exact ((φ.map_pow x n).symm.trans (congrArg φ hx)).trans htq
  let y := (z ≫ i.hom.hom)⁻¹ * g
  obtain ⟨d₀, hd₀⟩ := (schemeKernel_sections hker y).mpr (by
    change ((z ≫ i.hom.hom)⁻¹ * g) ≫ q.hom.hom = 1
    rw [postMul, postInv, hz, inv_mul_cancel])
  let d : 𝟙_ (SchemeOver k) ⟶ D.group.X := d₀
  have hd : d ≫ D.inclusion.hom.hom = y := hd₀
  refine ⟨lift z d, ?_⟩
  change lift z d ≫ m.hom.hom = g
  rw [hm, MonObj.comp_mul]
  simp only [Grp.comp_hom_hom, Grp.fst_hom_hom, Grp.snd_hom_hom,
    firstProjection, secondProjection, lift_fst_assoc, lift_snd_assoc]
  change (z ≫ i.hom.hom) * (d ≫ D.inclusion.hom.hom) = g
  rw [hd]
  exact mul_inv_cancel_left _ _

private theorem flatOfSurjectiveHom {A B : AffineAlgebraicGroup k}
    (f : A.val ⟶ B.val) (hs : Smooth B.val.X.hom) (hf : Surjective f.hom.hom.left) :
    Flat f.hom.hom.left := by
  letI := hs
  letI := isReduced_of_smooth_over_field B.val.X.hom
  obtain ⟨I, p, i, hi, _, _⟩ := schemeImageFactorization A B f
  haveI : Surjective i.hom.hom.left := ⟨fun y ↦ by
    obtain ⟨x, he⟩ := hf.1 y
    exact ⟨p.hom.hom.left x, (congrArg (fun g : A.val ⟶ B.val ↦ g.hom.hom.left x) hi.1).trans he⟩⟩
  letI := hi.2.2.2.2.2
  haveI : IsIso i.hom.hom.left := isIso_of_isClosedImmersion_of_surjective _
  letI := hi.2.1
  rw [← hi.1]
  exact Flat.comp p.hom.hom.left i.hom.hom.left

theorem centralProductFaithfullyFlat_conditional :
    CentreFormula.{u} →
    CentralProductFaithfullyFlat.{u} := by
  intro centre k _ G hG Z hZ T hT D hD m hm
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let F₀ := baseChange k K
  let H := GeometricGroup G
  have hH := (RadicalBaseChange.reductiveFieldExtension (K := K) G hG.1 hG.2.1).mpr hG
  obtain ⟨hz, ht, hzk, htk⟩ := centralTorusBaseChange G hG hZ hT K
  obtain ⟨hd, hdk, _⟩ := DerivedSubgroup.derivedSubgroupBaseChange K G D hD hG.1 hG.2.1
  let Z' := baseChangedSubgroup K Z hz
  let T' := baseChangedSubgroup K T ht
  let D' := baseChangedSubgroup K D hd
  obtain ⟨n, hn⟩ := mulMap (T'.inclusion ≫ Z'.inclusion) D'.inclusion (centralInclusion hzk T')
  have hsurj := geometricCentralProductSurjective centre H hH Z' hzk T' htk D' hdk n hn
  let e := prodComparisonIso F₀ T.group.X D.group.X
  have hem : e.inv ≫ (F.map m).hom.hom = n.hom.hom := by
    letI : GrpObj (F₀.obj G.val.X) := (F.obj G.val).grp
    change e.inv ≫ F₀.map m.hom.hom = n.hom.hom
    have he₁ : e.inv ≫ F₀.map (fst T.group.X D.group.X) =
        fst (F₀.obj T.group.X) (F₀.obj D.group.X) :=
      prodComparison_inv_fst K T.group.X D.group.X
    have he₂ : e.inv ≫ F₀.map (snd T.group.X D.group.X) =
        snd (F₀.obj T.group.X) (F₀.obj D.group.X) :=
      prodComparison_inv_snd K T.group.X D.group.X
    rw [hm, hn]
    simp only [firstProjection, secondProjection, Grp.comp_hom_hom, Grp.fst_hom_hom,
      Grp.snd_hom_hom, F₀.map_mul, F₀.map_comp, MonObj.comp_mul, ← Category.assoc, he₁, he₂]
    rfl
  haveI : Surjective (F.map m).hom.hom.left := ⟨fun y ↦ by
    obtain ⟨x, hx⟩ := hsurj.1 y
    exact ⟨e.inv.left x, (congrArg (fun g : _ ⟶ H.val.X ↦ g.left x) hem).trans hx⟩⟩
  have hpb := baseChangeMapPullback (K := K) m.hom.hom
  let fpqc : MorphismProperty Scheme.{u} := @Surjective ⊓ @Flat ⊓ @QuasiCompact
  have hp : fpqc (pullback.fst G.val.X.hom (fieldSpecMap k K)) :=
    MorphismProperty.of_isPullback (P := fpqc)
      (IsPullback.of_hasPullback G.val.X.hom (fieldSpecMap k K)).flip (fieldSpecMap_fpqc (k := k) (K := K))
  have hmSurj : Surjective m.hom.hom.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Surjective) (Q := fpqc) hpb hp
      (inferInstance : Surjective (F.map m).hom.hom.left)
  exact ⟨flatOfSurjectiveHom
    (A := productAlgebraicGroup (closedSubgroupAlgebraicGroup (subgroupOfSubgroup Z T))
      (closedSubgroupAlgebraicGroup D)) (B := G) m hG.1 hmSurj, hmSurj⟩

open private quotient_smooth_connected torus_after_algClosed_extension
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriExist

private theorem torusOfSurjectiveMap (A B : AffineAlgebraicGroup k) (f : A.val ⟶ B.val)
    (ht : IsTorus A.val) (hs : Smooth B.val.X.hom) (hf : Surjective f.hom.hom.left) :
    IsTorus B.val := by
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let A' := GeometricGroup A
  let B' := GeometricGroup B
  have hs' : Smooth B'.val.X.hom :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback B.val.X.hom (fieldSpecMap k K)) hs
  letI := hs'
  letI := isReduced_of_smooth_over_field B'.val.X.hom
  have hf' : Surjective (F.map f).hom.hom.left :=
    MorphismProperty.of_isPullback (baseChangeMapPullback (K := K) f.hom.hom).flip hf
  obtain ⟨I, p, hI, hi⟩ := image_of_geometric_torus (G := A') (Q := B') (F.map f)
    (torus_after_algClosed_extension K A ht)
  haveI : Surjective I.inclusion.hom.hom.left := ⟨fun y ↦ by
    obtain ⟨x, hx⟩ := hf'.1 y
    exact ⟨p.hom.hom.left x, (congrArg (fun g : A'.val ⟶ B'.val ↦ g.hom.hom.left x) hi).trans hx⟩⟩
  letI := I.isClosedImmersion
  haveI : IsIso I.inclusion.hom.hom.left := isIso_of_isClosedImmersion_of_surjective _
  letI := isIso_of_schemeIso I.inclusion
  exact torus_descends_from_algebraic_closure B (torus_of_iso (asIso I.inclusion) hI)

theorem derivedTorusQuotient_conditional :
    CentreFormula.{u} →
    DerivedTorusQuotient.{u} := by
  intro centre k _ G hG D hD
  obtain ⟨_, _, Q, q, _, _, hker, hfac, _, hquot⟩ := normalAffineQuotient G D hD.1
  obtain ⟨Z, hZ, T, hT, _⟩ := centralTorusExists_conditional centre G hG
  obtain ⟨m, hm⟩ := mulMap (T.inclusion ≫ Z.inclusion) D.inclusion (centralInclusion hZ T)
  have hms := (centralProductFaithfullyFlat_conditional centre G hG
    Z hZ T hT D hD m hm).2
  have hDq := (schemeKernel_sections hker D.inclusion.hom.hom).mp ⟨𝟙 _, by
    change 𝟙 _ ≫ D.inclusion.hom.hom = _
    simp⟩
  have he : m ≫ q = firstProjection T.group D.group ≫ T.inclusion ≫ Z.inclusion ≫ q := by
    apply Grp.hom_ext
    simp only [Grp.comp_hom_hom, hm, postMul, Category.assoc, hDq, MonObj.comp_one, mul_one]
  haveI := hms
  have hs : Surjective (m ≫ q).hom.hom.left := by
    letI := hfac.2.2.1
    exact inferInstanceAs (Surjective (m.hom.hom.left ≫ q.hom.hom.left))
  have hsurj : Surjective (T.inclusion ≫ Z.inclusion ≫ q).hom.hom.left := by
    rw [he] at hs
    exact ⟨Function.Surjective.of_comp hs.1⟩
  obtain ⟨hQ, _⟩ := quotient_smooth_connected q hfac.2.1 hfac.2.2.1 hG.1
    (connectedOfGeometricallyConnected G hG.2.1)
  exact ⟨Q, q, hker, hquot, torusOfSurjectiveMap
    (closedSubgroupAlgebraicGroup (subgroupOfSubgroup Z T)) Q _ hT.1 hQ hsurj⟩

end

end LinearAlgebraicGroups.Reductive.CentralDerived

universe v8_closure_440470ced2c76e16_u0
theorem _root_.«LinearAlgebraicGroups».«Reductive».«CentralDerived».«centralProductFaithfullyFlat» : _root_.«LinearAlgebraicGroups».«Specs».«CentralDerived».«CentralProductFaithfullyFlat».{v8_closure_440470ced2c76e16_u0} :=
  @_root_.«LinearAlgebraicGroups».«Reductive».«CentralDerived».«centralProductFaithfullyFlat_conditional».{v8_closure_440470ced2c76e16_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«SchemeCentre».«schemeCentre».{v8_closure_440470ced2c76e16_u0})
theorem _root_.«LinearAlgebraicGroups».«Reductive».«CentralDerived».«centralProductKernel» : _root_.«LinearAlgebraicGroups».«Specs».«CentralDerived».«CentralProductKernel».{v8_closure_440470ced2c76e16_u0} :=
  @_root_.«LinearAlgebraicGroups».«Reductive».«CentralDerived».«centralProductKernel_conditional».{v8_closure_440470ced2c76e16_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«SchemeCentre».«schemeCentre».{v8_closure_440470ced2c76e16_u0})
theorem _root_.«LinearAlgebraicGroups».«Reductive».«CentralDerived».«centralTorusExists» : _root_.«LinearAlgebraicGroups».«Specs».«CentralDerived».«CentralTorusExists».{v8_closure_440470ced2c76e16_u0} :=
  @_root_.«LinearAlgebraicGroups».«Reductive».«CentralDerived».«centralTorusExists_conditional».{v8_closure_440470ced2c76e16_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«SchemeCentre».«schemeCentre».{v8_closure_440470ced2c76e16_u0})
theorem _root_.«LinearAlgebraicGroups».«Reductive».«CentralDerived».«derivedSemisimple» : _root_.«LinearAlgebraicGroups».«Specs».«CentralDerived».«DerivedSemisimple».{v8_closure_440470ced2c76e16_u0} :=
  @_root_.«LinearAlgebraicGroups».«Reductive».«CentralDerived».«derivedSemisimple_conditional».{v8_closure_440470ced2c76e16_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«SchemeCentre».«schemeCentre».{v8_closure_440470ced2c76e16_u0})
theorem _root_.«LinearAlgebraicGroups».«Reductive».«CentralDerived».«derivedTorusQuotient» : _root_.«LinearAlgebraicGroups».«Specs».«CentralDerived».«DerivedTorusQuotient».{v8_closure_440470ced2c76e16_u0} :=
  @_root_.«LinearAlgebraicGroups».«Reductive».«CentralDerived».«derivedTorusQuotient_conditional».{v8_closure_440470ced2c76e16_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«SchemeCentre».«schemeCentre».{v8_closure_440470ced2c76e16_u0})
theorem _root_.«LinearAlgebraicGroups».«Reductive».«CentralDerived».«geometricSolvableRadical» : _root_.«LinearAlgebraicGroups».«Specs».«CentralDerived».«GeometricSolvableRadical».{v8_closure_440470ced2c76e16_u0} :=
  @_root_.«LinearAlgebraicGroups».«Reductive».«CentralDerived».«geometricSolvableRadical_conditional».{v8_closure_440470ced2c76e16_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«SchemeCentre».«schemeCentre».{v8_closure_440470ced2c76e16_u0})
theorem _root_.«LinearAlgebraicGroups».«Reductive».«CentralDerived».«semisimpleIffFiniteCentre» : _root_.«LinearAlgebraicGroups».«Specs».«CentralDerived».«SemisimpleIffFiniteCentre».{v8_closure_440470ced2c76e16_u0} :=
  @_root_.«LinearAlgebraicGroups».«Reductive».«CentralDerived».«semisimpleIffFiniteCentre_conditional».{v8_closure_440470ced2c76e16_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«SchemeCentre».«schemeCentre».{v8_closure_440470ced2c76e16_u0})
