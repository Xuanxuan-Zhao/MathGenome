import Specs.LinearAlgebraicGroups.Arithmetic.StronglyRegularSeparableTransporter
import LinearAlgebraicGroups.Descent.AutomorphismSequence
import LinearAlgebraicGroups.Descent.SmoothPoint
import LinearAlgebraicGroups.Relative.MaximalSplitTori
import LinearAlgebraicGroups.Reductive.WeylScheme
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.StronglyRegularSeparableTransporter

open _root_.LinearAlgebraicGroups.Specs Specs.StronglyRegularSeparableTransporter
open Specs.AutomorphismSequence
open Specs.GeometricRadicals (IsReductive IsSplitTorus IsTorus)
open Specs.SteinbergGeometricFibres (IsPointCentralizer)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open Specs.Fppf (schemeTopology IsFppf)
open LinearAlgebraicGroups.Descent.NonabelianCohomology (pointMap pointAction)

open private groupSectionsMap groupSectionsMap_locallySurjective groupSections_isSheaf
  range_of_local_sections groupSheaf_separated
  from LinearAlgebraicGroups.Descent.AutomorphismSequence
open private splitTorusImage from LinearAlgebraicGroups.Relative.MaximalSplitTori
open private baseChangeMapPullback from LinearAlgebraicGroups.Affine.Components
open private closedSubgroupOfLocus adjoint_factorization from LinearAlgebraicGroups.Affine.Stabilizers
open private conjugation conjugation_apply conjugationIso
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private isMonHom_of_comp_closed from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private splitTorusSmooth from LinearAlgebraicGroups.Reductive.WeylScheme

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option linter.style.haveILetI false

variable {k S : Type u} [Field k] [Field S] [Algebra k S]

private theorem imageIsTorus (A B I : AffineAlgebraicGroup k)
    (f : A.val ⟶ B.val) (p : A.val ⟶ I.val) (i : I.val ⟶ B.val)
    (h : IsImageFactorization f p i) (hA : IsTorus A.val) : IsTorus I.val := by
  obtain ⟨E, hField, hAlg, hSep, hSplit⟩ := hA
  letI := hField
  letI := hAlg
  let F := groupBaseChange k E
  let A' := baseChangedAlgebraicGroup E A
  let B' := baseChangedAlgebraicGroup E B
  obtain ⟨D, q, hD, hfac⟩ := splitTorusImage A' B' hSplit (F.map f)
  have hp := baseChangeMapPullback (K := E) p.hom.hom
  have hi := baseChangeMapPullback (K := E) i.hom.hom
  have heq : F.map p ≫ F.map i = F.map f := by rw [← F.map_comp, h.1]
  obtain ⟨e, _⟩ := schemeImageUniqueness A' B' (F.map f) (F.map p) (F.map i) q D.inclusion
    heq hfac.1
    (MorphismProperty.of_isPullback (P := @Flat) hp.flip h.2.1)
    (MorphismProperty.of_isPullback (P := @Surjective) hp.flip h.2.2.1)
    (MorphismProperty.of_isPullback (P := @IsClosedImmersion) hi.flip h.2.2.2.2.2)
    hfac.2.1 hfac.2.2.1 D.isClosedImmersion
  obtain ⟨r, ⟨j⟩⟩ := hD
  exact ⟨E, hField, hAlg, hSep, r, ⟨e ≪≫ j⟩⟩

variable {G H : GroupScheme k}

private def innerValue (a : groupSections H ⟶ automorphisms G)
    {Y : SchemeOver k} (h : Y ⟶ H.X) (t : Y ⟶ G.X) : Y ⟶ G.X :=
  ((a.app (op Y) ⟨h⟩).asIso.hom.app (op (Over.mk (𝟙 Y)))).hom t

private theorem innerValue_comp (a : groupSections H ⟶ automorphisms G)
    {Y V : SchemeOver k} (v : V ⟶ Y) (h : Y ⟶ H.X) (t : Y ⟶ G.X) :
    v ≫ innerValue a h t = innerValue a (v ≫ h) (v ≫ t) := by
  let A := a.app (op Y) ⟨h⟩
  let U := Over.mk (𝟙 Y)
  let W := (Over.map v).obj (Over.mk (𝟙 V))
  let z : W ⟶ U := Over.homMk v (by simp [U, W])
  have hn : restrictAut v A = a.app (op V) ⟨v ≫ h⟩ :=
    (NatTrans.naturality_apply a v.op ⟨h⟩).symm
  change v ≫ innerValue a h t =
    ((a.app (op V) ⟨v ≫ h⟩).asIso.hom.app (op (Over.mk (𝟙 V)))).hom (v ≫ t)
  rw [← hn]
  exact (ConcreteCategory.congr_hom (A.asIso.hom.naturality z.op) t).symm

private theorem fixes_comp (a : groupSections H ⟶ automorphisms G)
    (x : 𝟙_ (SchemeOver k) ⟶ G.X) {Y V : SchemeOver k} (v : V ⟶ Y)
    {h : Y ⟶ H.X} (hh : Fixes a x h) : Fixes a x (v ≫ h) := by
  change innerValue a h (toUnit Y ≫ x) = toUnit Y ≫ x at hh
  change innerValue a (v ≫ h) (toUnit V ≫ x) = toUnit V ≫ x
  have he := congrArg (v ≫ ·) hh
  rw [innerValue_comp, ← Category.assoc, comp_toUnit] at he
  exact he

private theorem fixes_of_local (a : groupSections H ⟶ automorphisms G)
    (x : 𝟙_ (SchemeOver k) ⟶ G.X) {Y : SchemeOver k} (h : Y ⟶ H.X)
    {s : Sieve Y} (hs : s ∈ schemeTopology k Y)
    (hl : ∀ ⦃V : SchemeOver k⦄ (v : V ⟶ Y), s v → Fixes a x (v ≫ h)) :
    Fixes a x h := by
  have he : (⟨innerValue a h (toUnit Y ≫ x)⟩ : (groupSections G).obj (op Y)) =
      ⟨toUnit Y ≫ x⟩ := by
    apply groupSheaf_separated (groupSections_isSheaf G) hs
    intro V v hv
    apply ULift.ext
    change v ≫ innerValue a h (toUnit Y ≫ x) = v ≫ toUnit Y ≫ x
    rw [innerValue_comp, ← Category.assoc, comp_toUnit]
    exact hl v hv
  exact congrArg ULift.down he

private theorem fixes_projection {G : AffineAlgebraicGroup k} (Q : AdjointQuotient G)
    (a : groupSections Q.quotient.val ⟶ automorphisms G.val)
    (onLift : ∀ (Y : SchemeOver k) (g : Y ⟶ G.val.X),
      a.app (op Y) ⟨g ≫ Q.projection.hom.hom⟩ = innerAut g)
    (x : 𝟙_ (SchemeOver k) ⟶ G.val.X) {Y : SchemeOver k} (g : Y ⟶ G.val.X) :
    Fixes a x (g ≫ Q.projection.hom.hom) ↔ Commute g (toUnit Y ≫ x) := by
  unfold Fixes
  rw [onLift]
  change (𝟙 Y ≫ g) * (toUnit Y ≫ x) * (𝟙 Y ≫ g)⁻¹ = toUnit Y ≫ x ↔ _
  rw [Category.id_comp, mul_inv_eq_iff_eq_mul]
  rfl

theorem adjointTorusStabilizer : AdjointTorusStabilizer.{u} := by
  intro k S _ _ _ _ G _ x T hT hTx Q a onLift
  let A := closedSubgroupAlgebraicGroup T
  let f := T.inclusion ≫ Q.projection
  obtain ⟨I, p, i, hp, _, _⟩ := schemeImageFactorization A Q.quotient f
  let D : ClosedSubgroup Q.quotient.val := ⟨I.val, i, hp.2.2.2.2.2⟩
  have hcomp : p.hom.hom ≫ i.hom.hom = T.inclusion.hom.hom ≫ Q.projection.hom.hom :=
    congrArg (fun z => z.hom.hom) hp.1
  haveI : IsClosedImmersion i.hom.hom.left := D.isClosedImmersion
  haveI : Mono i.hom.hom := Over.mono_of_mono_left _
  have injective (Y : (SchemeOver k)ᵒᵖ) :
      Function.Injective ((groupSectionsMap i).app Y) := by
    intro b c h
    apply ULift.ext
    exact (cancel_mono i.hom.hom).mp (congrArg ULift.down h)
  have hD : RepresentsSubgroup D (fun _ h => Fixes a x h) := by
    intro Y h
    constructor
    · intro hh
      let q := groupSectionsMap Q.projection
      letI : Presheaf.IsLocallySurjective (schemeTopology k) q :=
        groupSectionsMap_locallySurjective Q.projection Q.fppf
      have hmem := range_of_local_sections (groupSectionsMap i)
        (groupSections_isSheaf D.group) injective ⟨h⟩
        (groupSections_isSheaf Q.quotient.val)
        (Presheaf.imageSieve_mem (schemeTopology k) q ⟨h⟩) (by
          rintro V v ⟨⟨g⟩, hg⟩
          have he : g ≫ Q.projection.hom.hom = v ≫ h := congrArg ULift.down hg
          have hf := fixes_comp a x v hh
          rw [← he, fixes_projection Q a onLift] at hf
          obtain ⟨t, ht⟩ := (hTx V g).mp hf
          refine ⟨⟨t ≫ p.hom.hom⟩, ULift.ext ?_⟩
          change (t ≫ p.hom.hom) ≫ i.hom.hom = v ≫ h
          rw [Category.assoc, hcomp, ← Category.assoc, ht, he])
      obtain ⟨⟨z⟩, hz⟩ := hmem
      exact ⟨z, congrArg ULift.down hz⟩
    · rintro ⟨z, rfl⟩
      let q := groupSectionsMap p
      letI : Presheaf.IsLocallySurjective (schemeTopology k) q :=
        groupSectionsMap_locallySurjective p ⟨hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
      apply fixes_of_local a x _ (Presheaf.imageSieve_mem (schemeTopology k) q ⟨z⟩)
      rintro V v ⟨⟨t⟩, ht⟩
      have he : t ≫ p.hom.hom = v ≫ z := congrArg ULift.down ht
      rw [← Category.assoc, ← he, Category.assoc, hcomp, ← Category.assoc,
        fixes_projection Q a onLift]
      exact (hTx V _).mpr ⟨t, rfl⟩
  let j := ((yonedaGrp.map i).app (op ((testSpec k).obj (op (CommAlgCat.of k S))))).hom
  refine ⟨D, imageIsTorus A Q.quotient I f p i hp hT, hD, j, fun _ => rfl, ?_, ?_, ?_⟩
  · intro t t' h
    exact (cancel_mono i.hom.hom).mp h
  · intro σ t
    change (_ ≫ t) ≫ i.hom.hom = _ ≫ (t ≫ i.hom.hom)
    exact Category.assoc _ _ _
  · intro h
    exact (hD _ h).symm

section Transporter

variable {K : Type u} [Field K] [Algebra k K]

private abbrev extend := Over.mapPullbackAdj (fieldSpecMap k K)

open scoped CategoryTheory.Obj in
/-- The pullback adjunction preserves the multiplication on the represented groups of sections. -/
private def adjointSections (G : GroupScheme k) (U : SchemeOver K) :
    ((Over.map (fieldSpecMap k K)).obj U ⟶ G.X) ≃*
      (U ⟶ ((groupBaseChange k K).obj G).X) where
  toEquiv := (extend (k := k) (K := K)).homEquiv U G.X
  map_mul' p q := by
    let a := extend (k := k) (K := K)
    let e : ((Over.map (fieldSpecMap k K)).obj U ⟶ G.X) ≃
        (U ⟶ ((groupBaseChange k K).obj G).X) := a.homEquiv U G.X
    change e (p * q) = e p * e q
    have he (t : (Over.map (fieldSpecMap k K)).obj U ⟶ G.X) :
        e t = a.unit.app U ≫ (baseChange k K).map t :=
      a.homEquiv_unit U G.X t
    rw [he, he p, he q, (baseChange k K).map_mul p q, MonObj.comp_mul]

private theorem adjointSections_constant (G : GroupScheme k) (U : SchemeOver K)
    (x : 𝟙_ (SchemeOver k) ⟶ G.X) :
    adjointSections G U (toUnit _ ≫ x) = toUnit U ≫ scalarExtendedRationalPoint K x := by
  let F := baseChange k K
  let a := extend (k := k) (K := K)
  change a.homEquiv U G.X (toUnit _ ≫ x) = toUnit U ≫ scalarExtendedRationalPoint K x
  rw [Adjunction.homEquiv_unit, F.map_comp, scalarExtendedRationalPoint, ← Category.assoc,
    ← Category.assoc]
  congr 1
  let e := Functor.Monoidal.εIso F
  exact ((isTerminalTensorUnit.ofIso e).hom_ext _ _)

private def rightTranslation (G : GroupScheme k)
    (b : 𝟙_ (SchemeOver k) ⟶ G.X) : G.X ≅ G.X where
  hom := 𝟙 G.X * (toUnit G.X ≫ b)
  inv := 𝟙 G.X * (toUnit G.X ≫ b)⁻¹
  hom_inv_id := by simp [MonObj.comp_mul, GrpObj.comp_inv, mul_assoc]
  inv_hom_id := by simp [MonObj.comp_mul, mul_assoc]

private theorem rightTranslation_apply (G : GroupScheme k)
    (b : 𝟙_ (SchemeOver k) ⟶ G.X) {Y : SchemeOver k} (p : Y ⟶ G.X) :
    p ≫ (rightTranslation G b).hom = p * (toUnit Y ≫ b) := by
  simp [rightTranslation, MonObj.comp_mul]

private theorem intertwines_translate (G : GroupScheme k)
    (x y b : 𝟙_ (SchemeOver k) ⟶ G.X) (hb : b * x * b⁻¹ = y)
    {Y : SchemeOver k} (p : Y ⟶ G.X) :
    p * (toUnit Y ≫ x) = (toUnit Y ≫ y) * p ↔
      Commute (p ≫ (rightTranslation G b⁻¹).hom) (toUnit Y ≫ y) := by
  rw [rightTranslation_apply, GrpObj.comp_inv]
  have he := congrArg (toUnit Y ≫ ·) hb
  simp only [MonObj.comp_mul, GrpObj.comp_inv] at he
  change _ ↔ (p * (toUnit Y ≫ b)⁻¹) * (toUnit Y ≫ y) =
    (toUnit Y ≫ y) * (p * (toUnit Y ≫ b)⁻¹)
  let B := toUnit Y ≫ b
  let X := toUnit Y ≫ x
  let Y' := toUnit Y ≫ y
  have hx : B⁻¹ * Y' = X * B⁻¹ := by
    change B * X * B⁻¹ = Y' at he
    rw [← he]
    group
  change p * X = Y' * p ↔ p * B⁻¹ * Y' = Y' * (p * B⁻¹)
  rw [mul_assoc p B⁻¹ Y', hx, ← mul_assoc p X B⁻¹, ← mul_assoc Y' p B⁻¹,
    mul_right_cancel_iff]

private def transporterInclusion (G : GroupScheme k) (x y : 𝟙_ (SchemeOver k) ⟶ G.X) :=
  equalizer.ι (𝟙 G.X * (toUnit G.X ≫ x)) ((toUnit G.X ≫ y) * 𝟙 G.X)

private theorem transporter_factors (G : GroupScheme k) (x y : 𝟙_ (SchemeOver k) ⟶ G.X)
    {U : SchemeOver k} (g : U ⟶ G.X) :
    g * (toUnit U ≫ x) = (toUnit U ≫ y) * g ↔
      ∃ t, t ≫ transporterInclusion G x y = g := by
  let p := 𝟙 G.X * (toUnit G.X ≫ x)
  let q := (toUnit G.X ≫ y) * 𝟙 G.X
  have he : g ≫ p = g ≫ q ↔ g * (toUnit U ≫ x) = (toUnit U ≫ y) * g := by
    simp [p, q, MonObj.comp_mul]
  rw [← he]
  change _ ↔ ∃ t, t ≫ equalizer.ι p q = g
  exact ⟨fun h => ⟨equalizer.lift g h, equalizer.lift_ι _ _⟩, fun ⟨t, ht⟩ => by
    rw [← ht, Category.assoc, Category.assoc, equalizer.condition]⟩

private theorem scalarIntertwiner_factors (G : GroupScheme k)
    (x y : 𝟙_ (SchemeOver k) ⟶ G.X) {Z : SchemeOver k} (i : Z ⟶ G.X)
    (hi : ∀ (V : SchemeOver k) (p : V ⟶ G.X),
      p * (toUnit V ≫ x) = (toUnit V ≫ y) * p ↔ ∃ t, t ≫ i = p)
    {U : SchemeOver K} (g : U ⟶ ((groupBaseChange k K).obj G).X) :
    g * (show U ⟶ ((groupBaseChange k K).obj G).X from
      toUnit U ≫ scalarExtendedRationalPoint K x) =
      (show U ⟶ ((groupBaseChange k K).obj G).X from
        toUnit U ≫ scalarExtendedRationalPoint K y) * g ↔
      ∃ t, t ≫ (baseChange k K).map i = g := by
  let e := adjointSections G U
  have hx := adjointSections_constant G U x
  have hy := adjointSections_constant G U y
  change e _ = _ at hx hy
  calc
    _ ↔ e (e.symm g * (toUnit _ ≫ x)) = e ((toUnit _ ≫ y) * e.symm g) := by
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hx, hy]
    _ ↔ _ := e.injective.eq_iff.trans
      ((hi _ _).trans (adjoint_factorization K i g).symm)

private theorem isoOfLoci {X Y Z : SchemeOver k} (i : Y ⟶ X) (j : Z ⟶ X) [Mono i] [Mono j]
    (e : X ≅ X) (he : ∀ (U : SchemeOver k) (g : U ⟶ X),
      (∃ p, p ≫ i = g) ↔ ∃ q, q ≫ j = g ≫ e.hom) :
    ∃ a : Y ≅ Z, a.hom ≫ j = i ≫ e.hom := by
  obtain ⟨f, hf⟩ := (he Y i).mp ⟨𝟙 Y, Category.id_comp _⟩
  obtain ⟨b, hb⟩ := (he Z (j ≫ e.inv)).mpr ⟨𝟙 Z, by simp⟩
  refine ⟨⟨f, b, ?_, ?_⟩, hf⟩
  · apply (cancel_mono i).mp
    rw [Category.assoc, hb, ← Category.assoc, hf]
    simp
  · apply (cancel_mono j).mp
    rw [Category.assoc, hf, ← Category.assoc, hb]
    simp

private theorem centralizer_exists (G : GroupScheme k) [IsSeparated G.X.hom]
    (x : 𝟙_ (SchemeOver k) ⟶ G.X) :
    ∃ T : ClosedSubgroup G, IsPointCentralizer T x := by
  let P (U : SchemeOver k) := Subgroup.centralizer ({toUnit U ≫ x} : Set (U ⟶ G.X))
  have hp (U : SchemeOver k) (g : U ⟶ G.X) :
      g ∈ P U ↔ Commute g (toUnit U ≫ x) :=
    Subgroup.mem_centralizer_singleton_iff
  obtain ⟨T, hT⟩ := closedSubgroupOfLocus P (transporterInclusion G x x)
    (by unfold transporterInclusion; infer_instance) (by
      intro U g
      rw [hp]
      exact transporter_factors G x x g)
  exact ⟨T, fun U g => (hp U g).symm.trans (hT U g)⟩

private theorem splitCentralizer_of_conjugate (G : GroupScheme k)
    (x : 𝟙_ (SchemeOver k) ⟶ G.X) (T : ClosedSubgroup G) (hT : IsPointCentralizer T x)
    (y b : 𝟙_ (SchemeOver K) ⟶ ((groupBaseChange k K).obj G).X)
    (hb : b * (show 𝟙_ (SchemeOver K) ⟶ ((groupBaseChange k K).obj G).X from
      scalarExtendedRationalPoint K x) * b⁻¹ = y)
    (C : ClosedSubgroup ((groupBaseChange k K).obj G))
    (hC : IsPointCentralizer C y) (hs : IsSplitTorus C.group) :
    IsSplitTorus ((groupBaseChange k K).obj T.group) := by
  let F := groupBaseChange k K
  let j := F.map T.inclusion
  let i := C.inclusion
  let e := conjugationIso b
  let E := (Grp.forget (SchemeOver K)).mapIso e
  have hj : IsClosedImmersion j.hom.hom.left :=
    baseChangeClosedSubgroup k K T.inclusion T.isClosedImmersion
  haveI : IsClosedImmersion i.hom.hom.left := C.isClosedImmersion
  haveI : Mono j.hom.hom := Over.mono_of_mono_left _
  haveI : Mono i.hom.hom := Over.mono_of_mono_left _
  obtain ⟨a, ha⟩ := isoOfLoci j.hom.hom i.hom.hom E (by
    intro U p
    let x' : 𝟙_ (SchemeOver K) ⟶ ((groupBaseChange k K).obj G).X :=
      scalarExtendedRationalPoint K x
    have hp : Commute p (toUnit U ≫ x') ↔ ∃ t, t ≫ j.hom.hom = p :=
      scalarIntertwiner_factors (K := K) G x x T.inclusion.hom.hom hT p
    refine hp.symm.trans (Iff.trans ?_ (hC U (p ≫ E.hom)))
    let m := MulAut.conj (toUnit U ≫ b)
    have hpy : m (toUnit U ≫ x') = toUnit U ≫ y := by
      change (toUnit U ≫ b) * (toUnit U ≫ x') * (toUnit U ≫ b)⁻¹ = _
      simpa only [MonObj.comp_mul, GrpObj.comp_inv] using congrArg (toUnit U ≫ ·) hb
    change Commute p (toUnit U ≫ x') ↔
      Commute (p ≫ (conjugation b).hom.hom) (toUnit U ≫ y)
    rw [conjugation_apply, ← hpy]
    change Commute p (toUnit U ≫ x') ↔ Commute (m p) (m (toUnit U ≫ x'))
    exact ⟨fun h => h.map m.toMonoidHom, fun h => m.injective (by
      simpa only [map_mul] using h.eq)⟩)

  have ha' : a.hom ≫ i.hom.hom = (j ≫ e.hom).hom.hom := ha
  haveI := isMonHom_of_comp_closed a.hom (j ≫ e.hom) i ha'
  obtain ⟨r, ⟨t⟩⟩ := hs
  exact ⟨r, ⟨(Grp.mkIso' a) ≪≫ t⟩⟩

private theorem exists_transporter_point [IsSepClosed k] (G : AffineAlgebraicGroup k)
    (x y : 𝟙_ (SchemeOver k) ⟶ G.val.X) (C : ClosedSubgroup G.val)
    (hC : IsPointCentralizer C y) (hs : IsSplitTorus C.group)
    (g : 𝟙_ (SchemeOver K) ⟶ ((groupBaseChange k K).obj G.val).X)
    (hg : g * (show 𝟙_ (SchemeOver K) ⟶ ((groupBaseChange k K).obj G.val).X from
        scalarExtendedRationalPoint K x) * g⁻¹ = scalarExtendedRationalPoint K y) :
    ∃ b : 𝟙_ (SchemeOver k) ⟶ G.val.X, b * x * b⁻¹ = y := by
  let F := baseChange k K
  let H := (groupBaseChange k K).obj G.val
  let x' : 𝟙_ (SchemeOver K) ⟶ H.X := scalarExtendedRationalPoint K x
  let y' : 𝟙_ (SchemeOver K) ⟶ H.X := scalarExtendedRationalPoint K y
  let p := transporterInclusion G.val x y
  let i := C.inclusion.hom.hom
  haveI : IsAffine G.val.X.left := G.property.1
  haveI : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  haveI : QuasiCompact G.val.X.hom := G.property.2.2
  haveI : IsClosedImmersion p.left := by dsimp [p, transporterInclusion]; infer_instance
  haveI : Mono p := Over.mono_of_mono_left p
  haveI : IsClosedImmersion i.left := C.isClosedImmersion
  haveI : Mono i := Over.mono_of_mono_left i
  have hP (U : SchemeOver K) (a : U ⟶ H.X) :
      a * (toUnit U ≫ x') = (toUnit U ≫ y') * a ↔ ∃ t, t ≫ F.map p = a :=
    scalarIntertwiner_factors G.val x y p (fun _ => transporter_factors G.val x y) a
  have hC' (U : SchemeOver K) (a : U ⟶ H.X) :
      Commute a (toUnit U ≫ y') ↔ ∃ t, t ≫ F.map i = a :=
    scalarIntertwiner_factors G.val y y i hC a
  obtain ⟨e, _⟩ := isoOfLoci (F.map p) (F.map i) (rightTranslation H g⁻¹) (by
    intro U a
    rw [← hP, ← hC']
    exact intertwines_translate H x' y' g hg a)
  haveI : Smooth C.group.X.hom := splitTorusSmooth hs
  haveI : Smooth (F.obj C.group.X).hom :=
    inferInstanceAs (Smooth (pullback.snd C.group.X.hom (fieldSpecMap k K)))
  haveI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have hSmooth : Smooth (F.obj (equalizer
      (𝟙 G.val.X * (toUnit G.val.X ≫ x)) ((toUnit G.val.X ≫ y) * 𝟙 G.val.X))).hom := by
    rw [← Over.w e.hom]
    infer_instance
  let fpqc : MorphismProperty Scheme.{u} := @Surjective ⊓ @Flat ⊓ @QuasiCompact
  have hfpqc : fpqc (fieldSpecMap k K) := by
    obtain ⟨hflat, hsurj⟩ := (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (algebraMap k K))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
    exact ⟨⟨hsurj, hflat⟩, inferInstanceAs (QuasiCompact (fieldSpecMap k K))⟩
  haveI := MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Smooth) hfpqc hSmooth

  haveI : QuasiCompact (equalizer
      (𝟙 G.val.X * (toUnit G.val.X ≫ x)) ((toUnit G.val.X ≫ y) * 𝟙 G.val.X)).hom := by
    rw [← Over.w p]
    infer_instance
  have hg' : g * (toUnit (𝟙_ (SchemeOver K)) ≫ x') =
      (toUnit (𝟙_ (SchemeOver K)) ≫ y') * g := by
    rw [show toUnit (𝟙_ (SchemeOver K)) = 𝟙 _ from toUnit_unique _ _, Category.id_comp,
      Category.id_comp]
    exact mul_inv_eq_iff_eq_mul.mp hg
  obtain ⟨t, _⟩ := (hP _ g).mp hg'
  let P := equalizer (𝟙 G.val.X * (toUnit G.val.X ≫ x)) ((toUnit G.val.X ≫ y) * 𝟙 G.val.X)
  have hnonempty : Nonempty P.left :=
    ⟨(t.left ≫ pullback.fst P.hom (fieldSpecMap k K)) (IsLocalRing.closedPoint K)⟩
  obtain ⟨s, hs⟩ := LinearAlgebraicGroups.Descent.exists_rational_point_of_smooth P.hom hnonempty
  let s' : 𝟙_ (SchemeOver k) ⟶ P := Over.homMk s hs
  have hb := (transporter_factors G.val x y (s' ≫ p)).mpr ⟨s', rfl⟩
  rw [show toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ from toUnit_unique _ _, Category.id_comp,
    Category.id_comp] at hb
  exact ⟨s' ≫ p, mul_inv_eq_iff_eq_mul.mpr hb⟩

private def precomposeIso {V U : SchemeOver k} (e : U ≅ V) (G : GroupScheme k) :
    (V ⟶ G.X) ≃* (U ⟶ G.X) where
  toFun p := e.hom ≫ p
  invFun p := e.inv ≫ p
  left_inv p := by simp
  right_inv p := by simp
  map_mul' p q := MonObj.comp_mul _ _ _

private def pointExtension (G : GroupScheme k) :
    Points G.X (CommAlgCat.of k K) ≃*
      (𝟙_ (SchemeOver K) ⟶ ((groupBaseChange k K).obj G).X) :=
  (precomposeIso (Over.isoMk (Iso.refl _) (by simp)) G).trans
    (adjointSections G (𝟙_ (SchemeOver K)))

private theorem pointExtension_eq (G : GroupScheme k) (y : Points G.X (CommAlgCat.of k K)) :
    pointExtension G y = extendedPoint y := rfl

private theorem pointExtension_constant (G : GroupScheme k)
    (x : 𝟙_ (SchemeOver k) ⟶ G.X) :
    pointExtension G (toUnit _ ≫ x : Points G.X (CommAlgCat.of k K)) =
      scalarExtendedRationalPoint K x := by
  let i : (Over.map (fieldSpecMap k K)).obj (𝟙_ (SchemeOver K)) ⟶
      (testSpec k).obj (op (CommAlgCat.of k K)) := Over.homMk (𝟙 _) (by simp)
  change adjointSections G _ (i ≫ (toUnit _ ≫ x)) = _
  rw [← Category.assoc, comp_toUnit, adjointSections_constant]
  rw [show toUnit (𝟙_ (SchemeOver K)) = 𝟙 _ from toUnit_unique _ _, Category.id_comp]

end Transporter

theorem separableTransporter : SeparableTransporter.{u} := by
  intro k S _ _ _ _ G _ f x y C hs hC ⟨g, hg⟩
  letI : IsSepClosed S := IsSepClosure.sep_closed k
  let L := AlgebraicClosure k
  letI : Algebra S L := f.toRingHom.toAlgebra
  let H := baseChangedAlgebraicGroup S G
  let xS : 𝟙_ (SchemeOver S) ⟶ ((groupBaseChange k S).obj G.val).X := scalarExtendedRationalPoint S x
  let yS : 𝟙_ (SchemeOver S) ⟶ ((groupBaseChange k S).obj G.val).X := extendedPoint y
  let q := fieldSpecMap k S
  let v := fieldSpecMap S L
  let W := 𝟙_ (SchemeOver L)
  let U := (Over.map v).obj W
  let F := Over.map q
  let V := (testSpec k).obj (op (CommAlgCat.of k L))
  let Y := (testSpec k).obj (op (CommAlgCat.of k S))
  have hf : v ≫ q = fieldSpecMap k L := by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k S)) =
      Spec.map (CommRingCat.ofHom (algebraMap k L))
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => f.commutes a))
  let w : F.obj U ≅ V := Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ fieldSpecMap k L = (𝟙 _ ≫ v) ≫ q
    simp only [Category.id_comp, hf])
  let j : F.obj (𝟙_ (SchemeOver S)) ⟶ Y := Over.homMk (𝟙 _) (by
    simp only [F, Over.map_obj_hom, Over.tensorUnit_hom, Category.id_comp]
    rfl)
  let r : V ⟶ Y := (testSpec k).map (CommAlgCat.ofHom f).op
  have hr : F.map (toUnit U) ≫ j = w.hom ≫ r := by
    apply Over.OverMorphism.ext
    change (toUnit U).left ≫ 𝟙 _ = 𝟙 _ ≫ v
    have he := (toUnit U).w
    change (toUnit U).left ≫ 𝟙 _ = 𝟙 _ ≫ v at he
    simpa only [Category.comp_id, Category.id_comp] using he
  let e := (precomposeIso w G.val).trans (adjointSections G.val U)
  have ex : e (toUnit V ≫ x) = toUnit U ≫ xS := by
    change adjointSections G.val U (w.hom ≫ toUnit V ≫ x) = _
    rw [← Category.assoc, comp_toUnit, adjointSections_constant]
  have ey : e (pointMap k S G.val.X f y) = toUnit U ≫ yS := by
    change adjointSections G.val U (w.hom ≫ (r ≫ y)) = _
    rw [← Category.assoc, ← hr, Category.assoc]
    change (extend (k := k) (K := S)).homEquiv U G.val.X (F.map (toUnit U) ≫ (j ≫ y)) =
      toUnit U ≫ extendedPoint y
    rw [Adjunction.homEquiv_naturality_left]
    rfl
  have hbU : e g * (toUnit U ≫ xS) * (e g)⁻¹ = toUnit U ≫ yS := by
    change g * (toUnit V ≫ x) * g⁻¹ = pointMap k S G.val.X f y at hg
    have he := congrArg e hg
    rw [map_mul, map_mul, map_inv, ex, ey] at he
    exact he
  let d := adjointSections ((groupBaseChange k S).obj G.val) W
  have hbW : d (e g) * (show W ⟶ ((groupBaseChange S L).obj ((groupBaseChange k S).obj G.val)).X from
        scalarExtendedRationalPoint L xS) * (d (e g))⁻¹ = scalarExtendedRationalPoint L yS := by
    have h (p : 𝟙_ (SchemeOver S) ⟶ ((groupBaseChange k S).obj G.val).X) :
        d (toUnit U ≫ p) = scalarExtendedRationalPoint L p := by
      change adjointSections ((groupBaseChange k S).obj G.val) W (toUnit U ≫ p) = _
      rw [adjointSections_constant, show toUnit W = 𝟙 W from toUnit_unique _ _, Category.id_comp]
    simpa only [map_mul, map_inv, h] using congrArg d hbU
  obtain ⟨b, hb⟩ := exists_transporter_point H xS yS C hC hs (d (e g)) hbW
  let eS := pointExtension (K := S) G.val
  obtain ⟨b₀, hb₀⟩ := eS.surjective b
  have hxS : eS (toUnit _ ≫ x : Points G.val.X (CommAlgCat.of k S)) = xS :=
    pointExtension_constant G.val x
  have hyS : eS y = yS := pointExtension_eq G.val y
  haveI : IsAffine G.val.X.left := G.property.1
  obtain ⟨T, hT⟩ := centralizer_exists G.val x
  refine ⟨⟨b₀, eS.injective ?_⟩, T, ?_, hT⟩
  · simpa only [map_mul, map_inv, hb₀, hxS, hyS] using hb
  · exact ⟨S, inferInstance, inferInstance, IsSepClosure.separable,
      splitCentralizer_of_conjugate G.val x T hT yS b hb C hC hs⟩

end
end LinearAlgebraicGroups.Arithmetic.StronglyRegularSeparableTransporter
