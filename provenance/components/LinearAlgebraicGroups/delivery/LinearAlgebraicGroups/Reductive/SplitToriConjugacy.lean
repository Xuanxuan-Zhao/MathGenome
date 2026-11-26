import Specs.LinearAlgebraicGroups.Reductive.SplitToriConjugacy
import Specs.LinearAlgebraicGroups.Reductive.WeylScheme
import LinearAlgebraicGroups.Reductive.MaximalToriConjugate
import LinearAlgebraicGroups.Reductive.ConnectedTorusCentralizer
import LinearAlgebraicGroups.Multiplicative.CharacterDescent
import LinearAlgebraicGroups.Descent.SmoothTorsors
import LinearAlgebraicGroups.Descent.MatrixHilbert90
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.Reductive.WeylScheme
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj MonoidAlgebra TensorProduct

universe u

namespace LinearAlgebraicGroups.Reductive.SplitToriConjugacy

open _root_.LinearAlgebraicGroups.Specs
open Specs.GeometricRadicals (IsSplitTorus IsTorus IsReductive)
open Specs.DiagonalizableGroups (groupAlgebra)
open Specs.GeometricBorelConjugacy (ConjugatesSubgroups)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

open private extendedGroupIso extendedSpecIso_natural specGroupMap_comp
  from LinearAlgebraicGroups.Affine.ClosedSubgroups

open private schemeHopfHomEquiv from LinearAlgebraicGroups.Multiplicative.CharacterDescent

private def splitCoordinates (k : Type u) [Field k] (r : ℕ) :=
  groupAlgebra k (Specs.CharacterDescent.StandardLattice.{u} r)

private def splitHopfChange (K : Type u) [Field K] [Algebra k K] (r : ℕ) :
    extendedHopf K (splitCoordinates k r) ≅ splitCoordinates K r :=
  CommHopfAlgCat.isoMk (R := K)
    (CharacterDescent.groupAlgebraBaseChange k K (Specs.CharacterDescent.StandardLattice.{u} r))

private def splitCoordinateChange (K : Type u) [Field K] [Algebra k K] (r : ℕ) :
    specGroup (splitCoordinates K r) ≅
      (groupBaseChange k K).obj (specGroup (splitCoordinates k r)) :=
  (hopfSpec (CommRingCat.of K)).mapIso (splitHopfChange (k := k) K r).op ≪≫
    extendedGroupIso K (splitCoordinates k r)

private theorem splitTorus_baseChange {T : GroupScheme k} (hT : IsSplitTorus T) :
    IsSplitTorus ((groupBaseChange k K).obj T) := by
  obtain ⟨r, ⟨e⟩⟩ := hT
  obtain ⟨a⟩ := CharacterDescent.standardSplitTorus (k := k) r
  obtain ⟨b⟩ := CharacterDescent.standardSplitTorus (k := K) r
  exact ⟨r, ⟨(groupBaseChange k K).mapIso (e ≪≫ a.symm) ≪≫
    (splitCoordinateChange (k := k) K r).symm ≪≫ b⟩⟩

private theorem splitTorus_isTorus {T : GroupScheme k} (hT : IsSplitTorus T) :
    IsTorus T :=
  ⟨k, inferInstance, inferInstance, inferInstance, splitTorus_baseChange hT⟩

private def latticeMap (k : Type u) [Field k] {r s : ℕ}
    (a : Specs.CharacterDescent.StandardLattice.{u} s →*
      Specs.CharacterDescent.StandardLattice.{u} r) :
    splitCoordinates k s ⟶ splitCoordinates k r :=
  CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom k a)

private theorem splitCoordinateChange_natural {r s : ℕ}
    (a : Specs.CharacterDescent.StandardLattice.{u} s →*
      Specs.CharacterDescent.StandardLattice.{u} r) :
    specGroupMap (latticeMap K a) ≫ (splitCoordinateChange (k := k) K s).hom =
      (splitCoordinateChange (k := k) K r).hom ≫
        (groupBaseChange k K).map (specGroupMap (latticeMap k a)) := by
  let d (n : ℕ) := splitHopfChange (k := k) K n
  have h : (d s).hom ≫ latticeMap K a = extendedHopfMap K (latticeMap k a) ≫ (d r).hom := by
    apply CommHopfAlgCat.hom_ext
    apply BialgHom.coe_toAlgHom_injective
    letI : Algebra k (splitCoordinates K r) :=
      inferInstanceAs (Algebra k (MonoidAlgebra K (Specs.CharacterDescent.StandardLattice.{u} r)))
    letI : IsScalarTower k K (splitCoordinates K r) :=
      inferInstanceAs (IsScalarTower k K (MonoidAlgebra K (Specs.CharacterDescent.StandardLattice.{u} r)))
    apply Algebra.TensorProduct.ext_ring
    apply MonoidAlgebra.algHom_ext
    · intro m
      change MonoidAlgebra.mapDomainBialgHom K a
        (MonoidAlgebra.scalarTensorEquiv k K ((1 : K) ⊗ₜ[k] MonoidAlgebra.single m (1 : k))) =
        MonoidAlgebra.scalarTensorEquiv k K
          ((1 : K) ⊗ₜ[k] MonoidAlgebra.mapDomainBialgHom k a (MonoidAlgebra.single m (1 : k)))
      have eq {M : Type u} [CommGroup M] (v : M) :
          MonoidAlgebra.scalarTensorEquiv k K ((1 : K) ⊗ₜ[k] MonoidAlgebra.single v (1 : k)) =
            MonoidAlgebra.single v (1 : K) :=
        (MonoidAlgebra.scalarTensorEquiv k K (M := M)).toEquiv.eq_symm_apply.mp
          (MonoidAlgebra.scalarTensorEquiv_symm_single (R := k) (A := K) v 1).symm
      simp only [eq, MonoidAlgebra.mapDomainBialgHom_single]
    · ext
  have hn : specGroupMap (extendedHopfMap K (latticeMap k a)) ≫
        (extendedGroupIso K (splitCoordinates k s)).hom =
      (extendedGroupIso K (splitCoordinates k r)).hom ≫
        (groupBaseChange k K).map (specGroupMap (latticeMap k a)) :=
    Grp.hom_ext _ _ (extendedSpecIso_natural K (latticeMap k a))
  change specGroupMap (latticeMap K a) ≫ specGroupMap (d s).hom ≫
      (extendedGroupIso K _).hom = (specGroupMap (d r).hom ≫ (extendedGroupIso K _).hom) ≫ _
  rw [Category.assoc, ← hn, ← Category.assoc, ← Category.assoc,
    ← specGroupMap_comp, ← specGroupMap_comp, h]

private theorem splitTorus_hom_descends {T T' : GroupScheme k}
    (hT : IsSplitTorus T) (hT' : IsSplitTorus T') :
    Function.Surjective
      (fun f : T ⟶ T' ↦ (groupBaseChange k K).map f) := by
  intro f
  obtain ⟨r, ⟨e⟩⟩ := hT
  obtain ⟨s, ⟨e'⟩⟩ := hT'
  obtain ⟨d⟩ := CharacterDescent.standardSplitTorus (k := k) r
  obtain ⟨d'⟩ := CharacterDescent.standardSplitTorus (k := k) s
  let S := e ≪≫ d.symm
  let S' := e' ≪≫ d'.symm
  let F := groupBaseChange k K
  let c := splitCoordinateChange (k := k) K r ≪≫ (F.mapIso S).symm
  let c' := splitCoordinateChange (k := k) K s ≪≫ (F.mapIso S').symm
  let b := (schemeHopfHomEquiv (splitCoordinates K s) (splitCoordinates K r)).symm
    (c.hom ≫ f ≫ c'.inv)
  obtain ⟨a, ha⟩ := (MonoidAlgebra.mapDomainBialgHomEquiv (R := K)).surjective b.hom
  have hab : latticeMap K a = b := CommHopfAlgCat.hom_ext ha
  have hf : specGroupMap (latticeMap K a) = c.hom ≫ f ≫ c'.inv := by
    rw [hab]
    exact (schemeHopfHomEquiv _ _).apply_symm_apply _
  refine ⟨S.hom ≫ specGroupMap (latticeMap k a) ≫ S'.inv, ?_⟩
  have h := splitCoordinateChange_natural (k := k) (K := K) a
  have ec : c.hom ≫ F.map S.hom = (splitCoordinateChange (k := k) K r).hom := by
    change (_ ≫ F.map S.inv) ≫ F.map S.hom = _
    rw [Category.assoc, ← F.map_comp, S.inv_hom_id, F.map_id, Category.comp_id]
  have ec' : F.map S'.inv ≫ c'.inv = (splitCoordinateChange (k := k) K s).inv := by
    change F.map S'.inv ≫ F.map S'.hom ≫ _ = _
    rw [← Category.assoc, ← F.map_comp, S'.inv_hom_id, F.map_id, Category.id_comp]
  change F.map (S.hom ≫ specGroupMap (latticeMap k a) ≫ S'.inv) = f
  rw [Functor.map_comp, Functor.map_comp]
  apply (cancel_epi c.hom).mp
  apply (cancel_mono c'.inv).mp
  calc
    _ = (c.hom ≫ F.map S.hom) ≫
        F.map (specGroupMap (latticeMap k a)) ≫ (F.map S'.inv ≫ c'.inv) := by
      simp only [Category.assoc]
    _ = _ := by
      rw [ec, ec', ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      exact hf


open private mono_over comp_conjugateFamily centralizes_iff familyFactorizationLocus
  conjugation whisker_conjugation extensionAdj adjoint_family
  prodComparison_inv_fst conjugation_baseChange
  from LinearAlgebraicGroups.Affine.Stabilizers

open private isIso_over_product_map from LinearAlgebraicGroups.Affine.FixedPointSchemes

private theorem splitTorus_commute {T : GroupScheme k} (hT : IsSplitTorus T)
    {Y : SchemeOver k} (a b : Y ⟶ T.X) : Commute a b := by
  obtain ⟨r, ⟨e⟩⟩ := hT
  obtain ⟨d⟩ := CharacterDescent.standardSplitTorus (k := k) r
  let i := e ≪≫ d.symm
  have hc : IsCommMonObj (specGroup (splitCoordinates k r)).X :=
    (hopfSpecCommutativity k (splitCoordinates k r)).2
      (inferInstanceAs (Coalgebra.IsCocomm k (MonoidAlgebra k (Specs.CharacterDescent.StandardLattice.{u} r))))
  have := (isCommMonObj_iff_isMulCommutative _ |>.mp hc) Y
  let f := i.hom.hom.hom
  apply (commute_iff_eq _ _).2
  apply (cancel_mono f).mp
  rw [MonObj.mul_comp, MonObj.mul_comp]
  exact mul_comm' _ _

/-- The connected centralizer has constant image in the split Weyl group.
Evaluation at the identity identifies this constant with the neutral label. -/
private theorem centralizer_of_split_maximal
    (weyl : Specs.WeylScheme.Statement.{u}) (G : AffineAlgebraicGroup k)
    (hG : IsReductive G) (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group)
    (hmax : ∃ h, GeometricRadicals.IsMaximalTorus
      (GeometricRadicals.baseChangedSubgroup (AlgebraicClosure k) T h)) :
    Smooth T.group.X.hom ∧
      RepresentsSubgroup T (fun _ g ↦ Centralizes T.inclusion g) := by
  letI : Smooth G.val.X.hom := hG.1
  letI : GeometricallyConnected G.val.X.hom := hG.2.1
  letI : ConnectedSpace G.val.X.left := GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom
  have ht := splitTorus_isTorus hT
  have ht' : LinearAlgebraicGroups.CocharacterDynamics.IsTorusSubgroup T := by
    obtain ⟨L, _, _, _, r, hr⟩ := ht
    exact ⟨L, ‹Field L›, ‹Algebra k L›, ‹Algebra.IsSeparable k L›, r, hr⟩
  obtain ⟨C, hC, hsC, hcC⟩ :=
    LinearAlgebraicGroups.CocharacterDynamics.connectedTorusCentralizer G T ht'
  obtain ⟨N, j, _, W, q, hN, hj, hq, _, _, _, hw⟩ := weyl G hG T ht hmax
  obtain ⟨⟨d⟩, _⟩ := hw hT
  letI : GeometricallyConnected C.group.X.hom := hcC
  letI : ConnectedSpace C.group.X.left := GeometricallyConnected.connectedSpace_of_subsingleton C.group.X.hom
  have hc : Centralizes T.inclusion C.inclusion.hom.hom := (hC _ _).2 ⟨𝟙 _, Category.id_comp _⟩
  have hn : Normalizes T.inclusion C.inclusion.hom.hom :=
    ⟨Iso.refl _, Category.id_comp _, (Category.id_comp _).trans hc.symm⟩
  obtain ⟨n, hn⟩ := (hN _ _).1 hn
  haveI : Mono N.inclusion.hom.hom := mono_over _ N.isClosedImmersion
  have hne : (1 : 𝟙_ (SchemeOver k) ⟶ C.group.X) ≫ n = 1 := by
    apply (cancel_mono N.inclusion.hom.hom).mp
    rw [Category.assoc, hn, MonObj.one_comp, MonObj.one_comp]
  let e : 𝟙_ (SchemeOver k) ⟶ C.group.X := 1
  let x : C.group.X.left := e.left (IsLocalRing.closedPoint k)
  have hnx : d.constantGroup.families C.group.X (n ≫ q.hom.hom) x = 1 := by
    have h := d.constantGroup.naturality e (n ≫ q.hom.hom)
    rw [← Category.assoc, show e ≫ n = 1 from hne, MonObj.one_comp, map_one] at h
    exact (LocallyConstant.congr_fun h (IsLocalRing.closedPoint k)).symm
  have hnq : n ≫ q.hom.hom = toUnit _ ≫ η[W.val.X] := by
    apply (d.constantGroup.families _).injective
    rw [← Hom.one_def, map_one]
    apply LocallyConstant.ext
    intro y
    exact ((d.constantGroup.families C.group.X (n ≫ q.hom.hom)).apply_eq_of_preconnectedSpace y x).trans hnx
  have pb : IsPullback j.hom.hom (toUnit T.group.X) q.hom.hom η[W.val.X] := hq.1
  haveI : Mono T.inclusion.hom.hom := mono_over _ T.isClosedImmersion
  haveI : Mono C.inclusion.hom.hom := mono_over _ C.isClosedImmersion
  let a := pb.lift n (toUnit _) hnq
  have ha : a ≫ T.inclusion.hom.hom = C.inclusion.hom.hom := by
    have hj' := congrArg (fun f : T.group ⟶ G.val ↦ f.hom.hom) hj
    change j.hom.hom ≫ N.inclusion.hom.hom = _ at hj'
    rw [← hj', IsPullback.lift_fst_assoc, hn]
  have hcomm (Y : SchemeOver k) (t : Y ⟶ T.group.X) :
      Centralizes T.inclusion (t ≫ T.inclusion.hom.hom) := by
    refine (centralizes_iff _ _).2 (fun U p s ↦ ?_)
    rw [← Category.assoc]
    let m := ((yonedaGrp.map T.inclusion).app (op U)).hom
    exact (splitTorus_commute hT (p ≫ t) s).map m
  obtain ⟨b, hb⟩ := (hC _ _).1 (by simpa only [Category.id_comp] using hcomm _ (𝟙 _))
  let i : T.group.X ≅ C.group.X :=
    ⟨b, a, (cancel_mono T.inclusion.hom.hom).mp (by rw [Category.assoc, ha, hb, Category.id_comp]),
     (cancel_mono C.inclusion.hom.hom).mp (by rw [Category.assoc, hb, ha, Category.id_comp])⟩
  have h : Smooth (i.hom.left ≫ C.group.X.hom) := by
    letI := hsC
    letI : IsIso i.hom := ⟨⟨i.inv, i.hom_inv_id, i.inv_hom_id⟩⟩
    letI : IsIso i.hom.left := (Over.forget _).map_isIso i.hom
    infer_instance
  refine ⟨Over.w i.hom ▸ h, fun Y g ↦ ?_⟩
  constructor
  · intro hg
    obtain ⟨c, rfl⟩ := (hC _ _).1 hg
    exact ⟨c ≫ a, by rw [Category.assoc, ha]⟩
  · rintro ⟨t, rfl⟩
    exact hcomm Y t

variable {S H : GroupScheme k}

/-- The locus for a prescribed homomorphism, expressed without a choice of
coordinates on either group. -/
private def Intertwines (i j : S ⟶ H) {Y : SchemeOver k} (p : Y ⟶ H.X) : Prop :=
  conjugateFamily i p = fst S.X Y ≫ j.hom.hom

private theorem intertwines_iff {i j : S ⟶ H} {Y : SchemeOver k} {p : Y ⟶ H.X} :
    Intertwines i j p ↔ ∀ (U : SchemeOver k) (t : U ⟶ Y) (s : U ⟶ S.X),
      (t ≫ p) * (s ≫ i.hom.hom) * (t ≫ p)⁻¹ = s ≫ j.hom.hom := by
  constructor
  · intro h U t s
    simpa only [comp_conjugateFamily, lift_snd_assoc, lift_fst_assoc] using
      congrArg (lift s t ≫ ·) h
  · intro h
    simpa only [Intertwines, conjugateFamily] using h (S.X ⊗ Y) (snd _ _) (fst _ _)

private theorem intertwines_mul {i j : S ⟶ H} {Y : SchemeOver k}
    {p t : Y ⟶ H.X} (hp : Intertwines i j p) (ht : Centralizes i t) :
    Intertwines i j (p * t) := by
  apply intertwines_iff.mpr
  intro U a s
  have h := (centralizes_iff i t).mp ht U a s
  rw [MonObj.comp_mul, _root_.mul_inv_rev]
  calc
    _ = (a ≫ p) * ((a ≫ t) * (s ≫ i.hom.hom) * (a ≫ t)⁻¹) * (a ≫ p)⁻¹ := by
      simp only [mul_assoc]
    _ = s ≫ j.hom.hom := by
      rw [h.eq, mul_inv_cancel_right]
      exact intertwines_iff.mp hp U a s

private theorem centralizes_displacement {i j : S ⟶ H} {Y : SchemeOver k}
    {p q : Y ⟶ H.X} (hp : Intertwines i j p) (hq : Intertwines i j q) :
    Centralizes i (p⁻¹ * q) := by
  apply (centralizes_iff _ _).mpr
  intro U a s
  have h := (intertwines_iff.mp hq U a s).trans (intertwines_iff.mp hp U a s).symm
  rw [MonObj.comp_mul, GrpObj.comp_inv]
  apply (commute_iff_eq _ _).2
  calc
    _ = (a ≫ p)⁻¹ * (((a ≫ q) * (s ≫ i.hom.hom) * (a ≫ q)⁻¹) * (a ≫ q)) := by group
    _ = _ := by rw [h]; group

private theorem intertwines_rational {i j : S ⟶ H}
    {p : 𝟙_ (SchemeOver k) ⟶ H.X} :
    Intertwines i j p ↔
      (toUnit S.X ≫ p) * i.hom.hom * (toUnit S.X ≫ p)⁻¹ = j.hom.hom := by
  constructor
  · intro hp
    simpa only [Category.id_comp] using intertwines_iff.mp hp S.X (toUnit S.X) (𝟙 S.X)
  · intro hp
    apply intertwines_iff.mpr
    intro U t s
    have ht : t = toUnit U := toUnit_unique t (toUnit U)
    subst t
    have h := congrArg (s ≫ ·) hp
    simpa only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, comp_toUnit] using h

private theorem intertwines_baseChange (i j : S ⟶ H)
    {U : SchemeOver K} (p : U ⟶ ((groupBaseChange k K).obj H).X) :
    Intertwines ((groupBaseChange k K).map i) ((groupBaseChange k K).map j) p ↔
      Intertwines i j (((extensionAdj (k := k) K).homEquiv U H.X).symm p) := by
  let F := baseChange k K
  let L := Over.map (fieldSpecMap k K)
  let adj := extensionAdj (k := k) K
  let b := lift (L.map (fst (F.obj S.X) U) ≫ adj.counit.app S.X) (L.map (snd (F.obj S.X) U))
  haveI : IsIso b := isIso_over_product_map (fieldSpecMap k K) S.X U
  let p' : U ⟶ F.obj H.X := p
  let q : S.X ⊗ H.X ⟶ H.X := fst S.X H.X ≫ j.hom.hom
  have eq : (prodComparisonIso F S.X H.X).inv ≫ F.map q =
      fst (F.obj S.X) (F.obj H.X) ≫ F.map j.hom.hom := by
    rw [Functor.map_comp, ← Category.assoc, prodComparison_inv_fst]
  have ep : conjugateFamily ((groupBaseChange k K).map i) p =
      (F.obj S.X ◁ p') ≫ (prodComparisonIso F S.X H.X).inv ≫ F.map (conjugation i) := by
    rw [conjugation_baseChange K i]
    exact (whisker_conjugation ((groupBaseChange k K).map i) p).symm
  change conjugateFamily ((groupBaseChange k K).map i) p =
    fst (F.obj S.X) U ≫ F.map j.hom.hom ↔ Intertwines i j ((adj.homEquiv U H.X).symm p')
  rw [ep, ← whiskerLeft_fst_assoc (F.obj S.X) p',
    ← eq, ← (adj.homEquiv (F.obj S.X ⊗ U) H.X).symm.injective.eq_iff]
  erw [adjoint_family K (conjugation i) p', adjoint_family K q p']
  change b ≫ _ = b ≫ _ ↔ _
  rw [cancel_epi, whisker_conjugation]
  simp only [Intertwines, q, whiskerLeft_fst_assoc]
  rfl

private theorem intertwiner_locus (G : AffineAlgebraicGroup k) (T : ClosedSubgroup G.val)
    (j : T.group ⟶ G.val) :
    ∃ (P : SchemeOver k) (p : P ⟶ G.val.X), IsClosedImmersion p.left ∧
      ∀ Y (g : Y ⟶ G.val.X), Intertwines T.inclusion j g ↔ ∃ y : Y ⟶ P, y ≫ p = g := by
  let i := T.inclusion
  haveI : IsAffine G.val.X.left := G.property.1
  haveI : IsAffine T.group.X.left := (Unipotent.closedSubgroupAlgebraicGroup T).property.1
  letI : IsSeparated G.val.X.hom := IsSeparated.of_isAffineHom _
  let f := conjugation i
  let g := fst T.group.X G.val.X ≫ j.hom.hom
  let d := equalizer.ι f g
  obtain ⟨P, p, hp, h⟩ := familyFactorizationLocus d (inferInstanceAs (IsClosedImmersion d.left))
  refine ⟨P, p, hp, fun Y y ↦ ?_⟩
  rw [← h]
  have eq : Intertwines i j y ↔ (T.group.X ◁ y) ≫ f = (T.group.X ◁ y) ≫ g := by
    simp [f, g, Intertwines, whisker_conjugation]
  change Intertwines i j y ↔ _
  rw [eq]
  refine ⟨fun he ↦ ⟨equalizer.lift _ he, equalizer.lift_ι _ _⟩, ?_⟩
  rintro ⟨t, ht⟩
  rw [← ht, Category.assoc, Category.assoc, equalizer.condition]

open private cover_coversTop fieldHom_left from LinearAlgebraicGroups.Descent.AffineTorsorDescent

open Specs.Fppf in
/-- A nonempty locus of intertwiners is a right torsor when the given torus
represents the scheme centralizer. -/
private theorem intertwiner_torsor (G : AffineAlgebraicGroup k)
    (T : ClosedSubgroup G.val) (j : T.group ⟶ G.val)
    (hC : RepresentsSubgroup T (fun _ g ↦ Centralizes T.inclusion g))
    {P : SchemeOver k} (p : P ⟶ G.val.X) (hp : IsClosedImmersion p.left)
    (hP : ∀ Y (g : Y ⟶ G.val.X),
      Intertwines T.inclusion j g ↔ ∃ y : Y ⟶ P, y ≫ p = g)
    (hne : Nonempty P.left) :
    ∃ X : FppfTorsor (fieldBase k) T.group,
      ∀ U : Over (fieldBase k), X.val.Section U = ULift.{u+1} (U ⟶ Over.mk (toUnit P)) := by
  let X : Over (fieldBase k) := Over.mk (toUnit P)
  let i := T.inclusion.hom.hom
  letI : Mono p := mono_over _ hp
  letI : Mono i := mono_over _ T.isClosedImmersion
  have h (Y : SchemeOver k) (a : Y ⟶ P) (t : Y ⟶ T.group.X) :
      ∃ b : Y ⟶ P, b ≫ p = (a ≫ p) * (t ≫ i) :=
    (hP _ _).1 (intertwines_mul ((hP _ _).2 ⟨a, rfl⟩) ((hC _ _).2 ⟨t, rfl⟩))
  let move {Y : Over (fieldBase k)} (a : Y ⟶ X) (t : Y.left ⟶ T.group.X) : Y ⟶ X :=
    Over.homMk (h Y.left a.left t).choose (Over.mkIdTerminal.hom_ext _ _)
  have hm {Y : Over (fieldBase k)} (a : Y ⟶ X) (t : Y.left ⟶ T.group.X) :
      (move a t).left ≫ p = (a.left ≫ p) * (t ≫ i) :=
    (h _ _ _).choose_spec
  have test {Y : Over (fieldBase k)} {a b : Y ⟶ X} (e : a.left ≫ p = b.left ≫ p) : a = b :=
    Over.OverMorphism.ext ((cancel_mono p).1 e)
  let A : SchemeAction (fieldBase k) T.group :=
    { sheaf := representedSheaf X
      act := fun a t ↦ ⟨move a.down t.down⟩
      act_one := fun a ↦ ULift.ext (test (by
        rw [hm]
        change (a.down.left ≫ p) * ((1 : _ ⟶ T.group.X) ≫ i) = a.down.left ≫ p
        rw [MonObj.one_comp, mul_one]))
      act_mul := fun a t s ↦ ULift.ext (test (by
        change (move (move a.down t.down) s.down).left ≫ p =
          (move a.down (t.down * s.down)).left ≫ p
        rw [hm, hm, hm, MonObj.mul_comp, mul_assoc]))
      map_act := fun f a t ↦ ULift.ext (test (by
        change (f.left ≫ (move a.down t.down).left) ≫ p =
          (move (f ≫ a.down) (f.left ≫ t.down)).left ≫ p
        rw [Category.assoc, hm, hm, MonObj.comp_mul]
        simp only [Over.comp_left, Category.assoc])) }
  refine ⟨⟨A, ?_, ?_⟩, fun _ ↦ rfl⟩
  · intro Y a
    constructor
    · intro s t e
      have he := congrArg (fun b : ULift.{u+1} (Y ⟶ X) ↦ b.down.left ≫ p) e
      change (move a.down s.down).left ≫ p = (move a.down t.down).left ≫ p at he
      rw [hm, hm, mul_right_inj, cancel_mono] at he
      exact ULift.ext he
    · intro b
      have hc : Centralizes T.inclusion ((a.down.left ≫ p)⁻¹ * (b.down.left ≫ p)) :=
        centralizes_displacement ((hP _ _).2 ⟨a.down.left, rfl⟩) ((hP _ _).2 ⟨b.down.left, rfl⟩)
      obtain ⟨t, ht⟩ := (hC _ _).1 hc
      refine ⟨⟨t⟩, ULift.ext (test ?_)⟩
      change (move a.down t).left ≫ p = _
      rw [hm, ht, mul_inv_cancel_left]
  · haveI : IsClosedImmersion p.left := hp
    haveI : LocallyOfFiniteType G.val.X.hom := G.property.2.1
    haveI : LocallyOfFiniteType P.hom := by rw [← Over.w p]; infer_instance
    have hf : IsFppf X.hom.left := by
      rw [fieldHom_left]
      change IsFppf P.hom
      exact ⟨inferInstance, ⟨fun z ↦ ⟨Classical.choice hne, Subsingleton.elim _ _⟩⟩, inferInstance⟩
    intro Y
    refine (torsorTopology (fieldBase k)).superset_covering ?_ (cover_coversTop hf Y)
    rintro Z f ⟨l, ⟨a⟩⟩
    exact ⟨⟨a⟩⟩

open private scheme_coboundaries neutral_of_coboundaries
  from LinearAlgebraicGroups.Descent.MatrixHilbert90

open LinearAlgebraicGroups.Descent.MatrixHilbert90
open LinearAlgebraicGroups.Descent.NonabelianCohomology (pointAction)

private theorem splitTorus_coboundaries (S : Type u) [Field S] [Algebra k S]
    [IsSepClosure k S] {T : GroupScheme k} (hT : IsSplitTorus T) :
    AllContinuousCoboundaries (pointAction k S T.X) := by
  obtain ⟨r, ⟨e⟩⟩ := hT
  let I := ULift.{u} (Fin r)
  apply scheme_coboundaries ((groupPointsFunctor k).mapIso e ≪≫
    LinearAlgebraicGroups.StandardGroups.multiplicativePowerGroupPointsIso k I)
  intro L a ha
  let b (i : I) (σ : Gal(L/k)) : Lˣ := a σ i
  have hb (i : I) : groupCohomology.IsMulCocycle₁ (b i) := by
    intro σ τ
    have h := congrFun (ha σ τ) i
    change b i (σ * τ) = b i σ * Units.map σ.toAlgHom.toMonoidHom (b i τ) at h
    change b i (σ * τ) = Units.map σ.toAlgHom.toMonoidHom (b i τ) * b i σ
    rw [h, mul_comm]
  choose c hc using fun i ↦
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units _ (hb i)
  refine ⟨c, fun σ ↦ ?_⟩
  funext i
  change b i σ = (c i)⁻¹ * Units.map σ.toAlgHom.toMonoidHom (c i)
  have h := hc i σ
  change Units.map σ.toAlgHom.toMonoidHom (c i) / c i = b i σ at h
  rw [← h, div_eq_mul_inv, mul_comm]

open Specs.Fppf in
private theorem splitTorus_torsor_point (T : AffineAlgebraicGroup k)
    (hT : IsSplitTorus T.val) (hs : Smooth T.val.X.hom) (P : FppfTorsor (fieldBase k) T.val) :
    Nonempty (P.val.Section (fieldTest k)) := by
  let S := SeparableClosure k
  obtain ⟨e, _, he⟩ :=
    LinearAlgebraicGroups.Descent.SmoothTorsors.classification (S := S) T hs
  exact (he P).1.mp (neutral_of_coboundaries (splitTorus_coboundaries S hT) (e (Quotient.mk _ P)))

private theorem groupBaseChange_map_injective {A B : GroupScheme k} {f g : A ⟶ B}
    (h : (groupBaseChange k K).map f = (groupBaseChange k K).map g) : f = g := by
  let e := fieldSpecMap k K
  letI : Surjective e := ⟨fun _ ↦ ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  letI : Flat e := by
    change Flat (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    rw [Flat.SpecMap_iff]
    letI : Algebra k K := (CommRingCat.ofHom (algebraMap k K)).hom.toAlgebra
    exact Module.Flat.of_free (R := k) (M := K)
  letI : QuasiCompact e := inferInstanceAs (QuasiCompact (Spec.map _))
  letI : (baseChange k K).Faithful := inferInstanceAs ((Over.pullback e).Faithful)
  apply Grp.hom_ext
  exact (baseChange k K).map_injective (congrArg (fun a ↦ a.hom.hom) h)

/-- Conditional rational conjugacy for split geometrically maximal tori. -/
theorem splitToriConjugacy_conditional :
    Specs.WeylScheme.Statement.{u} → Specs.SplitToriConjugacy.Statement.{u} := by
  intro weyl k _ G hG T T' hT hT' ⟨ht, hmax⟩ ⟨ht', hmax'⟩
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let Gₖ := GeometricRadicals.GeometricGroup G
  letI : GeometricallyConnected G.val.X.hom := hG.1.2.1
  have hs : Smooth Gₖ.val.X.hom :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback G.val.X.hom (fieldSpecMap k K)) hG.1.1
  have hc : ConnectedSpace Gₖ.val.X.left :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _
      (IsPullback.of_hasPullback G.val.X.hom (fieldSpecMap k K))
  obtain ⟨g, e, he⟩ := LinearAlgebraicGroups.MaximalToriConjugate.maximalToriConjugate
    Gₖ hs hc _ _ hmax hmax'
  change 𝟙_ (SchemeOver K) ⟶ (F.obj G.val).X at g
  change F.obj T.group ≅ F.obj T'.group at e
  change (e.hom ≫ F.map T'.inclusion).hom.hom =
    (toUnit (F.obj T.group).X ≫ g) * (F.map T.inclusion).hom.hom *
      (toUnit (F.obj T.group).X ≫ g)⁻¹ at he
  obtain ⟨a, ha⟩ := splitTorus_hom_descends (K := K) hT hT' e.hom
  obtain ⟨b, hb⟩ := splitTorus_hom_descends (K := K) hT' hT e.inv
  change F.map a = e.hom at ha
  change F.map b = e.inv at hb
  let j : T.group ≅ T'.group :=
    { hom := a
      inv := b
      hom_inv_id := groupBaseChange_map_injective (K := K) (by
        change F.map (a ≫ b) = F.map (𝟙 T.group)
        rw [F.map_comp, ha, hb, e.hom_inv_id, F.map_id])
      inv_hom_id := groupBaseChange_map_injective (K := K) (by
        change F.map (b ≫ a) = F.map (𝟙 T'.group)
        rw [F.map_comp, hb, ha, e.inv_hom_id, F.map_id]) }
  have hg : Intertwines (F.map T.inclusion) (F.map (a ≫ T'.inclusion)) g := by
    apply intertwines_rational.2
    rw [F.map_comp, ha]
    exact he.symm
  obtain ⟨P, p, hp, hP⟩ := intertwiner_locus G T (a ≫ T'.inclusion)
  obtain ⟨v, _⟩ := (hP _ _).1 ((intertwines_baseChange T.inclusion (a ≫ T'.inclusion) g).1 hg)
  have hne : Nonempty P.left := ⟨v.left (IsLocalRing.closedPoint K)⟩
  obtain ⟨hsT, hC⟩ := centralizer_of_split_maximal weyl G hG.1 T hT ⟨ht, hmax⟩
  obtain ⟨Q, hQ⟩ := intertwiner_torsor G T _ hC p hp hP hne
  have hr := splitTorus_torsor_point (Unipotent.closedSubgroupAlgebraicGroup T) hT hsT Q
  rw [hQ] at hr
  obtain ⟨⟨x⟩⟩ := hr
  refine ⟨x.left ≫ p, j, ?_⟩
  exact (intertwines_rational.mp ((hP _ _).2 ⟨x.left, rfl⟩)).symm

end
end LinearAlgebraicGroups.Reductive.SplitToriConjugacy

universe v8_closure_454a4bf45a09f686_u0
theorem _root_.«LinearAlgebraicGroups».«Reductive».«SplitToriConjugacy».«splitToriConjugacy» : _root_.«LinearAlgebraicGroups».«Specs».«SplitToriConjugacy».«Statement».{v8_closure_454a4bf45a09f686_u0} :=
  @_root_.«LinearAlgebraicGroups».«Reductive».«SplitToriConjugacy».«splitToriConjugacy_conditional».{v8_closure_454a4bf45a09f686_u0} (@_root_.«LinearAlgebraicGroups».«Reductive».«WeylScheme».«weylScheme».{v8_closure_454a4bf45a09f686_u0})
