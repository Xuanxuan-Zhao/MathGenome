import Specs.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
import LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel
import LinearAlgebraicGroups.Solvable.LieKolchin
import LinearAlgebraicGroups.Solvable.TorusSections
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite WithConv
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.GeometricTorusSplitting

noncomputable section

open _root_.LinearAlgebraicGroups.Specs
open Specs.GeometricTorusSplitting
open Specs.SchemeDerivedGroup (IsSolvable)
open Specs.EquivariantUnipotentSeries (IsSplitTorus)
open Specs.SmoothDiagonalKernel (IsTorusGroup IsUpperTriangular)
open Specs.Unipotent (Index IsUnipotent IsFppfGroupQuotient closedSubgroupAlgebraicGroup)
open Specs.CharacterDescent (StandardLattice)
open Specs.DiagonalizableGroups (groupAlgebra)

open private groupPresentation quotientRepresentsImage schemeKernel_sections
  from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private embeds_of_flags upperHopfAlgebra UpperCoordinates quotientCoordinates
  evaluatedUpperTriangular from LinearAlgebraicGroups.Solvable.Triangularization
open private isoOfPointIso from LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel
open private kernel_of_closed_factor Unipotent.scheme_hom_spec Unipotent.onPoints
  from LinearAlgebraicGroups.Unipotent.CentralSeries
open private StandardGroups.evaluatedGeneralLinear
  from LinearAlgebraicGroups.Affine.StandardGroups
open private groupAlgebraOfCharacters groupLikeSpanOfSplit
  from LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private multiplicativeType_iff_coordinates from LinearAlgebraicGroups.Unipotent.Orthogonality

variable {k : Type u} [Field k]

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

private abbrev underlying (k : Type u) [Field k] :=
  Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))

private def triangularInclusionPoints (k : Type u) [Field k] (n : ℕ) :
    Specs.Triangularization.upperTriangularPoints k n ⟶
      Specs.StandardGroups.generalLinearPoints k (Index.{u} n) where
  app R := GrpCat.ofHom (Specs.Triangularization.upperTriangular (Index.{u} n) R).subtype
  naturality R S a := by
    ext x
    rfl

private theorem triangularInclusion (k : Type u) [Field k] (n : ℕ) :
    ∃ j : (Triangularization.upperTriangularGroup k n).val ⟶
        (StandardGroups.generalLinearGroup k (Index.{u} n)).val,
      IsClosedImmersion j.hom.hom.left ∧
      (groupPointsFunctor k).map j ≫ (StandardGroups.generalLinearGroupPointsIso k (Index n)).hom =
        (Triangularization.upperTriangularGroupPointsIso k n).hom ≫ triangularInclusionPoints k n := by
  let B := Triangularization.upperTriangularGroup k n
  let H := StandardGroups.generalLinearGroup k (Index.{u} n)
  let b := Triangularization.upperTriangularGroupPointsIso k n
  let e := StandardGroups.generalLinearGroupPointsIso k (Index.{u} n)
  let α := b.hom ≫ triangularInclusionPoints k n ≫ e.inv
  let j := (AffineAlgebraicGroup.groupHomEquiv B H).symm α
  have hj : (groupPointsFunctor k).map j = α :=
    (AffineAlgebraicGroup.groupHomEquiv B H).apply_symm_apply α
  refine ⟨j, ?_, ?_⟩
  · let q := quotientCoordinates k n
    let R := CommAlgCat.of k (UpperCoordinates k n)
    let x := (hopfSpecPointIso (upperHopfAlgebra k n)).hom.app R (toConv (AlgHom.id k _))
    letI := StandardGroups.generalLinearHopf k (Index.{u} n)
    let A := CommHopfAlgCat.of k (Specs.StandardGroups.GLCoordinates k (Index.{u} n))
    let y := (hopfSpecPointIso A).hom.app R (toConv q)
    have hxy : Unipotent.onPoints j R x = y := by
      rw [Unipotent.scheme_hom_spec (G := B) (H := H) α R x]
      apply (e.app R).groupIsoToMulEquiv.injective
      change e.hom.app R (e.inv.app R ((triangularInclusionPoints k n).app R (b.hom.app R x))) =
        e.hom.app R y
      rw [show e.hom.app R (e.inv.app R _) = _ from
        (e.app R).groupIsoToMulEquiv.apply_symm_apply _]
      have h : (hopfSpecPointIso (upperHopfAlgebra k n)).inv.app R x = toConv (AlgHom.id k _) :=
        ((hopfSpecPointIso (upperHopfAlgebra k n)).app R).groupIsoToMulEquiv.symm_apply_apply _
      have h' : (hopfSpecPointIso A).inv.app R y = toConv q :=
        ((hopfSpecPointIso A).app R).groupIsoToMulEquiv.symm_apply_apply _
      change (evaluatedUpperTriangular k n R
          ((hopfSpecPointIso (upperHopfAlgebra k n)).inv.app R x).ofConv).val =
        StandardGroups.evaluatedGeneralLinear ((hopfSpecPointIso A).inv.app R y).ofConv
      rw [h, h']
      rfl
    have hleft := congrArg (fun z : Points H.val.X R ↦ z.left) hxy
    change Spec.map (CommRingCat.ofHom (AlgHom.id k _).toRingHom) ≫ j.hom.hom.left =
      Spec.map (CommRingCat.ofHom q.toRingHom) at hleft
    rw [show CommRingCat.ofHom (AlgHom.id k _).toRingHom = 𝟙 _ from rfl, Spec.map_id,
      Category.id_comp] at hleft
    rw [hleft]
    exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  · rw [hj]
    simp [α, e, b]

private theorem triangularRealization [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (hGs : Smooth G.val.X.hom) (hGc : ConnectedSpace G.val.X.left) (hG : IsSolvable G.val) :
    ∃ (n : ℕ) (j : G.val ⟶ (StandardGroups.generalLinearGroup k (Index.{u} n)).val),
      IsClosedImmersion j.hom.hom.left ∧
      IsUpperTriangular j (StandardGroups.generalLinearGroupPointsIso k (Index n)) := by
  obtain ⟨A, _, ⟨a⟩⟩ := groupPresentation G
  obtain ⟨n, B, ⟨b⟩, f, hf⟩ := embeds_of_flags a
    (LieKolchin.invariantFullFlag G A a hGs hGc hG)
  let B' := Triangularization.upperTriangularGroup k n
  let b' := Triangularization.upperTriangularGroupPointsIso k n
  let i := isoOfPointIso B B' (b ≪≫ b'.symm)
  obtain ⟨j, hj, he⟩ := triangularInclusion k n
  refine ⟨n, f ≫ i.hom ≫ j, ?_, ?_⟩
  · letI := hf
    letI := hj
    haveI : IsIso i.hom.hom.hom.left := (underlying k).map_isIso i.hom
    exact IsClosedImmersion.comp f.hom.hom.left (i.hom.hom.hom.left ≫ j.hom.hom.left)
  · intro R x
    let e := StandardGroups.generalLinearGroupPointsIso k (Index.{u} n)
    have he' : (groupPointsFunctor k).map (f ≫ i.hom ≫ j) ≫ e.hom =
        (groupPointsFunctor k).map (f ≫ i.hom) ≫
          b'.hom ≫ triangularInclusionPoints k n := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun g ↦ (groupPointsFunctor k).map f ≫
          (groupPointsFunctor k).map i.hom ≫ g) he
    have hx := congrArg (fun m ↦ m.app R x) he'
    change e.hom.app R (Unipotent.onPoints (f ≫ i.hom ≫ j) R x) = _ at hx
    change (e.hom.app R (Unipotent.onPoints (f ≫ i.hom ≫ j) R x)).val.IsUpperTriangular
    rw [hx]
    exact (((b'.hom.app R) (Unipotent.onPoints (f ≫ i.hom) R x))).property

private theorem torus_multiplicativeType {D : AffineAlgebraicGroup k} (h : IsTorusGroup D) :
    (Specs.CharacterDescent.multiplicativeTypeSpecFunctor k).essImage D := by
  obtain ⟨A, ⟨e⟩, ht⟩ := h
  exact (multiplicativeType_iff_coordinates e).mpr (CharacterDescent.torusIsMultiplicativeType A ht)

private theorem split_of_torus [IsAlgClosed k] {D : AffineAlgebraicGroup k}
    (h : IsTorusGroup D) : IsSplitTorus D.val := by
  obtain ⟨A, ⟨e⟩, ht⟩ := h
  have hm := CharacterDescent.torusIsMultiplicativeType A ht
  have crit := CharacterDescent.torusAndSplitCriteria (K := k) A hm
  have hd : Specs.CharacterDescent.IsDiagonalizable A := crit.2.mpr (by
    intro σ x
    rw [Subsingleton.elim σ 1]
    exact (Descent.SemilinearAction.scalarExtension (K := k) A).one_act _)
  obtain ⟨r, ⟨c⟩⟩ := crit.1.mp ht
  let a := MulEquiv.ofBijective (CharacterDescent.baseChangeCharacterMap k A)
    (CharacterDescent.baseChangeCharacterMap_bijective k A hd)
  let d := CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv k k (a.trans c).symm) ≪≫
    groupAlgebraOfCharacters A (groupLikeSpanOfSplit A hd)
  obtain ⟨m⟩ := CharacterDescent.standardSplitTorus (k := k) r
  exact ⟨r, ⟨e.symm ≪≫ (hopfSpec (CommRingCat.of k)).mapIso d.op ≪≫ m⟩⟩

private theorem torus_of_split {D : AffineAlgebraicGroup k}
    (h : IsSplitTorus D.val) : IsTorusGroup D := by
  obtain ⟨r, ⟨e⟩⟩ := h
  obtain ⟨m⟩ := CharacterDescent.standardSplitTorus (k := k) r
  refine ⟨groupAlgebra k (StandardLattice.{u} r), ⟨m ≪≫ e.symm⟩, ?_⟩
  let A := groupAlgebra k (StandardLattice.{u} r)
  have eA : extendedHopf k A ≅ A :=
    CommHopfAlgCat.isoMk (CharacterDescent.groupAlgebraBaseChange k k (StandardLattice.{u} r))
  exact ⟨k, inferInstance, inferInstance, inferInstance, r, ⟨eA.symm⟩⟩

private theorem radicalQuotient [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (hGs : Smooth G.val.X.hom) (hGc : ConnectedSpace G.val.X.left) (hG : IsSolvable G.val) :
    ∃ (U : ClosedSubgroup G.val) (D : AffineAlgebraicGroup k) (p : G.val ⟶ D.val),
      IsUnipotentRadical (G := G) U ∧ IsFppfGroupQuotient U p ∧ IsSplitTorus D.val := by
  obtain ⟨n, j, hj, ht⟩ := triangularRealization G hGs hGc hG
  obtain ⟨d, _, D, p, i, U, hp, _, hk, htor, hs, hc, hn, hu, hmax⟩ :=
    SmoothDiagonalKernel.smoothDiagonalKernel n G _ _
      j (StandardGroups.generalLinearGroupPointsIso k (Index n))
      (StandardGroups.multiplicativePowerGroupPointsIso k (Index n)) hj ht hGs hGc
  refine ⟨U, D, p, ⟨hs, hc, hn, hu, hmax⟩, ?_, split_of_torus htor⟩
  exact ⟨kernel_of_closed_factor d p i hp.1 hp.2.2.2.2.2 _ hk,
    hp.2.1, hp.2.2.1, hp.2.2.2.1, quotientRepresentsImage hp hk⟩

/-- Orthogonality makes the quotient projection injective on all scheme-valued points of a torus. -/
private theorem torus_projection_mono {G D : AffineAlgebraicGroup k}
    {U : ClosedSubgroup G.val} {p : G.val ⟶ D.val} (hp : IsSchemeKernel p U)
    (hU : IsUnipotent (closedSubgroupAlgebraicGroup U))
    (T : ClosedSubgroup G.val) (hT : IsTorusGroup (closedSubgroupAlgebraicGroup T)) :
    Mono (T.inclusion ≫ p).hom.hom := by
  let P := pullback U.inclusion T.inclusion
  let b := pullback.snd U.inclusion T.inclusion
  let h := IsPullback.of_hasPullback U.inclusion T.inclusion
  let hX := h.map (Grp.forget (SchemeOver k))
  have hP : IsZero P := Unipotent.unipotentMultiplicativeTypeIntersection G U T
    (pullback.fst _ _) b h hU (torus_multiplicativeType hT)
  let e := (Grp.forget (SchemeOver k)).mapIso (hP.iso (Grp.isZero_trivial (SchemeOver k)))
  have ht : IsTerminal P.X := (isTerminalTensorUnit (C := SchemeOver k)).ofIso e.symm
  constructor
  intro X x y hxy
  let q := (T.inclusion ≫ p).hom.hom
  have hdiff : (x * y⁻¹) ≫ q = 1 := by
    rw [MonObj.mul_comp, GrpObj.inv_comp]
    exact mul_inv_eq_one.mpr hxy
  change (x * y⁻¹) ≫ (T.inclusion.hom.hom ≫ p.hom.hom) = 1 at hdiff
  obtain ⟨u, hu⟩ := (schemeKernel_sections hp ((x * y⁻¹) ≫ T.inclusion.hom.hom)).mpr
    (by simpa only [Category.assoc] using hdiff)
  let z : X ⟶ P.X := hX.lift u (x * y⁻¹) hu
  have hz : z ≫ b.hom.hom = x * y⁻¹ := hX.lift_snd _ _ _
  have hz' : z = 1 := ht.hom_ext _ _
  rw [hz', MonObj.one_comp] at hz
  exact mul_inv_eq_one.mp hz.symm

private theorem torus_projection_closed {G D : AffineAlgebraicGroup k}
    {U : ClosedSubgroup G.val} {p : G.val ⟶ D.val} (hp : IsSchemeKernel p U)
    (hU : IsUnipotent (closedSubgroupAlgebraicGroup U))
    (T : ClosedSubgroup G.val) (hT : IsTorusGroup (closedSubgroupAlgebraicGroup T)) :
    IsClosedImmersion (T.inclusion ≫ p).hom.hom.left := by
  obtain ⟨I, q, i, hi, _, _⟩ := LinearAlgebraicGroups.schemeImageFactorization
    (closedSubgroupAlgebraicGroup T) D (T.inclusion ≫ p)
  haveI : Mono (T.inclusion ≫ p).hom.hom := torus_projection_mono hp hU T hT
  haveI : Mono (q.hom.hom ≫ i.hom.hom) := by
    change Mono (q ≫ i).hom.hom
    rw [hi.1]
    infer_instance
  haveI : Mono q.hom.hom := mono_of_mono q.hom.hom i.hom.hom
  letI : Flat q.hom.hom.left := hi.2.1
  letI : Surjective q.hom.hom.left := hi.2.2.1
  letI := (closedSubgroupAlgebraicGroup (G := G) T).property.1
  letI := I.property.1
  haveI : IsIso q.hom.hom.left := Flat.isIso_of_surjective_of_mono _
  letI : IsClosedImmersion i.hom.hom.left := hi.2.2.2.2.2
  rw [← hi.1]
  exact IsClosedImmersion.comp _ _

private theorem closed_of_section {G D : AffineAlgebraicGroup k}
    {p : G.val ⟶ D.val} {s : D.val ⟶ G.val} (hs : s ≫ p = 𝟙 _) :
    IsClosedImmersion s.hom.hom.left := by
  letI := G.property.1
  letI := D.property.1
  apply IsClosedImmersion.of_surjective_of_isAffine
  have h := congrArg (fun (f : D.val ⟶ D.val) ↦ f.hom.hom.left.appTop) hs
  change (s.hom.hom.left ≫ p.hom.hom.left).appTop = Scheme.Hom.appTop (𝟙 D.val.X.left) at h
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at h
  exact fun x ↦ ⟨p.hom.hom.left.appTop x, ConcreteCategory.congr_hom h x⟩

private def conjugationBy (G : GroupScheme k) (a : 𝟙_ (SchemeOver k) ⟶ G.X) : G ⟶ G := by
  let c := toUnit G.X ≫ a
  refine Grp.homMk'' (c * 𝟙 G.X * c⁻¹) ?_ ?_
  · simp only [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, mul_one,
      MonObj.one_eq_one, mul_inv_cancel]
  · have hmul : fst G.X G.X * snd G.X G.X = μ[G.X] := by
      rw [CategoryTheory.Hom.mul_def, lift_fst_snd, Category.id_comp]
    conv_lhs => rw [← hmul]
    rw [← lift_fst_comp_snd_comp]
    change (fst G.X G.X * snd G.X G.X) ≫ (c * 𝟙 G.X * c⁻¹) =
      (fst G.X G.X ≫ (c * 𝟙 G.X * c⁻¹)) * (snd G.X G.X ≫ (c * 𝟙 G.X * c⁻¹))
    simp only [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, c, comp_toUnit_assoc]
    group

/-- Pull back the extension to the torus and compare the two sections there. -/
private theorem section_conjugates_lift [IsAlgClosed k] {G D : AffineAlgebraicGroup k}
    {U : ClosedSubgroup G.val} {p : G.val ⟶ D.val} (hp : IsFppfGroupQuotient U p)
    (hU : IsUnipotentRadical (G := G) U)
    {s : D.val ⟶ G.val} (hs : s ≫ p = 𝟙 _) (T : ClosedSubgroup G.val)
    (hT : IsTorusGroup (closedSubgroupAlgebraicGroup T)) :
    ∃ s' : D.val ⟶ G.val, s' ≫ p = 𝟙 _ ∧ (T.inclusion ≫ p) ≫ s' = T.inclusion := by
  let t := T.inclusion ≫ p
  let j := pullback.fst p t
  let q := pullback.snd p t
  let h := IsPullback.of_hasPullback p t
  let hX := h.map (Grp.forget (SchemeOver k))
  let hS := h.map (underlying k)
  have htc := torus_projection_closed hp.1 hU.2.2.2.1 T hT
  letI hjc : IsClosedImmersion j.hom.hom.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hS.flip htc
  let E := closedSubgroupAlgebraicGroup (G := G) ⟨_, j, hjc⟩
  have huz : U.inclusion ≫ p = 0 := Grp.hom_ext _ _ hp.1.w
  let v : U.group ⟶ E.val := pullback.lift U.inclusion (0 : U.group ⟶ T.group)
    (by rw [huz, zero_comp])
  have hvj : v ≫ j = U.inclusion := pullback.lift_fst _ _ _
  have hvq : v ≫ q = 0 := pullback.lift_snd _ _ _
  have hvjc : IsClosedImmersion (v.hom.hom.left ≫ j.hom.hom.left) :=
    by
      change IsClosedImmersion (v ≫ j).hom.hom.left
      rw [hvj]
      exact U.isClosedImmersion
  letI : IsClosedImmersion (v.hom.hom.left ≫ j.hom.hom.left) := hvjc
  let N : ClosedSubgroup E.val :=
    ⟨U.group, v, IsClosedImmersion.of_comp_isClosedImmersion v.hom.hom.left j.hom.hom.left⟩
  have hk : IsSchemeKernel q N := by
    have h₁ : v.hom.hom ≫ j.hom.hom = U.inclusion.hom.hom :=
      congrArg (fun f : U.group ⟶ G.val ↦ f.hom.hom) hvj
    have h₂ : η[T.group.X] ≫ t.hom.hom = η[D.val.X] := IsMonHom.one_hom _
    have h₃ : v.hom.hom ≫ q.hom.hom = toUnit U.group.X ≫ η[T.group.X] :=
      congrArg (fun f : U.group ⟶ T.group ↦ f.hom.hom) hvq
    change IsPullback v.hom.hom (toUnit _) q.hom.hom η[T.group.X]
    exact (show IsPullback (v.hom.hom ≫ j.hom.hom) (toUnit _)
      p.hom.hom (η[T.group.X] ≫ t.hom.hom) from by rw [h₁, h₂]; exact hp.1).of_right h₃ hX
  have hf : Flat q.hom.hom.left :=
    MorphismProperty.of_isPullback (P := @Flat) hS hp.2.1
  have hsurj : Surjective q.hom.hom.left :=
    MorphismProperty.of_isPullback (P := @Surjective) hS hp.2.2.1
  have ht₁ : (t ≫ s) ≫ p = 𝟙 T.group ≫ t := by simp [Category.assoc, hs]
  have ht₂ : T.inclusion ≫ p = 𝟙 T.group ≫ t := by simp [t]
  let s₁ : T.group ⟶ E.val := pullback.lift (t ≫ s) (𝟙 T.group) ht₁
  let s₂ : T.group ⟶ E.val := pullback.lift T.inclusion (𝟙 T.group) ht₂
  have hs₁q : s₁ ≫ q = 𝟙 _ := pullback.lift_snd _ _ _
  have hs₂q : s₂ ≫ q = 𝟙 _ := pullback.lift_snd _ _ _
  obtain ⟨a, ha⟩ := (TorusSections.splitTorusExtension E (closedSubgroupAlgebraicGroup T)
    N q hk hf hsurj (split_of_torus hT) hU.1 hU.2.1 hU.2.2.2.1).2 s₁ s₂ hs₁q hs₂q
  let b := a ≫ U.inclusion.hom.hom
  let c := conjugationBy G.val b
  let s' := s ≫ c
  have hc : c ≫ p = p := by
    apply Grp.hom_ext
    change ((toUnit G.val.X ≫ b) * 𝟙 G.val.X * (toUnit G.val.X ≫ b)⁻¹) ≫
      p.hom.hom = p.hom.hom
    have hkill : U.inclusion.hom.hom ≫ p.hom.hom = 1 := hp.1.w
    simp only [MonObj.mul_comp, GrpObj.inv_comp, b, Category.id_comp, Category.assoc, hkill,
      MonObj.comp_one, inv_one, one_mul, mul_one]
  refine ⟨s', by simp [s', Category.assoc, hc, hs], ?_⟩
  have h₁ : s₁.hom.hom ≫ j.hom.hom = t.hom.hom ≫ s.hom.hom :=
    congrArg (fun f : T.group ⟶ G.val ↦ f.hom.hom) (pullback.lift_fst _ _ _)
  have h₂ : s₂.hom.hom ≫ j.hom.hom = T.inclusion.hom.hom :=
    congrArg (fun f : T.group ⟶ G.val ↦ f.hom.hom) (pullback.lift_fst _ _ _)
  have h₃ : v.hom.hom ≫ j.hom.hom = U.inclusion.hom.hom :=
    congrArg (fun f : U.group ⟶ G.val ↦ f.hom.hom) hvj
  have he := congrArg (fun f : T.group.X ⟶ E.val.X ↦ f ≫ j.hom.hom) ha
  change (s₂.hom.hom ≫ j.hom.hom) =
    ((toUnit T.group.X ≫ a ≫ v.hom.hom) * s₁.hom.hom *
      (toUnit T.group.X ≫ a ≫ v.hom.hom)⁻¹) ≫ j.hom.hom at he
  simp only [MonObj.mul_comp, GrpObj.inv_comp, h₁, h₂, Category.assoc, h₃] at he
  apply Grp.hom_ext
  change t.hom.hom ≫ s.hom.hom ≫
    ((toUnit G.val.X ≫ b) * 𝟙 G.val.X * (toUnit G.val.X ≫ b)⁻¹) = _
  simpa only [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, ← Category.assoc,
    comp_toUnit, b] using he.symm

private theorem iso_projection_of_maximal [IsAlgClosed k] {G D : AffineAlgebraicGroup k}
    {U : ClosedSubgroup G.val} {p : G.val ⟶ D.val} (hp : IsFppfGroupQuotient U p)
    (hU : IsUnipotentRadical (G := G) U) (hD : IsSplitTorus D.val)
    {s : D.val ⟶ G.val} (hs : s ≫ p = 𝟙 _) (T : ClosedSubgroup G.val)
    (hT : IsMaximalTorus (G := G) T) : IsIso (T.inclusion ≫ p) := by
  obtain ⟨s', hs', ht⟩ := section_conjugates_lift hp hU hs T hT.1
  let S : ClosedSubgroup G.val := ⟨D.val, s', closed_of_section hs'⟩
  have hS : IsTorusGroup (closedSubgroupAlgebraicGroup S) := torus_of_split hD
  obtain ⟨f, hf⟩ := hT.2 S hS ⟨T.inclusion ≫ p, ht⟩
  change f ≫ T.inclusion = s' at hf
  have hleft : f ≫ (T.inclusion ≫ p) = 𝟙 D.val := by
    rw [← Category.assoc, hf, hs']
  haveI : Mono (T.inclusion ≫ p).hom.hom := torus_projection_mono hp.1 hU.2.2.2.1 T hT.1
  have hright : (T.inclusion ≫ p) ≫ f = 𝟙 T.group := by
    apply Grp.hom_ext
    apply (cancel_mono (T.inclusion ≫ p).hom.hom).mp
    change (((T.inclusion ≫ p) ≫ f) ≫ (T.inclusion ≫ p)).hom.hom = _
    rw [Category.assoc, hleft, Category.comp_id]
    change _ = 𝟙 T.group.X ≫ _
    rw [Category.id_comp]
  exact ⟨⟨f, hright, hleft⟩⟩

private theorem maximal_of_iso_projection {G D : AffineAlgebraicGroup k}
    {U : ClosedSubgroup G.val} {p : G.val ⟶ D.val} (hp : IsSchemeKernel p U)
    (hU : IsUnipotent (closedSubgroupAlgebraicGroup U)) (hD : IsSplitTorus D.val)
    (T : ClosedSubgroup G.val) [IsIso (T.inclusion ≫ p)] : IsMaximalTorus (G := G) T := by
  refine ⟨torus_of_split ?_, ?_⟩
  · obtain ⟨r, ⟨e⟩⟩ := hD
    exact ⟨r, ⟨asIso (T.inclusion ≫ p) ≪≫ e⟩⟩
  · rintro S hS ⟨j, hj⟩
    let f := S.inclusion ≫ p
    let v := inv (T.inclusion ≫ p) ≫ j
    have hv : v ≫ f = 𝟙 D.val := by
      simpa only [v, f, Category.assoc, reassoc_of% hj] using
        IsIso.inv_hom_id (T.inclusion ≫ p)
    haveI : Mono f.hom.hom := torus_projection_mono hp hU S hS
    have hcancel : f ≫ v = 𝟙 S.group := by
      apply Grp.hom_ext
      apply (cancel_mono f.hom.hom).mp
      change ((f ≫ v) ≫ f).hom.hom = _
      rw [Category.assoc, hv, Category.comp_id]
      rfl
    refine ⟨f ≫ inv (T.inclusion ≫ p), ?_⟩
    simpa only [v, Category.assoc, hj, Category.id_comp] using
      congrArg (· ≫ S.inclusion) hcancel

/-- The inverse uses the torus coordinate of the quotient and the residual kernel coordinate. -/
private theorem product_isIso {G D : AffineAlgebraicGroup k} {U T : ClosedSubgroup G.val}
    {p : G.val ⟶ D.val} (hp : IsSchemeKernel p U) [IsIso (T.inclusion ≫ p)] :
    IsIso (subgroupProduct U T) := by
  let j := U.inclusion.hom.hom
  let t := T.inclusion.hom.hom
  let f := p.hom.hom
  let s := (inv (T.inclusion ≫ p)).hom.hom
  let q := f ≫ s
  let a : G.val.X ⟶ G.val.X := 𝟙 G.val.X * (q ≫ t)⁻¹
  have hj : j ≫ f = 1 := hp.w
  have hts : (t ≫ f) ≫ s = 𝟙 T.group.X :=
    congrArg (fun h : T.group ⟶ T.group ↦ h.hom.hom) (IsIso.hom_inv_id (T.inclusion ≫ p))
  have hst : s ≫ t ≫ f = 𝟙 D.val.X :=
    congrArg (fun h : D.val ⟶ D.val ↦ h.hom.hom) (IsIso.inv_hom_id (T.inclusion ≫ p))
  have ha : a ≫ f = 1 := by
    simp only [a, q, MonObj.mul_comp, GrpObj.inv_comp, Category.id_comp, Category.assoc,
      hst, Category.comp_id, mul_inv_cancel]
  let r := hp.lift a (toUnit _) ha
  have hr : r ≫ j = a := hp.lift_fst _ _ _
  let m := subgroupProduct U T
  have hjq : j ≫ q = 1 := by
    rw [show q = f ≫ s from rfl, ← Category.assoc, hj, MonObj.one_comp]
  have htq : t ≫ q = 𝟙 T.group.X := (Category.assoc _ _ _).symm.trans hts
  have hm : m ≫ q = snd U.group.X T.group.X := by
    change ((fst _ _ ≫ j) * (snd _ _ ≫ t)) ≫ q = _
    rw [MonObj.mul_comp, Category.assoc, Category.assoc, hjq, htq, MonObj.comp_one,
      Category.comp_id, one_mul]
  refine ⟨⟨lift r q, ?_, ?_⟩⟩
  · apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, Category.id_comp]
      change m ≫ r = fst _ _
      letI := U.isClosedImmersion
      letI : Mono j := Over.mono_of_mono_left _
      apply (cancel_mono j).mp
      rw [Category.assoc, hr]
      rw [show m ≫ a = m * (m ≫ (q ≫ t))⁻¹ from by
        simp only [a, MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv],
        ← Category.assoc, hm]
      change ((fst _ _ ≫ j) * (snd _ _ ≫ t)) * (snd _ _ ≫ t)⁻¹ = fst _ _ ≫ j
      exact mul_inv_cancel_right _ _
    · simpa only [Category.assoc, lift_snd, Category.id_comp] using hm
  · change lift r q ≫ m = _
    change lift r q ≫ ((fst _ _ ≫ j) * (snd _ _ ≫ t)) = _
    simp only [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, hr, a,
      inv_mul_cancel_right]

theorem splitting : Splitting.{u} := by
  intro k _ _ G hGs hGc hG
  obtain ⟨U, D, p, hU, hp, hD⟩ := radicalQuotient G hGs hGc hG
  obtain ⟨⟨s, hs⟩, _⟩ := TorusSections.splitTorusExtension G D U p hp.1 hp.2.1 hp.2.2.1
    hD hU.1 hU.2.1 hU.2.2.2.1
  let T₀ : ClosedSubgroup G.val := ⟨D.val, s, closed_of_section hs⟩
  haveI : IsIso (T₀.inclusion ≫ p) := by change IsIso (s ≫ p); rw [hs]; infer_instance
  refine ⟨U, D, p, hU, hp, hD, ⟨T₀, maximal_of_iso_projection hp.1 hU.2.2.2.1 hD T₀⟩, ?_⟩
  intro T
  have hmax : IsMaximalTorus (G := G) T ↔ IsIso (T.inclusion ≫ p) :=
    ⟨iso_projection_of_maximal hp hU hD hs T,
      fun h ↦ @maximal_of_iso_projection k _ G D U p hp.1 hU.2.2.2.1 hD T h⟩
  exact ⟨hmax, fun h ↦ @product_isIso k _ G D U T p hp.1 (hmax.mp h)⟩

theorem conjugacy : Conjugacy.{u} := by
  intro k _ _ G hGs hGc hG U hU T₁ T₂ hT₁ hT₂
  obtain ⟨V, D, p, hV, hp, hD, _, ht⟩ := splitting G hGs hGc hG
  haveI : IsIso (T₁.inclusion ≫ p) := (ht T₁).1.mp hT₁
  haveI : IsIso (T₂.inclusion ≫ p) := (ht T₂).1.mp hT₂
  let e₁ := asIso (T₁.inclusion ≫ p)
  let e₂ := asIso (T₂.inclusion ≫ p)
  let s₁ := e₁.inv ≫ T₁.inclusion
  let s₂ := e₂.inv ≫ T₂.inclusion
  have hs₁ : s₁ ≫ p = 𝟙 D.val := by
    rw [show s₁ = e₁.inv ≫ T₁.inclusion from rfl, Category.assoc]
    exact e₁.inv_hom_id
  have hs₂ : s₂ ≫ p = 𝟙 D.val := by
    rw [show s₂ = e₂.inv ≫ T₂.inclusion from rfl, Category.assoc]
    exact e₂.inv_hom_id
  obtain ⟨a, ha⟩ := (TorusSections.splitTorusExtension G D V p hp.1 hp.2.1 hp.2.2.1
    hD hV.1 hV.2.1 hV.2.2.2.1).2 s₁ s₂ hs₁ hs₂
  obtain ⟨v, hv⟩ := hU.2.2.2.2 V hV.2.2.2.1
  refine ⟨a ≫ v.hom.hom, e₁ ≪≫ e₂.symm, ?_⟩
  have he := congrArg (fun f : D.val.X ⟶ G.val.X ↦ e₁.hom.hom.hom ≫ f) ha
  have hv' : v.hom.hom ≫ U.inclusion.hom.hom = V.inclusion.hom.hom :=
    congrArg (fun f : V.group ⟶ G.val ↦ f.hom.hom) hv
  have h₁ : e₁.hom.hom.hom ≫ s₁.hom.hom = T₁.inclusion.hom.hom :=
    congrArg (fun f : T₁.group ⟶ G.val ↦ f.hom.hom) (e₁.hom_inv_id_assoc T₁.inclusion)
  change e₁.hom.hom.hom ≫ s₂.hom.hom =
    e₁.hom.hom.hom ≫ ((toUnit D.val.X ≫ a ≫ V.inclusion.hom.hom) * s₁.hom.hom *
      (toUnit D.val.X ≫ a ≫ V.inclusion.hom.hom)⁻¹) at he
  simp only [MonObj.comp_mul, GrpObj.comp_inv, comp_toUnit_assoc, h₁] at he
  change e₁.hom.hom.hom ≫ s₂.hom.hom =
    (toUnit T₁.group.X ≫ (a ≫ v.hom.hom) ≫ U.inclusion.hom.hom) * _ *
      (toUnit T₁.group.X ≫ (a ≫ v.hom.hom) ≫ U.inclusion.hom.hom)⁻¹
  simpa only [Category.assoc, hv'] using he

end

end LinearAlgebraicGroups.GeometricTorusSplitting
