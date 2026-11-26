import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.CentralIsogenies
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.CentralSeries
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieLeftExact
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.NormalAffineQuotient
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SchemeCentre
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.WeylScheme
import Mathlib.AlgebraicGeometry.EffectiveEpi
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Ring
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Order
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Classification.CentralIsogenies

open _root_.LinearAlgebraicGroups.Specs
open Specs.CentralIsogenies
open Specs.CharacterDescent (Character)
open Specs.DiagonalizableGroups
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open Specs.SchemeDerivedGroup (IsSubgroupOf RepresentsQuotient)
open Specs.RootGroups (RootDimension RootSubgroups)
open Specs.CharacterPairing (absoluteRoots adjointWeightVectors characterValue)
open Specs.AdjointRepresentation (GroupPoints constants dualMap scale)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.SchemeCentre (CentreFormula rootLattice)
open LinearAlgebraicGroups.DiagonalizableGroups
  (diagonalRestrictionKernelAndQuotient diagonalFaithfullyFlatQuotients diagonalClosedSubgroups
    diagonalIntegerPowers)

open private specGroupMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private isMonHom_of_comp_closed schemeKernel_sections sameImage_iff groupPresentation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private integerHomEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private splitTorusSmooth from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.WeylScheme
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria

noncomputable section

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

variable {k : Type u} [Field k]

private abbrev underlying : GroupScheme k ⥤ Scheme.{u} :=
  Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))

set_option backward.isDefEq.respectTransparency false in
private theorem flat_of_surjective_torus_map {G H : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} {S : ClosedSubgroup H.val} (g : T.group ⟶ S.group)
    (hS : IsSplitTorus S.group) (hg : Surjective g.hom.hom.left) :
    Flat g.hom.hom.left := by
  let T' := Unipotent.closedSubgroupAlgebraicGroup T
  let S' := Unipotent.closedSubgroupAlgebraicGroup S
  obtain ⟨I, p, i, hp, _, _⟩ := schemeImageFactorization T' S' g
  have hcomp := congrArg (underlying (k := k)).map hp.1
  simp only [Functor.map_comp] at hcomp
  change p.hom.hom.left ≫ i.hom.hom.left = g.hom.hom.left at hcomp
  letI : Surjective (p.hom.hom.left ≫ i.hom.hom.left) := hcomp.symm ▸ hg
  letI : Surjective i.hom.hom.left := Surjective.of_comp p.hom.hom.left i.hom.hom.left
  letI : IsClosedImmersion i.hom.hom.left := hp.2.2.2.2.2
  letI : Smooth S'.val.X.hom := splitTorusSmooth hS
  letI : IsReduced S'.val.X.left := isReduced_of_smooth_over_field S'.val.X.hom
  haveI : IsIso i.hom.hom.left := isIso_of_isClosedImmersion_of_surjective _
  letI : Flat p.hom.hom.left := hp.2.1
  rw [← hcomp]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem finiteTorusRestriction {G H : GroupScheme k} {T : ClosedSubgroup G}
    {S : ClosedSubgroup H} {f : G ⟶ H} {fT : T.group ⟶ S.group}
    (hf : IsFinite f.hom.hom.left) (hfT : IsTorusRestriction f fT) :
    IsFinite fT.hom.hom.left := by
  letI := hf
  letI := T.isClosedImmersion
  letI := S.isClosedImmersion
  have he := congrArg (underlying (k := k)).map hfT.1
  simp only [Functor.map_comp] at he
  change fT.hom.hom.left ≫ S.inclusion.hom.hom.left =
    T.inclusion.hom.hom.left ≫ f.hom.hom.left at he
  haveI : IsFinite (fT.hom.hom.left ≫ S.inclusion.hom.hom.left) := by
    rw [he]
    infer_instance
  exact IsFinite.of_comp _ S.inclusion.hom.hom.left

set_option backward.isDefEq.respectTransparency false in
theorem characterPullback_injective {G H : GroupScheme k} (f : G ⟶ H)
    (hflat : Flat f.hom.hom.left) (hsurj : Surjective f.hom.hom.left) :
    Function.Injective (characterPullback f) := by
  letI := hflat
  letI := hsurj
  letI : Epi f.hom.hom.left := Flat.epi_of_flat_of_surjective _
  letI : Epi f.hom.hom := Over.epi_of_epi_left _
  intro χ ψ h
  apply Grp.hom_ext
  apply (cancel_epi f.hom.hom).mp
  exact congrArg (fun a : Character G ↦ a.hom.hom) h

private abbrev diagonal (M : Type u) [CommGroup M] : GroupScheme k :=
  specGroup (groupAlgebra k M)

private theorem groupAlgebraMap_comp {M N P : Type u}
    [CommGroup M] [CommGroup N] [CommGroup P] (a : M →* N) (b : N →* P) :
    groupAlgebraMap k a ≫ groupAlgebraMap k b = groupAlgebraMap k (b.comp a) := by
  apply CommHopfAlgCat.hom_ext
  exact (MonoidAlgebra.mapDomainBialgHom_comp (R := k) b a).symm

private theorem diagonalMap_id (M : Type u) [CommGroup M] :
    specGroupMap (groupAlgebraMap k (MonoidHom.id M)) = 𝟙 (diagonal (k := k) M) := by
  have h : groupAlgebraMap k (MonoidHom.id M) = 𝟙 (groupAlgebra k M) :=
    CommHopfAlgCat.hom_ext MonoidAlgebra.mapDomainBialgHom_id
  rw [h]
  exact (hopfSpec (CommRingCat.of k)).map_id _

private def diagonalIso {M N : Type u} [CommGroup M] [CommGroup N]
    (j : M ≃* N) : diagonal (k := k) N ≅ diagonal M where
  hom := specGroupMap (groupAlgebraMap k j.toMonoidHom)
  inv := specGroupMap (groupAlgebraMap k j.symm.toMonoidHom)
  hom_inv_id := by
    rw [← specGroupMap_comp, groupAlgebraMap_comp]
    have h : j.toMonoidHom.comp j.symm.toMonoidHom = MonoidHom.id N :=
      MonoidHom.ext (fun x ↦ j.apply_symm_apply x)
    rw [h, diagonalMap_id]
  inv_hom_id := by
    rw [← specGroupMap_comp, groupAlgebraMap_comp]
    have h : j.symm.toMonoidHom.comp j.toMonoidHom = MonoidHom.id M :=
      MonoidHom.ext (fun x ↦ j.symm_apply_apply x)
    rw [h, diagonalMap_id]

private def monomial {M : Type u} [CommGroup M] (m : M) :
    Character (diagonal (k := k) M) :=
  specGroupMap (groupAlgebraMap k
    ((zpowersHom M m).comp MulEquiv.ulift.toMonoidHom))

private theorem monomial_natural {M N : Type u} [CommGroup M] [CommGroup N]
    (l : M →* N) (m : M) :
    specGroupMap (groupAlgebraMap k l) ≫ monomial (k := k) m = monomial (l m) := by
  unfold monomial
  rw [← specGroupMap_comp]
  congr 1
  apply CommHopfAlgCat.hom_ext
  rw [CommHopfAlgCat.hom_comp]
  change (MonoidAlgebra.mapDomainBialgHom k l).comp
    (MonoidAlgebra.mapDomainBialgHom k ((zpowersHom M m).comp MulEquiv.ulift.toMonoidHom)) = _
  rw [← MonoidAlgebra.mapDomainBialgHom_comp]
  congr 1
  ext ⟨n⟩
  exact map_zpow l m n.toAdd

private theorem monomial_bijective (M : Type u) [CommGroup M] :
    Function.Bijective (monomial (k := k) (M := M)) := by
  let monomials : M ≃ (IntegerCharacters.{u} →* M) := (integerHomEquiv M).toEquiv
  let maps : (MonoidAlgebra k IntegerCharacters →ₐc[k] MonoidAlgebra k M) ≃
      (op (groupAlgebra k M) ⟶ op (groupAlgebra k IntegerCharacters)) :=
    { toFun := fun a => (CommHopfAlgCat.ofHom a).op
      invFun := fun a => a.unop.hom
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (monomials.trans (MonoidAlgebra.mapDomainBialgHomEquiv.trans
    (maps.trans (hopfSpec.fullyFaithful (R := CommRingCat.of k)).homEquiv))).bijective

private def monomialEquiv (M : Type u) [CommGroup M] :
    M ≃* Character (diagonal (k := k) M) := by
  let F := (integerHomEquiv M).trans
    (MonoidAlgebra.mapDomainBialgHomMulEquiv (R := k))
  let S := Spec.mapMulEquiv (R := k) (S := MonoidAlgebra k IntegerCharacters)
    (T := MonoidAlgebra k M)
  let f : M →* Character (diagonal (k := k) M) :=
    { toFun := monomial (k := k)
      map_one' := by
        apply Grp.hom_ext
        have h := congrArg (fun g ↦ WithConv.toConv g.ofConv.toAlgHom) (F.map_one)
        exact (congrArg S h).trans S.map_one
      map_mul' := fun m n ↦ by
        apply Grp.hom_ext
        have h := congrArg
          (fun g ↦ WithConv.toConv g.ofConv.toAlgHom) (F.map_mul m n)
        change WithConv.toConv (F (m * n)).ofConv.toAlgHom =
          WithConv.toConv (F m).ofConv.toAlgHom * WithConv.toConv (F n).ofConv.toAlgHom at h
        exact (congrArg S h).trans (S.map_mul _ _) }
  exact MulEquiv.ofBijective f (monomial_bijective M)

private def characterIso {A B : GroupScheme k} (i : A ≅ B) :
    Character A ≃* Character B where
  toFun f := i.inv ≫ f
  invFun f := i.hom ≫ f
  left_inv f := by simp
  right_inv f := by simp
  map_mul' f g := Grp.hom_ext _ _ (MonObj.comp_mul _ _ _)

set_option backward.isDefEq.respectTransparency false in
private theorem diagonalCharacterSubgroup_split {T : GroupScheme k} (hs : IsSplitTorus T)
    (N : Subgroup (Character T)) : IsSplitTorus (diagonal (k := k) N) := by
  obtain ⟨r, ⟨i⟩⟩ := hs
  let J := ULift.{u} (Fin r)
  obtain ⟨j⟩ := diagonalIntegerPowers k J
  let b := (monomialEquiv (k := k) (Multiplicative (J → ℤ))).trans (characterIso (j ≪≫ i.symm))
  let e : (J → ℤ) ≃ₗ[ℤ] Additive (Character T) := b.toAdditive.toIntLinearEquiv
  let N' := AddSubgroup.toIntSubmodule N.toAddSubgroup
  obtain ⟨n, ⟨B⟩⟩ := N'.nonempty_basis_of_pid ((Pi.basisFun ℤ J).map e)
  let F : (Fin n → ℤ) ≃+ (ULift.{u} (Fin n) → ℤ) :=
    { toFun := fun f j ↦ f j.down
      invFun := fun f j ↦ f ⟨j⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  let a : N ≃* Multiplicative (ULift.{u} (Fin n) → ℤ) :=
    (B.equivFun.toAddEquiv.trans F).toMultiplicative
  obtain ⟨j'⟩ := diagonalIntegerPowers k (ULift.{u} (Fin n))
  exact ⟨n, ⟨(diagonalIso a).symm ≪≫ j'⟩⟩

private theorem diagonal_map_exists {M N : Type u} [CommGroup M] [CommGroup N]
    (f : diagonal (k := k) N ⟶ diagonal M) :
    ∃ l : M →* N, specGroupMap (groupAlgebraMap k l) = f := by
  let ff := hopfSpec.fullyFaithful (R := CommRingCat.of k)
  let a : groupAlgebra k M ⟶ groupAlgebra k N := (ff.preimage f).unop
  let l := MonoidAlgebra.mapDomainBialgHomEquiv.symm a.hom
  have hl : groupAlgebraMap k l = a :=
    CommHopfAlgCat.hom_ext (MonoidAlgebra.mapDomainBialgHomEquiv.apply_symm_apply a.hom)
  exact ⟨l, hl ▸ ff.map_preimage f⟩

private theorem finite_of_finiteDiagonalRestriction {M : Type u} [CommGroup M] [Group.FG M]
    (N : Subgroup M) (hf : IsFinite (diagonalRestriction k N).hom.hom.left) :
    Finite (M ⧸ N) := by
  obtain ⟨hc, _, _, _, hkernel, _⟩ := diagonalRestrictionKernelAndQuotient k M N
  let K : ClosedSubgroup (diagonal (k := k) M) :=
    ⟨diagonal (M ⧸ N), diagonalClosedInclusion k N, hc⟩
  change IsSchemeKernel (diagonalRestriction k N) K at hkernel
  have hpb := hkernel.map (Over.forget (Spec (CommRingCat.of k)))
  have hf' : IsFinite K.group.X.hom :=
    MorphismProperty.of_isPullback hpb hf
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k (MonoidAlgebra k (M ⧸ N))))) at hf'
  have hf'' := (IsFinite.SpecMap_iff _).mp hf'
  haveI : Module.Finite k (MonoidAlgebra k (M ⧸ N)) := RingHom.finite_algebraMap.mp hf''
  exact (MonoidAlgebra.basis (M ⧸ N) k).linearIndependent.finite

set_option backward.isDefEq.respectTransparency false in
/-- Pullback along a torus restriction of a central isogeny has finite index. -/
theorem finiteIndexCharacterPullback (centre : CentreFormula.{u})
    (G₁ G₂ : AffineAlgebraicGroup k) (hG₁ : IsReductive G₁) (hG₂ : IsReductive G₂)
    (T₁ : ClosedSubgroup G₁.val) (T₂ : ClosedSubgroup G₂.val)
    (hs₁ : IsSplitTorus T₁.group) (hm₁ : IsGeometricallyMaximal T₁)
    (hs₂ : IsSplitTorus T₂.group) (hm₂ : IsGeometricallyMaximal T₂)
    (f : G₁.val ⟶ G₂.val) (fT : T₁.group ⟶ T₂.group)
    (hf : IsCentralIsogeny f) (hfT : IsTorusRestriction f fT) :
    Function.Injective (characterPullback fT) ∧
      Finite (Character T₁.group ⧸ (characterPullback fT).range) := by
  have hi := characterPullback_injective fT hfT.2.1 hfT.2.2
  refine ⟨hi, ?_⟩
  obtain ⟨hfg₁, e₁, he₁, _, _⟩ := centre G₁ hG₁ T₁ hs₁ hm₁
  obtain ⟨_, e₂, he₂, _, _⟩ := centre G₂ hG₂ T₂ hs₂ hm₂
  letI := hfg₁
  let l := characterPullback fT
  let d := e₁.hom ≫ fT ≫ e₂.inv
  obtain ⟨m, hmd⟩ := diagonal_map_exists d
  change ∀ α, e₁.hom ≫ α = monomial α at he₁
  change ∀ α, e₂.hom ≫ α = monomial α at he₂
  have he (χ : Character T₂.group) : m χ = l χ := by
    apply (monomial_bijective (k := k) _).injective
    rw [← monomial_natural m χ, hmd]
    change (e₁.hom ≫ fT ≫ e₂.inv) ≫ monomial χ = monomial (l χ)
    rw [← he₂ χ, ← he₁ (l χ)]
    simp [l, characterPullback]
  have hm : m = l := MonoidHom.ext he
  rw [hm] at hmd
  let j : Character T₂.group ≃* l.range :=
    MulEquiv.ofBijective l.rangeRestrict ⟨fun x y h ↦ hi (congrArg Subtype.val h),
      fun ⟨x, hx⟩ ↦ by
        obtain ⟨y, rfl⟩ := hx
        exact ⟨y, rfl⟩⟩
  have hj : l.range.subtype.comp j.toMonoidHom = l := rfl
  let i := diagonalIso (k := k) j
  have hd : diagonalRestriction k l.range ≫ i.hom = d := by
    change specGroupMap (groupAlgebraMap k l.range.subtype) ≫
      specGroupMap (groupAlgebraMap k j.toMonoidHom) = d
    rw [← specGroupMap_comp, groupAlgebraMap_comp, hj]
    exact hmd
  letI : IsFinite fT.hom.hom.left := finiteTorusRestriction hf.1 hfT
  change Finite (Character T₁.group ⧸ l.range)
  apply finite_of_finiteDiagonalRestriction (k := k)
  have hleft := congrArg (underlying (k := k)).map hd
  simp only [Functor.map_comp] at hleft
  change (diagonalRestriction k l.range).hom.hom.left ≫ i.hom.hom.hom.left =
    e₁.hom.hom.hom.left ≫ fT.hom.hom.left ≫ e₂.inv.hom.hom.left at hleft
  letI : IsIso e₁.hom.hom.hom.left := (underlying (k := k)).map_isIso e₁.hom
  letI : IsIso e₂.inv.hom.hom.left := (underlying (k := k)).map_isIso e₂.inv
  letI : IsIso i.hom := i.isIso_hom
  letI : IsIso i.hom.hom.hom.left := (underlying (k := k)).map_isIso i.hom
  haveI : IsFinite ((diagonalRestriction k l.range).hom.hom.left ≫ i.hom.hom.hom.left) := by
    rw [hleft]
    infer_instance
  exact IsFinite.of_comp _ i.hom.hom.hom.left

set_option backward.isDefEq.respectTransparency false in
/-- The full scheme kernel of a central isogeny factors through the split maximal torus. -/
theorem kernel_le_maximalTorus (centre : CentreFormula.{u})
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (hs : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T)
    (N : ClosedSubgroup G.val)
    (hN : Centralizes (𝟙 G.val) N.inclusion.hom.hom) :
    IsSubgroupOf N T := by
  obtain ⟨_, e, _, hc, hrep, _⟩ := centre G hG T hs hm
  let Z : ClosedSubgroup G.val :=
    ⟨diagonal (Character T.group ⧸ rootLattice T),
      diagonalClosedInclusion k (rootLattice T) ≫ e.hom ≫ T.inclusion, hc⟩
  change RepresentsSubgroup Z (fun _ z ↦ Centralizes (𝟙 G.val) z) at hrep
  obtain ⟨z, hz⟩ := (hrep _ _).mp hN
  let zT := diagonalClosedInclusion k (rootLattice T) ≫ e.hom
  let t := z ≫ zT.hom.hom
  have ht : t ≫ T.inclusion.hom.hom = N.inclusion.hom.hom := by
    change z ≫ (Grp.forget (SchemeOver k)).map (zT ≫ T.inclusion) =
      N.inclusion.hom.hom at hz
    rw [Functor.map_comp] at hz
    change z ≫ (zT.hom.hom ≫ T.inclusion.hom.hom) = N.inclusion.hom.hom at hz
    exact (Category.assoc _ _ _).trans hz
  letI := T.isClosedImmersion
  letI := isMonHom_of_comp_closed t N.inclusion T.inclusion ht
  exact ⟨Grp.homMk t, Grp.hom_ext _ _ ht⟩


set_option backward.isDefEq.respectTransparency false in
/-- The differential of a central isogeny can only kill vectors of weight one. -/
theorem lieKernel_le_zeroWeight (rootSubgroups : RootSubgroups.{u}) (centre : CentreFormula.{u})
    (G H : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (hs : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T)
    (f : G.val ⟶ H.val) (hf : IsCentralIsogeny f) {v : Lie k G.val}
    (hv : mapPointKernel f v = 0) : v ∈ adjointWeightVectors T 1 := by
  obtain ⟨N, hN, hz⟩ := hf.2.2.2
  obtain ⟨j, hj⟩ := kernel_le_maximalTorus centre G hG T hs hm N hz
  let E := Grp.trivial (SchemeOver k)
  let e : E ⟶ H.val := default
  let t : N.group ⟶ E := default
  let F := Grp.forget (SchemeOver k)
  have ht : F.map t = toUnit N.group.X :=
    (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
  have he : F.map e = η[H.val.X] := rfl
  have hp : IsPullback (F.map N.inclusion) (F.map t) (F.map f) (F.map e) := by
    rw [ht, he]
    exact hN
  have hpb := hp.of_map_of_faithful F
  have hr := (lieKernelComparison k (Grp.isZero_trivial (SchemeOver k)).isTerminal hpb).2
  have hvr : v ∈ Set.range (mapPointKernel N.inclusion) := by
    rw [hr]
    exact hv
  obtain ⟨w, rfl⟩ := hvr
  rw [← (rootSubgroups G hG T hs hm).1.2]
  refine ⟨mapPointKernel j w, ?_⟩
  rw [← (lieFunctoriality k).2.2 _ _ _ j T.inclusion w, hj]

private theorem characterValue_pullback {T S : GroupScheme k} (f : T ⟶ S) (β : Character S)
    (R : TestAlgebra k) (t : GroupPoints T R) :
    characterValue (characterPullback f β) R t =
      characterValue β R (t ≫ f.hom.hom) := by
  unfold characterValue
  congr 2

set_option backward.isDefEq.respectTransparency false in
/-- The differential intertwines the source torus action with the pulled-back
target torus action, with coefficients in every test algebra. -/
theorem mapPointKernel_intertwines {G H : GroupScheme k} {T : ClosedSubgroup G}
    {S : ClosedSubgroup H} (f : G ⟶ H) (fT : T.group ⟶ S.group)
    (hfT : IsTorusRestriction f fT) (α : Character T.group)
    {v : Lie k G} (hv : v ∈ adjointWeightVectors T α)
    (R : TestAlgebra k) (t : GroupPoints T.group R) :
    let w := mapPointKernel f v
    let t' := t ≫ fT.hom.hom
    let p := mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R))) w.toMul.val
    let g := mapPoints (constants R) (t' ≫ S.inclusion.hom.hom)
    g * p * g⁻¹ = mapPoints (scale R (characterValue α R t)) p := by
  dsimp only
  have h := congrArg (· ≫ f.hom.hom) (hv R t)
  have hcomp : fT.hom.hom ≫ S.inclusion.hom.hom =
      T.inclusion.hom.hom ≫ f.hom.hom :=
    congrArg (fun j : T.group ⟶ H ↦ j.hom.hom) hfT.1
  change ((mapPoints (constants R) (t ≫ T.inclusion.hom.hom) *
    mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R))) v.toMul.val *
    (mapPoints (constants R) (t ≫ T.inclusion.hom.hom))⁻¹) ≫ f.hom.hom) = _ at h
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp] at h
  have hv' : (mapPointKernel f v).toMul.val = v.toMul.val ≫ f.hom.hom := rfl
  rw [hv']
  simpa only [mapPoints, Category.assoc, hcomp] using h

set_option backward.isDefEq.respectTransparency false in
private theorem representsQuotient_section_eq {G Q : GroupScheme k}
    {D : ClosedSubgroup G} {q : G ⟶ Q} (hq : RepresentsQuotient D q)
    {X : SchemeOver k} (g g' : X ⟶ G.X) :
    g ≫ q.hom.hom = g' ≫ q.hom.hom ↔
      ∃ d : X ⟶ D.group.X, d ≫ D.inclusion.hom.hom = g⁻¹ * g' := by
  obtain ⟨e, he⟩ := hq
  have hv (x : X ⟶ G.X) :
      e.hom.hom.app (op X) (Specs.projectSection D x) = ULift.up (x ≫ q.hom.hom) :=
    congrArg (fun m => m.hom.app (op X) (ULift.up x)) he
  rw [← LinearAlgebraicGroups.rightQuotientProjectionEquality D g g']
  constructor
  · intro h
    apply (ConcreteCategory.bijective_of_isIso (e.hom.hom.app (op X))).1
    rw [hv, hv, h]
  · intro h
    exact congrArg ULift.down ((hv g).symm.trans
      ((congrArg (e.hom.hom.app (op X)) h).trans (hv g')))

private theorem representsQuotient_kernel_sections {G Q : GroupScheme k}
    {D : ClosedSubgroup G} {q : G ⟶ Q} (hq : RepresentsQuotient D q)
    {X : SchemeOver k} (g : X ⟶ G.X) :
    g ≫ q.hom.hom = 1 ↔ ∃ d : X ⟶ D.group.X, d ≫ D.inclusion.hom.hom = g := by
  simpa only [MonObj.one_comp, inv_one, one_mul, eq_comm (a := (1 : X ⟶ Q.X))] using
    representsQuotient_section_eq hq (1 : X ⟶ G.X) g

set_option backward.isDefEq.respectTransparency false in
private theorem representsQuotient_isSchemeKernel {G Q : GroupScheme k}
    {D : ClosedSubgroup G} {q : G ⟶ Q} (hq : RepresentsQuotient D q) :
    IsSchemeKernel q D := by
  classical
  have hunit : D.inclusion.hom.hom ≫ q.hom.hom = 1 :=
    (representsQuotient_kernel_sections hq _).mpr ⟨𝟙 _, Category.id_comp _⟩
  let t : D.group.X ⟶ 𝟙_ (SchemeOver k) := toUnit _
  let ηQ : 𝟙_ (SchemeOver k) ⟶ Q.X := η[Q.X]
  have hsq : D.inclusion.hom.hom ≫ q.hom.hom = t ≫ ηQ := hunit
  letI := D.isClosedImmersion
  letI : Mono D.inclusion.hom.hom := Over.mono_of_mono_left _
  let chooseLift (P : PullbackCone q.hom.hom ηQ) :
      ∃ d : P.pt ⟶ D.group.X, d ≫ D.inclusion.hom.hom = P.fst := by
    apply (representsQuotient_kernel_sections hq _).mp
    have e : P.snd = toUnit P.pt := (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
    exact P.condition.trans (congrArg (· ≫ ηQ) e)
  exact IsPullback.of_isLimit <|
    PullbackCone.IsLimit.mk hsq (fun P ↦ (chooseLift P).choose)
      (fun P ↦ (chooseLift P).choose_spec)
      (fun _ ↦ (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _)
      (fun P _ h _ ↦ (cancel_mono D.inclusion.hom.hom).mp (h.trans (chooseLift P).choose_spec.symm))

set_option backward.isDefEq.respectTransparency false in
/-- A presented fppf quotient of affine algebraic groups has the indicated
scheme kernel and is faithfully flat and locally of finite presentation. -/
theorem representsQuotient_isFppfGroupQuotient {G Q : AffineAlgebraicGroup k}
    {D : ClosedSubgroup G.val} {q : G.val ⟶ Q.val} (hq : RepresentsQuotient D q) :
    Specs.Unipotent.IsFppfGroupQuotient D q := by
  refine ⟨representsQuotient_isSchemeKernel hq, ?_⟩
  obtain ⟨I, p, i, hp, _, _⟩ := schemeImageFactorization G Q q
  let Y := (fppfOver k).uliftYoneda.{u + 1}
  have hloc : Sheaf.IsLocallySurjective (Y.map q.hom.hom) := by
    obtain ⟨e, he⟩ := hq
    change Presheaf.IsLocallySurjective (fppfOver k) (Y.map q.hom.hom).hom
    change rightQuotientProjection D ≫ e.hom = Y.map q.hom.hom at he
    rw [← he]
    letI := LinearAlgebraicGroups.rightQuotientLocalLifts D
    infer_instance
  letI : Epi (Y.map q.hom.hom) := Sheaf.epi_of_isLocallySurjective _
  have hpi : p.hom.hom ≫ i.hom.hom = q.hom.hom :=
    congrArg (fun j : G.val ⟶ Q.val ↦ j.hom.hom) hp.1
  have he : Y.map p.hom.hom ≫ Y.map i.hom.hom = Y.map q.hom.hom :=
    (Y.map_comp _ _).symm.trans (congrArg Y.map hpi)
  letI : Epi (Y.map i.hom.hom) := epi_of_epi_fac he
  letI := hp.2.2.2.2.2
  letI : Mono i.hom.hom := Over.mono_of_mono_left _
  have hm : Mono (Y.map i.hom.hom).hom := by
    rw [NatTrans.mono_iff_mono_app]
    intro X
    apply (CategoryTheory.mono_iff_injective _).mpr
    rintro ⟨x⟩ ⟨y⟩ hxy
    exact congrArg ULift.up ((cancel_mono i.hom.hom).mp (congrArg ULift.down hxy))
  letI : Mono (Y.map i.hom.hom) :=
    (sheafToPresheaf (fppfOver k) (Type (u + 1))).mono_of_mono_map (f := Y.map i.hom.hom) hm
  letI : IsIso (Y.map i.hom.hom) := isIso_of_mono_of_epi _
  let FF := (fppfOver k).fullyFaithfulUliftYoneda.{u + 1}
  letI : Y.ReflectsIsomorphisms := FF.reflectsIsomorphisms
  letI : IsIso i.hom.hom := isIso_of_reflects_iso i.hom.hom Y
  letI : IsIso i.hom.hom.left := (Over.forget _).map_isIso i.hom.hom
  have hc : p.hom.hom.left ≫ i.hom.hom.left = q.hom.hom.left :=
    congrArg (fun j : G.val.X ⟶ Q.val.X ↦ j.left) hpi
  refine ⟨?_, ?_, ?_, hq⟩
  · rw [← hc]
    exact MorphismProperty.comp_mem _ _ _ hp.2.1 (MorphismProperty.of_isIso _ _)
  · rw [← hc]
    exact MorphismProperty.comp_mem _ _ _ hp.2.2.1 (MorphismProperty.of_isIso _ _)
  · rw [← hc]
    exact MorphismProperty.comp_mem _ _ _ hp.2.2.2.1
      (inferInstanceAs (LocallyOfFinitePresentation i.hom.hom.left))

set_option backward.isDefEq.respectTransparency false in
/-- The image of a split maximal torus in a quotient by the scheme centre.
The quotient's image lattice is computed before proving maximality of that image. -/
theorem adjointTorusImage (centre : CentreFormula.{u})
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (hs : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T)
    (Z : ClosedSubgroup G.val)
    (hZ : RepresentsSubgroup Z (fun _ z ↦ Centralizes (𝟙 G.val) z))
    (Q : AffineAlgebraicGroup k) (q : G.val ⟶ Q.val) (hq : RepresentsQuotient Z q) :
    ∃ (T' : ClosedSubgroup Q.val) (qT : T.group ⟶ T'.group),
      IsSplitTorus T'.group ∧ IsTorusRestriction q qT ∧
      Function.Injective (characterPullback qT) ∧ (characterPullback qT).range = rootLattice T ∧
      Nonempty (diagonal (rootLattice T) ≅ T'.group) := by
  obtain ⟨hfg, e, he, hz, hzrep, _⟩ := centre G hG T hs hm
  let M := Character T.group
  let L := rootLattice T
  change ∀ α, e.hom ≫ α = monomial α at he
  letI : Group.FG M := hfg
  let Z₀ : ClosedSubgroup G.val :=
    ⟨diagonal (M ⧸ L), diagonalClosedInclusion k L ≫ e.hom ≫ T.inclusion, hz⟩
  change RepresentsSubgroup Z₀ (fun _ z ↦ Centralizes (𝟙 G.val) z) at hzrep
  let F := T.inclusion ≫ q
  obtain ⟨I, p, i, hp, _, _⟩ := schemeImageFactorization
    (Unipotent.closedSubgroupAlgebraicGroup T) Q F
  change T.group ⟶ I.val at p
  let T' : ClosedSubgroup Q.val := ⟨I.val, i, hp.2.2.2.2.2⟩
  let eT := e.hom ≫ p
  haveI : IsIso e.hom.hom.hom.left := (underlying (k := k)).map_isIso e.hom
  have hflat : Flat eT.hom.hom.left :=
    MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isIso _ _) hp.2.1
  have hsurj : Surjective eT.hom.hom.left :=
    MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isIso _ _) hp.2.2.1
  let I₀ : AffineGroupCategory k := ⟨I.val, I.property.1⟩
  obtain ⟨N, ⟨j, hj⟩, _⟩ := (diagonalFaithfullyFlatQuotients k M I₀ eT).mp ⟨hflat, hsurj⟩
  obtain ⟨hn, _, _, _, hnker, _⟩ := diagonalRestrictionKernelAndQuotient k M N
  let KN : ClosedSubgroup (diagonal (k := k) M) :=
    ⟨diagonal (M ⧸ N), diagonalClosedInclusion k N, hn⟩
  change IsSchemeKernel (diagonalRestriction k N) KN at hnker
  have hmono (J : ClosedSubgroup Q.val) : Mono J.inclusion.hom.hom :=
    letI := J.isClosedImmersion
    Over.mono_of_mono_left _
  letI := hmono T'
  letI := T.isClosedImmersion
  letI : Mono T.inclusion.hom.hom := Over.mono_of_mono_left _
  letI : IsIso e.hom.hom.hom := (Grp.forget (SchemeOver k)).map_isIso e.hom
  letI : IsIso j.hom.hom.hom := (Grp.forget (SchemeOver k)).map_isIso j.hom
  have hZ₀ : Z₀.inclusion.hom.hom =
      (diagonalClosedInclusion k L).hom.hom ≫ e.hom.hom.hom ≫ T.inclusion.hom.hom := by
    change (Grp.forget (SchemeOver k)).map (diagonalClosedInclusion k L ≫ e.hom ≫ T.inclusion) = _
    simp only [Functor.map_comp]
    rfl
  have hinc :
      (diagonalRestriction k N).hom.hom ≫ j.hom.hom.hom ≫ i.hom.hom =
        e.hom.hom.hom ≫ T.inclusion.hom.hom ≫ q.hom.hom := by
    change ((diagonalRestriction k N ≫ j.hom ≫ i).hom.hom) =
      ((e.hom ≫ T.inclusion ≫ q).hom.hom)
    rw [← Category.assoc, hj, Category.assoc, hp.1]
  have hsame {X : SchemeOver k} (t : X ⟶ (diagonal (k := k) M).X) :
      (∃ n : X ⟶ KN.group.X, n ≫ KN.inclusion.hom.hom = t) ↔
      ∃ z : X ⟶ Z₀.group.X, z ≫ (diagonalClosedInclusion k L).hom.hom = t := by
    have hcomm :
        t ≫ (diagonalRestriction k N).hom.hom = 1 ↔
          (t ≫ e.hom.hom.hom ≫ T.inclusion.hom.hom) ≫ q.hom.hom = 1 := by
      rw [Category.assoc, Category.assoc, ← hinc, ← Category.assoc]
      constructor
      · intro h
        simp only [h, MonObj.one_comp]
      · intro h
        apply (cancel_mono (j.hom.hom.hom ≫ i.hom.hom)).mp
        simpa only [MonObj.one_comp, Category.assoc] using h
    change t ∈ SubgroupSections KN X ↔ _
    rw [schemeKernel_sections hnker, hcomm, representsQuotient_kernel_sections hq,
      ← hZ, hzrep]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, (cancel_mono (e.hom.hom.hom ≫ T.inclusion.hom.hom)).mp ?_⟩
      simpa only [hZ₀, Category.assoc] using ha
    · rintro ⟨a, rfl⟩
      exact ⟨a, by simp only [hZ₀, Category.assoc]⟩
  obtain ⟨a, ha⟩ := (hsame KN.inclusion.hom.hom).mp ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨b, hb⟩ := (hsame (diagonalClosedInclusion k L).hom.hom).mpr ⟨𝟙 _, Category.id_comp _⟩
  have hLc : IsClosedImmersion (diagonalClosedInclusion k L).hom.hom.left :=
    (diagonalRestrictionKernelAndQuotient k M L).choose
  letI := hLc
  letI := hn
  letI : Mono (diagonalClosedInclusion k L).hom.hom := Over.mono_of_mono_left _
  letI : Mono KN.inclusion.hom.hom := Over.mono_of_mono_left _
  letI := isMonHom_of_comp_closed a KN.inclusion (diagonalClosedInclusion k L) ha
  letI := isMonHom_of_comp_closed b (diagonalClosedInclusion k L) KN.inclusion hb
  let d : KN.group ≅ diagonal (M ⧸ L) :=
    { hom := Grp.homMk a
      inv := Grp.homMk b
      hom_inv_id := by
        apply Grp.hom_ext
        apply (cancel_mono KN.inclusion.hom.hom).mp
        change (a ≫ b) ≫ KN.inclusion.hom.hom = (𝟙 _) ≫ KN.inclusion.hom.hom
        rw [Category.assoc, hb, ha, Category.id_comp]
      inv_hom_id := by
        apply Grp.hom_ext
        apply (cancel_mono (diagonalClosedInclusion k L).hom.hom).mp
        change (b ≫ a) ≫ (diagonalClosedInclusion k L).hom.hom =
          (𝟙 _) ≫ (diagonalClosedInclusion k L).hom.hom
        rw [Category.assoc, ha, hb, Category.id_comp] }
  have hN : N = L := by
    have hu := (diagonalClosedSubgroups k M KN.group KN.inclusion).mp hn
    exact hu.unique ⟨Iso.refl _, Category.id_comp _⟩ ⟨d, Grp.hom_ext _ _ ha⟩
  have hdiag : Nonempty (diagonal (k := k) L ≅ T'.group) := by
    change Nonempty (diagonal (k := k) L ≅ I₀.val)
    rw [← hN]
    exact ⟨j⟩
  obtain ⟨e'⟩ := hdiag
  obtain ⟨r, ⟨e''⟩⟩ := diagonalCharacterSubgroup_split hs L
  refine ⟨T', p, ⟨r, ⟨e'.symm ≪≫ e''⟩⟩, ⟨hp.1, hp.2.1, hp.2.2.1⟩,
    characterPullback_injective p hp.2.1 hp.2.2.1, ?_, ⟨e'⟩⟩
  change (characterPullback p).range = L
  rw [← hN]
  ext χ
  constructor
  · rintro ⟨ψ, rfl⟩
    obtain ⟨n, hn'⟩ := (monomial_bijective (k := k) N).surjective (j.hom ≫ ψ)
    have hh : e.hom ≫ characterPullback p ψ = monomial n.val := by
      change (e.hom ≫ p) ≫ ψ = _
      change eT ≫ ψ = _
      rw [← hj, Category.assoc, ← hn']
      exact monomial_natural N.subtype n
    change e.hom ≫ characterPullback p ψ = monomial n.val at hh
    rw [he] at hh
    exact (monomial_bijective (k := k) M).injective hh ▸ n.property
  · intro hχ
    let n : N := ⟨χ, hχ⟩
    refine ⟨j.inv ≫ monomial n, ?_⟩
    have h : e.hom ≫ characterPullback p (j.inv ≫ monomial n) = e.hom ≫ χ := by
      change e.hom ≫ p ≫ j.inv ≫ monomial n = _
      rw [← Category.assoc]
      change eT ≫ (j.inv ≫ monomial n) = _
      rw [← hj, Category.assoc, Iso.hom_inv_id_assoc, he]
      exact monomial_natural N.subtype n
    exact (cancel_epi e.hom).mp h

private theorem ringKrullDim_eq_of_integral_surj {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) (hs : Function.Surjective (PrimeSpectrum.comap f)) :
    ringKrullDim S = ringKrullDim R := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra.IsIntegral R S := ⟨hf⟩
  apply le_antisymm
  · apply krullDim_le_of_strictMono (PrimeSpectrum.comap f)
    intro p q h
    exact Ideal.IsIntegral.under_lt_under (R := R) (I := p.asIdeal) (J := q.asIdeal) h
  · apply iSup_le
    intro l
    obtain ⟨P, hP⟩ := hs l.head
    haveI : P.asIdeal.LiesOver l.head.asIdeal := ⟨(congrArg PrimeSpectrum.asIdeal hP).symm⟩
    obtain ⟨L, hL, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P.asIdeal
    exact le_sSup ⟨L, by simpa only using congrArg (fun n : ℕ ↦ (n : WithBot ℕ∞)) hL⟩

private theorem scheme_dimension_eq_of_finite_surjective {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (f : X ⟶ Y) [IsFinite f] [Surjective f] :
    topologicalKrullDim X = topologicalKrullDim Y := by
  let a := f.appTop
  let e := arrowIsoSpecΓOfIsAffine f
  have hspec : Surjective (Spec.map a) :=
    (MorphismProperty.arrow_mk_iso_iff @Surjective e).mp inferInstance
  have hx : topologicalKrullDim X = ringKrullDim Γ(X, ⊤) :=
    ((TopCat.homeoOfIso (Scheme.forgetToTop.mapIso X.isoSpec)).isHomeomorph.topologicalKrullDim_eq _).trans
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, ⊤))
  have hy : topologicalKrullDim Y = ringKrullDim Γ(Y, ⊤) :=
    ((TopCat.homeoOfIso (Scheme.forgetToTop.mapIso Y.isoSpec)).isHomeomorph.topologicalKrullDim_eq _).trans
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(Y, ⊤))
  rw [hx, hy]
  exact ringKrullDim_eq_of_integral_surj a.hom
    (RingHom.finite_iff_isIntegral_and_finiteType.mp f.finite_appTop).1 hspec.surj

private theorem ringKrullDim_ne_top_of_finiteType {k A : Type u} [Field k] [CommRing A]
    [Algebra k A] (hA : Algebra.FiniteType k A) :
    ringKrullDim A ≠ ⊤ := by
  obtain ⟨s, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial.mp hA
  refine ne_top_of_le_ne_top ?_ (ringKrullDim_le_of_surjective f.toRingHom hf)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
    zero_add, ← WithBot.coe_top]
  exact fun h ↦ ENat.natCast_ne_top _ (WithBot.coe_inj.mp h)

private theorem group_dimension_ne_top (G : AffineAlgebraicGroup k) :
    topologicalKrullDim G.val.X.left ≠ ⊤ := by
  obtain ⟨A, hA, ⟨e⟩⟩ := groupPresentation G
  let f := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso ((underlying (k := k)).mapIso e))
  have h := f.isHomeomorph.topologicalKrullDim_eq f
  change topologicalKrullDim (PrimeSpectrum A) = topologicalKrullDim G.val.X.left at h
  rw [← h, PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact ringKrullDim_ne_top_of_finiteType hA

private theorem group_dimension_ne_bot (G : AffineAlgebraicGroup k) :
    topologicalKrullDim G.val.X.left ≠ ⊥ := by
  let x := (η[G.val.X]).left (IsLocalRing.closedPoint k)
  let Z : TopologicalSpace.IrreducibleCloseds G.val.X.left :=
    ⟨closure ({x} : Set G.val.X.left), isIrreducible_singleton.closure, isClosed_closure⟩
  letI : Nonempty (TopologicalSpace.IrreducibleCloseds G.val.X.left) := ⟨Z⟩
  exact ne_bot_of_le_ne_bot (by simp : (0 : WithBot ℕ∞) ≠ ⊥) krullDim_nonneg

set_option backward.isDefEq.respectTransparency false in
/-- The two root sets of a central isogeny have the same finite cardinality. -/
theorem absoluteRootCardinality_eq (rootDimension : RootDimension.{u})
    (G₁ G₂ : AffineAlgebraicGroup k) (hG₁ : IsReductive G₁) (hG₂ : IsReductive G₂)
    (T₁ : ClosedSubgroup G₁.val) (T₂ : ClosedSubgroup G₂.val)
    (hs₁ : IsSplitTorus T₁.group) (hm₁ : IsGeometricallyMaximal T₁)
    (hs₂ : IsSplitTorus T₂.group) (hm₂ : IsGeometricallyMaximal T₂)
    (f : G₁.val ⟶ G₂.val) (fT : T₁.group ⟶ T₂.group)
    (hf : IsCentralIsogeny f) (hfT : IsTorusRestriction f fT) :
    (absoluteRoots T₁).Finite ∧ (absoluteRoots T₂).Finite ∧
      (absoluteRoots T₁).ncard = (absoluteRoots T₂).ncard := by
  obtain ⟨hfin₁, hd₁⟩ := rootDimension G₁ hG₁ T₁ hs₁ hm₁
  obtain ⟨hfin₂, hd₂⟩ := rootDimension G₂ hG₂ T₂ hs₂ hm₂
  refine ⟨hfin₁, hfin₂, ?_⟩
  let A₁ := Unipotent.closedSubgroupAlgebraicGroup T₁
  let A₂ := Unipotent.closedSubgroupAlgebraicGroup T₂
  letI : IsAffine G₁.val.X.left := G₁.property.1
  letI : IsAffine G₂.val.X.left := G₂.property.1
  letI : IsAffine T₁.group.X.left := A₁.property.1
  letI : IsAffine T₂.group.X.left := A₂.property.1
  letI := hf.1
  letI := hf.2.2.1
  letI := finiteTorusRestriction hf.1 hfT
  letI := hfT.2.2
  have hG := scheme_dimension_eq_of_finite_surjective f.hom.hom.left
  have hT := scheme_dimension_eq_of_finite_surjective fT.hom.hom.left
  have hn₁ : topologicalKrullDim T₁.group.X.left ≠ ⊥ := group_dimension_ne_bot A₁
  have hn₂ : topologicalKrullDim T₁.group.X.left ≠ ⊤ := group_dimension_ne_top A₁
  rw [hd₁, hd₂, ← hT] at hG
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hn₁
  rw [← hd, ← WithBot.coe_add, ← WithBot.coe_add] at hG
  have hnd : d ≠ ⊤ := by
    intro h
    exact hn₂ (hd.symm.trans (congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) h))
  have he : ((absoluteRoots T₁).ncard : ℕ∞) = (absoluteRoots T₂).ncard :=
    ENat.add_right_injective_of_ne_top hnd (WithBot.coe_inj.mp hG)
  exact ENat.natCast_inj.mp he

set_option backward.isDefEq.respectTransparency false

open private conjugateLe_iff centralizes_iff mono_over comp_conjugateFamily
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private whiskerLeft_pullback from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.FixedPointSchemes

private theorem forget_comp {A B C : GroupScheme k} (a : A ⟶ B) (b : B ⟶ C) :
    (a ≫ b).hom.hom = a.hom.hom ≫ b.hom.hom := rfl

private theorem forget_id (A : GroupScheme k) : (𝟙 A : A ⟶ A).hom.hom = 𝟙 A.X := rfl

private theorem descendAffine {X Y Z : SchemeOver k} (p : X ⟶ Y) (s : X ⟶ Z)
    [IsAffine X.left] [IsAffine Y.left] [Flat p.left] [Surjective p.left]
    (hs : ∀ ⦃A : SchemeOver k⦄ (x y : A ⟶ X), x ≫ p = y ≫ p → x ≫ s = y ≫ s) :
    ∃ d : Y ⟶ Z, p ≫ d = s := by
  haveI : EffectiveEpi p.left := (isRegularEpi_iff_effectiveEpi p.left).mp
    (isRegularEpi_of_flat_of_surjective_of_isAffine p.left)
  have h (A : Scheme) (x y : A ⟶ X.left) (e : x ≫ p.left = y ≫ p.left) :
      x ≫ s.left = y ≫ s.left := by
    let X' : SchemeOver k := Over.mk (x ≫ X.hom)
    let x' : X' ⟶ X := Over.homMk x
    let y' : X' ⟶ X := Over.homMk y (by
      change y ≫ X.hom = x ≫ X.hom
      rw [← Over.w p, ← Category.assoc, ← Category.assoc, e])
    exact congrArg Over.Hom.left (hs x' y' (Over.OverMorphism.ext e))
  let d := EffectiveEpi.desc p.left s.left (h _)
  have hd : p.left ≫ d = s.left := EffectiveEpi.fac p.left s.left (h _)
  haveI : Epi p.left := Flat.epi_of_flat_of_surjective _
  have dw : d ≫ Z.hom = Y.hom := (cancel_epi p.left).mp (by
    rw [← Category.assoc, hd, Over.w s, Over.w p])
  exact ⟨Over.homMk d dw, Over.OverMorphism.ext hd⟩

private theorem descendClosedFactor {X Y Z W : SchemeOver k}
    (p : X ⟶ Y) (j : W ⟶ Z) (g : Y ⟶ Z) (a : X ⟶ W)
    [IsAffine X.left] [IsAffine Y.left] [Flat p.left] [Surjective p.left]
    [Mono j] (ha : a ≫ j = p ≫ g) :
    ∃ b : Y ⟶ W, b ≫ j = g := by
  obtain ⟨b, hb⟩ := descendAffine p a (by
    intro A x y hxy
    apply (cancel_mono j).mp
    rw [Category.assoc, Category.assoc, ha, ← Category.assoc, hxy, Category.assoc])
  haveI : Epi p.left := Flat.epi_of_flat_of_surjective _
  haveI : Epi p := Over.epi_of_epi_left _
  exact ⟨b, (cancel_epi p).mp (by rw [← Category.assoc, hb, ha])⟩

private theorem whiskerRight_isPullback {A B Y : SchemeOver k} (p : A ⟶ B) :
    IsPullback (p ▷ Y) (fst A Y) (fst B Y) p := by
  refine ⟨by simp, ⟨PullbackCone.IsLimit.mk _ (fun c ↦ lift c.snd (c.fst ≫ snd B Y)) ?_ ?_ ?_⟩⟩
  · intro c
    apply CartesianMonoidalCategory.hom_ext
    · simp [c.condition]
    · simp
  · intro c
    simp
  · intro c g h₁ h₂
    apply CartesianMonoidalCategory.hom_ext
    · simpa using h₂
    · simpa using congrArg (fun t ↦ t ≫ snd B Y) h₁

private theorem pushforwardNormalizes {G H : GroupScheme k}
    (U : ClosedSubgroup G) (V : ClosedSubgroup H) (f : G ⟶ H) (qU : U.group ⟶ V.group)
    {A B : SchemeOver k} (q : A ⟶ B) (a : A ⟶ G.X) (b : B ⟶ H.X)
    (hU : qU ≫ V.inclusion = U.inclusion ≫ f) (he : q ≫ b = a ≫ f.hom.hom)
    [IsAffine A.left] [IsAffine B.left] [IsAffine U.group.X.left] [IsAffine V.group.X.left]
    [qUflat : Flat qU.hom.hom.left] [qUsurj : Surjective qU.hom.hom.left]
    [qflat : Flat q.left] [qsurj : Surjective q.left]
    (h : Normalizes U.inclusion a) :
    Normalizes V.inclusion b := by
  haveI : Mono V.inclusion.hom.hom := mono_over _ V.isClosedImmersion
  let p := qU.hom.hom ⊗ₘ q
  have hp₁ := (whiskerRight_isPullback (Y := A) qU.hom.hom).map (Over.forget _)
  have hp₂ := (whiskerLeft_pullback (H := V.group.X) q).map (Over.forget _)
  haveI : Flat p.left := by
    rw [show p = (qU.hom.hom ▷ A) ≫ (V.group.X ◁ q) from MonoidalCategory.tensorHom_def _ _]
    exact MorphismProperty.comp_mem _ _ _
      (MorphismProperty.of_isPullback hp₁.flip qUflat)
      (MorphismProperty.of_isPullback hp₂.flip qflat)
  haveI : Surjective p.left := by
    rw [show p = (qU.hom.hom ▷ A) ≫ (V.group.X ◁ q) from MonoidalCategory.tensorHom_def _ _]
    exact MorphismProperty.comp_mem (@Surjective : MorphismProperty Scheme.{u}) _ _
      (MorphismProperty.of_isPullback hp₁.flip qUsurj)
      (MorphismProperty.of_isPullback hp₂.flip qsurj)
  haveI : IsAffine (U.group.X ⊗ A).left := by rw [Over.tensorObj_left]; infer_instance
  haveI : IsAffine (V.group.X ⊗ B).left := by rw [Over.tensorObj_left]; infer_instance
  have hU' : qU.hom.hom ≫ V.inclusion.hom.hom = U.inclusion.hom.hom ≫ f.hom.hom :=
    congrArg (fun j : U.group ⟶ H ↦ j.hom.hom) hU
  have hg : p ≫ snd V.group.X B ≫ b = (snd U.group.X A ≫ a) ≫ f.hom.hom := by
    dsimp only [p]
    rw [tensorHom_snd_assoc, Category.assoc, he]
  have hu : p ≫ fst V.group.X B ≫ V.inclusion.hom.hom =
      (fst U.group.X A ≫ U.inclusion.hom.hom) ≫ f.hom.hom := by
    dsimp only [p]
    rw [tensorHom_fst_assoc, Category.assoc, hU']
  obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := (normalizesIff k U.inclusion U.isClosedImmersion _ _).mp h
  apply (normalizesIff k V.inclusion V.isClosedImmersion _ _).mpr
  constructor
  · refine descendClosedFactor p V.inclusion.hom.hom _ (c ≫ qU.hom.hom) ?_
    rw [Category.assoc, hU', ← Category.assoc, hc, comp_conjugateFamily]
    unfold conjugateFamily
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, ← hg, ← hu]
  · refine descendClosedFactor p V.inclusion.hom.hom _ (d ≫ qU.hom.hom) ?_
    rw [Category.assoc, hU', ← Category.assoc, hd, comp_conjugateFamily]
    unfold conjugateFamily
    simp only [MonObj.mul_comp, GrpObj.inv_comp, GrpObj.comp_inv, ← hg, ← hu]

open private algebraPoint characterValue_monomial adjointWeightVectors_iff extendCoordinates
  canonicalZero_eq from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private pointMatrix pointMatrix_evaluation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations
open Specs.AdjointRepresentation (TangentCoordinates conjugate)
open scoped Matrix

private theorem diagonalCharacterMap {T S : GroupScheme k} (f : T ⟶ S)
    (eT : diagonal (k := k) (Character T) ≅ T) (eS : diagonal (k := k) (Character S) ≅ S)
    (hT : ∀ χ, eT.hom ≫ χ = monomial χ) (hS : ∀ χ, eS.hom ≫ χ = monomial χ) :
    eT.hom ≫ f = specGroupMap (groupAlgebraMap k (characterPullback f)) ≫ eS.hom := by
  obtain ⟨m, hm⟩ := diagonal_map_exists (eT.hom ≫ f ≫ eS.inv)
  have he (χ : Character S) : m χ = characterPullback f χ := by
    apply (monomial_bijective (k := k) _).injective
    rw [← monomial_natural m χ, hm, ← hS χ, ← hT]
    simp [characterPullback]
  rw [MonoidHom.ext he] at hm
  rw [hm]
  simp

private theorem evaluateCharacter {T : GroupScheme k} (e : diagonal (k := k) (Character T) ≅ T)
    (he : ∀ χ, e.hom ≫ χ = monomial χ) (χ : Character T) (R : TestAlgebra k)
    (a : MonoidAlgebra k (Character T) →ₐ[k] R) :
    characterValue χ R (algebraPoint R a ≫ e.hom.hom.hom) = a (MonoidAlgebra.single χ 1) := by
  change characterValue (characterPullback e.hom χ) R (algebraPoint R a) = _
  change characterValue (e.hom ≫ χ) R (algebraPoint R a) = _
  rw [he χ]
  exact characterValue_monomial R a χ

private abbrev coordinateVector {J : Type u} [Fintype J] (R : TestAlgebra k) (z : J → k) :
    J → R := fun i ↦ algebraMap k R (z i)

private theorem extendCoordinates_apply {G : GroupScheme k} {J : Type u}
    [Fintype J] [AddCommGroup (Lie k G)] [Module k (Lie k G)]
    (b : Module.Basis J k (Lie k G)) (R : TestAlgebra k) (v : Lie k G) :
    extendCoordinates b R v = coordinateVector R (b.equivFun v) := rfl

private theorem exists_ne_zero_coordinate {G : GroupScheme k} {J : Type u}
    [Fintype J] (s : IdentityLieStructure G) {v : Lie k G} (hv : v ≠ 0) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ (b : Module.Basis J k (Lie k G)), ∃ i, b.equivFun v i ≠ 0 := by
  letI := s.lieRing
  letI := s.lieAlgebra
  intro b
  by_contra! h
  apply hv
  have hv' : b.equivFun v = (0 : J → k) := funext h
  exact (b.equivFun.injective (hv'.trans b.equivFun.map_zero.symm)).trans
    (canonicalZero_eq s).symm

private theorem char_eq_of_common_weight (G : AffineAlgebraicGroup k) (T : ClosedSubgroup G.val)
    (e : diagonal (k := k) (Character T.group) ≅ T.group)
    (he : ∀ χ, e.hom ≫ χ = monomial χ) {χ χ' : Character T.group}
    {v : Lie k G.val} (hv : v ≠ 0)
    (h : v ∈ adjointWeightVectors T χ) (h' : v ∈ adjointWeightVectors T χ') : χ = χ' := by
  classical
  obtain ⟨s⟩ := identityLieBracket k G
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨n, b, C, L, l, Ad, hAd, _, _⟩ := adjointRepresentation k G s
  let R := CommAlgCat.of k (MonoidAlgebra k (Character T.group))
  let a : MonoidAlgebra k (Character T.group) →ₐ[k] R := AlgHom.id k _
  let t : GroupPoints T.group R := algebraPoint R a ≫ e.hom.hom.hom
  have eq := ((adjointWeightVectors_iff C l Ad hAd T χ v).mp h R t).symm.trans
    ((adjointWeightVectors_iff C l Ad hAd T χ' v).mp h' R t)
  change characterValue χ R t • extendCoordinates b R v =
    characterValue χ' R t • extendCoordinates b R v at eq
  rw [evaluateCharacter e he χ R a, evaluateCharacter e he χ' R a,
    extendCoordinates_apply] at eq
  obtain ⟨i, hi⟩ := exists_ne_zero_coordinate s hv b
  have eqi := congrFun eq i
  change (MonoidAlgebra.single χ 1 : MonoidAlgebra k (Character T.group)) *
      algebraMap k R (b.equivFun v i) =
    MonoidAlgebra.single χ' 1 * algebraMap k R (b.equivFun v i) at eqi
  simp only [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one] at eqi
  have hcoeff := congrArg (fun x : MonoidAlgebra k (Character T.group) ↦ x.coeff χ) eqi
  by_contra hne
  simp only [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne hne, smul_eq_mul, mul_one, mul_zero] at hcoeff
  exact hi hcoeff

private theorem algHom_mulVec {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] {J : Type u} [Fintype J] [DecidableEq J] (a : A →ₐ[k] B)
    (Q : Matrix J J A) (z : J → k) (i : J) :
    a ((Q *ᵥ coordinateVector (CommAlgCat.of k A) z) i) =
      (a.mapMatrix Q *ᵥ coordinateVector (CommAlgCat.of k B) z) i := by
  have hv : a.toRingHom ∘ coordinateVector (CommAlgCat.of k A) z =
      coordinateVector (CommAlgCat.of k B) z := funext (fun i ↦ a.commutes (z i))
  have h := RingHom.map_mulVec a.toRingHom Q (coordinateVector (CommAlgCat.of k A) z) i
  rw [hv] at h
  exact h

private theorem algHom_coordinateVector_smul {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] {J : Type u} [Fintype J] (a : A →ₐ[k] B)
    (c : A) (z : J → k) (i : J) :
    a ((c • coordinateVector (CommAlgCat.of k A) z) i) =
      (a c • coordinateVector (CommAlgCat.of k B) z) i := by
  change a (c * algebraMap k A (z i)) = a c * algebraMap k B (z i)
  rw [map_mul, AlgHom.commutes]

private theorem transportedWeight
    (G H : AffineAlgebraicGroup k) (T : ClosedSubgroup G.val) (S : ClosedSubgroup H.val)
    (f : G.val ⟶ H.val) (fT : T.group ⟶ S.group) (hfT : IsTorusRestriction f fT)
    (eT : diagonal (k := k) (Character T.group) ≅ T.group)
    (eS : diagonal (k := k) (Character S.group) ≅ S.group)
    (hT : ∀ χ, eT.hom ≫ χ = monomial χ) (hS : ∀ χ, eS.hom ≫ χ = monomial χ)
    (α : Character T.group) {v : Lie k G.val} (hv : v ∈ adjointWeightVectors T α)
    (hn : mapPointKernel f v ≠ 0) :
    ∃ β : Character S.group, characterPullback fT β = α ∧
      mapPointKernel f v ∈ adjointWeightVectors S β := by
  classical
  let M := Character T.group
  let N := Character S.group
  let lT := characterPullback fT
  have hil := characterPullback_injective fT hfT.2.1 hfT.2.2
  let A := CommAlgCat.of k (MonoidAlgebra k M)
  let B := CommAlgCat.of k (MonoidAlgebra k N)
  let a : MonoidAlgebra k N →ₐ[k] MonoidAlgebra k M :=
    (MonoidAlgebra.mapDomainBialgHom k lT).toAlgHom
  let t : GroupPoints T.group A := algebraPoint A (AlgHom.id k _) ≫ eT.hom.hom.hom
  have ht : t ≫ fT.hom.hom = algebraPoint A a ≫ eS.hom.hom.hom := by
    have h := congrArg (fun i : diagonal (k := k) M ⟶ S.group ↦ i.hom.hom)
      (diagonalCharacterMap fT eT eS hT hS)
    change eT.hom.hom.hom ≫ fT.hom.hom =
      (testSpec k).map (CommAlgCat.ofHom a).op ≫ eS.hom.hom.hom at h
    have hid : algebraPoint A (AlgHom.id k _) = 𝟙 (diagonal (k := k) M).X := by
      change (testSpec k).map (𝟙 (op A)) = _
      exact (testSpec k).map_id _
    change (algebraPoint A (AlgHom.id k _) ≫ eT.hom.hom.hom) ≫ fT.hom.hom = _
    rw [hid]
    exact (congrArg (fun z : (diagonal (k := k) M).X ⟶ T.group.X ↦ z ≫ fT.hom.hom)
      (Category.id_comp eT.hom.hom.hom)).trans h
  let w := mapPointKernel f v
  obtain ⟨s⟩ := identityLieBracket k H
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨n, b, C, L, l, Ad, hAd, _, _⟩ := adjointRepresentation k H s
  let J := ULift.{u} (Fin n)
  let ρ : convolutionPoints (groupAlgebra k N) ⟶ Specs.StandardGroups.generalLinearPoints k J :=
    (hopfSpecPointIso (groupAlgebra k N)).hom ≫
      (groupPointsFunctor k).map (eS.hom ≫ S.inclusion ≫ Ad) ≫ l.hom
  let Q := pointMatrix (groupAlgebra k N) ρ
  let z : J → k := b.equivFun w
  have heval (R : TestAlgebra k) (c : MonoidAlgebra k N →ₐ[k] R) :
      ((l.hom.app R).hom (((groupPointsFunctor k).map (S.inclusion ≫ Ad)).app R
        (algebraPoint R c ≫ eS.hom.hom.hom))).val = c.mapMatrix Q := by
    exact pointMatrix_evaluation (groupAlgebra k N) ρ R (WithConv.toConv c)
  have hcoord (R : TestAlgebra k) :
      (C.equiv R (coordinateVector R z)).toMul.val =
        mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R))) w.toMul.val := by
    exact (C.naturality (CommAlgCat.ofHom (Algebra.ofId k R)) (b.equivFun w)).trans
      (congrArg (mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R)))) (C.at_base w))
  have h := mapPointKernel_intertwines f fT hfT α hv A t
  dsimp only at h
  have ha : a.mapMatrix Q *ᵥ coordinateVector A z =
      (MonoidAlgebra.single α 1 : A) • coordinateVector A z := by
    have hval : characterValue α A t = MonoidAlgebra.single α 1 :=
      evaluateCharacter eT hT α A (AlgHom.id k _)
    rw [← hcoord A, hval, ← C.smul] at h
    change conjugate ((t ≫ fT.hom.hom) ≫ S.inclusion.hom.hom)
        (C.equiv A (coordinateVector A z)) =
      (C.equiv A ((MonoidAlgebra.single α 1 : A) • coordinateVector A z)).toMul.val at h
    rw [← hAd, ht] at h
    have hcomp :
        ((groupPointsFunctor k).map Ad).app A
            ((algebraPoint A a ≫ eS.hom.hom.hom) ≫ S.inclusion.hom.hom) =
          ((groupPointsFunctor k).map (S.inclusion ≫ Ad)).app A
            (algebraPoint A a ≫ eS.hom.hom.hom) := by
      rw [Functor.map_comp, NatTrans.comp_app]
      rfl
    rw [hcomp, heval A a] at h
    apply (Subtype.val_injective.comp (C.equiv A).injective)
    exact h
  have ha' (i : J) : a ((Q *ᵥ coordinateVector B z) i) = MonoidAlgebra.single α (z i) := by
    rw [algHom_mulVec, ha]
    change MonoidAlgebra.single α 1 * algebraMap k A (z i) = _
    simp [Algebra.algebraMap_eq_smul_one, MonoidAlgebra.smul_single]
  obtain ⟨i, hi⟩ := exists_ne_zero_coordinate s hn b
  have hr : α ∈ Set.range lT := by
    by_contra hnα
    have hc := congrArg (fun x : A ↦ MonoidAlgebra.coeff x α) (ha' i)
    change (Finsupp.mapDomain lT (MonoidAlgebra.coeff ((Q *ᵥ coordinateVector B z) i))) α =
      (MonoidAlgebra.single α (z i)).coeff α at hc
    rw [Finsupp.mapDomain_of_notMem_range _ _ hnα, MonoidAlgebra.coeff_single,
      Finsupp.single_eq_same] at hc
    exact hi hc.symm
  obtain ⟨β, hβ⟩ := hr
  have hb : Q *ᵥ coordinateVector B z = (MonoidAlgebra.single β 1 : B) • coordinateVector B z := by
    funext j
    apply MonoidAlgebra.mapDomain_injective (R := k) hil
    change a ((Q *ᵥ coordinateVector B z) j) =
      a (((MonoidAlgebra.single β 1 : B) • coordinateVector B z) j)
    have haβ : a (MonoidAlgebra.single β 1) = MonoidAlgebra.single α 1 := by
      change (MonoidAlgebra.mapDomainBialgHom k lT) (MonoidAlgebra.single β 1) = _
      rw [MonoidAlgebra.mapDomainBialgHom_single, hβ]
    rw [algHom_coordinateVector_smul, haβ]
    exact (ha' j).trans (by simp [Algebra.algebraMap_eq_smul_one,
      MonoidAlgebra.smul_single])
  refine ⟨β, hβ, (adjointWeightVectors_iff C l Ad hAd S β w).mpr ?_⟩
  intro R y
  let d : GroupPoints (diagonal (k := k) N) R := y ≫ eS.inv.hom.hom
  let c' : op R ⟶ op (CommAlgCat.of k (MonoidAlgebra k N)) :=
    (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage d
  let c : MonoidAlgebra k N →ₐ[k] R := c'.unop.hom
  have hc : algebraPoint R c = d :=
    (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage d
  have hy : algebraPoint R c ≫ eS.hom.hom.hom = y := by
    rw [hc]
    change (y ≫ eS.inv.hom.hom) ≫ eS.hom.hom.hom = y
    have h := congrArg (fun j : S.group ⟶ S.group ↦ j.hom.hom) eS.inv_hom_id
    change eS.inv.hom.hom ≫ eS.hom.hom.hom = 𝟙 S.group.X at h
    rw [Category.assoc, h, Category.comp_id]
  dsimp only
  rw [← hy, heval R c, evaluateCharacter eS hS, extendCoordinates_apply]
  funext j
  rw [← algHom_mulVec, hb, algHom_coordinateVector_smul]

private theorem differential_weight_nonzero
    (rootSubgroups : RootSubgroups.{u}) (centre : CentreFormula.{u})
    (G H : AffineAlgebraicGroup k) (hG : IsReductive G) (T : ClosedSubgroup G.val)
    (hs : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T)
    (f : G.val ⟶ H.val) (hf : IsCentralIsogeny f) {α : Character T.group}
    (hα : α ≠ 1) {v : Lie k G.val} (hv : v ∈ adjointWeightVectors T α) (hn : v ≠ 0) :
    mapPointKernel f v ≠ 0 := by
  intro hz
  obtain ⟨_, e, he, _, _⟩ := centre G hG T hs hm
  exact hα (char_eq_of_common_weight G T e he hn hv
    (lieKernel_le_zeroWeight rootSubgroups centre G H hG T hs hm f hf hz))

open Specs.RootGroups (AdditiveLine HasScalarAction IsRootSubgroup rootPoint)
open Specs.RankOneFlag (SameSubgroup IsSplitAdditive)
open private hom_ext_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes
open private kernel_of_closed_factor from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries
open private isIso_of_trivial_kernel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness

private theorem rootPoint_map {A : AdditiveLine k} {G : GroupScheme k} (x : A.group ⟶ G)
    {R S : TestAlgebra k} (b : R ⟶ S) (a : R) :
    mapPoints b (rootPoint x R a) = rootPoint x S (b.hom a) := by
  have he : b.hom.comp (Polynomial.aeval a) = Polynomial.aeval (b.hom a) :=
    Polynomial.algHom_ext (by simp)
  change (testSpec k).map b.op ≫ (testSpec k).map (CommAlgCat.ofHom
    (Polynomial.aeval a : Polynomial k →ₐ[k] R)).op ≫ x.hom.hom = _
  rw [← Category.assoc, ← Functor.map_comp]
  unfold rootPoint
  congr 2
  exact congrArg (fun f : Polynomial k →ₐ[k] S ↦ (CommAlgCat.ofHom f).op) he

private theorem rootPoint_id_bijective (A : AdditiveLine k) (R : TestAlgebra k) :
    Function.Bijective (rootPoint (𝟙 A.group) R) := by
  classical
  let e := algSpec.fullyFaithful (R := CommRingCat.of k)
  have hf (a : R) :
      rootPoint (𝟙 A.group) R a =
        (testSpec k).map (CommAlgCat.ofHom (Polynomial.aeval a : Polynomial k →ₐ[k] R)).op := by
    change _ ≫ 𝟙 ((testSpec k).obj (op (CommAlgCat.of k (Polynomial k)))) = _
    exact Category.comp_id _
  constructor
  · intro a b hab
    rw [hf, hf] at hab
    have h := congrArg (fun j ↦ j.unop.hom Polynomial.X) (e.map_injective hab)
    change (Polynomial.aeval a : Polynomial k →ₐ[k] R) Polynomial.X =
      (Polynomial.aeval b : Polynomial k →ₐ[k] R) Polynomial.X at h
    simpa only [Polynomial.aeval_X] using h
  · intro p
    let c : op R ⟶ op (CommAlgCat.of k (Polynomial k)) := e.preimage p
    refine ⟨c.unop.hom Polynomial.X, ?_⟩
    have hc : (CommAlgCat.ofHom (Polynomial.aeval (c.unop.hom Polynomial.X))).op = c := by
      apply Quiver.Hom.unop_inj
      apply CommAlgCat.hom_ext
      apply Polynomial.algHom_ext
      exact Polynomial.aeval_X _
    rw [hf, hc]
    exact e.map_preimage p

private theorem rootPoint_zero {A : AdditiveLine k} {G : GroupScheme k}
    (x : A.group ⟶ G) (R : TestAlgebra k) : rootPoint x R 0 = 1 := by
  letI := A.operations.hopf
  let H : HopfAlgebraCategory k := CommHopfAlgCat.of k (Polynomial k)
  let a : WithConv (Polynomial k →ₐ[k] R) := 1
  have hc : Polynomial.aeval (0 : R) = a.ofConv := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X]
    change 0 = algebraMap k R (A.operations.epsilon Polynomial.X)
    rw [A.counit, map_zero]
  have hm : (testSpec k).map (CommAlgCat.ofHom a.ofConv).op = (1 : GroupPoints A.group R) :=
    ((hopfSpecPointIso H).hom.app R).hom.map_one
  calc
    rootPoint x R 0 = (1 : GroupPoints A.group R) ≫ x.hom.hom := by
      change (testSpec k).map (CommAlgCat.ofHom (Polynomial.aeval (0 : R))).op ≫ x.hom.hom = _
      rw [hc]
      exact congrArg (fun g : GroupPoints A.group R ↦ g ≫ x.hom.hom) hm
    _ = 1 := MonObj.one_comp _

private theorem rootPoint_injective {A : AdditiveLine k} {G : GroupScheme k}
    (x : A.group ⟶ G) [Mono x.hom.hom] (R : TestAlgebra k) :
    Function.Injective (rootPoint x R) := by
  intro a b h
  apply (rootPoint_id_bijective A R).1
  apply (cancel_mono x.hom.hom).mp
  change (((testSpec k).map (CommAlgCat.ofHom (Polynomial.aeval a)).op ≫
    𝟙 ((testSpec k).obj (op (CommAlgCat.of k (Polynomial k))))) ≫ x.hom.hom) =
      ((testSpec k).map (CommAlgCat.ofHom (Polynomial.aeval b)).op ≫
        𝟙 ((testSpec k).obj (op (CommAlgCat.of k (Polynomial k))))) ≫ x.hom.hom
  change (testSpec k).map (CommAlgCat.ofHom (Polynomial.aeval a)).op ≫ x.hom.hom =
    (testSpec k).map (CommAlgCat.ofHom (Polynomial.aeval b)).op ≫ x.hom.hom at h
  simpa only [Category.comp_id] using h

private theorem central_rootPoint_parameter_eq_zero {G : GroupScheme k} (T : ClosedSubgroup G)
    {α : Character T.group} (hα : α ≠ 1)
    (e : diagonal (k := k) (Character T.group) ≅ T.group)
    (he : ∀ χ, e.hom ≫ χ = monomial χ)
    {A : AdditiveLine k} (x : A.group ⟶ G) [Mono x.hom.hom] (hx : HasScalarAction T α x)
    (R : TestAlgebra k) (a : R) (h : Centralizes (𝟙 G) (rootPoint x R a)) : a = 0 := by
  classical
  let M := Character T.group
  let S := CommAlgCat.of k (MonoidAlgebra R M)
  let b : R ⟶ S := CommAlgCat.ofHom (IsScalarTower.toAlgHom k R (MonoidAlgebra R M))
  let c := MonoidAlgebra.mapAlgHom M (Algebra.ofId k R)
  let t : GroupPoints T.group S := algebraPoint S c ≫ e.hom.hom.hom
  have hn : Commute (rootPoint x S (b.hom a)) (t ≫ T.inclusion.hom.hom) := by
    have hc := (centralizes_iff (𝟙 G) (rootPoint x R a)).mp h
      ((testSpec k).obj (op S)) ((testSpec k).map b.op) (t ≫ T.inclusion.hom.hom)
    change Commute (mapPoints b (rootPoint x R a))
      ((t ≫ T.inclusion.hom.hom) ≫ (𝟙 G : G ⟶ G).hom.hom) at hc
    rwa [rootPoint_map, forget_id, Category.comp_id] at hc
  have hh := hx S t (b.hom a)
  dsimp only at hh
  rw [← hn.eq, mul_inv_cancel_right] at hh
  have hl := rootPoint_injective x S hh
  have hval : characterValue α S t = MonoidAlgebra.single α 1 := by
    rw [evaluateCharacter e he α S c]
    change MonoidAlgebra.mapAlgHom M (Algebra.ofId k R) (MonoidAlgebra.single α 1) = _
    rw [MonoidAlgebra.mapAlgHom_single, map_one]
  rw [hval] at hl
  change MonoidAlgebra.single 1 a = MonoidAlgebra.single α (1 : R) * MonoidAlgebra.single 1 a at hl
  rw [MonoidAlgebra.single_mul_single, mul_one, one_mul] at hl
  have hl' := congrArg (fun p : MonoidAlgebra R M ↦ p.coeff 1) hl
  have hne : (1 : M) ≠ α := fun h ↦ hα h.symm
  rw [MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne hne] at hl'
  exact hl'

private theorem sameSubgroupIso {G : GroupScheme k} {U V : ClosedSubgroup G}
    (h : SameSubgroup U V) : ∃ e : U.group ≅ V.group, e.hom ≫ V.inclusion = U.inclusion := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := h
  let F := Grp.forget (SchemeOver k)
  letI : Mono U.inclusion :=
    F.mono_of_mono_map (f := U.inclusion) (mono_over U.inclusion.hom.hom U.isClosedImmersion)
  letI : Mono V.inclusion :=
    F.mono_of_mono_map (f := V.inclusion) (mono_over V.inclusion.hom.hom V.isClosedImmersion)
  exact ⟨⟨p, q,
    (cancel_mono U.inclusion).mp (by rw [Category.assoc, hq, hp, Category.id_comp]),
    (cancel_mono V.inclusion).mp (by rw [Category.assoc, hp, hq, Category.id_comp])⟩, hp⟩

private theorem zero_mem_adjointWeight (G : AffineAlgebraicGroup k) (T : ClosedSubgroup G.val)
    (α : Character T.group) : (0 : Lie k G.val) ∈ adjointWeightVectors T α := by
  obtain ⟨s⟩ := identityLieBracket k G
  letI := s.lieRing
  letI := s.lieAlgebra
  rw [← RootData.CharacterPairing.adjointWeightSpaceVectors G T s α, canonicalZero_eq s]
  exact (Specs.CharacterPairing.adjointWeightSpace T α s).zero_mem

set_option backward.isDefEq.respectTransparency false in
private theorem rootGroup_pushforward
    (roots : RootSubgroups.{u}) (centre : CentreFormula.{u})
    (G H : AffineAlgebraicGroup k) (hG : IsReductive G) (hH : IsReductive H)
    (T : ClosedSubgroup G.val) (S : ClosedSubgroup H.val)
    (hsT : IsSplitTorus T.group) (hmT : IsGeometricallyMaximal T)
    (hsS : IsSplitTorus S.group) (hmS : IsGeometricallyMaximal S)
    (f : G.val ⟶ H.val) (fT : T.group ⟶ S.group)
    (hf : IsCentralIsogeny f) (hfT : IsTorusRestriction f fT)
    (β : Character S.group) (hβ : β ∈ absoluteRoots S)
    (hα : characterPullback fT β ∈ absoluteRoots T)
    (V₁ : ClosedSubgroup G.val) (V₂ : ClosedSubgroup H.val)
    (hV₁ : IsRootSubgroup T V₁ (characterPullback fT β))
    (hV₂ : IsRootSubgroup S V₂ β) :
    ∃ e : V₁.group ≅ V₂.group, e.hom ≫ V₂.inclusion = V₁.inclusion ≫ f := by
  let α := characterPullback fT β
  obtain ⟨_, eT, hT, _, _⟩ := centre G hG T hsT hmT
  obtain ⟨_, eS, hS, _, _⟩ := centre H hH S hsS hmS
  obtain ⟨_, _, U, hU, _, _, ⟨A, x, hx⟩, huniq⟩ := (roots G hG T hsT hmT).2 α hα
  obtain ⟨e₁, he₁⟩ := sameSubgroupIso (huniq V₁ hV₁)
  let U₀ := Unipotent.closedSubgroupAlgebraicGroup U
  let F : U₀.val ⟶ H.val := U.inclusion ≫ f
  obtain ⟨I, p, i, K, hp, _, hk, hq⟩ := schemeImageQuotient U₀ H F
  let J : ClosedSubgroup H.val := ⟨_, i, hp.2.2.2.2.2⟩
  obtain ⟨N, hn, hcentral⟩ := hf.2.2.2
  haveI := mono_over _ U.isClosedImmersion
  haveI : IsIso x.hom.hom.hom := (Grp.forget (SchemeOver k)).map_isIso x.hom
  haveI : Mono (x.hom ≫ U.inclusion).hom.hom := mono_comp _ _
  have hk_zero : K.inclusion = 0 := by
    apply Grp.hom_ext
    apply hom_ext_of_points (Unipotent.closedSubgroupAlgebraicGroup K).property.1
    intro R t
    let g : GroupPoints U.group R := t ≫ K.inclusion.hom.hom
    let d : GroupPoints A.group R := g ≫ x.inv.hom.hom
    obtain ⟨a, ha⟩ := (rootPoint_id_bijective A R).2 d
    have hag : rootPoint x.hom R a = g := by
      change (rootPoint (𝟙 A.group) R a) ≫ x.hom.hom.hom = g
      rw [ha]
      simp only [d, Category.assoc, ← forget_comp x.inv, Iso.inv_hom_id,
        forget_id, Category.comp_id]
    have hh : g ≫ F.hom.hom = 1 :=
      (schemeKernel_sections hk g).mp ⟨t, rfl⟩
    have hh' : (g ≫ U.inclusion.hom.hom) ≫ f.hom.hom = 1 := hh
    obtain ⟨z, hz⟩ := (schemeKernel_sections hn _).mpr hh'
    have hz' : Centralizes (𝟙 G.val) (z ≫ N.inclusion.hom.hom) := by
      apply (centralizes_iff _ _).mpr
      intro Y y t
      simpa only [Category.assoc] using
        (centralizes_iff _ _).mp hcentral Y (y ≫ z) t
    change z ≫ N.inclusion.hom.hom = g ≫ U.inclusion.hom.hom at hz
    rw [hz, ← hag] at hz'
    have ha0 := central_rootPoint_parameter_eq_zero T hα.1 eT hT (x.hom ≫ U.inclusion) hx R a
      (by
        change Centralizes (𝟙 G.val) ((rootPoint x.hom R a) ≫ U.inclusion.hom.hom)
        exact hz')
    change g = t ≫ (0 : K.group ⟶ U.group).hom.hom
    have hzero : (0 : K.group ⟶ U.group).hom.hom = (1 : K.group.X ⟶ U.group.X) := rfl
    rw [hzero, MonObj.comp_one, ← hag, ha0, rootPoint_zero]
  have hmK := mono_over _ K.isClosedImmersion
  haveI : Mono K.inclusion :=
    (Grp.forget (SchemeOver k)).mono_of_mono_map (f := K.inclusion) hmK
  have hz := IsZero.of_mono_eq_zero K.inclusion hk_zero
  have hk' := kernel_of_closed_factor F p i hp.1 hp.2.2.2.2.2 K hk
  letI := isIso_of_trivial_kernel p K ⟨hk', hp.2.1, hp.2.2.1, hp.2.2.2.1, hq⟩
    ⟨hz.iso (Grp.isZero_trivial _)⟩
  let e : U.group ≅ J.group := asIso p
  have hpi : e.hom ≫ J.inclusion = U.inclusion ≫ f := hp.1
  haveI : IsAffine T.group.X.left := (Unipotent.closedSubgroupAlgebraicGroup T).property.1
  haveI : IsAffine S.group.X.left := (Unipotent.closedSubgroupAlgebraicGroup S).property.1
  haveI : IsAffine U.group.X.left := U₀.property.1
  haveI : IsAffine J.group.X.left := I.property.1
  haveI := hp.2.1
  haveI := hp.2.2.1
  haveI := hfT.2.1
  haveI := hfT.2.2
  have hJ : IsRootSubgroup S J β := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · haveI : IsIso e.inv.hom.hom.left := (underlying (k := k)).map_isIso e.inv
      haveI : Etale e.inv.hom.hom.left := inferInstance
      rw [← Over.w e.inv.hom.hom]
      exact MorphismProperty.comp_mem (@Smooth : MorphismProperty Scheme.{u}) _ _
        (inferInstanceAs (Smooth e.inv.hom.hom.left)) hU.1
    · obtain ⟨c, hc, hε, hi, ⟨s⟩⟩ := hU.2.1
      exact ⟨c, hc, hε, hi, ⟨e.symm ≪≫ s⟩⟩
    · exact pushforwardNormalizes U J f p fT.hom.hom T.inclusion.hom.hom S.inclusion.hom.hom
        hp.1 (congrArg (fun l : T.group ⟶ H.val ↦ l.hom.hom) hfT.1) hU.2.2.1
    · rintro _ ⟨w, rfl⟩
      let v := mapPointKernel e.inv w
      have hvw : mapPointKernel e.hom v = w := by
        change mapPointKernel e.hom (mapPointKernel e.inv w) = w
        rw [← (lieFunctoriality k).2.2, Iso.inv_hom_id]
        exact (lieFunctoriality k).2.1 _ w
      have hw : mapPointKernel f (mapPointKernel U.inclusion v) =
          mapPointKernel J.inclusion w := by
        rw [← (lieFunctoriality k).2.2, ← hpi, (lieFunctoriality k).2.2, hvw]
      rw [← hw]
      by_cases hzero : mapPointKernel f (mapPointKernel U.inclusion v) = 0
      · rw [hzero]
        exact zero_mem_adjointWeight H S β
      · obtain ⟨β', hβ', h'⟩ :=
          transportedWeight G H T S f fT hfT eT eS hT hS α
            (hU.2.2.2 ⟨v, rfl⟩) hzero
        have hb : β' = β := characterPullback_injective fT hfT.2.1 hfT.2.2 hβ'
        exact hb ▸ h'
  obtain ⟨_, _, V, _, _, _, _, hVuniq⟩ := (roots H hH S hsS hmS).2 β hβ
  obtain ⟨eJ, heJ⟩ := sameSubgroupIso (hVuniq J hJ)
  obtain ⟨e₂, he₂⟩ := sameSubgroupIso (hVuniq V₂ hV₂)
  have hJ' : eJ.inv ≫ V.inclusion = J.inclusion := by
    rw [← heJ, Iso.inv_hom_id_assoc]
  have h₁' : e₁.inv ≫ U.inclusion = V₁.inclusion := by
    rw [← he₁, Iso.inv_hom_id_assoc]
  refine ⟨e₁.symm ≪≫ e ≪≫ eJ.symm ≪≫ e₂, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, he₂, hJ', hpi]
  rw [← Category.assoc, h₁']

open Specs.CharacterDescent (Cocharacter)
open Specs.AbstractPairing (IsAttachedCoroot)
open Specs.RootGroups (CorootReflection)
open Specs.CharacterPairing (pairing)
open Specs.NormalizerLatticeAction (ConstantGroup SplitImage)
open private pairing_eq_iff isTorus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private apply_conjugateFamily_eq from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.NormalizerLatticeAction

private theorem constantFamily {Q : GroupScheme k} {W : Type u} [Group W]
    (S : ConstantGroup Q W) {Y : SchemeOver k} [PreconnectedSpace Y.left]
    (p : Y ⟶ Q.X) (y : Y.left) :
    p = toUnit Y ≫ S.sectionPoint (S.families Y p y) := by
  apply (S.families Y).injective
  rw [S.constant]
  exact LocallyConstant.eq_const _ y

private theorem normalizerPoint_action {G : AffineAlgebraicGroup k}
    (T : ClosedSubgroup G.val) {N : ClosedSubgroup G.val}
    {W : GroupScheme k} {q : N.group ⟶ W}
    (hN : RepresentsSubgroup N (fun _ g ↦ Normalizes T.inclusion g))
    (D : SplitImage T.inclusion N.inclusion q)
    (g : 𝟙_ (SchemeOver k) ⟶ G.val.X) (hg : Normalizes T.inclusion g) :
    ∃ w : D.labels, (D.conjugation w).hom.hom.hom ≫ T.inclusion.hom.hom =
      (toUnit T.group.X ≫ g) * T.inclusion.hom.hom * (toUnit T.group.X ≫ g)⁻¹ := by
  obtain ⟨n, hn⟩ := (hN _ _).mp hg
  let K := 𝟙_ (SchemeOver k)
  haveI : Subsingleton K.left := inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
  let y : K.left := IsLocalRing.closedPoint k
  let w := D.constantGroup.families K (n ≫ q.hom.hom) y
  have hw := constantFamily D.constantGroup (n ≫ q.hom.hom) y
  have h := apply_conjugateFamily_eq T.inclusion (n ≫ N.inclusion.hom.hom) (D.conjugation w)
    (D.conjugates K n w hw) (toUnit T.group.X) (𝟙 _)
  refine ⟨w, ?_⟩
  simpa only [Category.id_comp, Category.assoc, hn, forget_comp] using h

/-- Two integral reflections with the same root in a finite group have equal
reflection functionals. Their product acts by a shear with square-zero part. -/
private theorem finite_reflection_functionals {M : Type u} [CommGroup M] [Module.Free ℤ (Additive M)]
    (W : Subgroup (MulAut M)) [Finite W] (a b : W) (α : M) (hα : α ≠ 1)
    (ℓ₁ ℓ₂ : Additive M →ₗ[ℤ] ℤ) (h₁ : ℓ₁ (Additive.ofMul α) = 2)
    (h₂ : ℓ₂ (Additive.ofMul α) = 2)
    (ha : ∀ χ : M, a.val χ = χ * α ^ (-ℓ₁ (Additive.ofMul χ)))
    (hb : ∀ χ : M, b.val χ = χ * α ^ (-ℓ₂ (Additive.ofMul χ))) :
    ℓ₁ = ℓ₂ := by
  let r := Additive.ofMul α
  let d := ℓ₂ - ℓ₁
  have hd : d r = 0 := by simp [d, r, h₁, h₂]
  have hs (x : Additive M) : Additive.ofMul ((a * b).val x.toMul) = x + d x • r := by
    change Additive.ofMul (a.val (b.val x.toMul)) = _
    rw [ha, hb, ofMul_mul, ofMul_zpow, ofMul_mul, ofMul_zpow]
    have hcalc : ℓ₁ (x + (-ℓ₂ x) • r) = ℓ₁ x - 2 * ℓ₂ x := by
      rw [map_add, map_smul, show ℓ₁ r = 2 from h₁, smul_eq_mul]
      ring
    change (x + (-ℓ₂ x) • r) + (-ℓ₁ (x + (-ℓ₂ x) • r)) • r = _
    rw [hcalc, add_assoc, ← add_smul]
    have : -ℓ₂ x + -(ℓ₁ x - 2 * ℓ₂ x) = d x := by
      change _ = ℓ₂ x - ℓ₁ x
      ring
    rw [this]
  have hp (n : ℕ) (x : Additive M) :
      Additive.ofMul (((a * b) ^ n).val x.toMul) = x + (n : ℤ) • (d x • r) := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ']
        change Additive.ofMul ((a * b).val (((a * b) ^ n).val x.toMul)) = _
        calc
          _ = (x + (n : ℤ) • (d x • r)) + d (x + (n : ℤ) • (d x • r)) • r := by
            have e := hs (Additive.ofMul (((a * b) ^ n).val x.toMul))
            conv_rhs at e => rw [ih]
            exact e
          _ = _ := by
            rw [map_add, map_smul, map_smul, hd, smul_zero, smul_zero, add_zero,
              add_assoc, Nat.cast_succ, add_smul, one_smul]
  have horder : 0 < orderOf (a * b) := orderOf_pos _
  ext x
  have hpower := hp (orderOf (a * b)) x
  rw [pow_orderOf_eq_one] at hpower
  change x = x + (orderOf (a * b) : ℤ) • (d x • r) at hpower
  have hz : (orderOf (a * b) : ℤ) • (d x • r) = 0 := add_left_cancel (hpower.symm.trans (add_zero x).symm)
  have hd0 : d x • r = 0 := (smul_eq_zero.mp hz).resolve_left (by exact_mod_cast horder.ne')
  have hr0 : r ≠ 0 := hα
  have hdx : d x = 0 := (smul_eq_zero.mp hd0).resolve_right hr0
  exact (sub_eq_zero.mp hdx).symm

private theorem pairing_pushforward {T S : GroupScheme k} (f : T ⟶ S)
    (χ : Character S) (c : Cocharacter T) :
    pairing S χ (c ≫ f) = pairing T (characterPullback f χ) c := by
  apply (pairing_eq_iff _ _ _).mp
  change (c ≫ f) ≫ χ = _
  rw [Category.assoc]
  exact (pairing_eq_iff _ _ _).mpr rfl

set_option backward.isDefEq.respectTransparency false in
private theorem attachedCoroot_pushforward
    (G H : AffineAlgebraicGroup k) (hH : IsReductive H)
    (T : ClosedSubgroup G.val) (S : ClosedSubgroup H.val)
    (hs : IsSplitTorus S.group) (hm : IsGeometricallyMaximal S)
    (f : G.val ⟶ H.val) (fT : T.group ⟶ S.group) (hfT : IsTorusRestriction f fT)
    (β : Character S.group) (hβ : β ∈ absoluteRoots S)
    (hα : characterPullback fT β ∈ absoluteRoots T)
    (c₁ : Cocharacter T.group) (c₂ : Cocharacter S.group)
    (hc₁ : IsAttachedCoroot T ⟨characterPullback fT β, hα⟩ c₁)
    (hc₂ : IsAttachedCoroot S ⟨β, hβ⟩ c₂) :
    c₁ ≫ fT = c₂ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, r₁, rfl⟩ := hc₁
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, r₂, rfl⟩ := hc₂
  obtain ⟨N, j, hjc, W, q, hN, hj, hq, _, _, _, hD⟩ :=
    Reductive.WeylScheme.weylScheme H hH S (isTorus_of_split hs) hm
  obtain ⟨⟨D⟩, _⟩ := hD hs
  let K := 𝟙_ (SchemeOver k)
  let g : K ⟶ H.val.X := r₁.representative ≫ f.hom.hom
  haveI : IsAffine K.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))
  haveI : IsAffine S.group.X.left := (Unipotent.closedSubgroupAlgebraicGroup S).property.1
  haveI : IsAffine T.group.X.left := (Unipotent.closedSubgroupAlgebraicGroup T).property.1
  haveI := hfT.2.1
  haveI := hfT.2.2
  have hn : Normalizes S.inclusion g :=
    pushforwardNormalizes T S f fT (𝟙 K) r₁.representative g hfT.1
      (Category.id_comp _) r₁.normalizes
  obtain ⟨a, ha⟩ := normalizerPoint_action S hN D g hn
  obtain ⟨b, hb⟩ := normalizerPoint_action S hN D r₂.representative r₂.normalizes
  have hf : fT.hom.hom ≫ S.inclusion.hom.hom = T.inclusion.hom.hom ≫ f.hom.hom :=
    congrArg (fun l : T.group ⟶ H.val ↦ l.hom.hom) hfT.1
  haveI : Mono S.inclusion.hom.hom := mono_over _ S.isClosedImmersion
  have hi : fT ≫ (D.conjugation a).hom = r₁.conjugation.hom ≫ fT := by
    apply Grp.hom_ext
    apply (cancel_mono S.inclusion.hom.hom).mp
    let n := toUnit T.group.X ≫ r₁.representative
    have h₁ : r₁.conjugation.hom.hom.hom ≫ T.inclusion.hom.hom =
        n * T.inclusion.hom.hom * n⁻¹ := r₁.conjugates
    change (fT.hom.hom ≫ (D.conjugation a).hom.hom.hom) ≫ S.inclusion.hom.hom =
      (r₁.conjugation.hom.hom.hom ≫ fT.hom.hom) ≫ S.inclusion.hom.hom
    rw [Category.assoc, ha, Category.assoc, hf]
    calc
      fT.hom.hom ≫ ((toUnit S.group.X ≫ g) * S.inclusion.hom.hom * (toUnit S.group.X ≫ g)⁻¹) =
          (n * T.inclusion.hom.hom * n⁻¹) ≫ f.hom.hom := by
        simp only [MonObj.comp_mul, GrpObj.comp_inv, MonObj.mul_comp, GrpObj.inv_comp,
          comp_toUnit_assoc, hf, n, g, Category.assoc]
      _ = _ := by rw [← h₁, Category.assoc]
  have hi' : fT ≫ (D.conjugation a).inv = r₁.conjugation.inv ≫ fT := by
    rw [← cancel_mono (D.conjugation a).hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Category.assoc, hi, Iso.inv_hom_id_assoc]
  have hb' : (D.conjugation b).hom = r₂.conjugation.hom := by
    apply Grp.hom_ext
    apply (cancel_mono S.inclusion.hom.hom).mp
    exact hb.trans r₂.conjugates.symm
  have hb'' : (D.conjugation b).inv = r₂.conjugation.inv := congrArg Iso.inv (Iso.ext hb')
  let c : Cocharacter S.group := r₁.coroot ≫ fT
  let d := r₂.coroot
  have ha' (χ : Character S.group) : a.val χ = χ * β ^ (-pairing S.group χ c) := by
    apply characterPullback_injective fT hfT.2.1 hfT.2.2
    rw [D.characterAction, map_mul, map_zpow]
    change fT ≫ (D.conjugation a).inv ≫ χ =
      characterPullback fT χ * characterPullback fT β ^ (-pairing S.group χ c)
    rw [← Category.assoc, hi', Category.assoc]
    rw [r₁.reflection, pairing_pushforward]
    rfl
  have hb₁ (χ : Character S.group) : b.val χ = χ * β ^ (-pairing S.group χ d) := by
    rw [D.characterAction, hb'', r₂.reflection]
  obtain ⟨hcomm, hfree, _, _, _, P, hp, hP⟩ :=
    RootData.CharacterPairing.perfectCharacterPairing S.group hs
  letI := hcomm
  letI := hfree
  letI := D.finite
  have hℓ₁ : P (Additive.ofMul β) (Additive.ofMul c) = 2 := by
    rw [hP, pairing_pushforward]
    exact r₁.root_pairing
  have hℓ₂ : P (Additive.ofMul β) (Additive.ofMul d) = 2 :=
    (hP _ _).trans r₂.root_pairing
  have hℓ := finite_reflection_functionals D.labels a b β hβ.1
    (P.flip (Additive.ofMul c)) (P.flip (Additive.ofMul d)) hℓ₁ hℓ₂
    (fun χ ↦ by rw [ha', LinearMap.flip_apply, hP])
    (fun χ ↦ by rw [hb₁, LinearMap.flip_apply, hP])
  exact congrArg Additive.toMul (hp.bijective_right.injective hℓ)

open Specs.GeometricRadicals (IsSemisimple IsTorus IsMaximalTorus baseChangedSubgroup)
open private solvable_iff_sections
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private unipotent_sections_solvable torus_commutative from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private torus_smooth_connected_solvable from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private baseChangeKernelSquare baseChangeMapPullback from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components
open private extendedGroupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private splitPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing

private theorem reductive_of_semisimple (G : AffineAlgebraicGroup k) (hG : IsSemisimple G) :
    IsReductive G := by
  let U := Specs.GeometricRadicals.geometricUnipotentRadical G
  let S := Specs.GeometricRadicals.geometricSolvableRadical G
  let A := Unipotent.closedSubgroupAlgebraicGroup U
  obtain ⟨hu, hU, _⟩ := LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest G
  obtain ⟨_, _, hmax⟩ := LinearAlgebraicGroups.GeometricRadicals.geometricSolvableRadicalLargest G
  have hsol := (solvable_iff_sections A hu.1 hu.2.1).mpr (unipotent_sections_solvable A hU)
  obtain ⟨j, hj⟩ := hmax U hu hsol
  obtain ⟨e⟩ := hG.2.2
  letI : Mono U.inclusion := (Grp.forget (SchemeOver (AlgebraicClosure k))).mono_of_mono_map
    (f := U.inclusion) (mono_over U.inclusion.hom.hom U.isClosedImmersion)
  have hj0 : j = 0 := IsZero.eq_of_tgt ((Grp.isZero_trivial _).of_iso e) _ _
  have hu0 : U.inclusion = 0 := by rw [← hj, hj0, zero_comp]
  exact ⟨hG.1, hG.2.1, ⟨(IsZero.of_mono_eq_zero U.inclusion hu0).iso (Grp.isZero_trivial _)⟩⟩

private theorem splitTorus_baseChange (K : Type u) [Field K] [Algebra k K]
    {T : GroupScheme k} (hT : IsSplitTorus T) :
    IsSplitTorus ((groupBaseChange k K).obj T) := by
  obtain ⟨r, ⟨i⟩⟩ := splitPresentation hT
  let A := groupAlgebra k (Specs.CharacterDescent.StandardLattice.{u} r)
  let B := groupAlgebra K (Specs.CharacterDescent.StandardLattice.{u} r)
  let e : extendedHopf K A ≅ B :=
    CommHopfAlgCat.isoMk
      (LinearAlgebraicGroups.CharacterDescent.groupAlgebraBaseChange k K
        (Specs.CharacterDescent.StandardLattice.{u} r))
  obtain ⟨j⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := K) r
  exact ⟨r, ⟨((hopfSpec (CommRingCat.of K)).mapIso e.op ≪≫
    extendedGroupIso K A ≪≫ (groupBaseChange k K).mapIso i).symm ≪≫ j⟩⟩

private theorem schemeKernel_eq_iff {G H : GroupScheme k} {q : G ⟶ H}
    {N : ClosedSubgroup G} (h : IsSchemeKernel q N)
    {X : SchemeOver k} (x y : X ⟶ G.X) :
    x ≫ q.hom.hom = y ≫ q.hom.hom ↔
      ∃ z : X ⟶ N.group.X, z ≫ N.inclusion.hom.hom = x⁻¹ * y := by
  haveI : IsClosedImmersion ((𝟙 H : H ⟶ H).hom.hom.left) :=
    inferInstanceAs (IsClosedImmersion (𝟙 H.X.left))
  exact (sameImage_iff (p := q) (i := 𝟙 H) (Category.comp_id _) h x y)

private theorem normalizes_of_commuting_image {G H : GroupScheme k} {q : G ⟶ H}
    {Z T : ClosedSubgroup G} (hk : IsSchemeKernel q Z)
    (j : Z.group ⟶ T.group) (hj : j ≫ T.inclusion = Z.inclusion)
    {X : SchemeOver k} (g : X ⟶ G.X)
    (h : ∀ ⦃Y : SchemeOver k⦄ (y : Y ⟶ X) (t : Y ⟶ T.group.X),
      Commute ((y ≫ g) ≫ q.hom.hom) ((t ≫ T.inclusion.hom.hom) ≫ q.hom.hom)) :
    Normalizes T.inclusion g := by
  have liftConjugate {Y : SchemeOver k} (z : Y ⟶ G.X) (t : Y ⟶ T.group.X)
      (hc : Commute (z ≫ q.hom.hom) ((t ≫ T.inclusion.hom.hom) ≫ q.hom.hom)) :
      ∃ w : Y ⟶ T.group.X,
        w ≫ T.inclusion.hom.hom = z * (t ≫ T.inclusion.hom.hom) * z⁻¹ := by
    let a := t ≫ T.inclusion.hom.hom
    have hr : (z * a * z⁻¹) ≫ q.hom.hom = a ≫ q.hom.hom := by
      rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hc.eq, mul_inv_cancel_right]
    obtain ⟨n, hn⟩ := (schemeKernel_eq_iff hk a (z * a * z⁻¹)).mp hr.symm
    refine ⟨t * (n ≫ j.hom.hom), ?_⟩
    rw [MonObj.mul_comp, Category.assoc, ← forget_comp, hj, hn]
    change a * (a⁻¹ * (z * a * z⁻¹)) = z * a * z⁻¹
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  apply (normalizesIff k T.inclusion T.isClosedImmersion _ _).mpr
  refine ⟨(conjugateLe_iff _ _).mpr fun Y y t ↦ liftConjugate (y ≫ g) t (h y t),
    (conjugateLe_iff _ _).mpr fun Y y t ↦ ?_⟩
  refine liftConjugate (y ≫ g⁻¹) t ?_
  rw [GrpObj.comp_inv, GrpObj.inv_comp]
  exact (h y t).inv_left

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 150000 in
private theorem geometricallyMaximal_image
    (G Q : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (hs : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T)
    (T' : ClosedSubgroup Q.val) (hs' : IsSplitTorus T'.group)
    (q : G.val ⟶ Q.val) (qT : T.group ⟶ T'.group) (hqT : IsTorusRestriction q qT)
    (Z : ClosedSubgroup G.val) (hq : Unipotent.IsFppfGroupQuotient Z q)
    (hZT : IsSubgroupOf Z T) :
    IsGeometricallyMaximal T' := by
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  obtain ⟨N, j, hjc, W, qW, hN, hj, hW, _, _, hD, _⟩ :=
    Reductive.WeylScheme.weylScheme G hG T (isTorus_of_split hs) hm
  obtain ⟨hNK, hN'⟩ := normalizerSchemeBaseChange k K T.inclusion N T.isClosedImmersion hN
  let hclosed {P R : GroupScheme k} (p : P ⟶ R) (c : IsClosedImmersion p.hom.hom.left) :
      IsClosedImmersion (F.map p).hom.hom.left :=
    MorphismProperty.of_isPullback (baseChangeMapPullback (K := K) p.hom.hom).flip c
  let TK := baseChangedSubgroup K T (hclosed T.inclusion T.isClosedImmersion)
  let T'K := baseChangedSubgroup K T' (hclosed T'.inclusion T'.isClosedImmersion)
  let ZK := baseChangedSubgroup K Z (hclosed Z.inclusion Z.isClosedImmersion)
  let NK := scalarExtendedSubgroup K N hNK
  let WK := F.obj W.val
  let qK := F.map q
  let qTK := F.map qT
  let qWK := F.map qW
  let jK := F.map j
  let J : ClosedSubgroup NK.group := ⟨TK.group, jK, hclosed j hjc⟩
  have hWker : IsSchemeKernel qWK J := baseChangeKernelSquare qW j hW.1
  have hker : IsSchemeKernel qK ZK := baseChangeKernelSquare q Z.inclusion hq.1
  obtain ⟨z, hz⟩ := hZT
  let zK := F.map z
  have hzK : zK ≫ TK.inclusion = ZK.inclusion := (F.map_comp _ _).symm.trans (F.congr_map hz)
  have hjK : jK ≫ NK.inclusion = TK.inclusion := (F.map_comp _ _).symm.trans (F.congr_map hj)
  have hqTK : qTK ≫ T'K.inclusion = TK.inclusion ≫ qK := by
    change F.map qT ≫ F.map T'.inclusion = F.map T.inclusion ≫ F.map q
    simpa only [Functor.map_comp] using F.congr_map hqT.1
  obtain ⟨D⟩ := hD K (splitTorus_baseChange K hs)
  haveI : IsAffine (F.obj G.val).X.left := (Unipotent.baseChangedAlgebraicGroup K G).property.1
  haveI : IsAffine (F.obj Q.val).X.left := (Unipotent.baseChangedAlgebraicGroup K Q).property.1
  have hqKflat : Flat qK.hom.hom.left :=
    MorphismProperty.of_isPullback (baseChangeMapPullback (K := K) q.hom.hom).flip hq.2.1
  have hqKsurj : Surjective qK.hom.hom.left :=
    MorphismProperty.of_isPullback (baseChangeMapPullback (K := K) q.hom.hom).flip hq.2.2.1
  refine ⟨hclosed T'.inclusion T'.isClosedImmersion, isTorus_of_split (splitTorus_baseChange K hs'), ?_⟩
  intro S hS hsub
  change IsSubgroupOf T'K S at hsub
  change IsSubgroupOf S T'K
  obtain ⟨t, ht⟩ := hsub
  let S₀ := Unipotent.closedSubgroupAlgebraicGroup
    (G := Unipotent.baseChangedAlgebraicGroup K Q) S
  haveI : IsAffine S.group.X.left := S₀.property.1
  haveI : IsCommMonObj S.group.X := torus_commutative S₀ hS
  haveI : ConnectedSpace S.group.X.left := (torus_smooth_connected_solvable S₀ hS).2.1
  let P := pullback qK S.inclusion
  let v : P ⟶ F.obj G.val := pullback.fst _ _
  let p : P ⟶ S.group := pullback.snd _ _
  have square := (Grp.forget (SchemeOver K)).map_isPullback
    (IsPullback.of_hasPullback qK S.inclusion)
  change IsPullback v.hom.hom p.hom.hom qK.hom.hom S.inclusion.hom.hom at square
  have square' : IsPullback v.hom.hom.left p.hom.hom.left qK.hom.hom.left S.inclusion.hom.hom.left :=
    square.map (Over.forget (Spec (CommRingCat.of K)))
  have hv : IsClosedImmersion v.hom.hom.left :=
    MorphismProperty.of_isPullback square'.flip S.isClosedImmersion
  haveI := hv
  haveI : IsAffine P.X.left := isAffine_of_isAffineHom v.hom.hom.left
  haveI : Flat p.hom.hom.left := MorphismProperty.of_isPullback square' hqKflat
  haveI : Surjective p.hom.hom.left := MorphismProperty.of_isPullback square' hqKsurj
  have H : Normalizes TK.inclusion v.hom.hom := by
    apply normalizes_of_commuting_image (T := TK) hker zK hzK
    intro Y y a
    have ha : TK.inclusion.hom.hom ≫ qK.hom.hom =
        qTK.hom.hom ≫ t.hom.hom ≫ S.inclusion.hom.hom := by
      rw [← forget_comp, ← hqTK, forget_comp, ← ht, forget_comp]
    rw [Category.assoc, square.w, Category.assoc, ha]
    simp only [← Category.assoc]
    exact (show Commute (y ≫ p.hom.hom) (a ≫ qTK.hom.hom ≫ t.hom.hom) from
      mul_comm _ _).map (IsMonHom.monoidHom S.inclusion.hom.hom Y)
  obtain ⟨a, ha⟩ := (hN' _ _).mp H
  haveI : Mono NK.inclusion.hom.hom := mono_over _ hNK
  have hb (Y : SchemeOver K) (x y : Y ⟶ P.X)
      (e : x ≫ p.hom.hom = y ≫ p.hom.hom) :
      x ≫ a ≫ qWK.hom.hom = y ≫ a ≫ qWK.hom.hom := by
    have h' : (x ≫ v.hom.hom) ≫ qK.hom.hom = (y ≫ v.hom.hom) ≫ qK.hom.hom := by
      rw [Category.assoc, Category.assoc, square.w, ← Category.assoc, e, Category.assoc]
    obtain ⟨n, hn⟩ := (schemeKernel_eq_iff hker _ _).mp h'
    have hNker : (x ≫ a) ≫ qWK.hom.hom = (y ≫ a) ≫ qWK.hom.hom := by
      apply (schemeKernel_eq_iff hWker _ _).mpr
      refine ⟨n ≫ zK.hom.hom, (cancel_mono NK.inclusion.hom.hom).mp ?_⟩
      rw [Category.assoc, Category.assoc, ← forget_comp, hjK, ← forget_comp, hzK,
        MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, ha, Category.assoc, ha]
      exact hn
    simpa only [Category.assoc] using hNker
  obtain ⟨d, hd⟩ := descendAffine p.hom.hom (a ≫ qWK.hom.hom)
    (by
      intro Y x y e
      simpa only [Category.assoc] using hb Y x y e)
  have hηa : η[P.X] ≫ a = η[NK.group.X] := by
    apply (cancel_mono NK.inclusion.hom.hom).mp
    rw [Category.assoc, ha, IsMonHom.one_hom, IsMonHom.one_hom]
  have hd1 : η[S.group.X] ≫ d = 1 := by
    rw [← IsMonHom.one_hom p.hom.hom, Category.assoc, hd, ← Category.assoc, hηa,
      IsMonHom.one_hom]
    exact (MonObj.one_eq_one (M := WK.X)).symm
  let y := (η[S.group.X]).left (IsLocalRing.closedPoint K)
  let w := D.constantGroup.families S.group.X d y
  have hd' : d = toUnit S.group.X ≫ D.constantGroup.sectionPoint w :=
    constantFamily D.constantGroup d y
  have hw : w = 1 := by
    have h := D.constantGroup.naturality (η[S.group.X]) d
    rw [hd1, map_one] at h
    have e := congrArg (fun m : LocallyConstant (𝟙_ (SchemeOver K)).left D.labels ↦
      m (IsLocalRing.closedPoint K)) h
    exact e.symm
  rw [hd', hw, map_one] at hd
  have hzero : a ≫ qWK.hom.hom = 1 := by simpa only [Category.assoc, MonObj.comp_one] using hd.symm
  obtain ⟨b, hb'⟩ := (schemeKernel_sections hWker a).mpr hzero
  change b ≫ J.inclusion.hom.hom = a at hb'
  have hv' : b ≫ TK.inclusion.hom.hom = v.hom.hom := by
    rw [← hjK, forget_comp, ← Category.assoc]
    change (b ≫ J.inclusion.hom.hom) ≫ NK.inclusion.hom.hom = _
    rw [hb', ha]
  haveI : Mono T'K.inclusion.hom.hom := mono_over _ T'K.isClosedImmersion
  obtain ⟨c, hc⟩ := descendClosedFactor p.hom.hom T'K.inclusion.hom.hom S.inclusion.hom.hom
    (b ≫ qTK.hom.hom) (by
      rw [Category.assoc, ← forget_comp, hqTK, forget_comp, ← Category.assoc, hv', square.w])
  letI := T'K.isClosedImmersion
  letI := isMonHom_of_comp_closed c S.inclusion T'K.inclusion hc
  exact ⟨Grp.homMk c, Grp.hom_ext _ _ hc⟩

set_option backward.isDefEq.respectTransparency false in
/-- A central isogeny identifies the roots and their root subgroups and
carries each attached coroot to the corresponding attached coroot. -/
theorem centralIsogenyComparison : CentralIsogenyComparison.{u} := by
  intro k _ G H hG hH T S hsT hmT hsS hmS f fT hf hcomm honto
  have hfT : IsTorusRestriction f fT :=
    ⟨hcomm, flat_of_surjective_torus_map fT hsS honto, honto⟩
  have dimensions : RootDimension.{u} := RootData.RootGroups.rootDimension
  have roots : RootSubgroups.{u} := RootData.RootGroups.rootSubgroups
  have centre : CentreFormula.{u} := RootData.SchemeCentre.schemeCentre
  obtain ⟨hinj, hind⟩ := finiteIndexCharacterPullback centre G H hG hH T S hsT hmT hsS hmS f fT hf hfT
  obtain ⟨hfinT, hfinS, hcard⟩ := absoluteRootCardinality_eq dimensions G H hG hH T S
    hsT hmT hsS hmS f fT hf hfT
  obtain ⟨_, eT, heT, _, _⟩ := centre G hG T hsT hmT
  obtain ⟨_, eS, heS, _, _⟩ := centre H hH S hsS hmS
  have hsurj : absoluteRoots T ⊆ characterPullback fT '' absoluteRoots S := by
    intro α hα
    obtain ⟨hα', v, hv, hn⟩ := hα
    have hw := differential_weight_nonzero roots centre G H hG T hsT hmT f hf hα' hv hn
    obtain ⟨β, hβ, h⟩ := transportedWeight G H T S f fT hfT eT eS heT heS α hv hw
    refine ⟨β, ⟨?_, _, h, hw⟩, hβ⟩
    rintro rfl
    exact hα' (hβ.symm.trans (map_one _))
  have himage : absoluteRoots T = characterPullback fT '' absoluteRoots S := by
    refine Set.eq_of_subset_of_ncard_le hsurj ?_ (hfinS.image _)
    rw [Set.ncard_image_of_injective _ hinj, hcard]
  refine ⟨hinj, hind,
    ⟨fun β hβ ↦ himage.symm ▸ Set.mem_image_of_mem _ hβ, hinj.injOn, hsurj⟩, ?_⟩
  intro β hβ hα
  exact ⟨rootGroup_pushforward roots centre G H hG hH T S hsT hmT hsS hmS
      f fT hf hfT β hβ hα,
    fun c₁ c₂ hc₁ hc₂ ↦ attachedCoroot_pushforward G H hH T S hsS hmS f fT hfT
      β hβ hα c₁ c₂ hc₁ hc₂⟩

/-- Pullback from the image maximal torus in any presentation of the adjoint
quotient identifies its character lattice with the root lattice. -/
theorem adjointCharacterLattice_of_quotient
    (G : AffineAlgebraicGroup k) (hG : IsSemisimple G)
    (T : ClosedSubgroup G.val) (hs : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T)
    (Z : ClosedSubgroup G.val) (hZ : RepresentsSubgroup Z (fun _ z ↦ Centralizes (𝟙 G.val) z))
    (Q : AffineAlgebraicGroup k) (q : G.val ⟶ Q.val) (hq : RepresentsQuotient Z q) :
    ∃ (T' : ClosedSubgroup Q.val) (qT : T.group ⟶ T'.group),
      IsSplitTorus T'.group ∧ IsGeometricallyMaximal T' ∧ IsTorusRestriction q qT ∧
      Function.Injective (characterPullback qT) ∧ (characterPullback qT).range = rootLattice T := by
  have centre : CentreFormula.{u} := RootData.SchemeCentre.schemeCentre
  have hGr := reductive_of_semisimple G hG
  obtain ⟨T', qT, hs', hqT, hχ, hL, _⟩ := adjointTorusImage centre G hGr T hs hm Z hZ Q q hq
  have hZc : Centralizes (𝟙 G.val) Z.inclusion.hom.hom :=
    (hZ _ _).mpr ⟨𝟙 _, Category.id_comp _⟩
  have hZT := kernel_le_maximalTorus centre G hGr T hs hm Z hZc
  have hm' := geometricallyMaximal_image G Q hGr T hs hm T' hs' q qT hqT Z
    (representsQuotient_isFppfGroupQuotient hq) hZT
  exact ⟨T', qT, hs', hm', hqT, hχ, hL⟩

/-- The adjoint quotient of a split semisimple group has root lattice as
the character lattice of its image maximal torus. -/
theorem adjointCharacterLattice : AdjointCharacterLattice.{u} := by
  intro k _ G hG T hs hm
  obtain ⟨_, e, _, hc, hZ, _⟩ := RootData.SchemeCentre.schemeCentre G
    (reductive_of_semisimple G hG) T hs hm
  let Z : ClosedSubgroup G.val :=
    ⟨diagonal (Character T.group ⧸ rootLattice T),
      diagonalClosedInclusion k (rootLattice T) ≫ e.hom ≫ T.inclusion, hc⟩
  change RepresentsSubgroup Z (fun _ z ↦ Centralizes (𝟙 G.val) z) at hZ
  have hz : Centralizes (𝟙 G.val) Z.inclusion.hom.hom :=
    (hZ _ _).mpr ⟨𝟙 _, Category.id_comp _⟩
  have hnormal : IsNormalSubgroup Z.inclusion := by
    refine ⟨snd G.val.X Z.group.X, ?_⟩
    have hcomm := (centralizes_iff _ _).mp hz
      (G.val.X ⊗ Z.group.X) (snd G.val.X Z.group.X) (fst G.val.X Z.group.X)
    change Commute (snd G.val.X Z.group.X ≫ Z.inclusion.hom.hom)
      (fst G.val.X Z.group.X ≫ 𝟙 G.val.X) at hcomm
    rw [Category.comp_id] at hcomm
    unfold subgroupConjugation
    rw [hcomm.symm.eq, mul_inv_cancel_right]
  obtain ⟨_, _, Q, q, _, _, _, _, _, hq⟩ := normalAffineQuotient G Z hnormal
  exact ⟨Z, Q, q, hZ, hq, adjointCharacterLattice_of_quotient G hG T hs hm Z hZ Q q hq⟩

end

end LinearAlgebraicGroups.Classification.CentralIsogenies
