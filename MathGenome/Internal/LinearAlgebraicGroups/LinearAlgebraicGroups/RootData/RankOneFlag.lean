import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.RankOneFlag
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterDynamics
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.WeylScheme
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SmoothOrbit
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.CodimensionTwoExtension
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.EtaleNormality
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct Matrix

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace LinearAlgebraicGroups.RankOneFlag

open _root_.LinearAlgebraicGroups.Specs

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (pairing)
open Specs.GeometricRadicals (IsSplitTorus)

/-- A nontrivial character of a split torus pairs positively with an integral cocharacter. -/
theorem exists_positive_cocharacter {k : Type u} [Field k] {T : GroupScheme k}
    (hT : IsSplitTorus T) {χ : Character T} (hχ : χ ≠ 1) :
    ∃ cochar : Cocharacter T, 0 < pairing T χ cochar := by
  obtain ⟨hc, _, _, _, _, P, hp, hP⟩ :=
    RootData.CharacterPairing.perfectCharacterPairing T hT
  letI := hc
  letI := hp
  have hne : P (Additive.ofMul χ) ≠ 0 := by
    intro h
    apply hχ
    exact (LinearMap.IsPerfPair.bijective_left P).injective (h.trans (map_zero P).symm)
  obtain ⟨y, hy⟩ : ∃ y, P (Additive.ofMul χ) y ≠ 0 := by
    by_contra! h
    exact hne (LinearMap.ext fun y => h y)
  by_cases hpos : 0 < P (Additive.ofMul χ) y
  · exact ⟨y.toMul, (hP χ y.toMul) ▸ hpos⟩
  · have hneg : 0 < P (Additive.ofMul χ) (-y) := by
      rw [map_neg]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hpos) hy)
    exact ⟨(-y).toMul, (hP χ (-y).toMul) ▸ hneg⟩

section Lattice

open Function Module Submodule

variable {M : Type u} [CommGroup M]

private abbrev CyclicQuotient (x : M) := Additive (M ⧸ Subgroup.zpowers x)
private abbrev SaturatedQuotient (x : M) :=
  Multiplicative (CyclicQuotient x ⧸ torsion ℤ (CyclicQuotient x))

private def saturatedProjection (x : M) : M →* SaturatedQuotient x :=
  ((torsion ℤ (CyclicQuotient x)).mkQ.toAddMonoidHom.toMultiplicativeRight).comp
    (QuotientGroup.mk' (Subgroup.zpowers x))

private theorem saturatedProjection_surjective (x : M) :
    Surjective (saturatedProjection x) :=
  (Submodule.mkQ_surjective _).comp QuotientGroup.mk_surjective

private theorem saturatedProjection_apply_self (x : M) : saturatedProjection x x = 1 := by
  have h : QuotientGroup.mk' (Subgroup.zpowers x) x = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers x)
  rw [saturatedProjection, MonoidHom.comp_apply, h, map_one]

private theorem saturatedProjection_ker_le (x : M) {N : Type u} [CommGroup N]
    [IsTorsionFree ℤ (Additive N)] (f : M →* N) (hf : f x = 1) :
    (saturatedProjection x).ker ≤ f.ker := by
  have hle : Subgroup.zpowers x ≤ f.ker :=
    Subgroup.zpowers_le.mpr hf
  let F : CyclicQuotient x →ₗ[ℤ] Additive N :=
    AddMonoidHom.toIntLinearMap (QuotientGroup.lift _ f hle).toAdditive
  intro y hy
  have hy' : (Additive.ofMul (QuotientGroup.mk' (Subgroup.zpowers x) y) : CyclicQuotient x)
      ∈ torsion ℤ (CyclicQuotient x) :=
    (Submodule.Quotient.mk_eq_zero _).mp hy
  obtain ⟨a, ha⟩ := (mem_torsion_iff _).mp hy'
  change (a : ℤ) • (Additive.ofMul (QuotientGroup.mk' (Subgroup.zpowers x) y) : CyclicQuotient x) = 0 at ha
  have h : (a : ℤ) • F (Additive.ofMul (QuotientGroup.mk' (Subgroup.zpowers x) y)) = 0 := by
    rw [← map_smul, ha, map_zero]
  have ha0 : (a : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp a.2
  exact ((isTorsionFree_iff_smul_eq_zero.mp inferInstance) _ _ h).resolve_left ha0

/-- A finite-order automorphism of a torsion-free abelian group which fixes
both a subgroup pointwise and its quotient is the identity. -/
theorem automorphism_eq_one_of_pow_eq_one_of_subgroup {M : Type u} [CommGroup M]
    [HasUniqueRoots M] (N : Subgroup M) (f : M ≃* M) (n : ℕ) (hn : n ≠ 0)
    (hpow : f ^ n = 1) (hN : ∀ x ∈ N, f x = x) (hquot : ∀ x, f x / x ∈ N) :
    f = 1 := by
  ext x
  let d := f x / x
  have hd : f d = d := hN d (hquot x)
  have hfx : f x = x * d := by simp [d]
  have hiter (m : ℕ) : (f ^ m) x = x * d ^ m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hd, hfx, pow_succ', mul_assoc]
  have hdn : d ^ n = 1 := by
    have h := hiter n
    rw [hpow, MulAut.one_apply] at h
    exact mul_left_cancel (h.symm.trans (mul_one x).symm)
  have hone : d = 1 := pow_left_injective hn (by simpa using hdn)
  simpa [hone] using hfx

private theorem saturatedProjection_power_relation (x y : M) (hy : saturatedProjection x y = 1) :
    ∃ n m : ℤ, n ≠ 0 ∧ y ^ n = x ^ m := by
  have hy' : (Additive.ofMul (QuotientGroup.mk' (Subgroup.zpowers x) y) : CyclicQuotient x) ∈
      torsion ℤ (CyclicQuotient x) := (Submodule.Quotient.mk_eq_zero _).mp hy
  obtain ⟨a, ha⟩ := (mem_torsion_iff _).mp hy'
  have hpow : (QuotientGroup.mk' (Subgroup.zpowers x)) (y ^ (a : ℤ)) = 1 := by
    rw [map_zpow]
    exact ha
  obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp ((QuotientGroup.eq_one_iff _).mp hpow)
  exact ⟨a, b, mem_nonZeroDivisors_iff_ne_zero.mp a.property, hb.symm⟩

private theorem saturatedProjection_prod_injective [IsMulTorsionFree M]
    (x : M) {N : Type u} [CommGroup N] [IsMulTorsionFree N] (f : M →* N) (hf : f x ≠ 1) :
    Function.Injective ((saturatedProjection x).prod f) := by
  let q := (saturatedProjection x).prod f
  intro y z h
  apply div_eq_one.mp
  let a := y / z
  have hy : q a = 1 := by
    change q (y / z) = 1
    rw [map_div, show q y = q z from h, div_self']
  change (saturatedProjection x a, f a) = (1, 1) at hy
  obtain ⟨n, m, hn, hnm⟩ := saturatedProjection_power_relation x a (congrArg Prod.fst hy)
  have hfn := congrArg f hnm
  have hf1 : f a = 1 := congrArg Prod.snd hy
  rw [map_zpow, map_zpow, hf1, one_zpow] at hfn
  have hm := (IsMulTorsionFree.zpow_eq_one_iff_right hf).mp hfn.symm
  rw [hm, zpow_zero] at hnm
  exact (IsMulTorsionFree.zpow_eq_one_iff_left hn).mp hnm

private theorem saturatedProjection_ker_cyclic [IsMulTorsionFree M] (x : M)
    {N : Type u} [CommGroup N] [IsCyclic N] [IsMulTorsionFree N] (f : M →* N) (hf : f x ≠ 1) :
    IsCyclic (saturatedProjection x).ker := by
  apply isCyclic_of_injective (f.comp (saturatedProjection x).ker.subtype)
  intro a b h
  apply Subtype.ext
  apply saturatedProjection_prod_injective x f hf
  change (saturatedProjection x a.val, f a.val) = (saturatedProjection x b.val, f b.val)
  rw [show saturatedProjection x a.val = 1 from a.property,
    show saturatedProjection x b.val = 1 from b.property]
  exact congrArg (Prod.mk 1) h

/-- The restriction to an infinite cyclic kernel bounds a finite group of lattice
automorphisms acting trivially on the quotient. -/
theorem card_le_two_of_fixes_quotient {M N : Type u} [CommGroup M] [CommGroup N]
    [HasUniqueRoots M] (p : M →* N) [IsCyclic p.ker] (W : Subgroup (MulAut M))
    [Finite W] (h : ∀ (w : W) x, p (w.val x) = p x) : Nat.card W ≤ 2 := by
  classical
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := p.ker)
  let r (w : W) : MulAut p.ker := {
    toFun x := ⟨w.val x, (h w x).trans x.property⟩
    invFun x := ⟨w⁻¹.val x, (h w⁻¹ x).trans x.property⟩
    left_inv x := Subtype.ext (w.val.symm_apply_apply x.val)
    right_inv x := Subtype.ext (w.val.apply_symm_apply x.val)
    map_mul' x y := Subtype.ext (map_mul w.val x.val y.val) }
  have hr (w : W) : r w a = a ∨ r w a = a⁻¹ := by
    by_cases ha₁ : a = 1
    · exact Or.inl (by rw [ha₁, map_one])
    have ha' : Subgroup.zpowers a = ⊤ := by
      exact top_unique fun x _ => Subgroup.mem_zpowers_iff.mpr (ha x)
    have he : Subgroup.zpowers (r w a) = Subgroup.zpowers a := by
      change Subgroup.zpowers ((r w).toMonoidHom a) = _
      rw [← MonoidHom.map_zpowers (r w).toMonoidHom a, ha',
        Subgroup.map_top_of_surjective _ (r w).surjective]
    obtain hw | hw := (Subgroup.zpowers_eq_zpowers_iff
      (not_isOfFinOrder_of_isMulTorsionFree ha₁)).mp he.symm
    · exact Or.inl hw.symm
    · exact Or.inr hw.symm
  have hinj (v w : W) (e : r v a = r w a) : v = w := by
    let z : W := w⁻¹ * v
    have hfixed (x : M) (hx : x ∈ p.ker) : z.val x = x := by
      obtain ⟨b, hb⟩ := ha ⟨x, hx⟩
      have he' : r v (⟨x, hx⟩ : p.ker) = r w (⟨x, hx⟩ : p.ker) := by
        rw [← hb, map_zpow, map_zpow, e]
      have hvw : v.val x = w.val x := congrArg Subtype.val he'
      change w.val.symm (v.val x) = x
      rw [hvw, MulEquiv.symm_apply_apply]
    have hquot (x : M) : z.val x / x ∈ p.ker := by
      change p (z.val x / x) = 1
      rw [map_div, h z, div_self']
    have hzneq : orderOf z ≠ 0 := (orderOf_pos z).ne'
    have hpow : z.val ^ orderOf z = 1 := by
      exact_mod_cast congrArg Subtype.val (pow_orderOf_eq_one z)
    have hz := automorphism_eq_one_of_pow_eq_one_of_subgroup p.ker z.val
      (orderOf z) hzneq hpow hfixed hquot
    exact (inv_mul_eq_one.mp (show w⁻¹ * v = 1 from Subtype.ext hz)).symm
  let sign (w : W) : Bool := decide (r w a = a)
  have hs : Function.Injective sign := by
    intro v w hsign
    apply hinj
    by_cases hv : r v a = a
    · have hw : r w a = a := of_decide_eq_true (hsign.symm.trans (decide_eq_true hv))
      exact hv.trans hw.symm
    · have hw : r w a ≠ a := fun hw => Bool.false_ne_true ((decide_eq_false hv).symm.trans (hsign.trans (decide_eq_true hw)))
      exact ((hr v).resolve_left hv).trans ((hr w).resolve_left hw).symm
  simpa using Nat.card_le_card_of_injective sign hs

end Lattice

section Centralizer

open Specs.CharacterDescent (StandardLattice)
open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap diagonalClosedInclusion)
open Specs.GeometricRadicals (IsTorus IsMaximalTorus baseChangedSubgroup)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)

open private integerHomEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private splitGroupHomEquiv groupLikeIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private splitPresentation latticeCoordinates from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private specGroupMap_comp extendedGroupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private factor_group_through_subgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private baseChangeMapIsPullback from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient
open private factor_closed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private torus_of_iso inclusion_mono from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate

variable {k : Type u} [Field k]

private def latticeCharacter (M : Type u) [CommGroup M] :
    M ≃* Character (specGroup (groupAlgebra k M)) :=
  (integerHomEquiv M).trans (splitGroupHomEquiv _ _)

private theorem latticeCharacter_comp {M N : Type u} [CommGroup M] [CommGroup N]
    (f : M →* N) (x : M) :
    specGroupMap (groupAlgebraMap k f) ≫ latticeCharacter (k := k) M x =
      latticeCharacter (k := k) N (f x) := by
  have hf : f.comp (integerHomEquiv M x) = integerHomEquiv N (f x) := by
    ext z
    exact map_zpow f x z.down.toAdd
  change specGroupMap (groupAlgebraMap k f) ≫
      specGroupMap (groupAlgebraMap k (integerHomEquiv M x)) = _
  rw [← specGroupMap_comp]
  congr 1
  apply CommHopfAlgCat.hom_ext
  change (MonoidAlgebra.mapDomainBialgHom k f).comp
    (MonoidAlgebra.mapDomainBialgHom k (integerHomEquiv M x)) =
      MonoidAlgebra.mapDomainBialgHom k (integerHomEquiv N (f x))
  rw [← hf]
  exact (MonoidAlgebra.mapDomainBialgHom_comp (R := k) f (integerHomEquiv M x)).symm

private theorem latticeMap_comp {M N P : Type u} [CommGroup M] [CommGroup N] [CommGroup P]
    (f : M →* N) (g : N →* P) :
    specGroupMap (groupAlgebraMap k g) ≫ specGroupMap (groupAlgebraMap k f) =
      specGroupMap (groupAlgebraMap k (g.comp f)) := by
  rw [← specGroupMap_comp]
  congr 1
  exact CommHopfAlgCat.hom_ext (MonoidAlgebra.mapDomainBialgHom_comp (R := k) g f).symm

private theorem lattice_torus_of_split {T : GroupScheme k} (h : IsSplitTorus T) : IsTorus T := by
  obtain ⟨r, ⟨e⟩⟩ := splitPresentation h
  let A := groupAlgebra k (StandardLattice.{u} r)
  let hA : extendedHopf k A ≅ A := CommHopfAlgCat.isoMk
    (LinearAlgebraicGroups.CharacterDescent.groupAlgebraBaseChange k k _)
  obtain ⟨m⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) r
  refine ⟨k, inferInstance, inferInstance, inferInstance, r, ⟨?_⟩⟩
  exact (groupBaseChange k k).mapIso e.symm ≪≫ (extendedGroupIso k A).symm ≪≫
    (hopfSpec (CommRingCat.of k)).mapIso hA.symm.op ≪≫ m

private theorem torsionFree_of_diagonal_torus (M : Type u) [CommGroup M]
    (h : IsTorus (specGroup (groupAlgebra k M))) : Module.IsTorsionFree ℤ (Additive M) := by
  let A := groupAlgebra k M
  obtain ⟨E, _, _, _, r, ⟨e⟩⟩ :=
    (LinearAlgebraicGroups.GeometricRadicals.torusCoordinateComparison A).mp h
  let eA : extendedHopf E A ≅ groupAlgebra E M := CommHopfAlgCat.isoMk
    (LinearAlgebraicGroups.CharacterDescent.groupAlgebraBaseChange k E M)
  let f : M ≃* StandardLattice.{u} r :=
    ((LinearAlgebraicGroups.CharacterDescent.monomialCharacterEquiv E).trans
      ((groupLikeIso (e ≪≫ eA)).trans
        (LinearAlgebraicGroups.CharacterDescent.monomialCharacterEquiv E).symm)).symm
  letI : Module.Free ℤ (Additive M) := Module.Free.of_equiv
    ((latticeCoordinates r).symm.trans f.toAdditive.symm.toIntLinearEquiv)
  infer_instance

private theorem saturatedQuotient_split (M : Type u) [CommGroup M] [Group.FG M] (x : M) :
    IsSplitTorus (specGroup (groupAlgebra k (M ⧸ (saturatedProjection x).ker))) := by
  let Q := CyclicQuotient x
  let S := Q ⧸ Submodule.torsion ℤ Q
  letI : Module.Finite ℤ Q := Module.Finite.iff_addGroup_fg.mpr
    (inferInstanceAs (AddGroup.FG Q))
  let r := Module.finrank ℤ S
  let b : Module.Basis (Fin r) ℤ S := Module.finBasis ℤ S
  let d : S ≃ₗ[ℤ] Additive (StandardLattice.{u} r) :=
    b.equivFun.trans (latticeCoordinates r).symm
  let j : M ⧸ (saturatedProjection x).ker ≃* StandardLattice.{u} r :=
    (QuotientGroup.quotientKerEquivOfSurjective _ (saturatedProjection_surjective x)).trans
      d.toAddEquiv.toMultiplicative
  obtain ⟨e⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) r
  exact ⟨r, ⟨(hopfSpec (CommRingCat.of k)).mapIso
    (CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv k k j.symm)).op ≪≫ e⟩⟩

private theorem kernel_subtorus_in_splitPresentation {T : GroupScheme k}
    {M : Type u} [CommGroup M] [Group.FG M]
    (i : specGroup (groupAlgebra k M) ≅ T) (χ : Character T) (x : M)
    (hx : latticeCharacter (k := k) M x = i.hom ≫ χ) :
    ∃ S : ClosedSubgroup T, Specs.RankOneFlag.IsKernelSubtorus χ S ∧
      ∃ e : specGroup (groupAlgebra k (M ⧸ (saturatedProjection x).ker)) ≅ S.group,
        e.hom ≫ S.inclusion = diagonalClosedInclusion k (saturatedProjection x).ker ≫ i.hom := by
  let N := (saturatedProjection x).ker
  let f := QuotientGroup.mk' N
  let j := diagonalClosedInclusion k N
  obtain ⟨hclosed, _⟩ := DiagonalizableGroups.diagonalRestrictionKernelAndQuotient k M N
  letI := hclosed
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  haveI : IsIso i.hom.hom.hom.left := F.map_isIso i.hom
  let S : ClosedSubgroup T :=
    ⟨_, j ≫ i.hom, IsClosedImmersion.comp _ _⟩
  have hxN : f x = 1 := (QuotientGroup.eq_one_iff (N := N) x).mpr (saturatedProjection_apply_self x)
  refine ⟨S, ⟨lattice_torus_of_split (saturatedQuotient_split M x), ?_, ?_⟩,
    Iso.refl _, Category.id_comp _⟩
  · change (j ≫ i.hom) ≫ χ = 1
    rw [Category.assoc, ← hx]
    change specGroupMap (groupAlgebraMap k f) ≫ latticeCharacter (k := k) M x = 1
    rw [latticeCharacter_comp, hxN, map_one]
  · intro D hD hDχ
    haveI := D.isClosedImmersion
    haveI : IsIso i.inv.hom.hom.left := F.map_isIso i.inv
    have hDi : IsClosedImmersion (D.inclusion ≫ i.inv).hom.hom.left :=
      IsClosedImmersion.comp D.inclusion.hom.hom.left i.inv.hom.hom.left
    obtain ⟨L, ⟨d, hd⟩, _⟩ :=
      (DiagonalizableGroups.diagonalClosedSubgroups k M D.group (D.inclusion ≫ i.inv)).mp hDi
    let p := QuotientGroup.mk' L
    letI := torsionFree_of_diagonal_torus (M ⧸ L) (torus_of_iso d hD)
    have hpχ : latticeCharacter (k := k) (M ⧸ L) (p x) = 1 := by
      have hd' : diagonalClosedInclusion k L = d.inv ≫ D.inclusion ≫ i.inv := by
        rw [← hd, Iso.inv_hom_id_assoc]
      rw [← latticeCharacter_comp, hx]
      change diagonalClosedInclusion k L ≫ i.hom ≫ χ = 1
      rw [hd', Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, hDχ]
      apply Grp.hom_ext
      exact MonObj.comp_one d.inv.hom.hom
    have hpx : p x = 1 :=
      (latticeCharacter (k := k) (M ⧸ L)).injective (hpχ.trans (map_one _).symm)
    let g := QuotientGroup.lift N p (saturatedProjection_ker_le x p hpx)
    refine ⟨d.hom ≫ specGroupMap (groupAlgebraMap k g), ?_⟩
    change (d.hom ≫ specGroupMap (groupAlgebraMap k g)) ≫ (j ≫ i.hom) = D.inclusion
    have hgj : specGroupMap (groupAlgebraMap k g) ≫ j = diagonalClosedInclusion k L := by
      change specGroupMap (groupAlgebraMap k g) ≫ specGroupMap (groupAlgebraMap k f) = _
      rw [latticeMap_comp, show g.comp f = p from MonoidHom.ext (fun _ => rfl)]
      rfl
    rw [Category.assoc, ← Category.assoc (specGroupMap (groupAlgebraMap k g)), hgj,
      ← Category.assoc, hd, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem largest_kernel_subtorus {T : GroupScheme k} (hT : IsSplitTorus T)
    (χ : Character T) : ∃ S : ClosedSubgroup T, Specs.RankOneFlag.IsKernelSubtorus χ S := by
  obtain ⟨r, ⟨i⟩⟩ := splitPresentation hT
  let M := StandardLattice.{u} r
  letI : Module.Finite ℤ (Additive M) := Module.Finite.equiv (latticeCoordinates r).symm
  letI : Group.FG M := GroupFG.iff_add_fg.mpr (Module.Finite.iff_addGroup_fg.mp inferInstance)
  obtain ⟨x, hx⟩ := (latticeCharacter (k := k) M).surjective (i.hom ≫ χ)
  obtain ⟨S, hS, _⟩ := kernel_subtorus_in_splitPresentation i χ x hx
  exact ⟨S, hS⟩

private theorem baseChange_closed {A G : GroupScheme k} (f : A ⟶ G)
    (hf : IsClosedImmersion f.hom.hom.left) :
    IsClosedImmersion ((groupBaseChange k (AlgebraicClosure k)).map f).hom.hom.left :=
  MorphismProperty.of_isPullback
    (baseChangeMapIsPullback (AlgebraicClosure k) f.hom.hom).flip hf

private theorem maximal_torus_in_intermediate_group {G : GroupScheme k}
    {T C : ClosedSubgroup G} {j : T.group ⟶ C.group} (hj : j ≫ C.inclusion = T.inclusion)
    (hT : Specs.RankOneFlag.IsGeometricallyMaximal T) :
    Specs.RankOneFlag.IsGeometricallyMaximal (⟨_, j, factor_closed hj⟩ : ClosedSubgroup C.group) := by
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  obtain ⟨ht, hmax⟩ := hT
  let T' := baseChangedSubgroup K T ht
  let C' := baseChangedSubgroup K C (baseChange_closed C.inclusion C.isClosedImmersion)
  let B : ClosedSubgroup C'.group := ⟨_, F.map j, baseChange_closed j (factor_closed hj)⟩
  have hj' : B.inclusion ≫ C'.inclusion = T'.inclusion := by
    change F.map j ≫ F.map C.inclusion = F.map T.inclusion
    rw [← Functor.map_comp, hj]
  refine ⟨B.isClosedImmersion, ?_⟩
  change IsMaximalTorus B
  refine ⟨hmax.1, ?_⟩
  intro D hD hBD
  obtain ⟨m, hm⟩ := hBD
  let D' := subgroupOfSubgroup C' D
  have hTD : IsSubgroupOf T' D' :=
    ⟨m, by change m ≫ D.inclusion ≫ C'.inclusion = T'.inclusion
           rw [← Category.assoc, hm, hj']⟩
  obtain ⟨g, hg⟩ := hmax.2 D' hD hTD
  haveI := inclusion_mono C'
  refine ⟨g, (cancel_mono C'.inclusion).mp ?_⟩
  rw [Category.assoc, hj']
  exact hg

theorem centralizerAndPositiveCocharacter :
    Specs.RankOneFlag.CentralizerAndPositiveCocharacter.{u} := by
  intro k _ G hG T hsplit hT α hα
  obtain ⟨S, hS⟩ := largest_kernel_subtorus hsplit α
  let S' := subgroupOfSubgroup T S
  obtain ⟨C, hC, hred⟩ :=
    Reductive.SubtorusCentralizer.centralizerReductive G hG T S'
      (lattice_torus_of_split hsplit) hS.1 ⟨S.inclusion, rfl⟩ hT
  obtain ⟨hc, _⟩ := RootData.CharacterPairing.perfectCharacterPairing T.group hsplit
  letI := hc
  have hcomm : Centralizes S'.inclusion T.inclusion.hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro X t s
    exact (show Commute t (s ≫ S.inclusion.hom.hom) from mul_comm _ _).map
      (IsMonHom.monoidHom T.inclusion.hom.hom X)
  obtain ⟨j, hj⟩ := (hC _ _).mp hcomm
  obtain ⟨f, hf⟩ := factor_group_through_subgroup C T.inclusion j hj
  let B : ClosedSubgroup C.group := ⟨_, f, factor_closed hf⟩
  exact ⟨⟨S, hS, C, hC, B, Iso.refl _, (Category.id_comp _).trans hf,
      maximal_torus_in_intermediate_group hf hT⟩,
    hred, exists_positive_cocharacter hsplit hα.1⟩

private theorem subgroupIso_of_same {G : GroupScheme k} {A B : ClosedSubgroup G}
    (h : Specs.RankOneFlag.SameSubgroup A B) :
    ∃ e : A.group ≅ B.group, e.hom ≫ B.inclusion = A.inclusion := by
  obtain ⟨⟨f, hf⟩, ⟨g, hg⟩⟩ := h
  letI := inclusion_mono A
  letI := inclusion_mono B
  exact ⟨⟨f, g, (cancel_mono A.inclusion).mp (by rw [Category.assoc, hg, hf, Category.id_comp]),
    (cancel_mono B.inclusion).mp (by rw [Category.assoc, hf, hg, Category.id_comp])⟩, hf⟩

open Specs.DiagonalizableGroups (IntegerCharacters integerGenerator)
open Specs.CharacterPairing (powerMorphism)
open CocharacterDynamics (oppositeCocharacter)
open private groupAlgebraMap_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private centralizes_comp_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterDynamics

local notation "Gm" => specGroup (groupAlgebra k IntegerCharacters)

private theorem integerCharacters_hasUniqueRoots : HasUniqueRoots IntegerCharacters.{u} :=
  ⟨fun n hn a b h => ULift.ext (pow_left_injective hn
    (show a.down ^ n = b.down ^ n from congrArg ULift.down h))⟩

/-- A positive pairing makes the kernel subtorus and cocharacter jointly generate the torus
in the sense of fppf descent for its commuting sections. -/
private theorem centralizes_kernelTorus_and_cocharacter {T H : GroupScheme k}
    (hT : IsSplitTorus T) {χ : Character T} {S : ClosedSubgroup T}
    (hS : Specs.RankOneFlag.IsKernelSubtorus χ S)
    (cochar : Cocharacter T) (hpos : 0 < pairing T χ cochar)
    (i : T ⟶ H) {Y : SchemeOver k} (g : Y ⟶ H.X) :
    Centralizes (S.inclusion ≫ i) g → Centralizes (cochar ≫ i) g → Centralizes i g := by
  intro hs hcochar
  obtain ⟨r, ⟨j⟩⟩ := splitPresentation hT
  let M := StandardLattice.{u} r
  letI : Module.Finite ℤ (Additive M) := Module.Finite.equiv (latticeCoordinates r).symm
  letI : Group.FG M := GroupFG.iff_add_fg.mpr (Module.Finite.iff_addGroup_fg.mp inferInstance)
  letI := integerCharacters_hasUniqueRoots
  letI : HasUniqueRoots M := inferInstanceAs (HasUniqueRoots (Fin r → IntegerCharacters.{u}))
  obtain ⟨x, hx⟩ := (latticeCharacter (k := k) M).surjective (j.hom ≫ χ)
  obtain ⟨f, hf⟩ := (splitGroupHomEquiv (k := k) M IntegerCharacters).surjective (cochar ≫ j.inv)
  change specGroupMap (groupAlgebraMap k f) = cochar ≫ j.inv at hf
  have hf' : specGroupMap (groupAlgebraMap k f) ≫ j.hom = cochar := by
    rw [hf, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hs0 : latticeCharacter (k := k) IntegerCharacters 1 =
      powerMorphism 0 := by
    rw [powerMorphism, zpow_zero]
    rfl
  have hfx : f x ≠ 1 := by
    intro h
    have he : cochar ≫ χ = powerMorphism 0 := by
      rw [← hf', Category.assoc, ← hx, latticeCharacter_comp, h]
      exact hs0
    exact hpos.ne' ((RootData.CharacterPairing.characterPairingComposition T χ cochar).1 0 |>.mp he)
  let N := (saturatedProjection x).ker
  let m := QuotientGroup.mk' N
  let Q := M ⧸ N
  obtain ⟨D, hD, e, he⟩ := kernel_subtorus_in_splitPresentation j χ x hx
  obtain ⟨a, ha⟩ := subgroupIso_of_same ⟨hS.2.2 D hD.1 hD.2.1, hD.2.2 S hS.1 hS.2.1⟩
  let p : specGroup (groupAlgebra k (Q × IntegerCharacters.{u})) ⟶ T :=
    specGroupMap (groupAlgebraMap k (m.prod f)) ≫ j.hom
  have hinj : Function.Injective (m.prod f) := by
    intro y z h
    apply saturatedProjection_prod_injective x f hfx
    have h₁ : m y = m z := congrArg Prod.fst h
    have h₂ : f y = f z := congrArg Prod.snd h
    let q := QuotientGroup.quotientKerEquivOfSurjective
      (saturatedProjection x) (saturatedProjection_surjective x)
    exact Prod.ext (congrArg q h₁) h₂
  let b := groupAlgebraMap k (m.prod f)
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  haveI : IsIso j.hom.hom.hom.left := F.map_isIso j.hom
  have hflat : Flat (specGroupMap b).hom.hom.left ∧ Surjective (specGroupMap b).hom.hom.left :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom b.hom.toAlgHom.toRingHom)).mpr
      (LinearAlgebraicGroups.hopfFaithfulFlatness k b (groupAlgebraMap_injective _ hinj))
  letI : Flat (specGroupMap b).hom.hom.left := hflat.1
  letI : Surjective (specGroupMap b).hom.hom.left := hflat.2
  letI : Flat p.hom.hom.left := by
    change Flat ((specGroupMap b).hom.hom.left ≫ j.hom.hom.hom.left)
    infer_instance
  letI : Surjective p.hom.hom.left := by
    change Surjective ((specGroupMap b).hom.hom.left ≫ j.hom.hom.hom.left)
    infer_instance
  apply (centralizes_comp_iff p i g).mp
  apply (centralizes_iff _ g).mpr
  intro U t z
  let p₁ := specGroupMap (groupAlgebraMap k (MonoidHom.inl Q IntegerCharacters))
  let p₂ := specGroupMap (groupAlgebraMap k (MonoidHom.inr Q IntegerCharacters))
  have hp : specGroupMap (groupAlgebraMap k (m.prod f)) =
      (p₁ ≫ diagonalClosedInclusion k N) * (p₂ ≫ specGroupMap (groupAlgebraMap k f)) := by
    rw [show diagonalClosedInclusion k N = specGroupMap (groupAlgebraMap k m) from rfl]
    simp only [p₁, p₂, latticeMap_comp]
    have h : m.prod f = (MonoidHom.inl Q IntegerCharacters).comp m *
        (MonoidHom.inr Q IntegerCharacters).comp f := by
      apply MonoidHom.ext
      intro v
      change (m v, f v) = (m v, 1) * (1, f v)
      rw [Prod.mk_mul_mk, mul_one, one_mul]
    change splitGroupHomEquiv (k := k) M (Q × IntegerCharacters) (m.prod f) = _
    rw [h, map_mul]
    rfl
  have hz : z ≫ (p ≫ i).hom.hom =
      ((z ≫ p₁.hom.hom ≫ e.hom.hom.hom ≫ a.hom.hom.hom) ≫ (S.inclusion ≫ i).hom.hom) *
      ((z ≫ p₂.hom.hom) ≫ (cochar ≫ i).hom.hom) := by
    change z ≫ (specGroupMap (groupAlgebraMap k (m.prod f))).hom.hom ≫ j.hom.hom.hom ≫ i.hom.hom = _
    rw [hp]
    change z ≫ ((p₁.hom.hom ≫ (diagonalClosedInclusion k N).hom.hom) *
        (p₂.hom.hom ≫ (specGroupMap (groupAlgebraMap k f)).hom.hom)) ≫ j.hom.hom.hom ≫ i.hom.hom =
      ((z ≫ p₁.hom.hom ≫ e.hom.hom.hom ≫ a.hom.hom.hom) ≫ (S.inclusion.hom.hom ≫ i.hom.hom)) *
      ((z ≫ p₂.hom.hom) ≫ (cochar.hom.hom ≫ i.hom.hom))
    have h₁ : e.hom.hom.hom ≫ a.hom.hom.hom ≫ S.inclusion.hom.hom =
        (diagonalClosedInclusion k N).hom.hom ≫ j.hom.hom.hom :=
      congrArg (fun u => u.hom.hom) ((congrArg (e.hom ≫ ·) ha).trans he)
    have h₂ : (specGroupMap (groupAlgebraMap k f)).hom.hom ≫ j.hom.hom.hom = cochar.hom.hom :=
      congrArg (fun u => u.hom.hom) hf'
    simp only [MonObj.comp_mul, MonObj.mul_comp, Category.assoc]
    rw [reassoc_of% h₁]
    exact congrArg (_ * ·) (by
      simpa only [Category.assoc] using congrArg (fun t => z ≫ p₂.hom.hom ≫ t ≫ i.hom.hom) h₂)
  rw [hz]
  exact ((centralizes_iff _ _).mp hs U t (z ≫ p₁.hom.hom ≫ e.hom.hom.hom ≫ a.hom.hom.hom)).mul_right
    ((centralizes_iff _ _).mp hcochar U t (z ≫ p₂.hom.hom))

open CocharacterDynamics (LimitDecomposition)
open private centralizes_precomp_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.ConnectedTorusCentralizer
open private mono_over from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

private theorem centralizes_iff_in_ambient {H A : GroupScheme k}
    (S : ClosedSubgroup H) (i : A ⟶ S.group) {Y : SchemeOver k} (g : Y ⟶ S.group.X) :
    Centralizes (i ≫ S.inclusion) (g ≫ S.inclusion.hom.hom) ↔ Centralizes i g := by
  haveI : Mono S.inclusion.hom.hom := mono_over _ S.isClosedImmersion
  constructor
  · intro h
    apply (centralizes_iff _ _).mpr
    intro U u a
    let m := IsMonHom.monoidHom S.inclusion.hom.hom U
    have e : Commute (m (u ≫ g)) (m (a ≫ i.hom.hom)) := by
      have h' := (centralizes_iff _ _).mp h U u a
      change Commute (u ≫ g ≫ S.inclusion.hom.hom)
        (a ≫ i.hom.hom ≫ S.inclusion.hom.hom) at h'
      change Commute ((u ≫ g) ≫ S.inclusion.hom.hom)
        ((a ≫ i.hom.hom) ≫ S.inclusion.hom.hom)
      simpa only [Category.assoc] using h'
    exact (cancel_mono S.inclusion.hom.hom).mp
      ((map_mul m _ _).trans (e.eq.trans (map_mul m _ _).symm))
  · intro h
    apply (centralizes_iff _ _).mpr
    intro U u a
    have h' := ((centralizes_iff _ _).mp h U u a).map (IsMonHom.monoidHom S.inclusion.hom.hom U)
    change Commute ((u ≫ g) ≫ S.inclusion.hom.hom)
      ((a ≫ i.hom.hom) ≫ S.inclusion.hom.hom) at h'
    change Commute (u ≫ g ≫ S.inclusion.hom.hom)
      (a ≫ i.hom.hom ≫ S.inclusion.hom.hom)
    simpa only [Category.assoc] using h'

private theorem centralizes_opposite_iff {H : GroupScheme k}
    (c : Cocharacter H) {Y : SchemeOver k} (g : Y ⟶ H.X) :
    Centralizes (oppositeCocharacter c) g ↔ Centralizes c g := by
  let e := (hopfSpec (CommRingCat.of k)).mapIso
    (CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv k k
      (MulEquiv.inv (G := IntegerCharacters.{u})))).symm.op
  change Centralizes (e.hom ≫ c) g ↔ Centralizes c g
  exact centralizes_precomp_iso e c g

private theorem subgroup_inclusion_of_represents {G : GroupScheme k}
    {A B : ClosedSubgroup G} {P Q : ∀ Y : SchemeOver k, (Y ⟶ G.X) → Prop}
    (hA : RepresentsSubgroup A P) (hB : RepresentsSubgroup B Q)
    (h : ∀ (Y : SchemeOver k) (g : Y ⟶ G.X), P Y g → Q Y g) :
    IsSubgroupOf A B := by
  have h₁ := (hA A.group.X A.inclusion.hom.hom).mpr ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨j, hj⟩ := (hB A.group.X A.inclusion.hom.hom).mp (h _ _ h₁)
  exact factor_group_through_subgroup B A.inclusion j hj

/-- In the root centralizer, the Levi factors of both signed limits are the maximal torus. -/
theorem limit_centralizers_eq_torus {G : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} (hT : IsSplitTorus T.group) {χ : Character T.group}
    (C : Specs.RankOneFlag.Centralizer T χ)
    (hH : GeometricRadicals.IsReductive (closedSubgroupAlgebraicGroup C.subgroup))
    (c : Cocharacter T.group) (hc : 0 < pairing T.group χ c)
    (D : LimitDecomposition (c ≫ C.torusIso.hom ≫ C.torus.inclusion))
    (E : LimitDecomposition (oppositeCocharacter (c ≫ C.torusIso.hom ≫ C.torus.inclusion))) :
    Specs.RankOneFlag.SameSubgroup D.centralizer C.torus ∧
      Specs.RankOneFlag.SameSubgroup E.centralizer C.torus := by
  let i := C.torusIso.hom ≫ C.torus.inclusion
  have hs (Y : SchemeOver k) (g : Y ⟶ C.subgroup.group.X) :
      Centralizes (C.kernelTorus.inclusion ≫ i) g := by
    apply (centralizes_iff_in_ambient C.subgroup _ g).mp
    have h : (C.kernelTorus.inclusion ≫ i) ≫ C.subgroup.inclusion =
        (subgroupOfSubgroup T C.kernelTorus).inclusion := by
      simp only [i, Category.assoc, C.torus_inclusion]
      rfl
    rw [h]
    exact (C.centralizes Y _).mpr ⟨g, rfl⟩
  have hcent (Y : SchemeOver k) (g : Y ⟶ C.subgroup.group.X) :
      Centralizes (c ≫ i) g ↔ Centralizes C.torus.inclusion g := by
    rw [← centralizes_precomp_iso C.torusIso C.torus.inclusion g]
    refine ⟨centralizes_kernelTorus_and_cocharacter hT C.kernelTorus_largest c hc i g (hs Y g), ?_⟩
    intro h
    apply (centralizes_iff _ _).mpr
    intro U u x
    have h' := (centralizes_iff _ _).mp h U u (x ≫ c.hom.hom)
    change Commute (u ≫ g) ((x ≫ c.hom.hom) ≫ i.hom.hom) at h'
    change Commute (u ≫ g) (x ≫ c.hom.hom ≫ i.hom.hom)
    simpa only [Category.assoc] using h'
  have hTrep := Reductive.TorusCentralizer.maximalTorusCentralizer _ hH C.torus
    (torus_of_iso C.torusIso (lattice_torus_of_split hT)) C.torus_maximal
  have hE (Y : SchemeOver k) (g : Y ⟶ C.subgroup.group.X) :
      Centralizes (oppositeCocharacter (c ≫ i)) g ↔ Centralizes C.torus.inclusion g :=
    (centralizes_opposite_iff _ g).trans (hcent Y g)
  exact ⟨⟨subgroup_inclusion_of_represents D.centralizer_points hTrep (fun Y g => (hcent Y g).mp),
    subgroup_inclusion_of_represents hTrep D.centralizer_points (fun Y g => (hcent Y g).mpr)⟩,
    ⟨subgroup_inclusion_of_represents E.centralizer_points hTrep (fun Y g => (hE Y g).mp),
    subgroup_inclusion_of_represents hTrep E.centralizer_points (fun Y g => (hE Y g).mpr)⟩⟩

open Specs.CharacterPairing (absoluteRoots adjointWeightVectors characterValue)
open Specs.AdjointRepresentation (GroupPoints)
open private adjointWeightVectors_iff zeroWeightVectors_iff_centralizes canonicalZero_eq
  characterValue_one from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing

private theorem character_eq_of_common_weight_vector (G : AffineAlgebraicGroup k)
    (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group)
    {χ ψ : Character T.group} {v : Lie k G.val}
    (hv : v ≠ 0) (hχ : v ∈ adjointWeightVectors T χ) (hψ : v ∈ adjointWeightVectors T ψ) :
    χ = ψ := by
  obtain ⟨s⟩ := identityLieBracket k G
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨n, b, C, L, l, Ad, hAd, _, _⟩ := adjointRepresentation k G s
  obtain ⟨i, hi⟩ : ∃ i, b.equivFun v i ≠ 0 := by
    by_contra! h
    apply hv
    refine Eq.trans ?_ (canonicalZero_eq s).symm
    apply b.equivFun.injective
    exact (funext h).trans b.equivFun.map_zero.symm
  apply RootData.CharacterPairing.characterValuesDetectCharacters hT
  intro R t
  have h₁ := (adjointWeightVectors_iff C l Ad hAd T χ v).mp hχ R t
  have h₂ := (adjointWeightVectors_iff C l Ad hAd T ψ v).mp hψ R t
  have he := congrFun (h₁.symm.trans h₂) i
  change characterValue χ R t * (algebraMap k R (b.equivFun v i)) =
    characterValue ψ R t * (algebraMap k R (b.equivFun v i)) at he
  have hu : IsUnit (algebraMap k R (b.equivFun v i)) :=
    (isUnit_iff_ne_zero.mpr hi).map (algebraMap k R)
  exact hu.mul_left_inj.mp he

/-- A nontrivial root supplies a tangent direction in its kernel-torus centralizer
whose adjoint character on the maximal torus is nontrivial. -/
theorem root_centralizer_noncommutative (G : AffineAlgebraicGroup k)
    (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group)
    {χ : Character T.group} (hχ : χ ∈ absoluteRoots T)
    (C : Specs.RankOneFlag.Centralizer T χ) : ¬ IsCommMonObj C.subgroup.group.X := by
  obtain ⟨hn, v, hv, hv₀⟩ := hχ
  let S := subgroupOfSubgroup T C.kernelTorus
  have hSaff : IsAffine S.group.X.left := (closedSubgroupAlgebraicGroup S).property.1
  have hTaff : IsAffine T.group.X.left := (closedSubgroupAlgebraicGroup T).property.1
  have hvS : v ∈ adjointWeightVectors S 1 := by
    intro R t
    have he := hv R (t ≫ C.kernelTorus.inclusion.hom.hom)
    have ha : characterValue χ R (t ≫ C.kernelTorus.inclusion.hom.hom) = 1 := by
      change characterValue (C.kernelTorus.inclusion ≫ χ) R t = 1
      rw [C.kernelTorus_largest.2.1]
      exact characterValue_one R t
    have e : t ≫ S.inclusion.hom.hom =
        (t ≫ C.kernelTorus.inclusion.hom.hom) ≫ T.inclusion.hom.hom :=
      (Category.assoc _ _ _).symm
    rw [ha] at he
    simpa only [characterValue_one, e] using he
  have hvC := (zeroWeightVectors_iff_centralizes S hSaff v).mp hvS
  obtain ⟨w, hw⟩ := (C.centralizes _ _).mp hvC
  intro hcomm
  letI := hcomm
  have hTcentral : Centralizes T.inclusion v.toMul.val := by
    apply (centralizes_iff _ _).mpr
    intro U u t
    let j := C.torusIso.hom ≫ C.torus.inclusion
    have h₁ : u ≫ v.toMul.val = (u ≫ w) ≫ C.subgroup.inclusion.hom.hom := by
      rw [Category.assoc, hw]
    have h₂ : t ≫ T.inclusion.hom.hom =
        (t ≫ j.hom.hom) ≫ C.subgroup.inclusion.hom.hom := by
      rw [Category.assoc]
      exact congrArg (fun f : T.group ⟶ G.val => t ≫ f.hom.hom) C.torus_inclusion.symm
    rw [h₁, h₂]
    exact (show Commute (u ≫ w) (t ≫ j.hom.hom) from mul_comm _ _).map
      (IsMonHom.monoidHom C.subgroup.inclusion.hom.hom U)
  exact hn (character_eq_of_common_weight_vector G T hT hv₀ hv
    ((zeroWeightVectors_iff_centralizes T hTaff v).mpr hTcentral))

open private charactersOfIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing

/-- A finite subgroup of the character-lattice automorphism group fixing
restriction to the largest kernel torus has cardinality at most two. -/
theorem card_le_two_of_fixes_kernelTorus {T : GroupScheme k} (hT : IsSplitTorus T)
    {χ : Character T} (hχ : χ ≠ 1) {S : ClosedSubgroup T}
    (hS : Specs.RankOneFlag.IsKernelSubtorus χ S) (W : Subgroup (MulAut (Character T)))
    [Finite W] (hW : ∀ (w : W) (ψ : Character T), S.inclusion ≫ w.val ψ = S.inclusion ≫ ψ) :
    Nat.card W ≤ 2 := by
  obtain ⟨r, ⟨j⟩⟩ := splitPresentation hT
  let M := StandardLattice.{u} r
  letI : Module.Finite ℤ (Additive M) := Module.Finite.equiv (latticeCoordinates r).symm
  letI : Group.FG M := GroupFG.iff_add_fg.mpr (Module.Finite.iff_addGroup_fg.mp inferInstance)
  letI := integerCharacters_hasUniqueRoots
  letI : HasUniqueRoots M := inferInstanceAs (HasUniqueRoots (Fin r → IntegerCharacters.{u}))
  let liftEquiv : IntegerCharacters.{u} ≃* Multiplicative ℤ := MulEquiv.ulift
  letI : IsCyclic IntegerCharacters.{u} :=
    isCyclic_of_injective liftEquiv.toMonoidHom liftEquiv.injective
  obtain ⟨x, hx⟩ := (latticeCharacter (k := k) M).surjective (j.hom ≫ χ)
  let c := (latticeCharacter (k := k) M).trans (charactersOfIso j)
  have hc : c x = χ := by
    change j.inv ≫ latticeCharacter (k := k) M x = χ
    rw [hx, Iso.inv_hom_id_assoc]
  have hxn : x ≠ 1 := fun h => hχ (hc.symm.trans (by rw [h, map_one]))
  obtain ⟨i, hi⟩ : ∃ i : Fin r, x i ≠ 1 := by
    by_contra! h
    exact hxn (funext h)
  let f : M →* IntegerCharacters.{u} :=
    { toFun := fun v => v i
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let p := (saturatedProjection x).comp c.symm.toMonoidHom
  let N := (saturatedProjection x).ker
  letI : IsCyclic N := saturatedProjection_ker_cyclic x f hi
  letI : IsCyclic p.ker := by
    let d : p.ker →* N :=
      (c.symm.toMonoidHom.comp p.ker.subtype).codRestrict N fun y => y.property
    exact isCyclic_of_injective d fun a b h => Subtype.ext
      (c.symm.injective (congrArg Subtype.val h))
  letI : HasUniqueRoots (Character T) :=
    ⟨fun n hn a b h => c.symm.injective (pow_left_injective hn (by
      simpa only [map_pow] using congrArg c.symm h))⟩
  obtain ⟨D, hD, e, he⟩ := kernel_subtorus_in_splitPresentation j χ x hx
  obtain ⟨a, ha⟩ := subgroupIso_of_same ⟨hS.2.2 D hD.1 hD.2.1, hD.2.2 S hS.1 hS.2.1⟩
  let m := QuotientGroup.mk' N
  have hb : e.hom ≫ a.hom ≫ S.inclusion = diagonalClosedInclusion k N ≫ j.hom :=
    (congrArg (e.hom ≫ ·) ha).trans he
  have hres (ψ : Character T) :
      latticeCharacter (k := k) (M ⧸ N) (m (c.symm ψ)) =
        e.hom ≫ a.hom ≫ S.inclusion ≫ ψ := by
    have hpsi : j.hom ≫ ψ = latticeCharacter (k := k) M (c.symm ψ) := by
      rw [← c.apply_symm_apply ψ]
      change j.hom ≫ (j.inv ≫ latticeCharacter (k := k) M (c.symm ψ)) =
        latticeCharacter (k := k) M (c.symm (c (c.symm ψ)))
      rw [Iso.hom_inv_id_assoc, MulEquiv.symm_apply_apply]
    rw [← latticeCharacter_comp m, ← hpsi, ← Category.assoc]
    change (diagonalClosedInclusion k N ≫ j.hom) ≫ ψ = _
    rw [← hb, Category.assoc, Category.assoc]
  apply card_le_two_of_fixes_quotient p W
  intro w ψ
  have heq : m (c.symm (w.val ψ)) = m (c.symm ψ) := by
    apply (latticeCharacter (k := k) _).injective
    rw [hres, hres, hW]
  let q := QuotientGroup.quotientKerEquivOfSurjective (saturatedProjection x)
    (saturatedProjection_surjective x)
  exact congrArg q heq

end Centralizer

section OppositeOpenCell

open Specs.CharacterDescent (Cocharacter)
open CocharacterDynamics (LimitDecomposition oppositeCocharacter multiplyFactors bigCellMap)
open private projection_eq_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.QuotientEmbedding
open private mono_over from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

variable {k : Type u} [Field k] {H : GroupScheme k}

private theorem opposite_cell_pullback {cochar : Cocharacter H}
    (D : LimitDecomposition cochar) (E : LimitDecomposition (oppositeCocharacter cochar))
    (Q : QuotientEmbedding.Presentation D.parabolic) :
    IsPullback (fst E.contracting.group.X D.parabolic.group.X)
      (multiplyFactors E.contracting.inclusion D.parabolic.inclusion)
      (E.contracting.inclusion.hom.hom ≫ Q.projection) Q.projection := by
  let U := E.contracting.group.X
  let B := D.parabolic.group.X
  let i := E.contracting.inclusion.hom.hom
  let j := D.parabolic.inclusion.hom.hom
  let m := multiplyFactors E.contracting.inclusion D.parabolic.inclusion
  have hmul {Y : SchemeOver k} (u : Y ⟶ U) (b : Y ⟶ B) :
      lift u b ≫ m = (u ≫ i) * (b ≫ j) := by
    change lift u b ≫ ((fst U B ≫ i) * (snd U B ≫ j)) = _
    simp only [MonObj.comp_mul, ← Category.assoc, lift_fst, lift_snd]
  have hq (Y : SchemeOver k) (u : Y ⟶ U) (h : Y ⟶ H.X) :
      u ≫ i ≫ Q.projection = h ≫ Q.projection ↔ ∃ b : Y ⟶ B, b ≫ j = (u ≫ i)⁻¹ * h := by
    rw [← Category.assoc u i]
    exact projection_eq_iff Q (u ≫ i) h
  have hc : fst U B ≫ (i ≫ Q.projection) = m ≫ Q.projection :=
    (hq _ _ _).mpr ⟨snd U B, by
      change snd U B ≫ j = (fst U B ≫ i)⁻¹ * ((fst U B ≫ i) * (snd U B ≫ j))
      rw [inv_mul_cancel_left]⟩
  have h (s : PullbackCone (i ≫ Q.projection) Q.projection) :
      ∃ b : s.pt ⟶ B, b ≫ j = (s.fst ≫ i)⁻¹ * s.snd := (hq _ _ _).mp s.condition
  choose a ha using h
  letI : Mono j := mono_over _ D.parabolic.isClosedImmersion
  refine IsPullback.of_isLimit (c := PullbackCone.mk (fst U B) m hc) ?_
  refine PullbackCone.IsLimit.mk hc (fun s => lift s.fst (a s)) (fun s => lift_fst _ _)
    (fun s => by rw [hmul, ha, mul_inv_cancel_left]) ?_
  intro s n hfst hsnd
  apply CartesianMonoidalCategory.hom_ext
  · rw [lift_fst, hfst]
  · have hcomp : n ≫ snd U B ≫ j = (s.fst ≫ i)⁻¹ * s.snd := by
      have e : (s.fst ≫ i) * (n ≫ snd U B ≫ j) = s.snd := by
        change n ≫ ((fst U B ≫ i) * (snd U B ≫ j)) = s.snd at hsnd
        simpa only [MonObj.comp_mul, ← Category.assoc, hfst] using hsnd
      rw [← e, inv_mul_cancel_left]
    rw [lift_snd, ← cancel_mono j, ha]
    exact hcomp

/-- The opposite contracting group maps by an open immersion to the right quotient
by the positive limit subgroup. -/
theorem opposite_contracting_open_cell (H : AffineAlgebraicGroup k) {cochar : Cocharacter H.val}
    (D : LimitDecomposition cochar) (E : LimitDecomposition (oppositeCocharacter cochar))
    (Q : QuotientEmbedding.Presentation D.parabolic)
    (hbig : IsOpenImmersion (bigCellMap D E).left) :
    IsOpenImmersion (E.contracting.inclusion.hom.hom ≫ Q.projection).left := by
  let U := E.contracting.group.X
  let d := multiplyFactors D.sectionMap D.contractingToParabolic
  let m := multiplyFactors E.contracting.inclusion D.parabolic.inclusion
  letI : IsIso d := D.product_iso
  let F := Over.forget (Spec (CommRingCat.of k))
  haveI : IsIso (𝟙 U ⊗ₘ d).left := F.map_isIso (𝟙 U ⊗ₘ d)
  have hd : d ≫ D.parabolic.inclusion.hom.hom =
      multiplyFactors D.centralizer.inclusion D.contracting.inclusion := by
    have hp : D.sectionMap.hom.hom ≫ D.parabolic.inclusion.hom.hom =
        D.centralizer.inclusion.hom.hom := congrArg (fun f => f.hom.hom) D.section_in_G
    have hu : D.contractingToParabolic.hom.hom ≫ D.parabolic.inclusion.hom.hom =
        D.contracting.inclusion.hom.hom := congrArg (fun f => f.hom.hom) D.contracting_in_G
    simp only [d, multiplyFactors, MonObj.mul_comp, Category.assoc, hp, hu]
  have h : (𝟙 U ⊗ₘ d) ≫ m = bigCellMap D E := by
    change _ ≫ ((fst _ _ ≫ E.contracting.inclusion.hom.hom) *
      (snd _ _ ≫ D.parabolic.inclusion.hom.hom)) = _
    have he : (𝟙 U ⊗ₘ d) ≫
        snd U D.parabolic.group.X ≫ D.parabolic.inclusion.hom.hom =
        snd U (D.centralizer.group.X ⊗ D.contracting.group.X) ≫
          multiplyFactors D.centralizer.inclusion D.contracting.inclusion := by
      rw [← Category.assoc, tensorHom_snd, Category.assoc, hd]
    rw [MonObj.comp_mul]
    change ((𝟙 U ⊗ₘ d) ≫ fst U D.parabolic.group.X ≫ E.contracting.inclusion.hom.hom) *
        ((𝟙 U ⊗ₘ d) ≫ snd U D.parabolic.group.X ≫ D.parabolic.inclusion.hom.hom) =
      (fst U _ ≫ E.contracting.inclusion.hom.hom) *
        (snd U _ ≫ multiplyFactors D.centralizer.inclusion D.contracting.inclusion)
    rw [he, ← Category.assoc, tensorHom_fst, Category.comp_id]
  have hm : IsOpenImmersion m.left := by
    apply (MorphismProperty.cancel_left_of_respectsIso (P := @IsOpenImmersion) (𝟙 U ⊗ₘ d).left m.left).mp
    rw [← Over.comp_left, h]
    exact hbig
  letI : LocallyOfFiniteType H.val.X.hom := H.property.2.1
  letI : IsAffine H.val.X.left := H.property.1
  letI : IsLocallyNoetherian H.val.X.left := LocallyOfFiniteType.isLocallyNoetherian H.val.X.hom
  letI : IsNoetherian H.val.X.left := ⟨⟩
  have hcover : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) Q.projection.left :=
    ⟨⟨Q.surjective, Q.flat⟩, inferInstance⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @IsOpenImmersion)
    ((opposite_cell_pullback D E Q).flip.map F) hcover hm

end OppositeOpenCell

section ReductiveCentralizer

open Specs.GeometricRadicals (IsReductive IsTrivialSubgroup geometricUnipotentRadical
  baseChangedSubgroup)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private normalSubgroup_of_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.NormalAffineQuotient
open private factor_closed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals

variable {k : Type u} [Field k]

private theorem trivial_of_subgroup_of_trivial {H : GroupScheme k}
    {A B : ClosedSubgroup H} (hAB : IsSubgroupOf A B)
    (hB : IsTrivialSubgroup B) : IsTrivialSubgroup A := by
  obtain ⟨f, hf⟩ := hAB
  obtain ⟨e⟩ := hB
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  letI : IsClosedImmersion (F.map A.inclusion) := A.isClosedImmersion
  haveI : Mono A.inclusion := F.mono_of_mono_map inferInstance
  haveI : Mono f := mono_of_mono_fac hf
  let p := f ≫ e.hom
  haveI : Mono p := inferInstanceAs (Mono (f ≫ e.hom))
  let j : Grp.trivial (SchemeOver k) ⟶ A.group := default
  have h : j ≫ p = 𝟙 _ := by
    subsingleton
  exact ⟨⟨p, j, (cancel_mono p).mp (by rw [Category.assoc, h, Category.comp_id, Category.id_comp]), h⟩⟩

private theorem reductive_of_groupIso {A B : AffineAlgebraicGroup k}
    (e : A.val ≅ B.val) (h : IsReductive A) : IsReductive B := by
  let θ := (Grp.forget (SchemeOver k) ⋙ Over.forget _).mapIso e
  have hθ : θ.inv ≫ A.val.X.hom = B.val.X.hom := Over.w e.inv.hom.hom
  have hs : Smooth B.val.X.hom := by
    rw [← hθ]
    letI := h.1
    infer_instance
  have hc : GeometricallyConnected B.val.X.hom := by
    rw [GeometricallyConnected.eq_geometrically, ← hθ]
    exact (geometrically (ConnectedSpace ·)).cancel_left_of_respectsIso θ.inv
      A.val.X.hom |>.mpr h.2.1.geometrically_connectedSpace
  refine ⟨hs, hc, ?_⟩
  let u := geometricUnipotentRadical B
  let d : (Specs.GeometricRadicals.GeometricGroup B).val ≅
      (Specs.GeometricRadicals.GeometricGroup A).val :=
    (groupBaseChange k (AlgebraicClosure k)).mapIso e.symm
  let φ := (Grp.forget (SchemeOver (AlgebraicClosure k)) ⋙ Over.forget _).mapIso d
  let V : ClosedSubgroup (Specs.GeometricRadicals.GeometricGroup A).val :=
    ⟨u.group, u.inclusion ≫ d.hom, by
      letI := u.isClosedImmersion
      change IsClosedImmersion (u.inclusion.hom.hom.left ≫ φ.hom)
      infer_instance⟩
  have hu := _root_.LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest B
  have hV : Specs.GeometricRadicals.IsSmoothConnectedNormal
      (G := Specs.GeometricRadicals.GeometricGroup A) V :=
    ⟨hu.1.1, hu.1.2.1, normalSubgroup_of_iso d.symm (Iso.refl _)
      (by change (u.inclusion ≫ d.hom) ≫ d.inv = 𝟙 _ ≫ u.inclusion
          simp only [Category.assoc, d.hom_inv_id, Category.comp_id, Category.id_comp]) hu.1.2.2⟩
  have hVu : Unipotent.IsUnipotent
      (closedSubgroupAlgebraicGroup (G := Specs.GeometricRadicals.GeometricGroup A) V) := by
    obtain ⟨L, p, hp⟩ := hu.2.1
    exact ⟨L, p, hp⟩
  have hA := _root_.LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest A
  have ht : IsTrivialSubgroup V :=
    trivial_of_subgroup_of_trivial (hA.2.2 V hV hVu) h.2.2
  exact ht

/-- Reductivity holds for any choice of the representing root centralizer. -/
theorem root_centralizer_reductive (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (hTs : IsSplitTorus T.group)
    (hT : Specs.RankOneFlag.IsGeometricallyMaximal T) {χ : Character T.group}
    (C : Specs.RankOneFlag.Centralizer T χ) :
    IsReductive (closedSubgroupAlgebraicGroup C.subgroup) := by
  let S := subgroupOfSubgroup T C.kernelTorus
  obtain ⟨A, hA, hAr⟩ := Reductive.SubtorusCentralizer.centralizerReductive G hG T S
    (lattice_torus_of_split hTs) C.kernelTorus_largest.1 ⟨C.kernelTorus.inclusion, rfl⟩ hT
  obtain ⟨e, _⟩ := subgroupIso_of_same
    ⟨subgroup_inclusion_of_represents hA C.centralizes (fun _ _ h => h),
      subgroup_inclusion_of_represents C.centralizes hA (fun _ _ h => h)⟩
  exact reductive_of_groupIso e hAr


open private fieldSpecMap_surjective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private isCommMonObj_of_groupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.HopfAlgebras
open private splitTorus_sectionsCommute from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
open private isIso_of_trivial_kernel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness

private theorem commutative_of_scalar_extension {K : Type u} [Field K] [Algebra k K]
    {H : GroupScheme k} (h : IsCommMonObj ((groupBaseChange k K).obj H).X) :
    IsCommMonObj H.X := by
  let F := baseChange k K
  letI : Surjective (fieldSpecMap k K) := fieldSpecMap_surjective K
  letI : Flat (fieldSpecMap k K) := by
    rw [Flat.SpecMap_iff]
    let : Algebra k K := (CommRingCat.ofHom (algebraMap k K)).hom.toAlgebra
    exact Module.Flat.of_free (R := k) (M := K)
  letI : QuasiCompact (fieldSpecMap k K) := inferInstanceAs (QuasiCompact (Spec.map _))
  have ff : F.Faithful := inferInstanceAs ((Over.pullback (fieldSpecMap k K)).Faithful)
  apply (isCommMonObj_iff_isMulCommutative _).mpr
  intro Y
  constructor
  constructor
  change ∀ g t : Y ⟶ H.X, g * t = t * g
  intro g t
  let M (g : Y ⟶ H.X) : F.obj Y ⟶ ((groupBaseChange k K).obj H).X := F.map g
  have m (g t : Y ⟶ H.X) : F.map (g * t) = M g * M t := by
    change F.map (lift g t ≫ μ[H.X]) =
      lift (F.map g) (F.map t) ≫ Functor.LaxMonoidal.μ F H.X H.X ≫ F.map μ[H.X]
    rw [Functor.map_comp, Functor.Monoidal.lift_μ_assoc]
  apply ff.map_injective
  rw [m, m]
  letI := (isCommMonObj_iff_isMulCommutative _).mp h (F.obj Y)
  exact mul_comm' (M g) (M t)

private theorem commutative_of_solvable_of_trivial_radical
    [IsAlgClosed k] (H : AffineAlgebraicGroup k)
    (hs : Smooth H.val.X.hom) (hc : ConnectedSpace H.val.X.left)
    {R : ClosedSubgroup H.val} (hrad : Specs.GeometricRadicals.IsUnipotentRadical H R)
    (hR : IsTrivialSubgroup R) (hsol : Specs.SchemeDerivedGroup.IsSolvable H.val) :
    IsCommMonObj H.val.X := by
  obtain ⟨U, D, p, hU, hq, hD, _⟩ := _root_.LinearAlgebraicGroups.GeometricTorusSplitting.splitting
    H hs hc hsol
  have hUR := hrad.2.2 U ⟨hU.1, hU.2.1, hU.2.2.1⟩ hU.2.2.2.1
  letI : IsIso p := isIso_of_trivial_kernel p U hq (trivial_of_subgroup_of_trivial hUR hR)
  exact isCommMonObj_of_groupIso (asIso p).symm
    ((isCommMonObj_iff_isMulCommutative _).mpr (splitTorus_sectionsCommute hD))


open Specs.GeometricRadicals (GeometricGroup)
open Specs.CharacterPairing (absoluteRoots)
open Specs.SchemeDerivedGroup (IsSolvable)
open private geometricSmooth from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper

/-- The root direction excludes solvability of the geometric centralizer. -/
theorem root_centralizer_geometrically_nonsolvable
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (hTs : IsSplitTorus T.group)
    (hT : Specs.RankOneFlag.IsGeometricallyMaximal T)
    {χ : Character T.group} (hχ : χ ∈ absoluteRoots T)
    (C : Specs.RankOneFlag.Centralizer T χ) :
    ¬ IsSolvable (GeometricGroup (closedSubgroupAlgebraicGroup C.subgroup)).val := by
  let H := closedSubgroupAlgebraicGroup C.subgroup
  have hH : IsReductive H := root_centralizer_reductive G hG T hTs hT C
  have hs := geometricSmooth H hH.1
  have hc : ConnectedSpace (GeometricGroup H).val.X.left :=
    pullback_of_geometrically hH.2.1.geometrically_connectedSpace (AlgebraicClosure k)
      (fieldSpecMap k (AlgebraicClosure k))
  have hrad := _root_.LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest H
  intro hsol
  apply root_centralizer_noncommutative G T hTs hχ C
  exact commutative_of_scalar_extension (K := AlgebraicClosure k)
    (commutative_of_solvable_of_trivial_radical (GeometricGroup H) hs hc hrad hH.2.2 hsol)

end ReductiveCentralizer

section WeylSections

open Specs.NormalizerLatticeAction (ConstantGroup SplitImage)
open private mono_over centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

variable {k : Type u} [Field k]

/-- Central subgroups of a torus have unchanged restricted characters under the normalizer. -/
private theorem split_labels_fix_central_map {H N Q T S : GroupScheme k}
    {i : T ⟶ H} (hi : IsClosedImmersion i.hom.hom.left)
    {v : N ⟶ H} {q : N ⟶ Q} (I : SplitImage i v q) (s : S ⟶ T)
    (h : ∀ n : 𝟙_ (SchemeOver k) ⟶ Q.X, ∃ a : 𝟙_ (SchemeOver k) ⟶ N.X, a ≫ q.hom.hom = n)
    (hs : ∀ a : 𝟙_ (SchemeOver k) ⟶ N.X, Centralizes (s ≫ i) (a ≫ v.hom.hom))
    (w : I.labels) (χ : Character T) : s ≫ w.val χ = s ≫ χ := by
  obtain ⟨a, ha⟩ := h (I.constantGroup.sectionPoint w)
  have he := I.conjugates _ a w (ha.trans (by congr 1))
  let g := toUnit S.X ≫ a ≫ v.hom.hom
  let l := lift s.hom.hom (toUnit S.X)
  have he' : g * (s ≫ i).hom.hom * g⁻¹ = (s ≫ (I.conjugation w).hom ≫ i).hom.hom := by
    have e := congrArg (fun r => l ≫ r) he
    simpa only [l, g, conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc,
      lift_fst_assoc, lift_snd_assoc, Grp.comp_hom_hom] using e
  have hh : Commute g (s ≫ i).hom.hom := by
    simpa only [g, Category.assoc, Category.id_comp] using
      (centralizes_iff _ _).mp (hs a) S.X (toUnit S.X) (𝟙 S.X)
  haveI : Mono i.hom.hom := mono_over _ hi
  have hc : s ≫ (I.conjugation w).hom = s := by
    apply Grp.hom_ext
    apply (cancel_mono i.hom.hom).mp
    change (s ≫ (I.conjugation w).hom ≫ i).hom.hom = (s ≫ i).hom.hom
    rw [← he', hh.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hc' : s ≫ (I.conjugation w).inv = s := by
    calc
      s ≫ (I.conjugation w).inv = (s ≫ (I.conjugation w).hom) ≫ (I.conjugation w).inv :=
        congrArg (· ≫ (I.conjugation w).inv) hc.symm
      _ = s := by rw [Category.assoc, (I.conjugation w).hom_inv_id, Category.comp_id]
  rw [I.characterAction, ← Category.assoc, hc']

private theorem scalarExtendedPoint_natural (K : Type u) [Field K] [Algebra k K]
    {X Y : SchemeOver k} (x : 𝟙_ (SchemeOver k) ⟶ X) (f : X ⟶ Y) :
    scalarExtendedRationalPoint K (x ≫ f) =
      scalarExtendedRationalPoint K x ≫ (baseChange k K).map f := by
  simp only [scalarExtendedRationalPoint, Functor.map_comp, Category.assoc]

/-- Each rational point of a scalar-extended constant group is a scalar-extended section. -/
private theorem constant_sections_after_scalar_extension {Q : GroupScheme k}
    {W : Type u} [Group W] (C : ConstantGroup Q W) (K : Type u) [Field K] [Algebra k K]
    (q : 𝟙_ (SchemeOver K) ⟶ (baseChange k K).obj Q.X) :
    ∃ w : W, q = scalarExtendedRationalPoint K (C.sectionPoint w) := by
  let f := fieldSpecMap k K
  let M := Over.map f
  let Y : SchemeOver K := 𝟙_ (SchemeOver K)
  let E := (Over.mapPullbackAdj f).homEquiv Y Q.X
  let e : (Over.mk (𝟙 (Spec (CommRingCat.of K))) : SchemeOver K) ≅ Y :=
    Over.mkIdTerminal.uniqueUpToIso isTerminalTensorUnit
  let e' : (M.obj (Over.mk (𝟙 (Spec (CommRingCat.of K))))) ≅ M.obj Y := M.mapIso e
  haveI : Subsingleton (M.obj Y).left :=
    ((Over.forget (Spec (CommRingCat.of k))).mapIso e').hom.homeomorph.subsingleton_congr.mp
      (inferInstanceAs (Subsingleton (Spec (CommRingCat.of K))))
  let θ : LocallyConstant (M.obj Y).left W := C.families (M.obj Y) (E.symm q)
  let p := e.hom.left (IsLocalRing.closedPoint K)
  let w := θ p
  refine ⟨w, E.symm.injective ?_⟩
  have hpt (z : 𝟙_ (SchemeOver k) ⟶ Q.X) :
      E.symm (scalarExtendedRationalPoint K z) = toUnit (M.obj Y) ≫ z := by
    have hn := (Over.mapPullbackAdj f).homEquiv_naturality_right_symm
      (Functor.LaxMonoidal.ε (baseChange k K) : Y ⟶ (baseChange k K).obj (𝟙_ (SchemeOver k))) z
    rw [scalarExtendedRationalPoint, hn]
    congr 1
    subsingleton
  rw [hpt]
  apply (C.families _).injective
  rw [C.constant]
  apply LocallyConstant.ext
  intro x
  change θ x = θ p
  congr 1
  exact Subsingleton.elim _ _

open private baseChangeKernelSquare from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components

private theorem two_labels {W : Type u} [Group W] [Finite W] (h : Nat.card W ≤ 2) :
    ∃ v : W, ∀ w : W, w = 1 ∨ w = v := by
  classical
  by_cases h₂ : Nat.card W = 2
  · obtain ⟨v, _, hv⟩ := (Nat.card_eq_two_iff' (1 : W)).mp h₂
    exact ⟨v, fun w => (eq_or_ne w 1).imp_right (hv w)⟩
  · have hpos : 0 < Nat.card W := Nat.card_pos
    have h₁ : Nat.card W = 1 := by omega
    letI := (Nat.card_eq_one_iff_unique.mp h₁).1
    exact ⟨1, fun w => Or.inl (Subsingleton.elim _ _)⟩

/-- Every normalizer point over an extension field is represented modulo
the extended torus by one of two ground-field sections. -/
private theorem two_geometric_normalizer_cosets {H : GroupScheme k}
    {T N : ClosedSubgroup H} {W : GroupScheme k} (q : N.group ⟶ W)
    (j : T.group ⟶ N.group) (hj : j ≫ N.inclusion = T.inclusion)
    (hq : IsPullback j.hom.hom (toUnit _) q.hom.hom η[W.X])
    (hN : RepresentsSubgroup N (fun _ g ↦ Normalizes T.inclusion g))
    (hT : RepresentsSubgroup T (fun _ g ↦ Centralizes T.inclusion g))
    (I : SplitImage T.inclusion N.inclusion q)
    (hcard : Nat.card I.labels ≤ 2)
    (hlift : ∀ w : 𝟙_ (SchemeOver k) ⟶ W.X,
      ∃ a : 𝟙_ (SchemeOver k) ⟶ N.group.X, a ≫ q.hom.hom = w) :
    ∃ n : 𝟙_ (SchemeOver k) ⟶ H.X, Normalizes T.inclusion n ∧
      ∀ (K : Type u) [Field K] [Algebra k K],
        ∀ g : 𝟙_ (SchemeOver K) ⟶ ((groupBaseChange k K).obj H).X,
          Normalizes ((groupBaseChange k K).map T.inclusion) g →
          Centralizes ((groupBaseChange k K).map T.inclusion) g ∨
            Centralizes ((groupBaseChange k K).map T.inclusion)
              ((show 𝟙_ (SchemeOver K) ⟶ ((groupBaseChange k K).obj H).X
                 from scalarExtendedRationalPoint K n)⁻¹ * g) := by
  letI := I.finite
  obtain ⟨v, hv⟩ := two_labels hcard
  obtain ⟨a, ha⟩ := hlift (I.constantGroup.sectionPoint v)
  let n := a ≫ N.inclusion.hom.hom
  refine ⟨n, (hN _ _).mpr ⟨a, rfl⟩, ?_⟩
  intro K _ _ g hg
  let F := groupBaseChange k K
  obtain ⟨hNB, hNB'⟩ := normalizerSchemeBaseChange k K T.inclusion N T.isClosedImmersion hN
  obtain ⟨hTB, hTB'⟩ := centralizerSchemeBaseChange k K T.inclusion T hT
  obtain ⟨b, hb⟩ := (hNB' _ _).mp hg
  change b ≫ (F.map N.inclusion).hom.hom = g at hb
  let q' := (F.map q).hom.hom
  let j' := (F.map j).hom.hom
  let d := (F.map N.inclusion).hom.hom
  letI : IsMonHom d := inferInstanceAs (IsMonHom (F.map N.inclusion).hom.hom)
  letI : IsMonHom q' := inferInstanceAs (IsMonHom (F.map q).hom.hom)
  have hj' : j' ≫ d = (F.map T.inclusion).hom.hom := by
    change (F.map j ≫ F.map N.inclusion).hom.hom = _
    rw [← Functor.map_comp, hj]
  have hp : IsPullback j' (toUnit _) q' η[(F.obj W).X] := baseChangeKernelSquare q j hq
  have hcent (c : 𝟙_ (SchemeOver K) ⟶ (F.obj N.group).X)
      (hc : c ≫ q' = η[(F.obj W).X]) :
      Centralizes (F.map T.inclusion) (c ≫ d) := by
    have hker : c ≫ q' = toUnit _ ≫ η[(F.obj W).X] := by
      rw [show toUnit (𝟙_ (SchemeOver K)) = 𝟙 _ from Subsingleton.elim _ _, Category.id_comp, hc]
    exact (hTB' _ _).mpr ⟨hp.lift c (toUnit _) hker, by
      change hp.lift c (toUnit _) hker ≫ (F.map T.inclusion).hom.hom = c ≫ d
      rw [← hj', ← Category.assoc, hp.lift_fst]⟩
  obtain ⟨w, hw⟩ := constant_sections_after_scalar_extension I.constantGroup K (b ≫ q')
  rcases hv w with rfl | rfl
  · left
    rw [← hb]
    apply hcent
    have he : I.constantGroup.sectionPoint 1 = η[W.X] := by
      rw [map_one, CategoryTheory.Hom.one_def,
        show toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ from Subsingleton.elim _ _, Category.id_comp]
    exact hw.trans (congrArg (scalarExtendedRationalPoint K) he)
  · right
    let a' : 𝟙_ (SchemeOver K) ⟶ (F.obj N.group).X := scalarExtendedRationalPoint K a
    have hq' : a' ≫ q' = b ≫ q' := by
      change scalarExtendedRationalPoint K a ≫ (baseChange k K).map q.hom.hom = _
      rw [← scalarExtendedPoint_natural, ha, hw]
    have hn : scalarExtendedRationalPoint K n = a' ≫ d :=
      scalarExtendedPoint_natural K a N.inclusion.hom.hom
    rw [hn, ← hb, ← GrpObj.inv_comp, ← MonObj.mul_comp]
    apply hcent
    rw [MonObj.mul_comp, GrpObj.inv_comp, hq', inv_mul_cancel]
    rw [CategoryTheory.Hom.one_def, show toUnit (𝟙_ (SchemeOver K)) = 𝟙 _ from Subsingleton.elim _ _,
      Category.id_comp]


open Specs.GeometricRadicals (IsReductive)
open Specs.RankOneFlag (Centralizer IsKernelSubtorus)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open private charactersOfIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing

private def transportKernelSubtorus {T U : GroupScheme k} (e : T ≅ U)
    (S : ClosedSubgroup T) : ClosedSubgroup U := by
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  letI := F.map_isIso e.hom
  letI := S.isClosedImmersion
  refine ⟨S.group, S.inclusion ≫ e.hom, ?_⟩
  change IsClosedImmersion (S.inclusion.hom.hom.left ≫ F.map e.hom)
  infer_instance

private theorem isKernelSubtorus_transport {T U : GroupScheme k} (e : T ≅ U)
    {χ : Character T} {S : ClosedSubgroup T} (h : IsKernelSubtorus χ S) :
    IsKernelSubtorus (e.inv ≫ χ) (transportKernelSubtorus e S) := by
  have he : (transportKernelSubtorus e S).inclusion ≫ e.inv = S.inclusion := by
    change (S.inclusion ≫ e.hom) ≫ e.inv = _
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  refine ⟨h.1, ?_, ?_⟩
  · rw [← Category.assoc, he]
    exact h.2.1
  · intro B hB hb
    let A := transportKernelSubtorus e.symm B
    have ha : A.inclusion ≫ χ = 1 := by
      change (B.inclusion ≫ e.inv) ≫ χ = 1
      rwa [Category.assoc]
    obtain ⟨j, hj⟩ := h.2.2 A hB ha
    refine ⟨j, ?_⟩
    change j ≫ S.inclusion ≫ e.hom = B.inclusion
    rw [← Category.assoc, hj]
    change (B.inclusion ≫ e.inv) ≫ e.hom = B.inclusion
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]

/-- The normalizer of the maximal torus of a root centralizer has at most two
cosets modulo that torus. One ground-field section suffices, besides the identity,
to represent them over every extension field. -/
theorem root_normalizer_two_cosets {G : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} (hT : IsSplitTorus T.group)
    {χ : Character T.group} (hχ : χ ≠ 1) (C : Centralizer T χ)
    (hH : IsReductive (closedSubgroupAlgebraicGroup C.subgroup)) :
    ∃ n : 𝟙_ (SchemeOver k) ⟶ C.subgroup.group.X, Normalizes C.torus.inclusion n ∧
      ∀ (K : Type u) [Field K] [Algebra k K],
        ∀ g : 𝟙_ (SchemeOver K) ⟶ ((groupBaseChange k K).obj C.subgroup.group).X,
          Normalizes ((groupBaseChange k K).map C.torus.inclusion) g →
          Centralizes ((groupBaseChange k K).map C.torus.inclusion) g ∨
            Centralizes ((groupBaseChange k K).map C.torus.inclusion)
              ((show 𝟙_ (SchemeOver K) ⟶ ((groupBaseChange k K).obj C.subgroup.group).X
                from scalarExtendedRationalPoint K n)⁻¹ * g) := by
  let H := closedSubgroupAlgebraicGroup C.subgroup
  let T' := C.torus
  have hT's : IsSplitTorus T'.group := by
    obtain ⟨r, ⟨e⟩⟩ := hT
    exact ⟨r, ⟨C.torusIso.symm ≪≫ e⟩⟩
  have hT't := lattice_torus_of_split hT's
  obtain ⟨N, j, _, W, q, hN, hj, hq, _, _, _, hsplit⟩ :=
    Reductive.WeylScheme.weylScheme H hH T' hT't C.torus_maximal
  obtain ⟨⟨I⟩, hpoint⟩ := hsplit hT's
  have hlift (w : 𝟙_ (SchemeOver k) ⟶ W.val.X) := (hpoint w).2
  let S := transportKernelSubtorus C.torusIso C.kernelTorus
  have hS := isKernelSubtorus_transport C.torusIso C.kernelTorus_largest
  have hnχ : C.torusIso.inv ≫ χ ≠ 1 := by
    exact fun he => hχ ((charactersOfIso C.torusIso).injective (he.trans (map_one _).symm))
  have hs (a : 𝟙_ (SchemeOver k) ⟶ N.group.X) :
      Centralizes (S.inclusion ≫ T'.inclusion) (a ≫ N.inclusion.hom.hom) := by
    apply (centralizes_iff_in_ambient C.subgroup _ _).mp
    have he : (S.inclusion ≫ T'.inclusion) ≫ C.subgroup.inclusion =
        (subgroupOfSubgroup T C.kernelTorus).inclusion := by
      change ((C.kernelTorus.inclusion ≫ C.torusIso.hom) ≫ C.torus.inclusion) ≫
        C.subgroup.inclusion = C.kernelTorus.inclusion ≫ T.inclusion
      rw [Category.assoc, Category.assoc, C.torus_inclusion]
    rw [he]
    exact (C.centralizes _ _).mpr ⟨a ≫ N.inclusion.hom.hom, rfl⟩
  letI := I.finite
  have hc := card_le_two_of_fixes_kernelTorus hT's hnχ hS I.labels
    (split_labels_fix_central_map T'.isClosedImmersion I S.inclusion hlift hs)
  exact two_geometric_normalizer_cosets q j hj hq.1 hN
    (Reductive.TorusCentralizer.maximalTorusCentralizer H hH T' hT't C.torus_maximal) I hc hlift

end WeylSections

section LimitFunctoriality

open Specs.AdjointRepresentation (GroupPoints)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open CocharacterDynamics (HasLimit LimitDecomposition oppositeCocharacter)

variable {k : Type u} [Field k] {A G : GroupScheme k}

/-- A morphism of groups carries a polynomial limit to the corresponding polynomial limit. -/
private theorem map_hasLimit (f : A ⟶ G) (c : Cocharacter A) {R : TestAlgebra k}
    {a z : GroupPoints A R} (h : HasLimit c a z) :
    HasLimit (c ≫ f) (show GroupPoints G R from a ≫ f.hom.hom)
      (show GroupPoints G R from z ≫ f.hom.hom) := by
  obtain ⟨p, hp, hz⟩ := h
  refine ⟨p ≫ f.hom.hom, ?_, ?_⟩
  · have horbit : CocharacterDynamics.orbit c a ≫ f.hom.hom =
        CocharacterDynamics.orbit (c ≫ f) (show GroupPoints G R from a ≫ f.hom.hom) := by
      change (_ * _ * _) ≫ f.hom.hom = _ * _ * _
      rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
      simp only [CocharacterDynamics.cocharacterPoint, Category.assoc]
      rfl
    rw [← horbit, ← hp]
    exact (Category.assoc _ _ _).symm
  · change _ = z ≫ f.hom.hom
    rw [← hz]
    exact (Category.assoc _ _ _).symm

open private subgroupInclusionFactors pointHom from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

private theorem map_limit_parabolic (ha : IsAffine A.X.left)
    (f : A ⟶ G) {c : Cocharacter A} (D : LimitDecomposition c)
    (E : LimitDecomposition (c ≫ f)) :
    ∃ j : D.parabolic.group ⟶ E.parabolic.group,
      j ≫ E.parabolic.inclusion = D.parabolic.inclusion ≫ f := by
  letI := ha
  letI := D.parabolic.isClosedImmersion
  have hAff : IsAffine D.parabolic.group.X.left :=
    isAffine_of_isAffineHom D.parabolic.inclusion.hom.hom.left
  refine subgroupInclusionFactors hAff E.parabolic (D.parabolic.inclusion ≫ f) ?_
  intro R p
  let p₀ := pointHom D.parabolic.inclusion R p
  obtain ⟨z, hz⟩ := (D.parabolic_points R p₀).mpr ⟨p, rfl⟩
  have eq : pointHom (D.parabolic.inclusion ≫ f) R p = pointHom f R p₀ :=
    (Category.assoc p D.parabolic.inclusion.hom.hom f.hom.hom).symm
  apply (E.parabolic_points _ _).mp
  exact ⟨pointHom f R z, eq.symm ▸ map_hasLimit f c hz⟩

private theorem map_limit_contracting (ha : IsAffine A.X.left)
    (f : A ⟶ G) {c : Cocharacter A} (D : LimitDecomposition c)
    (E : LimitDecomposition (c ≫ f)) :
    ∃ j : D.contracting.group ⟶ E.contracting.group,
      j ≫ E.contracting.inclusion = D.contracting.inclusion ≫ f := by
  letI := ha
  letI := D.contracting.isClosedImmersion
  have hAff : IsAffine D.contracting.group.X.left :=
    isAffine_of_isAffineHom D.contracting.inclusion.hom.hom.left
  refine subgroupInclusionFactors hAff E.contracting (D.contracting.inclusion ≫ f) ?_
  intro R p
  let p₀ := pointHom D.contracting.inclusion R p
  have hp := (D.contracting_points R p₀).mpr ⟨p, rfl⟩
  have eq : pointHom (D.contracting.inclusion ≫ f) R p = pointHom f R p₀ :=
    (Category.assoc p D.contracting.inclusion.hom.hom f.hom.hom).symm
  have hh : HasLimit (c ≫ f) (pointHom f R p₀) (pointHom f R 1) := map_hasLimit f c hp
  rw [map_one] at hh
  exact (E.contracting_points _ _).mp (eq.symm ▸ hh)

end LimitFunctoriality

section BorelComparison

open Specs.GeometricRadicals (GeometricGroup IsUnipotentRadical IsTrivialSubgroup IsMaximalTorus
  geometricUnipotentRadical)
open Specs.GeometricBorelConjugacy (IsBorel IsSmoothConnectedSolvable subgroupOfSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf IsSolvable)
open Specs.Unipotent (IsUnipotent closedSubgroupAlgebraicGroup)
open Specs.RankOneFlag (SameSubgroup)
open CocharacterDynamics (LimitDecomposition oppositeCocharacter multiplyFactors bigCellMap
  affineAlgebraicSubgroup)
open private subgroupOf_trans exists_borel_above
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private factor_closed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private factors_reduced_component from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SubtorusCentralizer
open private subgroup_of_intersection from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A geometric Borel contains each of its closed unipotent subgroups in its radical. -/
private theorem unipotent_subgroup_in_borel_radical {H : AffineAlgebraicGroup k}
    {B A : ClosedSubgroup H.val} (hB : IsBorel B) (hAB : IsSubgroupOf A B)
    (hu : IsUnipotent (closedSubgroupAlgebraicGroup A))
    {U : ClosedSubgroup B.group}
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U) :
    IsSubgroupOf A (subgroupOfSubgroup B U) := by
  obtain ⟨f, hf⟩ := hAB
  let V : ClosedSubgroup B.group := ⟨A.group, f, factor_closed hf⟩
  let D := closedSubgroupAlgebraicGroup B
  obtain ⟨L, _, _, hL, _, _⟩ := LinearAlgebraicGroups.GeometricTorusSplitting.splitting D
    hB.1.1 hB.1.2.1 hB.1.2.2
  have hLU := hU.2.2 L ⟨hL.1, hL.2.1, hL.2.2.1⟩ hL.2.2.2.1
  have hu' : IsUnipotent (closedSubgroupAlgebraicGroup (G := D) V) := by
    obtain ⟨R, e, he⟩ := hu
    exact ⟨R, e, he⟩
  obtain ⟨j, hj⟩ := subgroupOf_trans (hL.2.2.2.2 V hu') hLU
  refine ⟨j, ?_⟩
  change j ≫ U.inclusion ≫ B.inclusion = A.inclusion
  rw [← Category.assoc, hj]
  exact hf

/-- When the two displayed Borels exhaust the Borels through the torus,
a smooth connected unipotent group in both belongs to the ambient radical. -/
private theorem unipotent_subgroup_in_borel_pair {H : AffineAlgebraicGroup k}
    (hs : Smooth H.val.X.hom) (hc : ConnectedSpace H.val.X.left)
    {T B₁ B₂ A R : ClosedSubgroup H.val}
    (hT : IsMaximalTorus T) (hR : IsUnipotentRadical H R)
    (hpair : ∀ B : ClosedSubgroup H.val, IsBorel B → IsSubgroupOf T B →
      SameSubgroup B B₁ ∨ SameSubgroup B B₂)
    (h₁ : IsSubgroupOf A B₁) (h₂ : IsSubgroupOf A B₂)
    (hAs : Smooth A.group.X.hom) (hAc : ConnectedSpace A.group.X.left)
    (hA : IsUnipotent (closedSubgroupAlgebraicGroup A)) : IsSubgroupOf A R := by
  obtain ⟨I, J, hI, hJ, hIU⟩ :=
    Reductive.UnipotentRadicalIntersection.unipotentRadicalFromBorelIntersection H hs hc T hT
  have hAI : IsSubgroupOf A I := by
    apply (subgroup_of_intersection hI).mpr
    rintro _ ⟨B, U, hB, hTB, hU, rfl⟩
    have hAB : IsSubgroupOf A B :=
      (hpair B hB hTB).elim (fun hb => subgroupOf_trans h₁ hb.2)
        (fun hb => subgroupOf_trans h₂ hb.2)
    exact unipotent_subgroup_in_borel_radical hB hAB hA hU
  obtain ⟨f, hf⟩ := hAI
  obtain ⟨j, hj⟩ := factors_reduced_component J hJ f hAs hAc
  have e : IsSubgroupOf A (subgroupOfSubgroup I J) :=
    ⟨j, by change j ≫ J.inclusion ≫ I.inclusion = A.inclusion
           rw [← Category.assoc, hj, hf]⟩
  exact subgroupOf_trans e (hR.2.2 _ hIU.1 hIU.2.1)


open private isIso_of_schemeIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private trivial_map_eq_one from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness

/-- A closed subgroup that contains a dynamic open cell is the ambient group. -/
private theorem isIso_subgroup_of_big_cell_factor (H : AffineAlgebraicGroup k)
    [Smooth H.val.X.hom] [ConnectedSpace H.val.X.left]
    {c : Cocharacter H.val} (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (B : ClosedSubgroup H.val)
    (p : E.contracting.group.X ⊗ (D.centralizer.group.X ⊗ D.contracting.group.X) ⟶ B.group.X)
    (hp : p ≫ B.inclusion.hom.hom = bigCellMap D E) : IsIso B.inclusion := by
  haveI : IsIntegral H.val.X.left :=
    WordDomainGeometry.smoothConnectedGroupIntegral H inferInstance inferInstance
  letI : IsClosedImmersion B.inclusion.hom.hom.left := B.isClosedImmersion
  letI := CocharacterDynamics.bigCell H c D E
  have hnonempty : (Set.range (bigCellMap D E).left).Nonempty :=
    ⟨_, Set.mem_range_self ((lift η[E.contracting.group.X]
      (lift η[D.centralizer.group.X] η[D.contracting.group.X])).left (IsLocalRing.closedPoint k))⟩
  have hdense := (bigCellMap D E).left.isOpenEmbedding.isOpen_range.dense hnonempty
  have hle : Set.range (bigCellMap D E).left ⊆ Set.range B.inclusion.hom.hom.left := by
    rw [← hp, Over.comp_left]
    change Set.range (B.inclusion.hom.hom.left ∘ p.left) ⊆ _
    exact Set.range_comp_subset_range _ _
  have hclosed : IsClosed (Set.range B.inclusion.hom.hom.left) :=
    B.inclusion.hom.hom.left.isClosedEmbedding.isClosed_range
  have htop : Set.range B.inclusion.hom.hom.left = Set.univ := by
    rw [← Set.univ_subset_iff, ← hdense.closure_eq]
    exact closure_minimal hle hclosed
  haveI : Surjective B.inclusion.hom.hom.left := ⟨Set.range_eq_univ.mp htop⟩
  haveI : IsIso B.inclusion.hom.hom.left :=
    isIso_of_isClosedImmersion_of_surjective B.inclusion.hom.hom.left
  exact isIso_of_schemeIso B.inclusion

/-- In a Borel containing the contracting factors of the positive limit,
the opposite contraction is forced into the intersection of the radicals.
Its triviality identifies the positive limit with that Borel. -/
theorem limit_parabolic_equals_borel_of_two_borels (H : AffineAlgebraicGroup k)
    (hs : Smooth H.val.X.hom) (hc : ConnectedSpace H.val.X.left)
    {T B₁ B₂ R : ClosedSubgroup H.val}
    (hT : IsMaximalTorus T) (hR : IsUnipotentRadical H R) (ht : IsTrivialSubgroup R)
    (hB : IsBorel B₁)
    (hpair : ∀ B : ClosedSubgroup H.val, IsBorel B → IsSubgroupOf T B →
      SameSubgroup B B₁ ∨ SameSubgroup B B₂)
    {c : Cocharacter H.val}
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (hE : IsSubgroupOf E.parabolic B₂) (b : Cocharacter B₁.group)
    (hb : b ≫ B₁.inclusion = c) : IsSubgroupOf B₁ D.parabolic := by
  let A := closedSubgroupAlgebraicGroup B₁
  letI : Smooth A.val.X.hom := hB.1.1
  letI : ConnectedSpace A.val.X.left := hB.1.2.1
  obtain ⟨P⟩ := CocharacterDynamics.existsLimitDecomposition A b
  obtain ⟨V⟩ := CocharacterDynamics.existsLimitDecomposition A (oppositeCocharacter b)
  have hneg : oppositeCocharacter b ≫ B₁.inclusion = oppositeCocharacter c := by
    rw [oppositeCocharacter, oppositeCocharacter, Category.assoc, hb]
  let J := subgroupOfSubgroup B₁ V.contracting
  have hJ₁ : IsSubgroupOf J B₁ := ⟨V.contracting.inclusion, rfl⟩
  have hJ₂ : IsSubgroupOf J B₂ := by
    have Hmap : ∀ L : LimitDecomposition (oppositeCocharacter c),
        ∃ f : V.contracting.group ⟶ L.contracting.group,
          f ≫ L.contracting.inclusion = V.contracting.inclusion ≫ B₁.inclusion := by
      rw [← hneg]
      exact map_limit_contracting A.property.1 B₁.inclusion V
    exact subgroupOf_trans (subgroupOf_trans (Hmap E) ⟨E.contractingToParabolic, E.contracting_in_G⟩) hE
  have hsV : Smooth V.contracting.group.X.hom :=
    (CocharacterDynamics.limitSubgroupsSmooth A (oppositeCocharacter b) V).2.1
  have hcV : ConnectedSpace V.contracting.group.X.left := by
    letI := (CocharacterDynamics.geometricallyConnectedLimitSubgroups A (oppositeCocharacter b) V).2.1
    exact GeometricallyConnected.connectedSpace_of_subsingleton V.contracting.group.X.hom
  have huV : IsUnipotent (closedSubgroupAlgebraicGroup (G := H) J) := by
    obtain ⟨D', e, he⟩ := CocharacterDynamics.contractingSubgroupUnipotent
      A (oppositeCocharacter b) V
    exact ⟨D', e, he⟩
  have htJ : IsTrivialSubgroup J := trivial_of_subgroup_of_trivial
    (unipotent_subgroup_in_borel_pair hs hc hT hR hpair hJ₁ hJ₂ hsV hcV huV) ht
  have htV : Nonempty (V.contracting.group ≅ Grp.trivial (SchemeOver k)) := htJ
  let p := snd V.contracting.group.X (P.centralizer.group.X ⊗ P.contracting.group.X) ≫
    multiplyFactors P.sectionMap P.contractingToParabolic
  have hp : p ≫ P.parabolic.inclusion.hom.hom = bigCellMap P V := by
    have hl : P.sectionMap.hom.hom ≫ P.parabolic.inclusion.hom.hom =
        P.centralizer.inclusion.hom.hom :=
      (Grp.forget (SchemeOver k)).congr_map P.section_in_G
    have hr : P.contractingToParabolic.hom.hom ≫ P.parabolic.inclusion.hom.hom =
        P.contracting.inclusion.hom.hom :=
      (Grp.forget (SchemeOver k)).congr_map P.contracting_in_G
    have htriv := trivial_map_eq_one htV V.contracting.inclusion
      (fst V.contracting.group.X (P.centralizer.group.X ⊗ P.contracting.group.X))
    simp only [p, bigCellMap, multiplyFactors, htriv, one_mul, Category.assoc,
      MonObj.comp_mul, MonObj.mul_comp, hl, hr]
  letI := isIso_subgroup_of_big_cell_factor A P V P.parabolic p hp
  have hP : ∀ L : LimitDecomposition c, ∃ q : P.parabolic.group ⟶ L.parabolic.group,
      q ≫ L.parabolic.inclusion = P.parabolic.inclusion ≫ B₁.inclusion := by
    rw [← hb]
    exact map_limit_parabolic A.property.1 B₁.inclusion P
  obtain ⟨q, hq⟩ := hP D
  refine ⟨inv P.parabolic.inclusion ≫ q, ?_⟩
  rw [Category.assoc, hq, IsIso.inv_hom_id_assoc]


open private limit_parabolic_solvable sections_of_subgroup
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
open private rationalMap rationalSections solvable_iff_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals

/-- Over an algebraically closed field the signed limits with common Levi T
are contained in distinct Borels through T. -/
theorem signed_limits_in_distinct_borels (H : AffineAlgebraicGroup k)
    (hs : Smooth H.val.X.hom) (hc : ConnectedSpace H.val.X.left) (hn : ¬ IsSolvable H.val)
    (T : ClosedSubgroup H.val) (hT : IsMaximalTorus T)
    {c : Cocharacter H.val} (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (hD : SameSubgroup D.centralizer T) (hE : SameSubgroup E.centralizer T) :
    ∃ (B₁ B₂ : ClosedSubgroup H.val), IsBorel B₁ ∧ IsBorel B₂ ∧
      IsSubgroupOf T B₁ ∧ IsSubgroupOf T B₂ ∧ ¬ SameSubgroup B₁ B₂ ∧
      IsSubgroupOf D.parabolic B₁ ∧ IsSubgroupOf E.parabolic B₂ := by
  letI := hs
  letI := hc
  obtain ⟨B, hB, hTB⟩ := LinearAlgebraicGroups.GeometricBorelConjugacy.torusContainedInBorel
    H hs hc T hT.1
  have hl {t : Cocharacter H.val} (F : LimitDecomposition t)
      (hF : SameSubgroup F.centralizer T) :
      IsSmoothConnectedSolvable F.parabolic := by
    apply limit_parabolic_solvable H F hB
    intro g hg
    exact sections_of_subgroup (subgroupOf_trans hF.1 hTB) ((F.centralizer_points _ _).mp hg)
  obtain ⟨B₁, hB₁, hDB⟩ := exists_borel_above H D.parabolic (hl D hD)
  obtain ⟨B₂, hB₂, hEB⟩ := exists_borel_above H E.parabolic (hl E hE)
  have hm {t : Cocharacter H.val} (F : LimitDecomposition t)
      {B' : ClosedSubgroup H.val} (hF : SameSubgroup F.centralizer T)
      (hFB : IsSubgroupOf F.parabolic B') : IsSubgroupOf T B' :=
    subgroupOf_trans hF.2 (subgroupOf_trans ⟨F.sectionMap, F.section_in_G⟩ hFB)
  refine ⟨B₁, B₂, hB₁, hB₂, hm D hD hDB, hm E hE hEB, ?_, hDB, hEB⟩
  intro hsame
  obtain ⟨d, hd⟩ := hDB
  obtain ⟨e, he⟩ := subgroupOf_trans hEB hsame.2
  let U := E.contracting.group.X
  let V := D.centralizer.group.X ⊗ D.contracting.group.X
  let l := E.contractingToParabolic ≫ e
  let i := D.sectionMap ≫ d
  let j := D.contractingToParabolic ≫ d
  let p : U ⊗ V ⟶ B₁.group.X :=
    (fst U V ≫ l.hom.hom) * (snd U V ≫ multiplyFactors i j)
  have hl' : l.hom.hom ≫ B₁.inclusion.hom.hom = E.contracting.inclusion.hom.hom := by
    change ((E.contractingToParabolic ≫ e) ≫ B₁.inclusion).hom.hom = _
    rw [Category.assoc, he, E.contracting_in_G]
  have hi' : i.hom.hom ≫ B₁.inclusion.hom.hom = D.centralizer.inclusion.hom.hom := by
    change ((D.sectionMap ≫ d) ≫ B₁.inclusion).hom.hom = _
    rw [Category.assoc, hd, D.section_in_G]
  have hj' : j.hom.hom ≫ B₁.inclusion.hom.hom = D.contracting.inclusion.hom.hom := by
    change ((D.contractingToParabolic ≫ d) ≫ B₁.inclusion).hom.hom = _
    rw [Category.assoc, hd, D.contracting_in_G]
  have hp : p ≫ B₁.inclusion.hom.hom = bigCellMap D E := by
    dsimp only [p, bigCellMap, multiplyFactors]
    simp only [MonObj.comp_mul, MonObj.mul_comp, Category.assoc, hl', hi', hj', U, V]
  letI : IsIso B₁.inclusion := isIso_subgroup_of_big_cell_factor H D E B₁ p hp
  let f := inv B₁.inclusion
  letI : IsIso f.hom.hom := (Grp.forget (SchemeOver k)).map_isIso f
  letI : Group.IsSolvable (rationalSections B₁.group) :=
    (solvable_iff_sections (closedSubgroupAlgebraicGroup B₁) hB₁.1.1 hB₁.1.2.1).mp hB₁.1.2.2
  apply hn
  apply (solvable_iff_sections H hs hc).mpr
  exact Group.isSolvable_of_isSolvable_injective (f := rationalMap f)
    (fun _ _ h => (cancel_mono f.hom.hom).mp h)

end BorelComparison

section QuotientStabilizers

open Specs.GeometricBorelConjugacy (ConjugatesSubgroups)
open Specs.QuotientEmbedding (Presentation)
open private projection_eq_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.QuotientEmbedding

variable {k : Type u} [Field k] {H : GroupScheme k} {B : ClosedSubgroup H}

private theorem quotient_action_formula (Q : Presentation B) (a : ModObj H.X Q.scheme)
    (ha : (𝟙 H.X ⊗ₘ Q.projection) ≫ a.smul = μ[H.X] ≫ Q.projection)
    {Y : SchemeOver k} (g h : Y ⟶ H.X) :
    lift g (h ≫ Q.projection) ≫ a.smul = (g * h) ≫ Q.projection := by
  have he : lift g h ≫ (𝟙 H.X ⊗ₘ Q.projection) = lift g (h ≫ Q.projection) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [← he, Category.assoc, ha, ← Category.assoc]
  rfl

/-- A translate of the identity coset has scheme stabilizer the conjugate
of the subgroup used in the right quotient. -/
theorem quotient_stabilizer_at_translate (Q : Presentation B) (a : ModObj H.X Q.scheme)
    (ha : (𝟙 H.X ⊗ₘ Q.projection) ≫ a.smul = μ[H.X] ≫ Q.projection)
    (n : 𝟙_ (SchemeOver k) ⟶ H.X) (B' : ClosedSubgroup H) (hn : ConjugatesSubgroups n B B') :
    RepresentsSubgroup B' (fun _ g => Stabilizes a.smul (n ≫ Q.projection) g) := by
  obtain ⟨e, he⟩ := hn
  intro Y g
  let c := toUnit Y ≫ n
  have heval (b : Y ⟶ B.group.X) :
      b ≫ e.hom.hom.hom ≫ B'.inclusion.hom.hom = c * (b ≫ B.inclusion.hom.hom) * c⁻¹ := by
    have h := congrArg (b ≫ ·) he
    simpa only [c, Category.assoc, comp_toUnit_assoc, MonObj.comp_mul, GrpObj.comp_inv,
      Grp.comp_hom_hom] using h
  change lift g (toUnit Y ≫ n ≫ Q.projection) ≫ a.smul = toUnit Y ≫ n ≫ Q.projection ↔ _
  rw [← Category.assoc (toUnit Y) n, quotient_action_formula Q a ha]
  change (g * c) ≫ Q.projection = c ≫ Q.projection ↔ _
  rw [eq_comm, projection_eq_iff Q c (g * c)]
  constructor
  · rintro ⟨b, hb⟩
    change b ≫ B.inclusion.hom.hom = c⁻¹ * (g * c) at hb
    refine ⟨b ≫ e.hom.hom.hom, ?_⟩
    rw [Category.assoc, heval, hb]
    group
  · rintro ⟨b, hb⟩
    let l := b ≫ e.inv.hom.hom
    have he₀ : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ :=
      (Grp.forget (SchemeOver k)).congr_map e.inv_hom_id
    have h := heval l
    have he₁ : l ≫ e.hom.hom.hom = b := by
      dsimp only [l]
      rw [Category.assoc, he₀, Category.comp_id]
    rw [← Category.assoc l, he₁, hb] at h
    refine ⟨l, ?_⟩
    change l ≫ B.inclusion.hom.hom = c⁻¹ * (g * c)
    rw [h]
    group

/-- The opposite-cell map takes the identity section to the identity coset. -/
theorem quotient_cell_identity (U : ClosedSubgroup H) (Q : Presentation B) :
    η[U.group.X] ≫ U.inclusion.hom.hom ≫ Q.projection = η[H.X] ≫ Q.projection :=
  IsMonHom.one_hom_assoc _ _

end QuotientStabilizers

section OrbitOmission

open Specs.SmoothOrbit (orbitMap)
open private orbitMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SmoothOrbit
open private factors_of_range_subset from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SubtorusCentralizer

variable {k : Type u} [Field k] {G : GroupScheme k} {X : SchemeOver k}

/-- An orbit avoids every distinct rational point fixed by the acting group.
This statement concerns the underlying scheme image. -/
theorem orbit_disjoint_fixed_point (a : ModObj G.X X)
    (x y : 𝟙_ (SchemeOver k) ⟶ X) (hne : x ≠ y) (hy : IsClosedImmersion y.left)
    (hfixed : ∀ (Y : SchemeOver k) (g : Y ⟶ G.X), letI := a
      g • (toUnit Y ≫ y) = toUnit Y ≫ y) :
    Disjoint (Set.range (orbitMap a x).left) (Set.range y.left) := by
  rw [Set.disjoint_left]
  rintro _ ⟨u, rfl⟩ ⟨v, hv⟩
  let L := G.X.left.residueField u
  let f := G.X.left.fromSpecResidueField u
  let Y : SchemeOver k := Over.mk (f ≫ G.X.hom)
  let g : Y ⟶ G.X := Over.homMk f rfl
  have hr : Set.range (g ≫ orbitMap a x).left ⊆ Set.range y.left := by
    rintro _ ⟨z, rfl⟩
    refine ⟨v, ?_⟩
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    change y.left v = (orbitMap a x).left (f z)
    rw [Scheme.fromSpecResidueField_apply, hv]
  haveI : IsReduced Y.left := inferInstanceAs (IsReduced (Spec (G.X.left.residueField u)))
  obtain ⟨q, hq⟩ := factors_of_range_subset _ _ hy hr
  have hq' : toUnit Y ≫ y = g ≫ orbitMap a x := by
    rw [← hq]
    exact congrArg (fun p : Y ⟶ 𝟙_ (SchemeOver k) => p ≫ y) (Subsingleton.elim _ _)
  have hf : Flat Y.hom := by
    let φ := Scheme.Spec.preimage Y.hom
    have hφ : Scheme.Spec.map φ = Y.hom := Scheme.Spec.map_preimage _
    have hl : φ.unop.hom.Flat := by
      let : Algebra k L := φ.unop.hom.toAlgebra
      exact Module.Flat.of_free (R := k) (M := L)
    have hfl := (Flat.SpecMap_iff (f := φ.unop)).mpr hl
    exact hφ ▸ hfl
  have hs : Surjective Y.hom := ⟨fun _ => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩
  letI := hf
  letI := hs
  haveI : Epi (toUnit Y).left := Flat.epi_of_flat_of_surjective Y.hom
  haveI : Epi (toUnit Y) := Over.epi_of_epi_left _
  apply hne
  apply (cancel_epi (toUnit Y)).mp
  letI := a
  have hg : g • (toUnit Y ≫ x) = toUnit Y ≫ y := by
    rw [hq']
    exact (orbitMap_comp a x g).symm
  calc
    toUnit Y ≫ x = g⁻¹ • (g • (toUnit Y ≫ x)) := (inv_smul_smul g _).symm
    _ = toUnit Y ≫ y := by rw [hg, hfixed Y g⁻¹]


open Specs.GeometricBorelConjugacy (ConjugatesSubgroups)
open Specs.QuotientEmbedding (Presentation)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open private restrictGroupAction restrictGroupAction_on_points
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SubtorusCentralizer
open private basePoint_closed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.QuotientEmbedding

/-- The opposite orbit omits the normalizer coset whenever its conjugate
Borel contains the acting group and the two marked cosets are distinct. -/
theorem quotient_cell_disjoint_normalizer_coset {B U B' : ClosedSubgroup G}
    (Q : Presentation B) (a : ModObj G.X Q.scheme)
    (ha : (𝟙 G.X ⊗ₘ Q.projection) ≫ a.smul = μ[G.X] ≫ Q.projection)
    (n : 𝟙_ (SchemeOver k) ⟶ G.X) (hn : ConjugatesSubgroups n B B')
    (hu : IsSubgroupOf U B') (hne : η[G.X] ≫ Q.projection ≠ n ≫ Q.projection) :
    Disjoint (Set.range (U.inclusion.hom.hom ≫ Q.projection).left)
      (Set.range (n ≫ Q.projection).left) := by
  let b := restrictGroupAction U.inclusion a
  have he : orbitMap b (η[G.X] ≫ Q.projection) = U.inclusion.hom.hom ≫ Q.projection := by
    change lift (𝟙 U.group.X) (toUnit U.group.X ≫ η[G.X] ≫ Q.projection) ≫ b.smul = _
    rw [restrictGroupAction_on_points, Category.id_comp, ← Category.assoc (toUnit U.group.X),
      quotient_action_formula Q a ha]
    exact congrArg (fun v : U.group.X ⟶ G.X => v ≫ Q.projection) (mul_one _)
  rw [← he]
  apply orbit_disjoint_fixed_point b _ _ hne (basePoint_closed Q.quasiProjective _)
  intro Y g
  change lift g (toUnit Y ≫ n ≫ Q.projection) ≫ b.smul = toUnit Y ≫ n ≫ Q.projection
  rw [restrictGroupAction_on_points]
  apply (quotient_stabilizer_at_translate Q a ha n B' hn _ _).mpr
  obtain ⟨i, hi⟩ := hu
  refine ⟨g ≫ i.hom.hom, ?_⟩
  rw [Category.assoc]
  exact congrArg (fun f : U.group ⟶ G => g ≫ f.hom.hom) hi

end OrbitOmission

section ClassificationOfBorels

open Specs.GeometricBorelConjugacy (IsBorel ConjugatesSubgroups)
open Specs.GeometricRadicals (IsMaximalTorus)
open Specs.QuotientEmbedding (Presentation)
open Specs.NormalizerLatticeAction (IsFixedPoint)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.RankOneFlag (SameSubgroup)
open private projection_eq_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.QuotientEmbedding
open private quotientAction quotientAction_eval
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
open private quotientAct_projection from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper

variable {k : Type u} [Field k] {H : AffineAlgebraicGroup k}

private theorem same_subgroup_of_same_sections {S T : ClosedSubgroup H.val}
    {P : ∀ Y : SchemeOver k, (Y ⟶ H.val.X) → Prop}
    (hS : RepresentsSubgroup S P) (hT : RepresentsSubgroup T P) : SameSubgroup S T := by
  exact ⟨subgroup_inclusion_of_represents hS hT (fun _ _ h => h),
    subgroup_inclusion_of_represents hT hS (fun _ _ h => h)⟩

private theorem conjugates_by_identity (B : ClosedSubgroup H.val) :
    ConjugatesSubgroups η[H.val.X] B B := by
  refine ⟨Iso.refl _, ?_⟩
  change (𝟙 _ ≫ B.inclusion).hom.hom =
    (1 : B.group.X ⟶ H.val.X) * B.inclusion.hom.hom * 1⁻¹
  simp

private theorem quotient_action_equivariant {B : ClosedSubgroup H.val} (Q : Presentation B) :
    (𝟙 H.val.X ⊗ₘ Q.projection) ≫ (quotientAction Q).smul =
      μ[H.val.X] ≫ Q.projection := by
  have h : (𝟙 H.val.X ⊗ₘ Q.projection) =
      lift (fst H.val.X H.val.X) (snd H.val.X H.val.X ≫ Q.projection) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [h, quotientAction_eval, quotientAct_projection]
  simp only [CategoryTheory.Hom.mul_def, lift_fst_snd, Category.id_comp]

private theorem quotient_normalizer_points_of_two_cosets {T B : ClosedSubgroup H.val}
    (hTB : IsSubgroupOf T B) (Q : Presentation B)
    (n g : 𝟙_ (SchemeOver k) ⟶ H.val.X)
    (h : g ∈ SubgroupSections T (𝟙_ (SchemeOver k)) ∨
      n⁻¹ * g ∈ SubgroupSections T (𝟙_ (SchemeOver k))) :
    g ≫ Q.projection = η[H.val.X] ≫ Q.projection ∨ g ≫ Q.projection = n ≫ Q.projection := by
  obtain ⟨j, hj⟩ := hTB
  have hj' : j.hom.hom ≫ B.inclusion.hom.hom = T.inclusion.hom.hom :=
    (Grp.forget (SchemeOver k)).congr_map hj
  rcases h with ⟨t, ht⟩ | ⟨t, ht⟩
  · left
    symm
    apply (projection_eq_iff Q _ _).mpr
    refine ⟨t ≫ j.hom.hom, ?_⟩
    change (t ≫ j.hom.hom) ≫ B.inclusion.hom.hom =
      (η[H.val.X] : 𝟙_ (SchemeOver k) ⟶ H.val.X)⁻¹ * g
    rw [Category.assoc, hj']
    change t ≫ T.inclusion.hom.hom = _ at ht
    have he : η[H.val.X] = (1 : 𝟙_ (SchemeOver k) ⟶ H.val.X) := by
      rw [CategoryTheory.Hom.one_def,
        show toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ from Subsingleton.elim _ _, Category.id_comp]
    rw [he, inv_one, one_mul, ht]
  · right
    symm
    apply (projection_eq_iff Q _ _).mpr
    refine ⟨t ≫ j.hom.hom, ?_⟩
    change (t ≫ j.hom.hom) ≫ B.inclusion.hom.hom = n⁻¹ * g
    rw [Category.assoc, hj']
    exact ht

variable [IsAlgClosed k]

/-- If the normalizer acts through two cosets and two distinct Borels through the
torus exist, these exhaust the Borels through that torus. -/
theorem borels_through_torus_of_two_normalizer_cosets
    (hs : Smooth H.val.X.hom) (hc : ConnectedSpace H.val.X.left)
    {T B₁ B₂ : ClosedSubgroup H.val} (hT : IsMaximalTorus T)
    (hB₁ : IsBorel B₁) (hB₂ : IsBorel B₂)
    (h₁ : IsSubgroupOf T B₁) (h₂ : IsSubgroupOf T B₂)
    (hne : ¬ SameSubgroup B₁ B₂)
    (Q : Presentation B₁) (n : 𝟙_ (SchemeOver k) ⟶ H.val.X)
    (hcosets : ∀ g : 𝟙_ (SchemeOver k) ⟶ H.val.X, Normalizes T.inclusion g →
      g ∈ SubgroupSections T (𝟙_ (SchemeOver k)) ∨
        n⁻¹ * g ∈ SubgroupSections T (𝟙_ (SchemeOver k))) :
    n ≫ Q.projection ≠ η[H.val.X] ≫ Q.projection ∧
      ∀ B : ClosedSubgroup H.val, IsBorel B → IsSubgroupOf T B →
        SameSubgroup B B₁ ∨ SameSubgroup B B₂ := by
  let x := η[H.val.X] ≫ Q.projection
  let y := n ≫ Q.projection
  let a := quotientAction Q
  have ha := quotient_action_equivariant Q
  have hx := quotient_stabilizer_at_translate Q a ha _ B₁ (conjugates_by_identity B₁)
  have hpair (B : ClosedSubgroup H.val) (hB : IsBorel B) (hTB : IsSubgroupOf T B) :
      RepresentsSubgroup B (fun _ g => Stabilizes a.smul x g) ∨
        RepresentsSubgroup B (fun _ g => Stabilizes a.smul y g) := by
    obtain ⟨g, hg, hgB⟩ := MaximalToriConjugate.normalizerTransitiveOnBorels H hs hc T hT
      B₁ B hB₁ hB h₁ hTB
    have hrepr := quotient_stabilizer_at_translate Q a ha g B hgB
    rcases quotient_normalizer_points_of_two_cosets h₁ Q n g (hcosets g hg) with h | h
    · have h' : g ≫ Q.projection = x := h
      rw [h'] at hrepr
      exact Or.inl hrepr
    · have h' : g ≫ Q.projection = y := h
      rw [h'] at hrepr
      exact Or.inr hrepr
  have hy : RepresentsSubgroup B₂ (fun _ g => Stabilizes a.smul y g) :=
    (hpair B₂ hB₂ h₂).resolve_left fun h => hne (same_subgroup_of_same_sections hx h)
  refine ⟨fun h => hne (same_subgroup_of_same_sections hx (h ▸ hy)), ?_⟩
  intro B hB hTB
  exact (hpair B hB hTB).imp (fun h => same_subgroup_of_same_sections h hx)
    (fun h => same_subgroup_of_same_sections h hy)


/-- In a geometric Borel quotient the two specified normalizer cosets
give all torus-fixed rational points whenever those cosets exhaust the normalizer. -/
theorem quotient_fixed_points_of_two_normalizer_cosets
    (hs : Smooth H.val.X.hom) (hc : ConnectedSpace H.val.X.left)
    {T B N : ClosedSubgroup H.val} (hT : IsMaximalTorus T)
    (hB : IsBorel B) (hTB : IsSubgroupOf T B)
    (hN : RepresentsSubgroup N (fun _ g => Normalizes T.inclusion g))
    (Q : Presentation B) (n : 𝟙_ (SchemeOver k) ⟶ H.val.X) (hn : Normalizes T.inclusion n)
    (hcst : ∀ g : 𝟙_ (SchemeOver k) ⟶ H.val.X, Normalizes T.inclusion g →
      g ∈ SubgroupSections T (𝟙_ (SchemeOver k)) ∨
        n⁻¹ * g ∈ SubgroupSections T (𝟙_ (SchemeOver k))) :
    ∃ a : ModObj H.val.X Q.scheme,
      (𝟙 H.val.X ⊗ₘ Q.projection) ≫ a.smul = μ[H.val.X] ≫ Q.projection ∧
        ∀ x : 𝟙_ (SchemeOver k) ⟶ Q.scheme,
          IsFixedPoint a T x ↔ x = η[H.val.X] ≫ Q.projection ∨ x = n ≫ Q.projection := by
  obtain ⟨a, ha, _, hf, _, _⟩ :=
    LinearAlgebraicGroups.NormalizerLatticeAction.borelQuotientFixedPoints H hs hc
      T B hT hB hTB N hN Q
  have h : (𝟙 H.val.X ⊗ₘ Q.projection) =
      lift (fst H.val.X H.val.X) (snd H.val.X H.val.X ≫ Q.projection) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  refine ⟨a, h ▸ ha, fun x => ?_⟩
  rw [hf]
  constructor
  · rintro ⟨g, rfl⟩
    let g' := g ≫ N.inclusion.hom.hom
    exact quotient_normalizer_points_of_two_cosets hTB Q n g'
      (hcst g' ((hN _ _).mpr ⟨g, rfl⟩))
  · rintro (rfl | rfl)
    · refine ⟨η[N.group.X], IsMonHom.one_hom_assoc _ _⟩
    · obtain ⟨m, hm⟩ := (hN _ _).mp hn
      exact ⟨m, by rw [← Category.assoc, hm]⟩

end ClassificationOfBorels

section PositiveGrading

open Polynomial

variable {k A : Type u} [Field k] [CommRing A] [IsDomain A] [Algebra k A]

/-- A homogeneous generator modulo the square of the augmentation ideal
generates a positively graded algebra. The polynomial coaction encodes the grading. -/
theorem aeval_surjective_of_positive_grading (ε : A →ₐ[k] k) (D : A →ₐ[k] Polynomial A)
    (heval : ∀ a, (D a).eval 1 = a)
    (hcoeff : ∀ a n, D ((D a).coeff n) = monomial n ((D a).coeff n))
    (hzero : ∀ a, (D a).coeff 0 = algebraMap k A (ε a))
    {x : A} {d : ℕ} (hx : D x = monomial d x)
    (hspan : ∀ a : A, ε a = 0 →
      ∃ c : k, a - algebraMap k A c * x ∈ (RingHom.ker ε.toRingHom) ^ 2) :
    Function.Surjective (aeval x : Polynomial k →ₐ[k] A) := by
  classical
  let I := RingHom.ker ε.toRingHom
  let S := (aeval x : Polynomial k →ₐ[k] A).range
  have hxS : x ∈ S := ⟨X, aeval_X x⟩
  have haug (a : A) {n : ℕ} (hn : 0 < n) : ε ((D a).coeff n) = 0 := by
    have e := congrArg (fun p : Polynomial A => p.coeff 0) (hcoeff a n)
    rw [hzero, coeff_monomial, ite_eq_right hn.ne'] at e
    exact (algebraMap k A).injective (e.trans (map_zero _).symm)
  have hdeg (n : ℕ) (a : A) : (D a).coeff n ∈ S := by
    induction n using Nat.strong_induction_on generalizing a with
    | h n ih =>
      by_cases hn : n = 0
      · rw [hn, hzero]
        exact S.algebraMap_mem _
      have hn' : 0 < n := Nat.pos_of_ne_zero hn
      have hsq (b : A) (hb : b ∈ I ^ 2) : (D b).coeff n ∈ S := by
        rw [pow_two] at hb
        refine Submodule.mul_induction_on (M := I) (N := I) hb ?_ ?_
        · intro v hv w hw
          rw [map_mul, coeff_mul]
          apply S.sum_mem
          rintro ⟨i, j⟩ hij
          have hij' := Finset.mem_antidiagonal.mp hij
          by_cases hi : i = 0
          · have h : ε v = 0 := hv
            simp [hi, hzero, h, S.zero_mem]
          by_cases hj : j = 0
          · have h : ε w = 0 := hw
            simp [hj, hzero, h, S.zero_mem]
          exact S.mul_mem (ih _ (by omega) v) (ih _ (by omega) w)
        · intro v w hv hw
          rw [map_add, coeff_add]
          exact S.add_mem hv hw
      let b := (D a).coeff n
      obtain ⟨c, hc⟩ := hspan b (haug a hn')
      have heq : (D b).coeff n = b := by
        rw [hcoeff a n, coeff_monomial, ite_eq_left rfl]
      have hcx : (D (algebraMap k A c * x)).coeff n ∈ S := by
        rw [map_mul, D.commutes, hx, Polynomial.algebraMap_apply, C_mul_monomial, coeff_monomial]
        split
        · exact S.mul_mem (S.algebraMap_mem c) hxS
        · exact S.zero_mem
      have hs := hsq _ hc
      rw [map_sub, coeff_sub, heq] at hs
      have hsum := S.add_mem hs hcx
      rwa [sub_add_cancel] at hsum
  intro a
  have ha : a ∈ S := by
    rw [← heval a, eval_eq_sum_range]
    simp only [one_pow, mul_one]
    exact S.sum_mem fun n _ => hdeg n a
  exact ha

/-- A nonzero homogeneous coordinate of positive weight is transcendental
in a domain. -/
theorem aeval_injective_of_positive_weight (D : A →ₐ[k] Polynomial A)
    {x : A} {d : ℕ} (hx : D x = monomial d x) (hx₀ : x ≠ 0) (hd : 0 < d) :
    Function.Injective (aeval x : Polynomial k →ₐ[k] A) := by
  apply (injective_iff_map_eq_zero (aeval x : Polynomial k →ₐ[k] A)).mpr
  intro p hp
  have hD : D.comp (aeval x) = aeval (monomial d x) := by
    apply algHom_ext
    simpa only [AlgHom.comp_apply, aeval_X] using hx
  have hmap : D ((aeval x : Polynomial k →ₐ[k] A) p) =
      (p.map (algebraMap k A)).comp (monomial d x) := by
    rw [← AlgHom.comp_apply, hD, comp_eq_aeval]
    simp only [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq]
  rw [hp, map_zero] at hmap
  have hmapzero := (comp_eq_zero_iff.mp hmap.symm).resolve_right (by
    rintro ⟨_, hc⟩
    have hn := congrArg natDegree hc
    exact hd.ne' (by simpa only [natDegree_monomial_eq d hx₀, natDegree_C] using hn))
  exact (Polynomial.map_injective _ (algebraMap k A).injective)
    (hmapzero.trans (Polynomial.map_zero _).symm)

/-- A positive grading and a one-dimensional cotangent space give a single
homogeneous polynomial coordinate over the original coefficient field. -/
theorem exists_positive_polynomial_coordinate (ε : A →ₐ[k] k) (D : A →ₐ[k] Polynomial A)
    (heval : ∀ a, (D a).eval 1 = a)
    (hcoeff : ∀ a n, D ((D a).coeff n) = monomial n ((D a).coeff n))
    (hzero : ∀ a, (D a).coeff 0 = algebraMap k A (ε a))
    (hdim : Module.finrank k (RingHom.ker ε.toRingHom).Cotangent = 1) :
    ∃ (x : A) (d : ℕ), 0 < d ∧ ε x = 0 ∧ D x = monomial d x ∧
      Function.Bijective (aeval x : Polynomial k →ₐ[k] A) := by
  classical
  let I := RingHom.ker ε.toRingHom
  have hnz : ∃ v : I.Cotangent, v ≠ 0 := by
    by_contra! h
    letI : Subsingleton I.Cotangent := ⟨fun v w => (h v).trans (h w).symm⟩
    have h' : Module.finrank k I.Cotangent = 0 := Module.finrank_zero_of_subsingleton
    have h₁ : Module.finrank k I.Cotangent = 1 := hdim
    omega
  obtain ⟨v, hv⟩ := hnz
  obtain ⟨a, rfl⟩ := I.toCotangent_surjective v
  have hchoose : ∃ d, (D a.val).coeff d ∉ I ^ 2 := by
    by_contra! h
    apply hv
    apply (I.toCotangent_eq_zero a).mpr
    rw [← heval a.val, eval_eq_sum_range]
    simp only [one_pow, mul_one]
    exact (I ^ 2).sum_mem fun d _ => h d
  obtain ⟨d, hd⟩ := hchoose
  have hpos : 0 < d := by
    apply Nat.pos_of_ne_zero
    rintro rfl
    have ha : ε a.val = 0 := a.property
    exact hd (by simp only [hzero, ha, map_zero, Ideal.zero_mem])
  let x := (D a.val).coeff d
  have hx : D x = monomial d x := hcoeff _ _
  have hεx : ε x = 0 := by
    have e := congrArg (fun p : Polynomial A => p.coeff 0) hx
    rw [hzero, coeff_monomial, ite_eq_right hpos.ne'] at e
    exact (algebraMap k A).injective (e.trans (map_zero _).symm)
  have hx₀ : x ≠ 0 := by
    intro h
    apply hd
    change x ∈ I ^ 2
    rw [h]
    exact (I ^ 2).zero_mem
  let y : I := ⟨x, hεx⟩
  have hy : I.toCotangent y ≠ 0 := fun h => hd ((I.toCotangent_eq_zero y).mp h)
  have hspan (b : A) (hb : ε b = 0) :
      ∃ c : k, b - algebraMap k A c * x ∈ I ^ 2 := by
    let z : I := ⟨b, hb⟩
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (K := k) (I.toCotangent y) hy).mp hdim
      (I.toCotangent z)
    have hs : I.toCotangent (c • y) = I.toCotangent z :=
      ((I.toCotangent.restrictScalars k).map_smul c y).trans hc
    have he : (c • y : I).val = algebraMap k A c * x := by
      rw [← Algebra.smul_def]
      rfl
    refine ⟨c, ?_⟩
    have hm := (I.toCotangent_eq (x := z) (y := c • y)).mp hs.symm
    rwa [he] at hm
  exact ⟨x, d, hpos, hεx, hx, aeval_injective_of_positive_weight D hx hx₀ hpos,
    aeval_surjective_of_positive_grading ε D heval hcoeff hzero hx hspan⟩

end PositiveGrading

section PolynomialTranslation

open Polynomial

variable {k : Type u} [Field k]

/-- A group law on a polynomial line over a field is the additive law once
the coordinate vanishes at its identity. Over the universal first coordinate,
translation is an automorphism over the polynomial ring. -/
theorem polynomial_addition_of_translation (F I : Polynomial (Polynomial k))
    (hinv : F.comp I = X)
    (hleft : F.map (evalRingHom (0 : k)) = X)
    (hright : F.eval 0 = X) :
    F = C (X : Polynomial k) + X := by
  have hdeg := congrArg natDegree hinv
  rw [natDegree_comp, natDegree_X] at hdeg
  have hF : F.natDegree = 1 := Nat.dvd_one.mp ⟨I.natDegree, hdeg.symm⟩
  have hI : I.natDegree = 1 := Nat.dvd_one.mp ⟨F.natDegree, hdeg.symm.trans (Nat.mul_comm _ _)⟩
  have hlc := congrArg leadingCoeff hinv
  rw [leadingCoeff_comp (by rw [hI]; exact Nat.one_ne_zero), leadingCoeff_X, hF, pow_one] at hlc
  have hu : IsUnit (F.coeff 1) := by
    rw [← hF, coeff_natDegree]
    exact IsUnit.of_mul_eq_one _ hlc
  obtain ⟨c, _, hc⟩ := Polynomial.isUnit_iff.mp hu
  have hl := congrArg (fun p : Polynomial k => p.coeff 1) hleft
  rw [coeff_map, coeff_X_one, ← hc] at hl
  change (C c).eval (0 : k) = 1 at hl
  rw [eval_C] at hl
  have h1 : F.coeff 1 = 1 := by rw [← hc, hl, C_1]
  have h0 : F.coeff 0 = X := (coeff_zero_eq_eval_zero F).trans hright
  ext n
  rcases n with _ | _ | n
  · simp [h0]
  · simp [h1]
  · have hn : F.natDegree < n + 2 := by rw [hF]; omega
    simp [coeff_eq_zero_of_natDegree_lt hn, coeff_X]

end PolynomialTranslation

section ProjectiveLineCharts

open Polynomial LaurentPolynomial

private theorem toLaurent_coeff_neg {R : Type*} [Semiring R] (p : Polynomial R)
    {n : ℤ} (hn : n < 0) : p.toLaurent.coeff n = 0 := by
  apply Finsupp.notMem_support_iff.mp
  rw [support_coeff_toLaurent]
  intro h
  obtain ⟨i, _, hi⟩ := Finset.mem_map.mp h
  change (i : ℤ) = n at hi
  rw [← hi] at hn
  exact (not_lt_of_ge (Int.natCast_nonneg i)) hn

/-- The common elements of the two polynomial subrings of a Laurent polynomial ring
are the constants. Coefficient rings with nilpotents are allowed. -/
theorem polynomial_eq_constant_of_toLaurent_eq_invert {R : Type*} [CommSemiring R]
    {p q : Polynomial R} (h : p.toLaurent = invert q.toLaurent) :
    p = Polynomial.C (p.toLaurent.coeff 0) := by
  apply Polynomial.toLaurent_injective
  rw [Polynomial.toLaurent_C]
  ext n
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · rw [toLaurent_coeff_neg p hn, LaurentPolynomial.C_apply, ite_eq_right hn.ne]
  · rw [LaurentPolynomial.C_apply, ite_eq_left rfl]
  · rw [h, invert_apply, toLaurent_coeff_neg q (neg_neg_of_pos hn),
      LaurentPolynomial.C_apply, ite_eq_right hn.ne']

/-- The two unit factors of an automorphism preserving the zero sections are
trivial when they agree on the overlap and fix the unit section. -/
theorem polynomial_chart_units_eq_one {R : Type*} [CommRing R]
    (u v : (Polynomial R)ˣ)
    (h : (u : Polynomial R).toLaurent * invert (v : Polynomial R).toLaurent = 1)
    (h₁ : (u : Polynomial R).eval 1 = 1) : u = 1 ∧ v = 1 := by
  have hu : (↑u⁻¹ : Polynomial R).toLaurent * (u : Polynomial R).toLaurent = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have huv : (↑u⁻¹ : Polynomial R).toLaurent = invert (v : Polynomial R).toLaurent := by
    calc
      _ = (↑u⁻¹ : Polynomial R).toLaurent *
            ((u : Polynomial R).toLaurent * invert (v : Polynomial R).toLaurent) := by rw [h, mul_one]
      _ = _ := by rw [← mul_assoc, hu, one_mul]
  obtain hconst := polynomial_eq_constant_of_toLaurent_eq_invert huv
  have hprod : (↑u⁻¹ : Polynomial R) * (u : Polynomial R) = 1 := Units.inv_mul u
  have hvalue := congrArg (Polynomial.eval 1) hprod
  rw [eval_mul, eval_one, h₁, mul_one, hconst, eval_C] at hvalue
  have hui : (↑u⁻¹ : Polynomial R) = 1 := hconst.trans (by rw [hvalue, map_one])
  have hu' : u = 1 := by
    apply Units.ext
    simpa [hui] using hprod
  refine ⟨hu', Units.ext ?_⟩
  apply Polynomial.toLaurent_injective
  apply invert.injective
  simpa [hu'] using h

/-- An algebra automorphism preserving the zero section, in both directions,
takes the affine-line coordinate to a unit multiple of itself. -/
theorem polynomial_coordinate_eq_mul_unit {R : Type*} [CommRing R]
    (f : Polynomial R ≃ₐ[R] Polynomial R)
    (h : (f Polynomial.X).eval 0 = 0) (hi : (f.symm Polynomial.X).eval 0 = 0) :
    ∃ u : (Polynomial R)ˣ, f Polynomial.X = Polynomial.X * (u : Polynomial R) := by
  obtain ⟨p, hp⟩ := Polynomial.X_dvd_iff.mpr (by simpa only [Polynomial.coeff_zero_eq_eval_zero] using h)
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr (by simpa only [Polynomial.coeff_zero_eq_eval_zero] using hi)
  have hfactor : (Polynomial.X : Polynomial R) * (p * f q) = Polynomial.X * 1 := by
    have he := congrArg f hq
    rw [AlgEquiv.apply_symm_apply, map_mul, hp, mul_assoc] at he
    simpa only [mul_one] using he.symm
  have hunit : p * f q = 1 := Polynomial.isRegular_X.left hfactor
  exact ⟨Units.mkOfMulEqOne p (f q) hunit, hp⟩

/-- The affine chart automorphisms of the projective line are determined by
the two zero sections and the common unit section. -/
theorem polynomial_charts_eq_refl {R : Type*} [CommRing R]
    (f g : Polynomial R ≃ₐ[R] Polynomial R)
    (hf : (f Polynomial.X).eval 0 = 0) (hfi : (f.symm Polynomial.X).eval 0 = 0)
    (hg : (g Polynomial.X).eval 0 = 0) (hgi : (g.symm Polynomial.X).eval 0 = 0)
    (hone : (f Polynomial.X).eval 1 = 1)
    (hoverlap : (f Polynomial.X).toLaurent * invert (g Polynomial.X).toLaurent = 1) :
    f = AlgEquiv.refl ∧ g = AlgEquiv.refl := by
  obtain ⟨u, hu⟩ := polynomial_coordinate_eq_mul_unit f hf hfi
  obtain ⟨v, hv⟩ := polynomial_coordinate_eq_mul_unit g hg hgi
  have hT : (T 1 : LaurentPolynomial R) * T (-1) = 1 := by rw [← T_add]; simp
  have h : (u : Polynomial R).toLaurent * invert (v : Polynomial R).toLaurent = 1 := by
    rw [hu, hv, map_mul, map_mul, map_mul, Polynomial.toLaurent_X, invert_T] at hoverlap
    calc
      _ = (T 1 * T (-1)) * ((u : Polynomial R).toLaurent *
          invert (v : Polynomial R).toLaurent) := by rw [hT, one_mul]
      _ = _ := by
        rw [← hoverlap]
        ac_rfl
  have hu₁ : (u : Polynomial R).eval 1 = 1 := by
    rwa [hu, eval_mul, eval_X, one_mul] at hone
  obtain ⟨hu', hv'⟩ := polynomial_chart_units_eq_one u v h hu₁
  refine ⟨?_, ?_⟩
  · apply AlgEquiv.coe_toAlgHom_injective
    apply Polynomial.algHom_ext
    simpa [hu'] using hu
  · apply AlgEquiv.coe_toAlgHom_injective
    apply Polynomial.algHom_ext
    simpa [hv'] using hv

end ProjectiveLineCharts

section AffineLifting

open private affinePresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.ProjectiveSpaces

variable {k : Type u} [Field k]

/-- A point lifts along an affine fppf morphism after an fppf extension of the test algebra. -/
theorem exists_fppf_lift_of_affine_fppf {X Y : SchemeOver k} (q : X ⟶ Y)
    (haff : IsAffineHom q.left) (hq : Fppf.IsFppf q.left)
    {R : TestAlgebra k} (g : Points Y R) :
    ∃ (S : TestAlgebra k) (a : R ⟶ S) (m : Points X S),
      Fppf.IsFppf ((testSpec k).map a.op).left ∧ m ≫ q = mapPoints a g := by
  let Z := (testSpec k).obj (op R)
  let A := Over.mk (pullback.snd q.left g.left ≫ Z.hom)
  let p : A ⟶ Z := Over.homMk (pullback.snd q.left g.left) rfl
  let t : A ⟶ X := Over.homMk (pullback.fst q.left g.left) (by
    change pullback.fst q.left g.left ≫ X.hom = pullback.snd q.left g.left ≫ Z.hom
    rw [← Over.w q, ← Over.w g, ← Category.assoc, ← Category.assoc, pullback.condition])
  have hp : Fppf.IsFppf p.left := ⟨MorphismProperty.pullback_snd _ _ hq.1,
    MorphismProperty.pullback_snd _ _ hq.2.1, MorphismProperty.pullback_snd _ _ hq.2.2⟩
  letI : IsAffine Z.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  letI : IsAffineHom p.left := MorphismProperty.pullback_snd _ _ haff
  letI : IsAffine A.left := isAffine_of_isAffineHom p.left
  let c := affinePresentation A
  let e := c.2
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let a : R ⟶ c.1 := (ff.preimage (e.hom ≫ p)).unop
  have ha : (testSpec k).map a.op = e.hom ≫ p := ff.map_preimage _
  refine ⟨c.1, a, e.hom ≫ t, ?_, ?_⟩
  · haveI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
    rw [ha, Over.comp_left]
    letI := hp.1
    letI := hp.2.1
    letI := hp.2.2
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · rw [mapPoints, ha, Category.assoc, Category.assoc]
    congr 1
    apply Over.OverMorphism.ext
    exact pullback.condition

end AffineLifting

section TestSchemeActions

variable {k : Type u} [Field k] {G : GroupScheme k} {X : SchemeOver k}

/-- The product with the affine test scheme, viewed over that scheme. -/
abbrev overTest (X : SchemeOver k) (R : TestAlgebra k) : Over ((testSpec k).obj (op R)) :=
  Over.mk (snd X ((testSpec k).obj (op R)))

private def testActionHom (a : ModObj G.X X) {R : TestAlgebra k} (g : Points G.X R) :
    overTest X R ⟶ overTest X R :=
  letI := a
  let Z := (testSpec k).obj (op R)
  let p := fst X Z
  let q := snd X Z
  Over.homMk (lift ((q ≫ g) • p) q) (lift_snd _ _)

private theorem testActionHom_one (a : ModObj G.X X) (R : TestAlgebra k) :
    testActionHom a (1 : Points G.X R) = 𝟙 _ := by
  letI := a
  let Z := (testSpec k).obj (op R)
  let p := fst X Z
  let q := snd X Z
  apply Over.OverMorphism.ext
  change lift ((q ≫ (1 : Points G.X R)) • p) q = 𝟙 _
  rw [MonObj.comp_one, one_smul]
  exact lift_fst_snd

private theorem testActionHom_mul (a : ModObj G.X X) {R : TestAlgebra k} (g h : Points G.X R) :
    testActionHom a h ≫ testActionHom a g = testActionHom a (g * h) := by
  letI := a
  let Z := (testSpec k).obj (op R)
  let p := fst X Z
  let q := snd X Z
  apply Over.OverMorphism.ext
  change lift ((q ≫ h) • p) q ≫ lift ((q ≫ g) • p) q = lift ((q ≫ (g * h)) • p) q
  dsimp only [p, q]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst, ModObj.comp_smul, lift_snd_assoc,
      MonObj.comp_mul, mul_smul]
  · simp only [Category.assoc, lift_snd]

/-- A left action gives a homomorphism into the automorphism group over each test scheme. -/
def automorphismsOfAction (a : ModObj G.X X) (R : TestAlgebra k) :
    ((groupPointsFunctor k).obj G).obj R →* Aut (overTest X R) where
  toFun g := Aut.of ⟨testActionHom a g, testActionHom a g⁻¹,
    (testActionHom_mul a g⁻¹ g).trans (by rw [inv_mul_cancel, testActionHom_one]),
    (testActionHom_mul a g g⁻¹).trans (by rw [mul_inv_cancel, testActionHom_one])⟩
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    exact testActionHom_one a R
  map_mul' g h := by
    apply Aut.ext
    apply Iso.ext
    exact (testActionHom_mul a g h).symm

theorem automorphismsOfAction_fst (a : ModObj G.X X) {R : TestAlgebra k} (g : Points G.X R) :
    (automorphismsOfAction a R g).asIso.hom.left ≫ fst _ _ =
      lift (snd _ _ ≫ g) (fst _ _) ≫ a.smul := by
  letI := a
  let Z := (testSpec k).obj (op R)
  change lift ((snd X Z ≫ g) • fst X Z) (snd X Z) ≫ fst X Z = _
  rw [lift_fst]
  rfl

private def overTestMap (X : SchemeOver k) {R S : TestAlgebra k} (b : R ⟶ S) :
    (overTest X S).left ⟶ (overTest X R).left :=
  lift (fst _ _) (snd _ _ ≫ (testSpec k).map b.op)

theorem automorphismsOfAction_natural (a : ModObj G.X X) {R S : TestAlgebra k} (b : R ⟶ S)
    (g : Points G.X R) :
    (automorphismsOfAction a S (mapPoints b g)).asIso.hom.left ≫ overTestMap X b =
      overTestMap X b ≫ (automorphismsOfAction a R g).asIso.hom.left := by
  letI := a
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, overTestMap, lift_fst, automorphismsOfAction_fst,
      Category.assoc, automorphismsOfAction_fst, comp_lift_assoc, lift_snd_assoc, lift_fst]
    rfl
  · have hS := Over.w (automorphismsOfAction a S (mapPoints b g)).asIso.hom
    have hR := Over.w (automorphismsOfAction a R g).asIso.hom
    change (automorphismsOfAction a S (mapPoints b g)).asIso.hom.left ≫ snd X _ = snd X _ at hS
    change (automorphismsOfAction a R g).asIso.hom.left ≫ snd X _ = snd X _ at hR
    simp only [Category.assoc, overTestMap, lift_snd, hR, reassoc_of% hS]


end TestSchemeActions

section HomogeneousCoordinates

open Specs.RankOneFlag (Index plane planeBasis projectiveLine HasCoordinates)
open Specs.ProjectiveSpaces (AffineLine changeLineSubmodule chartRing coordinateRatio BasisPointFormula)
open private affinePointEquiv projectiveBasis point_has_principal_chart_cover chartPoint
  awayHom principalOpenCover ratio_self extendVector extendVector_coord lineOfSplitInjection affineLine_ext
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.ProjectiveSpaces

variable {k : Type u} [Field k]

private abbrev planeRepresentation (k : Type u) [Field k] :=
  ProjectiveSpaces.lineRepresentation k (plane k)

private abbrev planeLine {R : TestAlgebra k} (p : Points (projectiveLine k) R) :
    AffineLine k (plane k) R :=
  ((planeRepresentation k).points _ p).line R (𝟙 _)

private abbrev vectorOfCoordinates (R : TestAlgebra k) (v : Index.{u} → R) :
    R ⊗[k] plane k :=
  ((planeBasis k).baseChange R).equivFun.symm v

private theorem planeLine_change {R S : TestAlgebra k} (a : R ⟶ S)
    (p : Points (projectiveLine k) R) :
    (planeLine (mapPoints a p)).submodule = changeLineSubmodule k (plane k) a (planeLine p).submodule := by
  rw [← ((planeRepresentation k).points _ p).compatible a (𝟙 _)]
  change (((planeRepresentation k).points _ ((testSpec k).map a.op ≫ p)).line S (𝟙 _)).submodule = _
  rw [(planeRepresentation k).naturality]
  simp only [ProjectiveSpaces.LineFamily.pullback, mapPoints, Category.id_comp, Category.comp_id]

private theorem planeLine_ext {R : TestAlgebra k} {p q : Points (projectiveLine k) R}
    (h : (planeLine p).submodule = (planeLine q).submodule) : p = q := by
  change (affinePointEquiv (projectiveBasis k (plane k)) R (𝟙 _ ≫ p)).submodule =
    (affinePointEquiv (projectiveBasis k (plane k)) R (𝟙 _ ≫ q)).submodule at h
  simp only [Category.id_comp] at h
  exact (affinePointEquiv (projectiveBasis k (plane k)) R).injective
    (by apply affineLine_ext; exact h)

private def pointOfPlaneLine {R : TestAlgebra k} (L : AffineLine k (plane k) R) :
    Points (projectiveLine k) R :=
  (affinePointEquiv (projectiveBasis k (plane k)) R).symm L

private theorem planeLine_pointOfPlaneLine {R : TestAlgebra k} (L : AffineLine k (plane k) R) :
    planeLine (pointOfPlaneLine L) = L := by
  change affinePointEquiv (projectiveBasis k (plane k)) R (𝟙 _ ≫ pointOfPlaneLine L) = L
  rw [Category.id_comp]
  exact Equiv.apply_symm_apply _ _

private theorem vectorOfCoordinates_change {R S : TestAlgebra k} (a : R ⟶ S)
    (v : Index.{u} → R) :
    extendVector a (vectorOfCoordinates (k := k) R v) =
      vectorOfCoordinates (k := k) S (fun i => a.hom (v i)) := by
  let b := planeBasis k
  apply (b.baseChange S).ext_elem
  intro i
  change (b.baseChange S).coord i (extendVector a (vectorOfCoordinates R v)) =
    (b.baseChange S).coord i (vectorOfCoordinates S (fun j => a.hom (v j)))
  rw [extendVector_coord]
  change a.hom (((b.baseChange R).equivFun ((b.baseChange R).equivFun.symm v)) i) =
    ((b.baseChange S).equivFun ((b.baseChange S).equivFun.symm (fun j => a.hom (v j)))) i
  simp only [LinearEquiv.apply_symm_apply]

private theorem hasCoordinates_change {R S : TestAlgebra k} (a : R ⟶ S)
    {p : Points (projectiveLine k) R} {v : Index.{u} → R}
    (h : HasCoordinates (planeRepresentation k) R p v) :
    HasCoordinates (planeRepresentation k) S (mapPoints a p) (fun i => a.hom (v i)) := by
  change (planeLine p).submodule = Submodule.span R {vectorOfCoordinates R v} at h
  change (planeLine (mapPoints a p)).submodule = Submodule.span S {vectorOfCoordinates S _}
  rw [planeLine_change, h, ProjectiveSpaces.changeLineSubmodule_span, Set.image_singleton,
    vectorOfCoordinates_change]

private def coordinatesLine (R : TestAlgebra k) (v c : Index.{u} → R)
    (h : ∑ i, c i * v i = 1) : AffineLine k (plane k) R := by
  let f := LinearMap.toSpanSingleton R (R ⊗[k] plane k) (vectorOfCoordinates R v)
  let r := ∑ i, c i • ((planeBasis k).baseChange R).coord i
  have he : r (vectorOfCoordinates R v) = 1 := by
    change (∑ i, c i • ((planeBasis k).baseChange R).coord i) (vectorOfCoordinates R v) = 1
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      show ∀ i, ((planeBasis k).baseChange R).coord i (vectorOfCoordinates R v) = v i from
        fun i => congrFun (LinearEquiv.apply_symm_apply ((planeBasis k).baseChange R).equivFun v) i]
      using h
  exact lineOfSplitInjection f r (LinearMap.ext fun a => by
    change r (a • vectorOfCoordinates R v) = a
    rw [map_smul, he, smul_eq_mul, mul_one])
    (fun p => by let := p.nontrivial
                 rw [Module.rankAtStalk_self]
                 rfl)

private theorem coordinatesLine_submodule (R : TestAlgebra k) (v c : Index.{u} → R)
    (h : ∑ i, c i * v i = 1) :
    (coordinatesLine R v c h).submodule = Submodule.span R {vectorOfCoordinates R v} :=
  LinearMap.range_toSpanSingleton _

/-- A single affine fppf cover combines a finite principal open cover by taking the
product of the localized algebras. -/
private theorem principalCover_fppf {R : TestAlgebra k} {J : Type u} [Fintype J]
    (r : J → R) (hr : Ideal.span (Set.range r) = ⊤) :
    let S := CommAlgCat.of k (∀ j, Localization.Away (r j))
    let a : R ⟶ S := CommAlgCat.ofHom (AlgHom.pi fun j => (awayHom (k := k) (r j)).hom)
    Fppf.IsFppf ((testSpec k).map a.op).left := by
  classical
  intro S a
  let A (j : J) := CommRingCat.of (Localization.Away (r j))
  let s := sigmaSpec A
  let f := ((testSpec k).map a.op).left
  have hs (j : J) : Sigma.ι (fun i => Spec (A i)) j ≫ s ≫ f =
      ((testSpec k).map (awayHom (k := k) (r j)).op).left := by
    rw [ι_sigmaSpec_assoc]
    change Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ j)) ≫
      Spec.map (CommRingCat.ofHom a.hom.toRingHom) = _
    rw [← Spec.map_comp]
    rfl
  have hf (j : J) : IsOpenImmersion (Sigma.ι (fun i => Spec (A i)) j ≫ s ≫ f) := by
    rw [hs]
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (r j)))))
    infer_instance
  haveI : IsIso s := inferInstance
  have hd : s ≫ f =
      Sigma.desc (fun j => ((testSpec k).map (awayHom (k := k) (r j)).op).left) := by
    apply Sigma.hom_ext
    intro j
    rw [Sigma.ι_comp_desc, hs]
  have hflat : Flat (s ≫ f) := by
    rw [hd]
    apply IsZariskiLocalAtSource.sigmaDesc
    intro j
    rw [← hs j]
    letI := hf j
    exact inferInstance
  have hfp : LocallyOfFinitePresentation (s ≫ f) := by
    rw [hd]
    apply IsZariskiLocalAtSource.sigmaDesc
    intro j
    rw [← hs j]
    letI := hf j
    exact locallyOfFinitePresentation_of_isOpenImmersion _
  refine ⟨(MorphismProperty.cancel_left_of_respectsIso (P := @Flat) s f).mp hflat, ⟨?_⟩,
    (MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFinitePresentation) s f).mp hfp⟩
  intro x
  change PrimeSpectrum R at x
  obtain ⟨j, hj⟩ : ∃ j, r j ∉ x.asIdeal := by
    by_contra! h
    exact x.isPrime.ne_top (top_unique (hr ▸ Ideal.span_le.mpr (Set.range_subset_iff.mpr h)))
  obtain ⟨y, hy⟩ : x ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away (r j)))) := by
    rwa [PrimeSpectrum.localization_away_comap_range (Localization.Away (r j)) (r j)]
  let y' : Spec (A j) := y
  refine ⟨(Sigma.ι (fun i => Spec (A i)) j ≫ s) y', ?_⟩
  change f ((Sigma.ι (fun i => Spec (A i)) j ≫ s) y') = x
  calc
    _ = ((Sigma.ι (fun i => Spec (A i)) j ≫ s) ≫ f) y' :=
      (Scheme.Hom.comp_apply (Sigma.ι (fun i => Spec (A i)) j ≫ s) f y').symm
    _ = ((testSpec k).map (awayHom (k := k) (r j)).op).left y' :=
      congrArg (fun t : Spec (A j) ⟶ ((testSpec k).obj (op R)).left => t y')
        ((Category.assoc _ _ _).trans (hs j))
    _ = x := hy

/-- Each projective point has unimodular homogeneous coordinates over an affine fppf cover. -/
theorem exists_fppf_coordinates {R : TestAlgebra k} (p : Points (projectiveLine k) R) :
    ∃ (S : TestAlgebra k) (a : R ⟶ S) (v : Index.{u} → S),
      Fppf.IsFppf ((testSpec k).map a.op).left ∧
        Ideal.span (Set.range v) = ⊤ ∧ HasCoordinates (planeRepresentation k) S (mapPoints a p) v := by
  classical
  obtain ⟨e, he⟩ := ProjectiveSpaces.basisPointFormula k (plane k) Index (planeBasis k)
  obtain ⟨J, hJ, r, i, d, hr, hd⟩ := point_has_principal_chart_cover (p ≫ e.inv)
  letI := hJ
  let S := CommAlgCat.of k (∀ j, Localization.Away (r j))
  let a : R ⟶ S := CommAlgCat.ofHom (AlgHom.pi fun j => (awayHom (k := k) (r j)).hom)
  let π (j : J) : S ⟶ CommAlgCat.of k (Localization.Away (r j)) :=
    CommAlgCat.ofHom (Pi.evalAlgHom k (fun j => Localization.Away (r j)) j)
  let v (l : Index.{u}) : S := fun j => d j (coordinateRatio k Index (i j) l)
  let c (l : Index.{u}) : S := fun j => if l = i j then 1 else 0
  have hcv : ∑ l, c l * v l = 1 := by
    funext j
    change (Pi.evalRingHom (fun j => Localization.Away (r j)) j) (∑ l, c l * v l) = 1
    rw [map_sum]
    simp only [map_mul, Pi.evalRingHom_apply, c, v]
    rw [Finset.sum_eq_single (i j)]
    · simp [ratio_self]
    · intro l _ hl
      simp [hl]
    · simp
  let L := coordinatesLine S v c hcv
  let z := pointOfPlaneLine L
  have hz : HasCoordinates (planeRepresentation k) S z v :=
    (congrArg AffineLine.submodule (planeLine_pointOfPlaneLine L)).trans
      (coordinatesLine_submodule S v c hcv)
  refine ⟨S, a, v, principalCover_fppf r hr, ?_, ?_⟩
  · apply (Ideal.eq_top_iff_one _).mpr
    rw [← hcv]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)
  · have hpeq (j : J) : mapPoints (π j) (mapPoints a p) = mapPoints (π j) z := by
      apply planeLine_ext
      have hj := congrArg (· ≫ e.hom) (hd j)
      simp only [mapPoints, Category.assoc, Iso.inv_hom_id, Category.comp_id] at hj
      have hpj : mapPoints (π j) (mapPoints a p) = chartPoint (i j) (d j) ≫ e.hom := by
        simpa only [mapPoints, ← Category.assoc, ← Functor.map_comp, ← op_comp,
          show a ≫ π j = awayHom (r j) from rfl] using hj
      rw [hpj]
      exact (he (i j) _ (d j)).trans (hasCoordinates_change (π j) hz).symm
    have hpz : mapPoints a p = z := by
      apply Over.OverMorphism.ext
      let A (j : J) := CommRingCat.of (Localization.Away (r j))
      let s := sigmaSpec A
      haveI : IsIso s := inferInstance
      rw [← cancel_epi s]
      apply Sigma.hom_ext
      intro j
      rw [ι_sigmaSpec_assoc, ι_sigmaSpec_assoc]
      exact congrArg Over.Hom.left (hpeq j)
    exact hpz.symm ▸ hz


end HomogeneousCoordinates

section TwoCharts

open Specs.RankOneFlag (Index plane planeBasis projectiveLine HasCoordinates)
open Specs.ProjectiveSpaces (AffineLine)
open private lineCoord_bijective_of_one line_span_of_pivot extendVector extendVector_coord
  affinePoints_ext_principal point_has_principal_chart_cover chartPoint awayHom ratio_self
  changeLineSubmodule_eq_span
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.ProjectiveSpaces

variable {k : Type u} [Field k]

private def otherIndex (i : Index.{u}) : Index.{u} :=
  ⟨i.down.rev⟩

private theorem otherIndex_ne (i : Index.{u}) : otherIndex i ≠ i := by
  rcases i with ⟨i⟩
  fin_cases i <;> decide

private theorem eq_otherIndex {i j : Index.{u}} (h : j ≠ i) : j = otherIndex i := by
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  fin_cases i <;> fin_cases j <;> first | contradiction | rfl

@[simp]
private theorem otherIndex_otherIndex (i : Index.{u}) : otherIndex (otherIndex i) = i := by
  rcases i with ⟨i⟩
  exact congrArg ULift.up (Fin.rev_rev i)

private def affineCoordinates {R : TestAlgebra k} (i : Index.{u}) (z : R) :
    Index.{u} → R := fun j => if j = i then 1 else z

private def affinePoint (R : TestAlgebra k) (i : Index.{u}) (z : R) :
    Points (projectiveLine k) R :=
  pointOfPlaneLine (coordinatesLine R (affineCoordinates i z)
    (fun j => if j = i then 1 else 0) (by
      rw [Finset.sum_eq_single i]
      · simp [affineCoordinates]
      · intro j _ hj
        simp [hj]
      · simp))

private theorem affinePoint_coordinates (R : TestAlgebra k) (i : Index.{u}) (z : R) :
    (planeLine (affinePoint R i z)).submodule =
      Submodule.span R {vectorOfCoordinates R (affineCoordinates i z)} :=
  (congrArg AffineLine.submodule (planeLine_pointOfPlaneLine _)).trans
    (coordinatesLine_submodule _ _ _ _)

private theorem affinePoint_change {R S : TestAlgebra k} (a : R ⟶ S)
    (i : Index.{u}) (z : R) :
    mapPoints a (affinePoint R i z) = affinePoint S i (a.hom z) := by
  have h := hasCoordinates_change a (affinePoint_coordinates R i z)
  apply planeLine_ext
  change (planeLine (mapPoints a (affinePoint R i z))).submodule =
    Submodule.span S {vectorOfCoordinates S (fun j => a.hom (affineCoordinates i z j))} at h
  rw [h, affinePoint_coordinates]
  have hv : (fun j => a.hom (affineCoordinates i z j)) = affineCoordinates i (a.hom z) := by
    funext j
    by_cases hj : j = i <;> simp [affineCoordinates, hj]
  rw [hv]

private theorem affinePoint_injective (R : TestAlgebra k) (i : Index.{u}) :
    Function.Injective (affinePoint R i) := by
  intro z w e
  let b := (planeBasis k).baseChange R
  have h : Submodule.span R {vectorOfCoordinates R (affineCoordinates i z)} =
      Submodule.span R {vectorOfCoordinates R (affineCoordinates i w)} := by
    rw [← affinePoint_coordinates R i z, ← affinePoint_coordinates R i w, e]
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
    (h ▸ Submodule.mem_span_singleton_self (vectorOfCoordinates R (affineCoordinates i z)))
  have hi (j : Index.{u}) : a * affineCoordinates i w j = affineCoordinates i z j := by
    have h' := congrArg (b.coord j) ha
    simpa only [map_smul, smul_eq_mul,
      show ∀ v : Index.{u} → R, b.coord j (vectorOfCoordinates R v) = v j from fun v =>
        congrFun (LinearEquiv.apply_symm_apply b.equivFun v) j] using h'
  have h₁ : a = 1 := by simpa [affineCoordinates] using hi i
  simpa [affineCoordinates, otherIndex_ne, h₁] using (hi (otherIndex i)).symm

private theorem affinePoint_ne_opposite_zero {R : TestAlgebra k} [Nontrivial R]
    (i : Index.{u}) (z : R) : affinePoint R i z ≠ affinePoint R (otherIndex i) 0 := by
  intro e
  let b := (planeBasis k).baseChange R
  have h : Submodule.span R {vectorOfCoordinates R (affineCoordinates i z)} =
      Submodule.span R {vectorOfCoordinates R (affineCoordinates (otherIndex i) 0)} := by
    rw [← affinePoint_coordinates R i z, ← affinePoint_coordinates R (otherIndex i) 0, e]
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
    (h ▸ Submodule.mem_span_singleton_self (vectorOfCoordinates R (affineCoordinates i z)))
  have h' := congrArg (b.coord i) ha
  have h₀ : i ≠ otherIndex i := (otherIndex_ne i).symm
  have hscalar (v : Index.{u} → R) : b.coord i (vectorOfCoordinates R v) = v i :=
    congrFun (LinearEquiv.apply_symm_apply b.equivFun v) i
  rw [map_smul, smul_eq_mul, hscalar, hscalar] at h'
  simp [affineCoordinates, h₀] at h'


private theorem exists_affinePoint_of_coord_one {R : TestAlgebra k}
    (i : Index.{u}) (p : Points (projectiveLine k) R)
    (x : (planeLine p).submodule) (hx : ((planeBasis k).baseChange R).coord i x.val = 1) :
    ∃ z, p = affinePoint R i z := by
  let b := (planeBasis k).baseChange R
  have hbij := lineCoord_bijective_of_one (planeBasis k) i (planeLine p) x hx
  obtain ⟨v, hv, hL⟩ := line_span_of_pivot (planeBasis k) i ⟨planeLine p, hbij⟩
  refine ⟨b.coord (otherIndex i) v, planeLine_ext ?_⟩
  rw [hL, affinePoint_coordinates]
  congr 2
  apply b.ext_elem
  intro j
  change b.coord j v = (b.equivFun
    (vectorOfCoordinates R (affineCoordinates i (b.coord (otherIndex i) v)))) j
  rw [LinearEquiv.apply_symm_apply]
  by_cases hj : j = i
  · subst j
    simpa [affineCoordinates] using hv
  · rw [affineCoordinates, ite_eq_right hj, eq_otherIndex hj]

private theorem exists_affinePoint_of_avoids_opposite {R : TestAlgebra k}
    (i : Index.{u}) (p : Points (projectiveLine k) R)
    (h : ∀ (S : TestAlgebra k) [Nontrivial S] (a : R ⟶ S),
      mapPoints a p ≠ affinePoint S (otherIndex i) 0) :
    ∃ z, p = affinePoint R i z := by
  let L := planeLine p
  let f := ((planeBasis k).baseChange R).coord i ∘ₗ L.submodule.subtype
  let I : Ideal R := f.range
  by_cases hI : I = ⊤
  · have h1 : (1 : R) ∈ I := (Ideal.eq_top_iff_one _).mp hI
    obtain ⟨x, hx⟩ := h1
    exact exists_affinePoint_of_coord_one i p x hx
  obtain ⟨m, hm, him⟩ := I.exists_le_maximal hI
  let S := CommAlgCat.of k (R ⧸ m)
  let a : R ⟶ S := CommAlgCat.ofHom (Ideal.Quotient.mkₐ k m)
  let Q := planeLine (mapPoints a p)
  let b := (planeBasis k).baseChange S
  have hker : Q.submodule ≤ (b.coord i).ker := by
    change (planeLine (mapPoints a p)).submodule ≤ _
    rw [planeLine_change, changeLineSubmodule_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, extendVector_coord]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (him (show _ ∈ I from ⟨⟨x, hx⟩, rfl⟩))
  let F : Field (R ⧸ m) := Ideal.Quotient.field _
  haveI : Nontrivial S := (inferInstance : Nontrivial (R ⧸ m))
  have hQ : Q.submodule ≠ ⊥ := by
    intro hz
    let s : PrimeSpectrum S := ⟨⊥, inferInstanceAs (Ideal.IsPrime (⊥ : Ideal (R ⧸ m)))⟩
    have h0 := Q.rank_one s
    rw [hz] at h0
    have : Subsingleton (⊥ : Submodule S (S ⊗[k] plane k)) := inferInstance
    rw [Module.rankAtStalk_eq_zero_of_subsingleton] at h0
    exact Nat.zero_ne_one h0
  obtain ⟨y, hy, hy'⟩ := (Submodule.ne_bot_iff Q.submodule).mp hQ
  have hbi : b.coord i y = 0 := hker hy
  have hbj : b.coord (otherIndex i) y ≠ 0 := by
    intro hz
    apply hy'
    apply b.ext_elem
    intro j
    rw [map_zero]
    by_cases hj : j = i
    · simpa [hj] using hbi
    · rwa [eq_otherIndex hj]
  letI := F
  let z : S := (b.coord (otherIndex i) y)⁻¹
  have hnorm : b.coord (otherIndex i) (z • y) = 1 := by
    rw [map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hbj
  obtain ⟨c, hc⟩ := exists_affinePoint_of_coord_one (otherIndex i) (mapPoints a p)
    ⟨z • y, Q.submodule.smul_mem z hy⟩ hnorm
  have hcoord := affinePoint_coordinates S (otherIndex i) c
  have hmem : vectorOfCoordinates S (affineCoordinates (otherIndex i) c) ∈ Q.submodule := by
    change _ ∈ (planeLine (mapPoints a p)).submodule
    rw [hc, hcoord]
    exact Submodule.mem_span_singleton_self _
  have hc₀ := hker hmem
  change b.coord i (vectorOfCoordinates S (affineCoordinates (otherIndex i) c)) = 0 at hc₀
  change b.equivFun (b.equivFun.symm (affineCoordinates (otherIndex i) c)) i = 0 at hc₀
  rw [LinearEquiv.apply_symm_apply, affineCoordinates, ite_eq_right (otherIndex_ne i).symm] at hc₀
  exact (h S a (hc.trans (congrArg (affinePoint S (otherIndex i)) hc₀))).elim

private theorem affinePoint_overlap {R : TestAlgebra k} (i : Index.{u}) (z w : R) :
    affinePoint R i z = affinePoint R (otherIndex i) w ↔ z * w = 1 := by
  let b := (planeBasis k).baseChange R
  let v := affineCoordinates i z
  let v' := affineCoordinates (otherIndex i) w
  have h (a : R) :
      vectorOfCoordinates R v = a • vectorOfCoordinates R v' ↔
        ∀ j, v j = a * v' j := by
    rw [← (b.equivFun.injective.eq_iff), map_smul, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
    exact ⟨fun h j => congrFun h j, funext⟩
  constructor
  · intro he
    have hs : Submodule.span R {vectorOfCoordinates R v} = Submodule.span R {vectorOfCoordinates R v'} := by
      rw [← affinePoint_coordinates R i z, ← affinePoint_coordinates R (otherIndex i) w, he]
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
      (hs ▸ Submodule.mem_span_singleton_self (vectorOfCoordinates R v))
    have hn := (h a).mp ha.symm
    have h0 : 1 = a * w := by simpa [v, v', affineCoordinates, (otherIndex_ne i).symm] using hn i
    have h1 : z = a := by simpa [v, v', affineCoordinates, otherIndex_ne] using hn (otherIndex i)
    exact h1 ▸ h0.symm
  · intro hz
    have hv : vectorOfCoordinates R v = z • vectorOfCoordinates R v' :=
      (h z).mpr (fun j => by
        by_cases hj : j = i
        · subst j
          simp [v, v', affineCoordinates, (otherIndex_ne i).symm, hz]
        · rw [eq_otherIndex hj]
          simp [v, v', affineCoordinates, otherIndex_ne])
    apply planeLine_ext
    rw [affinePoint_coordinates, affinePoint_coordinates]
    change Submodule.span R {vectorOfCoordinates R v} = Submodule.span R {vectorOfCoordinates R v'}
    apply le_antisymm
    · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
      rw [hv]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
      apply Submodule.mem_span_singleton.mpr
      refine ⟨w, ?_⟩
      rw [hv, smul_smul, mul_comm w z, hz, one_smul]

private theorem affineChart_determines_of_principal
    {R : TestAlgebra k} (p : Points (projectiveLine k) R) :
    ∃ (J : Type u) (r : J → R) (i : J → Index.{u})
      (z : ∀ j, Localization.Away (r j)),
      Ideal.span (Set.range r) = ⊤ ∧
      (∀ j, mapPoints (awayHom (r j)) p = affinePoint _ (i j) (z j)) := by
  obtain ⟨e, he⟩ := ProjectiveSpaces.basisPointFormula k (plane k) Index (planeBasis k)
  obtain ⟨J, _, r, i, d, hr, hd⟩ := point_has_principal_chart_cover (p ≫ e.inv)
  refine ⟨J, r, i, fun j => d j (Specs.ProjectiveSpaces.coordinateRatio k _ (i j) (otherIndex (i j))),
    hr, fun j => ?_⟩
  have hj := congrArg (· ≫ e.hom) (hd j)
  simp only [mapPoints, Category.assoc, Iso.inv_hom_id, Category.comp_id] at hj
  change mapPoints (awayHom (r j)) p = _ at hj
  rw [hj]
  apply planeLine_ext
  refine (he (i j) _ (d j)).trans ?_
  rw [affinePoint_coordinates]
  congr 2
  apply congrArg
  funext l
  by_cases hl : l = i j
  · simp [hl, affineCoordinates, ratio_self]
  · rw [affineCoordinates, ite_eq_right hl, eq_otherIndex hl]

end TwoCharts

section RelativeAutomorphisms

open Specs.RankOneFlag (projectiveLine lineOver lineBaseMap)
open private overHom_ext_affine from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.ProjectiveSpaces

variable {k : Type u} [Field k]

private def relativePoint {R S : TestAlgebra k} (a : R ⟶ S) (p : Points (projectiveLine k) S) :
    Over.mk ((testSpec k).map a.op) ⟶ lineOver R :=
  Over.homMk (lift p ((testSpec k).map a.op)) (lift_snd _ _)

private def applyRelativeAut {R S : TestAlgebra k} (f : Aut (lineOver R)) (a : R ⟶ S)
    (p : Points (projectiveLine k) S) : Points (projectiveLine k) S :=
  (relativePoint a p ≫ f.asIso.hom).left ≫ fst _ _

private theorem relativePoint_applyRelativeAut {R S : TestAlgebra k} (f : Aut (lineOver R))
    (a : R ⟶ S) (p : Points (projectiveLine k) S) :
    relativePoint a (applyRelativeAut f a p) = relativePoint a p ≫ f.asIso.hom := by
  apply Over.OverMorphism.ext
  apply CartesianMonoidalCategory.hom_ext
  · simp [relativePoint, applyRelativeAut]
  · exact (lift_snd _ _).trans (Over.w (relativePoint a p ≫ f.asIso.hom)).symm

private theorem applyRelativeAut_one {R S : TestAlgebra k} (a : R ⟶ S)
    (p : Points (projectiveLine k) S) : applyRelativeAut 1 a p = p := by
  change (lift p ((testSpec k).map a.op) ≫ 𝟙 _) ≫ fst _ _ = p
  rw [Category.comp_id, lift_fst]

private theorem applyRelativeAut_mul {R S : TestAlgebra k} (f g : Aut (lineOver R)) (a : R ⟶ S)
    (p : Points (projectiveLine k) S) :
    applyRelativeAut (f * g) a p = applyRelativeAut f a (applyRelativeAut g a p) := by
  change _ = (relativePoint a (applyRelativeAut g a p) ≫ f.asIso.hom).left ≫ fst _ _
  rw [relativePoint_applyRelativeAut, Category.assoc]
  rfl

private theorem applyRelativeAut_injective {R S : TestAlgebra k} (f : Aut (lineOver R))
    (a : R ⟶ S) : Function.Injective (applyRelativeAut f a) := by
  intro p p' hp
  have h (x : Points (projectiveLine k) S) :
      applyRelativeAut f⁻¹ a (applyRelativeAut f a x) = x := by
    rw [← applyRelativeAut_mul, inv_mul_cancel, applyRelativeAut_one]
  exact (h p).symm.trans ((congrArg (applyRelativeAut f⁻¹ a) hp).trans (h p'))

private theorem applyRelativeAut_change {R S T : TestAlgebra k} (f : Aut (lineOver R))
    (a : R ⟶ S) (b : S ⟶ T) (p : Points (projectiveLine k) S) :
    mapPoints b (applyRelativeAut f a p) = applyRelativeAut f (a ≫ b) (mapPoints b p) := by
  change (testSpec k).map b.op ≫ (lift p ((testSpec k).map a.op) ≫ f.asIso.hom.left) ≫ fst _ _ =
    (lift (mapPoints b p) ((testSpec k).map (a ≫ b).op) ≫ f.asIso.hom.left) ≫ fst _ _
  simp only [mapPoints, op_comp, Functor.map_comp, ← comp_lift_assoc, Category.assoc]

private theorem relativeAut_ext {R : TestAlgebra k} {f g : Aut (lineOver R)}
    (h : ∀ (S : TestAlgebra k) (a : R ⟶ S) (p : Points (projectiveLine k) S),
      applyRelativeAut f a p = applyRelativeAut g a p) : f = g := by
  apply Aut.ext
  apply Iso.ext
  apply Over.OverMorphism.ext
  apply CartesianMonoidalCategory.hom_ext
  · apply overHom_ext_affine
    intro S m
    let FF := algSpec.fullyFaithful (R := CommRingCat.of k)
    let a : R ⟶ S := (FF.preimage (m ≫ snd _ _)).unop
    have ha : (testSpec k).map a.op = m ≫ snd _ _ := FF.map_preimage _
    rw [show m = (relativePoint a (m ≫ fst _ _)).left by
      change m = lift (m ≫ fst _ _) ((testSpec k).map a.op)
      rw [ha, lift_comp_fst_snd]]
    exact h S a (m ≫ fst _ _)
  · exact (Over.w f.asIso.hom).trans (Over.w g.asIso.hom).symm

open private isPullback_tensor_snd from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SmoothOrbit

private theorem lineBaseMap_eq_tensor {R S : TestAlgebra k} (a : R ⟶ S) :
    lineBaseMap a = 𝟙 (projectiveLine k) ⊗ₘ (testSpec k).map a.op := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [lineBaseMap]
  · simp [lineBaseMap]

private theorem lineBaseMap_pullback {R S : TestAlgebra k} (a : R ⟶ S) :
    IsPullback (lineBaseMap a) (lineOver S).hom (lineOver R).hom ((testSpec k).map a.op) := by
  rw [lineBaseMap_eq_tensor]
  exact isPullback_tensor_snd _

private def lineOverBaseIso {R S : TestAlgebra k} (a : R ⟶ S) :
    lineOver S ≅ (Over.pullback ((testSpec k).map a.op)).obj (lineOver R) :=
  Over.isoMk (lineBaseMap_pullback a).isoPullback
    (lineBaseMap_pullback a).isoPullback_hom_snd

private def changeRelativeAut {R S : TestAlgebra k} (a : R ⟶ S) (f : Aut (lineOver R)) :
    Aut (lineOver S) :=
  Aut.of (lineOverBaseIso a ≪≫ (Over.pullback ((testSpec k).map a.op)).mapIso f.asIso ≪≫
    (lineOverBaseIso a).symm)

private theorem changeRelativeAut_fac {R S : TestAlgebra k} (a : R ⟶ S) (f : Aut (lineOver R)) :
    (changeRelativeAut a f).asIso.hom.left ≫ lineBaseMap a = lineBaseMap a ≫ f.asIso.hom.left := by
  let e := lineOverBaseIso a
  let F := Over.pullback ((testSpec k).map a.op)
  let p := pullback.fst (lineOver R).hom ((testSpec k).map a.op)
  have he : e.hom.left ≫ p = lineBaseMap a := (lineBaseMap_pullback a).isoPullback_hom_fst
  have hei : e.inv.left ≫ lineBaseMap a = p := by
    rw [← he, ← Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.id_comp]
  have hf : (F.map f.asIso.hom).left ≫ p = p ≫ f.asIso.hom.left := pullback.lift_fst _ _ _
  change (e.hom ≫ F.map f.asIso.hom ≫ e.inv).left ≫ lineBaseMap a =
    lineBaseMap a ≫ f.asIso.hom.left
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hei,
    hf, ← Category.assoc e.hom.left, he]

private theorem applyRelativeAut_changeAut {R S T : TestAlgebra k} (a : R ⟶ S) (b : S ⟶ T)
    (f : Aut (lineOver R)) (p : Points (projectiveLine k) T) :
    applyRelativeAut (changeRelativeAut a f) b p = applyRelativeAut f (a ≫ b) p := by
  have he : lift p ((testSpec k).map b.op) ≫ lineBaseMap a =
      lift p ((testSpec k).map (a ≫ b).op) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [lineBaseMap]
    · simp [lineBaseMap, op_comp, Functor.map_comp]
  change (lift p ((testSpec k).map b.op) ≫ (changeRelativeAut a f).asIso.hom.left) ≫ fst _ _ =
    (lift p ((testSpec k).map (a ≫ b).op) ≫ f.asIso.hom.left) ≫ fst _ _
  have hf : lineBaseMap a ≫ fst _ _ = fst (projectiveLine k) ((testSpec k).obj (op S)) := lift_fst _ _
  rw [← hf, Category.assoc, ← Category.assoc (changeRelativeAut a f).asIso.hom.left,
    changeRelativeAut_fac]
  simp only [Category.assoc, reassoc_of% he]

end RelativeAutomorphisms

section FixingThreeSections

open Specs.RankOneFlag (Index projectiveLine lineOver)
open CocharacterDynamics (polynomialAlgebra laurentAlgebra laurentConstants)
open Polynomial LaurentPolynomial
open private affinePoints_ext_principal awayHom from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.ProjectiveSpaces

variable {k : Type u} [Field k] {R : TestAlgebra k}

private def FixesEndpoints (f : Aut (lineOver R)) : Prop :=
  ∀ i : Index.{u}, applyRelativeAut f (𝟙 R) (affinePoint R i 0) = affinePoint R i 0

private theorem fixesEndpoints_change {f : Aut (lineOver R)} (hf : FixesEndpoints f)
    {S : TestAlgebra k} (a : R ⟶ S) (i : Index.{u}) :
    applyRelativeAut f a (affinePoint S i 0) = affinePoint S i 0 := by
  have he := congrArg (mapPoints a) (hf i)
  rwa [applyRelativeAut_change, Category.id_comp, affinePoint_change, map_zero] at he

private theorem fixesEndpoints_inverse {f : Aut (lineOver R)} (hf : FixesEndpoints f) :
    FixesEndpoints f⁻¹ := by
  intro i
  apply applyRelativeAut_injective f (𝟙 R)
  rw [← applyRelativeAut_mul, mul_inv_cancel, applyRelativeAut_one, hf i]

private theorem applyRelativeAut_in_chart {f : Aut (lineOver R)} (hf : FixesEndpoints f)
    {S : TestAlgebra k} (a : R ⟶ S) (i : Index.{u}) (z : S) :
    ∃ w, applyRelativeAut f a (affinePoint S i z) = affinePoint S i w := by
  apply exists_affinePoint_of_avoids_opposite
  intro T _ b h
  rw [applyRelativeAut_change, affinePoint_change,
    ← fixesEndpoints_change hf (a ≫ b) (otherIndex i)] at h
  exact affinePoint_ne_opposite_zero i (b.hom z) (applyRelativeAut_injective f (a ≫ b) h)

private def polynomialConstants (R : TestAlgebra k) : R ⟶ polynomialAlgebra R :=
  CommAlgCat.ofHom (IsScalarTower.toAlgHom k R (Polynomial R))

private def chartPolynomial {f : Aut (lineOver R)} (hf : FixesEndpoints f) (i : Index.{u}) :
    Polynomial R :=
  (applyRelativeAut_in_chart hf (polynomialConstants R) i Polynomial.X).choose

private theorem applyRelativeAut_chartPolynomial {f : Aut (lineOver R)} (hf : FixesEndpoints f)
    {S : TestAlgebra k} (a : R ⟶ S) (i : Index.{u}) (z : S) :
    applyRelativeAut f a (affinePoint S i z) =
      affinePoint S i (Polynomial.aevalTower a.hom z (chartPolynomial hf i)) := by
  let b : polynomialAlgebra R ⟶ S := CommAlgCat.ofHom (Polynomial.aevalTower a.hom z)
  have hb : polynomialConstants R ≫ b = a := by
    ext c
    change Polynomial.aevalTower a.hom z (Polynomial.C c) = a.hom c
    exact Polynomial.aevalTower_C _ _ _
  have he := congrArg (mapPoints b)
    (applyRelativeAut_in_chart hf (polynomialConstants R) i Polynomial.X).choose_spec
  rw [applyRelativeAut_change, hb, affinePoint_change, affinePoint_change] at he
  simpa only [b, CommAlgCat.hom_ofHom, Polynomial.aevalTower_X, chartPolynomial] using he

private theorem chartPolynomial_aeval_eq {S : TestAlgebra k} (a : R ⟶ S)
    [Algebra R S] [IsScalarTower k R S] (ha : a.hom = IsScalarTower.toAlgHom k R S)
    (z : S) (p : Polynomial R) :
    Polynomial.aevalTower a.hom z p = Polynomial.aeval z p := by
  rw [ha]
  rfl

private def chartAlgebraAut {f : Aut (lineOver R)} (hf : FixesEndpoints f) (i : Index.{u}) :
    Polynomial R ≃ₐ[R] Polynomial R := by
  let p := chartPolynomial hf i
  let q := chartPolynomial (fixesEndpoints_inverse hf) i
  have hpoly (g : Aut (lineOver R)) (hg : FixesEndpoints g) (z : Polynomial R) :
      applyRelativeAut g (polynomialConstants R) (affinePoint _ i z) =
        affinePoint _ i (Polynomial.aeval z (chartPolynomial hg i)) := by
    rw [applyRelativeAut_chartPolynomial, chartPolynomial_aeval_eq (polynomialConstants R) rfl]
  refine AlgEquiv.ofAlgHom (Polynomial.aeval p) (Polynomial.aeval q)
    (Polynomial.algHom_ext ?_) (Polynomial.algHom_ext ?_)
  · have h := applyRelativeAut_mul f⁻¹ f (polynomialConstants R)
      (affinePoint _ i Polynomial.X)
    rw [inv_mul_cancel, applyRelativeAut_one, hpoly f hf,
      hpoly f⁻¹ (fixesEndpoints_inverse hf), Polynomial.aeval_X_left_apply] at h
    simpa only [AlgHom.comp_apply, Polynomial.aeval_X, AlgHom.id_apply, p, q] using
      ((affinePoint_injective _ i) h).symm
  · have h := applyRelativeAut_mul f f⁻¹ (polynomialConstants R)
      (affinePoint _ i Polynomial.X)
    rw [mul_inv_cancel, applyRelativeAut_one, hpoly f⁻¹ (fixesEndpoints_inverse hf),
      hpoly f hf, Polynomial.aeval_X_left_apply] at h
    simpa only [AlgHom.comp_apply, Polynomial.aeval_X, AlgHom.id_apply, p, q] using
      ((affinePoint_injective _ i) h).symm

private theorem chartAlgebraAut_X {f : Aut (lineOver R)} (hf : FixesEndpoints f) (i : Index.{u}) :
    chartAlgebraAut hf i Polynomial.X = chartPolynomial hf i := Polynomial.aeval_X _

private theorem chartAlgebraAut_symm_X {f : Aut (lineOver R)} (hf : FixesEndpoints f) (i : Index.{u}) :
    (chartAlgebraAut hf i).symm Polynomial.X = chartPolynomial (fixesEndpoints_inverse hf) i :=
  Polynomial.aeval_X _

private theorem chartPolynomial_eval_zero {f : Aut (lineOver R)} (hf : FixesEndpoints f) (i : Index.{u}) :
    (chartPolynomial hf i).eval 0 = 0 := by
  have h := applyRelativeAut_chartPolynomial hf (𝟙 R) i 0
  rw [hf i] at h
  have h₀ := (affinePoint_injective R i) h
  exact h₀.symm

private theorem chartPolynomial_overlap {f : Aut (lineOver R)} (hf : FixesEndpoints f) (i : Index.{u}) :
    (chartPolynomial hf i).toLaurent *
      invert (chartPolynomial hf (otherIndex i)).toLaurent = 1 := by
  let S := laurentAlgebra R
  let a := laurentConstants R
  have h : affinePoint S i (T 1) = affinePoint S (otherIndex i) (T (-1)) := by
    apply (affinePoint_overlap _ _ _).mpr
    change (T 1 : LaurentPolynomial R) * T (-1) = 1
    rw [← T_add]
    norm_num [T_zero]
  have he := congrArg (applyRelativeAut f a) h
  rw [applyRelativeAut_chartPolynomial, applyRelativeAut_chartPolynomial] at he
  have h₁ : Polynomial.aevalTower a.hom (T 1) = Polynomial.toLaurentAlg.restrictScalars k := by
    have h : Polynomial.aeval (T 1 : LaurentPolynomial R) = Polynomial.toLaurentAlg :=
      Polynomial.algHom_ext (by rw [Polynomial.aeval_X, Polynomial.toLaurentAlg_apply, toLaurent_X])
    exact congrArg (AlgHom.restrictScalars k) h
  have h₂ (p : Polynomial R) :
      Polynomial.aevalTower a.hom (T (-1)) p = invert p.toLaurent := by
    suffices h : (Polynomial.aevalTower a.hom (T (-1))).toRingHom =
        invert.toRingHom.comp Polynomial.toLaurent from DFunLike.congr_fun h p
    apply Polynomial.ringHom_ext
    · intro x
      simp [a, laurentConstants, Polynomial.aevalTower_C, toLaurent_C]
    · simp [Polynomial.aevalTower_X, toLaurent_X, invert_T]
  exact (by
    simpa only [h₁, Polynomial.toLaurentAlg_apply, AlgHom.coe_restrictScalars', h₂] using
      (affinePoint_overlap _ _ _).mp he)

private theorem relativeAut_eq_one_of_three {f : Aut (lineOver R)}
    (hf : FixesEndpoints f) (i : Index.{u})
    (hone : applyRelativeAut f (𝟙 R) (affinePoint R i 1) = affinePoint R i 1) :
    f = 1 := by
  have h₁ : (chartPolynomial hf i).eval 1 = 1 := by
    have h := applyRelativeAut_chartPolynomial hf (𝟙 R) i 1
    rw [hone] at h
    exact ((affinePoint_injective R i) h).symm
  obtain ⟨ha, hb⟩ := polynomial_charts_eq_refl (chartAlgebraAut hf i)
    (chartAlgebraAut hf (otherIndex i))
    (by rw [chartAlgebraAut_X]; exact chartPolynomial_eval_zero hf i)
    (by rw [chartAlgebraAut_symm_X]; exact chartPolynomial_eval_zero (fixesEndpoints_inverse hf) i)
    (by rw [chartAlgebraAut_X]; exact chartPolynomial_eval_zero hf _)
    (by rw [chartAlgebraAut_symm_X]; exact chartPolynomial_eval_zero (fixesEndpoints_inverse hf) _)
    (by rwa [chartAlgebraAut_X])
    (by rw [chartAlgebraAut_X, chartAlgebraAut_X]; exact chartPolynomial_overlap hf i)
  have hc (j : Index.{u}) : chartPolynomial hf j = Polynomial.X := by
    by_cases hj : j = i
    · subst j
      rw [← chartAlgebraAut_X, ha]
      rfl
    · rw [eq_otherIndex hj, ← chartAlgebraAut_X, hb]
      rfl
  apply relativeAut_ext
  intro S a p
  rw [applyRelativeAut_one]
  obtain ⟨J, r, j, z, hr, hz⟩ := affineChart_determines_of_principal p
  apply affinePoints_ext_principal r hr
  intro l
  rw [applyRelativeAut_change, hz, applyRelativeAut_chartPolynomial hf, hc, Polynomial.aevalTower_X]

end FixingThreeSections

section FppfDescent

variable {k : Type u} [Field k] {W X Y Z : SchemeOver k}

private theorem fppf_epi (f : X ⟶ Y) (hf : Fppf.IsFppf f.left) : Epi f := by
  letI := hf.1
  letI := hf.2.1
  letI := hf.2.2
  letI : Epi f.left := inferInstance
  exact Over.epi_of_epi_left f

private theorem exists_desc_of_fppf (f : X ⟶ Y) (hf : Fppf.IsFppf f.left)
    (g : X ⟶ Z) (hg : ∀ (T : SchemeOver k) (a b : T ⟶ X),
      a ≫ f = b ≫ f → a ≫ g = b ≫ g) :
    ∃ h : Y ⟶ Z, f ≫ h = g := by
  letI := hf.1
  letI := hf.2.1
  letI := hf.2.2
  have gl {T : Scheme.{u}} (a b : T ⟶ X.left) (hab : a ≫ f.left = b ≫ f.left) :
      a ≫ g.left = b ≫ g.left := by
    let T' := Over.mk (a ≫ X.hom)
    let a' : T' ⟶ X := Over.homMk a
    let b' : T' ⟶ X := Over.homMk b (by
      change b ≫ X.hom = a ≫ X.hom
      rw [← Over.w f, ← Category.assoc, ← hab, Category.assoc])
    exact congrArg Over.Hom.left (hg T' a' b' (Over.OverMorphism.ext hab))
  let h := EffectiveEpi.desc f.left g.left gl
  have hh : f.left ≫ h = g.left := EffectiveEpi.fac _ _ _
  refine ⟨Over.homMk h ?_, Over.OverMorphism.ext hh⟩
  apply (cancel_epi f.left).mp
  rw [← Category.assoc, hh, Over.w, Over.w]

private theorem isPullback_tensor_fst (f : X ⟶ Y) (Z : SchemeOver k) :
    IsPullback (f ⊗ₘ 𝟙 Z) (fst X Z) (fst Y Z) f := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (by simp)
    (fun c => lift c.snd (c.fst ≫ snd Y Z)) ?_ (by simp) ?_)
  · intro c
    apply CartesianMonoidalCategory.hom_ext
    · simpa using c.condition.symm
    · simp
  · intro c m h₁ h₂
    apply CartesianMonoidalCategory.hom_ext
    · simpa using h₂
    · simpa using congrArg (fun t => t ≫ snd Y Z) h₁

open private isPullback_tensor_snd modObjOfSchemeAction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SmoothOrbit

private theorem tensor_fppf {X' Y' : SchemeOver k} (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : Fppf.IsFppf f.left) (hg : Fppf.IsFppf g.left) :
    Fppf.IsFppf (f ⊗ₘ g).left := by
  have h₁ := (isPullback_tensor_fst f Y).flip.map (Over.forget _)
  have h₂ := (isPullback_tensor_snd (A := X') g).flip.map (Over.forget _)
  letI : Flat (f ⊗ₘ 𝟙 Y).left := MorphismProperty.of_isPullback h₁ hf.1
  letI : Surjective (f ⊗ₘ 𝟙 Y).left := MorphismProperty.of_isPullback h₁ hf.2.1
  letI : LocallyOfFinitePresentation (f ⊗ₘ 𝟙 Y).left := MorphismProperty.of_isPullback h₁ hf.2.2
  letI : Flat (𝟙 X' ⊗ₘ g).left := MorphismProperty.of_isPullback h₂ hg.1
  letI : Surjective (𝟙 X' ⊗ₘ g).left := MorphismProperty.of_isPullback h₂ hg.2.1
  letI : LocallyOfFinitePresentation (𝟙 X' ⊗ₘ g).left := MorphismProperty.of_isPullback h₂ hg.2.2
  rw [show f ⊗ₘ g = (f ⊗ₘ 𝟙 Y) ≫ (𝟙 X' ⊗ₘ g) by rw [tensorHom_def]; simp,
    Over.comp_left]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

variable {L M : GroupScheme k}

private theorem desc_groupAction (q : L ⟶ M) (hq : Fppf.IsFppf q.hom.hom.left)
    (a : ModObj L.X X)
    (hinv : ∀ (T : SchemeOver k) (g h : T ⟶ L.X) (z : T ⟶ X),
      g ≫ q.hom.hom = h ≫ q.hom.hom → lift g z ≫ a.smul = lift h z ≫ a.smul) :
    ∃ b : ModObj M.X X, (q.hom.hom ⊗ₘ 𝟙 X) ≫ b.smul = a.smul := by
  let f := q.hom.hom
  have hid : Fppf.IsFppf (𝟙 X : X ⟶ X).left := ⟨inferInstance, inferInstance, inferInstance⟩
  have hqX := tensor_fppf f (𝟙 X) hq hid
  obtain ⟨t, ht⟩ := exists_desc_of_fppf (f ⊗ₘ 𝟙 X) hqX a.smul (by
    intro T g h he
    have hl := congrArg (· ≫ fst M.X X) he
    have hr := congrArg (· ≫ snd M.X X) he
    simp only [f, Category.assoc, tensorHom_fst, tensorHom_snd, Category.comp_id] at hl hr
    have h' : lift (h ≫ fst L.X X) (g ≫ snd L.X X) = h := by
      rw [hr, lift_comp_fst_snd]
    simpa only [lift_comp_fst_snd, h'] using
      hinv T (g ≫ fst L.X X) (h ≫ fst L.X X) (g ≫ snd L.X X) hl)
  have hpoint {T : SchemeOver k} (g : T ⟶ L.X) (x : T ⟶ X) :
      lift (g ≫ f) x ≫ t = lift g x ≫ a.smul := by
    rw [← Category.comp_id x, ← lift_map_assoc, ht]
    simp only [Category.comp_id]
  let a' : PluckerEmbedding.SchemeAction M X := {
    act := t
    unit := by
      have h : toUnit X ≫ η[L.X] ≫ f = toUnit X ≫ η[M.X] := by
        rw [IsMonHom.one_hom]
      rw [← h, ← Category.assoc, hpoint]
      letI := a
      change (1 : X ⟶ L.X) • (𝟙 X) = 𝟙 X
      exact one_smul (X ⟶ L.X) (𝟙 X)
    assoc := by
      let e := f ⊗ₘ (f ⊗ₘ 𝟙 X)
      letI : Epi e := fppf_epi _ (tensor_fppf _ _ hq hqX)
      apply (cancel_epi e).mp
      have hfst : e ≫ fst M.X (M.X ⊗ X) = fst L.X (L.X ⊗ X) ≫ f := by
        simp [e]
      have hsndfst : e ≫ snd M.X (M.X ⊗ X) ≫ fst M.X X =
          (snd L.X (L.X ⊗ X) ≫ fst L.X X) ≫ f := by simp [e]
      have hsndsnd : e ≫ snd M.X (M.X ⊗ X) ≫ snd M.X X =
          snd L.X (L.X ⊗ X) ≫ snd L.X X := by simp [e]
      have hsndact : e ≫ snd M.X (M.X ⊗ X) ≫ t =
          snd L.X (L.X ⊗ X) ≫ a.smul := by
        simp only [e, tensorHom_snd_assoc, ht]
      simp only [comp_lift_assoc, Category.assoc, hfst, hsndfst, hsndsnd, hsndact]
      let g := fst L.X (L.X ⊗ X)
      let h := snd L.X (L.X ⊗ X) ≫ fst L.X X
      let x := snd L.X (L.X ⊗ X) ≫ snd L.X X
      change lift (lift (g ≫ f) (h ≫ f) ≫ μ[M.X]) x ≫ t =
        lift (g ≫ f) (snd L.X (L.X ⊗ X) ≫ a.smul) ≫ t
      have hm : lift (g ≫ f) (h ≫ f) ≫ μ[M.X] = (g * h) ≫ f :=
        (MonObj.mul_comp g h f).symm
      have hx : snd L.X (L.X ⊗ X) ≫ a.smul = lift h x ≫ a.smul := by
        rw [show lift h x = snd L.X (L.X ⊗ X) from lift_comp_fst_snd _]
      rw [hm, hx, hpoint, hpoint]
      letI := a
      exact mul_smul g h x }

  exact ⟨modObjOfSchemeAction a', ht⟩

end FppfDescent

section ProjectiveLinearAction

open Specs.RankOneFlag (Index plane planeBasis projectiveLine)
open Specs.ProjectiveSpaces (LineRepresentation)
open private modObjOfSchemeAction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SmoothOrbit
open private projectiveActionOfLinearRepresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.FlagSchemes
open private matrixPointEndHom matrixPoint_natural matrixTransport_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.PluckerEmbedding
open private overHom_ext_affine from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.ProjectiveSpaces
open private projection_eq_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.QuotientEmbedding

variable {k : Type u} [Field k] {L M PGL : GroupScheme k}

private theorem matrixTransport_scalar (R : TestAlgebra k) (a : Rˣ) (v : R ⊗[k] plane k) :
    PluckerEmbedding.matrixTransport (planeBasis k) R (Matrix.GeneralLinearGroup.scalar Index a) v =
      (a : R) • v := by
  let b := (planeBasis k).baseChange R
  change (Matrix.GeneralLinearGroup.toLin' b _).toLinearEquiv v = _
  rw [Matrix.GeneralLinearGroup.toLin'_apply, Matrix.GeneralLinearGroup.coe_scalar]
  have he : Matrix.scalar Index (a : R) *ᵥ b.repr v = (a : R) • ⇑(b.repr v) := by
    ext i
    exact Matrix.mulVec_diagonal _ _ _
  rw [he, map_smul]
  congr 1
  simpa only [Fintype.linearCombination_apply] using b.sum_repr v

private theorem map_matrixTransport_scalar (R : TestAlgebra k) (a : Rˣ)
    (N : Submodule R (R ⊗[k] plane k)) :
    N.map (PluckerEmbedding.matrixTransport (planeBasis k) R
      (Matrix.GeneralLinearGroup.scalar Index a)).toLinearMap = N := by
  apply le_antisymm
  · rintro v ⟨x, hx, rfl⟩
    exact (matrixTransport_scalar R a x).symm ▸ N.smul_mem (a : R) hx
  · intro v hv
    refine ⟨(↑a⁻¹ : R) • v, N.smul_mem _ hv, ?_⟩
    change PluckerEmbedding.matrixTransport (planeBasis k) R
      (Matrix.GeneralLinearGroup.scalar Index a) ((↑a⁻¹ : R) • v) = v
    rw [matrixTransport_scalar, smul_smul, Units.mul_inv, one_smul]

private theorem exists_projectiveLinearAction
    (em : (groupPointsFunctor k).obj M ≅ StandardGroups.multiplicativePoints k)
    (el : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k Index.{u})
    (s : M ⟶ L) (hs : IsClosedImmersion s.hom.hom.left)
    (hscalar : ∀ (R : TestAlgebra k) (a : Points M.X R),
      el.hom.app R (a ≫ s.hom.hom) = Matrix.GeneralLinearGroup.scalar Index (em.hom.app R a))
    (P : QuotientEmbedding.Presentation (⟨M, s, hs⟩ : ClosedSubgroup L))
    (q : L ⟶ PGL) (i : P.scheme ≅ PGL.X) (hi : P.projection ≫ i.hom = q.hom.hom) :
    ∃ b : ModObj PGL.X (projectiveLine k),
      Fppf.IsFppf q.hom.hom.left ∧
      ∀ (R : TestAlgebra k) (g : Points L.X R) (p : Points (projectiveLine k) R),
        (planeLine (lift (g ≫ q.hom.hom) p ≫ b.smul)).submodule =
          (planeLine p).submodule.map
            (PluckerEmbedding.matrixTransport (planeBasis k) R (el.hom.app R g)).toLinearMap := by
  let v := planeBasis k
  let ρ := planeRepresentation k
  let X := projectiveLine k
  let act := projectiveActionOfLinearRepresentation ρ
    (fun R g => PluckerEmbedding.matrixTransport v R (el.hom.app R g))
    (matrixPointEndHom v el) (fun _ _ => rfl) (by
      intro R T c g
      letI : Algebra R T := c.hom.toAlgebra
      letI : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' (c.hom.comp_algebraMap).symm
      change (PluckerEmbedding.matrixTransport v T (el.hom.app T (mapPoints c g))).toLinearMap.comp _ =
        LinearMap.comp _
          ((PluckerEmbedding.matrixTransport v R (el.hom.app R g)).toLinearMap.baseChange (↥T))
      rw [matrixPoint_natural el]
      exact matrixTransport_natural v c (el.hom.app R g))
  let a := modObjOfSchemeAction act.val
  have ha (R : TestAlgebra k) (g : Points L.X R) (p : Points X R) :
      (planeLine (lift g p ≫ a.smul)).submodule =
        (planeLine p).submodule.map
          (PluckerEmbedding.matrixTransport v R (el.hom.app R g)).toLinearMap :=
    act.property R g p
  have hfix (T : SchemeOver k) (c : T ⟶ M.X) (x : T ⟶ X) :
      lift (c ≫ s.hom.hom) x ≫ a.smul = x := by
    apply overHom_ext_affine
    intro R t
    rw [comp_lift_assoc, ← Category.assoc t c]
    apply planeLine_ext
    rw [ha, hscalar, map_matrixTransport_scalar]
  have hq : Fppf.IsFppf q.hom.hom.left := by
    rw [← hi, Over.comp_left]
    haveI : IsIso i.hom.left := (Over.forget _).map_isIso i.hom
    letI := P.flat
    letI := P.surjective
    letI := P.finitePresentation
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨b, hb⟩ := desc_groupAction q hq a (by
    intro T g h x hg
    have hg' : g ≫ P.projection = h ≫ P.projection := by
      rw [← cancel_mono i.hom, Category.assoc, Category.assoc, hi, hg]
    obtain ⟨c, hc⟩ := (projection_eq_iff P g h).mp hg'
    have hh : h = g * (c ≫ s.hom.hom) := by
      change c ≫ s.hom.hom = g⁻¹ * h at hc
      rw [hc, mul_inv_cancel_left]
    letI := a
    change g • x = h • x
    rw [hh, mul_smul]
    exact congrArg (g • ·) (hfix T c x).symm)
  refine ⟨b, hq, fun R g p => ?_⟩
  have he : lift (g ≫ q.hom.hom) p ≫ b.smul = lift g p ≫ a.smul := by
    simpa only [Category.assoc, lift_map_assoc, Category.comp_id] using
      congrArg (lift g p ≫ ·) hb
  rw [he, ha]

end ProjectiveLinearAction

section MatricesAndSections

open Specs.RankOneFlag (Index plane planeBasis projectiveLine HasCoordinates)
open private extendVector extendVector_coord from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.ProjectiveSpaces

variable {k : Type u} [Field k]

private abbrev firstIndex : Index.{u} := ⟨0⟩
private abbrev secondIndex : Index.{u} := otherIndex firstIndex

private theorem planeBasis_vector {R : TestAlgebra k} (i : Index.{u}) :
    vectorOfCoordinates R (affineCoordinates i 0) = (planeBasis k).baseChange R i := by
  let b := (planeBasis k).baseChange R
  apply b.ext_elem
  intro j
  change (b.equivFun (b.equivFun.symm (affineCoordinates i 0))) j = b.repr (b i) j
  rw [LinearEquiv.apply_symm_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp [affineCoordinates, eq_comm]

private theorem planeBasis_sum {R : TestAlgebra k} :
    vectorOfCoordinates R (affineCoordinates firstIndex 1) =
      (planeBasis k).baseChange R firstIndex + (planeBasis k).baseChange R secondIndex := by
  let b := (planeBasis k).baseChange R
  apply b.ext_elem
  intro j
  change (b.equivFun (b.equivFun.symm (affineCoordinates firstIndex 1))) j =
    b.repr (b firstIndex + b secondIndex) j
  rw [LinearEquiv.apply_symm_apply, map_add, Module.Basis.repr_self, Module.Basis.repr_self,
    Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
  by_cases hj : j = firstIndex
  · subst j
    simp [affineCoordinates, otherIndex_ne]
  · rw [eq_otherIndex hj]
    simp [affineCoordinates, otherIndex_ne, (otherIndex_ne firstIndex).symm]

private theorem span_smul_of_unit {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (a : Rˣ) (x : V) : Submodule.span R ({(a : R) • x} : Set V) = Submodule.span R {x} := by
  apply le_antisymm
  · exact (Submodule.span_singleton_le_iff_mem _ _).mpr (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x))
  · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    exact Submodule.mem_span_singleton.mpr ⟨(↑a⁻¹ : R), by rw [smul_smul, Units.inv_mul, one_smul]⟩

private theorem scalar_of_preserves_three {R : TestAlgebra k}
    (g : Matrix.GeneralLinearGroup Index.{u} R)
    (haxis : ∀ i : Index.{u},
      (planeLine (affinePoint R i 0)).submodule.map
        (PluckerEmbedding.matrixTransport (planeBasis k) R g).toLinearMap =
      (planeLine (affinePoint R i 0)).submodule)
    (hsum : (planeLine (affinePoint R firstIndex 1)).submodule.map
        (PluckerEmbedding.matrixTransport (planeBasis k) R g).toLinearMap =
      (planeLine (affinePoint R firstIndex 1)).submodule) :
    ∃ a : Rˣ, g = Matrix.GeneralLinearGroup.scalar Index a := by
  let b := (planeBasis k).baseChange R
  let e := PluckerEmbedding.matrixTransport (planeBasis k) R g
  have he (i : Index.{u}) : ∃ c : R, c • b i = e (b i) := by
    have h := haxis i
    rw [affinePoint_coordinates, planeBasis_vector, Submodule.map_span, Set.image_singleton] at h
    exact Submodule.mem_span_singleton.mp (h ▸ Submodule.mem_span_singleton_self _)
  choose c hc using he
  have hdiag : ∃ a : R, a • (b firstIndex + b secondIndex) = e (b firstIndex + b secondIndex) := by
    rw [affinePoint_coordinates, planeBasis_sum, Submodule.map_span, Set.image_singleton] at hsum
    exact Submodule.mem_span_singleton.mp (hsum ▸ Submodule.mem_span_singleton_self _)
  obtain ⟨a, ha⟩ := hdiag
  have hca (i : Index.{u}) : c i = a := by
    have hh := congrArg (b.coord i) ha
    rw [map_add e, ← hc firstIndex, ← hc secondIndex, map_smul, map_add, map_add,
      map_smul, map_smul] at hh
    by_cases hi : i = firstIndex
    · subst i
      simpa [b, Module.Basis.coord_apply, Finsupp.single_apply, otherIndex_ne] using hh.symm
    · rw [eq_otherIndex hi] at hh ⊢
      simpa [b, Module.Basis.coord_apply, Finsupp.single_apply, otherIndex_ne,
        (otherIndex_ne firstIndex).symm] using hh.symm
  have heq : e.toLinearMap = a • LinearMap.id := by
    apply b.ext
    intro i
    exact (hc i).symm.trans (congrArg (· • b i) (hca i))
  obtain ⟨y, hy⟩ := e.surjective (b firstIndex)
  have hunit : IsUnit a := by
    change e.toLinearMap y = b firstIndex at hy
    rw [heq] at hy
    have hh := congrArg (b.coord firstIndex) hy
    change b.coord firstIndex (a • y) = b.coord firstIndex (b firstIndex) at hh
    rw [map_smul, smul_eq_mul] at hh
    exact IsUnit.of_mul_eq_one _ (by simpa [Module.Basis.coord_apply] using hh)
  obtain ⟨u, hu⟩ := hunit
  refine ⟨u, (Matrix.GeneralLinearGroup.toLin' b).injective (Units.ext ?_)⟩
  change e.toLinearMap = (PluckerEmbedding.matrixTransport (planeBasis k) R _).toLinearMap
  rw [heq]
  ext y
  simp [matrixTransport_scalar, hu]

private def twoColumns {R : Type u} (v w : Index.{u} → R) : Matrix Index.{u} Index.{u} R :=
  fun i j => if j = firstIndex then v i else w i

private theorem twoColumns_det {R : Type u} [CommRing R] (v w : Index.{u} → R) :
    (twoColumns v w).det = v firstIndex * w secondIndex - w firstIndex * v secondIndex := by
  rw [← Matrix.det_submatrix_equiv_self (Equiv.ulift.symm : Fin 2 ≃ Index.{u}), Matrix.det_fin_two]
  rfl

private theorem vectors_eq_smul_of_det_zero {R : Type u} [Field R] {v w : Index.{u} → R}
    (hv : v ≠ 0) (hw : w ≠ 0) (hd : (twoColumns v w).det = 0) :
    ∃ a : Rˣ, w = (a : R) • v := by
  rw [twoColumns_det, sub_eq_zero] at hd
  have h (i : Index.{u}) (hi : v i ≠ 0) (he : ∀ j, v i * w j = w i * v j) :
      w = (w i / v i) • v := by
    funext j
    change w j = w i / v i * v j
    rw [div_mul_eq_mul_div, eq_div_iff hi, mul_comm (w j), he j]
  have hmul : ∃ a : R, w = a • v := by
    by_cases hv0 : v firstIndex = 0
    · have hv1 : v secondIndex ≠ 0 := by
        intro h0
        apply hv
        funext j
        by_cases hj : j = firstIndex
        · simpa [hj] using hv0
        · rwa [eq_otherIndex hj]
      refine ⟨w secondIndex / v secondIndex, h secondIndex hv1 (fun j => ?_)⟩
      by_cases hj : j = firstIndex
      · rw [hj, mul_comm (v secondIndex), mul_comm (w secondIndex)]
        exact hd.symm
      · rw [eq_otherIndex hj, mul_comm]
    · refine ⟨w firstIndex / v firstIndex, h firstIndex hv0 (fun j => ?_)⟩
      by_cases hj : j = firstIndex
      · rw [hj, mul_comm]
      · rw [eq_otherIndex hj]
        exact hd
  obtain ⟨a, ha⟩ := hmul
  have ha₀ : a ≠ 0 := fun h₀ => hw (by simpa [h₀] using ha)
  exact ⟨Units.mk0 a ha₀, ha⟩

private theorem nonzero_coordinates {R : TestAlgebra k} [Nontrivial R]
    (p : Points (projectiveLine k) R) {v : Index.{u} → R}
    (hv : HasCoordinates (planeRepresentation k) R p v) : v ≠ 0 := by
  intro h
  subst v
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  let P : PrimeSpectrum R := ⟨m, hm.isPrime⟩
  have e := (planeLine p).rank_one P
  change (planeLine p).submodule = Submodule.span R {vectorOfCoordinates R 0} at hv
  rw [show vectorOfCoordinates R 0 = 0 from map_zero ((planeBasis k).baseChange R).equivFun.symm,
    Submodule.span_zero_singleton] at hv
  rw [hv, Module.rankAtStalk_eq_zero_of_subsingleton] at e
  exact Nat.zero_ne_one e

private theorem isUnit_twoColumns_det {R : TestAlgebra k} {p q : Points (projectiveLine k) R}
    (hdist : ∀ (S : TestAlgebra k) [Nontrivial S] (a : R ⟶ S), mapPoints a p ≠ mapPoints a q)
    {v w : Index.{u} → R} (hv : HasCoordinates (planeRepresentation k) R p v)
    (hw : HasCoordinates (planeRepresentation k) R q w) : IsUnit (twoColumns v w).det := by
  by_contra hn
  obtain ⟨m, hm, hle⟩ := (Ideal.span {(twoColumns v w).det}).exists_le_maximal
    (fun ht => hn (Ideal.span_singleton_eq_top.mp ht))
  let S := CommAlgCat.of k (R ⧸ m)
  let a : R ⟶ S := CommAlgCat.ofHom (Ideal.Quotient.mkₐ k m)
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  letI : Field S := inferInstanceAs (Field (R ⧸ m))
  let v' : Index.{u} → S := fun i => a.hom (v i)
  let w' : Index.{u} → S := fun i => a.hom (w i)
  have hv' := hasCoordinates_change a hv
  have hw' := hasCoordinates_change a hw
  have hd : (twoColumns v' w').det = 0 := by
    have hh : a.hom (twoColumns v w).det = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (Set.mem_singleton _)))
    simpa only [twoColumns_det, map_sub, map_mul, v', w'] using hh
  obtain ⟨u, hu⟩ := vectors_eq_smul_of_det_zero
    (nonzero_coordinates _ hv') (nonzero_coordinates _ hw') hd
  apply hdist S a
  apply planeLine_ext
  change (planeLine (mapPoints a p)).submodule = Submodule.span S {vectorOfCoordinates S v'} at hv'
  change (planeLine (mapPoints a q)).submodule = Submodule.span S {vectorOfCoordinates S w'} at hw'
  change w' = (u : S) • v' at hu
  rw [hv', hw', hu,
    show vectorOfCoordinates S ((u : S) • v') = (u : S) • vectorOfCoordinates S v' from map_smul _ _ _,
    span_smul_of_unit]

private theorem transport_twoColumns {R : TestAlgebra k} (v w : Index.{u} → R)
    (h : IsUnit (twoColumns v w).det) (i : Index.{u}) :
    PluckerEmbedding.matrixTransport (planeBasis k) R
        (Matrix.GeneralLinearGroup.mk'' (twoColumns v w) h) ((planeBasis k).baseChange R i) =
      vectorOfCoordinates R (if i = firstIndex then v else w) := by
  let b := (planeBasis k).baseChange R
  change (Matrix.GeneralLinearGroup.toLin' b _).toLinearEquiv (b i) = _
  rw [Matrix.GeneralLinearGroup.toLin'_apply]
  change Fintype.linearCombination R b ((twoColumns v w) *ᵥ b.repr (b i)) = _
  rw [Module.Basis.repr_self, Finsupp.single_eq_pi_single, Matrix.mulVec_single_one]
  have he : (twoColumns v w).col i = if i = firstIndex then v else w := by
    funext j
    by_cases hi : i = firstIndex <;> simp [hi, twoColumns, Matrix.col]
  rw [he]
  change Fintype.linearCombination R b _ = b.equivFun.symm _
  rw [Module.Basis.equivFun_symm_apply, Fintype.linearCombination_apply]

end MatricesAndSections

section FrameOfThreeSections

open Specs.RankOneFlag (Index plane planeBasis projectiveLine HasCoordinates)

variable {k : Type u} [Field k] {R : TestAlgebra k}

private theorem twoColumns_mul_det {A : Type u} [CommRing A]
    (a b : A) (v w : Index.{u} → A) :
    (twoColumns (a • v) (b • w)).det = a * b * (twoColumns v w).det := by
  simp only [twoColumns_det, Pi.smul_apply, smul_eq_mul]
  ring

private theorem coordinates_of_third_column (v w z : Index.{u} → R) (i : Index.{u}) :
    (twoColumns z w).det * v i + (twoColumns v z).det * w i =
      (twoColumns v w).det * z i := by
  simp only [twoColumns_det]
  by_cases hi : i = firstIndex
  · rw [hi]
    ring
  · rw [eq_otherIndex hi]
    ring

private theorem frame_of_three_sections
    {p₀ p₁ p₂ : Points (projectiveLine k) R}
    (h₀₁ : ∀ (S : TestAlgebra k) [Nontrivial S] (a : R ⟶ S),
      mapPoints a p₀ ≠ mapPoints a p₁)
    (h₀₂ : ∀ (S : TestAlgebra k) [Nontrivial S] (a : R ⟶ S),
      mapPoints a p₀ ≠ mapPoints a p₂)
    (h₂₁ : ∀ (S : TestAlgebra k) [Nontrivial S] (a : R ⟶ S),
      mapPoints a p₂ ≠ mapPoints a p₁)
    {v w z : Index.{u} → R} (hv : HasCoordinates (planeRepresentation k) R p₀ v)
    (hw : HasCoordinates (planeRepresentation k) R p₁ w)
    (hz : HasCoordinates (planeRepresentation k) R p₂ z) :
    ∃ g : Matrix.GeneralLinearGroup Index.{u} R,
      let m := (PluckerEmbedding.matrixTransport (planeBasis k) R g).toLinearMap
      (planeLine (affinePoint R firstIndex 0)).submodule.map m = (planeLine p₀).submodule ∧
      (planeLine (affinePoint R secondIndex 0)).submodule.map m = (planeLine p₁).submodule ∧
      (planeLine (affinePoint R firstIndex 1)).submodule.map m = (planeLine p₂).submodule := by
  obtain ⟨d, hd⟩ := isUnit_twoColumns_det h₀₁ hv hw
  obtain ⟨d₀, hd₀⟩ := isUnit_twoColumns_det h₂₁ hz hw
  obtain ⟨d₁, hd₁⟩ := isUnit_twoColumns_det h₀₂ hv hz
  let a := d⁻¹ * d₀
  let b := d⁻¹ * d₁
  let v' : Index.{u} → R := (a : R) • v
  let w' : Index.{u} → R := (b : R) • w
  have hdet : IsUnit (twoColumns v' w').det := by
    rw [twoColumns_mul_det, ← hd]
    exact (a.isUnit.mul b.isUnit).mul d.isUnit
  let g := Matrix.GeneralLinearGroup.mk'' (twoColumns v' w') hdet
  have hvw : v' + w' = z := by
    funext i
    change (↑d⁻¹ : R) * ↑d₀ * v i + (↑d⁻¹ : R) * ↑d₁ * w i = z i
    rw [mul_assoc, mul_assoc, ← mul_add, hd₀, hd₁, coordinates_of_third_column, ← hd,
      ← mul_assoc, Units.inv_mul, one_mul]
  have hv' : PluckerEmbedding.matrixTransport (planeBasis k) R g
        ((planeBasis k).baseChange R firstIndex) = vectorOfCoordinates R v' := by
    simpa only [ite_true] using transport_twoColumns v' w' hdet (firstIndex : Index.{u})
  have hw' : PluckerEmbedding.matrixTransport (planeBasis k) R g
        ((planeBasis k).baseChange R secondIndex) = vectorOfCoordinates R w' := by
    simpa only [ite_eq_right (otherIndex_ne firstIndex)] using
      transport_twoColumns v' w' hdet (secondIndex : Index.{u})
  change (planeLine p₀).submodule = Submodule.span R {vectorOfCoordinates R v} at hv
  change (planeLine p₁).submodule = Submodule.span R {vectorOfCoordinates R w} at hw
  change (planeLine p₂).submodule = Submodule.span R {vectorOfCoordinates R z} at hz
  refine ⟨g, ?_, ?_, ?_⟩
  · rw [affinePoint_coordinates, planeBasis_vector, Submodule.map_span, Set.image_singleton, hv]
    change Submodule.span R (Set.singleton (PluckerEmbedding.matrixTransport (planeBasis k) R g
      ((planeBasis k).baseChange R firstIndex))) = _
    rw [hv', show vectorOfCoordinates R v' = (a : R) • vectorOfCoordinates R v from map_smul _ _ _]
    exact span_smul_of_unit _ _
  · rw [affinePoint_coordinates, planeBasis_vector, Submodule.map_span, Set.image_singleton, hw]
    change Submodule.span R (Set.singleton (PluckerEmbedding.matrixTransport (planeBasis k) R g
      ((planeBasis k).baseChange R secondIndex))) = _
    rw [hw', show vectorOfCoordinates R w' = (b : R) • vectorOfCoordinates R w from map_smul _ _ _]
    exact span_smul_of_unit _ _
  · rw [affinePoint_coordinates, planeBasis_sum, Submodule.map_span, Set.image_singleton, hz]
    change Submodule.span R (Set.singleton (PluckerEmbedding.matrixTransport (planeBasis k) R g
      ((planeBasis k).baseChange R firstIndex + (planeBasis k).baseChange R secondIndex))) = _
    rw [map_add, hv', hw', ← map_add, hvw]
    rfl

end FrameOfThreeSections

section ProjectiveAutomorphismComparison

open Specs.RankOneFlag (Index plane planeBasis projectiveLine lineOver lineBaseMap HasCoordinates)
open private projection_eq_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.QuotientEmbedding
open private overHom_ext_affine from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.ProjectiveSpaces

variable {k : Type u} [Field k] {PGL L M : GroupScheme k}
variable {R S : TestAlgebra k}

private theorem applyRelativeAut_ofAction (b : ModObj PGL.X (projectiveLine k))
    (g : Points PGL.X R) (a : R ⟶ S) (x : Points (projectiveLine k) S) :
    applyRelativeAut (automorphismsOfAction b R g) a x = lift (mapPoints a g) x ≫ b.smul := by
  change lift x ((testSpec k).map a.op) ≫
    (automorphismsOfAction b R g).asIso.hom.left ≫ fst _ _ = _
  rw [automorphismsOfAction_fst, comp_lift_assoc, lift_fst, lift_snd_assoc]

private theorem changeRelativeAut_ofAction (b : ModObj PGL.X (projectiveLine k))
    (a : R ⟶ S) (g : Points PGL.X R) :
    changeRelativeAut a (automorphismsOfAction b R g) =
      automorphismsOfAction b S (mapPoints a g) := by
  apply relativeAut_ext
  intro T d x
  rw [applyRelativeAut_changeAut, applyRelativeAut_ofAction, applyRelativeAut_ofAction]
  simp only [mapPoints, op_comp, Functor.map_comp, Category.assoc]

private theorem testSpec_fppf_comp {T : TestAlgebra k} (a : R ⟶ S) (b : S ⟶ T)
    (ha : Fppf.IsFppf ((testSpec k).map a.op).left)
    (hb : Fppf.IsFppf ((testSpec k).map b.op).left) :
    Fppf.IsFppf ((testSpec k).map (a ≫ b).op).left := by
  letI := ha.1
  letI := ha.2.1
  letI := ha.2.2
  letI := hb.1
  letI := hb.2.1
  letI := hb.2.2
  rw [op_comp, Functor.map_comp, Over.comp_left]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private theorem changeRelativeAut_injective {a : R ⟶ S}
    (ha : Fppf.IsFppf ((testSpec k).map a.op).left) :
    Function.Injective (changeRelativeAut a) := by
  let X := projectiveLine k
  let f := (testSpec k).map a.op
  have hid : Fppf.IsFppf (𝟙 X : X ⟶ X).left := ⟨inferInstance, inferInstance, inferInstance⟩
  have e : lineBaseMap a = (𝟙 X ⊗ₘ f) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [lineBaseMap, X, f]
    · simp [lineBaseMap, X, f]
  letI : Epi (lineBaseMap a) := fppf_epi _ (e.symm ▸ tensor_fppf (𝟙 X) f hid ha)
  intro F G hh
  apply Aut.ext
  apply Iso.ext
  apply Over.OverMorphism.ext
  apply (cancel_epi (lineBaseMap a)).mp
  rw [← changeRelativeAut_fac, ← changeRelativeAut_fac]
  exact congrArg (fun z : Aut (lineOver S) => z.asIso.hom.left ≫ lineBaseMap a) hh

private theorem mapPoints_compose {T : TestAlgebra k} (a : R ⟶ S) (d : S ⟶ T)
    {X : SchemeOver k} (x : Points X R) :
    mapPoints d (mapPoints a x) = mapPoints (a ≫ d) x := by
  simp only [mapPoints, op_comp, Functor.map_comp, Category.assoc]

private theorem mapPoints_identity {X : SchemeOver k} (x : Points X R) :
    mapPoints (𝟙 R) x = x := by
  change (testSpec k).map (𝟙 (op R)) ≫ x = x
  exact (congrArg (· ≫ x) ((testSpec k).map_id _)).trans (Category.id_comp x)

private theorem relativeAut_eq_of_three {f g : Aut (lineOver R)}
    (h₀ : applyRelativeAut f (𝟙 R) (affinePoint R firstIndex 0) =
      applyRelativeAut g (𝟙 R) (affinePoint R firstIndex 0))
    (h₁ : applyRelativeAut f (𝟙 R) (affinePoint R secondIndex 0) =
      applyRelativeAut g (𝟙 R) (affinePoint R secondIndex 0))
    (h₂ : applyRelativeAut f (𝟙 R) (affinePoint R firstIndex 1) =
      applyRelativeAut g (𝟙 R) (affinePoint R firstIndex 1)) : f = g := by
  have fix (x : Points (projectiveLine k) R)
      (h : applyRelativeAut f (𝟙 R) x = applyRelativeAut g (𝟙 R) x) :
      applyRelativeAut (g⁻¹ * f) (𝟙 R) x = x := by
    rw [applyRelativeAut_mul, h, ← applyRelativeAut_mul, inv_mul_cancel, applyRelativeAut_one]
  have hE : FixesEndpoints (g⁻¹ * f) := by
    intro i
    by_cases hi : i = firstIndex
    · rw [hi]
      exact fix _ h₀
    · rw [eq_otherIndex hi]
      exact fix _ h₁
  exact (inv_mul_eq_one.mp (relativeAut_eq_one_of_three hE firstIndex (fix _ h₂))).symm

private theorem triple_after_fppf (p₀ p₁ p₂ : Points (projectiveLine k) R) :
    ∃ (S : TestAlgebra k) (a : R ⟶ S) (v₀ v₁ v₂ : Index.{u} → S),
      Fppf.IsFppf ((testSpec k).map a.op).left ∧
      HasCoordinates (planeRepresentation k) S (mapPoints a p₀) v₀ ∧
      HasCoordinates (planeRepresentation k) S (mapPoints a p₁) v₁ ∧
      HasCoordinates (planeRepresentation k) S (mapPoints a p₂) v₂ := by
  obtain ⟨A, a, u, ha, _, hu⟩ := exists_fppf_coordinates p₀
  obtain ⟨B, b, v, hb, _, hv⟩ := exists_fppf_coordinates (mapPoints a p₁)
  obtain ⟨C, c, w, hc, _, hw⟩ := exists_fppf_coordinates (mapPoints (a ≫ b) p₂)
  have hu' := hasCoordinates_change (b ≫ c) hu
  have hv' := hasCoordinates_change c hv
  refine ⟨C, (a ≫ b) ≫ c, (fun i => (b ≫ c).hom (u i)), (fun i => c.hom (v i)), w,
    testSpec_fppf_comp _ _ (testSpec_fppf_comp a b ha hb) hc, ?_, ?_, ?_⟩
  · simpa only [mapPoints_compose, Category.assoc] using hu'
  · simpa only [mapPoints_compose, Category.assoc] using hv'
  · simpa only [mapPoints_compose] using hw

variable (el : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k Index.{u})
variable (q : L ⟶ PGL) (b : ModObj PGL.X (projectiveLine k))
variable (hact : ∀ (R : TestAlgebra k) (g : Points L.X R) (p : Points (projectiveLine k) R),
  (planeLine (lift (g ≫ q.hom.hom) p ≫ b.smul)).submodule =
    (planeLine p).submodule.map (PluckerEmbedding.matrixTransport (planeBasis k) R (el.hom.app R g)).toLinearMap)

include hact in
private theorem aut_fppf_matrix_lift (F : Aut (lineOver R)) :
    ∃ (S : TestAlgebra k) (a : R ⟶ S) (g : Points L.X S),
      Fppf.IsFppf ((testSpec k).map a.op).left ∧
      automorphismsOfAction b S (g ≫ q.hom.hom) = changeRelativeAut a F := by
  let p₀ := affinePoint R firstIndex 0
  let p₁ := affinePoint R secondIndex 0
  let p₂ := affinePoint R firstIndex 1
  let p (x : Points (projectiveLine k) R) := applyRelativeAut F (𝟙 R) x
  obtain ⟨S, a, v₀, v₁, v₂, ha, h₀, h₁, h₂⟩ := triple_after_fppf (p p₀) (p p₁) (p p₂)
  have hp (T : TestAlgebra k) (c : R ⟶ T) (x : Points (projectiveLine k) R) :
      mapPoints c (p x) = applyRelativeAut F c (mapPoints c x) := by
    simp only [p, applyRelativeAut_change, Category.id_comp]
  have hchart (T : TestAlgebra k) (c : S ⟶ T) (j : Index.{u}) (z : R) :
      mapPoints c (mapPoints a (p (affinePoint R j z))) =
        applyRelativeAut F (a ≫ c) (affinePoint T j ((a ≫ c).hom z)) := by
    rw [mapPoints_compose, hp, affinePoint_change]
  have h₀₁ (T : TestAlgebra k) [Nontrivial T] (c : S ⟶ T) :
      mapPoints c (mapPoints a (p p₀)) ≠ mapPoints c (mapPoints a (p p₁)) := by
    change mapPoints c (mapPoints a (p (affinePoint R firstIndex 0))) ≠
      mapPoints c (mapPoints a (p (affinePoint R secondIndex 0)))
    rw [hchart, hchart, map_zero]
    exact fun h => affinePoint_ne_opposite_zero (R := T) firstIndex 0
      (applyRelativeAut_injective F (a ≫ c) h)
  have h₀₂ (T : TestAlgebra k) [Nontrivial T] (c : S ⟶ T) :
      mapPoints c (mapPoints a (p p₀)) ≠ mapPoints c (mapPoints a (p p₂)) := by
    change mapPoints c (mapPoints a (p (affinePoint R firstIndex 0))) ≠
      mapPoints c (mapPoints a (p (affinePoint R firstIndex 1)))
    rw [hchart, hchart, map_zero, map_one]
    exact fun h => zero_ne_one (α := T)
      (affinePoint_injective T firstIndex (applyRelativeAut_injective F (a ≫ c) h))
  have h₂₁ (T : TestAlgebra k) [Nontrivial T] (c : S ⟶ T) :
      mapPoints c (mapPoints a (p p₂)) ≠ mapPoints c (mapPoints a (p p₁)) := by
    change mapPoints c (mapPoints a (p (affinePoint R firstIndex 1))) ≠
      mapPoints c (mapPoints a (p (affinePoint R secondIndex 0)))
    rw [hchart, hchart, map_one, map_zero]
    exact fun h => affinePoint_ne_opposite_zero (R := T) firstIndex 1
      (applyRelativeAut_injective F (a ≫ c) h)
  obtain ⟨m, hm₀, hm₁, hm₂⟩ := frame_of_three_sections h₀₁ h₀₂ h₂₁ h₀ h₁ h₂
  let g : Points L.X S := el.inv.app S m
  have hg : el.hom.app S g = m := by
    exact ConcreteCategory.congr_hom ((Iso.inv_hom_id_app el S)) m
  refine ⟨S, a, g, ha, relativeAut_eq_of_three ?_ ?_ ?_⟩
  · rw [applyRelativeAut_ofAction, applyRelativeAut_changeAut, Category.comp_id, mapPoints_identity]
    apply planeLine_ext
    rw [hact, hg]
    simpa only [hp, p₀, affinePoint_change, map_zero] using hm₀
  · rw [applyRelativeAut_ofAction, applyRelativeAut_changeAut, Category.comp_id, mapPoints_identity]
    apply planeLine_ext
    rw [hact, hg]
    simpa only [hp, p₁, affinePoint_change, map_zero] using hm₁
  · rw [applyRelativeAut_ofAction, applyRelativeAut_changeAut, Category.comp_id, mapPoints_identity]
    apply planeLine_ext
    rw [hact, hg]
    simpa only [hp, p₂, affinePoint_change, map_one] using hm₂

variable (q_lifts : ∀ {R : TestAlgebra k} (g : Points PGL.X R),
  ∃ (S : TestAlgebra k) (a : R ⟶ S) (m : Points L.X S),
    Fppf.IsFppf ((testSpec k).map a.op).left ∧ m ≫ q.hom.hom = mapPoints a g)

include hact q_lifts in
private theorem projectiveAction_injective
    (em : (groupPointsFunctor k).obj M ≅ StandardGroups.multiplicativePoints k)
    (s : M ⟶ L) (hs : IsClosedImmersion s.hom.hom.left)
    (hscalar : ∀ (R : TestAlgebra k) (a : Points M.X R),
      el.hom.app R (a ≫ s.hom.hom) = Matrix.GeneralLinearGroup.scalar Index (em.hom.app R a))
    (P : QuotientEmbedding.Presentation (⟨M, s, hs⟩ : ClosedSubgroup L))
    (i : P.scheme ≅ PGL.X) (hi : P.projection ≫ i.hom = q.hom.hom) :
    Function.Injective (automorphismsOfAction b R) := by
  intro g g' e
  obtain ⟨S, a, u, ha, hu⟩ := q_lifts g
  obtain ⟨T, c, v, hc, hv⟩ := q_lifts (mapPoints a g')
  let u' := mapPoints c u
  let d : Points L.X T := u'⁻¹ * v
  have hu' : u' ≫ q.hom.hom = mapPoints (a ≫ c) g := by
    rw [← mapPoints_compose, ← hu]
    change ((testSpec k).map c.op ≫ u) ≫ q.hom.hom =
      (testSpec k).map c.op ≫ u ≫ q.hom.hom
    exact Category.assoc _ _ _
  have hv' : v ≫ q.hom.hom = mapPoints (a ≫ c) g' := hv.trans (mapPoints_compose a c g')
  have e' : automorphismsOfAction b T (u' ≫ q.hom.hom) =
      automorphismsOfAction b T (v ≫ q.hom.hom) := by
    rw [hu', hv', ← changeRelativeAut_ofAction, ← changeRelativeAut_ofAction, e]
  have hOne : automorphismsOfAction b T (d ≫ q.hom.hom) = 1 := by
    rw [show d = u'⁻¹ * v from rfl, MonObj.mul_comp, GrpObj.inv_comp, map_mul, map_inv,
      e', inv_mul_cancel]
  have hd (x : Points (projectiveLine k) T) : lift (d ≫ q.hom.hom) x ≫ b.smul = x := by
    have h := congrArg (fun z : Aut (lineOver T) => applyRelativeAut z (𝟙 T) x) hOne
    simpa only [applyRelativeAut_one, applyRelativeAut_ofAction, mapPoints_identity] using h
  obtain ⟨t, ht⟩ := scalar_of_preserves_three (el.hom.app T d)
    (fun j => by rw [← hact, hd]) (by rw [← hact, hd])
  let w : Points M.X T := em.inv.app T t
  have hd' : w ≫ s.hom.hom = d := by
    apply (ConcreteCategory.bijective_of_isIso (el.hom.app T)).1
    rw [hscalar, ht]
    congr 1
    exact ConcreteCategory.congr_hom ((Iso.inv_hom_id_app em T)) t
  have hP : u' ≫ P.projection = v ≫ P.projection :=
    (projection_eq_iff P u' v).mpr ⟨w, hd'⟩
  have he : mapPoints (a ≫ c) g = mapPoints (a ≫ c) g' := by
    calc
      _ = u' ≫ q.hom.hom := hu'.symm
      _ = (u' ≫ P.projection) ≫ i.hom :=
        (congrArg (u' ≫ ·) hi.symm).trans (Category.assoc u' P.projection i.hom).symm
      _ = (v ≫ P.projection) ≫ i.hom := congrArg (· ≫ i.hom) hP
      _ = v ≫ q.hom.hom := by rw [Category.assoc, hi]
      _ = _ := hv'
  letI := fppf_epi ((testSpec k).map (a ≫ c).op) (testSpec_fppf_comp a c ha hc)
  exact (cancel_epi ((testSpec k).map (a ≫ c).op)).mp he

include hact in
private theorem projectiveAction_surjective
    (hinj : ∀ (R : TestAlgebra k), Function.Injective (automorphismsOfAction b R)) :
    Function.Surjective (automorphismsOfAction b R) := by
  intro F
  obtain ⟨S, a, m, ha, hm⟩ := aut_fppf_matrix_lift el q b hact F
  let p := m ≫ q.hom.hom
  obtain ⟨g, hg⟩ := exists_desc_of_fppf ((testSpec k).map a.op) ha p (by
    intro Y u v huv
    apply overHom_ext_affine
    intro T w
    let FF := algSpec.fullyFaithful (R := CommRingCat.of k)
    let c : S ⟶ T := (FF.preimage (w ≫ u)).unop
    let d : S ⟶ T := (FF.preimage (w ≫ v)).unop
    have hc : (testSpec k).map c.op = w ≫ u := FF.map_preimage _
    have hd : (testSpec k).map d.op = w ≫ v := FF.map_preimage _
    have hcd : a ≫ c = a ≫ d := by
      apply Quiver.Hom.op_inj
      apply FF.map_injective
      simp only [op_comp, Functor.map_comp, hc, hd, Category.assoc, huv]
    suffices e : mapPoints c p = mapPoints d p by
      simpa only [mapPoints, hc, hd, Category.assoc] using e
    apply hinj T
    rw [← changeRelativeAut_ofAction, ← changeRelativeAut_ofAction, hm]
    apply relativeAut_ext
    intro A r x
    rw [applyRelativeAut_changeAut, applyRelativeAut_changeAut, applyRelativeAut_changeAut,
      applyRelativeAut_changeAut, ← Category.assoc a c r, ← Category.assoc a d r, hcd])
  refine ⟨g, changeRelativeAut_injective ha ?_⟩
  rw [changeRelativeAut_ofAction, show mapPoints a g = p from hg]
  exact hm

end ProjectiveAutomorphismComparison

/-- The scalar fppf quotient represents the full projective-line automorphism functor. -/
theorem projectiveLineAutomorphisms : Specs.RankOneFlag.ProjectiveLineAutomorphisms.{u} := by
  intro k _
  obtain ⟨hm, hl, h⟩ := HomogeneousQuotient.projectiveLinearQuotient k Specs.RankOneFlag.Index
  letI := hm.hopf
  letI := hl.hopf
  obtain ⟨em, el, s, hs, hscalar, hn, P, PGL, q, i, hP, hk, hi⟩ := h
  obtain ⟨b, hq, hact⟩ := exists_projectiveLinearAction em el s hs hscalar P q i hi
  letI : IsAffine (StandardGroups.spectrum k
      (StandardGroups.GLCoordinates k Specs.RankOneFlag.Index)).val.X.left :=
    (StandardGroups.spectrum k (StandardGroups.GLCoordinates k Specs.RankOneFlag.Index)).property.1
  letI : IsAffine PGL.val.X.left := PGL.property.1
  have lifts {R : TestAlgebra k} (g : Points PGL.val.X R) :=
    exists_fppf_lift_of_affine_fppf q.hom.hom inferInstance hq g
  have hinj (R : TestAlgebra k) : Function.Injective (automorphismsOfAction b R) :=
    projectiveAction_injective el q b hact (@lifts) em s hs hscalar P i hi
  let e (R : TestAlgebra k) :=
    MulEquiv.ofBijective (automorphismsOfAction b R) ⟨hinj R, projectiveAction_surjective el q b hact hinj⟩
  exact ⟨hm, hl, em, el, s, hs, hscalar, hn, P, PGL, q, i, b, planeRepresentation k, e,
    hP, hk, hi, fun _ _ a g => automorphismsOfAction_natural b a g,
    fun _ g => automorphismsOfAction_fst b g, hact, @lifts, fun _ p => exists_fppf_coordinates p⟩


section AffinePuncture


open TopologicalSpace

private theorem smooth_domain_normal (k A : Type u) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [IsNoetherianRing A] [Algebra.Smooth k A] :
    AdvCommAlg.Normality.IsNormal A := by
  intro p
  refine ⟨inferInstance, ?_⟩
  obtain ⟨r, hr, n, alg, _, hEt⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := p.asIdeal)
  let P := MvPolynomial (Fin n) k
  let B := Localization.Away r
  letI : Algebra P B := alg
  letI : Algebra.IsStandardEtale P B := hEt
  have hP : AdvCommAlg.Normality.IsNormal P := by
    intro q
    exact ⟨inferInstance, isIntegrallyClosed_of_isLocalization (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl
      (fun x hx => mem_nonZeroDivisors_iff_ne_zero.mpr (fun he => hx (he ▸ q.asIdeal.zero_mem)))⟩
  obtain ⟨_, hb⟩ := AdvCommAlg.Normality.etale_normal_ascent P B hP
  have hd : Disjoint (Submonoid.powers r : Set A) (p.asIdeal : Set A) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hr
  let q := p.asIdeal.map (algebraMap A B)
  letI : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers r) B p.asIdeal p.isPrime hd
  let L := Localization.AtPrime q
  have hcomap : q.comap (algebraMap A B) = p.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers r) B p.isPrime hd
  letI : IsLocalization.AtPrime L (q.comap (algebraMap A B)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (.powers r) L q
  have hm : p.asIdeal.primeCompl = (q.comap (algebraMap A B)).primeCompl := by
    ext x
    change (x ∉ p.asIdeal) ↔ (x ∉ q.comap (algebraMap A B))
    rw [hcomap]
  letI : IsLocalization.AtPrime L p.asIdeal := by
    change IsLocalization p.asIdeal.primeCompl L
    rw [hm]
    infer_instance
  letI : IsIntegrallyClosed L := (hb ⟨q, inferInstance⟩).2
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv p.asIdeal.primeCompl L (Localization.AtPrime p.asIdeal)).toRingEquiv

/-- Removing a closed point of height at least two from a normal affine
scheme leaves global sections unchanged, so the resulting open is not affine. -/
private theorem height_le_one_of_affine_puncture (A : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] (hA : AdvCommAlg.Normality.IsNormal A)
    (p : PrimeSpectrum A) (W : Opens (PrimeSpectrum A))
    (hV : (W : Set (PrimeSpectrum A)) = {p}ᶜ)
    (ha : IsAffineOpen (show (Spec (CommRingCat.of A)).Opens from W)) :
    p.asIdeal.height ≤ 1 := by
  by_contra! hp
  let X := Spec (CommRingCat.of A)
  let V : X.Opens := W
  let B := (Spec.structureSheaf A).1.obj (op W)
  let f := X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
  have hrest :
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f) =
        CommRingCat.ofHom (algebraMap A B) := by
    rfl
  have hbij := AdvCommAlg.Normality.codimensionTwo_restriction_bijective A hA W
    (fun q hq => by
      change q ∈ (W : Set (PrimeSpectrum A))
      rw [hV, Set.mem_compl_iff, Set.mem_singleton_iff]
      rintro rfl
      exact hp.not_ge hq)
  letI : IsIso ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f) := by
    rw [hrest]
    exact (ConcreteCategory.isIso_iff_bijective
      (CommRingCat.ofHom (algebraMap A B))).2 hbij
  letI : IsIso f := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (CommRingCat.of A)).inv f
  haveI : IsIso V.ι := by
    have h : V.ι = ha.isoSpec.hom ≫ Spec.map f ≫ X.isoSpec.inv := by
      rw [← Category.assoc, IsAffineOpen.isoSpec_hom,
        Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top, Category.assoc]
      rw [show X.toSpecΓ = X.isoSpec.hom from rfl, Iso.hom_inv_id, Category.comp_id]
    rw [h]
    infer_instance
  have hsur : Surjective V.ι := inferInstance
  obtain ⟨x, hx⟩ := hsur.surj p
  have hm : p ∈ (W : Set (PrimeSpectrum A)) := by
    change p ∈ (V : Set X)
    rw [← Scheme.Opens.range_ι]
    exact ⟨x, hx⟩
  exact (show p ∉ ({p}ᶜ : Set (PrimeSpectrum A)) by simp) (hV ▸ hm)


/-- At a rational point of height one of a normal affine domain, the
augmentation ideal modulo its square has dimension one over the field. -/
private theorem cotangent_finrank_one_at_rational_height_one {k A : Type u}
    [Field k] [CommRing A] [IsDomain A] [IsNoetherianRing A] [Algebra k A]
    (hA : AdvCommAlg.Normality.IsNormal A) (ε : A →ₐ[k] k)
    (hdim : (RingHom.ker ε.toRingHom).height = 1) :
    Module.finrank k (RingHom.ker ε.toRingHom).Cotangent = 1 := by
  let I := RingHom.ker ε.toRingHom
  have he : Function.Surjective ε := fun t => ⟨algebraMap k A t, AlgHom.commutes ε t⟩
  letI : I.IsMaximal := RingHom.ker_isMaximal_of_surjective ε.toRingHom he
  let L := Localization.AtPrime I
  let J := IsLocalRing.maximalIdeal L
  letI : IsIntegrallyClosed L := (hA ⟨I, inferInstance⟩).2
  have hd : ringKrullDim L = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height I, show I.height = 1 from hdim]
    rfl
  have hn : ¬ IsField L := fun h => (show (0 : WithBot ℕ∞) ≠ 1 by decide)
    ((ringKrullDim_eq_zero_of_isField h).symm.trans hd)
  letI : Ring.KrullDimLE 1 L := Ring.krullDimLE_iff.mpr hd.le
  have hle : Ring.DimensionLEOne L :=
    ⟨fun h₁ h₂ => (Ring.krullDimLE_one_iff_of_isPrime_bot.mp
      (inferInstance : Ring.KrullDimLE 1 L)) _ h₁ h₂⟩
  letI : IsDedekindDomain L := (isDedekindDomain_iff L (FractionRing L)).mpr
    ⟨inferInstance, inferInstance, hle, (isIntegrallyClosed_iff _).mp inferInstance⟩
  letI : IsDiscreteValuationRing L :=
    ((IsDiscreteValuationRing.TFAE L hn).out 3 1).mp (inferInstance : IsDedekindDomain L)
  let f : A →ₐ[k] L := (Algebra.ofId A L).restrictScalars k
  have hp₁ : J.comap f.toRingHom = I := IsLocalization.AtPrime.under_maximalIdeal L I
  have hp₂ : (J ^ 2).comap f.toRingHom = I ^ 2 :=
    IsLocalization.AtPrime.under_maximalIdeal_pow I L 2
  let hl : I ≤ J.comap f := hp₁.ge
  let φ := Ideal.mapCotangent I J f hl
  have hi : Function.Injective φ := by
    intro x y h
    obtain ⟨a, rfl⟩ := I.toCotangent_surjective x
    obtain ⟨b, rfl⟩ := I.toCotangent_surjective y
    rw [Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent, Ideal.toCotangent_eq] at h
    apply (Ideal.toCotangent_eq _).mpr
    have hn' : f (a - b : A) ∈ J ^ 2 := by
      rw [map_sub]
      exact h
    change (a - b : A) ∈ (J ^ 2).comap f.toRingHom at hn'
    rwa [hp₂] at hn'
  have hs : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := J.toCotangent_surjective y
    let b := IsLocalization.AtPrime.equivQuotMaximalIdealPow I L 2
    obtain ⟨a, ha⟩ := (b.surjective.comp Ideal.Quotient.mk_surjective)
      (Ideal.Quotient.mk (J ^ 2) (x : L))
    change Ideal.Quotient.mk (J ^ 2) (f a) = _ at ha
    have ha₂ : f a - x ∈ J ^ 2 := Ideal.Quotient.eq.mp ha
    have haJ : f a ∈ J := by
      have hz := J.add_mem (Ideal.pow_le_self (by decide : 2 ≠ 0) ha₂) x.property
      simpa only [sub_add_cancel] using hz
    have haI : a ∈ I := by
      change a ∈ J.comap f.toRingHom at haJ
      rwa [hp₁] at haJ
    refine ⟨I.toCotangent ⟨a, haI⟩, ?_⟩
    rw [Ideal.mapCotangent_toCotangent]
    exact (Ideal.toCotangent_eq _).mpr ha₂
  let b : I.Cotangent ≃ₗ[k] IsLocalRing.CotangentSpace L := LinearEquiv.ofBijective φ ⟨hi, hs⟩
  let e : IsLocalRing.ResidueField L ≃ₐ[k] k :=
    ((IsLocalization.AtPrime.equivQuotMaximalIdeal I L).restrictScalars k).symm.trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := ε) he)
  have hr : Module.finrank k (IsLocalRing.ResidueField L) = 1 :=
    e.toLinearEquiv.finrank_eq.trans (Module.finrank_self k)
  letI : IsScalarTower k (IsLocalRing.ResidueField L) (IsLocalRing.CotangentSpace L) := by
    apply IsScalarTower.of_algebraMap_smul
    intro a x
    rw [IsScalarTower.algebraMap_apply k L]
    exact (IsScalarTower.algebraMap_smul (A := IsLocalRing.ResidueField L)
      (algebraMap k L a) x).trans (IsScalarTower.algebraMap_smul (A := L) a x)
  rw [b.finrank_eq, ← Module.finrank_mul_finrank k (IsLocalRing.ResidueField L),
    hr, one_mul]
  exact IsLocalRing.finrank_CotangentSpace_eq_one L

end AffinePuncture

section AffineChartsAndFixedPoints

open Specs.SmoothOrbit (orbitMap orbitSet)
open TopologicalSpace

variable {k : Type u} [Field k]

private def sectionSupport {X : SchemeOver k} (x : 𝟙_ (SchemeOver k) ⟶ X) : X.left :=
  x.left (IsLocalRing.closedPoint k)

private theorem sectionSupport_comp {X Y : SchemeOver k} (x : 𝟙_ (SchemeOver k) ⟶ X)
    (f : X ⟶ Y) : sectionSupport (x ≫ f) = f.left (sectionSupport x) :=
  rfl

private theorem proper_affine_discrete (X : SchemeOver k)
    (hs : IsProper X.hom) (ha : IsAffine X.left) : DiscreteTopology X.left := by
  haveI : IsAffine X.left := ha
  letI : IsProper X.hom := hs
  letI : IsFinite X.hom := IsFinite.iff_isProper_and_isAffineHom.mpr ⟨hs, inferInstance⟩
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr ha
  let V := (testSpec k).obj (op A.unop)
  haveI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have hfin : IsFinite V.hom := by
    rw [← Over.w e.hom]
    infer_instance
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k A.unop))) at hfin
  letI : Module.Finite k A.unop := RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp hfin)
  letI : IsArtinianRing A.unop := IsArtinianRing.of_finite k A.unop
  haveI : DiscreteTopology V.left := inferInstanceAs (DiscreteTopology (PrimeSpectrum A.unop))
  haveI : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
  exact DiscreteTopology.of_continuous_injective e.inv.left.continuous e.inv.left.homeomorph.injective

private theorem closed_inside_affine_open {X V : SchemeOver k} (j : V ⟶ X)
    [IsOpenImmersion j.left] (hV : IsAffine V.left)
    (Z : X.left.IdealSheafData) (hZ : Set.range Z.subschemeι ⊆ Set.range j.left) :
    IsAffine Z.subscheme := by
  let f := IsOpenImmersion.lift j.left Z.subschemeι hZ
  have hf : f ≫ j.left = Z.subschemeι := IsOpenImmersion.lift_fac _ _ _
  have hp : IsPullback f (𝟙 _) j.left Z.subschemeι :=
    IsPullback.of_vert_isIso_mono ⟨by rw [Category.id_comp, hf]⟩
  letI : IsClosedImmersion f := MorphismProperty.of_isPullback hp.flip inferInstance
  letI : IsAffine V.left := hV
  exact isAffine_of_isAffineHom f

private theorem orbit_closure_in_closed_support {T : GroupScheme k} {X : SchemeOver k}
    (a : ModObj T.X X) (x : 𝟙_ (SchemeOver k) ⟶ X)
    (liftT : ∀ t ∈ closedPoints T.X.left,
      ∃ y : 𝟙_ (SchemeOver k) ⟶ T.X, sectionSupport y = t)
    [JacobsonSpace T.X.left] (S : Set X.left) (hS : IsClosed S)
    (hx : ∀ g : 𝟙_ (SchemeOver k) ⟶ T.X, sectionSupport (lift g x ≫ a.smul) ∈ S) :
    closure (orbitSet a x) ⊆ S := by
  apply hS.closure_subset_iff.mpr
  let f := orbitMap a x
  have hpre : closedPoints T.X.left ⊆ f.left ⁻¹' S := by
    intro t ht
    obtain ⟨g, rfl⟩ := liftT t ht
    have hg : g ≫ f = lift g x ≫ a.smul := by
      unfold f orbitMap
      rw [← Category.assoc]
      congr 1
      apply CartesianMonoidalCategory.hom_ext
      · simp
      · simp [show toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ from Subsingleton.elim _ _]
    rw [Set.mem_preimage, ← sectionSupport_comp, hg]
    exact hx g
  have h := (hS.preimage f.left.continuous).closure_subset_iff.mpr hpre
  rw [closure_closedPoints] at h
  rintro _ ⟨t, rfl⟩
  exact h (Set.mem_univ t)

private theorem fixed_sections_in_closed_support {T : GroupScheme k} {X : SchemeOver k}
    (a : ModObj T.X X)
    (liftT : ∀ t ∈ closedPoints T.X.left,
      ∃ y : 𝟙_ (SchemeOver k) ⟶ T.X, sectionSupport y = t)
    (liftX : ∀ x ∈ closedPoints X.left,
      ∃ y : 𝟙_ (SchemeOver k) ⟶ X, sectionSupport y = x)
    [JacobsonSpace T.X.left] [JacobsonSpace X.left]
    (hfix : ∀ x : 𝟙_ (SchemeOver k) ⟶ X,
      ∃ y : 𝟙_ (SchemeOver k) ⟶ X,
        sectionSupport y ∈ closure (orbitSet a x) ∧ IsFixedBy a.smul y)
    {S : Set X.left} (hS : IsClosed S) (hne : S.Nonempty)
    (hst : ∀ (t : 𝟙_ (SchemeOver k) ⟶ T.X) (x : 𝟙_ (SchemeOver k) ⟶ X),
      sectionSupport x ∈ S → sectionSupport (lift t x ≫ a.smul) ∈ S) :
    ∃ y : 𝟙_ (SchemeOver k) ⟶ X, sectionSupport y ∈ S ∧ IsFixedBy a.smul y := by
  obtain ⟨p, hp, hp'⟩ := nonempty_inter_closedPoints hne hS.isLocallyClosed
  obtain ⟨x, rfl⟩ := liftX p hp'
  obtain ⟨y, hy, hf⟩ := hfix x
  exact ⟨y, orbit_closure_in_closed_support a x liftT S hS (fun t => hst t x hp) hy, hf⟩

/-- Two invariant affine opens containing the two fixed points of a proper
scheme cover it. If the first omits the second point, its complement is that
point. The fixed point hypothesis is obtained by applying the Borel fixed
point theorem to orbit closures. -/
private theorem range_eq_compl_of_two_fixed
    {T : GroupScheme k} [ConnectedSpace T.X.left] [JacobsonSpace T.X.left]
    {X U V : SchemeOver k} [IsProper X.hom] [JacobsonSpace X.left]
    (a : ModObj T.X X)
    (liftT : ∀ t ∈ closedPoints T.X.left,
      ∃ y : 𝟙_ (SchemeOver k) ⟶ T.X, sectionSupport y = t)
    (liftX : ∀ x ∈ closedPoints X.left,
      ∃ y : 𝟙_ (SchemeOver k) ⟶ X, sectionSupport y = x)
    (hfix : ∀ x : 𝟙_ (SchemeOver k) ⟶ X,
      ∃ y : 𝟙_ (SchemeOver k) ⟶ X,
        sectionSupport y ∈ closure (orbitSet a x) ∧ IsFixedBy a.smul y)
    (p q : 𝟙_ (SchemeOver k) ⟶ X)
    (hclass : ∀ x : 𝟙_ (SchemeOver k) ⟶ X, IsFixedBy a.smul x → x = p ∨ x = q)
    (i : U ⟶ X) (j : V ⟶ X) [IsOpenImmersion i.left] [IsOpenImmersion j.left]
    (hV : IsAffine V.left)
    (hp : sectionSupport p ∈ Set.range i.left) (hq : sectionSupport q ∈ Set.range j.left)
    (hqi : sectionSupport q ∉ Set.range i.left)
    (hi : ∀ (t : 𝟙_ (SchemeOver k) ⟶ T.X) (x : 𝟙_ (SchemeOver k) ⟶ X),
      sectionSupport (lift t x ≫ a.smul) ∈ Set.range i.left ↔ sectionSupport x ∈ Set.range i.left)
    (hj : ∀ (t : 𝟙_ (SchemeOver k) ⟶ T.X) (x : 𝟙_ (SchemeOver k) ⟶ X),
      sectionSupport (lift t x ≫ a.smul) ∈ Set.range j.left ↔ sectionSupport x ∈ Set.range j.left) :
    Set.range i.left = ({sectionSupport q} : Set X.left)ᶜ := by
  let S := (Set.range i.left)ᶜ
  let S' := (Set.range j.left)ᶜ
  have hS : IsClosed S := i.left.isOpenEmbedding.isOpen_range.isClosed_compl
  have hS' : IsClosed S' := j.left.isOpenEmbedding.isOpen_range.isClosed_compl
  have huv : S ⊆ Set.range j.left := by
    intro x hx
    by_contra h
    obtain ⟨r, hr, hr'⟩ := fixed_sections_in_closed_support a liftT liftX hfix
      (hS.inter hS') ⟨x, hx, h⟩
      (fun t y hy => ⟨fun h => hy.1 ((hi t y).mp h), fun h => hy.2 ((hj t y).mp h)⟩)
    rcases hclass r hr' with rfl | rfl
    · exact hr.1 hp
    · exact hr.2 hq
  let Z := Scheme.IdealSheafData.vanishingIdeal (⟨S, hS⟩ : Closeds X.left)
  let iZ := Z.subschemeι
  have hz : Set.range iZ = S := by
    change Set.range Z.subschemeι = _
    rw [Scheme.IdealSheafData.range_subschemeι]
    unfold Z Scheme.IdealSheafData.vanishingIdeal
    rw [Scheme.IdealSheafData.coe_support_mkOfMemSupportIff]
    rfl
  have hA : IsAffine Z.subscheme := closed_inside_affine_open j hV Z (hz ▸ huv)
  let Y : SchemeOver k := Over.mk (iZ ≫ X.hom)
  letI : IsProper Y.hom := inferInstanceAs (IsProper (iZ ≫ X.hom))
  have hdisc := proper_affine_discrete Y inferInstance hA
  letI : DiscreteTopology Z.subscheme := hdisc
  letI : DiscreteTopology Y.left := hdisc
  have hyclosed (z : Y.left) : IsClosed ({iZ z} : Set X.left) := by
    rw [← Set.image_singleton]
    exact iZ.isClosedEmbedding.isClosedMap _ (isClosed_discrete _)
  have singletonS : S = {sectionSupport q} := by
    apply Set.Subset.antisymm ?_ (Set.singleton_subset_iff.mpr hqi)
    intro x hx
    obtain ⟨z, rfl⟩ := hz.symm ▸ hx
    have hpclosed : iZ z ∈ closedPoints X.left := hyclosed z
    obtain ⟨r, hr⟩ := liftX (iZ z) hpclosed
    have hrs : sectionSupport r ∈ S := hr.symm ▸ hx
    have hOrb := orbit_closure_in_closed_support a r liftT S hS
      (fun t h => hrs ((hi t r).mp h))
    let f := orbitMap a r
    have hf (t : T.X.left) : f.left t ∈ Set.range iZ := by
      rw [hz]
      exact hOrb (subset_closure (Set.mem_range_self t))
    let l (t : T.X.left) : Y.left := (hf t).choose
    have hl (t : T.X.left) : iZ (l t) = f.left t := (hf t).choose_spec
    have hlc : Continuous l := by
      apply iZ.isClosedEmbedding.isEmbedding.isInducing.continuous_iff.mpr
      exact f.left.continuous.congr fun t => (hl t).symm
    let t₀ := sectionSupport (η[T.X])
    have ht₀ : f.left t₀ = sectionSupport r := by
      change sectionSupport (η[T.X] ≫ f) = sectionSupport r
      have hf' : η[T.X] ≫ f = r := by
        letI := a
        have hx₀ : (1 : 𝟙_ (SchemeOver k) ⟶ T.X) = η[T.X] := by
          rw [CategoryTheory.Hom.one_def, show toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ from
            Subsingleton.elim _ _, Category.id_comp]
        have hv : (1 : 𝟙_ (SchemeOver k) ⟶ T.X) • r = r := one_smul _ _
        change lift (1 : 𝟙_ (SchemeOver k) ⟶ T.X) r ≫ a.smul = r at hv
        rw [hx₀] at hv
        have he : η[T.X] ≫ lift (𝟙 T.X) (toUnit T.X ≫ r) = lift (η[T.X]) r := by
          apply CartesianMonoidalCategory.hom_ext
          · simp only [Category.assoc, lift_fst, Category.comp_id]
          · simp only [Category.assoc, lift_snd, comp_toUnit_assoc]
            rw [show toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ from Subsingleton.elim _ _, Category.id_comp]
        unfold f orbitMap
        rw [← Category.assoc, he]
        exact hv
      rw [hf']
    have hsame (t : T.X.left) : f.left t = sectionSupport r := by
      rw [← hl t, PreconnectedSpace.constant inferInstance hlc (x := t) (y := t₀), hl, ht₀]
    have hsingle : closure (orbitSet a r) ⊆ {sectionSupport r} :=
      (hr ▸ hyclosed z).closure_subset_iff.mpr (by
        rintro _ ⟨t, rfl⟩
        exact Set.mem_singleton_iff.mpr (hsame t))
    obtain ⟨b, hb, hb'⟩ := hfix r
    have he : sectionSupport b = sectionSupport r := Set.mem_singleton_iff.mp (hsingle hb)
    rcases hclass b hb' with rfl | rfl
    · exact (hrs (he ▸ hp)).elim
    · exact Set.mem_singleton_iff.mpr (hr.symm.trans he.symm)
  rw [← singletonS, compl_compl]

end AffineChartsAndFixedPoints

section ChartHeight


open TopologicalSpace

variable {k : Type u} [Field k]

private theorem height_one_from_affine_charts
    {X U : SchemeOver k} [IsSeparated X.hom] [IrreducibleSpace X.left]
    (A : TestAlgebra k) [IsDomain A] [IsNoetherianRing A] [Algebra.Smooth k A]
    (j₁ : (testSpec k).obj (op A) ⟶ X) (j₂ : U ⟶ X)
    [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    (hU : IsAffine U.left) (hne : Nonempty U.left)
    (p : PrimeSpectrum A) (hp : p.asIdeal.IsMaximal)
    (hj₂ : Set.range j₂.left = ({j₁.left p} : Set X.left)ᶜ) :
    p.asIdeal.height = 1 := by
  let I := j₁.left.opensRange
  let J := j₂.left.opensRange
  let W : Opens (PrimeSpectrum A) := j₁.left ⁻¹ᵁ J
  haveI : X.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from X.hom]
    infer_instance
  letI : IsAffine ((testSpec k).obj (op A)).left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  have hI : IsAffineOpen I := isAffineOpen_opensRange j₁.left
  have hJ : IsAffineOpen J := by
    letI := hU
    exact isAffineOpen_opensRange j₂.left
  have hW : IsAffineOpen (show ((testSpec k).obj (op A)).left.Opens from W) := by
    apply (j₁.left.isAffineOpen_iff_of_isOpenImmersion).mp
    have he : j₁.left ''ᵁ W = I ⊓ J := by
      apply Opens.ext
      change j₁.left '' (j₁.left ⁻¹' Set.range j₂.left) =
        Set.range j₁.left ∩ Set.range j₂.left
      rw [Set.image_preimage_eq_inter_range, Set.inter_comm]
    rw [he]
    exact hI.inf hJ
  have hw : (W : Set (PrimeSpectrum A)) = {p}ᶜ := by
    change j₁.left ⁻¹' Set.range j₂.left = _
    rw [hj₂, Set.preimage_compl]
    ext x
    change (j₁.left x ∉ ({j₁.left p} : Set X.left)) ↔ x ∉ ({p} : Set (PrimeSpectrum A))
    rw [Set.mem_singleton_iff, Set.mem_singleton_iff, j₁.left.isOpenEmbedding.injective.eq_iff]
  have hUpper := height_le_one_of_affine_puncture A (smooth_domain_normal k A) p W hw hW
  have hneW : (W : Set (PrimeSpectrum A)).Nonempty := by
    have hI' : (I : Set X.left).Nonempty :=
      ⟨j₁.left p, Set.mem_range_self p⟩
    have hJ' : (J : Set X.left).Nonempty :=
      ⟨j₂.left (Classical.choice hne), Set.mem_range_self _⟩
    obtain ⟨z, hz, ⟨v, rfl⟩⟩ := (I.isOpen.dense hI').inter_open_nonempty J J.isOpen hJ'
    exact ⟨v, hz⟩
  obtain ⟨v, hv⟩ := hneW
  have hvne : v ≠ p := by
    rw [hw] at hv
    exact fun h => hv (Set.mem_singleton_iff.mpr h)
  have hnp : p.asIdeal ≠ ⊥ := by
    intro h
    apply hvne
    apply PrimeSpectrum.ext
    exact (hp.eq_of_le v.isPrime.ne_top (h ▸ bot_le)).symm
  apply le_antisymm hUpper
  have hle := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hnp)
  simpa only [Ideal.height_bot, zero_add] using hle

end ChartHeight

section AdditiveCoordinate

open Specs.AdjointRepresentation (GroupPoints)
open Specs.StandardGroups (additivePoints spectrum)
open CocharacterDynamics (polynomialAlgebra polynomialEvaluate)

open Polynomial
variable {k : Type u} [Field k] {U : GroupScheme k}

/-- A coordinate identifying the underlying scheme with the affine line
and sending the unit to zero carries the group law to addition. -/
private theorem coordinate_of_product_is_add
    (coordinate : ∀ R : TestAlgebra k, GroupPoints U R ≃ R)
    (hn : ∀ {R S : TestAlgebra k} (a : R ⟶ S) (p : GroupPoints U R),
      coordinate S (mapPoints a p) = a.hom (coordinate R p))
    (h0 : ∀ R, coordinate R 1 = 0)
    (R : TestAlgebra k) (p q : GroupPoints U R) :
    coordinate R (p * q) = coordinate R p + coordinate R q := by
  let B := CommAlgCat.of k (Polynomial k)
  let S := polynomialAlgebra B
  let x : GroupPoints U S := (coordinate S).symm (C (X : Polynomial k))
  let y : GroupPoints U S := (coordinate S).symm (X : Polynomial (Polynomial k))
  let F : Polynomial (Polynomial k) := coordinate S (x * y)
  let I : Polynomial (Polynomial k) := coordinate S (x⁻¹ * y)
  have hx : coordinate S x = C (X : Polynomial k) := (coordinate S).apply_symm_apply _
  have hy : coordinate S y = (X : Polynomial (Polynomial k)) := (coordinate S).apply_symm_apply _
  have hmapMul {T : TestAlgebra k} (a : S ⟶ T) (r s : GroupPoints U S) :
      mapPoints a (r * s) = ((mapPoints a r : GroupPoints U T) * mapPoints a s) :=
    (((groupPointsFunctor k).obj U).map a).hom.map_mul r s
  have hF : F.comp I = X := by
    let a : S ⟶ S := CommAlgCat.ofHom ((Polynomial.aeval I :
      Polynomial (Polynomial k) →ₐ[Polynomial k] Polynomial (Polynomial k)).restrictScalars k)
    have hax : mapPoints a x = x := by
      apply (coordinate S).injective
      rw [hn, hx]
      change (Polynomial.aeval I : Polynomial (Polynomial k) →ₐ[Polynomial k] _) (C X) = C X
      exact (Polynomial.aeval I).commutes _
    have hay : mapPoints a y = x⁻¹ * y := by
      apply (coordinate S).injective
      rw [hn, hy, ← show I = coordinate S (x⁻¹ * y) from rfl]
      exact Polynomial.aeval_X _
    have h := (hn a (x * y)).symm
    rw [hmapMul, hax, hay, ← mul_assoc, mul_inv_cancel, one_mul, hy] at h
    change (Polynomial.aeval I : Polynomial (Polynomial k) →ₐ[Polynomial k] _) F = X at h
    simpa only [Polynomial.comp_eq_aeval] using h
  have hleft : F.map (evalRingHom (0 : k)) = X := by
    let b : B ⟶ CommAlgCat.of k k := CommAlgCat.ofHom (Polynomial.aeval 0)
    let a : S ⟶ polynomialAlgebra (CommAlgCat.of k k) :=
      CommAlgCat.ofHom (Polynomial.mapAlgHom b.hom)
    let T := polynomialAlgebra (CommAlgCat.of k k)
    have hax : (mapPoints a x : GroupPoints U T) = 1 := by
      apply (coordinate T).injective
      rw [hn, hx, h0]
      change (C (X : Polynomial k)).map b.hom.toRingHom = (0 : Polynomial k)
      rw [Polynomial.map_C]
      change (C ((Polynomial.aeval (0 : k)) (X : Polynomial k)) : Polynomial k) = 0
      rw [Polynomial.aeval_X, map_zero]
    have h := (hn a (x * y)).symm
    rw [hmapMul, hax, one_mul, hn, hy] at h
    change F.map (evalRingHom (0 : k)) = Polynomial.X.map (evalRingHom (0 : k)) at h
    simpa only [Polynomial.map_X] using h
  have hright : F.eval 0 = X := by
    let a := polynomialEvaluate B 0
    have hay : (mapPoints a y : GroupPoints U B) = 1 := by
      apply (coordinate B).injective
      rw [hn, hy, h0]
      exact Polynomial.eval_X
    have h := (hn a (x * y)).symm
    rw [hmapMul, hay, mul_one, hn, hx] at h
    change F.eval 0 = (C X : Polynomial (Polynomial k)).eval 0 at h
    simpa only [Polynomial.eval_C] using h
  have hsum := polynomial_addition_of_translation F I hF hleft hright
  let a : S ⟶ R := CommAlgCat.ofHom
    (Polynomial.aevalTower (Polynomial.aeval (coordinate R p)) (coordinate R q))
  have hax : mapPoints a x = p := by
    apply (coordinate R).injective
    rw [hn, hx]
    change Polynomial.aevalTower (Polynomial.aeval (coordinate R p)) (coordinate R q) (C X) = _
    rw [Polynomial.aevalTower_C, Polynomial.aeval_X]
  have hay : mapPoints a y = q := by
    apply (coordinate R).injective
    rw [hn, hy]
    exact Polynomial.aevalTower_X _ _
  have h := hn a (x * y)
  rw [hmapMul, hax, hay] at h
  change coordinate R (p * q) = a.hom F at h
  rw [h, hsum, map_add]
  change Polynomial.aevalTower (Polynomial.aeval (coordinate R p)) (coordinate R q) (C X) +
    Polynomial.aevalTower (Polynomial.aeval (coordinate R p)) (coordinate R q) X = _
  rw [Polynomial.aevalTower_C, Polynomial.aevalTower_X, Polynomial.aeval_X]

private theorem split_additive_of_coordinate (ha : IsAffine U.X.left)
    (coordinate : ∀ R : TestAlgebra k, GroupPoints U R ≃ R)
    (hn : ∀ {R S : TestAlgebra k} (a : R ⟶ S) (p : GroupPoints U R),
      coordinate S (mapPoints a p) = a.hom (coordinate R p))
    (h0 : ∀ R, coordinate R 1 = 0) : Specs.RankOneFlag.IsSplitAdditive U := by
  obtain ⟨h, hδ, hε, hi, e, _, c, _⟩ := StandardGroups.additiveGroupSpecification k
  letI := h.hopf
  let L := (spectrum (k := k) (Polynomial k)).val
  let E (R : TestAlgebra k) : GroupPoints U R ≃* Multiplicative R :=
    { toEquiv := (coordinate R).trans Multiplicative.ofAdd
      map_mul' := fun p q => coordinate_of_product_is_add coordinate hn h0 R p q }
  let N : (groupPointsFunctor k).obj U ≅ additivePoints k :=
    NatIso.ofComponents (fun R => (E R).toGrpIso) (by
      intro R S a
      apply GrpCat.ext
      intro p
      exact hn a p)
  let F := N ≪≫ c.symm
  obtain ⟨f, hf⟩ := (groupHomComparison k U L ha).2 F.hom
  obtain ⟨g, hg⟩ := (groupHomComparison k L U
    (inferInstanceAs (IsAffine (Spec (CommRingCat.of (Polynomial k)))))).2 F.inv
  change (groupPointsFunctor k).map f = F.hom at hf
  change (groupPointsFunctor k).map g = F.inv at hg
  refine ⟨h, hδ, hε, hi, ⟨⟨f, g, ?_, ?_⟩⟩⟩
  · apply (groupHomComparison k U U ha).1
    change (groupPointsFunctor k).map (f ≫ g) = (groupPointsFunctor k).map (𝟙 U)
    rw [Functor.map_comp, hf, hg, F.hom_inv_id]
    exact ((groupPointsFunctor k).map_id U).symm
  · apply (groupHomComparison k L L
      (inferInstanceAs (IsAffine (Spec (CommRingCat.of (Polynomial k)))))).1
    change (groupPointsFunctor k).map (g ≫ f) = (groupPointsFunctor k).map (𝟙 L)
    rw [Functor.map_comp, hg, hf, F.inv_hom_id]
    exact ((groupPointsFunctor k).map_id L).symm

end AdditiveCoordinate

section ContractingCoordinate

open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open CocharacterDynamics (cocharacterPoint LimitDecomposition orbit polynomialAlgebra laurentAlgebra
  polynomialEvaluate polynomialToLaurent laurentConstants laurentParameter
  mapPoints_comp mapPoints_cocharacterPoint)
open private pointHom scalePolynomial scaleLaurent scale_polynomial_laurent
  orbit_eval cocharacterPoint_mul from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private affinePointEquiv affinePointEquiv_natural
  polynomialContract polynomialContract_eq polynomialContract_restrict polynomialContract_natural
  polynomialContract_one polynomialContract_zero
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterSmoothAndUnipotent

variable {k : Type u} [Field k] {G : GroupScheme k}

private theorem contraction_scales_by_unit (ha : IsAffine G.X.left)
    (c : Cocharacter G) (D : LimitDecomposition c)
    {R : TestAlgebra k} (s : Rˣ) (x y : GroupPoints D.contracting.group R)
    (hy : pointHom D.contracting.inclusion R y =
      cocharacterPoint c R s * pointHom D.contracting.inclusion R x * (cocharacterPoint c R s)⁻¹) :
    polynomialContract ha c D y =
      mapPoints (scalePolynomial R s) (polynomialContract ha c D x) := by
  apply polynomialContract_eq
  change mapPoints (polynomialToLaurent R)
      (mapPoints (scalePolynomial R s)
        (pointHom D.contracting.inclusion _ (polynomialContract ha c D x))) = _
  rw [← mapPoints_comp, scale_polynomial_laurent, mapPoints_comp, polynomialContract_restrict]
  rw [scaleLaurent, orbit_eval]
  let a := laurentConstants R
  let t := laurentParameter R
  let l := Units.map a.hom.toMonoidHom s
  let z : GroupPoints G (laurentAlgebra R) := mapPoints a (pointHom D.contracting.inclusion R x)
  have hcomm : Commute (cocharacterPoint c (laurentAlgebra R) l)
      (cocharacterPoint c (laurentAlgebra R) t) := by
    show _ * _ = _ * _
    rw [← cocharacterPoint_mul, ← cocharacterPoint_mul, mul_comm]
  have hm : (mapPoints a (pointHom D.contracting.inclusion R y) : GroupPoints G (laurentAlgebra R)) =
      cocharacterPoint c (laurentAlgebra R) l * z * (cocharacterPoint c (laurentAlgebra R) l)⁻¹ := by
    change ((((groupPointsFunctor k).obj G).map a).hom (pointHom D.contracting.inclusion R y)) = _
    rw [hy, map_mul, map_mul, map_inv]
    change
      (show GroupPoints G (laurentAlgebra R) from mapPoints a (cocharacterPoint c R s)) * z *
        (show GroupPoints G (laurentAlgebra R) from mapPoints a (cocharacterPoint c R s))⁻¹ = _
    rw [mapPoints_cocharacterPoint]
  change cocharacterPoint c _ (l * t) * z * (cocharacterPoint c _ (l * t))⁻¹ =
    cocharacterPoint c _ t *
      (show GroupPoints G (laurentAlgebra R) from mapPoints a (pointHom D.contracting.inclusion R y)) *
      (cocharacterPoint c _ t)⁻¹
  rw [cocharacterPoint_mul, hcomm.eq, hm]
  group

open Polynomial

private theorem coeff_aeval_mul_X {B : Type*} [CommRing B]
    (p : Polynomial B) (t : B) (n : ℕ) :
    ((aeval (C t * X)) p).coeff n = p.coeff n * t ^ n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq, add_mul]
  | monomial j b =>
    rw [aeval_monomial, Polynomial.algebraMap_apply, mul_pow,
      ← map_pow, ← mul_assoc, ← map_mul, C_mul_X_pow_eq_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst j
      rfl
    · rw [zero_mul]

/-- The extension of conjugation to the affine parameter line yields a
nonnegative grading on the contracting subgroup's actual coordinate algebra. -/
private theorem contracting_coordinate_grading (ha : IsAffine G.X.left)
    (c : Cocharacter G) (D : LimitDecomposition c)
    (A : TestAlgebra k) (e : (testSpec k).obj (op A) ≅ D.contracting.group.X)
    (ε : A →ₐ[k] k)
    (hε : affinePointEquiv e (CommAlgCat.of k k) ε = 1) :
    ∃ p : A →ₐ[k] Polynomial A,
      (∀ a, (p a).eval 1 = a) ∧
      (∀ a n, p ((p a).coeff n) = monomial n ((p a).coeff n)) ∧
      (∀ a, (p a).coeff 0 = algebraMap k A (ε a)) := by
  let u : GroupPoints D.contracting.group A := affinePointEquiv e A (AlgHom.id k A)
  let p : A →ₐ[k] Polynomial A :=
    (affinePointEquiv e (polynomialAlgebra A)).symm (polynomialContract ha c D u)
  have hp : affinePointEquiv e (polynomialAlgebra A) p = polynomialContract ha c D u :=
    (affinePointEquiv e (polynomialAlgebra A)).apply_symm_apply _
  have hnat {R : TestAlgebra k} (b : A →ₐ[k] R) :
      polynomialContract ha c D (affinePointEquiv e R b) =
        affinePointEquiv e (polynomialAlgebra R) ((Polynomial.mapAlgHom b).comp p) := by
    let f : A ⟶ R := CommAlgCat.ofHom b
    have h₁ : affinePointEquiv e R b = mapPoints f u :=
      affinePointEquiv_natural e f (AlgHom.id k A)
    rw [h₁, polynomialContract_natural, ← hp]
    exact (affinePointEquiv_natural e (CocharacterDynamics.mapPolynomial f) p).symm
  have hone : (polynomialEvaluate A 1).hom.comp p = AlgHom.id k A := by
    apply (affinePointEquiv e A).injective
    rw [affinePointEquiv_natural, hp, polynomialContract_one]
  have hzero : (polynomialEvaluate A 0).hom.comp p = (Algebra.ofId k A).comp ε := by
    apply (affinePointEquiv e A).injective
    rw [affinePointEquiv_natural, hp, polynomialContract_zero]
    let f : CommAlgCat.of k k ⟶ A := CommAlgCat.ofHom (Algebra.ofId k A)
    have hh : affinePointEquiv e A ((Algebra.ofId k A).comp ε) =
      mapPoints f (affinePointEquiv e (CommAlgCat.of k k) ε) :=
      affinePointEquiv_natural e f ε
    rw [hh, hε]
    exact (((groupPointsFunctor k).obj D.contracting.group).map f).hom.map_one.symm
  refine ⟨p, fun a => AlgHom.congr_fun hone a, ?_, fun a => ?_⟩
  · intro a n
    let R := laurentAlgebra A
    let s := laurentParameter A
    let b₀ := (laurentConstants A).hom
    let b := (polynomialToLaurent A).hom.comp p
    let x : GroupPoints D.contracting.group R := affinePointEquiv e R b₀
    let y : GroupPoints D.contracting.group R := affinePointEquiv e R b
    have hx : x = mapPoints (laurentConstants A) u :=
      affinePointEquiv_natural e (laurentConstants A) (AlgHom.id k A)
    have hy : y = mapPoints (polynomialToLaurent A) (polynomialContract ha c D u) := by
      rw [← hp]
      exact affinePointEquiv_natural e (polynomialToLaurent A) p
    have hy' : pointHom D.contracting.inclusion R y =
        cocharacterPoint c R s * pointHom D.contracting.inclusion R x * (cocharacterPoint c R s)⁻¹ := by
      rw [hy, hx]
      exact polynomialContract_restrict ha c D u
    have h := contraction_scales_by_unit ha c D s x y hy'
    change polynomialContract ha c D (affinePointEquiv e R b) =
      mapPoints (scalePolynomial R s) (polynomialContract ha c D (affinePointEquiv e R b₀)) at h
    rw [hnat, hnat, ← affinePointEquiv_natural] at h
    have hh := (affinePointEquiv e (polynomialAlgebra R)).injective h
    have hc := congrArg (fun g : A →ₐ[k] Polynomial R => (g a).coeff n) hh
    change (Polynomial.mapAlgHom b (p a)).coeff n =
      ((aeval (C s.val * X)) (Polynomial.mapAlgHom b₀ (p a))).coeff n at hc
    rw [coeff_aeval_mul_X, Polynomial.coeff_mapAlgHom_apply, Polynomial.coeff_mapAlgHom_apply] at hc
    apply Polynomial.toLaurent_injective
    change (p ((p a).coeff n)).toLaurent = LaurentPolynomial.C ((p a).coeff n) * (LaurentPolynomial.T 1)^n at hc
    rw [LaurentPolynomial.T_pow, mul_one] at hc
    rw [Polynomial.toLaurent_C_mul_T]
    exact hc
  · have h := AlgHom.congr_fun hzero a
    change (p a).eval 0 = _ at h
    exact (Polynomial.coeff_zero_eq_eval_zero _).trans h

end ContractingCoordinate

section SignedLimitBaseChange

open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (absoluteRoots pairing)
open Specs.GeometricRadicals (GeometricGroup IsReductive IsSplitTorus IsMaximalTorus
  baseChangedSubgroup geometricUnipotentRadical)
open Specs.GeometricBorelConjugacy (IsBorel IsKBorel)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.Unipotent (closedSubgroupAlgebraicGroup baseChangedAlgebraicGroup)
open Specs.RankOneFlag (Centralizer SameSubgroup IsRankOneBorelPair AreTwoBorels)
open Specs.DiagonalizableGroups (IntegerCharacters groupAlgebra)
open Specs.QuotientEmbedding (Presentation)
open CocharacterDynamics (LimitDecomposition oppositeCocharacter cocharacterPoint unitPoint
  RepresentsOnAlgebras HasExtension HasLimit)
open private gm_baseChange baseChange_hasExtension_iff baseChange_hasLimit_iff baseChange_image_iff
  unitPointHom_apply unitEquiv opposite_point pointHom subgroupInclusionFactors
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private subgroupOf_trans factor_group_through_subgroup
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private factor_of_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private mono_over centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private centralizes_precomp_iso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.ConnectedTorusCentralizer
open private geometricSmooth
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper
open private rationalMap rationalSections solvable_iff_sections
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals

variable {k : Type u} [Field k]

private abbrev multiplicativeScheme (F : Type u) [Field F] : GroupScheme F :=
  specGroup (groupAlgebra F IntegerCharacters)

private theorem cocharacter_ext_units {G : GroupScheme k} {c d : Cocharacter G}
    (h : ∀ (R : TestAlgebra k) (s : Rˣ), cocharacterPoint c R s = cocharacterPoint d R s) :
    c = d := by
  apply (groupHomComparison k _ _
    (inferInstanceAs (IsAffine (Spec (CommRingCat.of (MonoidAlgebra k IntegerCharacters)))))).1
  ext R p
  have hp : unitPoint R (unitEquiv R p) = p := by
    rw [← unitPointHom_apply]
    exact (unitEquiv R).symm_apply_apply p
  change pointHom c R p = pointHom d R p
  rw [← hp]
  exact h R _

private theorem opposite_opposite {G : GroupScheme k} (c : Cocharacter G) :
    oppositeCocharacter (oppositeCocharacter c) = c := by
  apply cocharacter_ext_units
  intro R s
  rw [opposite_point, opposite_point, inv_inv]

private theorem opposite_baseChange {K : Type u} [Field K] [Algebra k K]
    {G : GroupScheme k} (c : Cocharacter G) (e : multiplicativeScheme K ≅ (groupBaseChange k K).obj (multiplicativeScheme k))
    (he : ∀ (R : TestAlgebra K) (s : Rˣ),
      baseChangePointGroupEquiv K (multiplicativeScheme k) R (pointHom e.hom R (unitPoint R s)) =
        unitPoint ((restrictTestAlgebra k K).obj R) s) :
    oppositeCocharacter (e.hom ≫ (groupBaseChange k K).map c) =
      e.hom ≫ (groupBaseChange k K).map (oppositeCocharacter c) := by
  apply cocharacter_ext_units
  intro R s
  rw [opposite_point]
  apply (baseChangePointGroupEquiv K G R).injective
  have h (d : Cocharacter G) (t : Rˣ) :
      baseChangePointGroupEquiv K G R
        (cocharacterPoint (e.hom ≫ (groupBaseChange k K).map d) R t) =
        cocharacterPoint d ((restrictTestAlgebra k K).obj R) t := by
    change baseChangePointGroupEquiv K G R
      (pointHom ((groupBaseChange k K).map d) R (pointHom e.hom R (unitPoint R t))) = _
    rw [show baseChangePointGroupEquiv K G R
      (pointHom ((groupBaseChange k K).map d) R (pointHom e.hom R (unitPoint R t))) =
        pointHom d _ (baseChangePointGroupEquiv K (multiplicativeScheme k) R (pointHom e.hom R (unitPoint R t)))
      from baseChangePointsSchemeNaturality k K d.hom.hom R _, he]
    rfl
  rw [h, h, opposite_point]

private def extendSubgroup (K : Type u) [Field K] [Algebra k K]
    {G : GroupScheme k} (B : ClosedSubgroup G) : ClosedSubgroup ((groupBaseChange k K).obj G) :=
  baseChangedSubgroup K B (baseChangeClosedSubgroup k K _ B.isClosedImmersion)

private theorem extend_subgroupOf {K : Type u} [Field K] [Algebra k K]
    {G : GroupScheme k} {B C : ClosedSubgroup G} (h : IsSubgroupOf B C) :
    IsSubgroupOf (extendSubgroup K B) (extendSubgroup K C) := by
  obtain ⟨j, hj⟩ := h
  exact ⟨(groupBaseChange k K).map j, by
    change (groupBaseChange k K).map j ≫ (groupBaseChange k K).map C.inclusion = _
    rw [← Functor.map_comp, hj]
    rfl⟩

private theorem subgroupOf_of_extend {K : Type u} [Field K] [Algebra k K]
    {G : GroupScheme k} {B C : ClosedSubgroup G}
    (h : IsSubgroupOf (extendSubgroup K B) (extendSubgroup K C)) : IsSubgroupOf B C := by
  obtain ⟨j, hj⟩ := h
  letI : IsClosedImmersion C.inclusion.hom.hom.left := C.isClosedImmersion
  have h' := (Grp.forget (SchemeOver K)).congr_map hj
  change j.hom.hom ≫ (baseChange k K).map C.inclusion.hom.hom =
    (baseChange k K).map B.inclusion.hom.hom at h'
  obtain ⟨f, hf⟩ := factor_of_baseChange K B.inclusion.hom.hom C.inclusion.hom.hom j.hom.hom h'
  exact factor_group_through_subgroup C B.inclusion f hf

private theorem same_subgroup_of_same_affine_points {G : AffineAlgebraicGroup k}
    {B C : ClosedSubgroup G.val} {P : ∀ R : TestAlgebra k, GroupPoints G.val R → Prop}
    (hB : RepresentsOnAlgebras B P) (hC : RepresentsOnAlgebras C P) :
    SameSubgroup B C := by
  have ha (J : ClosedSubgroup G.val) : IsAffine J.group.X.left :=
    (closedSubgroupAlgebraicGroup J).property.1
  refine ⟨subgroupInclusionFactors (ha B) C B.inclusion ?_,
    subgroupInclusionFactors (ha C) B C.inclusion ?_⟩
  · intro R b
    exact (hC _ _).mp ((hB _ _).mpr ⟨b, rfl⟩)
  · intro R c
    exact (hB _ _).mp ((hC _ _).mpr ⟨c, rfl⟩)

private theorem limits_subgroups_extend {K : Type u} [Field K] [Algebra k K]
    (H : AffineAlgebraicGroup k) {c : Cocharacter H.val} (D : LimitDecomposition c)
    (e : multiplicativeScheme K ≅ (groupBaseChange k K).obj (multiplicativeScheme k))
    (he : ∀ (R : TestAlgebra K) (s : Rˣ),
      baseChangePointGroupEquiv K (multiplicativeScheme k) R (pointHom e.hom R (unitPoint R s)) =
        unitPoint ((restrictTestAlgebra k K).obj R) s)
    (F : LimitDecomposition (e.hom ≫ (groupBaseChange k K).map c)) :
    SameSubgroup F.parabolic (extendSubgroup K D.parabolic) ∧
      SameSubgroup F.contracting (extendSubgroup K D.contracting) ∧
      SameSubgroup F.centralizer (extendSubgroup K D.centralizer) := by
  let J := baseChangedAlgebraicGroup K H
  constructor
  · apply same_subgroup_of_same_affine_points (G := J) F.parabolic_points
    intro R g
    exact (baseChange_hasExtension_iff c e he R g).trans
      ((D.parabolic_points _ _).trans (baseChange_image_iff D.parabolic R g).symm)
  constructor
  · apply same_subgroup_of_same_affine_points (G := J) F.contracting_points
    intro R g
    refine (baseChange_hasLimit_iff c e he R g 1).trans ?_
    change HasLimit c (baseChangePointGroupEquiv K H.val R g)
      (baseChangePointGroupEquiv K H.val R 1) ↔ _
    rw [map_one]
    exact (D.contracting_points _ _).trans (baseChange_image_iff D.contracting R g).symm
  · obtain ⟨_, h⟩ := centralizerSchemeBaseChange k K c D.centralizer D.centralizer_points
    apply same_subgroup_of_same_sections (H := J) F.centralizer_points
    intro Y g
    exact (centralizes_precomp_iso e _ g).trans (h Y g)


private theorem same_subgroup_trans {G : GroupScheme k} {A B C : ClosedSubgroup G}
    (h : SameSubgroup A B) (j : SameSubgroup B C) : SameSubgroup A C :=
  ⟨subgroupOf_trans h.1 j.1, subgroupOf_trans j.2 h.2⟩

private theorem same_subgroup_symm {G : GroupScheme k} {A B : ClosedSubgroup G}
    (h : SameSubgroup A B) : SameSubgroup B A := ⟨h.2, h.1⟩

private theorem borel_of_same [IsAlgClosed k] {H : AffineAlgebraicGroup k} {B C : ClosedSubgroup H.val}
    (hB : IsBorel B) (h : SameSubgroup B C) : IsBorel C := by
  obtain ⟨e, he⟩ := subgroupIso_of_same h
  let i := (Grp.forget (SchemeOver k)).mapIso e
  letI := (Over.forget _).map_isIso i.inv
  have hs : Smooth C.group.X.hom := by
    change Smooth ((Grp.forget (SchemeOver k)).obj C.group).hom
    rw [← Over.w i.inv]
    letI : Smooth ((Grp.forget (SchemeOver k)).obj B.group).hom := hB.1.1
    infer_instance
  have hc : ConnectedSpace C.group.X.left :=
    ((Over.forget _).mapIso i).hom.homeomorph.connectedSpace_iff.mp hB.1.2.1
  haveI : Group.IsSolvable (rationalSections B.group) :=
    (solvable_iff_sections (closedSubgroupAlgebraicGroup B) hB.1.1 hB.1.2.1).mp hB.1.2.2
  have hsol : SchemeDerivedGroup.IsSolvable C.group := by
    apply (solvable_iff_sections (closedSubgroupAlgebraicGroup C) hs hc).mpr
    apply Group.isSolvable_of_surjective (f := rationalMap e.hom)
    intro x
    exact ⟨x ≫ e.inv.hom.hom, by
      change (x ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = x
      rw [Category.assoc, show e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ from
        (Grp.forget (SchemeOver k)).congr_map e.inv_hom_id, Category.comp_id]⟩
  exact ⟨⟨hs, hc, hsol⟩, fun A ha hCA =>
    subgroupOf_trans (hB.2 A ha (subgroupOf_trans h.1 hCA)) h.1⟩

private theorem cocharacter_centralizes_self {G : GroupScheme k} (c : Cocharacter G) :
    Centralizes c c.hom.hom := by
  apply (centralizes_iff c _).mpr
  intro Y u x
  exact (show Commute u x from mul_comm _ _).map (IsMonHom.monoidHom c.hom.hom Y)

private theorem parabolic_of_cast {G : GroupScheme k} {c d : Cocharacter G}
    (h : c = d) (D : LimitDecomposition c) :
    (h ▸ D : LimitDecomposition d).parabolic = D.parabolic := by
  subst d
  rfl

private theorem signed_limit_borels_over_algClosed
    {K : Type u} [Field K] [IsAlgClosed K] (H : AffineAlgebraicGroup K)
    (hs : Smooth H.val.X.hom) (hc : ConnectedSpace H.val.X.left)
    (hn : ¬ SchemeDerivedGroup.IsSolvable H.val)
    {T : ClosedSubgroup H.val} (hT : IsMaximalTorus T)
    {R : ClosedSubgroup H.val} (hR : GeometricRadicals.IsUnipotentRadical H R)
    (htriv : GeometricRadicals.IsTrivialSubgroup R)
    {c : Cocharacter H.val}
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (hD : SameSubgroup D.centralizer T) (hE : SameSubgroup E.centralizer T)
    (n : 𝟙_ (SchemeOver K) ⟶ H.val.X)
    (hcosets : ∀ g : 𝟙_ (SchemeOver K) ⟶ H.val.X, Normalizes T.inclusion g →
      g ∈ SubgroupSections T (𝟙_ (SchemeOver K)) ∨
        n⁻¹ * g ∈ SubgroupSections T (𝟙_ (SchemeOver K))) :
    IsBorel D.parabolic ∧ IsBorel E.parabolic ∧ ¬ SameSubgroup D.parabolic E.parabolic ∧
      ∀ B : ClosedSubgroup H.val, IsBorel B → IsSubgroupOf T B →
        SameSubgroup B D.parabolic ∨ SameSubgroup B E.parabolic := by
  obtain ⟨B₁, B₂, hB₁, hB₂, h₁, h₂, hne, h₁D, h₂E⟩ :=
    signed_limits_in_distinct_borels H hs hc hn T hT D E hD hE
  obtain ⟨Q⟩ := QuotientEmbedding.quotientEmbedding K H B₁
  obtain ⟨_, hpair⟩ := borels_through_torus_of_two_normalizer_cosets hs hc hT hB₁ hB₂ h₁ h₂ hne Q n hcosets
  obtain ⟨f, hf⟩ := subgroupOf_trans ⟨D.sectionMap, D.section_in_G⟩ h₁D
  have hb : ∃ b : Cocharacter B₁.group, b ≫ B₁.inclusion = c := by
    obtain ⟨r, hr⟩ := (D.centralizer_points _ c.hom.hom).mp (cocharacter_centralizes_self c)
    obtain ⟨a, ha⟩ := factor_group_through_subgroup D.centralizer c r hr
    exact ⟨a ≫ f, by rw [Category.assoc, hf, ha]⟩
  obtain ⟨b₁, hb₁⟩ := hb
  have he₀ : ∃ b : Cocharacter B₂.group, b ≫ B₂.inclusion = oppositeCocharacter c := by
    obtain ⟨r, hr⟩ := (E.centralizer_points _ (oppositeCocharacter c).hom.hom).mp
      (cocharacter_centralizes_self (oppositeCocharacter c))
    obtain ⟨a, ha⟩ := factor_group_through_subgroup E.centralizer _ r hr
    obtain ⟨f₂, hf₂⟩ := subgroupOf_trans ⟨E.sectionMap, E.section_in_G⟩ h₂E
    exact ⟨a ≫ f₂, by rw [Category.assoc, hf₂, ha]⟩
  obtain ⟨b₂, hb₂⟩ := he₀
  have fr : IsSubgroupOf B₁ D.parabolic :=
    limit_parabolic_equals_borel_of_two_borels H hs hc hT hR htriv hB₁ hpair D E h₂E b₁ hb₁
  let hcc := (opposite_opposite c).symm
  let F : LimitDecomposition (oppositeCocharacter (oppositeCocharacter c)) := hcc ▸ D
  have hF : IsSubgroupOf F.parabolic B₁ := (parabolic_of_cast hcc D).symm ▸ h₁D
  have gr : IsSubgroupOf B₂ E.parabolic :=
    limit_parabolic_equals_borel_of_two_borels H hs hc hT hR htriv hB₂
      (fun B hB hTB => (hpair B hB hTB).symm) E F hF b₂ hb₂
  let d : SameSubgroup B₁ D.parabolic := ⟨fr, h₁D⟩
  let e : SameSubgroup B₂ E.parabolic := ⟨gr, h₂E⟩
  refine ⟨borel_of_same hB₁ d, borel_of_same hB₂ e, ?_, fun B hB hTB =>
    (hpair B hB hTB).imp (fun h => same_subgroup_trans h d) (fun h => same_subgroup_trans h e)⟩
  exact fun h => hne (same_subgroup_trans d (same_subgroup_trans h (same_subgroup_symm e)))

private theorem geometric_cosets_of_root_normalizer {H : AffineAlgebraicGroup k}
    (hH : IsReductive H) (T : ClosedSubgroup H.val) (hT : GeometricRadicals.IsTorus T.group)
    (hTm : Specs.RankOneFlag.IsGeometricallyMaximal T)
    (n : 𝟙_ (SchemeOver k) ⟶ H.val.X) (hn : Normalizes T.inclusion n) :
    let K := AlgebraicClosure k
    let T' := extendSubgroup K T
    let n' := scalarExtendedRationalPoint K n
    Normalizes T'.inclusion n' ∧
    (∀ g : 𝟙_ (SchemeOver K) ⟶ (GeometricGroup H).val.X, Centralizes T'.inclusion g ↔
      g ∈ SubgroupSections T' (𝟙_ (SchemeOver K))) ∧
    ∃ N : ClosedSubgroup (GeometricGroup H).val,
      RepresentsSubgroup N (fun _ g => Normalizes T'.inclusion g) := by
  intro K T' n'
  obtain ⟨N, hN⟩ := normalizerScheme k H T
  obtain ⟨_, hN'⟩ := normalizerSchemeBaseChange k K T.inclusion N T.isClosedImmersion hN
  obtain ⟨m, hm⟩ := (hN _ _).mp hn
  obtain ⟨_, hZ⟩ := centralizerSchemeBaseChange k K T.inclusion T
    (Reductive.TorusCentralizer.maximalTorusCentralizer H hH T hT hTm)
  refine ⟨(hN' _ _).mpr ⟨scalarExtendedRationalPoint K m, ?_⟩, fun g => hZ _ g, ⟨_, hN'⟩⟩
  change scalarExtendedRationalPoint K m ≫ (baseChange k K).map N.inclusion.hom.hom = _
  rw [← scalarExtendedPoint_natural, hm]

private theorem root_signed_limit_borels {G : AffineAlgebraicGroup k}
    (hG : IsReductive G) {T : ClosedSubgroup G.val} (hT : IsSplitTorus T.group)
    (hTm : Specs.RankOneFlag.IsGeometricallyMaximal T)
    {α : Character T.group} (hα : α ∈ absoluteRoots T) (C : Centralizer T α)
    (c : Cocharacter T.group) (hp : 0 < pairing T.group α c)
    (D : LimitDecomposition (c ≫ C.torusIso.hom ≫ C.torus.inclusion))
    (E : LimitDecomposition (oppositeCocharacter (c ≫ C.torusIso.hom ≫ C.torus.inclusion))) :
    let H := closedSubgroupAlgebraicGroup C.subgroup
    let K := AlgebraicClosure k
    let T' := extendSubgroup K C.torus
    ∃ n : 𝟙_ (SchemeOver k) ⟶ H.val.X,
      Normalizes C.torus.inclusion n ∧
      Normalizes T'.inclusion (scalarExtendedRationalPoint K n) ∧
      (∀ g : 𝟙_ (SchemeOver K) ⟶ (GeometricGroup H).val.X, Normalizes T'.inclusion g →
        g ∈ SubgroupSections T' (𝟙_ (SchemeOver K)) ∨
          (show 𝟙_ (SchemeOver K) ⟶ (GeometricGroup H).val.X from
            scalarExtendedRationalPoint K n)⁻¹ * g ∈ SubgroupSections T' (𝟙_ (SchemeOver K))) ∧
      (∃ N : ClosedSubgroup (GeometricGroup H).val,
        RepresentsSubgroup N (fun _ g => Normalizes T'.inclusion g)) ∧
      AreTwoBorels C.torus D.parabolic E.parabolic := by
  intro H K T'
  let H' := GeometricGroup H
  let d := c ≫ C.torusIso.hom ≫ C.torus.inclusion
  have hH := root_centralizer_reductive G hG T hT hTm C
  have hHs : Smooth H'.val.X.hom := geometricSmooth H hH.1
  have hHc : ConnectedSpace H'.val.X.left :=
    hH.2.1.geometrically_connectedSpace _ _ _ (IsPullback.of_hasPullback _ _)
  have hTmax : IsMaximalTorus T' := C.torus_maximal.choose_spec
  have hTsplit : IsSplitTorus C.torus.group := by
    obtain ⟨r, ⟨e⟩⟩ := hT
    exact ⟨r, ⟨C.torusIso.symm ≪≫ e⟩⟩
  obtain ⟨n, hn, hall⟩ := root_normalizer_two_cosets hT hα.1 C hH
  obtain ⟨hn', hcent, hN⟩ := geometric_cosets_of_root_normalizer hH C.torus
    (lattice_torus_of_split hTsplit) C.torus_maximal n hn
  have hcosets (g : 𝟙_ (SchemeOver K) ⟶ H'.val.X) (hg : Normalizes T'.inclusion g) :
      g ∈ SubgroupSections T' (𝟙_ (SchemeOver K)) ∨
        (show 𝟙_ (SchemeOver K) ⟶ (GeometricGroup H).val.X from
            scalarExtendedRationalPoint K n)⁻¹ * g ∈ SubgroupSections T' (𝟙_ (SchemeOver K)) :=
    (hall K g hg).imp ((hcent _).mp) ((hcent _).mp)
  refine ⟨n, hn, hn', hcosets, hN, ?_⟩
  obtain ⟨e, he⟩ := gm_baseChange k K
  let d' := e.hom ≫ (groupBaseChange k K).map d
  obtain ⟨D'⟩ := CocharacterDynamics.existsLimitDecomposition H' d'
  obtain ⟨E'⟩ := CocharacterDynamics.existsLimitDecomposition H' (oppositeCocharacter d')
  obtain ⟨hPD, _, hZD⟩ := limits_subgroups_extend H D e he D'
  have hneg : oppositeCocharacter d' =
      e.hom ≫ (groupBaseChange k K).map (oppositeCocharacter d) :=
    opposite_baseChange d e he
  have hCompare : ∀ (f : Cocharacter H'.val),
      f = e.hom ≫ (groupBaseChange k K).map (oppositeCocharacter d) →
      ∀ F : LimitDecomposition f, SameSubgroup F.parabolic (extendSubgroup K E.parabolic) ∧
        SameSubgroup F.centralizer (extendSubgroup K E.centralizer) := by
    intro f hf F
    subst f
    obtain ⟨h₁, _, h₂⟩ := limits_subgroups_extend H E e he F
    exact ⟨h₁, h₂⟩
  obtain ⟨hPE, hZE⟩ := hCompare _ hneg E'
  obtain ⟨hD, hE⟩ := limit_centralizers_eq_torus hT C hH c hp D E
  have extend_same {A B : ClosedSubgroup H.val} (h : SameSubgroup A B) :
      SameSubgroup (extendSubgroup K A) (extendSubgroup K B) :=
    ⟨extend_subgroupOf h.1, extend_subgroupOf h.2⟩
  obtain ⟨hBD, hBE, hne, hpair⟩ := signed_limit_borels_over_algClosed H' hHs hHc
    (root_centralizer_geometrically_nonsolvable G hG T hT hTm hα C) hTmax
    (_root_.LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest H) hH.2.2 D' E'
    (same_subgroup_trans hZD (extend_same hD)) (same_subgroup_trans hZE (extend_same hE))
    (scalarExtendedRationalPoint K n) hcosets
  refine ⟨⟨(extendSubgroup K D.parabolic).isClosedImmersion, borel_of_same hBD hPD⟩,
    ⟨(extendSubgroup K E.parabolic).isClosedImmersion, borel_of_same hBE hPE⟩,
    fun h => hne (same_subgroup_trans hPD (same_subgroup_trans (extend_same h) (same_subgroup_symm hPE))),
    subgroupOf_trans hD.2 ⟨D.sectionMap, D.section_in_G⟩,
    subgroupOf_trans hE.2 ⟨E.sectionMap, E.section_in_G⟩, ?_⟩
  refine ⟨T'.isClosedImmersion, (extendSubgroup K D.parabolic).isClosedImmersion,
    (extendSubgroup K E.parabolic).isClosedImmersion, fun B hB hTB => ?_⟩
  exact (hpair B hB hTB).imp (fun h => same_subgroup_trans h hPD)
    (fun h => same_subgroup_trans h hPE)

end SignedLimitBaseChange

section LaurentCoordinates


open Polynomial LaurentPolynomial

variable {k : Type u} [Field k]

private theorem laurent_unit_as_monomial (v : (LaurentPolynomial k)ˣ) :
    ∃ (a : kˣ) (m : ℤ), (v : LaurentPolynomial k) = LaurentPolynomial.C (a : k) * T m := by
  obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow (v : LaurentPolynomial k)
  obtain ⟨m, q, hq⟩ := LaurentPolynomial.exists_T_pow (↑v⁻¹ : LaurentPolynomial k)
  have h : p * q = (X : Polynomial k) ^ (n + m) := by
    apply Polynomial.toLaurent_injective
    rw [map_mul, hp, hq, Polynomial.toLaurent_X_pow, Nat.cast_add]
    rw [mul_mul_mul_comm, Units.mul_inv, one_mul, ← T_add]
  obtain ⟨j, _, v', hv'⟩ := (dvd_prime_pow (Polynomial.prime_X (R := k)) _).mp ⟨q, h.symm⟩
  have hu : IsUnit (↑v'⁻¹ : Polynomial k) := (v'⁻¹).isUnit
  obtain ⟨a, ha, he⟩ := Polynomial.isUnit_iff.mp hu
  have vhe : p = (C a : Polynomial k) * X ^ j := by
    calc
      p = p * v' * ↑v'⁻¹ := by rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [hv', ← he, mul_comm]
  refine ⟨ha.unit, (j : ℤ) - n, ?_⟩
  rw [← IsUnit.mul_left_inj (LaurentPolynomial.isUnit_T (n : ℤ)), ← hp,
    vhe, map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow,
    LaurentPolynomial.mul_T_assoc, sub_add_cancel, ha.unit_spec]

private def laurentPowerUnits (k : Type u) [Field k] :
    Multiplicative ℤ →* (LaurentPolynomial k)ˣ where
  toFun m :=
    { val := T m.toAdd
      inv := T (-m.toAdd)
      val_inv := by rw [← T_add, add_neg_cancel, T_zero]
      inv_val := by rw [← T_add, neg_add_cancel, T_zero] }
  map_one' := Units.ext T_zero
  map_mul' m n := Units.ext (T_add m.toAdd n.toAdd)

private theorem laurentPowerUnits_zpow (m n : ℤ) :
    laurentPowerUnits k (Multiplicative.ofAdd m) ^ n =
      laurentPowerUnits k (Multiplicative.ofAdd (n * m)) := by
  rw [← map_zpow]
  rfl

private theorem monomial_exp_unique (a b : kˣ) (m n : ℤ)
    (h : LaurentPolynomial.C (a : k) * T m = LaurentPolynomial.C (b : k) * T n) :
    m = n := by
  have he := congrArg LaurentPolynomial.degree h
  rw [degree_C_mul_T _ _ a.ne_zero, degree_C_mul_T _ _ b.ne_zero] at he
  exact WithBot.coe_inj.mp he

private theorem laurent_automorphism_parameter (e : LaurentPolynomial k ≃ₐ[k] LaurentPolynomial k) :
    ∃ a : kˣ, e (T 1) = LaurentPolynomial.C (a : k) * T 1 ∨
      e (T 1) = LaurentPolynomial.C (a : k) * T (-1) := by
  let T₁ := laurentPowerUnits k (Multiplicative.ofAdd 1)
  let C₀ : k →+* LaurentPolynomial k := LaurentPolynomial.C
  let f := Units.map e.toAlgHom.toMonoidHom
  let g := Units.map e.symm.toAlgHom.toMonoidHom
  obtain ⟨a, m, ha⟩ := laurent_unit_as_monomial (f T₁)
  obtain ⟨b, n, hb⟩ := laurent_unit_as_monomial (g T₁)
  have ha' : f T₁ = Units.map C₀.toMonoidHom a *
      laurentPowerUnits k (Multiplicative.ofAdd m) := Units.ext ha
  have hb' : g T₁ = Units.map C₀.toMonoidHom b *
      laurentPowerUnits k (Multiplicative.ofAdd n) := Units.ext hb
  have hT : laurentPowerUnits k (Multiplicative.ofAdd n) = T₁ ^ n := by
    symm
    simpa only [T₁, mul_one] using (laurentPowerUnits_zpow (k := k) 1 n)
  have heC (d : kˣ) : f (Units.map C₀.toMonoidHom d) = Units.map C₀.toMonoidHom d := by
    apply Units.ext
    change e (LaurentPolynomial.C (d : k)) = LaurentPolynomial.C (d : k)
    exact e.commutes _
  have h := congrArg f hb'
  rw [map_mul, heC, hT, map_zpow, ha', mul_zpow, ← map_zpow, laurentPowerUnits_zpow,
    ← mul_assoc, ← map_mul] at h
  have hf : f (g T₁) = T₁ := by
    apply Units.ext
    exact e.apply_symm_apply _
  rw [hf] at h
  have hh := congrArg Units.val h
  change (T 1 : LaurentPolynomial k) = LaurentPolynomial.C ((b * a ^ n : kˣ) : k) * T (n * m) at hh
  have hh' : LaurentPolynomial.C ((1 : kˣ) : k) * T 1 =
      LaurentPolynomial.C ((b * a ^ n : kˣ) : k) * T (n * m) := by
    simpa only [Units.val_one, map_one, one_mul] using hh
  have hm := (monomial_exp_unique 1 (b * a ^ n) 1 (n * m) hh').symm
  have hdiv : m ∣ (1 : ℤ) := ⟨n, by rw [mul_comm, hm]⟩
  refine ⟨a, ?_⟩
  have ha'' : e (T 1) = LaurentPolynomial.C (a : k) * T m := ha
  rcases Int.isUnit_iff.mp (isUnit_iff_dvd_one.mpr hdiv) with h₁ | h₁
  · exact Or.inl (by simpa only [h₁] using ha'')
  · exact Or.inr (by simpa only [h₁] using ha'')

end LaurentCoordinates

section QuotientScalarExtension

open Specs.GeometricRadicals (baseChangedSubgroup)
open Specs.QuotientEmbedding (Presentation IsQuasiProjective)
open private isPullback_tensor_snd from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SmoothOrbit
open private baseChangeMapIsPullback compareRepresentatives compareRepresentatives_projection
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient
open private baseChangeProjection_effectiveEpi baseChangeProjection_naturality
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

variable {k : Type u} [Field k]
variable (K : Type u) [Field K] [Algebra k K]

private theorem tensor_left_epi_of_flat_surjective {X Y Z : SchemeOver k} {f : Y ⟶ Z}
    (hf : Flat f.left) (hs : Surjective f.left) :
    Epi (X ◁ f) := by
  have h := (isPullback_tensor_snd (A := X) f).flip.map (Over.forget (Spec (CommRingCat.of k)))
  haveI : Flat (X ◁ f).left := MorphismProperty.of_isPullback h hf
  haveI : Surjective (X ◁ f).left := MorphismProperty.of_isPullback h hs
  exact (Over.forget (Spec (CommRingCat.of k))).epi_of_epi_map
    (Flat.epi_of_flat_of_surjective (X ◁ f).left)

private theorem baseChange_quotient_comparison {G : AffineAlgebraicGroup k} {B : ClosedSubgroup G.val}
    (Q : Presentation B) :
    ∃ (P : Presentation (extendSubgroup K B))
      (e : P.scheme ≅ (baseChange k K).obj Q.scheme),
      P.projection ≫ e.hom = (baseChange k K).map Q.projection := by
  obtain ⟨P⟩ := QuotientEmbedding.quotientEmbedding K
    (Specs.Unipotent.baseChangedAlgebraicGroup K G) (extendSubgroup K B)
  obtain ⟨_, e, he⟩ := HomogeneousQuotient.quotientBaseChange k K Q
  exact ⟨P, compareRepresentatives P e, compareRepresentatives_projection P _ e he⟩

private def presentationTransport {G : GroupScheme k} {B : ClosedSubgroup G}
    (P : Presentation B) {Y : SchemeOver k} (e : P.scheme ≅ Y)
    (q : G.X ⟶ Y) (hq : P.projection ≫ e.hom = q) : Presentation B where
  scheme := Y
  quasiProjective := by
    obtain ⟨V, hV, hM, hF, j, hj⟩ := P.quasiProjective
    letI : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
    letI : IsImmersion j.left := hj
    exact ⟨V, hV, hM, hF, e.inv ≫ j, inferInstanceAs (IsImmersion (e.inv.left ≫ j.left))⟩
  projection := q
  flat := by
    rw [← hq, Over.comp_left]
    letI := P.flat
    letI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
    infer_instance
  surjective := by
    rw [← hq, Over.comp_left]
    letI := P.surjective
    letI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
    infer_instance
  finitePresentation := by
    rw [← hq, Over.comp_left]
    letI := P.finitePresentation
    letI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
    infer_instance
  quotientIso := P.quotientIso ≪≫ (fppfOver k).uliftYoneda.mapIso e
  quotientProjection := by
    change rightQuotientProjection B ≫ P.quotientIso.hom ≫ (fppfOver k).uliftYoneda.map e.hom = _
    rw [← Category.assoc, P.quotientProjection, ← Functor.map_comp, hq]

private def baseChangeQuotientPresentation {G : AffineAlgebraicGroup k} {B : ClosedSubgroup G.val}
    (Q : Presentation B) : Presentation (extendSubgroup K B) :=
  let h := baseChange_quotient_comparison K Q
  presentationTransport h.choose h.choose_spec.choose ((baseChange k K).map Q.projection)
    h.choose_spec.choose_spec

private theorem prodComparisonIso_inv_eq_inv (A B : SchemeOver k) :
    (prodComparisonIso (baseChange k K) A B).inv =
      inv (CartesianMonoidalCategory.prodComparison (baseChange k K) A B) := by
  apply (cancel_epi (prodComparisonIso (baseChange k K) A B).hom).mp
  rw [Iso.hom_inv_id, prodComparisonIso_hom, IsIso.hom_inv_id]

private theorem quotient_smul_baseChange_support {G : GroupScheme k}
    {X : SchemeOver k} (q : G.X ⟶ X) (a : G.X ⊗ X ⟶ X)
    (h : (G.X ◁ q) ≫ a = μ[G.X] ≫ q) :
    (((groupBaseChange k K).obj G).X ◁ (baseChange k K).map q) ≫ baseChangeAction K a =
      μ[((groupBaseChange k K).obj G).X] ≫ (baseChange k K).map q := by
  let F := baseChange k K
  change (F.obj G.X ◁ F.map q) ≫ baseChangeAction K a = _
  have he : (F.obj G.X ◁ F.map q) ≫ (prodComparisonIso F G.X X).inv =
      (prodComparisonIso F G.X G.X).inv ≫ F.map (G.X ◁ q) := by
    simp only [F, prodComparisonIso_inv_eq_inv]
    exact (prodComparison_inv_natural_whiskerLeft F (A := G.X) q).symm
  unfold baseChangeAction
  rw [← Category.assoc, he, Category.assoc, ← Functor.map_comp, h, Functor.map_comp]
  change (prodComparisonIso F G.X G.X).inv ≫ F.map μ[G.X] ≫ F.map q =
    (Functor.LaxMonoidal.μ F G.X G.X ≫ F.map μ[G.X]) ≫ F.map q
  rw [Functor.Monoidal.μ_of_cartesianMonoidalCategory, Category.assoc]

private theorem baseChange_smul_restriction {G H X : SchemeOver k} (i : H ⟶ G) (act : G ⊗ X ⟶ X) :
    baseChangeAction K ((i ▷ X) ≫ act) =
      (((baseChange k K).map i) ▷ ((baseChange k K).obj X)) ≫ baseChangeAction K act := by
  unfold baseChangeAction
  simp only [prodComparisonIso_inv_eq_inv, Functor.map_comp]
  have h := prodComparison_inv_natural_whiskerRight (baseChange k K) (B := X) i
  simpa only [Category.assoc] using congrArg (· ≫ (baseChange k K).map act) h

private theorem baseChange_map_injective {X Y : SchemeOver k} :
    Function.Injective ((baseChange k K).map (X := X) (Y := Y)) := by
  intro f g h
  let p := pullback.fst X.hom (fieldSpecMap k K)
  letI : EffectiveEpi p := baseChangeProjection_effectiveEpi K X
  apply Over.OverMorphism.ext
  apply (cancel_epi p).mp
  rw [← baseChangeProjection_naturality K, ← baseChangeProjection_naturality K]
  rw [h]

private theorem scalarExtended_point_injective (X : SchemeOver k) :
    Function.Injective (scalarExtendedRationalPoint (X := X) K) := by
  intro x y h
  apply baseChange_map_injective K
  exact (cancel_epi (Functor.LaxMonoidal.ε (baseChange k K))).mp h

private theorem scalarExtended_fixed_iff {H X : SchemeOver k} (a : H ⊗ X ⟶ X)
    (x : 𝟙_ (SchemeOver k) ⟶ X) :
    IsFixedBy (baseChangeAction K a) (scalarExtendedRationalPoint K x) ↔ IsFixedBy a x := by
  let F := baseChange k K
  let e := prodComparisonIso F H (𝟙_ (SchemeOver k))
  let i : F.obj H ⊗ (𝟙_ (SchemeOver K)) ⟶ F.obj (H ⊗ (𝟙_ (SchemeOver k))) :=
    (F.obj H ◁ Functor.LaxMonoidal.ε F) ≫ e.inv
  have h : IsIso i := inferInstanceAs
    (IsIso ((F.obj H ◁ Functor.LaxMonoidal.ε F) ≫ e.inv))
  have hl : i ≫ F.map ((H ◁ x) ≫ a) =
      (F.obj H ◁ scalarExtendedRationalPoint K x) ≫ baseChangeAction K a := by
    have he := prodComparison_inv_natural_whiskerLeft F (A := H) x
    change (F.obj H ◁ Functor.LaxMonoidal.ε F) ≫ e.inv ≫ F.map ((H ◁ x) ≫ a) = _
    rw [← prodComparisonIso_inv_eq_inv K H (𝟙_ (SchemeOver k)),
      ← prodComparisonIso_inv_eq_inv K H X] at he
    rw [Functor.map_comp, ← Category.assoc e.inv, he]
    simp only [Category.assoc, scalarExtendedRationalPoint, baseChangeAction]
    rw [MonoidalCategory.whiskerLeft_comp_assoc]
  have hr : i ≫ F.map (snd H (𝟙_ (SchemeOver k)) ≫ x) =
      snd (F.obj H) (𝟙_ (SchemeOver K)) ≫ scalarExtendedRationalPoint K x := by
    rw [Functor.map_comp]
    have he : e.inv ≫ F.map (snd H (𝟙_ (SchemeOver k))) =
        snd (F.obj H) (F.obj (𝟙_ (SchemeOver k))) := by
      rw [show e.inv = inv (CartesianMonoidalCategory.prodComparison F H (𝟙_ (SchemeOver k))) from prodComparisonIso_inv_eq_inv K _ _]
      exact inv_prodComparison_map_snd F H _
    change ((F.obj H ◁ Functor.LaxMonoidal.ε F) ≫ e.inv) ≫ F.map (snd H (𝟙_ (SchemeOver k))) ≫
      F.map x = _
    rw [Category.assoc, ← Category.assoc e.inv, he]
    simp only [whiskerLeft_snd_assoc, scalarExtendedRationalPoint]
    rfl
  unfold IsFixedBy
  rw [← hl, ← hr, cancel_epi]
  exact (baseChange_map_injective K).eq_iff


private theorem range_baseChange_preimage {X Y : SchemeOver k} (f : X ⟶ Y) :
    Set.range ((baseChange k K).map f).left =
      pullback.fst Y.hom (fieldSpecMap k K) ⁻¹' Set.range f.left := by
  let h := baseChangeMapIsPullback K f
  rw [← h.isoPullback_hom_fst]
  change Set.range (pullback.fst (pullback.fst Y.hom (fieldSpecMap k K)) f.left ∘ h.isoPullback.hom) = _
  rw [h.isoPullback.hom.surjective.range_comp, Scheme.Pullback.range_fst]

private theorem baseChange_projection_surjective (Y : SchemeOver k) :
    Function.Surjective (pullback.fst Y.hom (fieldSpecMap k K)) := by
  have hs : Surjective (fieldSpecMap k K) :=
    ⟨fun _ => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  exact (MorphismProperty.of_isPullback (P := @Surjective)
    (IsPullback.of_hasPullback Y.hom (fieldSpecMap k K)).flip hs).surj

end QuotientScalarExtension

section QuotientFixedPoints

open Specs.GeometricRadicals (GeometricGroup IsMaximalTorus IsReductive)
open Specs.GeometricBorelConjugacy (ConjugatesSubgroups IsBorel)
open Specs.RankOneFlag (AreTwoBorels SameSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.QuotientEmbedding (Presentation)
open Specs.NormalizerLatticeAction (IsFixedPoint)
open private quotientAction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
open private restrictGroupAction_smul from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SmoothOrbit
open private fixedPoint_iff_fixedBy from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
open private innerIso transportSubgroup comp_innerMap geometricSmooth
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper

variable {k : Type u} [Field k]

private theorem fixedPoint_iff_subgroup_fixed {G : GroupScheme k} {X : SchemeOver k}
    (a : ModObj G.X X) (T : ClosedSubgroup G) (x : 𝟙_ (SchemeOver k) ⟶ X) :
    IsFixedPoint a T x ↔ IsFixedBy ((T.inclusion.hom.hom ▷ X) ≫ a.smul) x := by
  rw [fixedPoint_iff_fixedBy, restrictGroupAction_smul]
  simp only [tensorHom_def, MonoidalCategory.whiskerLeft_id, Category.comp_id]

private theorem normalizer_coset_has_other_borel_stabilizer [IsAlgClosed k]
    (H : AffineAlgebraicGroup k) (hs : Smooth H.val.X.hom) (hc : ConnectedSpace H.val.X.left)
    {T B₁ B₂ : ClosedSubgroup H.val} (hT : IsMaximalTorus T)
    (h₁ : IsBorel B₁) (h₂ : IsBorel B₂) (hTB₁ : IsSubgroupOf T B₁) (hTB₂ : IsSubgroupOf T B₂)
    (hne : ¬ SameSubgroup B₁ B₂) (Q : Presentation B₁)
    (a : ModObj H.val.X Q.scheme)
    (ha : (𝟙 H.val.X ⊗ₘ Q.projection) ≫ a.smul = μ[H.val.X] ≫ Q.projection)
    (n : 𝟙_ (SchemeOver k) ⟶ H.val.X)
    (hcosets : ∀ g : 𝟙_ (SchemeOver k) ⟶ H.val.X, Normalizes T.inclusion g →
      g ∈ SubgroupSections T (𝟙_ (SchemeOver k)) ∨
        n⁻¹ * g ∈ SubgroupSections T (𝟙_ (SchemeOver k))) :
    RepresentsSubgroup B₂ (fun _ g => Stabilizes a.smul (n ≫ Q.projection) g) := by
  obtain ⟨g, hg, hconj⟩ := MaximalToriConjugate.normalizerTransitiveOnBorels H
    hs hc T hT B₁ B₂ h₁ h₂ hTB₁ hTB₂
  have hsG := quotient_stabilizer_at_translate Q a ha g B₂ hconj
  have hs₀ := quotient_stabilizer_at_translate Q a ha η[H.val.X] B₁ (conjugates_by_identity B₁)
  rcases quotient_normalizer_points_of_two_cosets hTB₁ Q n g (hcosets g hg) with eq | eq
  · rw [eq] at hsG
    exact False.elim (hne (same_subgroup_of_same_sections (H := H) hs₀ hsG))
  · rw [eq] at hsG
    exact hsG

private theorem normalizer_conjugacy_of_borel_pair
    {H : AffineAlgebraicGroup k} {T B₁ B₂ : ClosedSubgroup H.val}
    (hH : IsReductive H) (hTm : Specs.RankOneFlag.IsGeometricallyMaximal T)
    (hB : AreTwoBorels T B₁ B₂)
    (n : 𝟙_ (SchemeOver k) ⟶ H.val.X)
    (hn : Normalizes ((extendSubgroup (AlgebraicClosure k) T).inclusion)
      (scalarExtendedRationalPoint (AlgebraicClosure k) n))
    (hcst :
      let K := AlgebraicClosure k
      let T' := extendSubgroup K T
      ∀ g : 𝟙_ (SchemeOver K) ⟶ (GeometricGroup H).val.X, Normalizes T'.inclusion g →
        g ∈ SubgroupSections T' (𝟙_ (SchemeOver K)) ∨
          (show 𝟙_ (SchemeOver K) ⟶ (GeometricGroup H).val.X from scalarExtendedRationalPoint K n)⁻¹ * g ∈ SubgroupSections T' (𝟙_ (SchemeOver K)))
    (hN :
      let K := AlgebraicClosure k
      ∃ N : ClosedSubgroup (GeometricGroup H).val, RepresentsSubgroup N
        (fun _ g => Normalizes (extendSubgroup K T).inclusion g))
    (Q : Presentation B₁) :
    let a := quotientAction Q
    ConjugatesSubgroups n B₁ B₂ ∧
    (η[H.val.X] ≫ Q.projection ≠ n ≫ Q.projection) ∧
    (∀ x : 𝟙_ (SchemeOver k) ⟶ Q.scheme,
      IsFixedBy ((T.inclusion.hom.hom ▷ Q.scheme) ≫ a.smul) x ↔
        x = η[H.val.X] ≫ Q.projection ∨ x = n ≫ Q.projection) ∧
    (∀ x : 𝟙_ (SchemeOver (AlgebraicClosure k)) ⟶ (baseChange k (AlgebraicClosure k)).obj Q.scheme,
      IsFixedBy (baseChangeAction (AlgebraicClosure k) ((T.inclusion.hom.hom ▷ Q.scheme) ≫ a.smul)) x ↔
        x = scalarExtendedRationalPoint (AlgebraicClosure k) (η[H.val.X] ≫ Q.projection) ∨
          x = scalarExtendedRationalPoint (AlgebraicClosure k) (n ≫ Q.projection)) := by
  intro a
  let K := AlgebraicClosure k
  let H' := GeometricGroup H
  let T' := extendSubgroup K T
  let B₁' := extendSubgroup K B₁
  let B₂' := extendSubgroup K B₂
  let n' := scalarExtendedRationalPoint K n
  let P := baseChangeQuotientPresentation K (G := H) Q
  have hH's : Smooth H'.val.X.hom := geometricSmooth H hH.1
  have hH'c : ConnectedSpace H'.val.X.left :=
    hH.2.1.geometrically_connectedSpace _ _ _ (IsPullback.of_hasPullback _ _)
  obtain ⟨⟨_, h₁⟩, ⟨_, h₂⟩, hne, hTB₁, hTB₂, _⟩ := hB
  have hne' : ¬ SameSubgroup B₁' B₂' := fun h =>
    hne ⟨subgroupOf_of_extend h.1, subgroupOf_of_extend h.2⟩
  have hT' : IsMaximalTorus T' := hTm.choose_spec
  have hTB₁' : IsSubgroupOf T' B₁' := extend_subgroupOf hTB₁
  have hTB₂' : IsSubgroupOf T' B₂' := extend_subgroupOf hTB₂
  obtain ⟨hneP, _⟩ := borels_through_torus_of_two_normalizer_cosets
    hH's hH'c hT' h₁ h₂ hTB₁' hTB₂' hne' P n' hcst
  obtain ⟨N, hN⟩ := hN
  obtain ⟨b, hb, hfixed⟩ := quotient_fixed_points_of_two_normalizer_cosets
    hH's hH'c hT' h₁ hTB₁' hN P n' hn hcst
  have ha := quotient_action_equivariant Q
  have hP : b.smul = baseChangeAction K a.smul := by
    letI := tensor_left_epi_of_flat_surjective (X := H'.val.X) P.flat P.surjective
    apply (cancel_epi (H'.val.X ◁ P.projection)).mp
    have hc := quotient_smul_baseChange_support K Q.projection a.smul
      (by simpa only [tensorHom_def, MonoidalCategory.id_whiskerRight, Category.id_comp] using ha)
    have hD : (H'.val.X ◁ P.projection) ≫ b.smul = μ[H'.val.X] ≫ P.projection := by
      simpa only [tensorHom_def, MonoidalCategory.id_whiskerRight, Category.id_comp] using hb
    exact hD.trans hc.symm
  have hOne : scalarExtendedRationalPoint K (η[H.val.X]) = η[H'.val.X] := rfl
  have h₀ : scalarExtendedRationalPoint K (η[H.val.X] ≫ Q.projection) =
      η[H'.val.X] ≫ P.projection := by
    rw [scalarExtendedPoint_natural, hOne]
    rfl
  have h₁' : scalarExtendedRationalPoint K (n ≫ Q.projection) = n' ≫ P.projection :=
    scalarExtendedPoint_natural K n Q.projection
  have hfixGeom (x : 𝟙_ (SchemeOver K) ⟶ P.scheme) :
      IsFixedBy (baseChangeAction K ((T.inclusion.hom.hom ▷ Q.scheme) ≫ a.smul)) x ↔
        x = scalarExtendedRationalPoint K (η[H.val.X] ≫ Q.projection) ∨
          x = scalarExtendedRationalPoint K (n ≫ Q.projection) := by
    rw [baseChange_smul_restriction, ← hP, h₀, h₁']
    exact ((fixedPoint_iff_subgroup_fixed b T' x).symm.trans (hfixed x))
  have hDistinct : η[H.val.X] ≫ Q.projection ≠ n ≫ Q.projection := by
    intro h
    apply hneP
    rw [← h₁', ← h₀, h]
  refine ⟨?_, hDistinct, ?_, hfixGeom⟩
  · have hstabG := normalizer_coset_has_other_borel_stabilizer H' hH's hH'c
      hT' h₁ h₂ hTB₁' hTB₂' hne' P b hb n' hcst
    let B := transportSubgroup B₁ (innerIso n)
    have hBn : ConjugatesSubgroups n B₁ B := by
      refine ⟨Iso.refl _, ?_⟩
      dsimp only [Iso.refl_hom]
      rw [Category.id_comp]
      exact comp_innerMap n B₁.inclusion.hom.hom
    have hstab := quotient_stabilizer_at_translate Q a ha n B hBn
    obtain ⟨_, hstab'⟩ := stabilizerSchemeBaseChange k K a.smul (n ≫ Q.projection) B hstab
    rw [← hP, h₁'] at hstab'
    have heq : SameSubgroup (extendSubgroup K B) B₂' :=
      same_subgroup_of_same_sections (H := H') hstab' hstabG
    obtain ⟨i, hi⟩ := subgroupIso_of_same
      (show SameSubgroup B B₂ from ⟨subgroupOf_of_extend heq.1, subgroupOf_of_extend heq.2⟩)
    refine ⟨i, ?_⟩
    rw [hi]
    exact comp_innerMap n B₁.inclusion.hom.hom
  · intro x
    rw [← scalarExtended_fixed_iff K]
    exact (hfixGeom (scalarExtendedRationalPoint K x)).trans
      (or_congr (scalarExtended_point_injective K _).eq_iff (scalarExtended_point_injective K _).eq_iff)

end QuotientFixedPoints

section SplitContracting

open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open CocharacterDynamics (LimitDecomposition)
open private group_geometricallyIrreducible from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterOpenCell
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private affinePointEquiv affinePointEquiv_natural smooth_affine_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterSmoothAndUnipotent

open Polynomial
variable {k : Type u} [Field k]

private abbrev affineLine (k : Type u) [Field k] : SchemeOver k :=
  (testSpec k).obj (op (CommAlgCat.of k (Polynomial k)))

private def affineLineZero (k : Type u) [Field k] :
    Points (affineLine k) (CommAlgCat.of k k) :=
  (testSpec k).map (CommAlgCat.ofHom (Polynomial.aeval (0 : k))).op

private theorem contracting_line_of_cotangent {G : GroupScheme k}
    (hG : IsAffine G.X.left) {c : Cocharacter G} (D : LimitDecomposition c)
    (A : TestAlgebra k) [IsDomain A] (e : (testSpec k).obj (op A) ≅ D.contracting.group.X)
    (ε : A →ₐ[k] k) (hε : affinePointEquiv e (CommAlgCat.of k k) ε = 1)
    (hdim : Module.finrank k (RingHom.ker ε.toRingHom).Cotangent = 1) :
    ∃ i : affineLine k ≅ D.contracting.group.X,
      affineLineZero k ≫ i.hom = 1 ∧ Specs.RankOneFlag.IsSplitAdditive D.contracting.group := by
  obtain ⟨p, h₁, hc, h₀⟩ := contracting_coordinate_grading hG c D A e ε hε
  obtain ⟨x, d, _, hx, _, hb⟩ := exists_positive_polynomial_coordinate ε p h₁ hc h₀ hdim
  let a : Polynomial k ≃ₐ[k] A := AlgEquiv.ofBijective (aeval x) hb
  let a' : CommAlgCat.of k (Polynomial k) ≅ A := CommAlgCat.isoMk a
  let i : affineLine k ≅ D.contracting.group.X := (testSpec k).mapIso a'.symm.op ≪≫ e
  have hε' : ε.comp a = aeval (0 : k) := by
    apply Polynomial.algHom_ext
    change ε ((aeval x : Polynomial k →ₐ[k] A) X) = _
    rw [aeval_X, aeval_X, hx]
  have hP : affineLineZero k ≫ i.hom = affinePointEquiv e (CommAlgCat.of k k) ε := by
    change (testSpec k).map (CommAlgCat.ofHom (aeval (0 : k))).op ≫
      (testSpec k).map a'.inv.op ≫ e.hom = _
    rw [← Category.assoc, ← Functor.map_comp]
    congr 1
    apply congrArg ((testSpec k).map)
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    change (aeval (0 : k)).comp a.symm = ε
    apply AlgHom.ext
    intro y
    change aeval (0 : k) (a.symm y) = ε y
    rw [← hε', AlgHom.comp_apply]
    exact congrArg ε (a.apply_symm_apply y)
  have hA : IsAffine D.contracting.group.X.left := by
    haveI : IsIso i.inv.left := (Over.forget _).map_isIso i.inv
    letI : IsAffine (affineLine k).left :=
      inferInstanceAs (IsAffine (Spec (CommRingCat.of (Polynomial k))))
    exact IsAffine.of_isIso i.inv.left
  refine ⟨i, hP.trans hε, ?_⟩
  let precompose (R : TestAlgebra k) : (A →ₐ[k] R) ≃ (Polynomial k →ₐ[k] R) :=
    { toFun := fun b => b.comp a
      invFun := fun b => b.comp a.symm
      left_inv := by
        intro b
        apply AlgHom.ext
        intro y
        exact congrArg b (a.apply_symm_apply y)
      right_inv := by
        intro b
        apply AlgHom.ext
        intro y
        exact congrArg b (a.symm_apply_apply y) }
  let point (R : TestAlgebra k) : (A →ₐ[k] R) ≃ GroupPoints D.contracting.group R :=
    affinePointEquiv e R
  let coordinate (R : TestAlgebra k) : GroupPoints D.contracting.group R ≃ R :=
    (point R).symm.trans ((precompose R).trans (Polynomial.aevalEquiv k R).symm)
  have hcoord (R : TestAlgebra k) (v : A →ₐ[k] R) :
      coordinate R (affinePointEquiv e R v) = v x := by
    change ((point R).symm (point R v)) (a X) = v x
    rw [(point R).symm_apply_apply v]
    change v ((aeval x : Polynomial k →ₐ[k] A) X) = v x
    rw [aeval_X]
  refine split_additive_of_coordinate hA coordinate ?_ ?_
  · intro R S b y
    obtain ⟨v, rfl⟩ := (affinePointEquiv e R).surjective y
    rw [← affinePointEquiv_natural, hcoord, hcoord]
    rfl
  · intro R
    let u : CommAlgCat.of k k ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
    have hm : (mapPoints u (1 : GroupPoints D.contracting.group (CommAlgCat.of k k)) :
        GroupPoints D.contracting.group R) = 1 :=
      (((groupPointsFunctor k).obj D.contracting.group).map u).hom.map_one
    rw [← hm, ← hε, ← affinePointEquiv_natural, hcoord]
    change algebraMap k R (ε x) = 0
    rw [hx, map_zero]


private theorem contracting_line_from_affine_charts
    (G : AffineAlgebraicGroup k) {c : Cocharacter G.val} (D : LimitDecomposition c)
    (hs : Smooth D.contracting.group.X.hom) (hc : ConnectedSpace D.contracting.group.X.left)
    {X V : SchemeOver k} [IsSeparated X.hom] [IrreducibleSpace X.left]
    (j : D.contracting.group.X ⟶ X) (v : V ⟶ X) [IsOpenImmersion j.left] [IsOpenImmersion v.left]
    (hV : IsAffine V.left) (hne : Nonempty V.left)
    (hr : Set.range v.left = ({sectionSupport (η[D.contracting.group.X] ≫ j)} : Set X.left)ᶜ) :
    ∃ i : affineLine k ≅ D.contracting.group.X,
      affineLineZero k ≫ i.hom = 1 ∧ Specs.RankOneFlag.IsSplitAdditive D.contracting.group := by
  let U := D.contracting.group.X
  let W := closedSubgroupAlgebraicGroup (G := G) D.contracting
  letI : ConnectedSpace W.val.X.left := hc
  letI : GeometricallyIrreducible U.hom := group_geometricallyIrreducible W
  letI : IrreducibleSpace U.left := GeometricallyIrreducible.irreducibleSpace_of_subsingleton U.hom
  letI : Smooth U.hom := hs
  letI : IsReduced U.left := isReduced_of_smooth_over_field U.hom
  letI : IsIntegral U.left := isIntegral_of_irreducibleSpace_of_isReduced _
  obtain ⟨R, ⟨e₀⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr W.property.1
  let A := R.unop
  let e : (testSpec k).obj (op A) ≅ U := e₀
  letI : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
  letI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  letI : IsIntegral (Spec (CommRingCat.of A)) := IsIntegral.of_isIso e.inv.left
  letI : IsDomain A :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain
      Γ(Spec (CommRingCat.of A), ⊤)
  letI : Algebra.Smooth k A := (smooth_affine_iff e).mp hs
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  let F := CommAlgCat.of k k
  let ε : A →ₐ[k] k := (affinePointEquiv e F).symm 1
  have hε : affinePointEquiv e F ε = 1 := (affinePointEquiv e F).apply_symm_apply _
  have hsur : Function.Surjective ε := fun x => ⟨algebraMap k A x, AlgHom.commutes ε x⟩
  let I := RingHom.ker ε.toRingHom
  letI : I.IsMaximal := RingHom.ker_isMaximal_of_surjective ε.toRingHom hsur
  let p : PrimeSpectrum A := ⟨I, inferInstance⟩
  have hp : p = PrimeSpectrum.comap ε.toRingHom (IsLocalRing.closedPoint k) := by
    apply PrimeSpectrum.ext
    change RingHom.ker ε.toRingHom = (IsLocalRing.maximalIdeal k).comap ε.toRingHom
    rw [IsLocalRing.maximalIdeal_eq_bot, RingHom.ker_eq_comap_bot]
  have hq := congrArg (fun f : Points U F => f.left (IsLocalRing.closedPoint k)) hε
  have he : e.hom.left p = sectionSupport (η[U]) := by
    change e.hom.left (PrimeSpectrum.comap ε.toRingHom (IsLocalRing.closedPoint k)) =
      η[U].left ((toUnit ((testSpec k).obj (op F))).left (IsLocalRing.closedPoint k)) at hq
    rw [hp, sectionSupport]
    letI : Subsingleton (𝟙_ (SchemeOver k)).left :=
      inferInstanceAs (Subsingleton (PrimeSpectrum k))
    exact hq.trans (congrArg (η[U].left) (Subsingleton.elim _ _))
  letI : IsOpenImmersion (e.hom ≫ j).left :=
    inferInstanceAs (IsOpenImmersion (e.hom.left ≫ j.left))
  have hr' : Set.range v.left = ({(e.hom ≫ j).left p} : Set X.left)ᶜ := by
    have hvalue : sectionSupport (η[U] ≫ j) = (e.hom ≫ j).left p :=
      (sectionSupport_comp _ _).trans (congrArg j.left he.symm)
    rw [hr, hvalue]
  have hd : I.height = 1 :=
    height_one_from_affine_charts A (e.hom ≫ j) v hV hne p inferInstance hr'
  exact contracting_line_of_cotangent G.property.1 D A e ε hε
    (cotangent_finrank_one_at_rational_height_one (smooth_domain_normal k A) ε hd)

end SplitContracting

section ContractingCellAction

open Specs.CharacterDescent (Cocharacter)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.QuotientEmbedding (Presentation)
open CocharacterDynamics (LimitDecomposition)
open private centralizes_iff conjugateLe_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private innerMap comp_innerMap from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper
open private translateAction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
open private projection_eq_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.QuotientEmbedding

variable {k : Type u} [Field k]

private theorem translateAction_comp {G : GroupScheme k} {X : SchemeOver k}
    (a : ModObj G.X X) (g h : 𝟙_ (SchemeOver k) ⟶ G.X) :
    (translateAction a g).hom ≫ (translateAction a h).hom = (translateAction a (h * g)).hom := by
  letI := a
  change ((toUnit X ≫ g) • (𝟙 X)) ≫ ((toUnit X ≫ h) • (𝟙 X)) =
    (toUnit X ≫ (h * g)) • (𝟙 X)
  rw [ModObj.comp_smul, comp_toUnit_assoc, Category.comp_id, MonObj.comp_mul, mul_smul]

private theorem translateAction_on_section {G : GroupScheme k} {X : SchemeOver k}
    (a : ModObj G.X X) (g : 𝟙_ (SchemeOver k) ⟶ G.X) (x : 𝟙_ (SchemeOver k) ⟶ X) :
    x ≫ (translateAction a g).hom = lift g x ≫ a.smul := by
  letI := a
  change x ≫ ((toUnit X ≫ g) • (𝟙 X)) = g • x
  rw [ModObj.comp_smul, comp_toUnit_assoc, Category.comp_id,
    show toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ from Subsingleton.elim _ _, Category.id_comp]

private theorem translateAction_stable_of_inclusions {G : GroupScheme k} {X U : SchemeOver k}
    (a : ModObj G.X X) (j : U ⟶ X) {g : 𝟙_ (SchemeOver k) ⟶ G.X}
    (h₁ : Set.range (j ≫ (translateAction a g).hom).left ⊆ Set.range j.left)
    (h₂ : Set.range (j ≫ (translateAction a g⁻¹).hom).left ⊆ Set.range j.left)
    (x : 𝟙_ (SchemeOver k) ⟶ X) :
    sectionSupport (lift g x ≫ a.smul) ∈ Set.range j.left ↔ sectionSupport x ∈ Set.range j.left := by
  let e := translateAction a g
  rw [← translateAction_on_section, sectionSupport_comp]
  constructor
  · rintro ⟨u, hu⟩
    apply h₂
    refine ⟨u, ?_⟩
    change e.inv.left (j.left u) = sectionSupport x
    rw [hu]
    exact congrArg (fun f : X ⟶ X => f.left (sectionSupport x)) e.hom_inv_id
  · rintro ⟨u, hu⟩
    exact h₁ ⟨u, congrArg e.hom.left hu⟩

private theorem contracting_of_cast {G : GroupScheme k} {c d : Cocharacter G}
    (h : c = d) (D : LimitDecomposition c) :
    (h ▸ D : LimitDecomposition d).contracting = D.contracting := by
  subst d
  rfl

/-- The rational points of the common Levi preserve the opposite cell.
Conjugation preserves the contracting subgroup and right multiplication by
the Levi gives the same coset. -/
private theorem translates_preserve_contracting_cell {H : AffineAlgebraicGroup k}
    {c : Cocharacter H.val} (E : LimitDecomposition c) {T B : ClosedSubgroup H.val}
    (hTC : IsSubgroupOf T E.centralizer) (hTB : IsSubgroupOf T B)
    (Q : Presentation B) (a : ModObj H.val.X Q.scheme)
    (ha : (𝟙 H.val.X ⊗ₘ Q.projection) ≫ a.smul = μ[H.val.X] ≫ Q.projection)
    (t : 𝟙_ (SchemeOver k) ⟶ T.group.X) :
    let j := E.contracting.inclusion.hom.hom ≫ Q.projection
    let n := t ≫ T.inclusion.hom.hom
    Set.range (j ≫ (translateAction a n).hom).left ⊆ Set.range j.left := by
  intro j n
  obtain ⟨f, hf⟩ := hTC
  have hc : Centralizes c n := (E.centralizer_points _ _).mpr
    ⟨t ≫ f.hom.hom, (Category.assoc _ _ _).trans
      (congrArg (t ≫ ·) ((Grp.forget (SchemeOver k)).congr_map hf))⟩
  have he : c ≫ innerMap n = c := by
    apply Grp.hom_ext
    change c.hom.hom ≫ (innerMap n).hom.hom = c.hom.hom
    rw [comp_innerMap]
    have h := (centralizes_iff c n).mp hc _ (toUnit _) (𝟙 _)
    rw [Category.id_comp] at h
    rw [h.eq, mul_assoc, mul_inv_cancel, mul_one]
  let F : LimitDecomposition (c ≫ innerMap n) := he.symm ▸ E
  have hF : F.contracting = E.contracting := contracting_of_cast he.symm E
  have hm := map_limit_contracting H.property.1 (innerMap n) E F
  rw [hF] at hm
  obtain ⟨r, hr⟩ := hm
  let Z := E.contracting.group.X
  let b := E.contracting.inclusion.hom.hom
  let n₀ := toUnit Z ≫ n
  have hb : (r ≫ E.contracting.inclusion).hom.hom = n₀ * b * n₀⁻¹ := by
    change (r ≫ E.contracting.inclusion).hom.hom =
      n₀ * E.contracting.inclusion.hom.hom * n₀⁻¹
    rw [hr, Grp.comp_hom_hom, comp_innerMap]
  have htran : j ≫ (translateAction a n).hom = (n₀ * b) ≫ Q.projection := by
    letI := a
    change j ≫ ((toUnit Q.scheme ≫ n) • (𝟙 Q.scheme)) = _
    rw [ModObj.comp_smul, comp_toUnit_assoc, Category.comp_id]
    exact quotient_action_formula Q a ha n₀ b
  have hproj : (n₀ * b) ≫ Q.projection = (n₀ * b * n₀⁻¹) ≫ Q.projection := by
    rw [projection_eq_iff, inv_mul_cancel_left]
    obtain ⟨u, hu⟩ := hTB
    let v := toUnit Z ≫ t ≫ u.hom.hom
    refine ⟨v⁻¹, ?_⟩
    change v⁻¹ ≫ B.inclusion.hom.hom = n₀⁻¹
    rw [GrpObj.inv_comp]
    congr 1
    change toUnit Z ≫ t ≫ u.hom.hom ≫ B.inclusion.hom.hom = _
    rw [show u.hom.hom ≫ B.inclusion.hom.hom = T.inclusion.hom.hom from
      (Grp.forget (SchemeOver k)).congr_map hu]
  have heq : j ≫ (translateAction a n).hom = r.hom.hom ≫ j := by
    rw [htran, hproj, ← hb]
    simp only [j, Grp.comp_hom_hom, Category.assoc]
  rw [heq, Over.comp_left]
  change Set.range (j.left ∘ r.hom.hom.left) ⊆ _
  exact Set.range_comp_subset_range _ _

private theorem translating_cell_by_normalizer_preserves_stability
    {G : GroupScheme k} {X U : SchemeOver k} (a : ModObj G.X X) (j : U ⟶ X)
    (T : ClosedSubgroup G) (n : 𝟙_ (SchemeOver k) ⟶ G.X)
    (hn : Normalizes T.inclusion n)
    (h : ∀ t : 𝟙_ (SchemeOver k) ⟶ T.group.X,
      Set.range (j ≫ (translateAction a (t ≫ T.inclusion.hom.hom)).hom).left ⊆ Set.range j.left)
    (t : 𝟙_ (SchemeOver k) ⟶ T.group.X) :
    let v := j ≫ (translateAction a n).hom
    Set.range (v ≫ (translateAction a (t ≫ T.inclusion.hom.hom)).hom).left ⊆ Set.range v.left := by
  intro v
  have hn' := ((normalizesIff k T.inclusion T.isClosedImmersion _ n).mp hn).2
  obtain ⟨u, hu⟩ := (conjugateLe_iff T.inclusion n⁻¹).mp hn'
    (𝟙_ (SchemeOver k)) (𝟙 _) t
  simp only [Category.id_comp, inv_inv] at hu
  have he : (t ≫ T.inclusion.hom.hom) * n = n * (u ≫ T.inclusion.hom.hom) := by
    rw [hu, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  change Set.range ((j ≫ (translateAction a n).hom) ≫
    (translateAction a (t ≫ T.inclusion.hom.hom)).hom).left ⊆ _
  rw [Category.assoc, translateAction_comp, he, ← translateAction_comp, ← Category.assoc]
  rw [Over.comp_left, show v.left = j.left ≫ (translateAction a n).hom.left from rfl]
  change Set.range ((translateAction a n).hom.left ∘
    (j ≫ (translateAction a (u ≫ T.inclusion.hom.hom)).hom).left) ⊆
    Set.range ((translateAction a n).hom.left ∘ j.left)
  rw [Set.range_comp, Set.range_comp]
  exact Set.image_mono (h u)

end ContractingCellAction

section GeometricOpenCell

open Specs.SmoothOrbit (orbitSet)
open Specs.SchemeDerivedGroup (IsSolvable)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private restrictGroupAction restrictGroupAction_smul from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SmoothOrbit
open private fixed_point_in_orbit_closure translateAction
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
open private sectionOfClosedPoint sectionOfClosedPoint_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry

set_option maxHeartbeats 1100000

variable {k : Type u} [Field k] [IsAlgClosed k]

private theorem opposite_cell_range_from_fixed_points
    {H : AffineAlgebraicGroup k} (T : ClosedSubgroup H.val)
    (hs : Smooth T.group.X.hom) (hc : ConnectedSpace T.group.X.left) (hsol : IsSolvable T.group)
    {X U : SchemeOver k} [IsProper X.hom]
    (a : ModObj H.val.X X) (x : 𝟙_ (SchemeOver k) ⟶ X)
    (j : U ⟶ X) [IsOpenImmersion j.left] (hU : IsAffine U.left)
    (hx : sectionSupport x ∈ Set.range j.left)
    (n : 𝟙_ (SchemeOver k) ⟶ H.val.X) (hn : Normalizes T.inclusion n)
    (hy : sectionSupport (x ≫ (translateAction a n).hom) ∉ Set.range j.left)
    (hfix : ∀ z : 𝟙_ (SchemeOver k) ⟶ X,
      IsFixedBy ((T.inclusion.hom.hom ▷ X) ≫ a.smul) z →
        z = x ∨ z = x ≫ (translateAction a n).hom)
    (hst : ∀ t : 𝟙_ (SchemeOver k) ⟶ T.group.X,
      Set.range (j ≫ (translateAction a (t ≫ T.inclusion.hom.hom)).hom).left ⊆ Set.range j.left) :
    Set.range j.left = ({sectionSupport (x ≫ (translateAction a n).hom)} : Set X.left)ᶜ := by
  let aT := restrictGroupAction T.inclusion a
  let v := j ≫ (translateAction a n).hom
  let A := closedSubgroupAlgebraicGroup T
  haveI : LocallyOfFiniteType T.group.X.hom := A.property.2.1
  haveI : ConnectedSpace T.group.X.left := hc
  haveI : JacobsonSpace T.group.X.left := LocallyOfFiniteType.jacobsonSpace T.group.X.hom
  haveI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hAct : aT.smul = (T.inclusion.hom.hom ▷ X) ≫ a.smul := by
    rw [restrictGroupAction_smul, tensorHom_def, MonoidalCategory.whiskerLeft_id, Category.comp_id]
  have hT (t : 𝟙_ (SchemeOver k) ⟶ T.group.X) (z : 𝟙_ (SchemeOver k) ⟶ X) :
      lift t z ≫ aT.smul = lift (t ≫ T.inclusion.hom.hom) z ≫ a.smul := by
    change lift t z ≫ (restrictGroupAction T.inclusion a).smul = _
    simp only [restrictGroupAction_smul, lift_map_assoc, Category.comp_id]
  have hv : ∀ t : 𝟙_ (SchemeOver k) ⟶ T.group.X,
      Set.range (v ≫ (translateAction a (t ≫ T.inclusion.hom.hom)).hom).left ⊆ Set.range v.left :=
    translating_cell_by_normalizer_preserves_stability a j T n hn hst
  letI : IsIso (translateAction a n).hom.left := (Over.forget _).map_isIso (translateAction a n).hom
  letI : IsOpenImmersion v.left := inferInstanceAs
    (IsOpenImmersion (j.left ≫ (translateAction a n).hom.left))
  have hr (z : 𝟙_ (SchemeOver k) ⟶ X) :
      ∃ y : 𝟙_ (SchemeOver k) ⟶ X,
        sectionSupport y ∈ closure (orbitSet aT z) ∧ IsFixedBy aT.smul y :=
    fixed_point_in_orbit_closure A hs hc hsol aT z
  refine range_eq_compl_of_two_fixed aT
    (fun t h => ⟨sectionOfClosedPoint T.group.X t h, sectionOfClosedPoint_apply _ _ _⟩)
    (fun t h => ⟨sectionOfClosedPoint X t h, sectionOfClosedPoint_apply _ _ _⟩)
    hr x (x ≫ (translateAction a n).hom) (fun z hz => hfix z (hAct ▸ hz))
    j v hU hx ?_ hy ?_ ?_
  · obtain ⟨z, hz⟩ := hx
    rw [sectionSupport_comp]
    exact ⟨z, congrArg (translateAction a n).hom.left hz⟩
  · intro t z
    rw [hT]
    exact translateAction_stable_of_inclusions a j (hst t)
      (by simpa only [GrpObj.inv_comp] using hst t⁻¹) z
  · intro t z
    rw [hT]
    exact translateAction_stable_of_inclusions a v (hv t)
      (by simpa only [GrpObj.inv_comp] using hv t⁻¹) z

end GeometricOpenCell

section OpenChartGluing



private theorem open_chart_overlap {L U V X : Scheme.{u}} {l : L ⟶ U} {m : L ⟶ V}
    {i : U ⟶ X} {j : V ⟶ X} [IsOpenImmersion l] [IsOpenImmersion j]
    (h : l ≫ i = m ≫ j)
    (hr : Set.range l = i ⁻¹' Set.range j) : IsPullback l m i j := by
  let f := IsOpenImmersion.isoOfRangeEq l (pullback.fst i j)
    (hr.trans (Scheme.Pullback.range_fst i j).symm)
  have hl : f.hom ≫ pullback.fst i j = l := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  refine IsPullback.of_iso_pullback ⟨h⟩ f hl ?_
  apply (cancel_mono j).mp
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, hl, h]

private def openCoverPair {A X : Scheme.{u}} (f₀ f₁ : A ⟶ X)
    [IsOpenImmersion f₀] [IsOpenImmersion f₁]
    (h : ∀ x : X, x ∈ Set.range f₀ ∨ x ∈ Set.range f₁) : X.OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun _ ↦ A) (fun b ↦ if b then f₁ else f₀)
    (fun x ↦ by
      rcases h x with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · exact ⟨false, y, rfl⟩
      · exact ⟨true, y, rfl⟩)
    (by intro b; cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance)

private theorem morphism_of_common_chart_overlap {A L X Y : Scheme.{u}} (f₀ f₁ : A ⟶ X)
    [IsOpenImmersion f₀] [IsOpenImmersion f₁]
    (hf : ∀ x : X, x ∈ Set.range f₀ ∨ x ∈ Set.range f₁)
    (g₀ g₁ : A ⟶ Y) (l m : L ⟶ A)
    (h : IsPullback l m f₀ f₁) (he : l ≫ g₀ = m ≫ g₁) :
    ∃ φ : X ⟶ Y, f₀ ≫ φ = g₀ ∧ f₁ ≫ φ = g₁ := by
  let C := openCoverPair f₀ f₁ hf
  let g (b : C.I₀) : C.X b ⟶ Y := if (show Bool from b) then g₁ else g₀
  have hglue (b d : C.I₀) : pullback.fst (C.f b) (C.f d) ≫ g b =
      pullback.snd (C.f b) (C.f d) ≫ g d := by
    cases b <;> cases d
    · change pullback.fst f₀ f₀ ≫ g₀ = pullback.snd f₀ f₀ ≫ g₀
      rw [(cancel_mono f₀).mp pullback.condition]
    · change pullback.fst f₀ f₁ ≫ g₀ = pullback.snd f₀ f₁ ≫ g₁
      apply (cancel_epi h.isoPullback.hom).mp
      rwa [← Category.assoc, h.isoPullback_hom_fst, ← Category.assoc, h.isoPullback_hom_snd]
    · change pullback.fst f₁ f₀ ≫ g₁ = pullback.snd f₁ f₀ ≫ g₀
      apply (cancel_epi h.flip.isoPullback.hom).mp
      rw [← Category.assoc, h.flip.isoPullback_hom_fst, ← Category.assoc, h.flip.isoPullback_hom_snd]
      exact he.symm
    · change pullback.fst f₁ f₁ ≫ g₁ = pullback.snd f₁ f₁ ≫ g₁
      rw [(cancel_mono f₁).mp pullback.condition]
  exact ⟨C.glueMorphisms g hglue, C.ι_glueMorphisms g hglue false, C.ι_glueMorphisms g hglue true⟩

private theorem iso_of_common_chart_overlap {A L X Y : Scheme.{u}} (f₀ f₁ : A ⟶ X)
    (g₀ g₁ : A ⟶ Y) [IsOpenImmersion f₀] [IsOpenImmersion f₁]
    [IsOpenImmersion g₀] [IsOpenImmersion g₁]
    (hf : ∀ x : X, x ∈ Set.range f₀ ∨ x ∈ Set.range f₁)
    (hg : ∀ y : Y, y ∈ Set.range g₀ ∨ y ∈ Set.range g₁)
    (l m : L ⟶ A) (hX : IsPullback l m f₀ f₁) (hY : IsPullback l m g₀ g₁) :
    ∃ e : X ≅ Y, f₀ ≫ e.hom = g₀ ∧ f₁ ≫ e.hom = g₁ := by
  obtain ⟨f, hf₀, hf₁⟩ := morphism_of_common_chart_overlap f₀ f₁ hf g₀ g₁ l m hX hY.w
  obtain ⟨g, hg₀, hg₁⟩ := morphism_of_common_chart_overlap g₀ g₁ hg f₀ f₁ l m hY hX.w
  refine ⟨⟨f, g, ?_, ?_⟩, hf₀, hf₁⟩
  · apply (openCoverPair f₀ f₁ hf).hom_ext
    intro b
    cases b
    · change f₀ ≫ f ≫ g = f₀ ≫ 𝟙 _
      rw [← Category.assoc, hf₀, hg₀, Category.comp_id]
    · change f₁ ≫ f ≫ g = f₁ ≫ 𝟙 _
      rw [← Category.assoc, hf₁, hg₁, Category.comp_id]
  · apply (openCoverPair g₀ g₁ hg).hom_ext
    intro b
    cases b
    · change g₀ ≫ g ≫ f = g₀ ≫ 𝟙 _
      rw [← Category.assoc, hg₀, hf₀, Category.comp_id]
    · change g₁ ≫ g ≫ f = g₁ ≫ 𝟙 _
      rw [← Category.assoc, hg₁, hf₁, Category.comp_id]

end OpenChartGluing

section ProjectiveLineCharts

open Specs.RankOneFlag (Index plane planeBasis projectiveLine)
open Specs.ProjectiveSpaces
open private ratio_self from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.ProjectiveSpaces

set_option maxHeartbeats 1800000
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

private abbrev puncturedLine (k : Type u) [Field k] : SchemeOver k :=
  (testSpec k).obj (op (CommAlgCat.of k (LaurentPolynomial k)))

private def invertLaurent (k : Type u) [Field k] : LaurentPolynomial k ≃ₐ[k] LaurentPolynomial k :=
  { LaurentPolynomial.invert with commutes' := LaurentPolynomial.invert_C }

private def puncturedLineInclusion (k : Type u) [Field k] : puncturedLine k ⟶ affineLine k :=
  (testSpec k).map (CommAlgCat.ofHom Polynomial.toLaurentAlg).op

private def inverseParameter (k : Type u) [Field k] : puncturedLine k ⟶ affineLine k :=
  (testSpec k).map (CommAlgCat.ofHom ((invertLaurent k).toAlgHom.comp Polynomial.toLaurentAlg)).op

private theorem puncturedLineOpen (k : Type u) [Field k] :
    IsOpenImmersion (puncturedLineInclusion k).left := by
  have h : (Polynomial.toLaurent : Polynomial k →+* LaurentPolynomial k) = algebraMap (Polynomial k) (LaurentPolynomial k) := by
    exact RingHom.ext (fun x => (LaurentPolynomial.algebraMap_eq_toLaurent x).symm)
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial k →+* LaurentPolynomial k)))
  rw [h]
  exact IsOpenImmersion.of_isLocalization (S := LaurentPolynomial k) (Polynomial.X : Polynomial k)

private theorem puncturedLineRange (k : Type u) [Field k] :
    Set.range (puncturedLineInclusion k).left =
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) : Set (PrimeSpectrum (Polynomial k))) := by
  have h : (Polynomial.toLaurent : Polynomial k →+* LaurentPolynomial k) = algebraMap (Polynomial k) (LaurentPolynomial k) := by
    exact RingHom.ext (fun x => (LaurentPolynomial.algebraMap_eq_toLaurent x).symm)
  change Set.range (PrimeSpectrum.comap (Polynomial.toLaurent : Polynomial k →+* LaurentPolynomial k)) = _
  rw [h]
  exact PrimeSpectrum.localization_away_comap_range (LaurentPolynomial k) Polynomial.X

private theorem puncturedLineRange_complement (k : Type u) [Field k] :
    Set.range (puncturedLineInclusion k).left = (Set.range (affineLineZero k).left)ᶜ := by
  rw [puncturedLineRange]
  change (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) : Set (PrimeSpectrum (Polynomial k))) =
    (Set.range (PrimeSpectrum.comap (Polynomial.evalRingHom (0 : k))))ᶜ
  have hker : RingHom.ker (Polynomial.evalRingHom (0 : k)) = Ideal.span {Polynomial.X} := by
    rw [Polynomial.ker_evalRingHom, map_zero, sub_zero]
  rw [range_comap_of_surjective _ _ (fun x => ⟨Polynomial.C x, Polynomial.eval_C⟩), hker]
  ext p
  change (Polynomial.X : Polynomial k) ∉ p.asIdeal ↔ ¬ Ideal.span {Polynomial.X} ≤ p.asIdeal
  rw [Ideal.span_singleton_le_iff_mem]

private def projectiveLineChart (k : Type u) [Field k] (i : Index.{u}) :
    affineLine k ⟶ projectiveLine k :=
  affinePoint (CommAlgCat.of k (Polynomial k)) i Polynomial.X

private theorem projectiveLineChart_coordinates {R : TestAlgebra k}
    (i : Index.{u}) (a : CommAlgCat.of k (Polynomial k) ⟶ R) :
    (testSpec k).map a.op ≫ projectiveLineChart k i = affinePoint R i (a.hom Polynomial.X) :=
  affinePoint_change a i Polynomial.X

private theorem polynomial_projective_charts (k : Type u) [Field k] :
    ∃ (e : coordinateProjectiveSpace k Index.{u} ≅ projectiveLine k)
      (b : ∀ i : Index.{u}, chartRing k Index.{u} i ≃ₐ[k] Polynomial k),
      (∀ (i j : Index.{u}), b i (coordinateRatio k Index.{u} i j) =
        if j = i then 1 else Polynomial.X) ∧
      (∀ i, projectiveLineChart k i =
        (testSpec k).map (CommAlgCat.ofHom (b i).toAlgHom).op ≫ chartMorphism i ≫ e.hom) := by
  have claim (i : Index.{u}) :
      ∃ b : chartRing k Index.{u} i ≃ₐ[k] Polynomial k,
        ∀ j : Index.{u}, b (coordinateRatio k Index.{u} i j) =
          if j = i then 1 else Polynomial.X := by
    obtain ⟨d, hC, hX⟩ := _root_.LinearAlgebraicGroups.ProjectiveSpaces.polynomialChartCoordinates k Index.{u} i
    let d' : MvPolynomial {j : Index.{u} // j ≠ i} k ≃ₐ[k] chartRing k Index.{u} i :=
      { d with commutes' := hC }
    letI : Unique {j : Index.{u} // j ≠ i} := ⟨⟨⟨otherIndex i, otherIndex_ne i⟩⟩,
      fun j => Subtype.ext (eq_otherIndex j.property)⟩
    let p := MvPolynomial.uniqueAlgEquiv k {j : Index.{u} // j ≠ i}
    refine ⟨d'.symm.trans p, fun j => ?_⟩
    by_cases h : j = i
    · subst j
      rw [ratio_self, map_one, ite_eq_left rfl]
    · have hr : d' (MvPolynomial.X ⟨j, h⟩) = coordinateRatio k Index.{u} i j := hX _
      rw [ite_eq_right h, ← hr, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
      exact MvPolynomial.aeval_X _ _
  choose b hb using claim
  obtain ⟨e, he⟩ := _root_.LinearAlgebraicGroups.ProjectiveSpaces.basisPointFormula k (plane k)
    Index.{u} (planeBasis k)
  refine ⟨e, b, hb, fun i => ?_⟩
  apply planeLine_ext
  rw [projectiveLineChart, affinePoint_coordinates]
  change _ = (((_root_.LinearAlgebraicGroups.ProjectiveSpaces.lineRepresentation k (plane k)).points _
        ((testSpec k).map (CommAlgCat.ofHom (b i).toAlgHom).op ≫ chartMorphism i ≫ e.hom)).line _ (𝟙 _)).submodule
  rw [he]
  have hfun : affineCoordinates i (R := CommAlgCat.of k (Polynomial k)) Polynomial.X =
      fun j => (b i) (coordinateRatio k Index.{u} i j) := funext (fun j => (hb i j).symm)
  rw [vectorOfCoordinates, hfun]
  rfl

private theorem projectiveLineCharts_cover (i : Index.{u}) :
    (∀ j, IsOpenImmersion (projectiveLineChart k j).left) ∧
    (∀ x : (projectiveLine k).left, x ∈ Set.range (projectiveLineChart k i).left ∨
      x ∈ Set.range (projectiveLineChart k (otherIndex i)).left) ∧
    IsPullback (puncturedLineInclusion k).left (inverseParameter k).left
      (projectiveLineChart k i).left (projectiveLineChart k (otherIndex i)).left := by
  obtain ⟨e, b, hb, h⟩ := polynomial_projective_charts k
  haveI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  let B (j : Index.{u}) : affineLine k ≅ chartScheme (k := k) j :=
    (testSpec k).mapIso ((CommAlgCat.isoEquivAlgEquiv).symm (b j)).op
  have hf (j : Index.{u}) : (projectiveLineChart k j).left =
      (B j).hom.left ≫ chartInclusion k Index.{u} j ≫ e.hom.left := by
    rw [h, Over.comp_left, Over.comp_left]
    rfl
  have hr (j : Index.{u}) : Set.range (projectiveLineChart k j).left =
      e.hom.left '' ((coordinateOpen k Index.{u} j : (Proj (grading k Index.{u})).Opens) : Set (Proj (grading k Index.{u}))) := by
    haveI : IsIso (B j).hom.left := (Over.forget _).map_isIso (B j).hom
    have hrange := (_root_.LinearAlgebraicGroups.ProjectiveSpaces.coordinateAffineCharts k Index.{u} j).2
    rw [hf]
    change Set.range (e.hom.left ∘ chartInclusion k Index.{u} j ∘ (B j).hom.left) = _
    rw [Set.range_comp, (B j).hom.left.surjective.range_comp, hrange]
  have hopen (j : Index.{u}) : IsOpenImmersion (projectiveLineChart k j).left := by
    haveI : IsIso (B j).hom.left := (Over.forget _).map_isIso (B j).hom
    haveI : IsOpenImmersion (chartInclusion k Index.{u} j) :=
      (_root_.LinearAlgebraicGroups.ProjectiveSpaces.coordinateAffineCharts k Index.{u} j).1
    rw [hf]
    infer_instance
  refine ⟨hopen, ?_, ?_⟩
  · intro x
    obtain ⟨y, rfl⟩ := e.hom.left.surjective x
    have hy : y ∈ ⨆ j, coordinateOpen k Index.{u} j := by
      rw [_root_.LinearAlgebraicGroups.ProjectiveSpaces.coordinateOpenCover k Index.{u}]
      trivial
    rw [TopologicalSpace.Opens.mem_iSup] at hy
    obtain ⟨j, hj⟩ := hy
    by_cases hji : j = i
    · subst j
      exact Or.inl (by rw [hr]; exact ⟨y, hj, rfl⟩)
    · rw [eq_otherIndex hji] at hj
      exact Or.inr (by rw [hr]; exact ⟨y, hj, rfl⟩)
  · haveI := puncturedLineOpen k
    haveI := hopen (otherIndex i)
    apply open_chart_overlap
    · rw [← Over.comp_left, ← Over.comp_left]
      apply congrArg Over.Hom.left
      rw [puncturedLineInclusion, inverseParameter, projectiveLineChart_coordinates, projectiveLineChart_coordinates]
      apply (affinePoint_overlap _ _ _).mpr
      change Polynomial.toLaurent Polynomial.X * LaurentPolynomial.invert (Polynomial.toLaurent Polynomial.X) = 1
      rw [Polynomial.toLaurent_X, LaurentPolynomial.invert_T, ← LaurentPolynomial.T_add,
        add_neg_cancel, LaurentPolynomial.T_zero]
    · rw [puncturedLineRange, hf, hr]
      ext p
      change p ∈ (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k)) ↔
        e.hom.left (chartInclusion k Index.{u} i ((B i).hom.left p)) ∈ e.hom.left '' _
      simp only [Set.mem_image]
      constructor
      · intro hp
        refine ⟨_, ?_, rfl⟩
        change (B i).hom.left p ∈ (chartInclusion k Index.{u} i) ⁻¹ᵁ coordinateOpen k Index.{u} (otherIndex i)
        rw [_root_.LinearAlgebraicGroups.ProjectiveSpaces.coordinateOverlap k Index.{u} i (otherIndex i)]
        change (b i) (coordinateRatio k Index.{u} i (otherIndex i)) ∉ p.asIdeal
        rwa [hb, ite_eq_right (otherIndex_ne i)]
      · rintro ⟨y, hy, heq⟩
        replace hy := (e.hom.left.injective heq) ▸ hy
        change (B i).hom.left p ∈ (chartInclusion k Index.{u} i) ⁻¹ᵁ coordinateOpen k Index.{u} (otherIndex i) at hy
        rw [_root_.LinearAlgebraicGroups.ProjectiveSpaces.coordinateOverlap k Index.{u} i (otherIndex i)] at hy
        change (b i) (coordinateRatio k Index.{u} i (otherIndex i)) ∉ p.asIdeal at hy
        rwa [hb, ite_eq_right (otherIndex_ne i)] at hy

end ProjectiveLineCharts

section MarkedLineCompletion

open Specs.RankOneFlag (Index plane planeBasis projectiveLine HasCoordinates)

set_option maxHeartbeats 1300000

variable {k : Type u} [Field k]

private def affineCoordinateChange (e : Polynomial k ≃ₐ[k] Polynomial k) :
    affineLine k ≅ affineLine k :=
  (testSpec k).mapIso ((CommAlgCat.isoEquivAlgEquiv).symm e).op

private theorem affineCoordinateChange_eval (e : Polynomial k ≃ₐ[k] Polynomial k) (b : k) :
    (testSpec k).map (CommAlgCat.ofHom (Polynomial.aeval b)).op ≫
      (affineCoordinateChange e).hom =
        (testSpec k).map (CommAlgCat.ofHom (Polynomial.aeval ((e Polynomial.X).eval b))).op := by
  change (testSpec k).map _ ≫ (testSpec k).map _ = _
  rw [← Functor.map_comp]
  have h : (Polynomial.aeval b : Polynomial k →ₐ[k] k).comp e.toAlgHom =
      Polynomial.aeval ((e Polynomial.X).eval b) := by
    apply Polynomial.algHom_ext
    rw [AlgHom.comp_apply, Polynomial.aeval_X]
    rfl
  exact congrArg (fun v : Polynomial k →ₐ[k] k =>
    (testSpec k).map (CommAlgCat.ofHom v).op) h

private theorem recenter_affine_chart {X : SchemeOver k} (v : affineLine k ⟶ X)
    [IsOpenImmersion v.left] (y : Points X (CommAlgCat.of k k))
    (hy : Set.range y.left ⊆ Set.range v.left) :
    ∃ e : affineLine k ≅ affineLine k, affineLineZero k ≫ e.hom ≫ v = y := by
  let q := IsOpenImmersion.lift v.left y.left hy
  have hq : q ≫ v.left = y.left := IsOpenImmersion.lift_fac _ _ _
  let p : Points (affineLine k) (CommAlgCat.of k k) := Over.homMk q (by
    rw [← Over.w v, ← Category.assoc, hq, Over.w])
  have hp : p ≫ v = y := Over.OverMorphism.ext hq
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let r : Polynomial k →ₐ[k] k := (F.preimage p).unop.hom
  have hr : (testSpec k).map (CommAlgCat.ofHom r).op = p := F.map_preimage p
  let e := Polynomial.algEquivAevalXAddC (r Polynomial.X)
  refine ⟨affineCoordinateChange e, ?_⟩
  rw [← Category.assoc, affineLineZero, affineCoordinateChange_eval, ← hp, ← hr]
  congr 3
  apply CommAlgCat.hom_ext
  apply Polynomial.algHom_ext
  change Polynomial.aeval ((e Polynomial.X).eval 0) Polynomial.X = r Polynomial.X
  rw [Polynomial.aeval_X]
  simp [e, Polynomial.algEquivAevalXAddC]

private theorem punctured_chart_range {X : SchemeOver k} (f : affineLine k ⟶ X)
    [IsOpenImmersion f.left] (x : Points X (CommAlgCat.of k k))
    (hx : affineLineZero k ≫ f = x) :
    Set.range (puncturedLineInclusion k ≫ f).left = Set.range f.left \ Set.range x.left := by
  rw [Over.comp_left]
  change Set.range (f.left ∘ (puncturedLineInclusion k).left) = _
  rw [Set.range_comp, puncturedLineRange_complement, ← hx, Over.comp_left]
  change f.left '' (Set.range (affineLineZero k).left)ᶜ =
    Set.range f.left \ Set.range (f.left ∘ (affineLineZero k).left)
  rw [Set.range_comp, Set.image_compl_eq_range_sdiff_image f.left.isOpenEmbedding.injective]

private theorem punctured_chart_preimage {X : SchemeOver k} (f : affineLine k ⟶ X)
    [IsOpenImmersion f.left] (x : Points X (CommAlgCat.of k k))
    (hx : affineLineZero k ≫ f = x) :
    f.left ⁻¹' (Set.range x.left)ᶜ = Set.range (puncturedLineInclusion k).left := by
  rw [puncturedLineRange_complement, ← hx, Over.comp_left]
  change f.left ⁻¹' (Set.range (f.left ∘ (affineLineZero k).left))ᶜ = _
  rw [Set.range_comp, Set.preimage_compl, Set.preimage_image_eq _ f.left.isOpenEmbedding.injective]

private theorem iso_of_two_affine_line_charts {X : SchemeOver k} [IsSeparated X.hom]
    (f g : affineLine k ⟶ X) [IsOpenImmersion f.left] [IsOpenImmersion g.left]
    (x y : Points X (CommAlgCat.of k k)) (hne : x ≠ y)
    (hx : affineLineZero k ≫ f = x) (hy : affineLineZero k ≫ g = y)
    (hf : Set.range f.left = (Set.range y.left)ᶜ) (hg : Set.range g.left = (Set.range x.left)ᶜ)
    (hcover : ∀ t : X.left, t ∈ Set.range f.left ∨ t ∈ Set.range g.left)
    (i : Index.{u}) :
    ∃ e : X ≅ projectiveLine k,
      x ≫ e.hom = affinePoint (CommAlgCat.of k k) i 0 ∧
      y ≫ e.hom = affinePoint (CommAlgCat.of k k) (otherIndex i) 0 := by
  let l := puncturedLineInclusion k
  let m := inverseParameter k
  let L := puncturedLine k
  haveI : IsOpenImmersion l.left := puncturedLineOpen k
  letI : IsOpenImmersion (l ≫ f).left := inferInstanceAs (IsOpenImmersion (l.left ≫ f.left))
  letI : IsOpenImmersion (l ≫ g).left := inferInstanceAs (IsOpenImmersion (l.left ≫ g.left))
  have hrg : Set.range (l ≫ f).left = Set.range (l ≫ g).left := by
    rw [punctured_chart_range f x hx, punctured_chart_range g y hy, hf, hg]
    ext p
    exact and_comm
  let u₀ := IsOpenImmersion.isoOfRangeEq (l ≫ f).left (l ≫ g).left hrg
  have hu₀ : u₀.hom ≫ (l ≫ g).left = (l ≫ f).left :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let u : L ≅ L := Over.isoMk u₀ (by
    calc
      u₀.hom ≫ L.hom = (u₀.hom ≫ (l ≫ g).left) ≫ X.hom := by rw [Category.assoc, Over.w]
      _ = L.hom := by rw [hu₀, Over.w])
  have hu : u.hom ≫ l ≫ g = l ≫ f := Over.OverMorphism.ext hu₀
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let E : LaurentPolynomial k ≃ₐ[k] LaurentPolynomial k :=
    CommAlgCat.isoEquivAlgEquiv (F.preimageIso u).unop
  have hE : (testSpec k).map (CommAlgCat.ofHom E.toAlgHom).op = u.hom :=
    F.map_preimage u.hom
  obtain ⟨a, ha⟩ := laurent_automorphism_parameter E
  letI := a.invertible
  let e := Polynomial.algEquivCMulXAddC (a : k) 0
  let s := affineCoordinateChange e
  have he : e Polynomial.X = Polynomial.C (a : k) * Polynomial.X := by
    simp only [e, Polynomial.algEquivCMulXAddC_apply, Polynomial.aeval_X, map_zero, add_zero]
  have hs : affineLineZero k ≫ s.hom = affineLineZero k := by
    rw [affineLineZero, affineCoordinateChange_eval, he]
    simp
  rcases ha with ha | ha
  · have hpar : E.toAlgHom.comp Polynomial.toLaurentAlg = Polynomial.toLaurentAlg.comp e.toAlgHom := by
      apply Polynomial.algHom_ext
      change E (Polynomial.toLaurent Polynomial.X) = Polynomial.toLaurent (e Polynomial.X)
      rw [he, map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X, ha]
    have hl : u.hom ≫ l = l ≫ s.hom := by
      rw [← hE]
      change (testSpec k).map _ ≫ (testSpec k).map _ = (testSpec k).map _ ≫ (testSpec k).map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (fun v : Polynomial k →ₐ[k] LaurentPolynomial k =>
        (testSpec k).map (CommAlgCat.ofHom v).op) hpar
    have hd : IsDominant l.left := by
      rw [isDominant_iff, DenseRange, puncturedLineRange]
      have h : ((PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k)) :
          Set (PrimeSpectrum (Polynomial k))).Nonempty :=
        ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.mem_basicOpen _ _ |>.mpr (by simp)⟩
      exact (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k)).isOpen.dense h
    letI := hd
    letI : IsReduced (affineLine k).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of (Polynomial k))))
    have hfg : f = s.hom ≫ g := by
      apply Over.OverMorphism.ext
      apply ext_of_isDominant_of_isSeparated X.hom ((Over.w f).trans (Over.w (s.hom ≫ g)).symm) l.left
      rw [← Over.comp_left, ← Over.comp_left, ← hu, ← Category.assoc, hl, Category.assoc]
    exact (hne (by rw [← hx, ← hy, hfg, ← Category.assoc, hs])).elim
  · have hpar : E.toAlgHom.comp Polynomial.toLaurentAlg =
        ((invertLaurent k).toAlgHom.comp Polynomial.toLaurentAlg).comp e.toAlgHom := by
      apply Polynomial.algHom_ext
      change E (Polynomial.toLaurent Polynomial.X) =
        LaurentPolynomial.invert (Polynomial.toLaurent (e Polynomial.X))
      rw [he, map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X,
        map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T, ha]
    have hm : u.hom ≫ l = m ≫ s.hom := by
      rw [← hE]
      change (testSpec k).map _ ≫ (testSpec k).map _ = (testSpec k).map _ ≫ (testSpec k).map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (fun v : Polynomial k →ₐ[k] LaurentPolynomial k =>
        (testSpec k).map (CommAlgCat.ofHom v).op) hpar
    let g' := s.hom ≫ g
    haveI : IsIso s.hom.left := (Over.forget _).map_isIso s.hom
    haveI : IsOpenImmersion g'.left := inferInstanceAs (IsOpenImmersion (s.hom.left ≫ g.left))
    have hg' : Set.range g'.left = Set.range g.left := s.hom.left.surjective.range_comp _
    have hcover' (z : X.left) : z ∈ Set.range f.left ∨ z ∈ Set.range g'.left := by
      rw [hg']
      exact hcover z
    have hcomp : l ≫ f = m ≫ g' := by rw [← hu, ← Category.assoc, hm, Category.assoc]
    have hX : IsPullback l.left m.left f.left g'.left := open_chart_overlap
      (congrArg Over.Hom.left hcomp) (by rw [hg', hg, punctured_chart_preimage f x hx])
    obtain ⟨hopen, hPcover, hP⟩ := projectiveLineCharts_cover (k := k) i
    haveI := hopen i
    haveI := hopen (otherIndex i)
    let p := projectiveLineChart k i
    let q := projectiveLineChart k (otherIndex i)
    obtain ⟨w, hw₀, hw₁⟩ := iso_of_common_chart_overlap f.left g'.left p.left q.left
      hcover' hPcover l.left m.left hX hP
    have hw : w.hom ≫ (projectiveLine k).hom = X.hom := by
      let C := openCoverPair f.left g'.left hcover'
      apply C.hom_ext
      intro b
      cases b
      · change f.left ≫ _ = f.left ≫ _
        rw [← Category.assoc, hw₀, Over.w p, Over.w f]
      · change g'.left ≫ _ = g'.left ≫ _
        rw [← Category.assoc, hw₁, Over.w q, Over.w g']
    let w' : X ≅ projectiveLine k := Over.isoMk w hw
    have hw₀' : f ≫ w'.hom = p := Over.OverMorphism.ext hw₀
    have hw₁' : g' ≫ w'.hom = q := Over.OverMorphism.ext hw₁
    have hy' : affineLineZero k ≫ g' = y := by
      rw [← Category.assoc, hs, hy]
    refine ⟨w', ?_, ?_⟩
    · rw [← hx, Category.assoc, hw₀', affineLineZero, projectiveLineChart_coordinates]
      exact congrArg (affinePoint _ i) (Polynomial.aeval_X (0 : k))
    · rw [← hy', Category.assoc, hw₁', affineLineZero, projectiveLineChart_coordinates]
      exact congrArg (affinePoint _ (otherIndex i)) (Polynomial.aeval_X (0 : k))

end MarkedLineCompletion

section OpenCellRange

open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricRadicals (GeometricGroup IsMaximalTorus)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.QuotientEmbedding (Presentation)
open CocharacterDynamics (LimitDecomposition)
open private quotientAction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
open private gm_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private torus_smooth_connected_solvable subgroupOf_trans
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private translateAction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
open private baseChangeMapIsPullback from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient

set_option maxHeartbeats 3000000

variable {k : Type u} [Field k]

private theorem range_section {X : SchemeOver k} (x : 𝟙_ (SchemeOver k) ⟶ X) :
    Set.range x.left = {sectionSupport x} := by
  letI : Subsingleton (𝟙_ (SchemeOver k)).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  ext t
  constructor
  · rintro ⟨p, rfl⟩
    exact Set.mem_singleton_iff.mpr (congrArg x.left (Subsingleton.elim _ _))
  · intro h
    exact ⟨IsLocalRing.closedPoint k, (Set.mem_singleton_iff.mp h).symm⟩

private theorem baseChange_quotient_action {K : Type u} [Field K] [Algebra k K]
    {H : AffineAlgebraicGroup k} {B : ClosedSubgroup H.val} (Q : Presentation B) :
    (quotientAction (baseChangeQuotientPresentation K (G := H) Q)).smul =
      baseChangeAction K (quotientAction Q).smul := by
  let P := baseChangeQuotientPresentation K (G := H) Q
  let H' := Specs.Unipotent.baseChangedAlgebraicGroup K H
  letI := tensor_left_epi_of_flat_surjective (X := H'.val.X) P.flat P.surjective
  apply (cancel_epi (H'.val.X ◁ P.projection)).mp
  have hb : (H'.val.X ◁ P.projection) ≫ (quotientAction P).smul = μ[H'.val.X] ≫ P.projection := by
    simpa only [tensorHom_def, MonoidalCategory.id_whiskerRight, Category.id_comp]
      using quotient_action_equivariant (H := H') P
  have ha : (H.val.X ◁ Q.projection) ≫ (quotientAction Q).smul = μ[H.val.X] ≫ Q.projection := by
    simpa only [tensorHom_def, MonoidalCategory.id_whiskerRight, Category.id_comp]
      using quotient_action_equivariant (H := H) Q
  exact hb.trans (quotient_smul_baseChange_support K Q.projection _ ha).symm

private theorem translate_identity_coset {G : GroupScheme k} {B : ClosedSubgroup G}
    (Q : Presentation B) (a : ModObj G.X Q.scheme)
    (ha : (𝟙 G.X ⊗ₘ Q.projection) ≫ a.smul = μ[G.X] ≫ Q.projection)
    (n : 𝟙_ (SchemeOver k) ⟶ G.X) :
    (η[G.X] ≫ Q.projection) ≫ (translateAction a n).hom = n ≫ Q.projection := by
  rw [translateAction_on_section, quotient_action_formula Q a ha n η[G.X]]
  have e : η[G.X] = (1 : 𝟙_ (SchemeOver k) ⟶ G.X) := by
    rw [CategoryTheory.Hom.one_def, show toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ from
      Subsingleton.elim _ _, Category.id_comp]
  rw [e, mul_one]

private theorem geometric_contracting_cell_range [IsAlgClosed k]
    {H : AffineAlgebraicGroup k} {T B : ClosedSubgroup H.val}
    (hT : IsMaximalTorus T) {c : Cocharacter H.val}
    (E : LimitDecomposition c) (hTC : IsSubgroupOf T E.centralizer) (hTB : IsSubgroupOf T B)
    (Q : Presentation B) [IsProper Q.scheme.hom]
    (n : 𝟙_ (SchemeOver k) ⟶ H.val.X) (hn : Normalizes T.inclusion n)
    (hfix : ∀ z : 𝟙_ (SchemeOver k) ⟶ Q.scheme,
      IsFixedBy ((T.inclusion.hom.hom ▷ Q.scheme) ≫ (quotientAction Q).smul) z →
        z = η[H.val.X] ≫ Q.projection ∨ z = n ≫ Q.projection)
    (hj : IsOpenImmersion (E.contracting.inclusion.hom.hom ≫ Q.projection).left)
    (hy : sectionSupport (n ≫ Q.projection) ∉ Set.range (E.contracting.inclusion.hom.hom ≫ Q.projection).left) :
    Set.range (E.contracting.inclusion.hom.hom ≫ Q.projection).left =
      (Set.range (n ≫ Q.projection).left)ᶜ := by
  let a := quotientAction Q
  let j := E.contracting.inclusion.hom.hom ≫ Q.projection
  let x := η[H.val.X] ≫ Q.projection
  let y := n ≫ Q.projection
  have hx : sectionSupport x ∈ Set.range j.left := by
    refine ⟨sectionSupport (η[E.contracting.group.X]), ?_⟩
    exact congrArg (fun p : 𝟙_ (SchemeOver k) ⟶ Q.scheme => sectionSupport p)
      (quotient_cell_identity E.contracting Q)
  obtain ⟨hs, hc, hsol⟩ := torus_smooth_connected_solvable (closedSubgroupAlgebraicGroup (G := H) T) hT.1
  have ha := quotient_action_equivariant (H := H) Q
  have htrans : x ≫ (translateAction a n).hom = y := translate_identity_coset Q a ha n
  have hU : IsAffine E.contracting.group.X.left := (closedSubgroupAlgebraicGroup (G := H) E.contracting).property.1
  letI : IsOpenImmersion j.left := hj
  have hr := opposite_cell_range_from_fixed_points (H := H) T hs hc hsol a x j hU hx n hn
    (htrans.symm ▸ hy) (fun z h => (hfix z h).imp id (fun ep => ep.trans htrans.symm))
    (translates_preserve_contracting_cell (H := H) E hTC hTB Q a ha)
  simpa only [htrans, ← range_section y] using hr

private theorem range_scalarExtendedRationalPoint {K : Type u} [Field K] [Algebra k K]
    {X : SchemeOver k} (x : 𝟙_ (SchemeOver k) ⟶ X) :
    Set.range (scalarExtendedRationalPoint K x).left = Set.range ((baseChange k K).map x).left := by
  let F := baseChange k K
  letI : IsIso (Functor.LaxMonoidal.ε F).left := (Over.forget _).map_isIso (Functor.LaxMonoidal.ε F)
  exact (Functor.LaxMonoidal.ε F).left.surjective.range_comp _

private theorem range_complement_of_baseChange {K : Type u} [Field K] [Algebra k K]
    {X U : SchemeOver k} (j : U ⟶ X) (y : 𝟙_ (SchemeOver k) ⟶ X)
    (h : Set.range ((baseChange k K).map j).left =
      (Set.range ((baseChange k K).map y).left)ᶜ) :
    Set.range j.left = (Set.range y.left)ᶜ := by
  rw [range_baseChange_preimage K, range_baseChange_preimage K, ← Set.preimage_compl] at h
  exact (baseChange_projection_surjective K X).preimage_injective h

private theorem baseChange_quotient_torus_action {K : Type u} [Field K] [Algebra k K]
    {H : AffineAlgebraicGroup k} {T B : ClosedSubgroup H.val} (Q : Presentation B) :
    let P := baseChangeQuotientPresentation K (G := H) Q
    (((extendSubgroup K T).inclusion.hom.hom ▷ P.scheme) ≫ (quotientAction P).smul) =
      baseChangeAction K ((T.inclusion.hom.hom ▷ Q.scheme) ≫ (quotientAction Q).smul) := by
  intro P
  calc
    _ = ((extendSubgroup K T).inclusion.hom.hom ▷ P.scheme) ≫ baseChangeAction K (quotientAction Q).smul :=
      congrArg (fun m => ((extendSubgroup K T).inclusion.hom.hom ▷ P.scheme) ≫ m)
        (baseChange_quotient_action (K := K) (H := H) Q)
    _ = _ := (baseChange_smul_restriction K T.inclusion.hom.hom (quotientAction Q).smul).symm

private theorem contracting_quotient_cell_range_aux
    {K : Type u} [Field K] [Algebra k K] [IsAlgClosed K]
    {H : AffineAlgebraicGroup k} {T B : ClosedSubgroup H.val}
    (hT : IsMaximalTorus (extendSubgroup K T)) {c : Cocharacter H.val}
    (E : LimitDecomposition c) (hTC : IsSubgroupOf T E.centralizer) (hTB : IsSubgroupOf T B)
    (Q : Presentation B) (hproper : IsProper Q.scheme.hom)
    (n : 𝟙_ (SchemeOver k) ⟶ H.val.X)
    (hn : Normalizes (extendSubgroup K T).inclusion
      (scalarExtendedRationalPoint K n))
    (hfix :
      let P := baseChangeQuotientPresentation K (G := H) Q
      ∀ x : 𝟙_ (SchemeOver K) ⟶ P.scheme,
        IsFixedBy (baseChangeAction K ((T.inclusion.hom.hom ▷ Q.scheme) ≫ (quotientAction Q).smul)) x ↔
        x = scalarExtendedRationalPoint K (η[H.val.X] ≫ Q.projection) ∨
          x = scalarExtendedRationalPoint K (n ≫ Q.projection))
    (hj : IsOpenImmersion (E.contracting.inclusion.hom.hom ≫ Q.projection).left)
    (hdisj : Disjoint (Set.range (E.contracting.inclusion.hom.hom ≫ Q.projection).left)
      (Set.range (n ≫ Q.projection).left)) :
    Set.range (E.contracting.inclusion.hom.hom ≫ Q.projection).left =
      (Set.range (n ≫ Q.projection).left)ᶜ := by
  let F := baseChange k K
  let H' := Specs.Unipotent.baseChangedAlgebraicGroup K H
  let T' := extendSubgroup K T
  let P := baseChangeQuotientPresentation K (G := H) Q
  let a := quotientAction P
  let n' := scalarExtendedRationalPoint K n
  let j := E.contracting.inclusion.hom.hom ≫ Q.projection
  let x := η[H'.val.X] ≫ P.projection
  let y := n' ≫ P.projection
  haveI : IsProper P.scheme.hom := MorphismProperty.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback Q.scheme.hom (fieldSpecMap k K)) hproper
  obtain ⟨m, hm⟩ := gm_baseChange k K
  let d := m.hom ≫ (groupBaseChange k K).map c
  obtain ⟨E'⟩ := CocharacterDynamics.existsLimitDecomposition H' d
  obtain ⟨_, hU, hZ⟩ := limits_subgroups_extend H E m hm E'
  have hTC' : IsSubgroupOf T' E'.centralizer := subgroupOf_trans (extend_subgroupOf hTC) hZ.2
  have hTB' : IsSubgroupOf T' (extendSubgroup K B) := extend_subgroupOf hTB
  obtain ⟨u, hu⟩ := subgroupIso_of_same hU
  let i := (Grp.forget (SchemeOver K)).mapIso u
  let j' := E'.contracting.inclusion.hom.hom ≫ P.projection
  have hj' : j' = i.hom ≫ F.map j := by
    have h := (Grp.forget (SchemeOver K)).congr_map hu
    change i.hom ≫ F.map E.contracting.inclusion.hom.hom = E'.contracting.inclusion.hom.hom at h
    change E'.contracting.inclusion.hom.hom ≫ F.map Q.projection = _
    rw [← h, Category.assoc, ← Functor.map_comp]
  haveI : IsIso i.hom.left := (Over.forget _).map_isIso i.hom
  haveI : IsOpenImmersion (F.map j).left := MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (baseChangeMapIsPullback K j).flip hj
  haveI : IsOpenImmersion j'.left := by rw [hj', Over.comp_left]; infer_instance
  have hRange : Set.range j'.left = Set.range (F.map j).left := by
    rw [hj', Over.comp_left]
    exact i.hom.left.surjective.range_comp _
  have hOne : scalarExtendedRationalPoint K (η[H.val.X]) = η[H'.val.X] := rfl
  have hx' : scalarExtendedRationalPoint K (η[H.val.X] ≫ Q.projection) = x := by
    rw [scalarExtendedPoint_natural, hOne]
    rfl
  have hy' : scalarExtendedRationalPoint K (n ≫ Q.projection) = y :=
    scalarExtendedPoint_natural K n Q.projection
  have hRy : Set.range y.left = Set.range (F.map (n ≫ Q.projection)).left :=
    (congrArg (fun p : 𝟙_ (SchemeOver K) ⟶ P.scheme => Set.range p.left) hy'.symm).trans
      (range_scalarExtendedRationalPoint (K := K) (n ≫ Q.projection))
  have hy : sectionSupport y ∉ Set.range j'.left := by
    rw [hRange, range_baseChange_preimage K]
    intro hy
    have hi : sectionSupport y ∈ Set.range y.left := Set.mem_range_self _
    rw [hRy, range_baseChange_preimage K] at hi
    exact Set.disjoint_left.mp hdisj hy hi
  have hfix' (z : 𝟙_ (SchemeOver K) ⟶ P.scheme) :
      IsFixedBy ((T'.inclusion.hom.hom ▷ P.scheme) ≫ a.smul) z → z = x ∨ z = y := by
    rw [baseChange_quotient_torus_action (K := K) (H := H) (T := T) Q]
    exact fun h => ((hfix z).mp h).imp (fun eq => eq.trans hx') (fun eq => eq.trans hy')
  have hr : Set.range j'.left = (Set.range y.left)ᶜ :=
    geometric_contracting_cell_range (H := H') hT E' hTC' hTB' P n' hn hfix' ‹_› hy
  exact range_complement_of_baseChange (K := K) j (n ≫ Q.projection)
    (hRange.symm.trans (hr.trans (congrArg Set.compl hRy)))

private theorem contracting_quotient_cell_range
    {H : AffineAlgebraicGroup k} {T B : ClosedSubgroup H.val}
    (hT : Specs.RankOneFlag.IsGeometricallyMaximal T) {c : Cocharacter H.val}
    (E : LimitDecomposition c) (hTC : IsSubgroupOf T E.centralizer) (hTB : IsSubgroupOf T B)
    (Q : Presentation B) (hproper : IsProper Q.scheme.hom)
    (n : 𝟙_ (SchemeOver k) ⟶ H.val.X)
    (hn : Normalizes (extendSubgroup (AlgebraicClosure k) T).inclusion
      (scalarExtendedRationalPoint (AlgebraicClosure k) n))
    (hfix :
      let K := AlgebraicClosure k
      let P := baseChangeQuotientPresentation K (G := H) Q
      ∀ x : 𝟙_ (SchemeOver K) ⟶ P.scheme,
        IsFixedBy (baseChangeAction K ((T.inclusion.hom.hom ▷ Q.scheme) ≫ (quotientAction Q).smul)) x ↔
        x = scalarExtendedRationalPoint K (η[H.val.X] ≫ Q.projection) ∨
          x = scalarExtendedRationalPoint K (n ≫ Q.projection))
    (hj : IsOpenImmersion (E.contracting.inclusion.hom.hom ≫ Q.projection).left)
    (hdisj : Disjoint (Set.range (E.contracting.inclusion.hom.hom ≫ Q.projection).left)
      (Set.range (n ≫ Q.projection).left)) :
    Set.range (E.contracting.inclusion.hom.hom ≫ Q.projection).left =
      (Set.range (n ≫ Q.projection).left)ᶜ := by
  exact contracting_quotient_cell_range_aux (K := AlgebraicClosure k) (H := H)
    hT.choose_spec E hTC hTB Q hproper n hn hfix hj hdisj

end OpenCellRange

section FlagQuotientCharts

open CharacterDescent (Cocharacter)
open Specs.GeometricRadicals (GeometricGroup IsReductive)
open Specs.GeometricBorelConjugacy (ConjugatesSubgroups IsKBorel)
open Specs.RankOneFlag (AreTwoBorels SameSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.QuotientEmbedding (Presentation)
open CocharacterDynamics (LimitDecomposition oppositeCocharacter)
open private quotientAction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
open private translateAction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
open private group_geometricallyIrreducible from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterOpenCell
open Order

set_option maxHeartbeats 1600000

variable {k : Type u} [Field k]

private theorem rank_one_borel_quotient_proper {H : AffineAlgebraicGroup k}
    (hH : IsReductive H) {B : ClosedSubgroup H.val} (hB : IsKBorel B)
    (hs : Smooth B.group.X.hom) (Q : Presentation B) : IsProper Q.scheme.hom := by
  letI : GeometricallyConnected H.val.X.hom := hH.2.1
  have hc := GeometricallyConnected.connectedSpace_of_subsingleton H.val.X.hom
  obtain ⟨i, hi⟩ := hB
  exact (BorelProper.quotientProperIff H hH.1 hc B hs Q).mpr
    ⟨i, _, hi, 𝟙 _, Category.id_comp _⟩

private theorem quotient_irreducible {H : AffineAlgebraicGroup k} (hH : IsReductive H)
    {B : ClosedSubgroup H.val} (Q : Presentation B) : IrreducibleSpace Q.scheme.left := by
  letI : Smooth H.val.X.hom := hH.1
  letI : GeometricallyConnected H.val.X.hom := hH.2.1
  letI : ConnectedSpace H.val.X.left := GeometricallyConnected.connectedSpace_of_subsingleton H.val.X.hom
  letI : GeometricallyIrreducible H.val.X.hom := group_geometricallyIrreducible H
  letI : IrreducibleSpace H.val.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton H.val.X.hom
  exact Function.Surjective.irreducibleSpace Q.projection.left.continuous Q.surjective.1

private theorem open_complements_of_distinct_points {X : SchemeOver k}
    {x y : 𝟙_ (SchemeOver k) ⟶ X} (hne : sectionSupport x ≠ sectionSupport y)
    {A B : SchemeOver k} {j : A ⟶ X} {v : B ⟶ X}
    (hj : Set.range j.left = (Set.range y.left)ᶜ)
    (hv : Set.range v.left = (Set.range x.left)ᶜ) :
    ∀ z : X.left, z ∈ Set.range j.left ∨ z ∈ Set.range v.left := by
  rw [hj, hv, range_section, range_section]
  intro z
  by_cases h : z = sectionSupport x
  · exact Or.inl (fun e => hne (h.symm.trans (Set.mem_singleton_iff.mp e)))
  · exact Or.inr (fun e => h (Set.mem_singleton_iff.mp e))

private theorem contracting_quotient_affine_charts
    {H : AffineAlgebraicGroup k} {T : ClosedSubgroup H.val}
    (hH : IsReductive H) {c : Cocharacter H.val}
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (hT : Specs.RankOneFlag.IsGeometricallyMaximal T) (hTE : IsSubgroupOf T E.centralizer)
    (hT₁ : IsSubgroupOf T D.parabolic) (Q : Presentation D.parabolic)
    (hp : IsProper Q.scheme.hom)
    (n : 𝟙_ (SchemeOver k) ⟶ H.val.X)
    (hn : Normalizes (extendSubgroup (AlgebraicClosure k) T).inclusion
      (scalarExtendedRationalPoint (AlgebraicClosure k) n))
    (hconj : ConjugatesSubgroups n D.parabolic E.parabolic)
    (hne : η[H.val.X] ≫ Q.projection ≠ n ≫ Q.projection)
    (hfix :
      let K := AlgebraicClosure k
      ∀ x : 𝟙_ (SchemeOver K) ⟶ (baseChange k K).obj Q.scheme,
        IsFixedBy (baseChangeAction K ((T.inclusion.hom.hom ▷ Q.scheme) ≫ (quotientAction Q).smul)) x ↔
        x = scalarExtendedRationalPoint K (η[H.val.X] ≫ Q.projection) ∨
          x = scalarExtendedRationalPoint K (n ≫ Q.projection)) :
    let j := E.contracting.inclusion.hom.hom ≫ Q.projection
    let x := η[H.val.X] ≫ Q.projection
    let y := n ≫ Q.projection
    let v := j ≫ (translateAction (quotientAction Q) n).inv
    IsOpenImmersion j.left ∧ IsOpenImmersion v.left ∧
    Set.range j.left = (Set.range y.left)ᶜ ∧ Set.range v.left = (Set.range x.left)ᶜ ∧
    (∀ z : Q.scheme.left, z ∈ Set.range j.left ∨ z ∈ Set.range v.left) ∧
    ∃ i : affineLine k ≅ E.contracting.group.X,
      affineLineZero k ≫ i.hom = 1 ∧ Specs.RankOneFlag.IsSplitAdditive E.contracting.group := by
  intro j x y v
  let a := quotientAction Q
  let t := translateAction a n
  let U := E.contracting.group.X
  have ha := quotient_action_equivariant (H := H) Q
  letI : Smooth H.val.X.hom := hH.1
  letI : GeometricallyConnected H.val.X.hom := hH.2.1
  letI : ConnectedSpace H.val.X.left := GeometricallyConnected.connectedSpace_of_subsingleton H.val.X.hom
  letI : IsProper Q.scheme.hom := hp
  haveI : IrreducibleSpace Q.scheme.left := quotient_irreducible hH Q
  haveI : IsOpenImmersion j.left := opposite_contracting_open_cell H D E Q (CocharacterDynamics.bigCell H c D E)
  haveI : IsIso t.inv.left := (Over.forget _).map_isIso t.inv
  haveI : IsOpenImmersion v.left := inferInstanceAs (IsOpenImmersion (j.left ≫ t.inv.left))
  have hU : IsSubgroupOf E.contracting E.parabolic := ⟨E.contractingToParabolic, E.contracting_in_G⟩
  have hdis := quotient_cell_disjoint_normalizer_coset Q a ha n hconj hU hne
  have hj : Set.range j.left = (Set.range y.left)ᶜ :=
    contracting_quotient_cell_range (H := H) hT E hTE hT₁ Q hp n hn hfix ‹_› hdis
  have htran : x ≫ t.hom = y := translate_identity_coset Q a ha n
  have hback : y ≫ t.inv = x := by rw [← htran, Category.assoc, t.hom_inv_id, Category.comp_id]
  have hv : Set.range v.left = (Set.range x.left)ᶜ := by
    change Set.range (t.inv.left ∘ j.left) = _
    rw [Set.range_comp, hj, Set.image_compl_eq ⟨t.inv.left.injective, t.inv.left.surjective⟩, ← Set.range_comp]
    rw [← show (y ≫ t.inv).left = t.inv.left ∘ y.left from rfl, hback]
  have hx : η[U] ≫ j = x := quotient_cell_identity E.contracting Q
  have hxj : sectionSupport x ∈ Set.range j.left := by
    rw [← hx, sectionSupport_comp]
    exact Set.mem_range_self _
  have hxy : sectionSupport x ≠ sectionSupport y := by
    intro eq
    apply (Set.disjoint_left.mp hdis) hxj
    rw [range_section, eq]
    exact Set.mem_singleton _
  refine ⟨‹_›, ‹_›, hj, hv, open_complements_of_distinct_points hxy hj hv, ?_⟩
  have hs := (CocharacterDynamics.limitSubgroupsSmooth H (oppositeCocharacter c) E).2.1
  haveI : GeometricallyConnected U.hom :=
    (CocharacterDynamics.geometricallyConnectedLimitSubgroups H (oppositeCocharacter c) E).2.1
  have hc := GeometricallyConnected.connectedSpace_of_subsingleton U.hom
  have hr : Set.range v.left = ({sectionSupport (η[U] ≫ j)} : Set Q.scheme.left)ᶜ := by
    rw [hx, hv, range_section]
  have hV : IsAffine U.left := (closedSubgroupAlgebraicGroup (G := H) E.contracting).property.1
  exact contracting_line_from_affine_charts H E hs hc j v hV ⟨sectionSupport (η[U])⟩ hr

private theorem affineLine_dimension (k : Type u) [Field k] :
    topologicalKrullDim (affineLine k).left = 1 := by
  change topologicalKrullDim (PrimeSpectrum (Polynomial k)) = 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]

private theorem dimension_of_affine_line_iso {X : SchemeOver k} (i : affineLine k ≅ X) :
    topologicalKrullDim X.left = 1 := by
  letI : IsIso i.hom.left := (Over.forget _).map_isIso i.hom
  rw [← i.hom.left.homeomorph.isHomeomorph.topologicalKrullDim_eq, affineLine_dimension]

private theorem smooth_of_two_open_charts {X A : SchemeOver k}
    (j v : A ⟶ X) [IsOpenImmersion j.left] [IsOpenImmersion v.left] (hs : Smooth A.hom)
    (hc : ∀ z : X.left, z ∈ Set.range j.left ∨ z ∈ Set.range v.left) :
    Smooth X.hom := by
  let C := openCoverPair j.left v.left hc
  refine (IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth) C).mpr ?_
  intro i
  cases i
  · change Smooth (j.left ≫ X.hom)
    rw [Over.w]
    exact hs
  · change Smooth (v.left ≫ X.hom)
    rw [Over.w]
    exact hs

private theorem dimension_of_two_open_charts {X A : SchemeOver k}
    (j v : A ⟶ X) [IsOpenImmersion j.left] [IsOpenImmersion v.left]
    (hd : topologicalKrullDim A.left = 1)
    (hc : ∀ z : X.left, z ∈ Set.range j.left ∨ z ∈ Set.range v.left) :
    topologicalKrullDim X.left = 1 := by
  apply le_antisymm
  · apply iSup_le
    intro s
    obtain ⟨x, hx⟩ := s.head.isIrreducible.nonempty
    have go (f : A ⟶ X) [IsOpenImmersion f.left] (hr : x ∈ Set.range f.left) :
        (s.length : WithBot ℕ∞) ≤ 1 := by
      let e := TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding _ f.left.isOpenEmbedding
      let q : LTSeries (TopologicalSpace.IrreducibleCloseds A.left) :=
        { length := s.length
          toFun := fun n ↦ e.symm ⟨s n, by
            obtain ⟨y, hy⟩ := hr
            refine ⟨y, ?_⟩
            change f.left y ∈ (s n : Set X.left)
            rw [hy]
            exact s.head_le n hx⟩
          step := fun n ↦ e.symm.strictMono (s.step n) }
      exact hd ▸ q.length_le_krullDim
    exact (hc x).elim (go j) (go v)
  · rw [← hd]
    exact j.left.isOpenEmbedding.isInducing.topologicalKrullDim_le

end FlagQuotientCharts

section FlagGeometry

open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricRadicals (GeometricGroup IsReductive)
open Specs.RankOneFlag (AreTwoBorels SameSubgroup HasCoordinates Index projectiveLine plane
  planeBasis FlagIdentification)
open Specs.QuotientEmbedding (Presentation)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open CocharacterDynamics (LimitDecomposition oppositeCocharacter)
open private quotientAction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
open private translateAction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection

set_option maxHeartbeats 2300000

variable {k : Type u} [Field k]

private theorem twoBorels_swap {H : GroupScheme k} {T B₁ B₂ : ClosedSubgroup H}
    (h : AreTwoBorels T B₁ B₂) : AreTwoBorels T B₂ B₁ := by
  obtain ⟨h₁, h₂, hne, hT₁, hT₂, ht, hi, hj, hs⟩ := h
  exact ⟨h₂, h₁, fun h => hne (same_subgroup_symm h), hT₂, hT₁, ht, hj, hi,
    fun B hB hTB => (hs B hB hTB).symm⟩

private theorem recast_limit_decomposition {H : GroupScheme k} {c d : Cocharacter H}
    (h : c = d) (D : LimitDecomposition c) :
    ∃ D' : LimitDecomposition d, D'.parabolic = D.parabolic ∧
      D'.centralizer = D.centralizer ∧ D'.contracting = D.contracting := by
  cases h
  exact ⟨D, rfl, rfl, rfl⟩

private theorem pointed_range {X : SchemeOver k} (x : 𝟙_ (SchemeOver k) ⟶ X) :
    Set.range (toUnit ((testSpec k).obj (op (CommAlgCat.of k k))) ≫ x).left = Set.range x.left := by
  let A := (testSpec k).obj (op (CommAlgCat.of k k))
  letI : Subsingleton (𝟙_ (SchemeOver k)).left := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have h : Function.Surjective (toUnit A).left :=
    fun y => ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩
  exact h.range_comp x.left

private theorem marked_quotient_iso
    {H : AffineAlgebraicGroup k} {B U : ClosedSubgroup H.val}
    (Q : Presentation B) (n : 𝟙_ (SchemeOver k) ⟶ H.val.X)
    [IsSeparated Q.scheme.hom] (i : affineLine k ≅ U.group.X)
    (hi : affineLineZero k ≫ i.hom = 1)
    (j : U.group.X ⟶ Q.scheme) (hj : j = U.inclusion.hom.hom ≫ Q.projection)
    (v : U.group.X ⟶ Q.scheme)
    [IsOpenImmersion j.left] [IsOpenImmersion v.left]
    (hrj : Set.range j.left = (Set.range (n ≫ Q.projection).left)ᶜ)
    (hrv : Set.range v.left = (Set.range (η[H.val.X] ≫ Q.projection).left)ᶜ)
    (hc : ∀ z : Q.scheme.left, z ∈ Set.range j.left ∨ z ∈ Set.range v.left) :
    ∃ e : Q.scheme ≅ projectiveLine k,
      HasCoordinates (planeRepresentation k) (CommAlgCat.of k k)
        (toUnit _ ≫ η[H.val.X] ≫ Q.projection ≫ e.hom) (fun j => if j.down = 0 then 1 else 0) ∧
      HasCoordinates (planeRepresentation k) (CommAlgCat.of k k)
        (toUnit _ ≫ n ≫ Q.projection ≫ e.hom) (fun j => if j.down = 1 then 1 else 0) := by
  let F := CommAlgCat.of k k
  let x : Points Q.scheme F := toUnit _ ≫ (η[H.val.X] ≫ Q.projection)
  let y : Points Q.scheme F := toUnit _ ≫ (n ≫ Q.projection)
  let f := i.hom ≫ j
  let g := i.hom ≫ v
  haveI : IsIso i.hom.left := (Over.forget _).map_isIso i.hom
  haveI : IsOpenImmersion f.left := inferInstanceAs (IsOpenImmersion (i.hom.left ≫ j.left))
  haveI : IsOpenImmersion g.left := inferInstanceAs (IsOpenImmersion (i.hom.left ≫ v.left))
  have hf : Set.range f.left = Set.range j.left := i.hom.left.surjective.range_comp _
  have hg : Set.range g.left = Set.range v.left := i.hom.left.surjective.range_comp _
  have hfr : Set.range f.left = (Set.range y.left)ᶜ := by rw [hf, hrj, pointed_range]
  have hgr : Set.range g.left = (Set.range x.left)ᶜ := by rw [hg, hrv, pointed_range]
  have hx : affineLineZero k ≫ f = x := by
    rw [← Category.assoc, hi, CategoryTheory.Hom.one_def, Category.assoc, hj]
    exact congrArg (fun q => toUnit _ ≫ q) (quotient_cell_identity U Q)
  have hcover (z : Q.scheme.left) : z ∈ Set.range f.left ∨ z ∈ Set.range g.left := by
    rw [hf, hg]
    exact hc z
  have hy : Set.range y.left ⊆ Set.range g.left := by
    intro z hz
    exact (hcover z).resolve_left (fun h => (hfr ▸ h) hz)
  have hne : x ≠ y := by
    intro h
    rw [← hx] at h
    have hp : y.left (IsLocalRing.closedPoint k) ∈ Set.range f.left :=
      ⟨(affineLineZero k).left (IsLocalRing.closedPoint k),
        congrArg (fun z : Points Q.scheme F => z.left (IsLocalRing.closedPoint k)) h⟩
    exact (hfr ▸ hp) (Set.mem_range_self _)
  obtain ⟨s, hs⟩ := recenter_affine_chart g y hy
  let g' := s.hom ≫ g
  haveI : IsIso s.hom.left := (Over.forget _).map_isIso s.hom
  haveI : IsOpenImmersion g'.left := inferInstanceAs (IsOpenImmersion (s.hom.left ≫ g.left))
  have hgr' : Set.range g'.left = Set.range g.left := by
    change Set.range (g.left ∘ s.hom.left) = _
    exact s.hom.left.surjective.range_comp _
  obtain ⟨e, he₀, he₁⟩ := iso_of_two_affine_line_charts f g' x y hne hx hs
    hfr (hgr'.trans hgr) (fun z => by rw [hgr']; exact hcover z) (⟨0⟩ : Index.{u})
  refine ⟨e, ?_, ?_⟩
  · change HasCoordinates (planeRepresentation k) F (x ≫ e.hom) _
    rw [he₀]
    have h : affineCoordinates (R := F) (⟨0⟩ : Index.{u}) 0 =
        fun j => if j.down = 0 then 1 else 0 := by
      funext j
      rcases j with ⟨j⟩
      fin_cases j <;> rfl
    exact h ▸ affinePoint_coordinates F (⟨0⟩ : Index.{u}) 0
  · change HasCoordinates (planeRepresentation k) F (y ≫ e.hom) _
    rw [he₁]
    have he : otherIndex (⟨0⟩ : Index.{u}) = ⟨1⟩ := rfl
    rw [he]
    have h : affineCoordinates (R := F) (⟨1⟩ : Index.{u}) 0 =
        fun j => if j.down = 1 then 1 else 0 := by
      funext j
      rcases j with ⟨j⟩
      fin_cases j <;> rfl
    exact h ▸ affinePoint_coordinates F (⟨1⟩ : Index.{u}) 0

private theorem geometry_of_quotient_by_signed_borel
    {H : AffineAlgebraicGroup k} {T : ClosedSubgroup H.val} (hH : IsReductive H)
    {c : Cocharacter H.val} (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (hT : Specs.RankOneFlag.IsGeometricallyMaximal T)
    (hE : SchemeDerivedGroup.IsSubgroupOf T E.centralizer)
    (hB : AreTwoBorels T D.parabolic E.parabolic)
    (n : 𝟙_ (SchemeOver k) ⟶ H.val.X) (hn : Normalizes T.inclusion n)
    (hn' : Normalizes (extendSubgroup (AlgebraicClosure k) T).inclusion
      (scalarExtendedRationalPoint (AlgebraicClosure k) n))
    (hcosets :
      let K := AlgebraicClosure k
      let T' := extendSubgroup K T
      ∀ g : 𝟙_ (SchemeOver K) ⟶ (GeometricGroup H).val.X, Normalizes T'.inclusion g →
        g ∈ SubgroupSections T' (𝟙_ (SchemeOver K)) ∨
          (show 𝟙_ (SchemeOver K) ⟶ (GeometricGroup H).val.X from
            scalarExtendedRationalPoint K n)⁻¹ * g ∈ SubgroupSections T' (𝟙_ (SchemeOver K)))
    (hN :
      let K := AlgebraicClosure k
      ∃ N : ClosedSubgroup (GeometricGroup H).val, RepresentsSubgroup N
        (fun _ g => Normalizes (extendSubgroup K T).inclusion g))
    (Q : Presentation D.parabolic) :
    (topologicalKrullDim E.contracting.group.X.left = 1 ∧ Specs.RankOneFlag.IsSplitAdditive E.contracting.group) ∧
    (Smooth Q.scheme.hom ∧ IsProper Q.scheme.hom ∧ topologicalKrullDim Q.scheme.left = 1 ∧
      Nonempty (FlagIdentification T D.parabolic E.parabolic E.contracting Q)) := by
  letI : Smooth H.val.X.hom := hH.1
  let a := quotientAction Q
  let j := E.contracting.inclusion.hom.hom ≫ Q.projection
  let v := j ≫ (translateAction a n).inv
  have ha := quotient_action_equivariant (H := H) Q
  have hsD := (CocharacterDynamics.limitSubgroupsSmooth H c D).1
  have huE := (CocharacterDynamics.limitSubgroupsSmooth H (oppositeCocharacter c) E).2.1
  have hi := rank_one_borel_quotient_proper (H := H) hH hB.1 hsD Q
  letI : IsProper Q.scheme.hom := hi
  obtain ⟨hconj, hne, hrat, hgeom⟩ :=
    normalizer_conjugacy_of_borel_pair (H := H) hH hT hB n hn' hcosets hN Q
  obtain ⟨hj, hv, hrj, hrv, hc, i, hcoord, hsplit⟩ :=
    contracting_quotient_affine_charts (H := H) hH D E hT hE hB.2.2.2.1 Q hi
      n hn' hconj hne hgeom
  letI : IsOpenImmersion j.left := hj
  letI : IsOpenImmersion v.left := hv
  have hdim := dimension_of_affine_line_iso i
  obtain ⟨e, hinfty, h₀⟩ := marked_quotient_iso (H := H) Q n i hcoord j rfl v hrj hrv hc
  refine ⟨⟨hdim, hsplit⟩, smooth_of_two_open_charts j v huE hc, hi, dimension_of_two_open_charts j v hdim hc, ⟨?_⟩⟩
  exact {
    action := a
    quotientEquivariance := ha
    coordinates := planeRepresentation k
    iso := e
    normalizerPoint := n
    normalizes := hn
    conjugates := hconj
    infinityCoordinates := hinfty
    zeroCoordinates := h₀
    distinct := hne
    rationalFixedPoints := hrat
    geometricFixedPoints := hgeom
    positiveStabilizer := quotient_stabilizer_at_translate Q a ha η[H.val.X] D.parabolic
      (conjugates_by_identity (H := H) D.parabolic)
    negativeStabilizer := quotient_stabilizer_at_translate Q a ha n E.parabolic hconj
    openCell := hj
    openCellRange := hrj
  }

/-- The signed contracting groups and the marked right quotient of a root centralizer. -/
theorem rankOneFlagGeometry : Specs.RankOneFlag.RankOneFlagGeometry.{u} := by
  intro k _ G hG T hTs hTm α hα C cochar hp
  let H := closedSubgroupAlgebraicGroup C.subgroup
  let c := cochar ≫ C.torusIso.hom ≫ C.torus.inclusion
  have hH : IsReductive H := root_centralizer_reductive G hG T hTs hTm C
  letI : Smooth H.val.X.hom := hH.1
  obtain ⟨D⟩ := CocharacterDynamics.existsLimitDecomposition H c
  obtain ⟨E⟩ := CocharacterDynamics.existsLimitDecomposition H (oppositeCocharacter c)
  obtain ⟨hD, hE⟩ := limit_centralizers_eq_torus hTs C hH cochar hp D E
  obtain ⟨n, hn, hn', hcosets, hN, hB⟩ := root_signed_limit_borels hG hTs hTm hα C cochar hp D E
  have huD := (CocharacterDynamics.limitSubgroupsSmooth H c D).2.1
  have huE := (CocharacterDynamics.limitSubgroupsSmooth H (oppositeCocharacter c) E).2.1
  have hQ := QuotientEmbedding.quotientEmbedding k H D.parabolic
  have hpos (Q : Presentation D.parabolic) :
      (topologicalKrullDim E.contracting.group.X.left = 1 ∧ Specs.RankOneFlag.IsSplitAdditive E.contracting.group) ∧
      (Smooth Q.scheme.hom ∧ IsProper Q.scheme.hom ∧ topologicalKrullDim Q.scheme.left = 1 ∧
        Nonempty (FlagIdentification C.torus D.parabolic E.parabolic E.contracting Q)) :=
    geometry_of_quotient_by_signed_borel (H := H) (T := C.torus) hH D E C.torus_maximal hE.2 hB n hn hn' hcosets hN Q
  obtain ⟨hEdim, hEadd⟩ := (hpos (Classical.choice hQ)).1
  have hDdim_add : topologicalKrullDim D.contracting.group.X.left = 1 ∧
      Specs.RankOneFlag.IsSplitAdditive D.contracting.group := by
    have hsign : c = oppositeCocharacter (oppositeCocharacter c) := (opposite_opposite c).symm
    obtain ⟨D', hpar, hcen, hctr⟩ := recast_limit_decomposition hsign D
    have hRev : AreTwoBorels C.torus E.parabolic D'.parabolic := by
      rw [hpar]
      exact twoBorels_swap hB
    obtain ⟨Q₁⟩ := QuotientEmbedding.quotientEmbedding k H E.parabolic
    have hlev : SchemeDerivedGroup.IsSubgroupOf C.torus D'.centralizer := hcen.symm ▸ hD.2
    have hDim := (geometry_of_quotient_by_signed_borel (H := H) (T := C.torus) hH E D'
      C.torus_maximal hlev hRev n hn hn' hcosets hN Q₁).1
    exact hctr ▸ hDim
  exact ⟨D, E, ⟨hD, hE, hB, huD, huE, hDdim_add.1, hEdim, hDdim_add.2, hEadd⟩, hQ, fun Q => (hpos Q).2⟩

end FlagGeometry
end

end LinearAlgebraicGroups.RankOneFlag
