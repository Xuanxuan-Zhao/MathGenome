import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.FaithfulLinearization
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.NormalAffineQuotient
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.ConnectedTorusCentralizer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.RingTheory.Finiteness.Descent
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct MonoidAlgebra Matrix
open Coalgebra

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

universe u

namespace LinearAlgebraicGroups.NormalizerLatticeAction

open _root_.LinearAlgebraicGroups.Specs
open Specs.NormalizerLatticeAction
open Specs.DiagonalizableGroups (diagonalGroup groupAlgebra)
open Specs.GeometricRadicals (IsSplitTorus IsTorus)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)

noncomputable section

variable {k : Type u} [Field k]

/-- The diagonal and mixed coefficients of a group-like element give orthogonal
idempotents, even when the coefficient ring has nilpotents. -/
private theorem groupLike_coefficients {R M : Type u} [CommRing R] [CommMonoid M] [DecidableEq M]
    (x : MonoidAlgebra R M) (hx : IsGroupLikeElem R x) (a b : M) :
    x.coeff a * x.coeff b = if a = b then x.coeff a else 0 := by
  classical
  let coeff (m : M) : MonoidAlgebra R M →ₗ[R] R := (Finsupp.lapply m).comp (MonoidAlgebra.coeffLinearEquiv R).toLinearMap
  let eval : MonoidAlgebra R M ⊗[R] MonoidAlgebra R M →ₗ[R] R :=
    (TensorProduct.lid R R).toLinearMap.comp (TensorProduct.map (coeff a) (coeff b))
  have diag (y : MonoidAlgebra R M) :
      eval (comul y) = if a = b then y.coeff a else 0 := by
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
      split <;> simp_all [eq_comm]
    | single m r =>
      simp only [MonoidAlgebra.comul_single, eval, LinearMap.comp_apply, LinearEquiv.coe_coe, coeff, MonoidAlgebra.coeff_single]
      by_cases ha : m = a <;> by_cases hb : m = b <;> simp_all [eq_comm]
  rw [← diag, hx.comul_eq_tmul_self]
  rfl

private theorem idempotent_eq_zero_or_one_of_connected {R : Type u} [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {x : R} (hx : IsIdempotentElem x) :
    x = 0 ∨ x = 1 := by
  let e := PrimeSpectrum.isIdempotentElemEquivClopens (R := R)
  let c := e ⟨x, hx⟩
  have h : IsClopen (c : Set (PrimeSpectrum R)) := c.isClopen
  rcases isClopen_iff.mp h with hz | ho
  · left
    have hc : c = ⊥ := SetLike.ext' hz
    have he := congrArg e.symm hc
    change (e.symm (e ⟨x, hx⟩) : {z : R // IsIdempotentElem z}) = _ at he
    rw [OrderIso.symm_apply_apply] at he
    rw [PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot] at he
    exact congrArg Subtype.val he
  · right
    have hc : c = ⊤ := SetLike.ext' ho
    have he := congrArg e.symm hc
    change (e.symm (e ⟨x, hx⟩) : {z : R // IsIdempotentElem z}) = _ at he
    rw [OrderIso.symm_apply_apply] at he
    rw [PrimeSpectrum.isIdempotentElemEquivClopens_symm_top] at he
    exact congrArg Subtype.val he

private theorem groupLike_monomial_of_connected {R M : Type u} [CommRing R] [CommMonoid M]
    [Nontrivial R] [ConnectedSpace (PrimeSpectrum R)] {x : MonoidAlgebra R M}
    (hx : IsGroupLikeElem R x) :
    ∃ m : M, x = MonoidAlgebra.of R M m := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : M, x.coeff a ≠ 0 := by
    by_contra! h
    exact hx.ne_zero (MonoidAlgebra.coeff_eq_zero.mp (Finsupp.ext h))
  have ha₁ : x.coeff a = 1 :=
    (idempotent_eq_zero_or_one_of_connected (show x.coeff a * x.coeff a = x.coeff a by simpa using groupLike_coefficients x hx a a)).resolve_left ha
  refine ⟨a, MonoidAlgebra.ext (Finsupp.ext (fun b ↦ ?_))⟩
  by_cases hab : a = b
  · subst b
    simp [MonoidAlgebra.of_apply, ha₁]
  · have hh := groupLike_coefficients x hx a b
    simp [ha₁, hab] at hh
    simpa [MonoidAlgebra.of_apply, hab] using hh

open private mono_over conjugateLe_iff centralizes_iff comp_conjugateFamily from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

private abbrev pointMap {X : SchemeOver k} {R U : TestAlgebra k} (a : R ⟶ U) :=
  mapPoints (X := X) a

/-- Conjugation with a specified factorization through the closed subgroup, as a
homomorphism on points over any extension of the test algebra. -/
private def conjugationOnPoints {G H : GroupScheme k} {R : TestAlgebra k}
    (i : H ⟶ G) [Mono i.hom.hom] (g : Points G.X R)
    (c : H.X ⊗ (testSpec k).obj (op R) ⟶ H.X)
    (hc : c ≫ i.hom.hom = conjugateFamily i g)
    {U : TestAlgebra k} (a : R ⟶ U) : Points H.X U →* Points H.X U where
  toFun t := lift t ((testSpec k).map a.op) ≫ c
  map_one' := by
    apply (cancel_mono i.hom.hom).mp
    simp [hc, conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv]
  map_mul' s t := by
    apply (cancel_mono i.hom.hom).mp
    simp only [Category.assoc, hc, conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv,
      lift_snd_assoc, lift_fst_assoc, MonObj.mul_comp]
    let p : Points G.X U := pointMap a g
    change p * ((s ≫ i.hom.hom) * (t ≫ i.hom.hom)) * p⁻¹ =
      (p * (s ≫ i.hom.hom) * p⁻¹) * (p * (t ≫ i.hom.hom) * p⁻¹)
    group

private theorem conjugationOnPoints_natural {G H : GroupScheme k} {R U V : TestAlgebra k}
    (i : H ⟶ G) [Mono i.hom.hom] (g : Points G.X R)
    (c : H.X ⊗ (testSpec k).obj (op R) ⟶ H.X)
    (hc : c ≫ i.hom.hom = conjugateFamily i g)
    (a : R ⟶ U) (b : U ⟶ V) (t : Points H.X U) :
    pointMap b (conjugationOnPoints i g c hc a t) =
      conjugationOnPoints i g c hc (a ≫ b) (pointMap b t) := by
  change (testSpec k).map b.op ≫ lift t ((testSpec k).map a.op) ≫ c =
    lift (pointMap b t) ((testSpec k).map (a ≫ b).op) ≫ c
  rw [← Category.assoc, comp_lift, op_comp, Functor.map_comp]

open Specs.DiagonalizableGroups (characterValuedPoints)
open LinearAlgebraicGroups.DiagonalizableGroups (groupAlgebraPointsIso)

private abbrev diagonalPointEquiv (M : Type u) [CommGroup M] (A : TestAlgebra k) :
    Points (specGroup (groupAlgebra k M)).X A ≃* (M →* Aˣ) :=
  ((groupAlgebraPointsIso k M).app A).groupIsoToMulEquiv

private theorem diagonalPointEquiv_natural {M : Type u} [CommGroup M]
    {A B : TestAlgebra k} (f : A ⟶ B) (t : Points (specGroup (groupAlgebra k M)).X A) :
    diagonalPointEquiv M B (pointMap f t) =
      (Units.map f.hom.toMonoidHom).comp (diagonalPointEquiv M A t) :=
  by
    let e := groupAlgebraPointsIso k M
    have h := ConcreteCategory.congr_hom (e.hom.naturality f) t
    exact h

/-- The character values obtained by conjugating the universal torus point over
the group algebra of the parameter ring are group-like over that ring. -/
private theorem conjugatedMonomials_groupLike
    {G : GroupScheme k} {M : Type u} [CommGroup M] {A : TestAlgebra k}
    (i : specGroup (groupAlgebra k M) ⟶ G) [Mono i.hom.hom] (g : Points G.X A)
    (c : (specGroup (groupAlgebra k M)).X ⊗ (testSpec k).obj (op A) ⟶
      (specGroup (groupAlgebra k M)).X)
    (hc : c ≫ i.hom.hom = conjugateFamily i g) :
    let B := CommAlgCat.of k (MonoidAlgebra A M)
    let a : A ⟶ B := CommAlgCat.ofHom (IsScalarTower.toAlgHom k A B)
    let t := (diagonalPointEquiv M B).symm (MonoidAlgebra.of A M).toHomUnits
    ∀ m : M, IsGroupLikeElem A
      ((diagonalPointEquiv M B (conjugationOnPoints i g c hc a t) m : Bˣ) : B) := by
  dsimp only
  let B := CommAlgCat.of k (MonoidAlgebra A M)
  let D := CommAlgCat.of k (MonoidAlgebra A M ⊗[A] MonoidAlgebra A M)
  letI : CommRing D := inferInstanceAs (CommRing (MonoidAlgebra A M ⊗[A] MonoidAlgebra A M))
  letI : CommGroup Dˣ := Units.instCommGroupUnits
  let a : A ⟶ B := CommAlgCat.ofHom (IsScalarTower.toAlgHom k A B)
  let l : B ⟶ D := CommAlgCat.ofHom
    ((Algebra.TensorProduct.includeLeft : MonoidAlgebra A M →ₐ[A] D).restrictScalars k)
  let r : B ⟶ D := CommAlgCat.ofHom
    ((Algebra.TensorProduct.includeRight : MonoidAlgebra A M →ₐ[A] D).restrictScalars k)
  let d : B ⟶ D := CommAlgCat.ofHom ((Bialgebra.comulAlgHom A (MonoidAlgebra A M)).restrictScalars k)
  let e : B ⟶ A := CommAlgCat.ofHom ((Bialgebra.counitAlgHom A (MonoidAlgebra A M)).restrictScalars k)
  have hl : a ≫ l = a ≫ d := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact ((Algebra.TensorProduct.includeLeft : MonoidAlgebra A M →ₐ[A] D).commutes x).trans
      ((Bialgebra.comulAlgHom A (MonoidAlgebra A M)).commutes x).symm
  have hr : a ≫ r = a ≫ d := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact ((Algebra.TensorProduct.includeRight : MonoidAlgebra A M →ₐ[A] D).commutes x).trans
      ((Bialgebra.comulAlgHom A (MonoidAlgebra A M)).commutes x).symm
  have he : a ≫ e = 𝟙 A := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact (Bialgebra.counitAlgHom A (MonoidAlgebra A M)).commutes x
  let t := (diagonalPointEquiv M B).symm (MonoidAlgebra.of A M).toHomUnits
  have ht : diagonalPointEquiv M B t = (MonoidAlgebra.of A M).toHomUnits :=
    (diagonalPointEquiv M B).apply_symm_apply _
  have hd : pointMap d t = pointMap l t * pointMap r t := by
    apply (diagonalPointEquiv M D).injective
    rw [(diagonalPointEquiv M D).map_mul, diagonalPointEquiv_natural, diagonalPointEquiv_natural,
      diagonalPointEquiv_natural, ht]
    apply MonoidHom.ext
    intro m
    apply Units.ext
    change comul (MonoidAlgebra.single m (1 : A)) =
      (MonoidAlgebra.single m (1 : A) ⊗ₜ[A] (1 : B)) *
        ((1 : B) ⊗ₜ[A] MonoidAlgebra.single m (1 : A))
    rw [MonoidAlgebra.comul_single, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [Bialgebra.comul_one, Algebra.TensorProduct.one_def, TensorProduct.map_tmul]
    rfl
  have ht1 : pointMap e t = 1 := by
    apply (diagonalPointEquiv M A).injective
    rw [map_one, diagonalPointEquiv_natural, ht]
    apply MonoidHom.ext
    intro m
    apply Units.ext
    change counit (R := A) (MonoidAlgebra.single m (1 : A)) = 1
    exact MonoidAlgebra.counit_single _ _
  intro m
  let p := conjugationOnPoints i g c hc a t
  have hpD : pointMap d p = pointMap l p * pointMap r p := by
    simp only [p, conjugationOnPoints_natural, hl, hr, hd, map_mul]
  have hpE : pointMap e p = 1 := by
    rw [conjugationOnPoints_natural, he, ht1, map_one]
  constructor
  · have h := congrArg (fun q ↦ ((diagonalPointEquiv M A q m : Aˣ) : A)) hpE
    rw [diagonalPointEquiv_natural, map_one] at h
    exact h
  · have h := congrArg (fun q ↦ ((diagonalPointEquiv M D q m : Dˣ) : D)) hpD
    rw [(diagonalPointEquiv M D).map_mul, diagonalPointEquiv_natural,
      diagonalPointEquiv_natural, diagonalPointEquiv_natural] at h
    let x : MonoidAlgebra A M := (diagonalPointEquiv M B p m).val
    change comul x = (x ⊗ₜ[A] (1 : B)) * ((1 : B) ⊗ₜ[A] x) at h
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at h
    exact h


private theorem conjugationOnPoints_eq {G H : GroupScheme k} {A U : TestAlgebra k}
    (i : H ⟶ G) [Mono i.hom.hom] (g : Points G.X A)
    (c : H.X ⊗ (testSpec k).obj (op A) ⟶ H.X) (hc : c ≫ i.hom.hom = conjugateFamily i g)
    (a : A ⟶ U) (t : Points H.X U) :
    conjugationOnPoints i g c hc a t ≫ i.hom.hom =
      pointMap a g * (t ≫ i.hom.hom) * (pointMap a g)⁻¹ := by
  change (lift t ((testSpec k).map a.op) ≫ c) ≫ _ = _
  simp [hc, conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv]

private theorem groupAlgebra_eval {A U : TestAlgebra k} {M : Type u} [CommGroup M]
    (f : A ⟶ U) (t : Points (specGroup (groupAlgebra k M)).X U) :
    let B := CommAlgCat.of k (MonoidAlgebra A M)
    let a : A ⟶ B := CommAlgCat.ofHom (IsScalarTower.toAlgHom k A B)
    let t₀ := (diagonalPointEquiv M B).symm (MonoidAlgebra.of A M).toHomUnits
    ∃ b : B ⟶ U, a ≫ b = f ∧ pointMap b t₀ = t := by
  dsimp only
  let χ := diagonalPointEquiv M U t
  let b := MonoidAlgebra.liftNCAlgHom f.hom ((Units.coeHom U).comp χ) (fun _ _ ↦ Commute.all _ _)
  refine ⟨CommAlgCat.ofHom b, ?_, ?_⟩
  · apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    change b (MonoidAlgebra.single 1 x) = f.hom x
    simp [b, MonoidAlgebra.liftNC_single]
  · apply (diagonalPointEquiv M U).injective
    rw [diagonalPointEquiv_natural, MulEquiv.apply_symm_apply]
    apply MonoidHom.ext
    intro m
    apply Units.ext
    change b (MonoidAlgebra.single m 1) = (χ m).val
    simp [b, MonoidAlgebra.liftNC_single]

private theorem conjugationOnPoints_of_specializes_to_one
    {G : GroupScheme k} {M : Type u} [CommGroup M] {A : TestAlgebra k}
    [Nontrivial A] [ConnectedSpace (PrimeSpectrum A)]
    (i : specGroup (groupAlgebra k M) ⟶ G) [Mono i.hom.hom] (g : Points G.X A)
    (c : (specGroup (groupAlgebra k M)).X ⊗ (testSpec k).obj (op A) ⟶
      (specGroup (groupAlgebra k M)).X)
    (hc : c ≫ i.hom.hom = conjugateFamily i g)
    (f : A ⟶ CommAlgCat.of k k) (hf : pointMap f g = 1)
    {U : TestAlgebra k} (a : A ⟶ U) (t : Points (specGroup (groupAlgebra k M)).X U) :
    conjugationOnPoints i g c hc a t = t := by
  let B := CommAlgCat.of k (MonoidAlgebra A M)
  let B₀ := CommAlgCat.of k (MonoidAlgebra k M)
  let a₀ : A ⟶ B := CommAlgCat.ofHom (IsScalarTower.toAlgHom k A B)
  let a₁ : CommAlgCat.of k k ⟶ B₀ := CommAlgCat.ofHom (Algebra.ofId k B₀)
  let α : B ⟶ B₀ := CommAlgCat.ofHom
    (MonoidAlgebra.mapAlgHom M f.hom)
  let t₀ := (diagonalPointEquiv M B).symm (MonoidAlgebra.of A M).toHomUnits
  have hcomp : a₀ ≫ α = f ≫ a₁ := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    change (MonoidAlgebra.mapAlgHom M f.hom) (MonoidAlgebra.single 1 x) =
      MonoidAlgebra.single 1 (f.hom x)
    exact MonoidAlgebra.mapAlgHom_single f.hom 1 x
  have hgen : pointMap (f ≫ a₁) g = 1 := by
    change (testSpec k).map (f ≫ a₁).op ≫ g = _
    rw [op_comp, Functor.map_comp, Category.assoc]
    change (testSpec k).map a₁.op ≫ pointMap f g = _
    rw [hf, MonObj.comp_one]
  let s := conjugationOnPoints i g c hc a₀ t₀
  have hs : pointMap α s = pointMap α t₀ := by
    change pointMap α (conjugationOnPoints i g c hc a₀ t₀) = _
    rw [conjugationOnPoints_natural, hcomp, ← cancel_mono i.hom.hom, conjugationOnPoints_eq, hgen]
    simp
  have hs₀ : s = t₀ := by
    apply (diagonalPointEquiv M B).injective
    apply MonoidHom.ext
    intro m
    apply Units.ext
    obtain ⟨b, hb⟩ := groupLike_monomial_of_connected
      (conjugatedMonomials_groupLike i g c hc m)
    symm at hb
    have hm := congrArg (fun v ↦ ((diagonalPointEquiv M B₀ v m : B₀ˣ) : B₀)) hs
    rw [diagonalPointEquiv_natural, diagonalPointEquiv_natural] at hm
    change α.hom ((diagonalPointEquiv M B s m : Bˣ) : B) =
      α.hom ((diagonalPointEquiv M B t₀ m : Bˣ) : B) at hm
    have ht₀ : diagonalPointEquiv M B t₀ = (MonoidAlgebra.of A M).toHomUnits :=
      (diagonalPointEquiv M B).apply_symm_apply _
    rw [ht₀] at hm ⊢
    change MonoidAlgebra.of A M b = ((diagonalPointEquiv M B s m : Bˣ) : B) at hb
    rw [← hb] at hm ⊢
    change (MonoidAlgebra.mapAlgHom M f.hom) (MonoidAlgebra.single b 1) =
      (MonoidAlgebra.mapAlgHom M f.hom) (MonoidAlgebra.single m 1) at hm
    rw [MonoidAlgebra.mapAlgHom_single, MonoidAlgebra.mapAlgHom_single, map_one] at hm
    rw [MonoidAlgebra.single_left_injective (R := k) one_ne_zero hm]
    rfl
  obtain ⟨b, hb, ht⟩ := groupAlgebra_eval a t
  change a₀ ≫ b = a at hb
  change pointMap b t₀ = t at ht
  rw [← hb, ← ht, ← conjugationOnPoints_natural]
  exact congrArg (pointMap b) hs₀

open private geometricallyIrreducible_of_connected geometry_of_smooth_geometricallyIrreducible
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private factor_of_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

private theorem centralizes_on_connected_affine {G : GroupScheme k} {M : Type u}
    [CommGroup M] {A : TestAlgebra k} [Nontrivial A] [ConnectedSpace (PrimeSpectrum A)]
    (i : specGroup (groupAlgebra k M) ⟶ G) [Mono i.hom.hom] (g : Points G.X A)
    (hn : ConjugateLe i g) (f : A ⟶ CommAlgCat.of k k) (hf : pointMap f g = 1) :
    Centralizes i g := by
  let H := specGroup (groupAlgebra k M)
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  obtain ⟨c, hc⟩ := hn
  let X := H.X ⊗ (testSpec k).obj (op A)
  haveI : IsAffine H.X.left := inferInstanceAs
    (IsAffine (Spec (CommRingCat.of (MonoidAlgebra k M))))
  haveI : IsAffineHom ((testSpec k).obj (op A)).hom :=
    inferInstanceAs (IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap k A))))
  haveI : IsAffine X.left :=
    IsAffine.of_isPullback (IsPullback.of_hasPullback H.X.hom
      ((testSpec k).obj (op A)).hom)
  obtain ⟨U, ⟨d⟩⟩ := essImage_algSpec.mpr (inferInstance : IsAffine X.left)
  let t : Points H.X U.unop := d.hom ≫ fst _ _
  let a := (ff.preimage (d.hom ≫ snd H.X ((testSpec k).obj (op A)))).unop
  have ha : (testSpec k).map a.op = d.hom ≫ snd H.X ((testSpec k).obj (op A)) :=
    ff.map_preimage _
  have he := conjugationOnPoints_of_specializes_to_one i g c hc f hf a t
  have hc' := congrArg (fun z ↦ z ≫ i.hom.hom) he
  rw [conjugationOnPoints_eq] at hc'
  unfold Centralizes
  apply (cancel_epi d.hom).mp
  rw [comp_conjugateFamily]
  change (((testSpec k).map a.op ≫ g) * (t ≫ i.hom.hom)) *
    ((testSpec k).map a.op ≫ g)⁻¹ = t ≫ i.hom.hom at hc'
  rw [ha] at hc'
  simpa only [t, Category.assoc] using hc'

private theorem splitDiagonalCentral {G : AffineAlgebraicGroup k}
    [Smooth G.val.X.hom] [ConnectedSpace G.val.X.left] {M : Type u} [CommGroup M]
    (i : specGroup (groupAlgebra k M) ⟶ G.val) [Mono i.hom.hom]
    (hn : IsNormalSubgroup i) {Y : SchemeOver k} (y : Y ⟶ G.val.X) :
    Centralizes i y := by
  let H := specGroup (groupAlgebra k M)
  obtain ⟨A', ⟨e⟩⟩ := essImage_algSpec.mpr G.property.1
  let A := A'.unop
  let g : Points G.val.X A := e.hom
  haveI : GeometricallyIrreducible G.val.X.hom := geometricallyIrreducible_of_connected G
  haveI : IsIntegral G.val.X.left := (geometry_of_smooth_geometricallyIrreducible G.val.X).2.2
  let e' : Spec (CommRingCat.of A) ≅ G.val.X.left := (Over.forget _).mapIso e
  haveI : IsIntegral (Spec (CommRingCat.of A)) := IsIntegral.of_isIso e'.inv
  haveI : IsDomain A := (affine_isIntegral_iff (CommRingCat.of A)).mp inferInstance
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let f : A ⟶ CommAlgCat.of k k := (ff.preimage ((1 : Points G.val.X
    (CommAlgCat.of k k)) ≫ e.inv)).unop
  have hf : pointMap f g = 1 := by
    change (testSpec k).map (ff.preimage _) ≫ e.hom = _
    rw [ff.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  obtain ⟨c, hc⟩ := (conjugateLe_iff i g).mpr (fun U t h ↦
    normalSubgroup_conjugate_sections hn (t ≫ g) h)
  have hall : Centralizes i g := by
    haveI : ConnectedSpace (PrimeSpectrum A) :=
      e'.hom.homeomorph.connectedSpace_iff.mpr inferInstance
    exact centralizes_on_connected_affine i g ⟨c, hc⟩ f hf
  apply (centralizes_iff i y).mpr
  intro U p h
  have he := (centralizes_iff i g).mp hall U (p ≫ y ≫ e.inv) h
  simpa [g] using he

private theorem centralizes_of_split {G : AffineAlgebraicGroup k}
    [Smooth G.val.X.hom] [ConnectedSpace G.val.X.left] (T : ClosedSubgroup G.val)
    (hs : IsSplitTorus T.group) (hn : IsNormalSubgroup T.inclusion)
    {Y : SchemeOver k} (g : Y ⟶ G.val.X) : Centralizes T.inclusion g := by
  obtain ⟨r, ⟨e⟩⟩ := hs
  obtain ⟨d⟩ := LinearAlgebraicGroups.DiagonalizableGroups.diagonalIntegerPowers k (ULift.{u} (Fin r))
  let b := d ≪≫ e.symm
  let i := b.hom ≫ T.inclusion
  letI : Mono T.inclusion.hom.hom := mono_over _ T.isClosedImmersion
  haveI : IsIso b.hom.hom.hom := (Grp.forget _).map_isIso b.hom
  haveI : Mono i.hom.hom := mono_comp _ _
  have hb : b.inv.hom.hom ≫ b.hom.hom.hom = 𝟙 T.group.X :=
    (Grp.forget _).congr_map b.inv_hom_id
  have hn' : IsNormalSubgroup i := by
    obtain ⟨v, hv⟩ := normalSubgroup_conjugate_sections hn
      (fst G.val.X _ : G.val.X ⊗ _ ⟶ G.val.X) (snd G.val.X _ ≫ b.hom.hom.hom)
    refine ⟨v ≫ b.inv.hom.hom, ?_⟩
    change (v ≫ b.inv.hom.hom) ≫ b.hom.hom.hom ≫ T.inclusion.hom.hom = subgroupConjugation i
    rw [Category.assoc, ← Category.assoc b.inv.hom.hom b.hom.hom.hom, hb,
      Category.id_comp, hv]
    simp [subgroupConjugation, i]
  have h := splitDiagonalCentral i hn' g
  apply (centralizes_iff T.inclusion g).mpr
  intro U a t
  have e := (centralizes_iff i g).mp h U a (t ≫ b.inv.hom.hom)
  change Commute (a ≫ g) ((t ≫ b.inv.hom.hom) ≫ b.hom.hom.hom ≫ T.inclusion.hom.hom) at e
  simpa only [Category.assoc, ← Category.assoc b.inv.hom.hom b.hom.hom.hom, hb,
    Category.id_comp] using e

/-- A normal torus in a smooth connected affine algebraic group is central. -/
theorem normalTorusCentral_conditional :
    TorusFreeUnipotent.MaximalTorusCentralizer.{u} →
    TorusFreeUnipotent.Unipotence.{u} → NormalTorusCentral.{u} := by
  intro _ _ k _ G hG hconn T hT hn Y y
  letI : Smooth G.val.X.hom := hG
  letI : ConnectedSpace G.val.X.left := hconn
  obtain ⟨K, _, _, _, hs⟩ := hT
  let F := groupBaseChange k K
  let G' := baseChangedAlgebraicGroup K G
  haveI : Smooth G'.val.X.hom := inferInstanceAs
    (Smooth (pullback.snd G.val.X.hom (fieldSpecMap k K)))
  haveI : IrreducibleSpace G'.val.X.left := pullback_of_geometrically
    (geometricallyIrreducible_of_connected G).geometrically_irreducibleSpace K (fieldSpecMap k K)
  let T' : ClosedSubgroup G'.val :=
    ⟨F.obj T.group, F.map T.inclusion, baseChangeClosedSubgroup k K _ T.isClosedImmersion⟩
  have hn' : IsNormalSubgroup T'.inclusion := baseChangeNormalSubgroup k K T.inclusion hn
  have hc' := centralizes_of_split T' hs hn' ((baseChange k K).map y)
  obtain ⟨C, hc⟩ := centralizerScheme k G T
  obtain ⟨hi, hC'⟩ := centralizerSchemeBaseChange k K T.inclusion C hc
  obtain ⟨c, hcy⟩ := (hC' _ _).mp hc'
  haveI := C.isClosedImmersion
  exact (hc _ _).mpr (factor_of_baseChange K y C.inclusion.hom.hom c hcy)

open Specs.Unipotent (IsFppfGroupQuotient)
open Specs.NormalizerLatticeAction (GeometricFibres)
open private isMonHom_of_comp_closed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private baseChangeKernelSquare baseChangeMapPullback from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components
open private exists_section_lift from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry

private theorem centralizes_conjugate {G H : GroupScheme k} (i : H ⟶ G)
    (hi : IsClosedImmersion i.hom.hom.left) {Y : SchemeOver k} {c n : Y ⟶ G.X}
    (hc : Centralizes i c) (hn : Normalizes i n) :
    Centralizes i (n * c * n⁻¹) := by
  apply (centralizes_iff i _).mpr
  intro U u s
  obtain ⟨d, hd⟩ := (conjugateLe_iff i _).mp
    ((normalizesIff k i hi Y n).mp hn).2 U u s
  rw [GrpObj.comp_inv] at hd
  have h := ((centralizes_iff i c).mp hc U u d).conj (u ≫ n)
  rw [hd, inv_inv] at h
  have he : (u ≫ n) * ((u ≫ n)⁻¹ * (s ≫ i.hom.hom) * (u ≫ n)) * (u ≫ n)⁻¹ =
      s ≫ i.hom.hom := by group
  rw [he] at h
  simpa only [MonObj.comp_mul, GrpObj.comp_inv] using h

private theorem centralizer_in_normalizer {G H : GroupScheme k} {i : H ⟶ G}
    (hi : IsClosedImmersion i.hom.hom.left) {C N : ClosedSubgroup G}
    (hC : RepresentsSubgroup C (fun _ g ↦ Centralizes i g))
    (hN : RepresentsSubgroup N (fun _ g ↦ Normalizes i g)) :
    ∃ (j : C.group ⟶ N.group) (hj : IsClosedImmersion j.hom.hom.left),
      j ≫ N.inclusion = C.inclusion ∧ IsNormalSubgroup (⟨C.group, j, hj⟩ : ClosedSubgroup N.group).inclusion := by
  have hc := (hC _ _).mpr ⟨𝟙 _, Category.id_comp _⟩
  have hn : Normalizes i C.inclusion.hom.hom := ⟨Iso.refl _, Category.id_comp _, by
    rw [Iso.refl_hom, Category.id_comp, ← hc]⟩
  obtain ⟨f, hf⟩ := (hN _ _).mp hn
  haveI := N.isClosedImmersion
  haveI := isMonHom_of_comp_closed f C.inclusion N.inclusion hf
  let j : C.group ⟶ N.group := Grp.homMk'' f (IsMonHom.one_hom f) (IsMonHom.mul_hom f)
  have hj : j ≫ N.inclusion = C.inclusion := Grp.hom_ext _ _ hf
  have hji : IsClosedImmersion (j.hom.hom.left ≫ N.inclusion.hom.hom.left) := by
    rw [show j.hom.hom.left ≫ N.inclusion.hom.hom.left = C.inclusion.hom.hom.left from
      congrArg (fun f : C.group ⟶ G ↦ f.hom.hom.left) hj]
    exact C.isClosedImmersion
  have hjc := IsClosedImmersion.of_comp_isClosedImmersion j.hom.hom.left N.inclusion.hom.hom.left
  refine ⟨j, hjc, hj, ?_⟩
  let U := N.group.X ⊗ C.group.X
  let n : U ⟶ G.X := fst _ _ ≫ N.inclusion.hom.hom
  let c : U ⟶ G.X := snd _ _ ≫ C.inclusion.hom.hom
  have hnormal := (hN U n).mpr ⟨fst _ _, rfl⟩
  have hcentral := (hC U c).mpr ⟨snd _ _, rfl⟩
  obtain ⟨a, ha⟩ := (hC U _).mp (centralizes_conjugate i hi hcentral hnormal)
  refine ⟨a, ?_⟩
  haveI : Mono N.inclusion.hom.hom := mono_over _ N.isClosedImmersion
  change a ≫ j.hom.hom = subgroupConjugation j
  apply (cancel_mono N.inclusion.hom.hom).mp
  have he : j.hom.hom ≫ N.inclusion.hom.hom = C.inclusion.hom.hom :=
    congrArg (fun f : C.group ⟶ G ↦ f.hom.hom) hj
  rw [Category.assoc, he, ha]
  simp [subgroupConjugation, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, he, n, c]

private theorem translatedKernelPullback {N C Q : GroupScheme k}
    (q : N ⟶ Q) (j : C ⟶ N)
    (h : IsPullback j.hom.hom (toUnit C.X) q.hom.hom η[Q.X])
    (n : 𝟙_ (SchemeOver k) ⟶ N.X) :
    IsPullback ((toUnit C.X ≫ n) * j.hom.hom) (toUnit C.X) q.hom.hom (n ≫ q.hom.hom) := by
  have comm : CommSq ((toUnit C.X ≫ n) * j.hom.hom) (toUnit C.X) q.hom.hom (n ≫ q.hom.hom) := by
    constructor
    rw [MonObj.mul_comp, h.w]
    rw [← Category.assoc _ n, show toUnit C.X ≫ η[Q.X] = (1 : C.X ⟶ Q.X) from rfl, mul_one]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk comm.w ?_ ?_ ?_ ?_)
  · intro s
    exact h.lift ((toUnit s.pt ≫ n)⁻¹ * s.fst) s.snd (by
      rw [MonObj.mul_comp, GrpObj.inv_comp, s.condition]
      rw [Category.assoc, toUnit_unique (toUnit s.pt) s.snd, inv_mul_cancel]
      exact (MonObj.comp_one s.snd).symm)
  · intro s
    simp only [MonObj.comp_mul, comp_toUnit_assoc, IsPullback.lift_fst]
    simp
  · intro s
    exact h.lift_snd _ _ _
  · intro s m h₁ h₂
    apply h.hom_ext
    · rw [h.lift_fst]
      have hu : (toUnit s.pt ≫ n) * (m ≫ j.hom.hom) = s.fst := by
        simpa only [MonObj.comp_mul, comp_toUnit_assoc] using h₁
      rw [← hu, inv_mul_cancel_left]
    · rw [h.lift_snd, h₂]

private theorem geometricFibres_of_fppf {C N Q : AffineAlgebraicGroup k}
    (q : N.val ⟶ Q.val) (j : C.val ⟶ N.val) (hj : IsClosedImmersion j.hom.hom.left)
    (hf : IsFppfGroupQuotient (G := N) (Q := Q) ⟨C.val, j, hj⟩ q) :
    GeometricFibres j q := by
  intro K _ _ _
  dsimp only
  intro w
  let F := groupBaseChange k K
  let N' := baseChangedAlgebraicGroup K N
  let Q' := baseChangedAlgebraicGroup K Q
  let : LocallyOfFiniteType (F.obj N.val).X.hom := N'.property.2.1
  let : LocallyOfFiniteType (F.obj Q.val).X.hom := Q'.property.2.1
  have hs : Surjective (F.map q).hom.hom.left :=
    MorphismProperty.of_isPullback (P := @Surjective) (baseChangeMapPullback (K := K) q.hom.hom).flip hf.2.2.1
  obtain ⟨n, hn⟩ := exists_section_lift (F.map q).hom.hom w (hs.1 _)
  refine ⟨n, hn, ?_⟩
  rw [← hn]
  exact translatedKernelPullback (F.map q) (F.map j) (baseChangeKernelSquare q j hf.1) n

private theorem quotientOfRepresentingSubgroups {G : AffineAlgebraicGroup k}
    {S N C : ClosedSubgroup G.val}
    (hN : RepresentsSubgroup N (fun _ g ↦ Normalizes S.inclusion g))
    (hC : RepresentsSubgroup C (fun _ g ↦ Centralizes S.inclusion g)) :
    ∃ (j : C.group ⟶ N.group) (hj : IsClosedImmersion j.hom.hom.left)
      (Q : AffineAlgebraicGroup k) (q : N.group ⟶ Q.val),
      j ≫ N.inclusion = C.inclusion ∧
      IsFppfGroupQuotient (G := closedSubgroupAlgebraicGroup N) ⟨_, j, hj⟩ q ∧ GeometricFibres j q := by
  obtain ⟨j, hj, he, hnormal⟩ := centralizer_in_normalizer S.isClosedImmersion hC hN
  let N' := closedSubgroupAlgebraicGroup N
  let C' : ClosedSubgroup N'.val := ⟨C.group, j, hj⟩
  obtain ⟨L, f, Q, q, i, hK, hqK, himage, hcanonical, e, heq⟩ :=
    normalAffineQuotient N' C' hnormal
  have hq : IsFppfGroupQuotient (G := N') C' q :=
    ⟨hqK, himage.2.1, himage.2.2.1, himage.2.2.2.1, e, heq⟩
  exact ⟨j, hj, Q, q, he, hq,
    geometricFibres_of_fppf (C := closedSubgroupAlgebraicGroup C) q j hj hq⟩

/-- Construct the affine fppf quotient and the translation isomorphisms of its
geometric fibres. -/
theorem existsNormalizerQuotient {G : AffineAlgebraicGroup k} (S : ClosedSubgroup G.val) :
    ∃ (N C : ClosedSubgroup G.val)
      (j : C.group ⟶ N.group) (hj : IsClosedImmersion j.hom.hom.left)
      (Q : AffineAlgebraicGroup k) (q : N.group ⟶ Q.val),
      RepresentsSubgroup N (fun _ g ↦ Normalizes S.inclusion g) ∧
      RepresentsSubgroup C (fun _ g ↦ Centralizes S.inclusion g) ∧
      j ≫ N.inclusion = C.inclusion ∧
      IsFppfGroupQuotient (G := closedSubgroupAlgebraicGroup N) ⟨_, j, hj⟩ q ∧ GeometricFibres j q := by
  obtain ⟨N, hN⟩ := normalizerScheme k G S
  obtain ⟨C, hC⟩ := centralizerScheme k G S
  obtain ⟨j, hj, Q, q, he, hq, hgeo⟩ := quotientOfRepresentingSubgroups hN hC
  exact ⟨N, C, j, hj, Q, q, hN, hC, he, hq, hgeo⟩

open Specs.GeometricBorelConjugacy (IsBorel ConjugatesSubgroups subgroupOfSubgroup)
open Specs.GeometricRadicals (IsMaximalTorus)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.QuotientEmbedding (Presentation)

open private quotientAct quotientAct_comp quotientAct_one quotientAct_mul quotientAct_projection
  rationalLift
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper
open private projection_eq_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.QuotientEmbedding
open private conjugationIso transportSubgroup conjugates_maximal restrictSubgroup compose_restrict
  local_maximal_of_ambient solvable_tori_conjugate conjugates_trans conjugates_in_ambient
  comp_conjugate conjugate conjugate_inv_cancel rationalConstant
  normalizes_of_conjugates_self
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate

@[instance_reducible]
private def quotientAction {G : GroupScheme k} {B : ClosedSubgroup G} (P : Presentation B) :
    ModObj G.X P.scheme where
  smul := quotientAct P (fst _ _) (snd _ _)
  one_smul := by
    change (η[G.X] ▷ P.scheme) ≫ quotientAct P _ _ = (λ_ P.scheme).hom
    rw [quotientAct_comp, whiskerRight_fst, whiskerRight_snd, MonObj.one_eq_one,
      MonObj.comp_one, quotientAct_one, leftUnitor_hom]
  mul_smul := by
    let act := quotientAct P (fst G.X P.scheme) (snd _ _)
    change (μ[G.X] ▷ P.scheme) ≫ act =
      (α_ G.X G.X P.scheme).hom ≫ (G.X ◁ act) ≫ act
    simp only [act, quotientAct_comp, whiskerRight_fst, whiskerRight_snd,
      whiskerLeft_fst, whiskerLeft_snd, associator_hom_fst, associator_hom_snd_fst,
      associator_hom_snd_snd, MonObj.mul_eq_mul]
    simp only [MonObj.comp_mul, quotientAct_mul]

private theorem quotientAction_eval {G : GroupScheme k} {B : ClosedSubgroup G} (P : Presentation B)
    {Y : SchemeOver k} (g : Y ⟶ G.X) (x : Y ⟶ P.scheme) :
    lift g x ≫ (quotientAction P).smul = quotientAct P g x := by
  change lift g x ≫ quotientAct P (fst _ _) (snd _ _) = _
  rw [quotientAct_comp, lift_fst, lift_snd]

private theorem quotientFixed_iff {G : GroupScheme k} {T B : ClosedSubgroup G}
    (P : Presentation B) (g : 𝟙_ (SchemeOver k) ⟶ G.X) :
    IsFixedPoint (quotientAction P) T (g ≫ P.projection) ↔
      ∃ b : T.group.X ⟶ B.group.X,
        b ≫ B.inclusion.hom.hom =
          (toUnit T.group.X ≫ g)⁻¹ * T.inclusion.hom.hom * (toUnit T.group.X ≫ g) := by
  let c := toUnit T.group.X ≫ g
  change (lift T.inclusion.hom.hom (toUnit T.group.X ≫ g ≫ P.projection) ≫
    (quotientAction P).smul = toUnit T.group.X ≫ g ≫ P.projection) ↔ _
  rw [← Category.assoc (toUnit T.group.X) g P.projection, quotientAction_eval, quotientAct_projection]
  rw [eq_comm, projection_eq_iff]
  simp only [mul_assoc]
  rfl

private theorem normalizerFixed {G : GroupScheme k} {T B N : ClosedSubgroup G}
    (hTB : IsSubgroupOf T B) (hN : RepresentsSubgroup N (fun _ g ↦ Normalizes T.inclusion g))
    (P : Presentation B) (n : 𝟙_ (SchemeOver k) ⟶ N.group.X) :
    IsFixedPoint (quotientAction P) T (n ≫ N.inclusion.hom.hom ≫ P.projection) := by
  rw [← Category.assoc n N.inclusion.hom.hom P.projection, quotientFixed_iff]
  let g := n ≫ N.inclusion.hom.hom
  have hn : Normalizes T.inclusion g := (hN _ _).mpr ⟨n, rfl⟩
  obtain ⟨d, hd⟩ := (conjugateLe_iff T.inclusion g⁻¹).mp
    ((normalizesIff k T.inclusion T.isClosedImmersion _ g).mp hn).2 _ (toUnit _) (𝟙 _)
  obtain ⟨i, hi⟩ := hTB
  refine ⟨d ≫ i.hom.hom, ?_⟩
  rw [Category.assoc, show i.hom.hom ≫ B.inclusion.hom.hom = T.inclusion.hom.hom from
    congrArg (fun f : T.group ⟶ G ↦ f.hom.hom) hi, hd]
  simp only [Category.id_comp, GrpObj.comp_inv, inv_inv, g]

private theorem fixedPointLiftToNormalizer [IsAlgClosed k]
    {G : AffineAlgebraicGroup k} {T B N : ClosedSubgroup G.val} (hT : IsMaximalTorus T)
    (hB : IsBorel B) (hTB : IsSubgroupOf T B)
    (hN : RepresentsSubgroup N (fun _ g ↦ Normalizes T.inclusion g))
    (P : Presentation B) (g : 𝟙_ (SchemeOver k) ⟶ G.val.X)
    (hf : IsFixedPoint (quotientAction P) T (g ≫ P.projection)) :
    ∃ n : 𝟙_ (SchemeOver k) ⟶ N.group.X, n ≫ N.inclusion.hom.hom ≫ P.projection =
      g ≫ P.projection := by
  obtain ⟨j, hj⟩ := hTB
  let S := restrictSubgroup T B j hj
  have hS := compose_restrict T B j hj
  let e := conjugationIso g⁻¹
  let T' := transportSubgroup e T
  have hconj : ConjugatesSubgroups g⁻¹ T T' := by
    refine ⟨Iso.refl _, ?_⟩
    change (𝟙 T.group ≫ T'.inclusion).hom.hom = _
    rw [Category.id_comp]
    change T.inclusion.hom.hom ≫ conjugate g⁻¹ (𝟙 G.val.X) = _
    rw [comp_conjugate, Category.comp_id]
    rfl
  obtain ⟨v, hv⟩ := (quotientFixed_iff P g).mp hf
  have hv' : v ≫ B.inclusion.hom.hom = T'.inclusion.hom.hom := by
    change v ≫ B.inclusion.hom.hom = T.inclusion.hom.hom ≫ conjugate g⁻¹ (𝟙 G.val.X)
    rw [comp_conjugate, Category.comp_id, hv]
    simp only [conjugate, rationalConstant, GrpObj.comp_inv, inv_inv]
  have := B.isClosedImmersion
  have := isMonHom_of_comp_closed v T'.inclusion B.inclusion hv'
  let i : T'.group ⟶ B.group := Grp.homMk'' v (IsMonHom.one_hom v) (IsMonHom.mul_hom v)
  have hi : i ≫ B.inclusion = T'.inclusion := Grp.hom_ext _ _ hv'
  let D := restrictSubgroup T' B i hi
  have hD := compose_restrict T' B i hi
  obtain ⟨b, hb⟩ := solvable_tori_conjugate
    LinearAlgebraicGroups.GeometricTorusSplitting.splitting
    LinearAlgebraicGroups.GeometricTorusSplitting.conjugacy (closedSubgroupAlgebraicGroup B)
    hB.1.1 hB.1.2.1 hB.1.2.2 S D
    (local_maximal_of_ambient _ _ (hS.symm ▸ hT))
    (local_maximal_of_ambient _ _ (hD.symm ▸ conjugates_maximal hconj hT))
  have hb' : ConjugatesSubgroups (b ≫ B.inclusion.hom.hom) T T' := by
    change subgroupOfSubgroup B S = T at hS
    change subgroupOfSubgroup B D = T' at hD
    rw [← hS, ← hD]
    exact conjugates_in_ambient B hb
  have hconj' : ConjugatesSubgroups g T' T := by
    refine ⟨Iso.refl _, ?_⟩
    change (𝟙 T.group ≫ T.inclusion).hom.hom = _
    rw [Category.id_comp]
    change T.inclusion.hom.hom = conjugate g (T.inclusion.hom.hom ≫ conjugate g⁻¹ (𝟙 G.val.X))
    rw [comp_conjugate, Category.comp_id]
    simpa using (conjugate_inv_cancel g⁻¹ T.inclusion.hom.hom).symm
  obtain ⟨n, hn⟩ := (hN _ _).mp (normalizes_of_conjugates_self T (conjugates_trans hb' hconj'))
  refine ⟨n, ?_⟩
  rw [← Category.assoc n, hn, eq_comm, projection_eq_iff, inv_mul_cancel_left]
  exact ⟨b, rfl⟩

/-- The subset fixed by the full torus orbit map is a single normalizer orbit. -/
theorem borelFixedPointOrbit
    {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (T B : ClosedSubgroup G.val) (hT : IsMaximalTorus T) (hB : IsBorel B)
    (hTB : IsSubgroupOf T B) (N : ClosedSubgroup G.val)
    (hN : RepresentsSubgroup N (fun _ g ↦ Normalizes T.inclusion g))
    (P : Presentation B) :
    ∃ a : ModObj G.val.X P.scheme,
      lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ P.projection) ≫ a.smul =
        μ[G.val.X] ≫ P.projection ∧
      (∀ x : 𝟙_ (SchemeOver k) ⟶ P.scheme,
        IsFixedPoint a T x ↔
          ∃ n : 𝟙_ (SchemeOver k) ⟶ N.group.X, n ≫ N.inclusion.hom.hom ≫ P.projection = x) ∧
      ∀ x y : 𝟙_ (SchemeOver k) ⟶ P.scheme,
        IsFixedPoint a T x → IsFixedPoint a T y →
        ∃ n : 𝟙_ (SchemeOver k) ⟶ N.group.X,
          lift (n ≫ N.inclusion.hom.hom) x ≫ a.smul = y := by
  let : LocallyOfFinitePresentation P.projection.left := P.finitePresentation
  refine ⟨quotientAction P, ?_, ?_, ?_⟩
  · rw [quotientAction_eval, quotientAct_projection, MonObj.mul_eq_mul]
  · intro x
    refine ⟨fun hx ↦ ?_, ?_⟩
    · obtain ⟨g, rfl⟩ := rationalLift P.projection P.surjective inferInstance x
      exact fixedPointLiftToNormalizer hT hB hTB hN P g hx
    · rintro ⟨n, rfl⟩
      exact normalizerFixed hTB hN P n
  · intro x y hx hy
    obtain ⟨g, rfl⟩ := rationalLift P.projection P.surjective inferInstance x
    obtain ⟨h, rfl⟩ := rationalLift P.projection P.surjective inferInstance y
    obtain ⟨n, hn⟩ := fixedPointLiftToNormalizer hT hB hTB hN P g hx
    obtain ⟨m, hm⟩ := fixedPointLiftToNormalizer hT hB hTB hN P h hy
    refine ⟨m * n⁻¹, ?_⟩
    rw [quotientAction_eval, ← hn, ← Category.assoc n, quotientAct_projection,
      MonObj.mul_comp _ _ N.inclusion.hom.hom, GrpObj.inv_comp, inv_mul_cancel_right]
    exact hm

open Topology TopologicalSpace
open private iso_of_same_subgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.ConnectedTorusCentralizer

private theorem centralizes_on_connected_affine_split
    {G H : GroupScheme k} (i : H ⟶ G) (hi : IsClosedImmersion i.hom.hom.left)
    (hs : IsSplitTorus H) {A : TestAlgebra k} [ConnectedSpace (PrimeSpectrum A)]
    (g : Points G.X A) (hn : ConjugateLe i g)
    (f : A ⟶ CommAlgCat.of k k) (hf : pointMap f g = 1) :
    Centralizes i g := by
  obtain ⟨r, ⟨e⟩⟩ := hs
  obtain ⟨d⟩ := LinearAlgebraicGroups.DiagonalizableGroups.diagonalIntegerPowers k (ULift.{u} (Fin r))
  let b := d ≪≫ e.symm
  let j := b.hom ≫ i
  let : Mono i.hom.hom := mono_over _ hi
  let : IsIso b.hom.hom.hom := (Grp.forget _).map_isIso b.hom
  let : Mono j.hom.hom := mono_comp _ _
  let : Nontrivial A := f.hom.toRingHom.domain_nontrivial
  have hb : b.inv.hom.hom ≫ b.hom.hom.hom = 𝟙 H.X :=
    (Grp.forget _).congr_map b.inv_hom_id
  have hn' : ConjugateLe j g := by
    apply (conjugateLe_iff j g).mpr
    intro U u t
    obtain ⟨s, hs⟩ := (conjugateLe_iff i g).mp hn U u (t ≫ b.hom.hom.hom)
    refine ⟨s ≫ b.inv.hom.hom, ?_⟩
    change (s ≫ b.inv.hom.hom) ≫ b.hom.hom.hom ≫ i.hom.hom = _
    rw [Category.assoc, ← Category.assoc b.inv.hom.hom b.hom.hom.hom, hb, Category.id_comp, hs]
    rfl
  have h := centralizes_on_connected_affine j g hn' f hf
  apply (centralizes_iff i g).mpr
  intro U a t
  have h' := (centralizes_iff j g).mp h U a (t ≫ b.inv.hom.hom)
  change Commute (a ≫ g) ((t ≫ b.inv.hom.hom) ≫ b.hom.hom.hom ≫ i.hom.hom) at h'
  simpa only [Category.assoc, ← Category.assoc b.inv.hom.hom b.hom.hom.hom, hb,
    Category.id_comp] using h'

private theorem isAffineOpen_of_isClopen {X : Scheme.{u}} [IsAffine X]
    (U : X.Opens) (hc : IsClopen (U : Set X)) : IsAffineOpen U := by
  let V : Clopens (Spec Γ(X, ⊤)) := ⟨X.isoSpec.inv ⁻¹' (U : Set X),
    hc.preimage X.isoSpec.inv.continuous⟩
  obtain ⟨e, he⟩ := (PrimeSpectrum.isIdempotentElemEquivClopens (R := Γ(X, ⊤))).surjective V
  have hv : X.isoSpec.inv ⁻¹ᵁ U = PrimeSpectrum.basicOpen e.val := by
    apply SetLike.coe_injective
    exact congrArg (fun w : Clopens (PrimeSpectrum Γ(X, ⊤)) ↦ (w : Set (PrimeSpectrum Γ(X, ⊤)))) he.symm
  have h := (hv ▸ IsAffineOpen.Spec_basicOpen e.val : IsAffineOpen (X.isoSpec.inv ⁻¹ᵁ U))
  have hpre : X.isoSpec.hom ⁻¹ᵁ (X.isoSpec.inv ⁻¹ᵁ U) = U := by
    ext x
    change (X.isoSpec.inv (X.isoSpec.hom x) ∈ U) ↔ x ∈ U
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  exact hpre ▸ h.preimage_of_isIso X.isoSpec.hom

private theorem centralizer_contains_open_component {G : AffineAlgebraicGroup k}
    {S N C : ClosedSubgroup G.val} (hs : IsSplitTorus S.group)
    (hN : RepresentsSubgroup N (fun _ g ↦ Normalizes S.inclusion g))
    (hC : RepresentsSubgroup C (fun _ g ↦ Centralizes S.inclusion g))
    (j : C.group ⟶ N.group) (hj : j ≫ N.inclusion = C.inclusion)
    (U : N.group.X.left.Opens)
    (hU : (U : Set N.group.X.left) = connectedComponent (η[N.group.X].left (IsLocalRing.closedPoint k))) :
    let V : SchemeOver k := Over.mk (U.ι ≫ N.group.X.hom)
    let v : V ⟶ N.group.X := Over.homMk U.ι
    ∃ l : V ⟶ C.group.X, l ≫ j.hom.hom = v := by
  intro V v
  let x := η[N.group.X].left (IsLocalRing.closedPoint k)
  let N' := closedSubgroupAlgebraicGroup N
  let : IsAffine N.group.X.left := N'.property.1
  have hap : IsAffine V.left :=
    isAffineOpen_of_isClopen U ⟨hU.symm ▸ isClosed_connectedComponent, U.isOpen⟩
  have hconn : ConnectedSpace V.left := by
    change ConnectedSpace (U : Set N.group.X.left)
    rw [← isConnected_iff_connectedSpace, hU]
    exact isConnected_connectedComponent
  obtain ⟨A', ⟨e⟩⟩ := essImage_algSpec.mpr hap
  let A := A'.unop
  let g : Points G.val.X A := e.hom ≫ v ≫ N.inclusion.hom.hom
  have hn := (hN _ _).mpr ⟨e.hom ≫ v, Category.assoc ..⟩
  let e' : Spec (CommRingCat.of A) ≅ V.left := (Over.forget _).mapIso e
  let : ConnectedSpace (PrimeSpectrum A) := e'.hom.homeomorph.connectedSpace_iff.mpr hconn
  let a : Spec (CommRingCat.of k) ⟶ V.left :=
    IsOpenImmersion.lift U.ι η[N.group.X].left (by
      rintro _ ⟨y, rfl⟩
      rw [Subsingleton.elim y (IsLocalRing.closedPoint k)]
      have hx : x ∈ U := by
        change x ∈ (U : Set N.group.X.left)
        rw [hU]
        exact mem_connectedComponent
      exact ⟨⟨x, hx⟩, rfl⟩)
  have ha : a ≫ U.ι = η[N.group.X].left := IsOpenImmersion.lift_fac _ _ _
  let e₀ : (testSpec k).obj (op (CommAlgCat.of k k)) ≅ 𝟙_ (SchemeOver k) :=
    Over.isoMk (Iso.refl (Spec (CommRingCat.of k))) (by
      change (𝟙 _) ≫ (𝟙 _) = Spec.map (𝟙 (CommRingCat.of k))
      rw [Spec.map_id, Category.comp_id])
  let a₀ : (𝟙_ (SchemeOver k)) ⟶ V := Over.homMk a (by
    change a ≫ U.ι ≫ N.group.X.hom = _
    rw [← Category.assoc, ha]
    exact Over.w η[N.group.X])
  have ha₀ : a₀ ≫ v = (1 : 𝟙_ (SchemeOver k) ⟶ N.group.X) := by
    apply Over.OverMorphism.ext
    exact ha
  let a' := e₀.hom ≫ a₀
  have ha' : a' ≫ v = 1 := by
    rw [Category.assoc, ha₀, MonObj.comp_one]
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let f : A ⟶ CommAlgCat.of k k := (ff.preimage (a' ≫ e.inv)).unop
  have hf : pointMap f g = 1 := by
    change (testSpec k).map (ff.preimage (a' ≫ e.inv)) ≫ (e.hom ≫ v ≫ N.inclusion.hom.hom) = _
    rw [ff.map_preimage, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc a', ha',
      MonObj.one_comp]
  have hc := centralizes_on_connected_affine_split S.inclusion S.isClosedImmersion hs g
    ((normalizesIff k S.inclusion S.isClosedImmersion _ g).mp hn).1 f hf
  obtain ⟨c, hc⟩ := (hC _ _).mp hc
  let l := e.inv ≫ c
  refine ⟨l, ?_⟩
  let : Mono N.inclusion.hom.hom := mono_over _ N.isClosedImmersion
  apply (cancel_mono N.inclusion.hom.hom).mp
  have he : j.hom.hom ≫ N.inclusion.hom.hom = C.inclusion.hom.hom :=
    congrArg (fun f : C.group ⟶ G.val ↦ f.hom.hom) hj
  change (e.inv ≫ c) ≫ j.hom.hom ≫ N.inclusion.hom.hom = _
  rw [Category.assoc, he, hc, Iso.inv_hom_id_assoc]

open private quotientRepresentsImage from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient

private theorem quotientByCentralizer_finiteEtale_split
    {G : AffineAlgebraicGroup k} {S N C : ClosedSubgroup G.val}
    {Q : AffineAlgebraicGroup k} (q : N.group ⟶ Q.val)
    (hs : IsSplitTorus S.group)
    (hN : RepresentsSubgroup N (fun _ g ↦ Normalizes S.inclusion g))
    (hC : RepresentsSubgroup C (fun _ g ↦ Centralizes S.inclusion g))
    [ConnectedSpace C.group.X.left]
    (j : C.group ⟶ N.group) (hj : j ≫ N.inclusion = C.inclusion)
    (hjc : IsClosedImmersion j.hom.hom.left)
    (hQ : IsFppfGroupQuotient (G := closedSubgroupAlgebraicGroup N) ⟨C.group, j, hjc⟩ q) :
    IsFinite Q.val.X.hom ∧ Etale Q.val.X.hom ∧ GeometricallyConnected q.hom.hom.left := by
  let N' := closedSubgroupAlgebraicGroup N
  let C' : ClosedSubgroup N'.val := ⟨C.group, j, hjc⟩
  obtain ⟨E, H, p, i, h, _⟩ := identityComponentAndQuotient k N'
  let x := η[N.group.X].left (IsLocalRing.closedPoint k)
  let : IsAffine N.group.X.left := N'.property.1
  let : LocallyOfFiniteType N.group.X.hom := N'.property.2.1
  let : IsLocallyNoetherian N.group.X.left := LocallyOfFiniteType.isLocallyNoetherian N.group.X.hom
  let : IsNoetherian N.group.X.left := ⟨⟩
  let U : N.group.X.left.Opens := ⟨connectedComponent x, (isClopenConnectedComponent _ x).2⟩
  let V : SchemeOver k := Over.mk (U.ι ≫ N.group.X.hom)
  let v : V ⟶ N.group.X := Over.homMk U.ι
  obtain ⟨l, hl⟩ := centralizer_contains_open_component hs hN hC j hj U rfl
  have hcomp : Set.range i.hom.hom.left = (U : Set N.group.X.left) := by
    rw [h.identityComponent]
    congr 2
    exact @Subsingleton.elim (Spec (CommRingCat.of k)) inferInstance _ _
  have hvo : Set.range v.left = (U : Set N.group.X.left) := U.range_ι
  let : IsOpenImmersion i.hom.hom.left := h.openImmersion
  let : IsOpenImmersion v.left := inferInstanceAs (IsOpenImmersion U.ι)
  let τ : H.X.left ≅ V.left := IsOpenImmersion.isoOfRangeEq i.hom.hom.left v.left (hcomp.trans hvo.symm)
  have hτ : τ.hom ≫ v.left = i.hom.hom.left := IsOpenImmersion.isoOfRangeEq_hom_fac .. 
  let a : H.X ⟶ C.group.X := Over.homMk τ.hom (by
    change τ.hom ≫ (v.left ≫ N.group.X.hom) = _
    rw [← Category.assoc, hτ]
    exact Over.w i.hom.hom) ≫ l
  have ha : a ≫ j.hom.hom = i.hom.hom := by
    change ((_ : H.X ⟶ V) ≫ l) ≫ j.hom.hom = _
    rw [Category.assoc, hl]
    exact Over.OverMorphism.ext hτ
  have hc : Set.range j.hom.hom.left ⊆ Set.range i.hom.hom.left := by
    rw [hcomp, show (U : Set N.group.X.left) = connectedComponent x from rfl]
    rw [← Set.image_univ]
    apply (isConnected_univ.image _ j.hom.hom.left.continuous.continuousOn).subset_connectedComponent
    · rw [Set.image_univ]
      refine ⟨η[C.group.X].left (IsLocalRing.closedPoint k), ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left]
      exact congrArg (fun z : 𝟙_ (SchemeOver k) ⟶ N.group.X ↦
        z.left (IsLocalRing.closedPoint k)) (IsMonHom.one_hom j.hom.hom)
  let b₀ := IsOpenImmersion.lift i.hom.hom.left j.hom.hom.left hc
  have hb₀ : b₀ ≫ i.hom.hom.left = j.hom.hom.left := IsOpenImmersion.lift_fac _ _ _
  let b : C.group.X ⟶ H.X := Over.homMk b₀ (by
    calc
      b₀ ≫ H.X.hom = b₀ ≫ (i.hom.hom.left ≫ N.group.X.hom) := congrArg (b₀ ≫ ·) (Over.w i.hom.hom).symm
      _ = C.group.X.hom := by rw [← Category.assoc, hb₀, Over.w j.hom.hom])
  have hb : b ≫ i.hom.hom = j.hom.hom := Over.OverMorphism.ext hb₀
  let : Mono j.hom.hom := mono_over _ hjc
  let : Mono i.hom.hom := mono_over _ h.closedImmersion
  let e : C.group.X ≅ H.X := ⟨b, a,
    (cancel_mono j.hom.hom).mp (by rw [Category.assoc, ha, hb, Category.id_comp]),
    (cancel_mono i.hom.hom).mp (by rw [Category.assoc, hb, ha, Category.id_comp])⟩
  have hp : IsSchemeKernel p C' := by
    have hp0 : IsPullback i.hom.hom (toUnit H.X) p.hom.hom η[E.X] :=
      IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext h.kernel.w) h.kernel
    unfold IsSchemeKernel
    change IsPullback j.hom.hom (toUnit C.group.X) p.hom.hom η[E.X]
    apply hp0.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simpa [e] using hb
    · apply Subsingleton.elim
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  let : IsFinite E.X.hom := h.finite
  let : IsAffine E.X.left := isAffine_of_isAffineHom E.X.hom
  have hfac : IsImageFactorization p p (𝟙 E) := by
    refine ⟨Category.comp_id _, h.flat, h.surjective, h.locallyOfFinitePresentation, ?_, ?_⟩
    · exact @isAffineHom_of_isAffine N.group.X.left E.X.left p.hom.hom.left
        N'.property.1 inferInstance
    · change IsClosedImmersion (𝟙 E.X.left)
      infer_instance
  obtain ⟨z, hz⟩ := quotientRepresentsImage hfac hp
  obtain ⟨w, hw⟩ := hQ.2.2.2.2
  let F := (fppfOver k).uliftYoneda
  let t : Q.val.X ≅ E.X := (fppfOver k).fullyFaithfulUliftYoneda.preimageIso (w.symm ≪≫ z)
  have ht : F.map t.hom = w.inv ≫ z.hom :=
    (fppfOver k).fullyFaithfulUliftYoneda.map_preimage _
  have hqt : q.hom.hom ≫ t.hom = p.hom.hom := by
    apply F.map_injective
    rw [F.map_comp, ht, ← hw, ← hz, Category.assoc, Iso.hom_inv_id_assoc]
  let t' := (Over.forget (Spec (CommRingCat.of k))).mapIso t
  have hqt' : q.hom.hom.left ≫ t'.hom = p.hom.hom.left :=
    congrArg (fun m : N.group.X ⟶ E.X ↦ m.left) hqt
  refine ⟨?_, ?_, ?_⟩
  · rw [← Over.w t.hom]
    exact inferInstanceAs (IsFinite (t'.hom ≫ E.X.hom))
  · rw [← Over.w t.hom]
    let : Etale E.X.hom := h.etale
    exact inferInstanceAs (Etale (t'.hom ≫ E.X.hom))
  · rw [GeometricallyConnected.eq_geometrically,
      ← MorphismProperty.cancel_right_of_respectsIso (geometrically (ConnectedSpace ·)) _ t'.hom,
      hqt']
    exact h.connectedFibers.geometrically_connectedSpace

open private isCommMonObj_of_groupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.HopfAlgebras
open private solvable_maximal_torus_iff isTorus_iff_coordinates
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private split_of_torus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting

private theorem splitTorus_sectionsCommute {T : GroupScheme k} (hT : IsSplitTorus T)
    (Y : SchemeOver k) : IsMulCommutative (Y ⟶ T.X) := by
  obtain ⟨r, ⟨e⟩⟩ := hT
  obtain ⟨d⟩ := LinearAlgebraicGroups.DiagonalizableGroups.diagonalIntegerPowers k (ULift.{u} (Fin r))
  let b := d ≪≫ e.symm
  let M := Multiplicative (ULift.{u} (Fin r) → ℤ)
  have h : IsCommMonObj (specGroup (groupAlgebra k M)).X :=
    (hopfSpecCommutativity k (groupAlgebra k M)).mpr inferInstance
  exact (isCommMonObj_iff_isMulCommutative _).mp (isCommMonObj_of_groupIso b h) Y

private theorem normalizerInBorelCentralizes [IsAlgClosed k] {G : AffineAlgebraicGroup k}
    {T B : ClosedSubgroup G.val} (hT : IsMaximalTorus T) (hB : IsBorel B)
    (hTB : IsSubgroupOf T B) {b : 𝟙_ (SchemeOver k) ⟶ B.group.X}
    (hn : Normalizes T.inclusion (b ≫ B.inclusion.hom.hom)) :
    Centralizes T.inclusion (b ≫ B.inclusion.hom.hom) := by
  obtain ⟨j, hj⟩ := hTB
  let S := restrictSubgroup T B j hj
  have hS := compose_restrict T B j hj
  let A := closedSubgroupAlgebraicGroup B
  have hmax : IsMaximalTorus S := local_maximal_of_ambient _ _ (hS.symm ▸ hT)
  obtain ⟨U, D, q, _, _, hD, _, hsplit⟩ :=
    LinearAlgebraicGroups.GeometricTorusSplitting.splitting A hB.1.1 hB.1.2.1 hB.1.2.2
  let : IsIso (j ≫ q) :=
    (hsplit S).1.mp ((solvable_maximal_torus_iff A S).mpr hmax)
  let : IsIso (j ≫ q).hom.hom := (Grp.forget _).map_isIso (j ≫ q)
  let : Mono B.inclusion.hom.hom := mono_over _ B.isClosedImmersion
  have hj' : j.hom.hom ≫ B.inclusion.hom.hom = T.inclusion.hom.hom :=
    congrArg (fun f : T.group ⟶ G.val ↦ f.hom.hom) hj
  apply (centralizes_iff T.inclusion _).mpr
  intro Y y t
  obtain ⟨s, hs⟩ := (conjugateLe_iff T.inclusion _).mp
    ((normalizesIff k T.inclusion T.isClosedImmersion _ _).mp hn).1 Y y t
  have he : s ≫ j.hom.hom = ((y ≫ b) * (t ≫ j.hom.hom)) * (y ≫ b)⁻¹ := by
    apply (cancel_mono B.inclusion.hom.hom).mp
    change s ≫ j.hom.hom ≫ B.inclusion.hom.hom = _ ≫ B.inclusion.hom.hom
    rw [hj', hs]
    rw [MonObj.mul_comp, GrpObj.inv_comp, MonObj.mul_comp]
    simp only [Category.assoc, hj']
  have hst : s = t := by
    apply (cancel_mono (j ≫ q).hom.hom).mp
    change s ≫ (j.hom.hom ≫ q.hom.hom) = t ≫ (j.hom.hom ≫ q.hom.hom)
    rw [← Category.assoc, he, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
    let : IsMulCommutative (Y ⟶ D.val.X) := splitTorus_sectionsCommute hD Y
    rw [mul_comm' ((y ≫ b) ≫ q.hom.hom), mul_assoc, mul_inv_cancel, mul_one, Category.assoc]
  rw [hst] at hs
  exact mul_inv_eq_iff_eq_mul.mp hs.symm

private theorem borelNormalizerCosets [IsAlgClosed k] {G : AffineAlgebraicGroup k}
    {T B N C : ClosedSubgroup G.val} (hT : IsMaximalTorus T) (hB : IsBorel B)
    (hTB : IsSubgroupOf T B)
    (hN : RepresentsSubgroup N (fun _ g ↦ Normalizes T.inclusion g))
    (hC : RepresentsSubgroup C (fun _ g ↦ Centralizes T.inclusion g))
    (hCB : IsSubgroupOf C B)
    (P : Presentation B) (n₁ n₂ : 𝟙_ (SchemeOver k) ⟶ N.group.X) :
    (n₁ ≫ N.inclusion.hom.hom ≫ P.projection =
      n₂ ≫ N.inclusion.hom.hom ≫ P.projection) ↔
      Centralizes T.inclusion ((n₂⁻¹ * n₁) ≫ N.inclusion.hom.hom) := by
  rw [eq_comm, ← Category.assoc n₂, ← Category.assoc n₁, projection_eq_iff]
  rw [← GrpObj.inv_comp, ← MonObj.mul_comp]
  let g := (n₂⁻¹ * n₁) ≫ N.inclusion.hom.hom
  change (∃ b : 𝟙_ (SchemeOver k) ⟶ B.group.X, b ≫ B.inclusion.hom.hom = g) ↔ _
  constructor
  · rintro ⟨b, hb⟩
    have hn : Normalizes T.inclusion g := (hN _ _).mpr ⟨n₂⁻¹ * n₁, rfl⟩
    change Centralizes T.inclusion g
    rw [← hb] at hn ⊢
    exact normalizerInBorelCentralizes hT hB hTB hn
  · intro hc
    obtain ⟨c, hc'⟩ := (hC _ _).mp hc
    obtain ⟨i, hi⟩ := hCB
    refine ⟨c ≫ i.hom.hom, ?_⟩
    rw [Category.assoc, show i.hom.hom ≫ B.inclusion.hom.hom = C.inclusion.hom.hom from
      congrArg (fun f : C.group ⟶ G.val ↦ f.hom.hom) hi, hc']

private theorem centralizer_geometricallyConnected {G : AffineAlgebraicGroup k}
    [Smooth G.val.X.hom] [ConnectedSpace G.val.X.left] {S C : ClosedSubgroup G.val}
    (hs : IsTorus S.group) (hC : RepresentsSubgroup C (fun _ g ↦ Centralizes S.inclusion g)) :
    GeometricallyConnected C.group.X.hom := by
  obtain ⟨D, hD, _, hgeo⟩ := CocharacterDynamics.connectedTorusCentralizer G S hs
  obtain ⟨e⟩ := iso_of_same_subgroup C D hC hD
  let e' := (Over.forget (Spec (CommRingCat.of k))).mapIso e
  have : GeometricallyConnected (e'.hom ≫ D.group.X.hom) :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyConnected) _ _).mpr hgeo
  exact (Over.w e.hom) ▸ this

open private fieldSpec_surjective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.ConnectedTorusCentralizer

open private groupPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private extendedGroupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

private theorem isFinite_of_fieldExtension (Q : AffineAlgebraicGroup k)
    (K : Type u) [Field K] [Algebra k K]
    (h : IsFinite ((groupBaseChange k K).obj Q.val).X.hom) :
    IsFinite Q.val.X.hom := by
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation Q
  let F := groupBaseChange k K
  let U := Grp.forget (SchemeOver K)
  let V := Over.forget (Spec (CommRingCat.of K))
  let i := U.mapIso (extendedGroupIso K A ≪≫ F.mapIso e)
  let i' := V.mapIso i
  let : IsFinite (F.obj Q.val).X.hom := h
  have he : IsFinite (specGroup (extendedHopf K A)).X.hom :=
    (Over.w i.hom) ▸ inferInstanceAs (IsFinite (i'.hom ≫ (F.obj Q.val).X.hom))
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[k] A)))) at he
  let : Module.Finite K (K ⊗[k] A) :=
    RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp he)
  let : Module.Finite k A := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat K
  have ha : IsFinite (specGroup A).X.hom := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k A)))
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  let j := (Grp.forget (SchemeOver k)).mapIso e
  let j' := (Over.forget (Spec (CommRingCat.of k))).mapIso j
  let := ha
  exact (Over.w j.inv) ▸ inferInstanceAs (IsFinite (j'.inv ≫ (specGroup A).X.hom))

private theorem baseChangedGroupQuotient (K : Type u) [Field K] [Algebra k K]
    {C N Q : AffineAlgebraicGroup k} (q : N.val ⟶ Q.val) (j : C.val ⟶ N.val)
    (hj : IsClosedImmersion j.hom.hom.left)
    (hQ : IsFppfGroupQuotient (G := N) (Q := Q) ⟨_, j, hj⟩ q)
    (hj' : IsClosedImmersion ((groupBaseChange k K).map j).hom.hom.left) :
    IsFppfGroupQuotient (G := baseChangedAlgebraicGroup K N) (Q := baseChangedAlgebraicGroup K Q)
      ⟨_, (groupBaseChange k K).map j, hj'⟩ ((groupBaseChange k K).map q) := by
  let F := groupBaseChange k K
  let N' := baseChangedAlgebraicGroup K N
  let Q' := baseChangedAlgebraicGroup K Q
  let j' := F.map j
  let q' := F.map q
  let D : ClosedSubgroup N'.val := ⟨F.obj C.val, j', hj'⟩
  have hk : IsSchemeKernel q' D := baseChangeKernelSquare q j hQ.1
  have hpb := (baseChangeMapPullback (K := K) q.hom.hom).flip
  have hflat : Flat q'.hom.hom.left := MorphismProperty.of_isPullback hpb hQ.2.1
  have hsurj : Surjective q'.hom.hom.left := MorphismProperty.of_isPullback hpb hQ.2.2.1
  have hfp : LocallyOfFinitePresentation q'.hom.hom.left :=
    MorphismProperty.of_isPullback hpb hQ.2.2.2.1
  have hq_aff : IsAffineHom q'.hom.hom.left := @isAffineHom_of_isAffine
    N'.val.X.left Q'.val.X.left q'.hom.hom.left
    N'.property.1 Q'.property.1
  have hfac : IsImageFactorization q' q' (𝟙 Q'.val) :=
    ⟨Category.comp_id _, hflat, hsurj, hfp, hq_aff, by
      change IsClosedImmersion (𝟙 Q'.val.X.left)
      infer_instance⟩
  obtain ⟨e, he⟩ := quotientRepresentsImage hfac hk
  exact ⟨hk, hflat, hsurj, hfp, e, he⟩

private theorem quotientByCentralizer_finiteEtale
    {G : AffineAlgebraicGroup k} [Smooth G.val.X.hom] [ConnectedSpace G.val.X.left]
    {S N C : ClosedSubgroup G.val}
    {Q : AffineAlgebraicGroup k} (q : N.group ⟶ Q.val)
    (hs : IsTorus S.group)
    (hN : RepresentsSubgroup N (fun _ g ↦ Normalizes S.inclusion g))
    (hC : RepresentsSubgroup C (fun _ g ↦ Centralizes S.inclusion g))
    (j : C.group ⟶ N.group) (hj : j ≫ N.inclusion = C.inclusion)
    (hjc : IsClosedImmersion j.hom.hom.left)
    (hQ : IsFppfGroupQuotient (G := closedSubgroupAlgebraicGroup N) ⟨C.group, j, hjc⟩ q) :
    IsFinite Q.val.X.hom ∧ Etale Q.val.X.hom := by
  have hgc := centralizer_geometricallyConnected hs hC
  obtain ⟨K, _, _, _, hsplit⟩ := hs
  let b := fieldSpecMap k K
  let F := groupBaseChange k K
  let G' := baseChangedAlgebraicGroup K G
  let Q' := baseChangedAlgebraicGroup K Q
  let S' : ClosedSubgroup G'.val :=
    ⟨F.obj S.group, F.map S.inclusion, baseChangeClosedSubgroup k K _ S.isClosedImmersion⟩
  obtain ⟨hNc, hN'⟩ := normalizerSchemeBaseChange k K S.inclusion N S.isClosedImmersion hN
  obtain ⟨hCc, hC'⟩ := centralizerSchemeBaseChange k K S.inclusion C hC
  let N' := scalarExtendedSubgroup K N hNc
  let C' := scalarExtendedSubgroup K C hCc
  let j' := F.map j
  let q' := F.map q
  have hji : j' ≫ N'.inclusion = C'.inclusion := by
    change F.map j ≫ F.map N.inclusion = F.map C.inclusion
    rw [← F.map_comp, hj]
  have hj' : IsClosedImmersion j'.hom.hom.left := baseChangeClosedSubgroup k K j hjc
  let : GeometricallyConnected C'.group.X.hom :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback C.group.X.hom b) hgc
  let : ConnectedSpace C'.group.X.left := GeometricallyConnected.connectedSpace_of_subsingleton C'.group.X.hom
  have hQ' := baseChangedGroupQuotient K (C := closedSubgroupAlgebraicGroup C)
    (N := closedSubgroupAlgebraicGroup N) (Q := Q) q j hjc hQ hj'
  have hfin := quotientByCentralizer_finiteEtale_split (G := G') (S := S') (N := N')
    (C := C') (Q := Q') q' hsplit hN' hC' j' hji hj' hQ'
  refine ⟨isFinite_of_fieldExtension Q K hfin.1, ?_⟩
  exact MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Etale)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (g := b)
    ⟨⟨fieldSpec_surjective b, inferInstance⟩, inferInstance⟩ hfin.2.1

/-- The normalizer and centralizer are represented over the ground field, and
their affine right fppf quotient is finite étale with geometric fibres given
by left translates of the centralizer. -/
theorem existsFiniteEtaleNormalizerQuotient (G : AffineAlgebraicGroup k)
    [Smooth G.val.X.hom] [ConnectedSpace G.val.X.left]
    (S : ClosedSubgroup G.val) (hS : IsTorus S.group) :
    ∃ (N C : ClosedSubgroup G.val)
      (j : C.group ⟶ N.group) (hj : IsClosedImmersion j.hom.hom.left)
      (Q : AffineAlgebraicGroup k) (q : N.group ⟶ Q.val),
      RepresentsSubgroup N (fun _ g ↦ Normalizes S.inclusion g) ∧
      RepresentsSubgroup C (fun _ g ↦ Centralizes S.inclusion g) ∧
      j ≫ N.inclusion = C.inclusion ∧
      IsFppfGroupQuotient (G := closedSubgroupAlgebraicGroup N) ⟨_, j, hj⟩ q ∧
      IsFinite Q.val.X.hom ∧ Etale Q.val.X.hom ∧ GeometricFibres j q := by
  obtain ⟨N, C, j, hj, Q, q, hN, hC, he, hq, hf⟩ := existsNormalizerQuotient (G := G) S
  obtain ⟨hfin, hEtale⟩ := quotientByCentralizer_finiteEtale q hS hN hC j he hj hq
  exact ⟨N, C, j, hj, Q, q, hN, hC, he, hq, hfin, hEtale, hf⟩

open private sameImage_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient

private theorem finite_rationalSections [IsAlgClosed k] (X : SchemeOver k)
    [IsFinite X.hom] : Finite (𝟙_ (SchemeOver k) ⟶ X) := by
  have hu : (X.hom ⁻¹' ({IsLocalRing.closedPoint k} : Set (Spec (CommRingCat.of k)))) = Set.univ :=
    Set.eq_univ_of_forall fun _ ↦ Subsingleton.elim _ _
  letI : Finite X.left := Set.finite_univ_iff.mp (hu ▸ X.hom.finite_preimage_singleton _)
  apply Finite.of_injective (fun p : 𝟙_ (SchemeOver k) ⟶ X ↦
    p.left (IsLocalRing.closedPoint k))
  intro p q h
  apply Over.OverMorphism.ext
  let p' : {s : Spec (CommRingCat.of k) ⟶ X.left // s ≫ X.hom = 𝟙 _} := ⟨p.left, Over.w p⟩
  let q' : {s : Spec (CommRingCat.of k) ⟶ X.left // s ≫ X.hom = 𝟙 _} := ⟨q.left, Over.w q⟩
  have he : pointEquivClosedPoint X.hom p' = pointEquivClosedPoint X.hom q' := Subtype.ext h
  exact congrArg Subtype.val ((pointEquivClosedPoint X.hom).injective he)

/-- The finite geometric fixed set in the Borel quotient is one normalizer
orbit and is indexed by right cosets of the centralizer on geometric points. -/
theorem borelQuotientFixedPoints_conditional :
    TorusFreeUnipotent.MaximalTorusCentralizer.{u} →
    TorusFreeUnipotent.Unipotence.{u} → BorelQuotientFixedPoints.{u} := by
  classical
  intro maximalCentralizer _ k _ _ G hG hconn T B hT hB hTB N hN P
  letI : Smooth G.val.X.hom := hG
  letI : ConnectedSpace G.val.X.left := hconn
  obtain ⟨C, hC, _, _, _, hCinc, _⟩ := maximalCentralizer G hG hconn T hT
  have hCB := hCinc B hB hTB
  obtain ⟨a, ha, hfix, htrans⟩ := borelFixedPointOrbit G T B hT hB hTB N hN P
  refine ⟨a, ha, ?_, hfix, borelNormalizerCosets hT hB hTB hN hC hCB P, htrans⟩
  obtain ⟨j, hj, Q, q, he, hq⟩ := quotientOfRepresentingSubgroups hN hC
  letI : IsFinite Q.val.X.hom := (quotientByCentralizer_finiteEtale q hT.1 hN hC j he hj hq.1).1
  letI := finite_rationalSections Q.val.X
  let W := {x : 𝟙_ (SchemeOver k) ⟶ P.scheme | IsFixedPoint a T x}
  let chooseN (x : W) := ((hfix x.val).mp x.property).choose
  have chooseN_spec (x : W) : chooseN x ≫ N.inclusion.hom.hom ≫ P.projection = x.val :=
    ((hfix x.val).mp x.property).choose_spec
  suffices h : Finite W by exact @Set.toFinite _ _ h
  apply Finite.of_injective (fun x : W ↦ chooseN x ≫ q.hom.hom)
  intro x y hxy
  let I : ClosedSubgroup N.group := ⟨C.group, j, hj⟩
  haveI : IsClosedImmersion ((𝟙 Q.val : Q.val ⟶ Q.val).hom.hom.left) :=
    inferInstanceAs (IsClosedImmersion (𝟙 Q.val.X.left))
  have hmem := (sameImage_iff (p := q) (i := 𝟙 Q.val) (Category.comp_id q)
    (N := I) hq.1.1 (chooseN y) (chooseN x)).mp hxy.symm
  change ∃ c : 𝟙_ (SchemeOver k) ⟶ C.group.X, c ≫ j.hom.hom = (chooseN y)⁻¹ * chooseN x at hmem
  obtain ⟨c, hc⟩ := hmem
  have hh : ((chooseN y)⁻¹ * chooseN x) ≫ N.inclusion.hom.hom = c ≫ C.inclusion.hom.hom := by
    rw [← hc, Category.assoc]
    exact congrArg (fun f : C.group ⟶ G.val ↦ c ≫ f.hom.hom) he
  have hcent := (hC _ _).mpr ⟨c, hh.symm⟩
  apply Subtype.ext
  rw [← chooseN_spec x, ← chooseN_spec y]
  exact (borelNormalizerCosets hT hB hTB hN hC hCB P _ _).mpr hcent

/-- Over a connected test algebra the conjugation of a diagonalizable group
acts on its character values by one homomorphism of its character group. -/
private theorem conjugationCharacterHom {G : GroupScheme k} {M : Type u} [CommGroup M]
    {A : TestAlgebra k} [Nontrivial A] [ConnectedSpace (PrimeSpectrum A)]
    (i : specGroup (groupAlgebra k M) ⟶ G) [Mono i.hom.hom] (g : Points G.X A)
    (c : (specGroup (groupAlgebra k M)).X ⊗ (testSpec k).obj (op A) ⟶
      (specGroup (groupAlgebra k M)).X)
    (hc : c ≫ i.hom.hom = conjugateFamily i g) :
    ∃ δ : M →* M, ∀ (U : TestAlgebra k) (a : A ⟶ U)
      (t : Points (specGroup (groupAlgebra k M)).X U),
      diagonalPointEquiv M U (conjugationOnPoints i g c hc a t) =
        (diagonalPointEquiv M U t).comp δ := by
  let B := CommAlgCat.of k (MonoidAlgebra A M)
  let a₀ : A ⟶ B := CommAlgCat.ofHom (IsScalarTower.toAlgHom k A B)
  let t₀ := (diagonalPointEquiv M B).symm (MonoidAlgebra.of A M).toHomUnits
  let s := conjugationOnPoints i g c hc a₀ t₀
  let χ := diagonalPointEquiv M B s
  have hm (m : M) : ∃ n : M, (χ m).val = MonoidAlgebra.of A M n :=
    groupLike_monomial_of_connected (conjugatedMonomials_groupLike i g c hc m)
  choose δ hδ using hm
  let φ : M →* M :=
    { toFun := δ
      map_one' := by
        apply MonoidAlgebra.of_injective (R := A)
        rw [← hδ, map_one, map_one]
        rfl
      map_mul' := by
        intro x y
        apply MonoidAlgebra.of_injective (R := A)
        rw [← hδ, map_mul (MonoidAlgebra.of A M), ← hδ, ← hδ, map_mul]
        rfl }
  refine ⟨φ, ?_⟩
  intro U a t
  obtain ⟨b, hb, ht⟩ := groupAlgebra_eval a t
  change a₀ ≫ b = a at hb
  change pointMap b t₀ = t at ht
  rw [← hb, ← ht, ← conjugationOnPoints_natural,
    diagonalPointEquiv_natural, diagonalPointEquiv_natural, MulEquiv.apply_symm_apply]
  apply MonoidHom.ext
  intro m
  apply Units.ext
  change b.hom (χ m).val = b.hom (MonoidAlgebra.of A M (δ m))
  exact congrArg b.hom (hδ m)

/-- A normalizing family of a split diagonalizable group on a connected affine
base gives a single lattice automorphism on that base. -/
theorem normalizingCharacterAutomorphism {G : GroupScheme k} {M : Type u} [CommGroup M]
    {A : TestAlgebra k} [Nontrivial A] [ConnectedSpace (PrimeSpectrum A)]
    (i : specGroup (groupAlgebra k M) ⟶ G)
    (hi : IsClosedImmersion i.hom.hom.left) (g : Points G.X A) (hn : Normalizes i g) :
    ∃ δ : M ≃* M,
      ∀ (R : TestAlgebra k) (a : A ⟶ R) (t : Points (specGroup (groupAlgebra k M)).X R),
        let t' := (diagonalPointEquiv M R).symm ((diagonalPointEquiv M R t).comp δ.toMonoidHom)
        t' ≫ i.hom.hom = pointMap a g * (t ≫ i.hom.hom) * (pointMap a g)⁻¹ := by
  let : Mono i.hom.hom := mono_over _ hi
  obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := (normalizesIff k i hi _ g).mp hn
  obtain ⟨δ, hδ⟩ := conjugationCharacterHom i g c hc
  obtain ⟨ε, hε⟩ := conjugationCharacterHom i g⁻¹ d hd
  let B := CommAlgCat.of k (MonoidAlgebra A M)
  let a : A ⟶ B := CommAlgCat.ofHom (IsScalarTower.toAlgHom k A B)
  let t := (diagonalPointEquiv M B).symm (MonoidAlgebra.of A M).toHomUnits
  let F := conjugationOnPoints i g c hc a
  let H := conjugationOnPoints i g⁻¹ d hd a
  have hf (v : Points (specGroup (groupAlgebra k M)).X B) : F (H v) = v := by
    apply (cancel_mono i.hom.hom).mp
    change conjugationOnPoints i g c hc a (H v) ≫ i.hom.hom = _
    rw [conjugationOnPoints_eq]
    change pointMap a g * (conjugationOnPoints i g⁻¹ d hd a v ≫ i.hom.hom) *
      (pointMap a g)⁻¹ = _
    rw [conjugationOnPoints_eq]
    change pointMap a g *
        (((testSpec k).map a.op ≫ g⁻¹) * (v ≫ i.hom.hom) * ((testSpec k).map a.op ≫ g⁻¹)⁻¹) *
      (pointMap a g)⁻¹ = _
    rw [GrpObj.comp_inv]
    change pointMap a g * ((pointMap a g)⁻¹ * (v ≫ i.hom.hom) * ((pointMap a g)⁻¹)⁻¹) *
      (pointMap a g)⁻¹ = _
    group
  have hh (v : Points (specGroup (groupAlgebra k M)).X B) : H (F v) = v := by
    apply (cancel_mono i.hom.hom).mp
    change conjugationOnPoints i g⁻¹ d hd a (F v) ≫ i.hom.hom = _
    rw [conjugationOnPoints_eq]
    change ((testSpec k).map a.op ≫ g⁻¹) *
      (conjugationOnPoints i g c hc a v ≫ i.hom.hom) * ((testSpec k).map a.op ≫ g⁻¹)⁻¹ = _
    rw [conjugationOnPoints_eq, GrpObj.comp_inv]
    change (pointMap a g)⁻¹ * (pointMap a g * (v ≫ i.hom.hom) * (pointMap a g)⁻¹) *
      ((pointMap a g)⁻¹)⁻¹ = _
    group
  have hδε (m : M) : ε (δ m) = m := by
    have he := congrArg (diagonalPointEquiv M B) (hf t)
    change diagonalPointEquiv M B (conjugationOnPoints i g c hc a (conjugationOnPoints i g⁻¹ d hd a t)) =
      diagonalPointEquiv M B t at he
    rw [hδ, hε, MulEquiv.apply_symm_apply] at he
    apply MonoidAlgebra.of_injective (R := A)
    exact congrArg (fun s : M →* Bˣ ↦ (s m).val) he
  have hεδ (m : M) : δ (ε m) = m := by
    have he := congrArg (diagonalPointEquiv M B) (hh t)
    change diagonalPointEquiv M B (conjugationOnPoints i g⁻¹ d hd a (conjugationOnPoints i g c hc a t)) =
      diagonalPointEquiv M B t at he
    rw [hε, hδ, MulEquiv.apply_symm_apply] at he
    apply MonoidAlgebra.of_injective (R := A)
    exact congrArg (fun s : M →* Bˣ ↦ (s m).val) he
  let e : M ≃* M := { toFun := δ, invFun := ε, left_inv := hδε, right_inv := hεδ, map_mul' := map_mul δ }
  refine ⟨e, ?_⟩
  intro R b v
  dsimp only
  have h := hδ R b v
  change diagonalPointEquiv M R (conjugationOnPoints i g c hc b v) =
    (diagonalPointEquiv M R v).comp e.toMonoidHom at h
  rw [← h, MulEquiv.symm_apply_apply, conjugationOnPoints_eq]

/-- The automorphisms preserving a finite generating set form a finite type. -/
theorem finite_weightPreservingAutomorphisms {M : Type u} [Group M] (s : Set M) (hs : s.Finite)
    (hgen : Subgroup.closure s = ⊤) :
    Finite {a : MulAut M // Set.MapsTo (a : M → M) s s} := by
  classical
  letI : Fintype s := hs.fintype
  letI : Fintype (s → s) := inferInstance
  let restrict (a : {a : MulAut M // Set.MapsTo (a : M → M) s s}) (x : s) : s :=
    ⟨a.val x.val, a.property x.property⟩
  apply Finite.of_injective restrict
  intro a b h
  apply Subtype.ext
  apply MulEquiv.ext
  intro m
  have hclosure : m ∈ Subgroup.closure s := hgen.symm ▸ Subgroup.mem_top m
  induction hclosure using Subgroup.closure_induction with
  | mem x hx =>
    exact congrArg (fun r : s → s ↦ (r ⟨x, hx⟩).val) h
  | one => simp
  | mul x y hx hy ihx ihy => simp only [map_mul, ihx, ihy]
  | inv x hx ih => simp only [map_inv, ih]

open Specs.CharacterDescent (Character)
open Specs.DiagonalizableGroups (groupAlgebraMap IntegerCharacters)
open WithConv
open private specGroupMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private pointsIso_precompose from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private isAffine_product_left from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.FixedPointSchemes
open private exists_field_point from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus

open private charactersTo charactersTo_evaluation charactersTo_natural integerPointsIso pointsIso_spec
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private hom_ext_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes

private def standardMultiplicativePoints (k : Type u) [Field k] :
    (groupPointsFunctor k).obj (specGroup (groupAlgebra k IntegerCharacters)) ≅
      StandardGroups.multiplicativePoints k :=
  groupAlgebraPointsIso k IntegerCharacters ≪≫ integerPointsIso

private abbrev multiplicativeGroupAlgebra (k : Type u) [Field k] : AffineAlgebraicGroup k := by
  let e : Multiplicative ℤ ≃* IntegerCharacters.{u} := MulEquiv.ulift.symm
  letI : Group.FG IntegerCharacters.{u} := Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
  exact diagonalGroup k IntegerCharacters


private theorem splitCharacter_evaluation {M : Type u} [CommGroup M] {S : GroupScheme k}
    (b : specGroup (groupAlgebra k M) ≅ S) (x : M) (R : TestAlgebra k) (t : Points S.X R) :
    (standardMultiplicativePoints k).hom.app R
      (t ≫ (b.inv ≫ charactersTo (multiplicativeGroupAlgebra k)
        (standardMultiplicativePoints k) M x).hom.hom) =
      diagonalPointEquiv M R (t ≫ b.inv.hom.hom) x := by
  change (standardMultiplicativePoints k).hom.app R
    (t ≫ b.inv.hom.hom ≫ (charactersTo (multiplicativeGroupAlgebra k)
      (standardMultiplicativePoints k) M x).hom.hom) = _
  rw [← Category.assoc]
  exact charactersTo_evaluation (multiplicativeGroupAlgebra k)
    (standardMultiplicativePoints k) x R (t ≫ b.inv.hom.hom)

private def splitCharacter {M : Type u} [CommGroup M] {S : GroupScheme k}
    (b : specGroup (groupAlgebra k M) ≅ S) : M ≃* Character S where
  toFun x := b.inv ≫ charactersTo (multiplicativeGroupAlgebra k) (standardMultiplicativePoints k) M x
  invFun χ := (charactersTo (multiplicativeGroupAlgebra k)
    (standardMultiplicativePoints k) M).symm (b.hom ≫ χ)
  left_inv x := by simp
  right_inv χ := by
    let c := charactersTo (multiplicativeGroupAlgebra k) (standardMultiplicativePoints k) M
    change b.inv ≫ c (c.symm (b.hom ≫ χ)) = χ
    rw [c.apply_symm_apply, Iso.inv_hom_id_assoc]
  map_mul' x y := by
    let a (z : M) : Character S :=
      b.inv ≫ charactersTo (multiplicativeGroupAlgebra k) (standardMultiplicativePoints k) M z
    change a (x * y) = a x * a y
    apply Grp.hom_ext
    let e := (Over.forget (Spec (CommRingCat.of k))).mapIso ((Grp.forget (SchemeOver k)).mapIso b)
    have hS : IsAffine S.X.left :=
      @IsAffine.of_isIso _ _ e.inv inferInstance
        (by exact inferInstanceAs (IsAffine (Spec (CommRingCat.of (MonoidAlgebra k M)))))
    apply hom_ext_of_points hS
    intro R t
    apply (ConcreteCategory.bijective_of_isIso ((standardMultiplicativePoints k).hom.app R)).1
    have h : (a x * a y).hom.hom = (a x).hom.hom * (a y).hom.hom := rfl
    rw [h, MonObj.comp_mul]
    change (standardMultiplicativePoints k).hom.app R (t ≫ (a (x * y)).hom.hom) =
      (standardMultiplicativePoints k).hom.app R
        ((t ≫ (a x).hom.hom) * (t ≫ (a y).hom.hom))
    rw [map_mul]
    have he (z : M) := splitCharacter_evaluation b z R t
    change (standardMultiplicativePoints k).hom.app R (t ≫ (a (x * y)).hom.hom) = _
    rw [he, he, he, map_mul]

private theorem splitCharacter_eval {M : Type u} [CommGroup M] {S : GroupScheme k}
    (b : specGroup (groupAlgebra k M) ≅ S) (x : M) (R : TestAlgebra k) (t : Points S.X R) :
    (standardMultiplicativePoints k).hom.app R (t ≫ (splitCharacter b x).hom.hom) =
      diagonalPointEquiv M R (t ≫ b.inv.hom.hom) x :=
  splitCharacter_evaluation b x R t

section WeightBasis

open LinearAlgebraicGroups.RationalRepresentations
open private tensorCoordinate_tmul from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations

variable {I : Type u} [Fintype I] [DecidableEq I]

private def coordinateChange {V : Type u} [AddCommGroup V] [Module k V]
    (b d : Module.Basis I k V) : Matrix.GeneralLinearGroup I k :=
  Matrix.GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (d.equivFun.symm.trans b.equivFun))

private theorem coordinateChange_entry {V : Type u} [AddCommGroup V] [Module k V]
    (b d : Module.Basis I k V) (i j : I) :
    (coordinateChange b d).val i j = b.coord i (d j) := by
  have h := Matrix.GeneralLinearGroup.toLin.apply_symm_apply
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (d.equivFun.symm.trans b.equivFun))
  have e := congrArg (fun g : LinearMap.GeneralLinearGroup k (I → k) ↦ g.val (Pi.single j 1) i) h
  change (((coordinateChange b d).val *ᵥ Pi.single j 1) i) =
    b.equivFun (d.equivFun.symm (Pi.single j 1)) i at e
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at e
  rw [show d.equivFun.symm (Pi.single j 1) = d j by
    apply d.equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    ext l
    simp [Module.Basis.equivFun_self, Pi.single_apply, eq_comm]] at e
  exact e

private def scalarMatrix (P : Matrix.GeneralLinearGroup I k) (R : TestAlgebra k) :
    Matrix.GeneralLinearGroup I R :=
  Matrix.GeneralLinearGroup.map (algebraMap k R) P

private def rebaseMatrixPoints (P : Matrix.GeneralLinearGroup I k) :
    StandardGroups.generalLinearPoints k I ≅ StandardGroups.generalLinearPoints k I := by
  refine NatIso.ofComponents (fun R ↦ (MulAut.conj (scalarMatrix P R)⁻¹).toGrpIso) ?_
  intro R S a
  apply GrpCat.ext
  intro g
  let g' : Matrix.GeneralLinearGroup I R := g
  change (scalarMatrix P S)⁻¹ * Matrix.GeneralLinearGroup.map a.hom.toRingHom g' * scalarMatrix P S =
    Matrix.GeneralLinearGroup.map a.hom.toRingHom ((scalarMatrix P R)⁻¹ * g' * scalarMatrix P R)
  have h : Matrix.GeneralLinearGroup.map a.hom.toRingHom (scalarMatrix P R) = scalarMatrix P S := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    exact a.hom.commutes _
  rw [map_mul, map_mul, map_inv, h]

/-- The basis change matrix intertwines the original coaction matrix with the
diagonal coaction matrix of a basis of weight vectors. -/
private theorem diagonal_coactionMatrix {M : Type u} [CommGroup M]
    {V : Type u} [AddCommGroup V] [Module k V] (b d : Module.Basis I k V)
    (ρ : RightComodule k (groupAlgebra k M) V) (w : I → M)
    (hw : ∀ j, d j ∈ WeightDecomposition.weightSpace ρ (w j)) :
    let P := scalarMatrix (coordinateChange b d) (CommAlgCat.of k (MonoidAlgebra k M))
    coefficients (groupAlgebra k M) b ρ * P.val =
      P.val * Matrix.diagonal (fun j ↦ MonoidAlgebra.of k M (w j)) := by
  intro P
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have hP (i j : I) : P.val i j = algebraMap k (MonoidAlgebra k M) (b.coord i (d j)) := by
    change algebraMap k (MonoidAlgebra k M) ((coordinateChange b d).val i j) = _
    rw [coordinateChange_entry]
  simp only [hP]
  let c := (tensorCoordinate b i).comp ρ.coaction
  have h := congrArg c (b.sum_repr (d j))
  change c (∑ l, b.repr (d j) l • b l) = c (d j) at h
  simp only [map_sum, map_smul] at h
  calc
    (∑ l, coefficients (groupAlgebra k M) b ρ i l *
        algebraMap k (MonoidAlgebra k M) (b.coord l (d j))) =
        ∑ l, b.repr (d j) l • c (b l) := by
      apply Finset.sum_congr rfl
      intro l _
      change _ = _ • coefficients (groupAlgebra k M) b ρ i l
      rw [Algebra.smul_def, mul_comm]
      rfl
    _ = c (d j) := h
    _ = _ := by
      change tensorCoordinate b i (ρ.coaction (d j)) = _
      rw [WeightDecomposition.mem_weightSpace.mp (hw j), tensorCoordinate_tmul, Algebra.smul_def]

private abbrev splitAffineGroup (M : Type u) [CommGroup M] : AffineGroupCategory k :=
  ⟨specGroup (groupAlgebra k M), inferInstanceAs
    (IsAffine (Spec (CommRingCat.of (MonoidAlgebra k M))))⟩

private abbrev universalDiagonalPoint (M : Type u) [CommGroup M] :
    Points ((splitAffineGroup (k := k) M).val.X) (CommAlgCat.of k (MonoidAlgebra k M)) :=
  (hopfSpecPointIso (groupAlgebra k M)).hom.app _ (toConv (AlgHom.id k _))

open private pointMatrix pointMatrix_evaluation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations

private theorem diagonal_onPoints_of_universal {M : Type u} [CommGroup M]
    {L : GroupScheme k}
    (e : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k I)
    (r : (splitAffineGroup (k := k) M).val ⟶ L) (w : I → M)
    (hu : let B := CommAlgCat.of k (MonoidAlgebra k M)
          let t₀ := universalDiagonalPoint (k := k) M
          (e.hom.app B (t₀ ≫ r.hom.hom) : Matrix.GeneralLinearGroup I B).val =
            Matrix.diagonal (fun j ↦ (diagonalPointEquiv M B t₀ (w j)).val))
    (R : TestAlgebra k) (t : Points (splitAffineGroup (k := k) M).val.X R) :
    (e.hom.app R (t ≫ r.hom.hom) : Matrix.GeneralLinearGroup I R).val =
      Matrix.diagonal (fun j ↦ (diagonalPointEquiv M R t (w j)).val) := by
  let A := groupAlgebra k M
  let hP := hopfSpecPointIso A
  let B := CommAlgCat.of k (MonoidAlgebra k M)
  let t₀ := universalDiagonalPoint (k := k) M
  let α := hP.hom ≫ (groupPointsFunctor k).map r ≫ e.hom
  obtain ⟨g, rfl⟩ := (ConcreteCategory.bijective_of_isIso (hP.hom.app R)).2 t
  change (α.app R g : Matrix.GeneralLinearGroup I R).val = _
  rw [pointMatrix_evaluation A α R g]
  change pointMatrix A α = Matrix.diagonal
    (fun j ↦ (diagonalPointEquiv M B t₀ (w j)).val) at hu
  rw [hu]
  apply Matrix.ext
  intro i j
  change g.ofConv (Matrix.diagonal (fun l ↦ (diagonalPointEquiv M B t₀ (w l)).val) i j) =
    Matrix.diagonal (fun l ↦ (diagonalPointEquiv M R (hP.hom.app R g) (w l)).val) i j
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    have h₁ := pointsIso_spec M B (AlgHom.id k (MonoidAlgebra k M)) (w i)
    have h₂ := pointsIso_spec M R g.ofConv (w i)
    change (diagonalPointEquiv M B t₀ (w i)).val = MonoidAlgebra.of k M (w i) at h₁
    change (diagonalPointEquiv M R (hP.hom.app R g) (w i)).val =
      g.ofConv (MonoidAlgebra.of k M (w i)) at h₂
    rw [h₁, h₂]
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij, map_zero]

private theorem rebase_diagonal_onPoints {M : Type u} [CommGroup M]
    {V : Type u} [AddCommGroup V] [Module k V] (b d : Module.Basis I k V)
    {L : GroupScheme k}
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k I)
    (r : (splitAffineGroup (k := k) M).val ⟶ L)
    (ρ : RightComodule k (groupAlgebra k M) V)
    (hρ : coefficients (groupAlgebra k M) b ρ =
      universalMatrix (groupAlgebra k M) (splitAffineGroup M) L
        (hopfSpecPointIso (groupAlgebra k M)) l r)
    (w : I → M) (hw : ∀ j, d j ∈ WeightDecomposition.weightSpace ρ (w j)) :
    let e := l ≪≫ rebaseMatrixPoints (coordinateChange b d)
    ∀ (R : TestAlgebra k) (t : Points (splitAffineGroup (k := k) M).val.X R),
      (e.hom.app R (t ≫ r.hom.hom) : Matrix.GeneralLinearGroup I R).val =
        Matrix.diagonal (fun j ↦ (diagonalPointEquiv M R t (w j)).val) := by
  let B := CommAlgCat.of k (MonoidAlgebra k M)
  let t₀ := universalDiagonalPoint (k := k) M
  let P := scalarMatrix (coordinateChange b d) B
  intro e
  apply diagonal_onPoints_of_universal e r w
  change (e.hom.app B (t₀ ≫ r.hom.hom) : Matrix.GeneralLinearGroup I B).val =
    Matrix.diagonal (fun j ↦ (diagonalPointEquiv M B t₀ (w j)).val)
  have ht (x : M) : (diagonalPointEquiv M B t₀ x).val = MonoidAlgebra.of k M x :=
    pointsIso_spec M B (AlgHom.id k (MonoidAlgebra k M)) x
  have h := diagonal_coactionMatrix b d ρ w hw
  change coefficients (groupAlgebra k M) b ρ * P.val =
    P.val * Matrix.diagonal (fun j ↦ MonoidAlgebra.of k M (w j)) at h
  rw [show (fun j ↦ (diagonalPointEquiv M B t₀ (w j)).val) = _ from
    funext (fun j ↦ ht (w j))]
  change (P⁻¹).val * universalMatrix (groupAlgebra k M) (splitAffineGroup M) L
    (hopfSpecPointIso (groupAlgebra k M)) l r * P.val = _
  rw [mul_assoc, ← hρ, h, ← mul_assoc, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.GeneralLinearGroup.coe_one, one_mul]

private theorem diagonalize_splitRepresentation {M : Type u} [CommGroup M]
    {L : GroupScheme k}
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k I)
    (r : (splitAffineGroup (k := k) M).val ⟶ L) :
    ∃ (e : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k I) (w : I → M),
      ∀ (R : TestAlgebra k) (t : Points (splitAffineGroup (k := k) M).val.X R),
        (e.hom.app R (t ≫ r.hom.hom) : Matrix.GeneralLinearGroup I R).val =
          Matrix.diagonal (fun j ↦ (diagonalPointEquiv M R t (w j)).val) := by
  classical
  let A := groupAlgebra k M
  let b : Module.Basis I k (I → k) := Pi.basisFun k I
  obtain ⟨E, hE⟩ := representationCoactionComparison A b (splitAffineGroup M) L (hopfSpecPointIso A) l
  let ρ := E r
  letI : FiniteDimensional k (I → k) := b.finiteDimensional_of_finite
  obtain ⟨J, _, d, w, hw⟩ := DiagonalizableFixedLocus.existsWeightBasis ρ
  letI := Fintype.ofFinite J
  have hcard : Fintype.card J = Fintype.card I :=
    (Module.finrank_eq_card_basis d).symm.trans (Module.finrank_eq_card_basis b)
  let jI : J ≃ I := Fintype.equivOfCardEq hcard
  let d' := d.reindex jI
  let w' : I → M := w ∘ jI.symm
  have hw' (j : I) : d' j ∈ WeightDecomposition.weightSpace ρ (w' j) := by
    simpa only [d', w', Function.comp_apply, Module.Basis.reindex_apply] using hw (jI.symm j)
  exact ⟨l ≪≫ rebaseMatrixPoints (coordinateChange b d'), w',
    rebase_diagonal_onPoints b d' l r ρ (hE r) w' hw'⟩

private theorem splitWeightBasis {M : Type u} [CommGroup M]
    (G : AffineAlgebraicGroup k) {S : GroupScheme k}
    (bS : specGroup (groupAlgebra k M) ≅ S) (i : S ⟶ G.val) :
    ∃ (n : ℕ) (L : AffineAlgebraicGroup k)
      (e : (groupPointsFunctor k).obj L.val ≅
        StandardGroups.generalLinearPoints k (ULift.{u} (Fin n)))
      (f : G.val ⟶ L.val) (w : ULift.{u} (Fin n) → M),
    IsClosedImmersion f.hom.hom.left ∧
    ∀ (R : TestAlgebra k) (t : Points S.X R),
      (e.hom.app R (t ≫ (i ≫ f).hom.hom) : Matrix.GeneralLinearGroup _ R).val =
        Matrix.diagonal (fun j ↦ (diagonalPointEquiv M R (t ≫ bS.inv.hom.hom) (w j)).val) := by
  obtain ⟨n, L, ⟨l⟩, f, hf⟩ := faithfulLinearization k G
  let r : (splitAffineGroup M).val ⟶ L.val := bS.hom ≫ i ≫ f
  obtain ⟨e, w, hdiag⟩ := diagonalize_splitRepresentation l r
  refine ⟨n, L, e, f, w, hf, fun R t ↦ ?_⟩
  have h := hdiag R (t ≫ bS.inv.hom.hom)
  have hb : bS.inv.hom.hom ≫ bS.hom.hom.hom = 𝟙 S.X :=
    (Grp.forget _).congr_map bS.inv_hom_id
  change (e.hom.app R ((t ≫ bS.inv.hom.hom) ≫ bS.hom.hom.hom ≫ (i ≫ f).hom.hom) :
    Matrix.GeneralLinearGroup _ R).val = _ at h
  have heq : (t ≫ bS.inv.hom.hom) ≫ bS.hom.hom.hom = t := by
    rw [Category.assoc, hb, Category.comp_id]
  rw [← Category.assoc (t ≫ bS.inv.hom.hom), heq] at h
  exact h

end WeightBasis

private theorem faithfulWeights_of_splitWeightBasis {M : Type u} [CommGroup M]
    {G S : GroupScheme k} (b : specGroup (groupAlgebra k M) ≅ S) (i : S ⟶ G)
    (hi : IsClosedImmersion i.hom.hom.left) {n : ℕ} (L : AffineAlgebraicGroup k)
    (e : (groupPointsFunctor k).obj L.val ≅
      StandardGroups.generalLinearPoints k (ULift.{u} (Fin n)))
    (f : G ⟶ L.val) (w : ULift.{u} (Fin n) → M)
    (hf : IsClosedImmersion f.hom.hom.left)
    (hd : ∀ (R : TestAlgebra k) (t : Points S.X R),
      (e.hom.app R (t ≫ (i ≫ f).hom.hom) : Matrix.GeneralLinearGroup _ R).val =
        Matrix.diagonal (fun j ↦ (diagonalPointEquiv M R (t ≫ b.inv.hom.hom) (w j)).val)) :
    FaithfulWeights i (Set.range (splitCharacter b ∘ w)) := by
  classical
  let χ := splitCharacter b ∘ w
  refine ⟨n, L, e, standardMultiplicativePoints k, f, χ, hf, rfl, ?_, ?_⟩
  · let H := Subgroup.closure (Set.range w)
    let R := CommAlgCat.of k (MonoidAlgebra k (M ⧸ H))
    let ψ := (MonoidAlgebra.of k (M ⧸ H)).toHomUnits.comp (QuotientGroup.mk' H)
    let t := (diagonalPointEquiv M R).symm ψ
    let s : Points S.X R := t ≫ b.hom.hom.hom
    have hs : s ≫ b.inv.hom.hom = t := by
      have hb : b.hom.hom.hom ≫ b.inv.hom.hom = 𝟙 (specGroup (groupAlgebra k M)).X :=
        (Grp.forget _).congr_map b.hom_inv_id
      rw [Category.assoc, hb, Category.comp_id]
    have hψ (j : ULift.{u} (Fin n)) : ψ (w j) = 1 := by
      change (MonoidAlgebra.of k (M ⧸ H)).toHomUnits (QuotientGroup.mk' H (w j)) = 1
      have hwj : w j ∈ H := Subgroup.subset_closure ⟨j, rfl⟩
      rw [show QuotientGroup.mk' H (w j) = 1 from (QuotientGroup.eq_one_iff (w j)).mpr hwj, map_one]
    have hm : e.hom.app R (s ≫ (i ≫ f).hom.hom) = 1 := by
      apply Units.ext
      rw [hd, hs, MulEquiv.apply_symm_apply]
      change Matrix.diagonal (fun j ↦ (ψ (w j)).val) = (1 : Matrix _ _ R)
      simp_rw [hψ, Units.val_one, Matrix.diagonal_one]
    have hs1 : s = 1 := by
      have hmono : Mono (i ≫ f).hom.hom := by
        letI := mono_over i.hom.hom hi
        letI := mono_over f.hom.hom hf
        exact mono_comp i.hom.hom f.hom.hom
      apply (cancel_mono (i ≫ f).hom.hom).mp
      apply (ConcreteCategory.bijective_of_isIso (e.hom.app R)).1
      simpa only [MonObj.one_comp, map_one] using hm
    have hψ1 : ψ = 1 := by
      calc
        ψ = diagonalPointEquiv M R (s ≫ b.inv.hom.hom) :=
          (congrArg (diagonalPointEquiv M R) hs).trans
            (MulEquiv.apply_symm_apply (diagonalPointEquiv M R) ψ) |>.symm
        _ = 1 := by rw [hs1, MonObj.one_comp, map_one]
    have hH : H = ⊤ := by
      apply top_unique
      intro x _
      apply (QuotientGroup.eq_one_iff (N := H) x).mp
      apply MonoidAlgebra.of_injective (R := k)
      have hx := congrArg (fun z : M →* Rˣ ↦ (z x).val) hψ1
      change MonoidAlgebra.of k (M ⧸ H) (QuotientGroup.mk' H x) = 1 at hx
      exact hx
    let c := (splitCharacter b).toMonoidHom
    rw [show Set.range χ = c '' Set.range w from Set.range_comp ..,
      ← MonoidHom.map_closure c (Set.range w)]
    change H.map c = ⊤
    rw [hH, Subgroup.map_top_of_surjective _ (splitCharacter b).surjective]
  · intro R t
    rw [hd]
    congr 1
    funext j
    exact congrArg Units.val (splitCharacter_eval b (w j) R t).symm

private def splitTorusAutomorphism {M : Type u} [CommGroup M] (δ : M ≃* M) :
    specGroup (groupAlgebra k M) ≅ specGroup (groupAlgebra k M) := by
  have invId (ε : M ≃* M) : groupAlgebraMap k ε.symm.toMonoidHom ≫
      groupAlgebraMap k ε.toMonoidHom = 𝟙 (groupAlgebra k M) := by
    apply CommHopfAlgCat.hom_ext
    change (MonoidAlgebra.mapDomainBialgHom k ε.toMonoidHom).comp
      (MonoidAlgebra.mapDomainBialgHom k ε.symm.toMonoidHom) = BialgHom.id k _
    rw [← MonoidAlgebra.mapDomainBialgHom_comp, show
      ε.toMonoidHom.comp ε.symm.toMonoidHom = MonoidHom.id M from
        MonoidHom.ext ε.apply_symm_apply]
    exact MonoidAlgebra.mapDomainBialgHom_id
  refine ⟨specGroupMap (groupAlgebraMap k δ.toMonoidHom),
    specGroupMap (groupAlgebraMap k δ.symm.toMonoidHom), ?_, ?_⟩
  · rw [← specGroupMap_comp, invId δ]
    exact (hopfSpec (CommRingCat.of k)).map_id _
  · have h : groupAlgebraMap k δ.toMonoidHom ≫ groupAlgebraMap k δ.symm.toMonoidHom =
        𝟙 (groupAlgebra k M) := by
      simpa only [MulEquiv.symm_symm] using invId δ.symm
    rw [← specGroupMap_comp, h]
    exact (hopfSpec (CommRingCat.of k)).map_id _

private def splitConjugation {M : Type u} [CommGroup M] {S : GroupScheme k}
    (b : specGroup (groupAlgebra k M) ≅ S) (δ : M ≃* M) : S ≅ S :=
  b.symm ≪≫ splitTorusAutomorphism δ ≪≫ b

/-- Conjugation on a connected affine parameter scheme is induced by a single
automorphism of the split torus over the field. -/
private theorem exists_splitConjugation {M : Type u} [CommGroup M] {G S : GroupScheme k}
    {Y : SchemeOver k} (ha : IsAffine Y.left) (hconn : ConnectedSpace Y.left)
    (b : specGroup (groupAlgebra k M) ≅ S) (i : S ⟶ G)
    (hi : IsClosedImmersion i.hom.hom.left) (g : Y ⟶ G.X) (hg : Normalizes i g) :
    ∃ δ : M ≃* M,
      conjugateFamily i g = fst S.X Y ≫ ((splitConjugation b δ).hom ≫ i).hom.hom := by
  obtain ⟨A, ⟨e⟩⟩ := essImage_algSpec.mpr ha
  let D := specGroup (groupAlgebra k M)
  let F := Grp.forget (SchemeOver k)
  let b₀ := F.mapIso b
  let e₀ := (Over.forget (Spec (CommRingCat.of k))).mapIso e
  letI : ConnectedSpace (PrimeSpectrum A.unop) := e₀.hom.homeomorph.connectedSpace_iff.mpr hconn
  letI : Nontrivial A.unop := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  let j : D ⟶ G := b.hom ≫ i
  let h : Points G.X A.unop := e.hom ≫ g
  have hj : IsClosedImmersion j.hom.hom.left := by
    letI := hi
    change IsClosedImmersion (b₀.hom.left ≫ i.hom.hom.left)
    infer_instance
  have transport (x : Y ⟶ G.X) (y : Points G.X A.unop) (he : e.hom ≫ x = y)
      (hx : ConjugateLe i x) : ConjugateLe j y := by
    apply (conjugateLe_iff j y).mpr
    intro U u t
    obtain ⟨a, hal⟩ := (conjugateLe_iff i x).mp hx U (u ≫ e.hom) (t ≫ b₀.hom)
    refine ⟨a ≫ b₀.inv, ?_⟩
    change (a ≫ b₀.inv) ≫ b₀.hom ≫ i.hom.hom =
      (u ≫ y) * ((t ≫ b₀.hom) ≫ i.hom.hom) * (u ≫ y)⁻¹
    rw [Category.assoc a, b₀.inv_hom_id_assoc]
    simpa only [Category.assoc, he] using hal
  have hn := (normalizesIff k i hi _ g).mp hg
  have hn' : Normalizes j h :=
    (normalizesIff k j hj _ h).mpr
      ⟨transport g h rfl hn.1, transport g⁻¹ h⁻¹ (GrpObj.comp_inv _ _) hn.2⟩
  obtain ⟨δ, hδ⟩ := normalizingCharacterAutomorphism j hj h hn'
  refine ⟨δ, ?_⟩
  letI : IsAffine D.X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of (MonoidAlgebra k M))))
  letI : IsAffine S.X.left :=
    @IsAffine.of_isIso _ _ ((Over.forget _).mapIso b₀).inv inferInstance
      (by exact inferInstanceAs (IsAffine (Spec (CommRingCat.of (MonoidAlgebra k M)))))
  letI : IsAffine Y.left := ha
  apply hom_ext_of_points isAffine_product_left
  intro R p
  let u := p ≫ snd S.X Y
  let t := (p ≫ fst S.X Y) ≫ b₀.inv
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let a : A.unop ⟶ R := (ff.preimage (u ≫ e.inv)).unop
  have ha' : (testSpec k).map a.op ≫ e.hom = u := by
    change (testSpec k).map (ff.preimage (u ≫ e.inv)) ≫ e.hom = u
    rw [ff.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hact : (diagonalPointEquiv M R).symm ((diagonalPointEquiv M R t).comp δ.toMonoidHom) =
      t ≫ (splitTorusAutomorphism (k := k) δ).hom.hom.hom := by
    apply (diagonalPointEquiv M R).injective
    rw [MulEquiv.apply_symm_apply]
    apply MonoidHom.ext
    intro m
    exact (pointsIso_precompose δ.toMonoidHom R t m).symm
  have he := hδ R a t
  rw [hact] at he
  change (t ≫ (splitTorusAutomorphism (k := k) δ).hom.hom.hom) ≫ b₀.hom ≫ i.hom.hom =
    (((testSpec k).map a.op ≫ e.hom) ≫ g) * ((t ≫ b₀.hom) ≫ i.hom.hom) *
      (((testSpec k).map a.op ≫ e.hom) ≫ g)⁻¹ at he
  rw [ha', show t ≫ b₀.hom = p ≫ fst S.X Y by simp [t]] at he
  rw [comp_conjugateFamily]
  change _ = (p ≫ fst S.X Y) ≫ b₀.inv ≫
    (splitTorusAutomorphism (k := k) δ).hom.hom.hom ≫ b₀.hom ≫ i.hom.hom
  simpa only [t, u, Category.assoc] using he.symm

private theorem splitConjugation_on_quotientFibres {M : Type u} [CommGroup M]
    {G : AffineAlgebraicGroup k} {S N : ClosedSubgroup G.val} {Q : GroupScheme k}
    (b : specGroup (groupAlgebra k M) ≅ S.group) (q : N.group ⟶ Q)
    (hN : RepresentsSubgroup N (fun _ g ↦ Normalizes S.inclusion g))
    [DiscreteTopology Q.X.left] [GeometricallyConnected q.hom.hom.left] :
    ∃ δ : Q.X.left → (M ≃* M),
      ∀ (Y : SchemeOver k) (n : Y ⟶ N.group.X) (x : Q.X.left),
        (∀ y : Y.left, (n ≫ q.hom.hom).left y = x) →
          conjugateFamily S.inclusion (n ≫ N.inclusion.hom.hom) =
            fst S.group.X Y ≫ ((splitConjugation b (δ x)).hom ≫ S.inclusion).hom.hom := by
  classical
  have h (x : Q.X.left) : ∃ δ : M ≃* M,
      ∀ (Y : SchemeOver k) (n : Y ⟶ N.group.X),
        (∀ y : Y.left, (n ≫ q.hom.hom).left y = x) →
          conjugateFamily S.inclusion (n ≫ N.inclusion.hom.hom) =
            fst S.group.X Y ≫ ((splitConjugation b δ).hom ≫ S.inclusion).hom.hom := by
    let f := q.hom.hom.left
    let U : N.group.X.left.Opens :=
      ⟨f ⁻¹' {x}, (isOpen_discrete {x}).preimage f.continuous⟩
    let V : SchemeOver k := Over.mk (U.ι ≫ N.group.X.hom)
    let v : V ⟶ N.group.X := Over.homMk U.ι
    haveI : IsAffine N.group.X.left := (closedSubgroupAlgebraicGroup N).property.1
    have ha : IsAffine V.left := isAffineOpen_of_isClopen U
      ((isClopen_discrete {x}).preimage f.continuous)
    have hc : ConnectedSpace V.left :=
      isConnected_iff_connectedSpace.mp (f.isConnected_preimage_singleton x)
    have hn := (hN _ _).mpr ⟨v, rfl⟩
    obtain ⟨δ, he⟩ := exists_splitConjugation ha hc b S.inclusion S.isClosedImmersion _ hn
    refine ⟨δ, ?_⟩
    intro Y n hnx
    have hsub : Set.range n.left ⊆ Set.range U.ι := by
      rw [U.range_ι]
      rintro _ ⟨y, rfl⟩
      exact hnx y
    let a := IsOpenImmersion.lift U.ι n.left hsub
    have ha' : a ≫ U.ι = n.left := IsOpenImmersion.lift_fac _ _ _
    let l : Y ⟶ V := Over.homMk a (by
      change a ≫ U.ι ≫ N.group.X.hom = Y.hom
      rw [← Category.assoc, ha', Over.w n])
    have hl : l ≫ v = n := Over.OverMorphism.ext ha'
    let p := lift (fst S.group.X Y) (snd S.group.X Y ≫ l)
    have hp := congrArg (fun z ↦ p ≫ z) he
    change p ≫ conjugateFamily S.inclusion (v ≫ N.inclusion.hom.hom) = _ at hp
    rw [comp_conjugateFamily] at hp
    simpa only [Category.assoc, lift_fst_assoc, lift_snd_assoc, p, reassoc_of% hl,
      conjugateFamily] using hp
  choose δ hδ using h
  exact ⟨δ, fun Y n x ↦ hδ x Y n⟩

/-- Two families lift simultaneously after a single faithfully flat cover. -/
private theorem commonQuotientLift {N Q Y : SchemeOver k} (q : N ⟶ Q)
    [Flat q.left] [Surjective q.left] (x y : Y ⟶ Q) :
    ∃ (V : SchemeOver k) (p : V ⟶ Y) (n m : V ⟶ N),
      Flat p.left ∧ Surjective p.left ∧ n ≫ q = p ≫ x ∧ m ≫ q = p ≫ y := by
  let A := pullback q x
  let B := pullback q y
  let a : A ⟶ Y := pullback.snd q x
  let b : B ⟶ Y := pullback.snd q y
  let U := Over.forget (Spec (CommRingCat.of k))
  have ha := (IsPullback.of_hasPullback q x).map U
  have hb := (IsPullback.of_hasPullback q y).map U
  haveI : Flat a.left := MorphismProperty.of_isPullback ha ‹Flat q.left›
  haveI : Surjective a.left := MorphismProperty.of_isPullback ha ‹Surjective q.left›
  haveI : Flat b.left := MorphismProperty.of_isPullback hb ‹Flat q.left›
  haveI : Surjective b.left := MorphismProperty.of_isPullback hb ‹Surjective q.left›
  let V := pullback a b
  let f : V ⟶ A := pullback.fst a b
  let g : V ⟶ B := pullback.snd a b
  let p := f ≫ a
  have hp := (IsPullback.of_hasPullback a b).map U
  haveI : Flat f.left := MorphismProperty.of_isPullback hp.flip ‹Flat b.left›
  haveI : Surjective f.left := MorphismProperty.of_isPullback hp.flip ‹Surjective b.left›
  refine ⟨V, p, f ≫ pullback.fst q x, g ≫ pullback.fst q y, ?_, ?_, ?_, ?_⟩
  · exact inferInstanceAs (Flat (f.left ≫ a.left))
  · exact inferInstanceAs (Surjective (f.left ≫ a.left))
  · simp [p, a, pullback.condition]
  · simp only [p, f, g, a, b, Category.assoc, pullback.condition]

private theorem quotient_eq_of_conjugateFamily_eq {G : AffineAlgebraicGroup k}
    {S N C : ClosedSubgroup G.val} {Q : GroupScheme k} (q : N.group ⟶ Q)
    (hC : RepresentsSubgroup C (fun _ g ↦ Centralizes S.inclusion g))
    (j : C.group ⟶ N.group) (hj : j ≫ N.inclusion = C.inclusion)
    (hjc : IsClosedImmersion j.hom.hom.left)
    (hker : IsSchemeKernel q (⟨C.group, j, hjc⟩ : ClosedSubgroup N.group))
    {Y : SchemeOver k} (n m : Y ⟶ N.group.X)
    (h : conjugateFamily S.inclusion (n ≫ N.inclusion.hom.hom) =
      conjugateFamily S.inclusion (m ≫ N.inclusion.hom.hom)) :
    n ≫ q.hom.hom = m ≫ q.hom.hom := by
  let v := N.inclusion.hom.hom
  have hc : Centralizes S.inclusion ((n⁻¹ * m) ≫ v) := by
    apply (centralizes_iff S.inclusion _).mpr
    intro U u t
    have h' := congrArg (fun z ↦ lift t u ≫ z) h
    simp only [comp_conjugateFamily, lift_snd_assoc, lift_fst_assoc] at h'
    let a := u ≫ n ≫ v
    let b := u ≫ m ≫ v
    let s := t ≫ S.inclusion.hom.hom
    change a * s * a⁻¹ = b * s * b⁻¹ at h'
    haveI : IsMonHom v := inferInstanceAs (IsMonHom N.inclusion.hom.hom)
    have hv : u ≫ (n⁻¹ * m) ≫ v = a⁻¹ * b := by
      rw [← Category.assoc u, MonObj.comp_mul, MonObj.mul_comp, GrpObj.comp_inv,
        GrpObj.inv_comp, Category.assoc, Category.assoc]
    rw [hv]
    change Commute (a⁻¹ * b) s
    calc
      a⁻¹ * b * s = a⁻¹ * (b * s * b⁻¹) * b := by group
      _ = a⁻¹ * (a * s * a⁻¹) * b := by rw [h']
      _ = s * (a⁻¹ * b) := by group
  obtain ⟨c, he⟩ := (hC _ _).mp hc
  haveI : Mono v := mono_over _ N.isClosedImmersion
  have hc' : c ≫ j.hom.hom = n⁻¹ * m := by
    apply (cancel_mono v).mp
    exact (congrArg (fun z : C.group ⟶ G.val ↦ c ≫ z.hom.hom) hj).trans he
  haveI : IsClosedImmersion ((𝟙 Q : Q ⟶ Q).hom.hom.left) :=
    inferInstanceAs (IsClosedImmersion (𝟙 Q.X.left))
  exact (sameImage_iff (p := q) (i := 𝟙 Q) (Category.comp_id q) hker n m).mpr ⟨c, hc'⟩

private theorem apply_conjugateFamily_eq {G S : GroupScheme k}
    (i : S ⟶ G) {Y U : SchemeOver k} (g : Y ⟶ G.X) (α : S ≅ S)
    (h : conjugateFamily i g = fst S.X Y ≫ (α.hom ≫ i).hom.hom)
    (y : U ⟶ Y) (s : U ⟶ S.X) :
    s ≫ (α.hom ≫ i).hom.hom = (y ≫ g) * (s ≫ i.hom.hom) * (y ≫ g)⁻¹ := by
  have h' := congrArg (fun z ↦ lift s y ≫ z) h
  simpa only [comp_conjugateFamily, Category.assoc, lift_fst_assoc, lift_snd_assoc] using h'.symm

private theorem conjugation_comp {G S : GroupScheme k} (i : S ⟶ G)
    (hi : IsClosedImmersion i.hom.hom.left) {Y : SchemeOver k} [Flat Y.hom] [Surjective Y.hom]
    (g₁ g₂ : Y ⟶ G.X) (α₁ α₂ α₁₂ : S ≅ S)
    (h₁ : conjugateFamily i g₁ = fst S.X Y ≫ (α₁.hom ≫ i).hom.hom)
    (h₂ : conjugateFamily i g₂ = fst S.X Y ≫ (α₂.hom ≫ i).hom.hom)
    (h₁₂ : conjugateFamily i (g₁ * g₂) = fst S.X Y ≫ (α₁₂.hom ≫ i).hom.hom) :
    α₁₂ = α₂ ≪≫ α₁ := by
  apply Iso.ext
  apply Grp.hom_ext
  letI : Mono i.hom.hom := mono_over i.hom.hom hi
  apply (cancel_mono i.hom.hom).mp
  have hp := Over.isPullback_of_binaryFan_isLimit _ (tensorProductIsBinaryProduct S.X Y)
  let x := fst S.X Y
  let y := snd S.X Y
  letI : Flat x.left := MorphismProperty.of_isPullback hp.flip ‹Flat Y.hom›
  letI : Surjective x.left := MorphismProperty.of_isPullback hp.flip ‹Surjective Y.hom›
  letI : Epi x.left := Flat.epi_of_flat_of_surjective _
  letI : Epi x := Over.epi_of_epi_left _
  apply (cancel_epi x).mp
  have e₁ := apply_conjugateFamily_eq i g₁ α₁ h₁ y (x ≫ α₂.hom.hom.hom)
  have e₂ := apply_conjugateFamily_eq i g₂ α₂ h₂ y x
  have e₁₂ := apply_conjugateFamily_eq i (g₁ * g₂) α₁₂ h₁₂ y x
  let a := y ≫ g₁
  let b := y ≫ g₂
  let s := x ≫ i.hom.hom
  have h₁' : x ≫ α₂.hom.hom.hom ≫ α₁.hom.hom.hom ≫ i.hom.hom =
      a * (x ≫ α₂.hom.hom.hom ≫ i.hom.hom) * a⁻¹ := by
    change (x ≫ α₂.hom.hom.hom) ≫ α₁.hom.hom.hom ≫ i.hom.hom =
      a * ((x ≫ α₂.hom.hom.hom) ≫ i.hom.hom) * a⁻¹ at e₁
    simpa only [Category.assoc] using e₁
  have h₂' : x ≫ α₂.hom.hom.hom ≫ i.hom.hom = b * s * b⁻¹ := e₂
  have h₁₂' : x ≫ α₁₂.hom.hom.hom ≫ i.hom.hom = (a * b) * s * (a * b)⁻¹ := by
    rw [MonObj.comp_mul] at e₁₂
    exact e₁₂
  change x ≫ α₁₂.hom.hom.hom ≫ i.hom.hom =
    x ≫ (α₂.hom.hom.hom ≫ α₁.hom.hom.hom) ≫ i.hom.hom
  rw [Category.assoc α₂.hom.hom.hom, h₁', h₂', h₁₂']
  group

private def inverseCharacterPullback {S : GroupScheme k} (α : S ≅ S) :
    MulAut (Character S) where
  toFun χ := α.inv ≫ χ
  invFun χ := α.hom ≫ χ
  left_inv χ := α.hom_inv_id_assoc χ
  right_inv χ := α.inv_hom_id_assoc χ
  map_mul' χ ψ := by
    apply Grp.hom_ext
    change α.inv.hom.hom ≫ ((χ * ψ).hom.hom) =
      (α.inv ≫ χ).hom.hom * (α.inv ≫ ψ).hom.hom
    change α.inv.hom.hom ≫ (χ.hom.hom * ψ.hom.hom) =
      (α.inv.hom.hom ≫ χ.hom.hom) * (α.inv.hom.hom ≫ ψ.hom.hom)
    exact MonObj.comp_mul _ _ _

private theorem inverseCharacterPullback_trans {S : GroupScheme k} (α β : S ≅ S) :
    inverseCharacterPullback (β ≪≫ α) = inverseCharacterPullback α * inverseCharacterPullback β := by
  apply MulEquiv.ext
  intro χ
  change (α.inv ≫ β.inv) ≫ χ = α.inv ≫ β.inv ≫ χ
  exact Category.assoc _ _ _

private abbrev RationalSections (X : SchemeOver k) :=
  𝟙_ (SchemeOver k) ⟶ X

private def sectionValue {X : SchemeOver k} (s : RationalSections X) : X.left :=
  s.left (IsLocalRing.closedPoint k)

private theorem constantSection_value {X Y : SchemeOver k} (s : RationalSections X) (y : Y.left) :
    (toUnit Y ≫ s).left y = sectionValue s := by
  change s.left ((toUnit Y).left y) = s.left (IsLocalRing.closedPoint k)
  congr 1
  exact Subsingleton.elim (α := Spec (CommRingCat.of k)) _ _

private theorem pointSections_of_etale (X : SchemeOver k) [DiscreteTopology X.left] [Etale X.hom]
    (h : ∀ (Y : SchemeOver k) (a b : Y ⟶ X) (x : X.left),
      (∀ y : Y.left, a.left y = x) → (∀ y : Y.left, b.left y = x) → a = b) :
    Function.Bijective (sectionValue (X := X)) := by
  refine ⟨?_, ?_⟩
  · intro a b hab
    apply h _ a b (sectionValue a)
    · intro y
      rw [Subsingleton.elim (α := Spec (CommRingCat.of k)) y (IsLocalRing.closedPoint k)]
      rfl
    · intro y
      rw [hab, Subsingleton.elim (α := Spec (CommRingCat.of k)) y (IsLocalRing.closedPoint k)]
      rfl
  · intro x
    let U : X.left.Opens := ⟨{x}, isOpen_discrete _⟩
    let p : (U : Scheme) ⟶ Spec (CommRingCat.of k) := U.ι ≫ X.hom
    letI : Etale p := inferInstanceAs (Etale (U.ι ≫ X.hom))
    haveI : Mono p := by
      constructor
      intro Z f g hfg
      let Y : SchemeOver k := Over.mk (f ≫ p)
      have h₁ : (f ≫ U.ι) ≫ X.hom = Y.hom := Category.assoc .. 
      have h₂ : (g ≫ U.ι) ≫ X.hom = Y.hom := (Category.assoc ..).trans hfg.symm
      let a : Y ⟶ X := Over.homMk (f ≫ U.ι) h₁
      let b : Y ⟶ X := Over.homMk (g ≫ U.ι) h₂
      have ha (z : Y.left) : a.left z = x := (f z).property
      have hb (z : Y.left) : b.left z = x := (g z).property
      exact (cancel_mono U.ι).mp (congrArg (fun m : Y ⟶ X ↦ m.left) (h Y a b x ha hb))
    haveI : Surjective p :=
      ⟨fun y ↦ ⟨⟨x, rfl⟩, Subsingleton.elim _ _⟩⟩
    letI : IsOpenImmersion p := IsOpenImmersion.of_flat_of_mono p
    letI : IsIso p := isIso_of_isOpenImmersion_of_opensRange_eq_top p
      (SetLike.coe_injective (Set.range_eq_univ.mpr p.surjective))
    let s : RationalSections X := Over.homMk (inv p ≫ U.ι) (by
      change (inv p ≫ U.ι) ≫ X.hom = 𝟙 _
      rw [Category.assoc, ← show p = U.ι ≫ X.hom from rfl, IsIso.inv_hom_id])
    exact ⟨s, (inv p (IsLocalRing.closedPoint k)).property⟩

private theorem constantGroupOfPointSections (Q : GroupScheme k)
    [DiscreteTopology Q.X.left]
    (huniq : ∀ (Y : SchemeOver k) (a b : Y ⟶ Q.X) (x : Q.X.left),
      (∀ y : Y.left, a.left y = x) → (∀ y : Y.left, b.left y = x) → a = b)
    (hpoints : Function.Bijective (sectionValue (X := Q.X))) :
    ∃ P : ConstantGroup Q (RationalSections Q.X), P.sectionPoint = MonoidHom.id _ := by
  classical
  let v := Equiv.ofBijective (sectionValue (X := Q.X)) hpoints
  let F (Y : SchemeOver k) (f : Y ⟶ Q.X) : LocallyConstant Y.left (RationalSections Q.X) :=
    ⟨v.symm ∘ f.left, (IsLocallyConstant.of_discrete _).comp_continuous f.left.continuous⟩
  have hinj (Y : SchemeOver k) : Function.Injective (F Y) := by
    intro a b hab
    have h (y : Y.left) : a.left y = b.left y :=
      v.symm.injective (congrArg (fun l : LocallyConstant Y.left (RationalSections Q.X) ↦ l y) hab)
    apply Over.OverMorphism.ext
    apply Scheme.hom_ext_of_forall
    intro y
    let U : Y.left.Opens := ⟨a.left ⁻¹' {a.left y}, (isOpen_discrete _).preimage a.left.continuous⟩
    let Z : SchemeOver k := Over.mk (U.ι ≫ Y.hom)
    let f : Z ⟶ Y := Over.homMk U.ι
    refine ⟨U, rfl, ?_⟩
    exact congrArg (fun m : Z ⟶ Q.X ↦ m.left) <|
      huniq Z (f ≫ a) (f ≫ b) (a.left y)
        (fun z ↦ z.property) (fun z ↦ (h z.val).symm.trans z.property)
  have hsurj (Y : SchemeOver k) : Function.Surjective (F Y) := by
    intro c
    let W := RationalSections Q.X
    let U (w : W) : Y.left.Opens := ⟨{y | c y = w}, c.isLocallyConstant.isOpen_fiber w⟩
    let P : Y.left.OpenCover := {
      I₀ := W
      X w := U w
      f w := (U w).ι
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun y ↦ ⟨c y, ⟨⟨y, rfl⟩, rfl⟩⟩, fun w ↦ inferInstance⟩ }
    let a (w : W) : P.X w ⟶ Q.X.left := P.f w ≫ Y.hom ≫ w.left
    have ha (i j : W) :
        pullback.fst (P.f i) (P.f j) ≫ a i = pullback.snd (P.f i) (P.f j) ≫ a j := by
      by_cases hij : i = j
      · subst j
        simp only [a, pullback.condition_assoc]
      · letI : IsEmpty ↥(pullback (P.f i) (P.f j) : Scheme) := ⟨fun z ↦ by
          let l := pullback.fst (P.f i) (P.f j) z
          let r := pullback.snd (P.f i) (P.f j) z
          have he : (P.f i) l = (P.f j) r := by
            change (P.f i) (pullback.fst (P.f i) (P.f j) z) =
              (P.f j) (pullback.snd (P.f i) (P.f j) z)
            rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
          have hl : c ((P.f i) l) = i := l.property
          have hr : c ((P.f j) r) = j := r.property
          exact hij (hl.symm.trans ((congrArg c he).trans hr))⟩
        exact isInitialOfIsEmpty.hom_ext _ _
    let g := P.glueMorphisms a ha
    have hg : g ≫ Q.X.hom = Y.hom := by
      apply P.hom_ext
      intro i
      rw [← Category.assoc, P.ι_glueMorphisms]
      change (P.f i ≫ Y.hom ≫ i.left) ≫ Q.X.hom = _
      rw [Category.assoc, Category.assoc, Over.w i]
      change P.f i ≫ Y.hom ≫ 𝟙 _ = P.f i ≫ Y.hom
      rw [Category.comp_id]
    let f : Y ⟶ Q.X := Over.homMk g hg
    refine ⟨f, ?_⟩
    apply LocallyConstant.ext
    intro y
    apply v.injective
    change v (v.symm (g y)) = sectionValue (c y)
    rw [Equiv.apply_symm_apply]
    have e := congrArg (fun z : P.X (c y) ⟶ Q.X.left ↦ z ⟨y, rfl⟩)
      (P.ι_glueMorphisms a ha (c y))
    change g y = (c y).left (Y.hom y) at e
    exact e.trans (congrArg (c y).left
      (Subsingleton.elim (α := Spec (CommRingCat.of k)) _ _))
  have hmul (Y : SchemeOver k) (f g : Y ⟶ Q.X) : F Y (f * g) = F Y f * F Y g := by
    apply LocallyConstant.ext
    intro y
    let P := Y.left.fromSpecResidueField y
    let Z : SchemeOver k := Over.mk (P ≫ Y.hom)
    let p : Z ⟶ Y := Over.homMk P
    let z₀ : Z.left := IsLocalRing.closedPoint (Y.left.residueField y)
    have hz : p.left z₀ = y := Y.left.fromSpecResidueField_apply y z₀
    have hc (a : Y ⟶ Q.X) :
        p ≫ a = toUnit Z ≫ v.symm (a.left y) := by
      apply huniq Z _ _ (a.left y)
      · intro z
        rw [Subsingleton.elim (α := Spec (Y.left.residueField y)) z z₀]
        change a.left (p.left z₀) = _
        rw [hz]
      · intro z
        exact (constantSection_value _ z).trans (v.apply_symm_apply _)
    have he : p ≫ (f * g) = toUnit Z ≫ (v.symm (f.left y) * v.symm (g.left y)) := by
      rw [MonObj.comp_mul, hc f, hc g, MonObj.comp_mul]
    have h0 := congrArg (fun a : Z ⟶ Q.X ↦ a.left z₀) he
    change (f * g).left (p.left z₀) =
      (toUnit Z ≫ (v.symm (f.left y) * v.symm (g.left y))).left z₀ at h0
    rw [hz, constantSection_value] at h0
    change v.symm ((f * g).left y) = v.symm (f.left y) * v.symm (g.left y)
    change (f * g).left y = v (v.symm (f.left y) * v.symm (g.left y)) at h0
    exact (congrArg v.symm h0).trans (v.symm_apply_apply _)
  refine ⟨⟨MonoidHom.id _, fun Y ↦ { Equiv.ofBijective (F Y) ⟨hinj Y, hsurj Y⟩ with
    map_mul' := hmul Y }, ?_, ?_⟩, rfl⟩
  · intro X Y f g
    rfl
  · intro Y s
    apply LocallyConstant.ext
    intro y
    change v.symm ((toUnit Y ≫ s).left y) = s
    rw [constantSection_value]
    exact v.symm_apply_apply _

private def relabelConstantGroup {Q : GroupScheme k} {W W' : Type u} [Group W] [Group W']
    (P : ConstantGroup Q W) (e : W' ≃* W) : ConstantGroup Q W' where
  sectionPoint := P.sectionPoint.comp e.toMonoidHom
  families Y := (P.families Y).trans
    { toFun := LocallyConstant.map e.symm
      invFun := LocallyConstant.map e
      left_inv f := by apply LocallyConstant.ext; intro y; exact e.apply_symm_apply (f y)
      right_inv f := by apply LocallyConstant.ext; intro y; exact e.symm_apply_apply (f y)
      map_mul' f g := by apply LocallyConstant.ext; intro y; exact map_mul e.symm (f y) (g y) }
  naturality f y := by
    apply LocallyConstant.ext
    intro x
    change e.symm (P.families _ (f ≫ y) x) = e.symm (P.families _ y (f.left x))
    rw [P.naturality]
    rfl
  constant Y w := by
    apply LocallyConstant.ext
    intro x
    change e.symm (P.families _ (toUnit Y ≫ P.sectionPoint (e w)) x) = w
    rw [P.constant]
    exact e.symm_apply_apply _

private theorem splitConjugation_character {M : Type u} [CommGroup M] {S : GroupScheme k}
    (b : specGroup (groupAlgebra k M) ≅ S) (δ : M ≃* M) (x : M) :
    (splitConjugation b δ).inv ≫ splitCharacter b x = splitCharacter b (δ.symm x) := by
  let c := charactersTo (multiplicativeGroupAlgebra k) (standardMultiplicativePoints k) M
  change (b.inv ≫ specGroupMap (groupAlgebraMap k δ.symm.toMonoidHom) ≫ b.hom) ≫
    b.inv ≫ c x = b.inv ≫ c (δ.symm x)
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [charactersTo_natural]
  rfl

/-- An invertible intertwiner has a nonzero entry in each column. With a
character basis this entry identifies the original weight with the twisted
weight in its row. -/
private theorem splitConjugation_permutesWeights {M : Type u} [CommGroup M]
    {G S : GroupScheme k} (b : specGroup (groupAlgebra k M) ≅ S) (i : S ⟶ G)
    {n : ℕ} (L : AffineAlgebraicGroup k)
    (e : (groupPointsFunctor k).obj L.val ≅
      StandardGroups.generalLinearPoints k (ULift.{u} (Fin n)))
    (f : G ⟶ L.val) (w : ULift.{u} (Fin n) → M)
    (hd : ∀ (R : TestAlgebra k) (t : Points S.X R),
      (e.hom.app R (t ≫ (i ≫ f).hom.hom) : Matrix.GeneralLinearGroup _ R).val =
        Matrix.diagonal (fun j ↦ (diagonalPointEquiv M R (t ≫ b.inv.hom.hom) (w j)).val))
    {Y : SchemeOver k} [Nonempty Y.left] (g : Y ⟶ G.X) (δ : M ≃* M)
    (hg : conjugateFamily i g = fst S.X Y ≫ ((splitConjugation b δ).hom ≫ i).hom.hom) :
    Set.MapsTo (δ.symm : M → M) (Set.range w) (Set.range w) := by
  classical
  obtain ⟨K, _, _, p, _⟩ := exists_field_point Y (Classical.choice ‹Nonempty Y.left›)
  let I := ULift.{u} (Fin n)
  let A := CommAlgCat.of k K
  let R := CommAlgCat.of k (MonoidAlgebra K M)
  let a : A ⟶ R := CommAlgCat.ofHom (IsScalarTower.toAlgHom k K (MonoidAlgebra K M))
  let t := (diagonalPointEquiv M R).symm (MonoidAlgebra.of K M).toHomUnits
  let b₀ := (Grp.forget (SchemeOver k)).mapIso b
  let s : Points S.X R := t ≫ b₀.hom
  let s' : Points S.X R := s ≫ (splitConjugation b δ).hom.hom.hom
  have hs : s ≫ b₀.inv = t := by simp [s]
  have hs' : s' ≫ b₀.inv = t ≫ (splitTorusAutomorphism (k := k) δ).hom.hom.hom := by
    change (t ≫ b₀.hom ≫ b₀.inv ≫
      (splitTorusAutomorphism (k := k) δ).hom.hom.hom ≫ b₀.hom) ≫ b₀.inv = _
    simp [Category.assoc]
  have hval (x : M) : (diagonalPointEquiv M R (s' ≫ b₀.inv) x).val =
      MonoidAlgebra.of K M (δ x) := by
    rw [hs']
    have h := pointsIso_precompose δ.toMonoidHom R t x
    change diagonalPointEquiv M R (t ≫ (splitTorusAutomorphism (k := k) δ).hom.hom.hom) x =
      diagonalPointEquiv M R t (δ x) at h
    rw [h, show diagonalPointEquiv M R t = (MonoidAlgebra.of K M).toHomUnits from
      MulEquiv.apply_symm_apply _ _]
    rfl
  let ρ := (groupPointsFunctor k).map f ≫ e.hom
  let r : Points G.X A := p ≫ g
  let P₀ : Matrix.GeneralLinearGroup I K := ρ.app A r
  let P : Matrix.GeneralLinearGroup I R := ρ.app R (mapPoints a r)
  have hP (i j : I) : P.val i j = algebraMap K R (P₀.val i j) := by
    have h := ConcreteCategory.congr_hom (ρ.naturality a)
      (show ((groupPointsFunctor k).obj G).obj A from r)
    exact congrArg (fun Z : Matrix.GeneralLinearGroup I R ↦ Z.val i j) h
  have hconj := apply_conjugateFamily_eq i g (splitConjugation b δ) hg (mapPoints a p) s
  change s' ≫ i.hom.hom = mapPoints a r * (s ≫ i.hom.hom) * (mapPoints a r)⁻¹ at hconj
  let F : Points G.X R →* Matrix.GeneralLinearGroup I R := (ρ.app R).hom
  have hQ : F (s' ≫ i.hom.hom) * P = P * F (s ≫ i.hom.hom) := by
    rw [hconj, map_mul, map_mul, map_inv]
    change (P * F (s ≫ i.hom.hom) * P⁻¹) * P = _
    group
  have hmatrix :
      Matrix.diagonal (fun l : I ↦ MonoidAlgebra.of K M (δ (w l))) * P.val =
        P.val * Matrix.diagonal (fun l : I ↦ MonoidAlgebra.of K M (w l)) := by
    have H := congrArg (fun Z : Matrix.GeneralLinearGroup I R ↦ Z.val) hQ
    change (e.hom.app R (s' ≫ (i ≫ f).hom.hom) : Matrix.GeneralLinearGroup I R).val * P.val =
      P.val * (e.hom.app R (s ≫ (i ≫ f).hom.hom) : Matrix.GeneralLinearGroup I R).val at H
    rw [hd, hd] at H
    change Matrix.diagonal (fun l : I ↦ (diagonalPointEquiv M R (s' ≫ b₀.inv) (w l)).val) * P.val =
      P.val * Matrix.diagonal (fun l : I ↦ (diagonalPointEquiv M R (s ≫ b₀.inv) (w l)).val) at H
    simp_rw [hval, hs, show diagonalPointEquiv M R t = (MonoidAlgebra.of K M).toHomUnits from
      MulEquiv.apply_symm_apply _ _] at H
    exact H
  rintro _ ⟨j, rfl⟩
  have hcol : ∃ l : I, P₀.val l j ≠ 0 := by
    by_contra! h
    have hz := congrArg (fun Z : Matrix.GeneralLinearGroup I K ↦ Z.val j j) (inv_mul_cancel P₀)
    change ((P₀⁻¹).val * P₀.val) j j = (1 : Matrix I I K) j j at hz
    simp [Matrix.mul_apply, h] at hz
  obtain ⟨l, hl⟩ := hcol
  have hunit : IsUnit (P.val l j) := by
    rw [hP]
    exact (isUnit_iff_ne_zero.mpr hl).map (algebraMap K R)
  have H := congrArg (fun Z : Matrix I I R ↦ Z l j) hmatrix
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at H
  have he : MonoidAlgebra.of K M (δ (w l)) = MonoidAlgebra.of K M (w j) := by
    apply hunit.mul_left_cancel
    rwa [mul_comm (P.val l j)]
  refine ⟨l, ?_⟩
  have hx := (MonoidAlgebra.of_injective (R := K)) he
  exact δ.injective (hx.trans (δ.apply_symm_apply (w j)).symm)

private theorem splitImage_of_lattice {M : Type u} [CommGroup M]
    {G : AffineAlgebraicGroup k} {S N C : ClosedSubgroup G.val}
    {Q : AffineAlgebraicGroup k} (q : N.group ⟶ Q.val)
    (b : specGroup (groupAlgebra k M) ≅ S.group)
    {n : ℕ} (L : AffineAlgebraicGroup k)
    (l : (groupPointsFunctor k).obj L.val ≅
      StandardGroups.generalLinearPoints k (ULift.{u} (Fin n)))
    (f : G.val ⟶ L.val) (wts : ULift.{u} (Fin n) → M)
    (hf : IsClosedImmersion f.hom.hom.left)
    (hd : ∀ (R : TestAlgebra k) (t : Points S.group.X R),
      (l.hom.app R (t ≫ (S.inclusion ≫ f).hom.hom) : Matrix.GeneralLinearGroup _ R).val =
        Matrix.diagonal (fun a ↦ (diagonalPointEquiv M R (t ≫ b.inv.hom.hom) (wts a)).val))
    (hN : RepresentsSubgroup N (fun _ g ↦ Normalizes S.inclusion g))
    (hC : RepresentsSubgroup C (fun _ g ↦ Centralizes S.inclusion g))
    (j : C.group ⟶ N.group) (hj : j ≫ N.inclusion = C.inclusion)
    (hjc : IsClosedImmersion j.hom.hom.left)
    (hQ : IsFppfGroupQuotient (G := closedSubgroupAlgebraicGroup N) (Q := Q) ⟨_, j, hjc⟩ q)
    [Etale Q.val.X.hom] [GeometricallyConnected q.hom.hom.left] :
    Nonempty (SplitImage S.inclusion N.inclusion q) := by
  classical
  letI : DiscreteTopology Q.val.X.left := discreteTopologyOfEtaleOverField Q.val.X.hom
  letI : IsAffine Q.val.X.left := Q.property.1
  letI : Flat q.hom.hom.left := hQ.2.1
  letI : Surjective q.hom.hom.left := hQ.2.2.1
  obtain ⟨δ, hδ⟩ := splitConjugation_on_quotientFibres b q hN
  let W := RationalSections Q.val.X
  let α (w : W) := splitConjugation b (δ (sectionValue w))
  have hconj (w : W) {Y : SchemeOver k} (n : Y ⟶ N.group.X)
      (hn : n ≫ q.hom.hom = toUnit Y ≫ w) :
      conjugateFamily S.inclusion (n ≫ N.inclusion.hom.hom) =
        fst S.group.X Y ≫ ((α w).hom ≫ S.inclusion).hom.hom :=
    hδ Y n _ (fun y ↦ hn.symm ▸ constantSection_value w y)
  have descend (Y : SchemeOver k) (x y : Y ⟶ Q.val.X)
      (h : ∀ (V : SchemeOver k) (p : V ⟶ Y) (n m : V ⟶ N.group.X),
        n ≫ q.hom.hom = p ≫ x → m ≫ q.hom.hom = p ≫ y →
        conjugateFamily S.inclusion (n ≫ N.inclusion.hom.hom) =
          conjugateFamily S.inclusion (m ≫ N.inclusion.hom.hom)) : x = y := by
    obtain ⟨V, p, n, m, hf, hs, hn, hm⟩ := commonQuotientLift q.hom.hom x y
    letI : Flat p.left := hf
    letI : Surjective p.left := hs
    letI : Epi p.left := Flat.epi_of_flat_of_surjective p.left
    letI : Epi p := Over.epi_of_epi_left p
    apply (cancel_epi p).mp
    rw [← hn, ← hm]
    exact quotient_eq_of_conjugateFamily_eq q hC j hj hjc hQ.1 n m (h V p n m hn hm)
  have huniq (Y : SchemeOver k) (x y : Y ⟶ Q.val.X) (z : Q.val.X.left)
      (hx : ∀ v : Y.left, x.left v = z) (hy : ∀ v : Y.left, y.left v = z) : x = y := by
    apply descend Y x y
    intro V p n m hn hm
    have h₁ (v : V.left) : (n ≫ q.hom.hom).left v = z := hn.symm ▸ hx (p.left v)
    have h₂ (v : V.left) : (m ≫ q.hom.hom).left v = z := hm.symm ▸ hy (p.left v)
    exact (hδ V n z h₁).trans (hδ V m z h₂).symm
  have hb := pointSections_of_etale Q.val.X huniq
  obtain ⟨P, hP⟩ := constantGroupOfPointSections Q.val huniq hb
  have hmul (x y : W) : α (x * y) = α y ≪≫ α x := by
    obtain ⟨V, p, n, m, hf, hs, hn, hm⟩ := commonQuotientLift q.hom.hom x y
    have hp : p = toUnit V := toUnit_unique p (toUnit V)
    have hv : V.hom = p.left := by
      have ee := Over.w p
      change p.left ≫ 𝟙 _ = V.hom at ee
      simpa using ee.symm
    letI : Flat V.hom := hv.symm ▸ hf
    letI : Surjective V.hom := hv.symm ▸ hs
    have e₁ := hconj x n (hp ▸ hn)
    have e₂ := hconj y m (hp ▸ hm)
    have hn' : (n * m) ≫ q.hom.hom = toUnit V ≫ (x * y) := by
      rw [MonObj.mul_comp, MonObj.comp_mul, hn, hm, hp]
    have e₁₂ := hconj (x * y) (n * m) hn'
    rw [MonObj.mul_comp] at e₁₂
    exact conjugation_comp S.inclusion S.isClosedImmersion _ _ _ _ _ e₁ e₂ e₁₂
  let ψ : W →* MulAut (Character S.group) := MonoidHom.mk'
    (fun w ↦ inverseCharacterPullback (α w)) (fun x y ↦ by
      rw [hmul, inverseCharacterPullback_trans])
  have hinj : Function.Injective ψ := by
    intro x y he
    have he' (m : M) : (δ (sectionValue x)).symm m = (δ (sectionValue y)).symm m := by
      apply (splitCharacter b).injective
      rw [← splitConjugation_character, ← splitConjugation_character]
      exact congrArg (fun r : MulAut (Character S.group) ↦ r (splitCharacter b m)) he
    have hD : δ (sectionValue x) = δ (sectionValue y) :=
      congrArg MulEquiv.symm (MulEquiv.ext he')
    have ha : α x = α y := congrArg (splitConjugation b) hD
    apply descend _ x y
    intro V p n m hn hm
    have hp : p = toUnit V := toUnit_unique p (toUnit V)
    rw [hconj x n (hp ▸ hn), hconj y m (hp ▸ hm), ha]
  let e := MonoidHom.ofInjective hinj
  let CP := relabelConstantGroup P e.symm
  have hsection (w : ψ.range) : CP.sectionPoint w = e.symm w := by
    change P.sectionPoint (e.symm w) = _
    rw [hP]
    rfl
  haveI : Finite Q.val.X.left := finite_of_compact_of_discrete
  haveI : Finite W := Finite.of_injective sectionValue hb.injective
  let weights := Set.range (splitCharacter b ∘ wts)
  have hweights : FaithfulWeights S.inclusion weights :=
    faithfulWeights_of_splitWeightBasis b S.inclusion S.isClosedImmersion L l f wts hf hd
  refine ⟨⟨ψ.range, Finite.of_surjective e e.surjective, CP, weights, hweights, ?_,
    (fun w ↦ α (e.symm w)), ?_, ?_⟩⟩
  · intro w χ hχ
    obtain ⟨i, rfl⟩ := hχ
    let x := e.symm w
    have he : ψ x = w.val := congrArg Subtype.val (e.apply_symm_apply w)
    obtain ⟨V, p, a, _, _, hsurj, ha, _⟩ := commonQuotientLift q.hom.hom x x
    letI : Nonempty V.left := ⟨(hsurj.surj (IsLocalRing.closedPoint k)).choose⟩
    have hp : p = toUnit V := toUnit_unique p (toUnit V)
    have hperm := splitConjugation_permutesWeights b S.inclusion L l f wts hd
      (a ≫ N.inclusion.hom.hom) (δ (sectionValue x)) (hconj x a (hp ▸ ha))
    obtain ⟨t, ht⟩ := hperm (show wts i ∈ Set.range wts from ⟨i, rfl⟩)
    refine ⟨t, ?_⟩
    change splitCharacter b (wts t) = w.val (splitCharacter b (wts i))
    rw [← he, ht]
    exact (splitConjugation_character b (δ (sectionValue x)) (wts i)).symm
  · intro w χ
    have he : ψ (e.symm w) = w.val := congrArg Subtype.val (e.apply_symm_apply w)
    rw [← he]
    rfl
  · intro Y n w hn
    exact hconj (e.symm w) n (by rwa [hsection] at hn)

private theorem splitImage_of_splitTorus {G : AffineAlgebraicGroup k}
    {S N C : ClosedSubgroup G.val} {Q : AffineAlgebraicGroup k}
    (q : N.group ⟶ Q.val) (hs : IsSplitTorus S.group)
    (hN : RepresentsSubgroup N (fun _ g ↦ Normalizes S.inclusion g))
    (hC : RepresentsSubgroup C (fun _ g ↦ Centralizes S.inclusion g))
    [ConnectedSpace C.group.X.left]
    (j : C.group ⟶ N.group) (hj : j ≫ N.inclusion = C.inclusion)
    (hjc : IsClosedImmersion j.hom.hom.left)
    (hQ : IsFppfGroupQuotient (G := closedSubgroupAlgebraicGroup N) (Q := Q) ⟨_, j, hjc⟩ q) :
    Nonempty (SplitImage S.inclusion N.inclusion q) := by
  obtain ⟨_, he, hg⟩ := quotientByCentralizer_finiteEtale_split q hs hN hC j hj hjc hQ
  letI : Etale Q.val.X.hom := he
  letI : GeometricallyConnected q.hom.hom.left := hg
  obtain ⟨r, ⟨e⟩⟩ := hs
  obtain ⟨d⟩ := LinearAlgebraicGroups.DiagonalizableGroups.diagonalIntegerPowers k (ULift.{u} (Fin r))
  let b := d ≪≫ e.symm
  obtain ⟨n, L, l, f, wts, hf, hd⟩ := splitWeightBasis G b S.inclusion
  exact splitImage_of_lattice q b L l f wts hf hd hN hC j hj hjc hQ

/-- The finite étale normalizer quotient is the image on the character lattice
over each field over which the torus splits. -/
theorem quotientByCentralizer_conditional :
    TorusFreeUnipotent.MaximalTorusCentralizer.{u} →
    TorusFreeUnipotent.Unipotence.{u} → QuotientByCentralizer.{u} := by
  intro _ _ k _ G hG hconn S hS
  letI : Smooth G.val.X.hom := hG
  letI : ConnectedSpace G.val.X.left := hconn
  obtain ⟨N, C, j, hj, Q, q, hN, hC, he, hq, hF, hE, hFib⟩ :=
    existsFiniteEtaleNormalizerQuotient G S hS
  have hCg := centralizer_geometricallyConnected hS hC
  refine ⟨N, C, j, hj, Q, q, hN, hC, he, hq, hF, hE, hFib, ?_, ?_⟩
  · intro hs
    letI : GeometricallyConnected C.group.X.hom := hCg
    letI : ConnectedSpace C.group.X.left :=
      GeometricallyConnected.connectedSpace_of_subsingleton C.group.X.hom
    exact splitImage_of_splitTorus q hs hN hC j he hj hq
  · intro K _ _ F hs
    let G' := baseChangedAlgebraicGroup K G
    let Q' := baseChangedAlgebraicGroup K Q
    let S' : ClosedSubgroup G'.val :=
      ⟨F.obj S.group, F.map S.inclusion, baseChangeClosedSubgroup k K _ S.isClosedImmersion⟩
    obtain ⟨hNc, hN'⟩ := normalizerSchemeBaseChange k K S.inclusion N S.isClosedImmersion hN
    obtain ⟨hCc, hC'⟩ := centralizerSchemeBaseChange k K S.inclusion C hC
    let N' := scalarExtendedSubgroup K N hNc
    let C' := scalarExtendedSubgroup K C hCc
    have hji : F.map j ≫ N'.inclusion = C'.inclusion := by
      change F.map j ≫ F.map N.inclusion = F.map C.inclusion
      rw [← F.map_comp, he]
    have hj' := baseChangeClosedSubgroup k K j hj
    letI : GeometricallyConnected C'.group.X.hom :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback C.group.X.hom (fieldSpecMap k K)) hCg
    letI : ConnectedSpace C'.group.X.left :=
      GeometricallyConnected.connectedSpace_of_subsingleton C'.group.X.hom
    have hq' := baseChangedGroupQuotient K (C := closedSubgroupAlgebraicGroup C)
      (N := closedSubgroupAlgebraicGroup N) (Q := Q) q j hj hq hj'
    exact splitImage_of_splitTorus (G := G') (S := S') (N := N') (C := C') (Q := Q')
      (F.map q) hs hN' hC' (F.map j) hji hj' hq'

end

end LinearAlgebraicGroups.NormalizerLatticeAction

universe v8_closure_622b9e562cb53715_u0
theorem _root_.«LinearAlgebraicGroups».«NormalizerLatticeAction».«borelQuotientFixedPoints» : _root_.«LinearAlgebraicGroups».«Specs».«NormalizerLatticeAction».«BorelQuotientFixedPoints».{v8_closure_622b9e562cb53715_u0} :=
  @_root_.«LinearAlgebraicGroups».«NormalizerLatticeAction».«borelQuotientFixedPoints_conditional».{v8_closure_622b9e562cb53715_u0} (@_root_.«LinearAlgebraicGroups».«TorusFreeUnipotent».«maximalTorusCentralizer».{v8_closure_622b9e562cb53715_u0}) (@_root_.«LinearAlgebraicGroups».«TorusFreeUnipotent».«torusFreeUnipotent».{v8_closure_622b9e562cb53715_u0})
theorem _root_.«LinearAlgebraicGroups».«NormalizerLatticeAction».«normalTorusCentral» : _root_.«LinearAlgebraicGroups».«Specs».«NormalizerLatticeAction».«NormalTorusCentral».{v8_closure_622b9e562cb53715_u0} :=
  @_root_.«LinearAlgebraicGroups».«NormalizerLatticeAction».«normalTorusCentral_conditional».{v8_closure_622b9e562cb53715_u0} (@_root_.«LinearAlgebraicGroups».«TorusFreeUnipotent».«maximalTorusCentralizer».{v8_closure_622b9e562cb53715_u0}) (@_root_.«LinearAlgebraicGroups».«TorusFreeUnipotent».«torusFreeUnipotent».{v8_closure_622b9e562cb53715_u0})
theorem _root_.«LinearAlgebraicGroups».«NormalizerLatticeAction».«quotientByCentralizer» : _root_.«LinearAlgebraicGroups».«Specs».«NormalizerLatticeAction».«QuotientByCentralizer».{v8_closure_622b9e562cb53715_u0} :=
  @_root_.«LinearAlgebraicGroups».«NormalizerLatticeAction».«quotientByCentralizer_conditional».{v8_closure_622b9e562cb53715_u0} (@_root_.«LinearAlgebraicGroups».«TorusFreeUnipotent».«maximalTorusCentralizer».{v8_closure_622b9e562cb53715_u0}) (@_root_.«LinearAlgebraicGroups».«TorusFreeUnipotent».«torusFreeUnipotent».{v8_closure_622b9e562cb53715_u0})
