import Specs.LinearAlgebraicGroups.Representation.SteinbergTensorProduct
import LinearAlgebraicGroups.Representation.SteinbergTensorStep
import LinearAlgebraicGroups.Representation.WeylModules
import LinearAlgebraicGroups.RootData.SpecialLinearDatum
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.Representation.NonsplitSymmetricPower
open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj Kronecker TensorProduct

universe u

namespace LinearAlgebraicGroups.Representation.SteinbergTensorProduct

open LinearAlgebraicGroups.Specs
open Specs.SteinbergTensorProduct
open CharacterDescent (Character Cocharacter)
open CharacterPairing (pairing)
open AbstractPairing (Datum IsAttachedCoroot Root)
open FlagLineBundle (OppositeBorelPair)
open InducedNonvanishing (Dominant)
open Specs.GeometricRadicals (IsSemisimple IsUnipotentRadical)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open RootWeightAction (SimpleRoot Representation)
open SimpleClassification (SocleModel)

noncomputable section

set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem digitWeight_eq_prod {X : Type*} [CommGroup X] (p : ℕ) (l : List X) :
    digitWeight p l = ∏ i ∈ Finset.range l.length, l.getD i 1 ^ (p ^ i) := by
  induction l with
  | nil => simp [digitWeight]
  | cons a l ih =>
    rw [List.length_cons, Finset.prod_range_succ', digitWeight, ih, ← Finset.prod_pow]
    simp only [List.getD_cons_zero, pow_zero, pow_one, List.getD_cons_succ, pow_succ, pow_mul]
    exact mul_comm _ _

private theorem coordinate_digitWeight {X : Type*} [CommGroup X] {I : Type*}
    (e : Additive X →ₗ[ℤ] (I → ℤ)) (p : ℕ) (a : X) (l : List X) (j : I) :
    e (Additive.ofMul (digitWeight p (a :: l))) j =
      e (Additive.ofMul a) j + (p : ℤ) * e (Additive.ofMul (digitWeight p l)) j := by
  change e (Additive.ofMul a + p • Additive.ofMul (digitWeight p l)) j = _
  simp [nsmul_eq_mul]

private theorem bounded_digits {X : Type*} [CommGroup X] {I : Type*}
    (e : Additive X ≃ₗ[ℤ] (I → ℤ)) {p : ℕ} (hp : 1 < p) (n : ℕ)
    (x : X) (hx : ∀ j, 0 ≤ e (Additive.ofMul x) j ∧ e (Additive.ofMul x) j < (p : ℤ)^n) :
    ∃ l : List X, (∀ a ∈ l, ∀ j, 0 ≤ e (Additive.ofMul a) j ∧ e (Additive.ofMul a) j < p) ∧
      digitWeight p l = x := by
  induction n generalizing x with
  | zero =>
      refine ⟨[], by simp, ?_⟩
      apply Additive.ofMul.injective
      apply e.injective
      ext j
      have h := hx j
      simp only [pow_zero] at h
      have hz : e (Additive.ofMul x) j = 0 := by omega
      rw [hz]
      change e 0 j = 0
      simp
  | succ n ih =>
      let v := e (Additive.ofMul x)
      let a : X := Additive.toMul (e.symm (fun j => v j % (p : ℤ)))
      let y : X := Additive.toMul (e.symm (fun j => v j / (p : ℤ)))
      have ha : e (Additive.ofMul a) = fun j => v j % (p : ℤ) := e.apply_symm_apply _
      have hy : e (Additive.ofMul y) = fun j => v j / (p : ℤ) := e.apply_symm_apply _
      have hp' : 0 < (p : ℤ) := by omega
      obtain ⟨l, hl, he⟩ := ih y (fun j => by
        rw [hy]
        exact ⟨Int.ediv_nonneg (hx j).1 hp'.le,
          Int.ediv_lt_of_lt_mul hp' (by simpa only [pow_succ] using (hx j).2)⟩)
      refine ⟨a :: l, ?_, ?_⟩
      · intro b hb j
        rcases List.mem_cons.mp hb with rfl | hb
        · rw [ha]
          exact ⟨Int.emod_nonneg _ hp'.ne', Int.emod_lt_of_pos _ hp'⟩
        · exact hl b hb j
      · apply Additive.ofMul.injective
        apply e.injective
        ext j
        change e.toLinearMap (Additive.ofMul (digitWeight p (a :: l))) j = _
        rw [coordinate_digitWeight e.toLinearMap]
        change e (Additive.ofMul a) j + (p : ℤ) * e (Additive.ofMul (digitWeight p l)) j = _
        rw [he, ha, hy]
        exact Int.emod_add_mul_ediv _ _

private def integerDigit (p x : ℤ) : ℕ → ℤ
  | 0 => x % p
  | i + 1 => integerDigit p (x / p) i

private theorem integerDigit_zero (p : ℤ) (i : ℕ) : integerDigit p 0 i = 0 := by
  induction i with
  | zero => simp [integerDigit]
  | succ i ih => simpa [integerDigit] using ih

private theorem coordinate_getD {X : Type*} [CommGroup X] {I : Type*}
    (e : Additive X →ₗ[ℤ] (I → ℤ)) {p : ℕ} (hp : 0 < p) (l : List X)
    (hl : ∀ a ∈ l, ∀ j, 0 ≤ e (Additive.ofMul a) j ∧ e (Additive.ofMul a) j < p)
    (i : ℕ) (j : I) :
    e (Additive.ofMul (l.getD i 1)) j =
      integerDigit p (e (Additive.ofMul (digitWeight p l)) j) i := by
  induction l generalizing i with
  | nil =>
    change e 0 j = integerDigit p (e 0 j) i
    simp [integerDigit_zero]
  | cons a l ih =>
    have ha := hl a (by simp) j
    have hp' : (p : ℤ) ≠ 0 := by omega
    rw [coordinate_digitWeight]
    cases i with
    | zero =>
      change e (Additive.ofMul a) j =
        (e (Additive.ofMul a) j + (p : ℤ) * e (Additive.ofMul (digitWeight p l)) j) % p
      rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt ha.1 ha.2]
    | succ i =>
      rw [List.getD_cons_succ, integerDigit, Int.add_mul_ediv_left _ _ hp',
        Int.ediv_eq_zero_of_lt ha.1 ha.2, zero_add]
      exact ih (fun a ha => hl a (List.mem_cons_of_mem _ ha)) i

private theorem lattice_digits {X : Type*} [CommGroup X] {I : Type*} [Fintype I]
    (e : Additive X ≃ₗ[ℤ] (I → ℤ)) {p : ℕ} (hp : 1 < p) (x : X)
    (hx : ∀ j, 0 ≤ e (Additive.ofMul x) j) :
    ∃ l : List X, (∀ a ∈ l, ∀ j, 0 ≤ e (Additive.ofMul a) j ∧ e (Additive.ofMul a) j < p) ∧
      digitWeight p l = x ∧ ∀ l' : List X,
        (∀ a ∈ l', ∀ j, 0 ≤ e (Additive.ofMul a) j ∧ e (Additive.ofMul a) j < p) →
        digitWeight p l' = x → ∀ i, l'.getD i 1 = l.getD i 1 := by
  classical
  let f j := (e (Additive.ofMul x) j).toNat
  let n := ∑ j, f j
  have hbound (j : I) : e (Additive.ofMul x) j < (p : ℤ)^n := by
    have hnat : f j ≤ n := Finset.single_le_sum (fun j _ => Nat.zero_le (f j)) (Finset.mem_univ j)
    have hlt : f j < p ^ n := hnat.trans_lt (Nat.lt_pow_self hp)
    have hcast : ((f j : ℕ) : ℤ) < (p : ℤ)^n := by exact_mod_cast hlt
    rwa [Int.toNat_of_nonneg (hx j)] at hcast
  obtain ⟨l, hl, he⟩ := bounded_digits e hp n x (fun j => ⟨hx j, hbound j⟩)
  refine ⟨l, hl, he, fun l' hl' he' i => ?_⟩
  apply Additive.ofMul.injective
  apply e.injective
  ext j
  have hp' : 0 < p := by omega
  have h₁ := coordinate_getD e.toLinearMap hp' l' hl' i j
  have h₂ := coordinate_getD e.toLinearMap hp' l hl i j
  rw [he'] at h₁
  rw [he] at h₂
  exact h₁.trans h₂.symm

section WeightLattice

open private baseSimpleRoot from LinearAlgebraicGroups.Representation.ParabolicLineWeights
open private coroot_eq_of_reflection from LinearAlgebraicGroups.Classification.TransportedRootCoordinates
open private borel_of_regular_cocharacter from LinearAlgebraicGroups.RootData.BorelsAndChambers

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

private theorem attached_coroot_eq (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X]
    (D : Datum P.torus) (a : Root P.torus) (c : Cocharacter P.torus.group)
    (hc : IsAttachedCoroot P.torus a c) :
    c = Additive.toMul (D.rootDatum.coroot a) := by
  obtain ⟨C, s, _, _, M, N, _, Q, F, J, L, x, y, _, _, _, _, R, rfl⟩ := hc
  exact coroot_eq_of_reflection P.reductive P.split P.maximal D a R

private theorem weightCoordinates (hG : IsSemisimple G) (hsc : GeometricallySimplyConnected G)
    (P : OppositeBorelPair G) :
    ∃ (_ : Fintype (SimpleRoot P.torus P.positive))
      (e : Additive (Character P.torus.group) ≃ₗ[ℤ] (SimpleRoot P.torus P.positive → ℤ)),
      ∀ a c, IsAttachedCoroot P.torus a.val c →
        ∀ x, e (Additive.ofMul x) a = pairing P.torus.group x c := by
  classical
  obtain ⟨t, _, ht, _, hpos⟩ := borel_of_regular_cocharacter G P.reductive P.torus P.split P.maximal
    P.positive P.positiveBorel P.inPositive
  obtain ⟨h, D, _, hbase⟩ := RootData.SimpleRoots.simpleRoots G P.reductive P.torus P.split P.maximal
  letI := h
  obtain ⟨b, hb, _⟩ := hbase t ht
  letI := D.finiteRoots
  letI : Fintype b.support := Fintype.ofFinite _
  let j : b.support ≃ SimpleRoot P.torus P.positive :=
    { toFun := fun i => ((baseSimpleRoot hpos.symm hb i.val).mp i.property).choose
      invFun := fun a => ⟨a.val, (baseSimpleRoot hpos.symm hb a.val).mpr ⟨a, rfl⟩⟩
      left_inv := fun i => Subtype.ext ((baseSimpleRoot hpos.symm hb i.val).mp i.property).choose_spec
      right_inv := fun i => Subtype.ext ((baseSimpleRoot hpos.symm hb i.val).mp
        ((baseSimpleRoot hpos.symm hb i.val).mpr ⟨i, rfl⟩)).choose_spec }
  letI : Fintype (SimpleRoot P.torus P.positive) := Fintype.ofEquiv b.support j
  have hspan := (Classification.SimplyConnectedLattice.latticeCriterion
    G hG P.torus P.split P.maximal D).mp hsc
  let bY : Module.Basis b.support ℤ (Additive (Cocharacter P.torus.group)) :=
    Module.Basis.mk b.linearIndepOn_coroot (by
      change ⊤ ≤ Submodule.span ℤ (Set.range (fun i : b.support => D.rootDatum.coroot i.val))
      rw [show Set.range (fun i : b.support => D.rootDatum.coroot i.val) = D.rootDatum.coroot '' b.support by
        ext y
        constructor
        · rintro ⟨i, rfl⟩
          exact ⟨i.val, i.property, rfl⟩
        · rintro ⟨i, hi, rfl⟩
          exact ⟨⟨i, hi⟩, rfl⟩
        , b.span_int_coroot_support]
      exact hspan.ge)
  let e := D.rootDatum.toLinearMap.toPerfPair.trans (bY.dualBasis.reindex j).equivFun
  refine ⟨inferInstance, e, fun a c hc x => ?_⟩
  change (bY.dualBasis.reindex j).equivFun
    (D.rootDatum.toLinearMap.toPerfPair (Additive.ofMul x)) a = _
  rw [Module.Basis.equivFun_apply, Module.Basis.repr_reindex, Finsupp.equivMapDomain_apply, ← Module.Basis.equivFun_apply,
    Module.Basis.dualBasis_equivFun, show bY (j.symm a) = D.rootDatum.coroot a.val from
      Module.Basis.mk_apply _ _ _]
  rw [attached_coroot_eq P D a.val c hc, ← D.pairing_eq]
  rfl

theorem digits_conditional
    (_ : NonsplitSymmetricPower.FrobeniusSubmodule.{u})
    (_ : NonsplitSymmetricPower.InductionIdentification.{u})
    (_ : NonsplitSymmetricPower.MarkedFlagAndSocle.{u})
    (_ : NonsplitSymmetricPower.Nonsplit.{u})
    (_ : NonsplitSymmetricPower.PolynomialAction.{u})
    (_ : NonsplitSymmetricPower.RelativeFrobeniusComparison.{u}) : Digits.{u} := by
  intro k _ _ p hp _ G hG hsc P lam hlam
  obtain ⟨fin, e, he⟩ := weightCoordinates hG hsc P
  letI := fin
  obtain ⟨comm, D, _⟩ := RootData.BorelPositivity.borelPositivity G P.reductive P.torus P.split P.maximal
  letI := comm
  have dom (x : Character P.torus.group) :
      Dominant P x ↔ ∀ a, 0 ≤ e (Additive.ofMul x) a := by
    constructor
    · intro h a
      rw [he a _ (D.attached a.val)]
      exact h a _ (D.attached a.val)
    · intro h a c hc
      exact (he a c hc x) ▸ h a
  have restricted (x : Character P.torus.group) : Restricted P p x ↔
      ∀ j, 0 ≤ e (Additive.ofMul x) j ∧ e (Additive.ofMul x) j < p := by
    constructor
    · intro h a
      exact ⟨(dom x).mp h.1 a,
        (he a _ (D.attached a.val) x).symm ▸ h.2 a _ (D.attached a.val)⟩
    · intro h
      exact ⟨(dom x).mpr (fun a => (h a).1), fun a c hc => (he a c hc x) ▸ (h a).2⟩
  obtain ⟨l, hl, hlval, huniq⟩ := lattice_digits e hp.out.one_lt lam ((dom lam).mp hlam)
  exact ⟨l, fun a ha => (restricted a).mpr (hl a ha), hlval,
    fun l' hl' => huniq l' (fun a ha => (restricted a).mp (hl' a ha))⟩

end WeightLattice

section Matrices

open AdjointRepresentation (GroupPoints)
open RootWeightAction (act extendVector mem_fixedSpace mem_weightSpace)
open PrimitiveLine (orbitCoefficient)
open private characterEvaluation characterValue_eq_unit from LinearAlgebraicGroups.RootData.RootGroups

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
variable {I J K : Type u} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

private abbrev actionMatrix (r : Representation G.val I) (R : TestAlgebra k)
    (g : GroupPoints G.val R) : Matrix I I R := (r.app R g).val

private theorem matrixIso_trans
    {r : ∀ R : TestAlgebra k, GroupPoints G.val R → Matrix I I R}
    {s : ∀ R : TestAlgebra k, GroupPoints G.val R → Matrix J J R}
    {t : ∀ R : TestAlgebra k, GroupPoints G.val R → Matrix K K R}
    (hr : MatrixIsomorphism (G := G) r s) (hs : MatrixIsomorphism (G := G) s t) :
    MatrixIsomorphism (G := G) r t := by
  obtain ⟨C, D, hCD, hDC, hC⟩ := hr
  obtain ⟨E, F, hEF, hFE, hE⟩ := hs
  refine ⟨E * C, D * F, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc C, hCD, Matrix.one_mul, hEF]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc F, hFE, Matrix.one_mul, hDC]
  · intro R g
    rw [Matrix.map_mul (f := algebraMap k R), Matrix.mul_assoc, hC, ← Matrix.mul_assoc,
      hE, Matrix.mul_assoc]

private theorem matrixIso_symm
    {r : ∀ R : TestAlgebra k, GroupPoints G.val R → Matrix I I R}
    {s : ∀ R : TestAlgebra k, GroupPoints G.val R → Matrix J J R}
    (hr : MatrixIsomorphism (G := G) r s) : MatrixIsomorphism (G := G) s r := by
  obtain ⟨C, D, hCD, hDC, hC⟩ := hr
  refine ⟨D, C, hDC, hCD, fun R g => ?_⟩
  have h' : C.map (algebraMap k R) * D.map (algebraMap k R) = 1 := by
    rw [← Matrix.map_mul (f := algebraMap k R), hCD, Matrix.map_one _ (map_zero _) (map_one _)]
  have hd : D.map (algebraMap k R) * C.map (algebraMap k R) = 1 := by
    rw [← Matrix.map_mul (f := algebraMap k R), hDC, Matrix.map_one _ (map_zero _) (map_one _)]
  calc
    _ = D.map (algebraMap k R) * (s R g * C.map (algebraMap k R)) * D.map (algebraMap k R) := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc (s R g), h', Matrix.mul_one]
    _ = _ := by rw [← hC, ← Matrix.mul_assoc, hd, Matrix.one_mul]

omit [Fintype I] [Fintype J] [Fintype K] [DecidableEq I] [DecidableEq J] [DecidableEq K] in
private theorem matrixFrom_eq_pow {P : OppositeBorelPair G} {U : ClosedSubgroup P.positive.group}
    {l : List (Character P.torus.group)} (F : Factors P U l) (p n : ℕ)
    (R : TestAlgebra k) (g : GroupPoints G.val R) :
    F.matrixFrom p n R g = fun i j => F.matrix p R g i j ^ (p ^ n) := by
  induction F generalizing n with
  | nil => ext i j; simp [Factors.matrixFrom, Factors.matrix]
  | cons S F ih =>
    ext ⟨i, j⟩ ⟨a, b⟩
    simp only [Factors.matrixFrom, Factors.matrix, Matrix.kronecker_apply, ih, mul_pow,
      ← pow_mul, ← pow_succ']

omit [Fintype I] in
private theorem extend_single (R : TestAlgebra k) (j : I) :
    extendVector R (Pi.single j (1 : k)) = Pi.single j (1 : R) := by
  funext i
  by_cases h : i = j
  · subst i
    simp [extendVector]
  · simp [extendVector, Pi.single_eq_of_ne h]

private theorem matrixIso_of_equivariant {r : Representation G.val I} {s : Representation G.val J}
    (e : (I → k) ≃ₗ[k] (J → k)) (he : PrimitiveLine.IsEquivariant r s e.toLinearMap) :
    MatrixIsomorphism (G := G) (actionMatrix r) (actionMatrix s) := by
  let C := LinearMap.toMatrix' e.toLinearMap
  let D := LinearMap.toMatrix' e.symm.toLinearMap
  have hCD : C * D = 1 := by
    rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id]
  have hDC : D * C = 1 := by
    rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]
  refine ⟨C, D, hCD, hDC, ?_⟩
  intro R g
  ext i j
  by_contra hne
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_ne_zero k (sub_ne_zero.mpr hne)
  apply hℓ
  have hcoeff := congrFun (he R g ℓ (Pi.single j 1)) i
  rw [map_sub, sub_eq_zero, Matrix.mul_apply, Matrix.mul_apply, map_sum, map_sum]
  have hmul (c : k) (a : R) : ℓ (algebraMap k R c * a) = c * ℓ a := by
    simpa only [Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply] using map_smul ℓ c a
  have hentry (m : I) : orbitCoefficient r R g ℓ (Pi.single j 1) m =
      ℓ (actionMatrix r R g m j) := by
    change ℓ ((actionMatrix r R g).mulVec (extendVector R (Pi.single j 1)) m) = _
    rw [extend_single, Matrix.mulVec_single_one]
    rfl
  have hleft : e (orbitCoefficient r R g ℓ (Pi.single j 1)) i =
      ∑ m, C i m * ℓ (actionMatrix r R g m j) := by
    change e.toLinearMap _ i = _
    rw [← LinearMap.toMatrix'_mulVec e.toLinearMap]
    simp only [Matrix.mulVec, dotProduct, hentry]
    rfl
  have hright : orbitCoefficient s R g ℓ (e (Pi.single j 1)) i =
      ∑ m, C m j * ℓ (actionMatrix s R g i m) := by
    change ℓ (∑ m, actionMatrix s R g i m * algebraMap k R (e (Pi.single j 1) m)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [mul_comm (actionMatrix s R g i m), hmul]
    rfl
  rw [LinearEquiv.coe_coe, hleft, hright] at hcoeff
  simp only [Matrix.map_apply, hmul]
  rw [hcoeff]
  apply Finset.sum_congr rfl
  intro m _
  rw [mul_comm (actionMatrix s R g i m), hmul]

private theorem matrixIso_tensor_twist (p : ℕ) [Fact p.Prime] [CharP k p]
    {r : ∀ R : TestAlgebra k, GroupPoints G.val R → Matrix I I R}
    {s : ∀ R : TestAlgebra k, GroupPoints G.val R → Matrix J J R}
    (h : MatrixIsomorphism (G := G) r s)
    (a : ∀ R : TestAlgebra k, GroupPoints G.val R → Matrix K K R) :
    MatrixIsomorphism (G := G)
      (fun R g => a R g ⊗ₖ (fun i j => r R g i j ^ p))
      (fun R g => a R g ⊗ₖ (fun i j => s R g i j ^ p)) := by
  obtain ⟨C, D, hCD, hDC, hC⟩ := h
  let f := frobenius k p
  let E : Matrix (K × J) (K × I) k := 1 ⊗ₖ C.map f
  let F : Matrix (K × I) (K × J) k := 1 ⊗ₖ D.map f
  refine ⟨E, F, ?_, ?_, ?_⟩
  · dsimp only [E, F]
    rw [← Matrix.mul_kronecker_mul, one_mul, ← Matrix.map_mul (f := f), hCD,
      Matrix.map_one _ (map_zero f) (map_one f), Matrix.one_kronecker_one]
  · dsimp only [E, F]
    rw [← Matrix.mul_kronecker_mul, one_mul, ← Matrix.map_mul (f := f), hDC,
      Matrix.map_one _ (map_zero f) (map_one f), Matrix.one_kronecker_one]
  · intro R g
    rcases subsingleton_or_nontrivial R with hR | hR
    · letI := hR
      exact Subsingleton.elim _ _
    letI := hR
    haveI : CharP R p := CharP.of_ringHom_of_ne_zero (algebraMap k R) p
      (Fact.out : p.Prime).ne_zero
    let fR := frobenius R p
    have hmap : E.map (algebraMap k R) = 1 ⊗ₖ (C.map (algebraMap k R)).map fR := by
      ext ⟨i, j⟩ ⟨l, m⟩
      simp only [E, Matrix.map_apply, Matrix.kronecker_apply, map_mul]
      change algebraMap k R ((1 : Matrix K K k) i l) * algebraMap k R (C j m ^ p) =
        (1 : Matrix K K R) i l * (algebraMap k R (C j m)) ^ p
      rw [map_pow]
      congr 1
      by_cases h : i = l <;> simp [Matrix.one_apply, h]
    have hF := congrArg (fun M : Matrix J I R => M.map fR) (hC R g)
    rw [Matrix.map_mul (f := fR), Matrix.map_mul (f := fR)] at hF
    rw [hmap, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, one_mul, mul_one]
    exact congrArg (fun M : Matrix J I R => a R g ⊗ₖ M) hF

end Matrices

section TensorFormula

open RationalRepresentations
open SimpleClassification (Realizes HasHighestWeight)
open AdjointRepresentation (GroupPoints)
open RootWeightAction (act extendVector)
open Unipotent (closedSubgroupAlgebraicGroup)

open private pointCoordinates pointCoordinates_apply
  from LinearAlgebraicGroups.Representation.RestrictedSimplicity
open private matrixAction matrixAction_eq_evaluate realizes_restrict
  from LinearAlgebraicGroups.Representation.SteinbergTensorStep
open private tensorCoaction_eq tensorCoefficients
  from LinearAlgebraicGroups.Representation.TensorAndDual
open private trivialRepresentation primitive_trivial
  from LinearAlgebraicGroups.Representation.ParabolicLineWeights

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
variable {P : OppositeBorelPair G} {U : ClosedSubgroup P.positive.group}

private theorem realized_matrix {V I : Type u} [AddCommGroup V] [Module k V]
    [Fintype I] [DecidableEq I] {A : HopfAlgebraCategory k} (e : specGroup A ≅ G.val)
    (b : Module.Basis I k V) (δ : RightComodule k A V) (r : Representation G.val I)
    (hr : Realizes e b δ r) (R : TestAlgebra k) (a : A →ₐ[k] R) (i j : I) :
    actionMatrix r R (pointCoordinates e R a) i j = a (coefficients A b δ i j) := by
  have hv : b.equivFun (b j) = Pi.single j 1 := by
    ext x
    by_cases h : x = j
    · subst x; simp
    · simp [h, Ne.symm h]
  have hm := hr R a (b.equivFun (b j)) i
  rw [LinearEquiv.symm_apply_apply, ← matrixAction_eq_evaluate] at hm
  change (actionMatrix r R (pointCoordinates e R a)).mulVec
    (extendVector R (b.equivFun (b j))) i = _ at hm
  rw [hv, extend_single, Matrix.mulVec_single_one] at hm
  change actionMatrix r R (pointCoordinates e R a) i j = _ at hm
  refine hm.trans ?_
  unfold matrixAction
  rw [hv]
  simp [Pi.single_apply, eq_comm]

private theorem tensor_step_matrix {p : ℕ} {eta mu : Character P.torus.group}
    (S : SocleModel P U eta) (M : SocleModel P U mu)
    (a : M.A ⟶ S.A) (rho sigma : RightComodule k S.A M.socle)
    (tau : RightComodule k S.A (S.socle ⊗[k] M.socle))
    (r : Representation G.val (S.J × M.J))
    (ha : specGroupMap a ≫ M.groupIso.hom = S.groupIso.hom)
    (hrho : rho.coaction = a.hom.toAlgHom.toLinearMap.lTensor M.socle ∘ₗ M.socleCoaction.coaction)
    (hsigma : Specs.SteinbergTensorStep.IsFirstTwist p S.A M.socleBasis rho sigma)
    (htau : tau.coaction = tensorCoactionMap S.A S.socleCoaction sigma)
    (hr : Realizes S.groupIso (S.socleBasis.tensorProduct M.socleBasis) tau r) :
    actionMatrix r = fun R g => actionMatrix S.socleAction R g ⊗ₖ
      (fun i j => actionMatrix M.socleAction R g i j ^ p) := by
  have hM := realizes_restrict a S.groupIso M.groupIso ha M.socleBasis
    M.socleCoaction rho hrho M.socleAction M.socleAction_spec
  have ht : tau = tensorCoaction S.A S.socleBasis M.socleBasis S.socleCoaction sigma := by
    cases tau with
    | mk coact coassoc counit =>
      generalize h : tensorCoaction S.A S.socleBasis M.socleBasis S.socleCoaction sigma = d
      cases d with
      | mk coact' coassoc' counit' =>
        have h' := tensorCoaction_eq S.A S.socleBasis M.socleBasis S.socleCoaction sigma
        rw [h] at h'
        change coact' = _ at h'
        change coact = _ at htau
        cases htau.trans h'.symm
        rfl
  subst tau
  funext R g
  obtain ⟨b, rfl⟩ := (pointCoordinates S.groupIso R).surjective g
  ext ⟨i, j⟩ ⟨l, m⟩
  rw [realized_matrix _ _ _ _ hr, Matrix.kronecker_apply,
    realized_matrix _ _ _ _ S.socleAction_spec, realized_matrix _ _ _ _ hM,
    tensorCoefficients, hsigma, map_mul, map_pow]

private theorem trivial_simple : PrimitiveLine.IsSimple (trivialRepresentation (G := G)) := by
  refine ⟨top_ne_bot, fun N _ => ?_⟩
  by_cases h : N = ⊥
  · exact Or.inl h
  · right
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff N).mp h
    have h0 : v ⟨()⟩ ≠ 0 := by
      intro hz
      apply hv0
      funext i
      have hi : i = ⟨()⟩ := Subsingleton.elim _ _
      subst i
      exact hz
    apply top_unique
    intro w _
    have hw : w = (w ⟨()⟩ / v ⟨()⟩) • v := by
      funext i
      have hi : i = ⟨()⟩ := Subsingleton.elim _ _
      subst i
      exact (div_mul_cancel₀ _ h0).symm
    rw [hw]
    exact N.smul_mem _ hv

private theorem simpleModelIso (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U)
    {I : Type u} [Fintype I] [DecidableEq I] {chi : Character P.torus.group}
    (r : Representation G.val I) (L : SocleModel P U chi)
    (hs : PrimitiveLine.IsSimple r) (hw : HasHighestWeight P U r chi) :
    MatrixIsomorphism (G := G) (actionMatrix r) (actionMatrix L.socleAction) := by
  have hc := SimpleClassification.classification G P U hU
  obtain ⟨C, hC⟩ := hc.2.2 chi (hc.2.1 r hs chi hw)
  obtain ⟨⟨f, hf⟩⟩ := (hC r hs).mpr hw
  obtain ⟨⟨g, hg⟩⟩ := (hC L.socleAction L.simple).mpr ⟨_, L.primitive⟩
  exact matrixIso_trans (matrixIso_of_equivariant f hf)
    (matrixIso_symm (matrixIso_of_equivariant g hg))

private theorem digitWeight_dominant (p : ℕ) (l : List (Character P.torus.group))
    (hl : ∀ a ∈ l, Dominant P a) : Dominant P (digitWeight p l) := by
  obtain ⟨comm, D, _⟩ := RootData.BorelPositivity.borelPositivity G P.reductive P.torus P.split P.maximal
  letI := comm
  intro a c hc
  induction l with
  | nil =>
    rw [← D.pairing_eq]
    change D.rootDatum.toLinearMap 0 (Additive.ofMul c) ≥ 0
    simp
  | cons x l ih =>
    have hx := hl x (List.mem_cons_self) a c hc
    have htail := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    rw [← D.pairing_eq] at hx htail ⊢
    change 0 ≤ D.rootDatum.toLinearMap
      (Additive.ofMul x + p • Additive.ofMul (digitWeight p l)) (Additive.ofMul c)
    simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
    exact add_nonneg hx (mul_nonneg (Int.natCast_nonneg p) htail)

private theorem tensor_formula [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hG : IsSemisimple G) (hsc : GeometricallySimplyConnected G)
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U)
    {l : List (Character P.torus.group)} (hl : ∀ a ∈ l, Restricted P p a)
    (F : Factors P U l) (L : SocleModel P U (digitWeight p l)) :
    MatrixIsomorphism (G := G) (F.matrix p) (actionMatrix L.socleAction) := by
  induction F with
  | nil =>
    have h := simpleModelIso hU trivialRepresentation L trivial_simple ⟨_, primitive_trivial⟩
    have hunit : actionMatrix (trivialRepresentation (G := G)) =
        (Factors.nil (P := P) (U := U)).matrix p := by
      funext R g
      ext i j
      change (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) R) i j = 1
      simp [Matrix.one_apply, Subsingleton.elim i j]
    rw [hunit] at h
    exact h
  | @cons a l S F ih =>
    have ha := hl a List.mem_cons_self
    have hl' x hx := hl x (List.mem_cons_of_mem a hx)
    have hmu := digitWeight_dominant p l (fun x hx => (hl' x hx).1)
    obtain ⟨M, _⟩ := (SimpleClassification.classification G P U hU).2.2 _ hmu
    obtain ⟨b, rho, sigma, tau, r, hb, hrho, _, hsigma, htau, hr, hrs, hwt, _⟩ :=
      SteinbergTensorStep.oneStep p G hG hsc P U hU a _ ha.1 hmu ha.2 S M
    have he := tensor_step_matrix S M b rho sigma tau r hb hrho hsigma htau hr
    have h₁ := matrixIso_tensor_twist p (ih hl' M) (actionMatrix S.socleAction)
    have h₂ := simpleModelIso hU r L hrs hwt
    rw [he] at h₂
    exact matrixIso_trans h₁ h₂

private theorem exists_factors (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U)
    (l : List (Character P.torus.group)) (hl : ∀ a ∈ l, Dominant P a) :
    Nonempty (Factors P U l) := by
  induction l with
  | nil => exact ⟨Factors.nil⟩
  | cons a l ih =>
    obtain ⟨S, _⟩ := (SimpleClassification.classification G P U hU).2.2 a (hl a List.mem_cons_self)
    obtain ⟨F⟩ := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    exact ⟨Factors.cons S F⟩

theorem tensorProductFormula_conditional
    (_ : NonsplitSymmetricPower.FrobeniusSubmodule.{u})
    (_ : NonsplitSymmetricPower.InductionIdentification.{u})
    (_ : NonsplitSymmetricPower.MarkedFlagAndSocle.{u})
    (_ : NonsplitSymmetricPower.Nonsplit.{u})
    (_ : NonsplitSymmetricPower.PolynomialAction.{u})
    (_ : NonsplitSymmetricPower.RelativeFrobeniusComparison.{u}) : TensorProductFormula.{u} := by
  intro k _ _ p _ _ G hG hsc P U hU l hl
  have hd a ha := (hl a ha).1
  obtain ⟨L, _⟩ := (SimpleClassification.classification G P U hU).2.2 _
    (digitWeight_dominant p l hd)
  refine ⟨exists_factors hU l hd, ⟨L⟩, fun F M => ?_⟩
  have h : F.matrixFrom p 0 = F.matrix p := by
    funext R g
    simpa only [pow_zero, pow_one] using matrixFrom_eq_pow F p 0 R g
  rw [h]
  exact tensor_formula p hG hsc hU hl F M

end TensorFormula

section RelativeTwists

open RationalRepresentations
open FiniteDistributions (twistCoordinates frobeniusPullback frobeniusPullback_formula)
open Specs.RelativeFrobenius (extendAlong scalarTensor)
open private extendedMatrix from LinearAlgebraicGroups.Representation.SteinbergTensorStep
open private map_coactionMatrix from LinearAlgebraicGroups.Representation.TensorAndDual
open private extAlong counit_tmul comul_tmul comulTensorMap comulTensorMap_tmul
  from LinearAlgebraicGroups.Affine.RelativeFrobenius

private theorem scalarExtensionAssocIso {K L M : Type u} [Field K] [Field L] [Field M]
    (α : K →+* L) (β : L →+* M) (A : HopfAlgebraCategory K) :
    ∃ e : extendAlong (β.comp α) A ≅ extendAlong β (extendAlong α A),
      ∀ (c : M) (x : A),
        e.hom.hom (scalarTensor (β.comp α) A c x) =
          scalarTensor β (extendAlong α A) c (scalarTensor α A 1 x) := by
  letI : Algebra K L := α.toAlgebra
  letI : Algebra L M := β.toAlgebra
  letI : Algebra K M := (β.comp α).toAlgebra
  letI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' rfl
  let e : extendAlong (β.comp α) A ≃ₐ[M] extendAlong β (extendAlong α A) :=
    (Algebra.TensorProduct.cancelBaseChange K L M M A).symm
  have he (c : M) (x : A) :
      e (scalarTensor (β.comp α) A c x) =
        scalarTensor β (extendAlong α A) c (scalarTensor α A 1 x) :=
    Algebra.TensorProduct.cancelBaseChange_symm_tmul K L M M A c x
  refine ⟨CommHopfAlgCat.isoMk (BialgEquiv.ofAlgEquiv e ?_ ?_), he⟩
  · apply extAlong (β.comp α) A
    intro x
    change Bialgebra.counitAlgHom M (extendAlong β (extendAlong α A))
        (e (scalarTensor (β.comp α) A 1 x)) =
      Bialgebra.counitAlgHom M (extendAlong (β.comp α) A) (scalarTensor (β.comp α) A 1 x)
    rw [he, counit_tmul, counit_tmul, counit_tmul]
    rfl
  · apply extAlong (β.comp α) A
    intro x
    symm
    change Bialgebra.comulAlgHom M (extendAlong β (extendAlong α A))
        (e (scalarTensor (β.comp α) A 1 x)) =
      Algebra.TensorProduct.map e.toAlgHom e.toAlgHom
        (Bialgebra.comulAlgHom M (extendAlong (β.comp α) A) (scalarTensor (β.comp α) A 1 x))
    rw [he, comul_tmul, comul_tmul, comul_tmul]
    generalize Bialgebra.comulAlgHom K A x = t
    induction t using TensorProduct.inductionOn with
    | tmul x y => simp only [comulTensorMap_tmul, Algebra.TensorProduct.map_tmul,
        AlgEquiv.coe_toAlgHom, he]
    | add x y hx hy => simp only [map_add, hx, hy]

private theorem scalarExtensionTwistIso {K k : Type u} [Field K] [Field k]
    (α : K →+* k) (f : k →+* k) (h : f.comp α = α) (A : HopfAlgebraCategory K) :
    ∃ e : extendAlong α A ≅ extendAlong f (extendAlong α A),
      ∀ x : A, e.hom.hom (scalarTensor α A 1 x) =
        scalarTensor f (extendAlong α A) 1 (scalarTensor α A 1 x) := by
  obtain ⟨e, he⟩ := scalarExtensionAssocIso α f A
  refine ⟨eqToIso (congrArg (fun g => extendAlong g A) h.symm) ≪≫ e, fun x => ?_⟩
  have hx (a b : K →+* k) (hab : a = b) :
      (eqToHom (congrArg (fun g => extendAlong g A) hab)).hom (scalarTensor a A 1 x) =
        scalarTensor b A 1 x := by
    subst b
    rfl
  change e.hom.hom ((eqToHom (congrArg (fun g => extendAlong g A) h.symm)).hom
    (scalarTensor α A 1 x)) = _
  rw [hx α (f.comp α) h.symm, he]

private theorem splitModelRelativeTwist : SplitModelRelativeTwist.{u} := by
  intro k _ p n _ _
  dsimp only
  intro A₀
  let base : ULift.{u} (ZMod p) →+* k :=
    (ZMod.castHom (dvd_refl p) k).comp ULift.ringEquiv.toRingHom
  let f := iterateFrobenius k p n
  have h : f.comp base = base := by
    rw [← RingHom.cancel_right (f := (ULift.ringEquiv : ULift.{u} (ZMod p) ≃+* _).symm.toRingHom)
      (hf := ULift.ringEquiv.symm.surjective)]
    exact Subsingleton.elim _ _
  obtain ⟨e, he⟩ := scalarExtensionTwistIso base f h A₀
  refine ⟨e, he, fun F hF R g a => ?_⟩
  change g (F.hom (e.hom.hom (scalarTensor base A₀ 1 a))) = _
  rw [he, hF, one_smul, map_pow]

theorem relativeTwistMatrices_conditional
    (_ : NonsplitSymmetricPower.FrobeniusSubmodule.{u})
    (_ : NonsplitSymmetricPower.InductionIdentification.{u})
    (_ : NonsplitSymmetricPower.MarkedFlagAndSocle.{u})
    (_ : NonsplitSymmetricPower.Nonsplit.{u})
    (_ : NonsplitSymmetricPower.PolynomialAction.{u})
    (_ : NonsplitSymmetricPower.RelativeFrobeniusComparison.{u}) : RelativeTwistMatrices.{u} := by
  refine ⟨?_, splitModelRelativeTwist⟩
  intro k V I _ _ _ _ _ p n _ _ A b rho
  let B := twistCoordinates k p n A
  let f := iterateFrobenius k p n
  let C : Matrix I I B := fun i j => scalarTensor f A 1 (coefficients A b rho i j)
  have hC : IsCoactionMatrix B C := extendedMatrix f _ (coefficients_isCoactionMatrix A b rho)
  let delta := coactionOfMatrix B b C hC
  let F := frobeniusPullback p n A
  let D := F.hom.toAlgHom.mapMatrix C
  have hD : IsCoactionMatrix A D := map_coactionMatrix F hC
  let sigma := coactionOfMatrix A b D hD
  have hd : coefficients B b delta = C := coefficients_coactionOfMatrix B b C hC
  have hs : coefficients A b sigma = D := coefficients_coactionOfMatrix A b D hD
  refine ⟨F, delta, sigma, frobeniusPullback_formula p n A, ?_, ?_, ?_⟩
  · rw [hd]
    exact fun i j => rfl
  · apply b.ext
    intro j
    rw [coaction_apply_basis A b sigma, LinearMap.comp_apply, coaction_apply_basis B b delta,
      hd, hs, map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [LinearMap.lTensor_tmul]; rfl)
  · intro i j
    rw [hs]
    change F.hom (scalarTensor f A 1 (coefficients A b rho i j)) = _
    simpa only [one_smul] using (frobeniusPullback_formula p n A) 1 (coefficients A b rho i j)

end RelativeTwists

section RankOne

open AdjointRepresentation (GroupPoints)
open GeneralLinearStructure (SpecialMatrixPoints)
open CharacterPairing (characterValue)
open Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (RepresentsOnAlgebras)
open Specs.SpecialLinearDatum (DiagonalTorus LatticeIdentification CharacterLattice coordinate determinantOneUnits)
open Specs.NonsplitSymmetricPower (Forms exponents term purePowers purePowerMap frobeniusMatrix extend contract)
open PrimitiveLine (IsSimple IsStable)
open RootWeightAction (act extendVector mem_fixedSpace mem_weightSpace)
open SimpleClassification (HasHighestWeight)
open private unipotent_diagonal from LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private same_subgroup_of_same_affine_points from LinearAlgebraicGroups.RootData.RankOneFlag
open private sameSubgroupIso from LinearAlgebraicGroups.Classification.CentralIsogenies
open private charactersOfIso from LinearAlgebraicGroups.RootData.CharacterPairing
open private characterValue_restrict from LinearAlgebraicGroups.Representation.ParabolicLineWeights
open private socleInclusion socleInclusion_injective socleInclusion_equivariant
  from LinearAlgebraicGroups.Representation.WeylModules

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

private def naturalAction (s : SpecialMatrixPoints G 2) :
    Representation G.val (ULift.{u} (Fin 2)) :=
  s.hom ≫
    { app := fun R => GrpCat.ofHom Matrix.SpecialLinearGroup.toGL
      naturality := by
        intro R S f
        apply GrpCat.ext
        intro x
        apply Units.ext
        rfl }

private theorem stable_transvection (s : SpecialMatrixPoints G 2)
    {N : Submodule k (ULift.{u} (Fin 2) → k)} (hN : IsStable (naturalAction s) N)
    {v : ULift.{u} (Fin 2) → k} (hv : v ∈ N)
    {i j : ULift.{u} (Fin 2)} (hij : i ≠ j) (hj : v j ≠ 0) :
    Pi.single i 1 ∈ N := by
  let R := CommAlgCat.of k k
  let t : Matrix.SpecialLinearGroup (ULift.{u} (Fin 2)) k :=
    Matrix.SpecialLinearGroup.transvection hij 1
  obtain ⟨g, hg⟩ := ((s.app R).groupIsoToMulEquiv).surjective t
  change s.hom.app R g = t at hg
  have horbit :
      act (naturalAction s) R g (extendVector R v) ∈ N := by
    apply hN v hv
    let W (S : TestAlgebra k) (x : GroupPoints G.val S) : Submodule k (ULift.{u} (Fin 2) → k) :=
      Submodule.span k (Set.range fun ℓ : S →ₗ[k] k =>
        fun i => ℓ (act (naturalAction s) S (x ≫ 𝟙 G.val.X) (extendVector S v) i))
    have hle : W R g ≤ CyclicHighestWeight.orbitSpan (naturalAction s) (𝟙 G.val.X) v :=
      le_iSup₂ (f := W) R g
    apply hle
    apply Submodule.subset_span
    refine ⟨LinearMap.id, ?_⟩
    rw [Category.comp_id]
    rfl
  have hv' : v j • Pi.single i (1 : k) ∈ N := by
    have h := N.sub_mem horbit hv
    change ((s.hom.app R g).val.mulVec (extendVector R v) - v) ∈ N at h
    have he : extendVector R v = v := by
      funext a
      exact Algebra.algebraMap_self_apply (v a)
    rw [hg, he, Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec,
      Matrix.one_mulVec, Matrix.single_mulVec_eq, one_mul, add_sub_cancel_left] at h
    exact h
  simpa only [smul_smul, inv_mul_cancel₀ hj, one_smul] using N.smul_mem (v j)⁻¹ hv'

private theorem natural_simple (s : SpecialMatrixPoints G 2) : IsSimple (naturalAction s) := by
  classical
  refine ⟨top_ne_bot, fun N hN => ?_⟩
  by_cases h : N = ⊥
  · exact Or.inl h
  right
  obtain ⟨v, hv, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  let i : ULift.{u} (Fin 2) := ⟨0⟩
  let j : ULift.{u} (Fin 2) := ⟨1⟩
  have hij : i ≠ j := by decide
  have hs : v i ≠ 0 ∨ v j ≠ 0 := by
    by_contra! hzero
    apply hne
    funext a
    rcases a with ⟨a⟩
    fin_cases a
    · exact hzero.1
    · exact hzero.2
  have hi : Pi.single i (1 : k) ∈ N ∧ Pi.single j (1 : k) ∈ N := by
    rcases hs with h0 | h1
    · have ej := stable_transvection s hN hv hij.symm h0
      exact ⟨stable_transvection s hN ej hij (by simp), ej⟩
    · have ei := stable_transvection s hN hv hij h1
      exact ⟨ei, stable_transvection s hN ei hij.symm (by simp)⟩
  apply top_unique
  rw [← (Pi.basisFun k _).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨a⟩, rfl⟩
  rw [Pi.basisFun_apply]
  fin_cases a
  · exact hi.1
  · exact hi.2

private theorem natural_highestWeight {s : SpecialMatrixPoints G 2}
    (P : OppositeBorelPair G) (U : ClosedSubgroup P.positive.group)
    (χ : Character P.torus.group)
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U)
    (hT : ∀ (R : TestAlgebra k) (g : GroupPoints G.val R),
      g ∈ SubgroupSections P.torus ((testSpec k).obj (Opposite.op R)) ↔
        (s.hom.app R g).val ⟨0⟩ ⟨1⟩ = 0 ∧ (s.hom.app R g).val ⟨1⟩ ⟨0⟩ = 0)
    (hχ : ∀ (R : TestAlgebra k) (t : GroupPoints P.torus.group R),
      characterValue χ R t = (s.hom.app R (t ≫ P.torus.inclusion.hom.hom)).val ⟨0⟩ ⟨0⟩)
    (hB : ∀ (R : TestAlgebra k) (g : GroupPoints G.val R),
      g ∈ SubgroupSections P.positive ((testSpec k).obj (Opposite.op R)) ↔
        (s.hom.app R g).val ⟨1⟩ ⟨0⟩ = 0) :
    HasHighestWeight P U (naturalAction s) χ := by
  let i : ULift.{u} (Fin 2) := ⟨0⟩
  let N : ClosedSubgroup G.val :=
    ⟨U.group, U.inclusion ≫ P.positive.inclusion, by
      letI := U.isClosedImmersion
      letI := P.positive.isClosedImmersion
      exact IsClosedImmersion.comp _ _⟩
  have hcol (R : TestAlgebra k) (b : GroupPoints N.group R) (j : ULift.{u} (Fin 2))
      (hj : j ≠ i) : (actionMatrix (naturalAction s) R (b ≫ N.inclusion.hom.hom)) j i = 0 := by
    obtain ⟨j⟩ := j
    fin_cases j
    · exact (hj rfl).elim
    · apply (hB R _).mp
      refine ⟨b ≫ U.inclusion.hom.hom, ?_⟩
      change (b ≫ U.inclusion.hom.hom) ≫ P.positive.inclusion.hom.hom =
        b ≫ U.inclusion.hom.hom ≫ P.positive.inclusion.hom.hom
      exact Category.assoc _ _ _
  have hdiag := unipotent_diagonal N hU.2.1 i (naturalAction s) hcol
  refine ⟨Pi.single i 1, by simp, mem_fixedSpace.mpr ?_, mem_weightSpace.mpr ?_⟩
  · intro R b
    change (actionMatrix (naturalAction s) R (b ≫ N.inclusion.hom.hom)).mulVec
      (extendVector R (Pi.single i 1)) = extendVector R (Pi.single i 1)
    rw [extend_single, Matrix.mulVec_single_one]
    funext j
    by_cases hj : j = i
    · subst j
      change (actionMatrix (naturalAction s) R (b ≫ N.inclusion.hom.hom)) i i = (Pi.single i (1 : R) : ULift.{u} (Fin 2) → R) i
      rw [Pi.single_eq_same]
      exact hdiag R b
    · rw [Pi.single_eq_of_ne hj]
      exact hcol R b j hj
  · intro R t
    change (actionMatrix (naturalAction s) R (t ≫ P.torus.inclusion.hom.hom)).mulVec
      (extendVector R (Pi.single i 1)) = characterValue χ R t • extendVector R (Pi.single i 1)
    rw [extend_single, Matrix.mulVec_single_one]
    funext a
    by_cases ha : a = i
    · subst a
      change (s.hom.app R (t ≫ P.torus.inclusion.hom.hom)).val i i =
        characterValue χ R t * (Pi.single i (1 : R) : ULift.{u} (Fin 2) → R) i
      rw [Pi.single_eq_same, mul_one]
      exact (hχ R t).symm
    · have ha' : a = ⟨1⟩ := by
        rcases a with ⟨a⟩
        fin_cases a
        · exact (ha rfl).elim
        · rfl
      change (s.hom.app R (t ≫ P.torus.inclusion.hom.hom)).val a i =
        characterValue χ R t * (Pi.single i (1 : R) : ULift.{u} (Fin 2) → R) a
      rw [Pi.single_eq_of_ne ha, mul_zero, ha']
      exact ((hT R _).mp ⟨t, rfl⟩).2

private theorem markedCharacter_generates {s : SpecialMatrixPoints G 2}
    (T : DiagonalTorus (r := 1) s) (D : LatticeIdentification T)
    (P : OppositeBorelPair G) (chi : Character P.torus.group)
    (hT : ∀ (R : TestAlgebra k) (g : GroupPoints G.val R),
      g ∈ SubgroupSections P.torus ((testSpec k).obj (Opposite.op R)) ↔
        (s.hom.app R g).val ⟨0⟩ ⟨1⟩ = 0 ∧ (s.hom.app R g).val ⟨1⟩ ⟨0⟩ = 0)
    (hchi : ∀ (R : TestAlgebra k) (t : GroupPoints P.torus.group R),
      characterValue chi R t = (s.hom.app R (t ≫ P.torus.inclusion.hom.hom)).val ⟨0⟩ ⟨0⟩) :
    chi ≠ 1 ∧ ∀ psi : Character P.torus.group, ∃ n : ℤ, chi ^ n = psi := by
  let diag (R : TestAlgebra k) (g : GroupPoints G.val R) : Prop :=
    (s.hom.app R g).val ⟨0⟩ ⟨1⟩ = 0 ∧ (s.hom.app R g).val ⟨1⟩ ⟨0⟩ = 0
  have hP : RepresentsOnAlgebras P.torus diag := fun R g => (hT R g).symm
  have hD : RepresentsOnAlgebras T.subgroup diag := by
    intro R g
    change diag R g ↔ g ∈ SubgroupSections T.subgroup ((testSpec k).obj (Opposite.op R))
    rw [T.range]
    constructor
    · intro h
      rintro ⟨i⟩ ⟨j⟩ hij
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact h.1
      · exact h.2
      · exact (hij rfl).elim
    · intro h
      exact ⟨h _ _ (by decide), h _ _ (by decide)⟩
  obtain ⟨i, hi⟩ := sameSubgroupIso (same_subgroup_of_same_affine_points hP hD)
  let l : CharacterLattice 2 :=
    (Submodule.span ℤ ({(1 : Fin 2 → ℤ)} : Set (Fin 2 → ℤ))).mkQ (coordinate 2 0)
  let x : Character T.subgroup.group := Additive.toMul (D.characters.symm l)
  let f := charactersOfIso i.symm
  have hf : f x = chi := by
    apply RootData.CharacterPairing.characterValuesDetectCharacters P.split
    intro R t
    change characterValue (i.hom ≫ x) R t = _
    rw [characterValue_restrict i.hom x, hchi]
    let t' : GroupPoints T.subgroup.group R := t ≫ i.hom.hom.hom
    have ht' : t' ≫ T.subgroup.inclusion.hom.hom = t ≫ P.torus.inclusion.hom.hom := by
      change t ≫ i.hom.hom.hom ≫ T.subgroup.inclusion.hom.hom = _
      rw [← Category.assoc]
      exact congrArg (fun q : P.torus.group ⟶ G.val => t ≫ q.hom.hom) hi
    rw [← ht']
    change characterValue x R t' = _
    have hmat := congrArg (fun m : Matrix (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) R =>
      m ⟨0⟩ ⟨0⟩) (T.matrix R t')
    rw [hmat]
    change characterValue x R t' = ↑(determinantOneUnits (T.pointsIso.hom.app R t') ⟨0⟩)
    change characterValue (Additive.toMul (D.characters.symm l)) R t' = _
    unfold l
    rw [D.characterValue_eq]
    simp [Fin.prod_univ_two, coordinate]
  obtain ⟨a, _, ha, _, _, _⟩ := RootData.SpecialLinearDatum.sizeTwoLattices
  have hcoord : a (D.characters (Additive.ofMul x)) = 1 := by
    change a (D.characters (D.characters.symm l)) = 1
    rw [LinearEquiv.apply_symm_apply]
    exact ha
  constructor
  · intro he
    have hx : x = 1 := f.injective (by rw [hf, he, map_one])
    rw [hx, show Additive.ofMul (1 : Character T.subgroup.group) = 0 from rfl,
      D.characters.map_zero, a.map_zero] at hcoord
    exact zero_ne_one hcoord
  · intro psi
    obtain ⟨b, rfl⟩ := f.surjective psi
    let n := a (D.characters (Additive.ofMul b))
    have hb : x ^ n = b := by
      apply Additive.ofMul.injective
      apply D.characters.injective
      apply a.injective
      change a (D.characters (n • Additive.ofMul x)) = n
      rw [map_smul, map_smul, hcoord, zsmul_eq_mul, mul_one]
      rfl
    refine ⟨n, ?_⟩
    rw [← hf, ← map_zpow, hb]

private theorem extend_purePower {R : Type u} [CommRing R] [Algebra k R]
    (p : ℕ) (v : Fin 2 → k) :
    extend (purePowerMap k p v) = purePowerMap R p (fun i => algebraMap k R (v i)) := by
  apply Subtype.ext
  change MvPolynomial.map (algebraMap k R)
      ((v 0 • term k p 0 + v 1 • term k p (Fin.last p) : Forms k p) : MvPolynomial (Fin 2) k) =
    ((algebraMap k R (v 0) • term R p 0 +
      algebraMap k R (v 1) • term R p (Fin.last p) : Forms R p) : MvPolynomial (Fin 2) R)
  have h (Q : Type u) [CommRing Q] (a : Q) (i : Fin (p + 1)) :
      ((a • term Q p i : Forms Q p) : MvPolynomial (Fin 2) Q) =
        MvPolynomial.monomial (exponents p i) a := by
    change a • (MvPolynomial.monomial (exponents p i) (1 : Q)) = _
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_mul_monomial, mul_one]
  let f : MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) R := MvPolynomial.map (algebraMap k R)
  have ht (a : k) (i : Fin (p + 1)) :
      f (↑(a • term k p i : Forms k p)) =
        ↑(algebraMap k R a • term R p i : Forms R p) := by
    calc
      _ = f (MvPolynomial.monomial (exponents p i) a) := congrArg f (h k a i)
      _ = MvPolynomial.monomial (exponents p i) (algebraMap k R a) :=
        MvPolynomial.map_monomial (algebraMap k R) _ _
      _ = _ := (h R _ _).symm
  change f ((↑(v 0 • term k p 0 : Forms k p) : MvPolynomial (Fin 2) k) +
      ↑(v 1 • term k p (Fin.last p) : Forms k p)) =
    (↑(algebraMap k R (v 0) • term R p 0 : Forms R p) : MvPolynomial (Fin 2) R) +
      ↑(algebraMap k R (v 1) • term R p (Fin.last p) : Forms R p)
  exact (f.map_add _ _).trans (congrArg₂ (· + ·) (ht (v 0) 0) (ht (v 1) (Fin.last p)))

private theorem exponents_injective (p : ℕ) : Function.Injective (exponents p) := by
  intro i j h
  apply Fin.ext
  have hh := congrArg (fun a : Fin 2 →₀ ℕ => a 1) h
  simpa [exponents] using hh

private theorem contract_add {R : Type u} [CommRing R] [Algebra k R]
    {n : ℕ} (ell : R →ₗ[k] k) (x y : Forms R n) :
    contract ell (x + y) = contract ell x + contract ell y := by
  simp only [contract, Submodule.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add, add_smul,
    Finset.sum_add_distrib]

private theorem contract_term {R : Type u} [CommRing R] [Algebra k R]
    {n : ℕ} (ell : R →ₗ[k] k) (a : R) (i : Fin (n + 1)) :
    contract ell (a • term R n i) = ell a • term k n i := by
  classical
  unfold contract
  rw [Finset.sum_eq_single i]
  · simp [term]
  · intro j _ hji
    have h : exponents n i ≠ exponents n j :=
      fun h => hji ((exponents_injective n) h).symm
    simp [term, MvPolynomial.coeff_monomial, h]
  · exact fun h => (h (Finset.mem_univ i)).elim

private theorem contract_purePower {R : Type u} [CommRing R] [Algebra k R]
    (p : ℕ) (ell : R →ₗ[k] k) (v : Fin 2 → R) :
    contract ell (purePowerMap R p v) = purePowerMap k p (fun i => ell (v i)) := by
  change contract ell (v 0 • term R p 0 + v 1 • term R p (Fin.last p)) =
    ell (v 0) • term k p 0 + ell (v 1) • term k p (Fin.last p)
  rw [contract_add, contract_term, contract_term]

theorem rankOneExample_conditional
    (frobeniusSubmodule : NonsplitSymmetricPower.FrobeniusSubmodule.{u})
    (_ : NonsplitSymmetricPower.InductionIdentification.{u})
    (markedFlagAndSocle : NonsplitSymmetricPower.MarkedFlagAndSocle.{u})
    (_ : NonsplitSymmetricPower.Nonsplit.{u})
    (_ : NonsplitSymmetricPower.PolynomialAction.{u})
    (_ : NonsplitSymmetricPower.RelativeFrobeniusComparison.{u}) : RankOneExample.{u} := by
  intro k _ _ p hp _ G s
  obtain ⟨P, chi, U, H, r, c, L, hU, hT, hchi, hB, _, _, _, E, hE, _, _, haction⟩ :=
    markedFlagAndSocle k p G s
  obtain ⟨T, D, _, _, _, _, _, hsc⟩ := RootData.SpecialLinearDatum.matrixPinnedDatum k 1 G s
  have hG := RootData.SpecialLinearDatum.semisimple k 1 G s
  obtain ⟨hne, hgen⟩ := markedCharacter_generates T D P chi hT hchi
  obtain ⟨_, e, he⟩ := weightCoordinates hG hsc P
  have hdp := (SimpleClassification.classification G P U hU).2.1 L.socleAction
    L.simple (chi ^ p) ⟨_, L.primitive⟩
  have hpair (a : SimpleRoot P.torus P.positive) (c : Cocharacter P.torus.group)
      (hc : IsAttachedCoroot P.torus a.val c) : pairing P.torus.group chi c = 1 := by
    let b : Character P.torus.group := Additive.toMul (e.symm (fun _ => 1))
    have hb : e (Additive.ofMul b) = fun _ => 1 := e.apply_symm_apply _
    obtain ⟨n, hn⟩ := hgen b
    have hm : n * pairing P.torus.group chi c = 1 := by
      have hw := congrArg (fun x : Character P.torus.group => e (Additive.ofMul x) a) hn
      change e (n • Additive.ofMul chi) a = e (Additive.ofMul b) a at hw
      rw [map_smul, hb, Pi.smul_apply, zsmul_eq_mul, he a c hc] at hw
      exact hw
    have hnonneg : 0 ≤ pairing P.torus.group chi c := by
      have hw := hdp a c hc
      rw [← he a c hc] at hw
      change 0 ≤ e (p • Additive.ofMul chi) a at hw
      have hh : e (p • Additive.ofMul chi) = p • e (Additive.ofMul chi) :=
        map_nsmul e.toAddMonoidHom _ _
      rw [hh, Pi.smul_apply, nsmul_eq_mul, he a c hc] at hw
      exact nonneg_of_mul_nonneg_right hw (by exact_mod_cast hp.out.pos)
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hm with h | h
    · exact h.2
    · omega
  have hp' : (1 : ℤ) < (p : ℤ) := by exact_mod_cast hp.out.one_lt
  have hchiR : Restricted P p chi :=
    ⟨fun a c hc => (hpair a c hc).symm ▸ (zero_le_one : (0 : ℤ) ≤ 1),
      fun a c hc => (hpair a c hc).symm ▸ hp'⟩
  have hzero (a : SimpleRoot P.torus P.positive) (c : Cocharacter P.torus.group)
      (hc : IsAttachedCoroot P.torus a.val c) : pairing P.torus.group 1 c = 0 := by
    rw [← he a c hc]
    change e 0 a = 0
    rw [e.map_zero]
    rfl
  have hzeroR : Restricted P p 1 :=
    ⟨fun a c hc => (hzero a c hc).symm ▸ le_rfl,
      fun a c hc => (hzero a c hc).symm ▸ ((zero_le_one : (0 : ℤ) ≤ 1).trans_lt hp')⟩
  refine ⟨P, chi, U, L, hU, hchi, hne, hpair, ?_, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact hzeroR
    · exact hchiR
  · simp [digitWeight]
  obtain ⟨M, _⟩ := (SimpleClassification.classification G P U hU).2.2 chi hchiR.1
  refine ⟨M, simpleModelIso hU (naturalAction s) M (natural_simple s)
    (natural_highestWeight P U chi hU hT hchi hB), ?_⟩
  obtain ⟨hinj, hrange, hfrob⟩ := frobeniusSubmodule k p
  let f := E.toLinearMap.comp (purePowerMap k p)
  have hf : f.range = L.socle := by
    rw [LinearMap.range_comp, hrange, hE]
  let f' := f.codRestrict L.socle (fun w => hf ▸ LinearMap.mem_range_self f w)
  have hbij : Function.Bijective f' := by
    constructor
    · intro x y h
      exact hinj (E.injective (congrArg Subtype.val h))
    · intro w
      have hw : (w : L.I → k) ∈ f.range := hf.symm ▸ w.property
      obtain ⟨v, hv⟩ := hw
      exact ⟨v, Subtype.ext hv⟩
  let j := LinearEquiv.ofBijective f' hbij
  refine ⟨E, j, hE, fun _ => rfl, ?_⟩
  intro R g ell v
  dsimp only
  let m := (s.hom.app R g).val.submatrix ULift.up ULift.up
  let w := (frobeniusMatrix p m).mulVec (fun i => algebraMap k R (v i))
  have hx := haction R g ell (purePowerMap k p v)
  change E (contract ell (NonsplitSymmetricPower.act m (extend (purePowerMap k p v)))) =
    PrimitiveLine.orbitCoefficient L.inducedAction R g ell (E (purePowerMap k p v)) at hx
  rw [extend_purePower, hfrob, contract_purePower] at hx
  apply socleInclusion_injective L
  rw [socleInclusion_equivariant L]
  have hinc (z : Fin 2 → k) : socleInclusion L (L.socleBasis.equivFun (j z)) =
      E (purePowerMap k p z) := by
    change (L.socleBasis.equivFun.symm (L.socleBasis.equivFun (j z)) : L.I → k) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  change socleInclusion L (L.socleBasis.equivFun (j (fun i => ell (w i)))) = _
  rw [hinc, hinc]
  exact hx

end RankOne

end
end LinearAlgebraicGroups.Representation.SteinbergTensorProduct

universe v8_closure_f6af02eb42a0df26_u0
theorem _root_.«LinearAlgebraicGroups».«Representation».«SteinbergTensorProduct».«digits» : _root_.«LinearAlgebraicGroups».«Specs».«SteinbergTensorProduct».«Digits».{v8_closure_f6af02eb42a0df26_u0} :=
  @_root_.«LinearAlgebraicGroups».«Representation».«SteinbergTensorProduct».«digits_conditional».{v8_closure_f6af02eb42a0df26_u0} (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«frobeniusSubmodule».{v8_closure_f6af02eb42a0df26_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«inductionIdentification».{v8_closure_f6af02eb42a0df26_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«markedFlagAndSocle».{v8_closure_f6af02eb42a0df26_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«nonsplit».{v8_closure_f6af02eb42a0df26_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«polynomialAction».{v8_closure_f6af02eb42a0df26_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«relativeFrobeniusComparison».{v8_closure_f6af02eb42a0df26_u0})
theorem _root_.«LinearAlgebraicGroups».«Representation».«SteinbergTensorProduct».«rankOneExample» : _root_.«LinearAlgebraicGroups».«Specs».«SteinbergTensorProduct».«RankOneExample».{v8_closure_f6af02eb42a0df26_u0} :=
  @_root_.«LinearAlgebraicGroups».«Representation».«SteinbergTensorProduct».«rankOneExample_conditional».{v8_closure_f6af02eb42a0df26_u0} (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«frobeniusSubmodule».{v8_closure_f6af02eb42a0df26_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«inductionIdentification».{v8_closure_f6af02eb42a0df26_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«markedFlagAndSocle».{v8_closure_f6af02eb42a0df26_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«nonsplit».{v8_closure_f6af02eb42a0df26_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«polynomialAction».{v8_closure_f6af02eb42a0df26_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«relativeFrobeniusComparison».{v8_closure_f6af02eb42a0df26_u0})
theorem _root_.«LinearAlgebraicGroups».«Representation».«SteinbergTensorProduct».«relativeTwistMatrices» : _root_.«LinearAlgebraicGroups».«Specs».«SteinbergTensorProduct».«RelativeTwistMatrices».{v8_closure_f6af02eb42a0df26_u0} :=
  @_root_.«LinearAlgebraicGroups».«Representation».«SteinbergTensorProduct».«relativeTwistMatrices_conditional».{v8_closure_f6af02eb42a0df26_u0} (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«frobeniusSubmodule».{v8_closure_f6af02eb42a0df26_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«inductionIdentification».{v8_closure_f6af02eb42a0df26_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«markedFlagAndSocle».{v8_closure_f6af02eb42a0df26_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«nonsplit».{v8_closure_f6af02eb42a0df26_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«polynomialAction».{v8_closure_f6af02eb42a0df26_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«relativeFrobeniusComparison».{v8_closure_f6af02eb42a0df26_u0})
theorem _root_.«LinearAlgebraicGroups».«Representation».«SteinbergTensorProduct».«tensorProductFormula» : _root_.«LinearAlgebraicGroups».«Specs».«SteinbergTensorProduct».«TensorProductFormula».{v8_closure_f6af02eb42a0df26_u0} :=
  @_root_.«LinearAlgebraicGroups».«Representation».«SteinbergTensorProduct».«tensorProductFormula_conditional».{v8_closure_f6af02eb42a0df26_u0} (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«frobeniusSubmodule».{v8_closure_f6af02eb42a0df26_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«inductionIdentification».{v8_closure_f6af02eb42a0df26_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«markedFlagAndSocle».{v8_closure_f6af02eb42a0df26_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«nonsplit».{v8_closure_f6af02eb42a0df26_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«polynomialAction».{v8_closure_f6af02eb42a0df26_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«relativeFrobeniusComparison».{v8_closure_f6af02eb42a0df26_u0})
