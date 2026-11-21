import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SymplecticAdjointSurjectivity
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalRootsC
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.AutomorphismDecomposition
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Linarith
import Batteries.Tactic.OpenPrivate

namespace LieAlgebrasAndRepresentations.SymplecticAdjointSurjectivity

open Specs.LieAlgebrasAndRepresentations
open Specs.LieAlgebrasAndRepresentations.ClassicalRootsC
open Specs.LieAlgebrasAndRepresentations.SymplecticAdjointSurjectivity
open Module NormedSpace Matrix
open scoped Matrix Norms.Operator

noncomputable section

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

private def longRoot {n : ℕ} (i : Fin n) : Weight n := (2 : ℂ) • eps i

private def chamberPoint (n : ℕ) : V n := fun i => (n : ℂ) - (i.val : ℂ)

private def chamberValue {n : ℕ} (α : Weight n) : ℝ := (α (chamberPoint n)).re

private theorem chamberValue_long {n : ℕ} (i : Fin n) :
    0 < chamberValue (longRoot i) := by
  have hi : (i.val : ℝ) < n := by exact_mod_cast i.isLt
  simp [chamberValue, chamberPoint, longRoot, eps, Complex.mul_re]

private theorem chamberValue_sum {n : ℕ} (i j : Fin n) :
    0 < chamberValue (eps i + eps j) := by
  have hi : (i.val : ℝ) < n := by exact_mod_cast i.isLt
  have hj : (j.val : ℝ) < n := by exact_mod_cast j.isLt
  simp [chamberValue, chamberPoint, eps]
  linarith

private theorem chamberValue_sub {n : ℕ} (i j : Fin n) :
    0 < chamberValue (eps i - eps j) ↔ i < j := by
  simp [chamberValue, chamberPoint, eps, sub_pos]

private theorem chamberValue_neg {n : ℕ} (α : Weight n) :
    chamberValue (-α) = -chamberValue α := by simp [chamberValue]

private theorem chamberValue_regular {n : ℕ} {α : Weight n} (hα : α ∈ listedRoots n) :
    chamberValue α ≠ 0 := by
  rcases hα with ⟨i, rfl | rfl⟩ | ⟨i, j, hij, rfl | rfl | rfl | rfl⟩
  · exact (chamberValue_long i).ne'
  · rw [chamberValue_neg]
    exact neg_ne_zero.mpr (chamberValue_long i).ne'
  · exact ((chamberValue_sub i j).mpr hij).ne'
  · rw [chamberValue_neg]
    exact neg_ne_zero.mpr ((chamberValue_sub i j).mpr hij).ne'
  · exact (chamberValue_sum i j).ne'
  · rw [chamberValue_neg]
    exact neg_ne_zero.mpr (chamberValue_sum i j).ne'

private theorem long_mem {n : ℕ} (i : Fin n) : longRoot i ∈ listedRoots n :=
  Or.inl ⟨i, Or.inl rfl⟩

private theorem neg_long_mem {n : ℕ} (i : Fin n) : -longRoot i ∈ listedRoots n :=
  Or.inl ⟨i, Or.inr rfl⟩

private theorem root_coordinate_bound {n : ℕ} {α : Weight n} (hα : α ∈ listedRoots n)
    (i : Fin n) : (coordinates α i).re ≤ 2 ∧ ((coordinates α i).re = 2 → α = longRoot i) := by
  rcases hα with ⟨j, rfl | rfl⟩ | ⟨j, k, hjk, rfl | rfl | rfl | rfl⟩
  · by_cases h : i = j
    · subst j
      norm_num [coordinates, eps, longRoot]
    · norm_num [coordinates, eps, longRoot, Pi.single_apply, h, Ne.symm h]
  · by_cases h : i = j
    · subst j
      norm_num [coordinates, eps, longRoot]
    · norm_num [coordinates, eps, longRoot, Pi.single_apply, h, Ne.symm h]
  all_goals
    have hne : j ≠ k := hjk.ne
    by_cases h₁ : i = j <;> by_cases h₂ : i = k <;>
      simp_all [coordinates, eps, eq_comm] <;> norm_num

/-- A positive long root is the unique root at the maximum of its coordinate. -/
private theorem long_extreme {n : ℕ} (i : Fin n) {β γ : Weight n}
    (hβ : β ∈ listedRoots n) (hγ : γ ∈ listedRoots n)
    (h : β + γ = (2 : ℂ) • longRoot i) : β = γ := by
  have hs := congrArg (fun α : Weight n => (coordinates α i).re) h
  have hβi := root_coordinate_bound hβ i
  have hγi := root_coordinate_bound hγ i
  have hs' : (coordinates β i).re + (coordinates γ i).re = 4 := by
    norm_num [coordinates, eps, longRoot, Complex.mul_re] at hs ⊢
    exact hs
  exact (hβi.2 (by linarith [hβi.1, hγi.1])).trans
    (hγi.2 (by linarith [hβi.1, hγi.1])).symm

private theorem signed_long_ne {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {β γ : Weight n} (hβ : β = longRoot i ∨ β = -longRoot i)
    (hγ : γ = longRoot j ∨ γ = -longRoot j) : β ≠ γ := by
  intro h
  have he := congrArg (fun α : Weight n => α (Pi.single i 1)) h
  rcases hβ with rfl | rfl <;> rcases hγ with rfl | rfl <;>
    norm_num [longRoot, eps, Pi.single_apply, hij, Ne.symm hij] at he

/-- The short roots are midpoints of distinct roots, so a positive root with
the extremal property must be a positive long root. -/
private theorem long_of_positive_extreme {n : ℕ} {α : Weight n}
    (hα : α ∈ listedRoots n) (hpos : 0 < chamberValue α)
    (he : ∀ β ∈ listedRoots n, ∀ γ ∈ listedRoots n,
      β + γ = (2 : ℂ) • α → β = γ) : ∃ i, α = longRoot i := by
  rcases hα with ⟨i, rfl | rfl⟩ | ⟨i, j, hij, rfl | rfl | rfl | rfl⟩
  · exact ⟨i, rfl⟩
  · rw [show -((2 : ℂ) • eps i) = -longRoot i from rfl, chamberValue_neg] at hpos
    exact False.elim ((not_lt_of_ge (neg_nonpos.mpr (chamberValue_long i).le)) hpos)
  · exact False.elim (signed_long_ne hij.ne (Or.inl rfl) (Or.inr rfl)
      (he _ (long_mem i) _ (neg_long_mem j) (by simp [longRoot, sub_eq_add_neg])))
  · exact False.elim (signed_long_ne hij.ne (Or.inr rfl) (Or.inl rfl)
      (he _ (neg_long_mem i) _ (long_mem j) (by simp [longRoot, sub_eq_add_neg, add_comm])))
  · exact False.elim (signed_long_ne hij.ne (Or.inl rfl) (Or.inl rfl)
      (he _ (long_mem i) _ (long_mem j) (by simp [longRoot, smul_add])))
  · exact False.elim (signed_long_ne hij.ne (Or.inr rfl) (Or.inr rfl)
      (he _ (neg_long_mem i) _ (neg_long_mem j) (by simp [longRoot, smul_add, add_comm])))

/-- A complex linear root permutation preserving this positive system fixes
each positive long root, since it induces an increasing permutation of
the diagonal coordinates. These roots form a basis of the dual Cartan. -/
private theorem root_permutation_eq_one {n : ℕ} (T : Weight n ≃ₗ[ℂ] Weight n)
    (hroots : ∀ α, T α ∈ listedRoots n ↔ α ∈ listedRoots n)
    (hpos : ∀ α ∈ listedRoots n, 0 < chamberValue α → 0 < chamberValue (T α)) :
    ∀ α, T α = α := by
  have hi (i : Fin n) : ∃ j, T (longRoot i) = longRoot j := by
    refine long_of_positive_extreme ((hroots _).mpr (long_mem i))
      (hpos _ (long_mem i) (chamberValue_long i)) ?_
    intro β hβ γ hγ h
    obtain ⟨b, rfl⟩ := T.surjective β
    obtain ⟨c, rfl⟩ := T.surjective γ
    have hs : b + c = (2 : ℂ) • longRoot i := T.injective (by simpa only [map_add, map_smul] using h)
    rw [long_extreme i ((hroots b).mp hβ) ((hroots c).mp hγ) hs]
  choose σ hσ using hi
  have hε (i : Fin n) : T (eps i) = eps (σ i) := by
    apply smul_right_injective (Weight n) (show (2 : ℂ) ≠ 0 by norm_num)
    simpa only [longRoot, map_smul] using hσ i
  have hσmono : StrictMono σ := by
    intro i j hij
    have hp := hpos _ (Or.inr ⟨i, j, hij, Or.inl rfl⟩) ((chamberValue_sub i j).mpr hij)
    rw [map_sub, hε, hε] at hp
    exact (chamberValue_sub _ _).mp hp
  have hσid (i : Fin n) : σ i = i := hσmono.apply_eq
  let b := (Pi.basisFun ℂ (Fin n)).dualBasis
  have hb (i : Fin n) : b i = eps i := by
    ext t
    simp [b, eps]
  have heq : T.toLinearMap = LinearMap.id := b.ext (fun i => by
    change T (b i) = b i
    rw [hb, hε, hσid])
  exact fun α => LinearMap.congr_fun heq α


section MatrixExponentials

open Specs.LieAlgebrasAndRepresentations.RegularSemisimple (algebraNorm)
open Specs.LieAlgebrasAndRepresentations.CartanConjugacy (exponentialOperator)
open private exp_intertwine from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.AutomorphismDecomposition

set_option backward.isDefEq.respectTransparency false in
private theorem exp_mem_symplectic {n : ℕ} (X : sp n) :
    exp (X : Mat n) ∈ symplecticGroup (Fin n) ℂ := by
  apply SymplecticGroup.mem_iff'.mpr
  rw [← Matrix.exp_transpose]
  let J := Matrix.J (Fin n) ℂ
  have hX : (X : Mat n)ᵀ * J = J * -(X : Mat n) := by
    have hm : (X : Mat n) ∈ skewAdjointMatricesLieSubalgebra J := X.property
    exact (mem_skewAdjointMatricesSubmodule _ _).mp ((mem_skewAdjointMatricesLieSubalgebra _ _).mp hm)
  have h : SemiconjBy J (X : Mat n) (-(X : Mat n)ᵀ) := by
    change J * (X : Mat n) = (-(X : Mat n)ᵀ) * J
    rw [Matrix.neg_mul, hX, Matrix.mul_neg, neg_neg]
  change exp ((X : Mat n)ᵀ) * J * exp (X : Mat n) = J
  simpa only [neg_neg] using h.exp_neg_mul_mul_exp_eq_self

set_option backward.isDefEq.respectTransparency false in
private theorem exponentialOperator_matrix_of_intertwines {n : ℕ}
    {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (j : L →ₗ[ℂ] Mat n) (X Y : L)
    (hj : ∀ y, j ⁅X, y⁆ = j X * j y - j y * j X) :
    j (exponentialOperator X Y) = exp (j X) * j Y * exp (-(j X)) := by
  let M := Mat n
  let : NormedRing M := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℂ M := Matrix.linftyOpNormedAlgebra
  let : NormedRing (M →L[ℂ] M) := ContinuousLinearMap.toNormedRing
  let : Algebra ℚ (M →L[ℂ] M) := RestrictScalars.algebra ℚ ℂ _
  let : NormedAlgebra ℚ (M →L[ℂ] M) := NormedAlgebra.restrictScalars ℚ ℂ _
  let : NormedAddCommGroup L := algebraNorm
  let : NormedSpace ℂ L := NormedSpace.induced ℂ L
    (Fin (finrank ℂ L) → ℂ) (finBasis ℂ L).equivFun
  let left : M →+* (M →L[ℂ] M) :=
    { toFun := ContinuousLinearMap.mul ℂ M
      map_one' := ContinuousLinearMap.ext fun y => one_mul y
      map_zero' := ContinuousLinearMap.ext fun y => zero_mul y
      map_add' a b := ContinuousLinearMap.ext fun y => add_mul a b y
      map_mul' a b := ContinuousLinearMap.ext fun y => mul_assoc a b y }
  let rightTranspose : M →+* (M →L[ℂ] M) :=
    { toFun := fun a => (ContinuousLinearMap.mul ℂ M).flip aᵀ
      map_one' := ContinuousLinearMap.ext fun y => by
        change y * (1 : M)ᵀ = y
        rw [transpose_one, mul_one]
      map_zero' := ContinuousLinearMap.ext fun y => by
        change y * (0 : M)ᵀ = 0
        rw [transpose_zero, mul_zero]
      map_add' := by
        intro a b
        apply ContinuousLinearMap.ext
        intro y
        change y * (a + b)ᵀ = y * aᵀ + y * bᵀ
        rw [transpose_add, mul_add]
      map_mul' := by
        intro a b
        apply ContinuousLinearMap.ext
        intro y
        change y * (a * b)ᵀ = (y * bᵀ) * aᵀ
        rw [transpose_mul, mul_assoc] }
  have hleft : Continuous left := (ContinuousLinearMap.mul ℂ M).continuous
  have hright : Continuous rightTranspose :=
    (ContinuousLinearMap.mul ℂ M).flip.continuous.comp continuous_id.matrix_transpose
  let A := left (j X)
  let B := rightTranspose (-(j X))ᵀ
  have hB (y : M) : B y = y * -(j X) := by
    change y * (-(j X))ᵀᵀ = _
    rw [transpose_transpose]
  have hcomm : Commute A B := by
    apply ContinuousLinearMap.ext
    intro y
    change A (B y) = B (A y)
    rw [hB, hB]
    exact (mul_assoc _ _ _).symm
  let D := LinearMap.toContinuousLinearMap (LieAlgebra.ad ℂ L X)
  let f : L →L[ℂ] M := LinearMap.toContinuousLinearMap j
  have hf (y : L) : f (D y) = (A + B) (f y) := by
    rw [_root_.add_apply, hB]
    change j ⁅X, y⁆ = j X * j y + j y * -(j X)
    rw [hj, Matrix.mul_neg, sub_eq_add_neg]
  have hAexp (y : M) : exp A y = exp (j X) * y := by
    rw [show exp A = left (exp (j X)) from (map_exp left hleft _).symm]
    rfl
  have hBexp (y : M) : exp B y = y * exp (-(j X)) := by
    rw [show exp B = rightTranspose ((exp (-(j X)))ᵀ) from by
      rw [← Matrix.exp_transpose]
      exact (map_exp rightTranspose hright _).symm]
    change y * (exp (-(j X)))ᵀᵀ = _
    rw [transpose_transpose]
  have h := exp_intertwine D (A + B) f hf Y
  have hAdd : exp (A + B) = exp A * exp B := NormedSpace.exp_add_of_commute hcomm
  have h' : f (exp D Y) = exp (A + B) (f Y) := h
  rw [hAdd] at h'
  change f (exp D Y) = exp A (exp B (f Y)) at h'
  rw [hAexp, hBexp] at h'
  exact h'.trans (mul_assoc _ _ _).symm

private theorem exponentialOperator_matrix {n : ℕ} (X Y : sp n) :
    (exponentialOperator X Y : Mat n) =
      exp (X : Mat n) * (Y : Mat n) * exp (-(X : Mat n)) :=
  exponentialOperator_matrix_of_intertwines (sp n).toSubmodule.subtype X Y (fun _ => rfl)

end MatrixExponentials

section InnerLifts

open Specs.LieAlgebrasAndRepresentations.AutomorphismDecomposition
open Specs.LieAlgebrasAndRepresentations.CartanConjugacy (exponentialOperator)

private abbrev Sp (n : ℕ) := symplecticGroup (Fin n) ℂ

private theorem coe_inv_mul {n : ℕ} (A : Sp n) :
    ((A⁻¹ : Sp n) : Mat n) * (A : Mat n) = 1 :=
  congrArg (fun B : Sp n => (B : Mat n)) (inv_mul_cancel A)

private def liftable (n : ℕ) : Subgroup (Aut (sp n)) where
  carrier := {g | ∃ A : Sp n, ∀ Y : sp n,
    (g.val Y : Mat n) = (A : Mat n) * (Y : Mat n) * ((A⁻¹ : Sp n) : Mat n)}
  one_mem' := ⟨1, fun Y => by
    change (Y : Mat n) = ((1 : Sp n) : Mat n) * (Y : Mat n) * (((1 : Sp n)⁻¹ : Sp n) : Mat n)
    rw [inv_one]
    change (Y : Mat n) = 1 * (Y : Mat n) * 1
    rw [one_mul, mul_one]⟩
  mul_mem' := by
    rintro g h ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A * B, fun Y => ?_⟩
    change (g.val (h.val Y) : Mat n) = _
    rw [hA, hB, _root_.mul_inv_rev]
    change (A : Mat n) * ((B : Mat n) * (Y : Mat n) * ((B⁻¹ : Sp n) : Mat n)) *
      ((A⁻¹ : Sp n) : Mat n) =
      ((A : Mat n) * (B : Mat n)) * (Y : Mat n) *
        (((B⁻¹ : Sp n) : Mat n) * ((A⁻¹ : Sp n) : Mat n))
    simp only [mul_assoc]
  inv_mem' := by
    rintro g ⟨A, hA⟩
    refine ⟨A⁻¹, fun Y => ?_⟩
    have h := hA (g.val.symm Y)
    rw [LinearEquiv.apply_symm_apply] at h
    change (g.val.symm Y : Mat n) = ((A⁻¹ : Sp n) : Mat n) * (Y : Mat n) *
      ((A⁻¹⁻¹ : Sp n) : Mat n)
    rw [inv_inv, h, ← mul_assoc, ← mul_assoc, coe_inv_mul,
      one_mul, mul_assoc, coe_inv_mul, mul_one]

private theorem inner_le_liftable (n : ℕ) : inner (sp n) ≤ liftable n := by
  rw [AutomorphismDecomposition.innerGenerated (sp n)]
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨X, hX⟩
  let A : Sp n := ⟨exp (X : Mat n), exp_mem_symplectic X⟩
  refine ⟨A, fun Y => ?_⟩
  rw [SymplecticGroup.coe_inv']
  change (g.val Y : Mat n) = exp (X : Mat n) * (Y : Mat n) * (exp (X : Mat n))⁻¹
  rw [← Matrix.exp_neg, ← exponentialOperator_matrix, ← LinearMap.congr_fun hX Y]
  rfl

end InnerLifts

section Diagram

open Specs.LieAlgebrasAndRepresentations.AutomorphismDecomposition
open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)
open Specs.LieAlgebrasAndRepresentations.VermaModules (Direction Regular)
open Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient (Normalized)
open Specs.LieAlgebrasAndRepresentations.RealRootSpace
open Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSet_value rootSpace_value)
open Specs.LieAlgebrasAndRepresentations.MaximalTori (IsMaximalToral_value)
open private asLieEquiv basedRootSystem rootTransport_apply rootTransport_mem rootTransport
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.AutomorphismDecomposition
open private direction_vector simple_equiv
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FiniteHighestWeightExistence

private theorem positive_value_of_simple_permutation {L : Type*}
    [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (hss : SolvableRadical.IsSemisimple_value ℂ L)
    {H : LieSubalgebra ℂ L} (hH : IsMaximalToral_value H) {φ : Direction H}
    (hφ : Regular H φ) (t : Dual ℂ H ≃ₗ[ℂ] Dual ℂ H)
    (ht : ∀ α, t α ∈ rootSet_value H ↔ α ∈ rootSet_value H)
    (p : Equiv.Perm (simple H φ)) (hs : ∀ i : simple H φ, t i.val = (p i).val)
    {α : Dual ℂ H} (hα : α ∈ rootSet_value H) (hαpos : 0 < φ α) : 0 < φ (t α) := by
  let d := RealRootSpace.realization_of_maximalToral hss H hH
  let : Fact (Realization H) := ⟨d⟩
  let := d.normedAddCommGroup
  let := d.innerProductSpace
  obtain ⟨v, hv⟩ := direction_vector d φ
  obtain ⟨q, hq⟩ := simple_equiv d φ hv
  let x := rootRestriction H α
  have hx : d.j x = α := d.extension_root α hα
  have hxpos : x ∈ positiveRoots (realRoots H) v :=
    ⟨⟨α, hα, rfl⟩, by rwa [← hv, hx]⟩
  have hxmem := positive_mem_closure_simple d.root_system.toRootAxioms v hxpos
  have hn (y : E H) (hy : y ∈ AddSubmonoid.closure (simpleRoots (realRoots H) v)) :
      0 ≤ φ (t (d.j y)) := by
    induction hy using AddSubmonoid.closure_induction with
    | mem z hz =>
      obtain ⟨i, hi⟩ := q.surjective ⟨z, hz⟩
      have he : d.j z = i.val := by simpa only [hi] using hq i
      rw [he, hs]
      exact (p i).property.1.2.le
    | zero => simp
    | add a b ha hb hpa hpb =>
      simp only [map_add]
      exact add_nonneg hpa hpb
  have h := hn x hxmem
  rw [hx] at h
  exact lt_of_le_of_ne h (hφ _ ((ht α).mpr hα)).symm

private theorem root_coordinates {n : ℕ} {H : LieSubalgebra ℂ (sp n)}
    (e : V n ≃ₗ[ℂ] H)
    (he : ∀ α : Weight n,
      ((LieModule.weightSpace (sp n) (fun h : H => α (e.symm h))).toSubmodule.map
        (sp n).toSubmodule.subtype) = Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.rootSpace α)
    (a : Dual ℂ H) : a ∈ rootSet_value H ↔ e.dualMap a ∈ listedRoots n := by
  rw [← ClassicalRootsC.roots n]
  have hf : (fun h : H => (e.dualMap a) (e.symm h)) = a := by
    funext h
    change a (e (e.symm h)) = a h
    rw [e.apply_symm_apply]
  have hspace : (rootSpace_value H a).map (sp n).toSubmodule.subtype =
      Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.rootSpace (e.dualMap a) := by
    simpa only [rootSpace_value, hf] using he (e.dualMap a)
  change (a ≠ 0 ∧ rootSpace_value H a ≠ ⊥) ↔
    (e.dualMap a ≠ 0 ∧ Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.rootSpace (e.dualMap a) ≠ ⊥)
  rw [← hspace, LinearEquiv.map_ne_zero_iff]
  refine and_congr_right (fun _ => ?_)
  have hi := Submodule.map_injective_of_injective
    (show Function.Injective (sp n).toSubmodule.subtype from Subtype.coe_injective)
  rw [← Submodule.map_bot (sp n).toSubmodule.subtype, hi.ne_iff]

set_option maxHeartbeats 700000 in
/-- The diagram action for the decreasing diagonal chamber is trivial. -/
private theorem aut_mem_inner {n : ℕ} (hss : SolvableRadical.IsSemisimple_value ℂ (sp n))
    (G : Aut (sp n)) : G ∈ inner (sp n) := by
  classical
  obtain ⟨H, hcartan, e, _, hrootSpace⟩ := ClassicalRootsC.cartan_transport n
  have hH := (isCartan_iff_maximal_toral hss H).mp
    ((isCartan_iff_isCartanSubalgebra H).mpr hcartan)
  let E₀ := e.dualMap
  have hR (a : Dual ℂ H) : a ∈ rootSet_value H ↔ E₀ a ∈ listedRoots n :=
    root_coordinates e hrootSpace a
  let φ : Direction H :=
    Complex.reLm.comp ((Dual.eval ℂ H (e (chamberPoint n))).restrictScalars ℝ)
  have hφ : Regular H φ := fun a ha => chamberValue_regular ((hR a).mp ha)
  have hφval (a : Dual ℂ H) : φ a = chamberValue (E₀ a) := rfl
  have ht (i : simple H φ) := exists_root_triple hss H hH i.val i.property.1.1
  choose u v hu hv hnu hnv hbr _ _ using ht
  have hnorm : Normalized H φ u v := fun i => ⟨hu i, hv i, hnu i, hnv i, hbr i⟩
  obtain ⟨_, s, hs, _, hbij⟩ := AutomorphismDecomposition.decomposition hss H hH φ hφ u v hnorm
  obtain ⟨⟨k, p⟩, hpG⟩ := hbij.surjective G
  have hp : p = 1 := by
    let d := RealRootSpace.realization_of_maximalToral hss H hH
    let := d.normedAddCommGroup
    let := d.innerProductSpace
    obtain ⟨_, _, _, c, _, _, hc, _⟩ := basedRootSystem d hφ
    let g := asLieEquiv (s p)
    let U := c.equiv c p.val
    have hU' : g.toLinearMap.comp H.toSubmodule.subtype =
        H.toSubmodule.subtype.comp U.toLinearMap := by
      apply c.ext
      intro i
      change g (c i : sp n) = (U (c i) : sp n)
      rw [Basis.equiv_apply, (hc i).2.1, (hc (p.val i)).2.1]
      exact (hs p i).2.2
    have hU (x : H) : g (x : sp n) = (U x : sp n) := LinearMap.congr_fun hU' x
    have hgH : H.map g.toLieHom = H := by
      apply le_antisymm
      · rintro _ ⟨y, hy, rfl⟩
        change g y ∈ H
        rw [hU ⟨y, hy⟩]
        exact (U ⟨y, hy⟩).property
      · intro y hy
        let x := U.symm ⟨y, hy⟩
        refine ⟨(x : sp n), x.property, ?_⟩
        change g (x : sp n) = y
        rw [hU, U.apply_symm_apply]
    let t := rootTransport g hgH
    have htroot (a : Dual ℂ H) : t a ∈ rootSet_value H ↔ a ∈ rootSet_value H :=
      rootTransport_mem g hgH a
    have hts (i : simple H φ) : t i.val = (p.val i).val := by
      apply c.ext
      intro j
      obtain ⟨j, rfl⟩ := p.val.surjective j
      have hj : (g.ofSubalgebras H H hgH).toLinearEquiv (c j) = c (p.val j) := by
        apply Subtype.ext
        have hUj : U (c j) = c (p.val j) := by simp [U]
        exact (hU (c j)).trans (congrArg Subtype.val hUj)
      change (rootTransport g hgH i.val) (c (p.val j)) = (p.val i).val (c (p.val j))
      conv_lhs => rw [← hj, rootTransport_apply]
      rw [(hc j).2.1, (hc (p.val j)).2.1]
      exact (p.property j i).symm
    let T := (E₀.symm.trans t).trans E₀
    have hTR (a : Weight n) : T a ∈ listedRoots n ↔ a ∈ listedRoots n := by
      change E₀ (t (E₀.symm a)) ∈ listedRoots n ↔ _
      rw [← hR, htroot, hR, E₀.apply_symm_apply]
    have hTP (a : Weight n) (ha : a ∈ listedRoots n) (hap : 0 < chamberValue a) :
        0 < chamberValue (T a) := by
      have ha' : E₀.symm a ∈ rootSet_value H := (hR _).mpr (by simpa using ha)
      have hap' : 0 < φ (E₀.symm a) := by rwa [hφval, E₀.apply_symm_apply]
      exact positive_value_of_simple_permutation hss hH hφ t htroot p.val hts ha' hap'
    have hTid := root_permutation_eq_one T hTR hTP
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply Subtype.ext
    have hfix : E₀ (t i.val) = E₀ i.val := by simpa [T] using hTid (E₀ i.val)
    exact (hts i).symm.trans (E₀.injective hfix)
  change k.val * s p = G at hpG
  rw [hp, map_one, mul_one] at hpG
  exact hpG ▸ k.property

end Diagram

/-- Every complex Lie automorphism of the stated symplectic matrix algebra
is conjugation by a complex symplectic matrix. -/
theorem adjointSurjectivity : adjointSurjectivityType := by
  intro n _ hss g
  exact inner_le_liftable n (aut_mem_inner hss ⟨g.toLinearEquiv, g.map_lie⟩)

end
end LieAlgebrasAndRepresentations.SymplecticAdjointSurjectivity
