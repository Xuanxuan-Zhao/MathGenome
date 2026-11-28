import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.SerrePresentation
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.ClassicalPositive
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing

/-! At `q = 1`, the positive Serre algebra is the enveloping algebra of the
strictly upper triangular 3 × 3 matrices. -/

namespace LieNotes.Quantum.ClassicalPositive

open SerrePresentation UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v

abbrev positive := Specs.LieNotes.Quantum.ClassicalPositive.positive
abbrev e12 := Specs.LieNotes.Quantum.ClassicalPositive.e12
abbrev e23 := Specs.LieNotes.Quantum.ClassicalPositive.e23
abbrev e13 := Specs.LieNotes.Quantum.ClassicalPositive.e13

variable (A : Type u) [CommRing A]

local notation "S₁" => SerreAlgebra A (1 : Aˣ)
local notation "U" => UniversalEnvelopingAlgebra A (positive A)
local notation "x₁" => x (1 : Aˣ)
local notation "y₁" => y (1 : Aˣ)
local notation "z₁" => z (1 : Aˣ)

theorem positive_le_sl : positive A ≤ LieAlgebra.SpecialLinear.sl (Fin 3) A := by
  intro M hM
  change ∀ i j, j ≤ i → M i j = 0 at hM
  change Matrix.trace M = 0
  exact Finset.sum_eq_zero (fun i _ => hM i i le_rfl)

theorem z_eq_lie : z₁ = ⁅x₁, y₁⁆ := by
  simp [Specs.LieNotes.Quantum.SerrePresentation.z, Ring.lie_def]

private theorem serrePolynomial_one {B : Type v} [Ring B] [Algebra A B] (a b : B) :
    serrePolynomial (1 : Aˣ) a b = ⁅a, ⁅a, b⁆⁆ := by
  unfold serrePolynomial Specs.LieNotes.Quantum.SerrePresentation.serrePolynomial
  simp only [inv_one, Units.val_one, add_smul, one_smul, Ring.lie_def]
  noncomm_ring

private theorem lie_x_z : ⁅x₁, z₁⁆ = 0 := by
  rw [z_eq_lie, ← serrePolynomial_one A]
  exact relationXY_zero 1

private theorem lie_y_z : ⁅y₁, z₁⁆ = 0 := by
  have h : ⁅y₁, ⁅y₁, x₁⁆⁆ = 0 :=
    (serrePolynomial_one A y₁ x₁).symm.trans (relationYX_zero 1)
  rw [z_eq_lie, ← lie_skew x₁ y₁, lie_neg, h, neg_zero]

/-- At the classical parameter the commutator of the generators is central. -/
theorem z_central (a : S₁) : Commute z₁ a := by
  have surj : Function.Surjective (quotientMap (1 : Aˣ)) :=
    Ideal.Quotient.mkₐ_surjective A _
  obtain ⟨b, rfl⟩ := surj a
  induction b using FreeAlgebra.induction with
  | grade0 r =>
    rw [AlgHom.commutes]
    exact (Algebra.commutes r z₁).symm
  | grade1 i =>
    fin_cases i
    · exact (sub_eq_zero.mp (lie_x_z A) : Commute x₁ z₁).symm
    · exact (sub_eq_zero.mp (lie_y_z A) : Commute y₁ z₁).symm
  | mul b c hb hc =>
    rw [map_mul]
    exact hb.mul_right hc
  | add b c hb hc =>
    rw [map_add]
    exact hb.add_right hc

private theorem lie_e12_e23 : ⁅e12 A, e23 A⁆ = e13 A := by
  apply Subtype.ext
  change Matrix.single (0 : Fin 3) 1 (1 : A) * Matrix.single 1 2 1 -
    Matrix.single 1 2 1 * Matrix.single 0 1 1 = Matrix.single 0 2 1
  simp (disch := decide) only [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne,
    mul_one, sub_zero]

private theorem lie_e12_e13 : ⁅e12 A, e13 A⁆ = 0 := by
  apply Subtype.ext
  change Matrix.single (0 : Fin 3) 1 (1 : A) * Matrix.single 0 2 1 -
    Matrix.single 0 2 1 * Matrix.single 0 1 1 = 0
  simp (disch := decide) only [Matrix.single_mul_single_of_ne, sub_self]

private theorem lie_e23_e13 : ⁅e23 A, e13 A⁆ = 0 := by
  apply Subtype.ext
  change Matrix.single (1 : Fin 3) 2 (1 : A) * Matrix.single 0 2 1 -
    Matrix.single 0 2 1 * Matrix.single 1 2 1 = 0
  simp (disch := decide) only [Matrix.single_mul_single_of_ne, sub_self]

private theorem expand_matrix (M : positive A) :
    M = M.1 0 1 • e12 A + M.1 1 2 • e23 A + M.1 0 2 • e13 A := by
  have hM : ∀ i j, j ≤ i → M.1 i j = 0 := M.2
  apply Subtype.ext
  ext i j
  change M.1 i j = M.1 0 1 * Matrix.single (0 : Fin 3) 1 (1 : A) i j +
    M.1 1 2 * Matrix.single 1 2 1 i j + M.1 0 2 * Matrix.single 0 2 1 i j
  fin_cases i <;> fin_cases j <;>
    simp (disch := decide) only [Matrix.single_apply, ite_eq_left, ite_eq_right, mul_one,
      mul_zero, zero_add, add_zero, hM] <;> rfl

private theorem lie_of_linear_combinations {L : Type v} [LieRing L] [LieAlgebra A L]
    (a b c : L) (hab : ⁅a, b⁆ = c) (hac : ⁅a, c⁆ = 0) (hbc : ⁅b, c⁆ = 0)
    (r s t r' s' t' : A) :
    ⁅r • a + s • b + t • c, r' • a + s' • b + t' • c⁆ = (r * s' - s * r') • c := by
  have hba : ⁅b, a⁆ = -c := by rw [← lie_skew b a, hab]
  have hca : ⁅c, a⁆ = 0 := by rw [← lie_skew c a, hac, neg_zero]
  have hcb : ⁅c, b⁆ = 0 := by rw [← lie_skew c b, hbc, neg_zero]
  simp only [add_lie, lie_add, smul_lie, lie_smul, lie_self, hab, hac, hbc, hba, hca, hcb,
    smul_zero, add_zero, zero_add, smul_smul, smul_neg]
  rw [mul_comm r' s, mul_comm s' r, add_comm, ← sub_eq_add_neg, sub_smul]

private def preimages : positive A →ₗ[A] S₁ where
  toFun M := M.1 0 1 • x₁ + M.1 1 2 • y₁ + M.1 0 2 • z₁
  map_add' M N := by
    change ((M.1 0 1 + N.1 0 1) • x₁ + (M.1 1 2 + N.1 1 2) • y₁ +
      (M.1 0 2 + N.1 0 2) • z₁) = _
    simp only [add_smul]
    abel
  map_smul' r M := by
    change (r * M.1 0 1) • x₁ + (r * M.1 1 2) • y₁ + (r * M.1 0 2) • z₁ =
      r • (M.1 0 1 • x₁ + M.1 1 2 • y₁ + M.1 0 2 • z₁)
    simp only [smul_add, smul_smul]

private theorem preimages_e12 : preimages A (e12 A) = x₁ := by
  change Matrix.single (0 : Fin 3) 1 (1 : A) 0 1 • x₁ +
    Matrix.single (0 : Fin 3) 1 (1 : A) 1 2 • y₁ +
    Matrix.single (0 : Fin 3) 1 (1 : A) 0 2 • z₁ = x₁
  simp (disch := decide) only [Matrix.single_apply_same, Matrix.single_apply_of_ne,
    one_smul, zero_smul, add_zero]

private theorem preimages_e23 : preimages A (e23 A) = y₁ := by
  change Matrix.single (1 : Fin 3) 2 (1 : A) 0 1 • x₁ +
    Matrix.single (1 : Fin 3) 2 (1 : A) 1 2 • y₁ +
    Matrix.single (1 : Fin 3) 2 (1 : A) 0 2 • z₁ = y₁
  simp (disch := decide) only [Matrix.single_apply_same, Matrix.single_apply_of_ne,
    one_smul, zero_smul, add_zero, zero_add]

private theorem preimages_e13 : preimages A (e13 A) = z₁ := by
  change Matrix.single (0 : Fin 3) 2 (1 : A) 0 1 • x₁ +
    Matrix.single (0 : Fin 3) 2 (1 : A) 1 2 • y₁ +
    Matrix.single (0 : Fin 3) 2 (1 : A) 0 2 • z₁ = z₁
  simp (disch := decide) only [Matrix.single_apply_same, Matrix.single_apply_of_ne,
    one_smul, zero_smul, add_zero, zero_add]

private def preimagesLie : positive A →ₗ⁅A⁆ S₁ where
  __ := preimages A
  map_lie' {M N} := by
    change preimages A ⁅M, N⁆ = ⁅preimages A M, preimages A N⁆
    have h : ⁅M, N⁆ = (M.1 0 1 * N.1 1 2 - M.1 1 2 * N.1 0 1) • e13 A := by
      conv_lhs => rw [expand_matrix A M, expand_matrix A N]
      exact lie_of_linear_combinations A _ _ _ (lie_e12_e23 A) (lie_e12_e13 A)
        (lie_e23_e13 A) _ _ _ _ _ _
    rw [h, map_smul, preimages_e13]
    exact (lie_of_linear_combinations A x₁ y₁ z₁ (z_eq_lie A).symm
      (lie_x_z A) (lie_y_z A) _ _ _ _ _ _).symm

private def toSerre : U →ₐ[A] S₁ := UniversalEnvelopingAlgebra.lift A (preimagesLie A)

private def images : Fin 2 → U :=
  Fin.cases (ι A (e12 A)) (fun _ => ι A (e23 A))

private theorem serre_images (M N : positive A) (h : ⁅M, ⁅M, N⁆⁆ = 0) :
    serrePolynomial (1 : Aˣ) (ι A M) (ι A N) = 0 := by
  rw [serrePolynomial_one A, ← (ι A).map_lie M N, ← (ι A).map_lie M ⁅M, N⁆, h, map_zero]

private theorem serre_images_xy : serrePolynomial (1 : Aˣ) (images A 0) (images A 1) = 0 :=
  serre_images A (e12 A) (e23 A) (by rw [lie_e12_e23, lie_e12_e13])

private theorem serre_images_yx : serrePolynomial (1 : Aˣ) (images A 1) (images A 0) = 0 :=
  serre_images A (e23 A) (e12 A) (by
    rw [← lie_skew (e23 A) (e12 A), lie_e12_e23, lie_neg, lie_e23_e13, neg_zero])

private def toEnveloping : S₁ →ₐ[A] U :=
  SerrePresentation.lift 1 (images A) (serre_images_xy A) (serre_images_yx A)

private theorem toEnveloping_x : toEnveloping A x₁ = ι A (e12 A) :=
  lift_generator 1 (images A) (serre_images_xy A) (serre_images_yx A) 0

private theorem toEnveloping_y : toEnveloping A y₁ = ι A (e23 A) :=
  lift_generator 1 (images A) (serre_images_xy A) (serre_images_yx A) 1

private theorem toEnveloping_z : toEnveloping A z₁ = ι A (e13 A) := by
  rw [z_eq_lie]
  change (toEnveloping A : S₁ →ₗ⁅A⁆ U) ⁅x₁, y₁⁆ = _
  rw [LieHom.map_lie]
  change ⁅toEnveloping A x₁, toEnveloping A y₁⁆ = _
  rw [toEnveloping_x, toEnveloping_y, ← (ι A).map_lie, lie_e12_e23]

private theorem toSerre_ι (M : positive A) :
    toSerre A (ι A M) = preimages A M :=
  lift_ι_apply A (preimagesLie A) M

private theorem serre_inverse : (toSerre A).comp (toEnveloping A) = AlgHom.id A S₁ := by
  apply SerrePresentation.hom_ext
  intro i
  fin_cases i
  · change toSerre A (toEnveloping A x₁) = x₁
    rw [toEnveloping_x, toSerre_ι, preimages_e12]
  · change toSerre A (toEnveloping A y₁) = y₁
    rw [toEnveloping_y, toSerre_ι, preimages_e23]

private theorem enveloping_inverse : (toEnveloping A).comp (toSerre A) = AlgHom.id A U := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro M
  change toEnveloping A (toSerre A (ι A M)) = ι A M
  rw [toSerre_ι]
  conv_rhs => rw [expand_matrix A M]
  simp only [preimages, LinearMap.coe_mk, AddHom.coe_mk, map_add, map_smul,
    toEnveloping_x, toEnveloping_y, toEnveloping_z]

/-- The isomorphism sends the three positive generators to the indicated matrix units
in the universal enveloping algebra. -/
theorem classical_specialization :
    ∃ e : S₁ ≃ₐ[A] U,
      e x₁ = ι A (e12 A) ∧ e y₁ = ι A (e23 A) ∧ e z₁ = ι A (e13 A) :=
  ⟨AlgEquiv.ofAlgHom (toEnveloping A) (toSerre A) (enveloping_inverse A) (serre_inverse A),
    toEnveloping_x A, toEnveloping_y A, toEnveloping_z A⟩

end LieNotes.Quantum.ClassicalPositive
