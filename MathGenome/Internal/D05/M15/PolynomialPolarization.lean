import MathGenome.Internal.Specs.D05.M15.PolynomialPolarization
import MathGenome.Internal.D05.M15.PolynomialBridge
import MathGenome.Internal.D05.M15.MultilinearDimension
import MathGenome.Internal.D05.M15.PolynomialPolarization.SubsetIdentity

noncomputable section
namespace D05.M15.PolynomialPolarization
open scoped BigOperators
open Specs.D05.M15.PolynomialPolarization

abbrev diagonalPolynomial := @Specs.D05.M15.PolynomialPolarization.diagonalPolynomial
abbrev averagedProduct := @Specs.D05.M15.PolynomialPolarization.averagedProduct

theorem diagonal_polynomial_homogeneous :
    Specs.D05.M15.PolynomialPolarization.diagonal_polynomial_homogeneous := by
  intro K V _ _ _ n p b B
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro r _
  apply MvPolynomial.IsHomogeneous.C_mul
  simpa using MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun i : Fin p => (MvPolynomial.X (r i) : MvPolynomial (Fin n) K))
    (fun _ => 1) (fun i _ => MvPolynomial.isHomogeneous_X K (r i))

theorem diagonal_polynomial_evaluation :
    Specs.D05.M15.PolynomialPolarization.diagonal_polynomial_evaluation := by
  intro K V _ _ _ n p b B
  classical
  ext v
  rw [PolynomialBridge.coordinate_evaluation_apply]
  simp only [Specs.D05.M15.PolynomialPolarization.diagonalPolynomial,
    map_sum, map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X, rawDiagonal]
  have h := D05.M15.MultilinearDimension.basis_expansion (fun _ : Fin p => b) B
    (fun _ => v)
  simp only [smul_eq_mul] at h
  convert h.symm using 2
  · ext; simp
  · simp [Module.Basis.coord_apply, mul_comm]

theorem averaged_product_formula :
    Specs.D05.M15.PolynomialPolarization.averaged_product_formula := by
  intro K V _ _ _ p φ v
  simp [Specs.D05.M15.PolynomialPolarization.averagedProduct,
    MultilinearMap.domDomCongr_apply, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiRing_apply, smul_eq_mul]

theorem averaged_product_symmetric :
    Specs.D05.M15.PolynomialPolarization.averaged_product_symmetric := by
  intro K V _ _ _ p φ τ v
  rw [averaged_product_formula, averaged_product_formula]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft τ)
    (fun σ : Equiv.Perm (Fin p) => ∏ i, φ i ((v ∘ τ) (σ i)))
    (fun σ : Equiv.Perm (Fin p) => ∏ i, φ i (v (σ i))) (fun _ => rfl)

theorem averaged_product_diagonal :
    Specs.D05.M15.PolynomialPolarization.averaged_product_diagonal := by
  intro K V _ _ _ _ p φ v
  unfold rawDiagonal
  rw [averaged_product_formula]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p)), one_mul]

section Existence
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

omit [CharZero K] in
private theorem symmetric_smul {p : ℕ}
    {B : MultilinearMap K (fun _ : Fin p => V) K} (hB : IsSymmetric B) (c : K) :
    IsSymmetric (c • B) := by
  intro σ v
  simp only [smul_apply, hB σ v]

omit [CharZero K] in
private theorem symmetric_add {p : ℕ}
    {B C : MultilinearMap K (fun _ : Fin p => V) K}
    (hB : IsSymmetric B) (hC : IsSymmetric C) : IsSymmetric (B + C) := by
  intro σ v
  simp only [add_apply, hB σ v, hC σ v]

omit [CharZero K] in
/-- Coordinate evaluation of the polynomial corresponding to a covector. -/
theorem evaluate_dual_generator {n : ℕ} (b : Module.Basis (Fin n) K V)
    (φ : Module.Dual K V) (v : V) :
    Specs.D05.M15.PolynomialBridge.coordinateEvaluation b
      (Specs.D05.M15.SymmetricBasis.polynomialEquiv b.dualBasis
        (_root_.SymmetricAlgebra.ι K (Module.Dual K V) φ)) v = φ v := by
  change ((Specs.D05.M15.PolynomialBridge.coordinateEvaluation b).comp
    (Specs.D05.M15.PolynomialBridge.dualPolynomialEquiv b).toAlgHom)
      (_root_.SymmetricAlgebra.ι K (Module.Dual K V) φ) v = φ v
  rw [← PolynomialBridge.evaluation_bridge b]
  exact PolynomialBridge.evaluation_generator φ v

/-- Finite tensor expansion implements the linear combination of monomial
preimages. This does not assume any polarization certificate. -/
theorem tensor_diagonal_exists {n : ℕ} (b : Module.Basis (Fin n) K V) (p : ℕ)
    (t : TensorPower K p (Module.Dual K V)) :
    ∃ B : MultilinearMap K (fun _ : Fin p => V) K, IsSymmetric B ∧
      rawDiagonal B = Specs.D05.M15.PolynomialBridge.coordinateEvaluation b
        (D05.M15.SymmetricBasis.tensorPolynomialMap b.dualBasis p t) := by
  classical
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c φ =>
    refine ⟨c • averagedProduct φ, symmetric_smul (averaged_product_symmetric φ) c, ?_⟩
    funext v
    change c * rawDiagonal (averagedProduct φ) v = _
    rw [averaged_product_diagonal, map_smul,
      D05.M15.SymmetricBasis.tensorPolynomialMap_tprod, map_smul, map_prod]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_apply, evaluate_dual_generator]
  | add x y hx hy =>
    obtain ⟨B, hB, hdiagB⟩ := hx
    obtain ⟨C, hC, hdiagC⟩ := hy
    refine ⟨B + C, symmetric_add hB hC, ?_⟩
    funext v
    change rawDiagonal B v + rawDiagonal C v = _
    rw [hdiagB, hdiagC, map_add, map_add]
    rfl

end Existence

theorem homogeneous_polynomial_form :
    Specs.D05.M15.PolynomialPolarization.homogeneous_polynomial_form := by
  intro K V _ _ _ _ n p b P hP
  have hmem : P ∈ LinearMap.range
      (D05.M15.SymmetricBasis.tensorPolynomialMap b.dualBasis p) := by
    rw [D05.M15.SymmetricBasis.polynomialRange_eq]
    exact hP
  obtain ⟨t, rfl⟩ := hmem
  obtain ⟨B, hB, hdiag⟩ := tensor_diagonal_exists b p t
  refine ⟨B, ⟨hB, hdiag⟩, ?_⟩
  intro C hC
  exact SubsetIdentity.raw_diagonal_injective p C B hC.1 hB (hC.2.trans hdiag.symm)

theorem diagonal_iff_polynomial :
    Specs.D05.M15.PolynomialPolarization.diagonal_iff_polynomial := by
  intro K V _ _ _ _ n p b q
  constructor
  · rintro ⟨B, _, hB⟩
    exact ⟨diagonalPolynomial b B, diagonal_polynomial_homogeneous b B,
      (diagonal_polynomial_evaluation b B).trans hB⟩
  · rintro ⟨P, hP, hq⟩
    obtain ⟨B, hB, _⟩ := homogeneous_polynomial_form b P hP
    exact ⟨B, hB.1, hB.2.trans hq⟩

theorem unique_formal_polynomial :
    Specs.D05.M15.PolynomialPolarization.unique_formal_polynomial := by
  intro K V _ _ _ _ n p b B
  refine ⟨diagonalPolynomial b B,
    ⟨diagonal_polynomial_homogeneous b B, diagonal_polynomial_evaluation b B⟩, ?_⟩
  intro P hP
  exact PolynomialBridge.coordinate_evaluation_injective b
    (hP.2.trans (diagonal_polynomial_evaluation b B).symm)

theorem polarization_formula :
    Specs.D05.M15.PolynomialPolarization.polarization_formula :=
  SubsetIdentity.polarization_formula

theorem degree_zero : Specs.D05.M15.PolynomialPolarization.degree_zero := by
  intro K V _ _ _ n b B
  classical
  constructor
  · simp only [Specs.D05.M15.PolynomialPolarization.diagonalPolynomial,
      Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    rw [Fintype.sum_unique]
    congr 1
    exact congrArg B (Subsingleton.elim _ _)
  · intro v
    exact congrArg B (Subsingleton.elim _ _)

end D05.M15.PolynomialPolarization
