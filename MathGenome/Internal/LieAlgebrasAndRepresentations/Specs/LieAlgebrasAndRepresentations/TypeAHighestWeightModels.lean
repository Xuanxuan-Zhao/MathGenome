import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalRootsA
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
import Mathlib.Algebra.Lie.Matrix
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import MathGenome.Internal.D05.M15.ExteriorDerivation
import MathGenome.Internal.D05.M15.SymmetricBasis
import MathGenome.Internal.D05.M15.SymmetricDerivation

/-! The classical examples in LA-G09, with the standard upper triangular
positive system and the Cartan and coroots of LA-D08-A. -/

noncomputable section
open scoped TensorProduct

namespace Specs.LieAlgebrasAndRepresentations.TypeAHighestWeightModels

open ClassicalRootsA VermaModules VermaWeightsUniversal SimpleHighestWeightQuotient MvPolynomial

abbrev Vector (n : ℕ) := Fin (n + 1) → ℂ

abbrev vectorBasis (n : ℕ) : Module.Basis (Fin (n + 1)) ℂ (Vector n) :=
  Pi.basisFun ℂ _

/-- Evaluation at a diagonal element with strictly decreasing real entries. -/
def orderingElement (n : ℕ) : cartan n :=
  let t : Fin (n + 1) → ℂ := fun i => -(i.val : ℂ)
  let m := (∑ i, t i) / (n + 1 : ℂ)
  ⟨⟨Matrix.diagonal (fun i => t i - m), by
    change Matrix.trace (Matrix.diagonal (fun i => t i - m)) = 0
    have h : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    simp [Matrix.trace, Finset.sum_sub_distrib, nsmul_eq_mul, m, mul_div_cancel₀, h]⟩,
    Matrix.isDiag_diagonal _⟩

def direction (n : ℕ) : Direction (cartan n) :=
  Complex.reLm.comp ((Module.Dual.eval ℂ (cartan n) (orderingElement n)).restrictScalars ℝ)

/-- For 1 ≤ k < n+1 this is the kth fundamental weight. -/
def omega (n k : ℕ) : Module.Dual ℂ (cartan n) :=
  ∑ i : Fin (n + 1), if i.val < k then epsilon n i else 0

section Models

variable {n : ℕ}
attribute [local instance 100] LieRing.ofAssociativeRing

private def polynomialGenerator (n : ℕ) : Vector n →ₗ[ℂ] MvPolynomial (Fin (n + 1)) ℂ :=
  (vectorBasis n).constr ℂ (MvPolynomial.X (R := ℂ))

private theorem polynomialGenerator_apply (v : Vector n) :
    polynomialGenerator n v = ∑ i, v i • (X i : MvPolynomial (Fin (n + 1)) ℂ) := by
  rw [polynomialGenerator, Module.Basis.constr_apply_fintype]
  rfl

def polynomialDerivation (A : sl n) :
    Derivation ℂ (MvPolynomial (Fin (n + 1)) ℂ) (MvPolynomial (Fin (n + 1)) ℂ) :=
  MvPolynomial.mkDerivation ℂ (fun i => polynomialGenerator n ⁅A, vectorBasis n i⁆)

@[simp] theorem polynomialDerivation_X (A : sl n) (i : Fin (n + 1)) :
    polynomialDerivation A (X i) = polynomialGenerator n ⁅A, vectorBasis n i⁆ :=
  MvPolynomial.mkDerivation_X _ _ _

private theorem polynomialDerivation_generator (A : sl n) (v : Vector n) :
    polynomialDerivation A (polynomialGenerator n v) = polynomialGenerator n ⁅A, v⁆ := by
  have eq : (polynomialDerivation A).toLinearMap.comp (polynomialGenerator n) =
      (polynomialGenerator n).comp (LieModule.toEnd ℂ (sl n) (Vector n) A) := by
    apply (vectorBasis n).ext
    intro i
    simp [polynomialGenerator]
  exact LinearMap.congr_fun eq v

private def polynomialDerivationHom (n : ℕ) :
    sl n →ₗ⁅ℂ⁆ Derivation ℂ (MvPolynomial (Fin (n + 1)) ℂ) (MvPolynomial (Fin (n + 1)) ℂ) where
  toFun := polynomialDerivation
  map_add' A B := MvPolynomial.derivation_ext fun i => by simp [add_lie]
  map_smul' c A := MvPolynomial.derivation_ext fun i => by simp [smul_lie]
  map_lie' {A B} := MvPolynomial.derivation_ext fun i => by
    simp only [polynomialDerivation_X, Derivation.commutator_apply, polynomialDerivation_generator]
    rw [← map_sub, lie_lie]

instance polynomialLieRingModule (n : ℕ) : LieRingModule (sl n) (MvPolynomial (Fin (n + 1)) ℂ) :=
  LieRingModule.compLieHom _ (polynomialDerivationHom n)

instance polynomialLieModule (n : ℕ) : LieModule ℂ (sl n) (MvPolynomial (Fin (n + 1)) ℂ) :=
  LieModule.compLieHom _ (polynomialDerivationHom n)

theorem polynomial_lie (A : sl n) (p : MvPolynomial (Fin (n + 1)) ℂ) :
    ⁅A, p⁆ = polynomialDerivation A p := rfl

private theorem polynomialGenerator_homogeneous (v : Vector n) :
    (polynomialGenerator n v).IsHomogeneous 1 := by
  rw [polynomialGenerator_apply]
  exact Submodule.sum_mem (homogeneousSubmodule _ _ 1)
    (fun i _ => Submodule.smul_mem _ _ (isHomogeneous_X ℂ i))

private theorem polynomialDerivation_mem (A : sl n) {a : ℕ} {p : MvPolynomial (Fin (n + 1)) ℂ}
    (hp : p.IsHomogeneous a) : (polynomialDerivation A p).IsHomogeneous a := by
  classical
  have hp' : p = ∑ s ∈ p.support, monomial s (p.coeff s) := p.as_sum
  conv_lhs => rw [hp']
  rw [map_sum]
  refine IsHomogeneous.sum _ _ _ fun s hs => ?_
  rw [polynomialDerivation, mkDerivation_monomial]
  apply Submodule.smul_mem (homogeneousSubmodule _ _ a)
  refine IsHomogeneous.sum _ _ _ fun i hi => ?_
  change (monomial (s - Finsupp.single i 1) (s i : ℂ) *
      polynomialGenerator n ⁅A, vectorBasis n i⁆).IsHomogeneous a
  have hle : Finsupp.single i 1 ≤ s := Finsupp.single_le_iff.mpr
    (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
  have hdeg : (s - Finsupp.single i 1).degree + 1 = a := by
    calc
      _ = (s - Finsupp.single i 1).degree + (Finsupp.single i 1).degree := by simp
      _ = s.degree := by rw [← map_add, tsub_add_cancel_of_le hle]
      _ = a := by rw [Finsupp.degree_eq_weight_one]; exact hp (mem_support_iff.mp hs)
  exact hdeg ▸ (isHomogeneous_monomial _ rfl).mul (polynomialGenerator_homogeneous _)

/-- The symmetric power in its homogeneous polynomial realization.
The action differentiates the linear substitution on generators. -/
def symmetricPower (n a : ℕ) : LieSubmodule ℂ (sl n) (MvPolynomial (Fin (n + 1)) ℂ) where
  toSubmodule := homogeneousSubmodule _ _ a
  lie_mem := fun {_ _} hp => polynomialDerivation_mem _ hp

open _root_.D05.M15.ExteriorDerivation in
private theorem exteriorDerivation_commutator (A B : Module.End ℂ (Vector n)) :
    induced ⁅A, B⁆ = induced A * induced B - induced B * induced A := by
  apply _root_.D05.M15.ExteriorDerivation.derivation_ext
  · exact induced_leibniz _
  · intro x y
    simp only [LinearMap.sub_apply, Module.End.mul_apply, induced_mul, map_add]
    noncomm_ring
  · intro v
    simp only [LinearMap.sub_apply, Module.End.mul_apply, induced_generator,
      LieRing.of_associative_ring_bracket, map_sub]

open _root_.D05.M15.ExteriorDerivation in
private def exteriorDerivationHom (n : ℕ) :
    sl n →ₗ⁅ℂ⁆ Module.End ℂ (ExteriorAlgebra ℂ (Vector n)) where
  toFun A := induced (LieModule.toEnd ℂ (sl n) (Vector n) A)
  map_add' A B := by
    rw [map_add]
    apply _root_.D05.M15.ExteriorDerivation.derivation_ext
    · exact induced_leibniz _
    · intro x y
      simp only [LinearMap.add_apply, induced_mul, add_mul, mul_add]
      abel
    · intro v
      simp only [induced_generator, LinearMap.add_apply, map_add]
  map_smul' c A := by
    rw [RingHom.id_apply, map_smul]
    apply _root_.D05.M15.ExteriorDerivation.derivation_ext
    · exact induced_leibniz _
    · intro x y
      simp only [LinearMap.smul_apply, induced_mul, smul_add, Algebra.smul_mul_assoc,
        Algebra.mul_smul_comm]
    · intro v
      simp only [induced_generator, LinearMap.smul_apply, map_smul]
  map_lie' {A B} := by rw [LieHom.map_lie]; exact exteriorDerivation_commutator _ _

instance exteriorLieRingModule (n : ℕ) : LieRingModule (sl n) (ExteriorAlgebra ℂ (Vector n)) :=
  LieRingModule.compLieHom _ (exteriorDerivationHom n)

instance exteriorLieModule (n : ℕ) : LieModule ℂ (sl n) (ExteriorAlgebra ℂ (Vector n)) :=
  LieModule.compLieHom _ (exteriorDerivationHom n)

theorem exterior_lie (A : sl n) (p : ExteriorAlgebra ℂ (Vector n)) :
    ⁅A, p⁆ = _root_.D05.M15.ExteriorDerivation.induced (LieModule.toEnd ℂ (sl n) (Vector n) A) p := rfl

/-- The canonical homogeneous exterior power, with the operator acting on
each entry of a wedge and summing the results. -/
def exteriorPower (n k : ℕ) : LieSubmodule ℂ (sl n) (ExteriorAlgebra ℂ (Vector n)) where
  toSubmodule := ⋀[ℂ]^k (Vector n)
  lie_mem := fun {A p} hp =>
    _root_.D05.M15.ExteriorDerivation.degree_preserved (LieModule.toEnd ℂ (sl n) (Vector n) A) k p hp

/-- The symmetric tensor quotient of the algebra core. -/
abbrev SymmetricQuotient (n a : ℕ) :=
  _root_.Specs.D05.M15.Symmetric.symmetricPower ℂ (Vector n) a

/-- Coordinate realization induced by sending the standard basis to the variables. -/
def symmetricPolynomialEquiv (n a : ℕ) :
    SymmetricQuotient n a ≃ₗ[ℂ] symmetricPower n a :=
  _root_.D05.M15.SymmetricBasis.powerPolynomialEquiv (vectorBasis n) a

private def symmetricQuotientAction (n a : ℕ) :
    sl n →ₗ⁅ℂ⁆ Module.End ℂ (SymmetricQuotient n a) :=
  (symmetricPolynomialEquiv n a).symm.lieConj.toLieHom.comp
    (LieModule.toEnd ℂ (sl n) (symmetricPower n a))

instance symmetricQuotientLieRingModule (n a : ℕ) :
    LieRingModule (sl n) (SymmetricQuotient n a) :=
  LieRingModule.compLieHom _ (symmetricQuotientAction n a)

instance symmetricQuotientLieModule (n a : ℕ) :
    LieModule ℂ (sl n) (SymmetricQuotient n a) :=
  LieModule.compLieHom _ (symmetricQuotientAction n a)

theorem symmetricQuotient_lie {a : ℕ} (A : sl n) (q : SymmetricQuotient n a) :
    ⁅A, q⁆ = (symmetricPolynomialEquiv n a).symm ⁅A, symmetricPolynomialEquiv n a q⁆ := rfl

end Models

local instance {n : ℕ} {χ : U (borel_value (cartan n) (direction n)) →ₐ[ℂ] ℂ} :
    LieRingModule (sl n) (induced_value (cartan n) (direction n) χ) :=
  inducedLieRingModule (cartan n) (direction n) χ

local instance {n : ℕ} {χ : U (borel_value (cartan n) (direction n)) →ₐ[ℂ] ℂ} :
    LieModule ℂ (sl n) (induced_value (cartan n) (direction n) χ) :=
  inducedLieModule (cartan n) (direction n) χ

/-- Identification with the canonical simple quotient for the indicated weight. -/
def HasLabel (n : ℕ) (lam : Module.Dual ℂ (cartan n)) (V : Type)
    [AddCommGroup V] [Module ℂ V] [LieRingModule (sl n) V] [LieModule ℂ (sl n) V] : Prop :=
  ∃ χ : U (borel_value (cartan n) (direction n)) →ₐ[ℂ] ℂ,
    IsWeightCharacter (cartan n) (direction n) lam χ ∧
    Nonempty (V ≃ₗ⁅ℂ,sl n⁆ simpleQuotient_value (cartan n) (direction n) χ)

def positive_roots_type : Prop := ∀ n : ℕ, 1 ≤ n →
  Regular (cartan n) (direction n) ∧
    SerreRelations.positive (cartan n) (direction n) =
      {α | ∃ i j : Fin (n + 1), i < j ∧ α = root n i j}

def simple_roots_type : Prop := ∀ n : ℕ, 1 ≤ n →
  SerreRelations.simple (cartan n) (direction n) =
    {α | ∃ i : Fin n, α = root n i.castSucc i.succ}

def fundamental_weights_type : Prop := ∀ n k : ℕ, 1 ≤ k → k ≤ n → ∀ i : Fin n,
  omega n k (coroot n i.castSucc i.succ) = if i.val + 1 = k then 1 else 0

def defining_type : Prop := ∀ n : ℕ, 1 ≤ n → HasLabel n (omega n 1) (Vector n)

def symmetric_type : Prop := ∀ n : ℕ, 1 ≤ n → ∀ a : ℕ,
  HasLabel n ((a : ℂ) • omega n 1) (symmetricPower n a)

/-- The model also identifies the symmetric tensor quotient with the simple
module. Its action agrees, under the canonical inclusion, with the derivation
extending the defining matrix action on the generators of the symmetric algebra. -/
def symmetric_quotient_type : Prop := ∀ n a : ℕ, 1 ≤ n →
  HasLabel n ((a : ℂ) • omega n 1) (SymmetricQuotient n a) ∧
  ∀ (A : sl n) (q : SymmetricQuotient n a),
    _root_.Specs.D05.M15.SymmetricBasis.powerInclusion (K := ℂ) (V := Vector n) a ⁅A, q⁆ =
      _root_.D05.M15.SymmetricDerivation.induced (LieModule.toEnd ℂ (sl n) (Vector n) A)
        (_root_.Specs.D05.M15.SymmetricBasis.powerInclusion (K := ℂ) (V := Vector n) a q)

def exterior_type : Prop := ∀ n k : ℕ, 1 ≤ k → k ≤ n →
  HasLabel n (omega n k) (exteriorPower n k)

abbrev TensorWithDual := Vector 2 ⊗[ℂ] Module.Dual ℂ (Vector 2)
abbrev Scalar := TrivialLieModule ℂ (sl 2) ℂ

instance scalarAdjointLieRingModule : LieRingModule (sl 2) (Scalar × sl 2) where
  bracket x y := (0, ⁅x, y.2⁆)
  add_lie x y z := Prod.ext (by simp) (add_lie x y z.2)
  lie_add x y z := Prod.ext (by simp) (lie_add x y.2 z.2)
  leibniz_lie x y z := Prod.ext (by simp) (leibniz_lie x y z.2)

instance scalarAdjointLieModule : LieModule ℂ (sl 2) (Scalar × sl 2) where
  smul_lie c x y := Prod.ext (by change (0 : Scalar) = c • 0; rw [smul_zero]) (smul_lie c x y.2)
  lie_smul c x y := Prod.ext (by change (0 : Scalar) = c • 0; rw [smul_zero]) (lie_smul c x y.2)

def tensor_with_dual_type : Prop :=
  HasLabel 2 (omega 2 1 + omega 2 2) (sl 2) ∧
  Module.finrank ℂ (sl 2) = 8 ∧
  ∃ e : TensorWithDual ≃ₗ⁅ℂ,sl 2⁆ Scalar × sl 2,
    ∀ v : Vector 2, ∀ f : Module.Dual ℂ (Vector 2),
      (TrivialLieModule.equiv ℂ (sl 2) ℂ (e (v ⊗ₜ[ℂ] f)).1 = f v / 3) ∧
      ((e (v ⊗ₜ[ℂ] f)).2 : Matrix (Fin 3) (Fin 3) ℂ) =
        Matrix.vecMulVec v (fun i => f (vectorBasis 2 i)) - (f v / 3) • (1 : Matrix (Fin 3) (Fin 3) ℂ)

end Specs.LieAlgebrasAndRepresentations.TypeAHighestWeightModels
