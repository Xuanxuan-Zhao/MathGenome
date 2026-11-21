import MathGenome.Internal.Specs.D05.M15.PolynomialBridge.Domain
import MathGenome.Internal.Specs.D05.M07.DualBasis
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Algebra.Algebra.Pi

/-! Statements for K05.15.polynomial_bridge, paper.tex:3032–3038.
The symmetric algebra and formal coefficient polynomials are the upstream objects.
Evaluation is pointwise on the original vector space. All finite bases, including
empty ones, are allowed. Only the injectivity results assume an infinite field.
-/
noncomputable section
namespace Specs.D05.M15.PolynomialBridge
open D05.Foundations
open Specs.D05.M15.Symmetric
universe u v

/-- The basis-free algebra map extending evaluation of linear functionals. -/
def evaluation (K : Type u) (V : Type v) [Field K] [AddCommGroup V] [Module K V] :
    symmetricAlgebra K (Module.Dual K V) →ₐ[K] (V → K) :=
  _root_.SymmetricAlgebra.lift
    { toFun := fun f v => f v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- Evaluate formal polynomials at the coordinates of vectors in the chosen basis. -/
def coordinateEvaluation {K : Type u} {V : Type v} [Field K] [AddCommGroup V]
    [Module K V] {n : ℕ} (b : Module.Basis (Fin n) K V) :
    FormalPolynomial K n →ₐ[K] (V → K) :=
  MvPolynomial.aeval (fun i v => b.coord i v)

/-- The preceding polynomial isomorphism applied to the actual dual basis. -/
def dualPolynomialEquiv {K : Type u} {V : Type v} [Field K] [AddCommGroup V]
    [Module K V] {n : ℕ} (b : Module.Basis (Fin n) K V) :
    symmetricAlgebra K (Module.Dual K V) ≃ₐ[K] FormalPolynomial K n :=
  Specs.D05.M15.SymmetricBasis.polynomialEquiv b.dualBasis

def evaluation_type := ∀ (K : Type u) (V : Type v) [Field K]
  [AddCommGroup V] [Module K V], symmetricAlgebra K (Module.Dual K V) →ₐ[K] (V → K)
def evaluation_value : evaluation_type.{u,v} := evaluation

def coordinateEvaluation_type := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] {n : ℕ} (b : Module.Basis (Fin n) K V),
    FormalPolynomial K n →ₐ[K] (V → K)
def coordinateEvaluation_value : coordinateEvaluation_type.{u,v} := @coordinateEvaluation

def dualPolynomialEquiv_type := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] {n : ℕ} (b : Module.Basis (Fin n) K V),
    symmetricAlgebra K (Module.Dual K V) ≃ₐ[K] FormalPolynomial K n
def dualPolynomialEquiv_value : dualPolynomialEquiv_type.{u,v} := @dualPolynomialEquiv

def evaluation_generator : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (f : Module.Dual K V) (v : V),
    evaluation K V (_root_.SymmetricAlgebra.ι K (Module.Dual K V) f) v = f v

def coordinate_evaluation_apply : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] {n : ℕ} (b : Module.Basis (Fin n) K V)
  (p : FormalPolynomial K n) (v : V),
    coordinateEvaluation b p v = MvPolynomial.eval (fun i => b.coord i v) p

/-- Both directions identify the formal variables with the coordinate functionals. -/
def polynomial_coordinates : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] {n : ℕ} (b : Module.Basis (Fin n) K V) (i : Fin n),
  dualPolynomialEquiv b (_root_.SymmetricAlgebra.ι K (Module.Dual K V) (b.coord i)) =
    MvPolynomial.X i ∧
  (dualPolynomialEquiv b).symm (MvPolynomial.X i) =
    _root_.SymmetricAlgebra.ι K (Module.Dual K V) (b.coord i)

/-- The formal-polynomial identification intertwines the two actual algebra maps. -/
def evaluation_bridge : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] {n : ℕ} (b : Module.Basis (Fin n) K V),
    evaluation K V = (coordinateEvaluation b).comp (dualPolynomialEquiv b).toAlgHom

/-- Vanishing as a function detects zero formal coefficients over an infinite field. -/
def formal_evaluation_injective : Prop := ∀ (K : Type u) [Field K] [Infinite K]
  (n : ℕ), Function.Injective (fun p : FormalPolynomial K n =>
    fun a : Fin n → K => MvPolynomial.eval a p)

def coordinate_evaluation_injective : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [Infinite K] [AddCommGroup V] [Module K V] {n : ℕ} (b : Module.Basis (Fin n) K V),
    Function.Injective (coordinateEvaluation b)

def evaluation_injective : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [Infinite K] [AddCommGroup V] [Module K V] {n : ℕ} (b : Module.Basis (Fin n) K V),
    Function.Injective (evaluation K V)

/-- Constants are detected even over a finite field. -/
def zero_variables_injective : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (b : Module.Basis (Fin 0) K V),
    Function.Injective (coordinateEvaluation b) ∧ Function.Injective (evaluation K V)

/-- For every finite field, the specific one-variable formal polynomial is
nonzero even though its value function is zero. -/
def finite_field_counterexample : Prop := ∀ (K : Type u) [Field K] [Fintype K],
  (MvPolynomial.X (0 : Fin 1) ^ Fintype.card K - MvPolynomial.X 0 :
    FormalPolynomial K 1) ≠ 0 ∧
  ∀ a : Fin 1 → K, MvPolynomial.eval a
    (MvPolynomial.X 0 ^ Fintype.card K - MvPolynomial.X 0) = 0

/-- The same obstruction is present on any nonempty finite coordinate basis. -/
def finite_field_symmetric_counterexample : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [Fintype K] [AddCommGroup V] [Module K V] {n : ℕ}
  (b : Module.Basis (Fin n) K V) (i : Fin n),
  let x := _root_.SymmetricAlgebra.ι K (Module.Dual K V) (b.coord i)
  x ^ Fintype.card K - x ≠ 0 ∧ evaluation K V (x ^ Fintype.card K - x) = 0

/-- No conclusion about evaluation injectivity is used in the domain results. -/
def formal_polynomial_domain : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ), IsDomain (FormalPolynomial K n)

def symmetric_domain : Prop := ∀ (K : Type u) (V : Type v) [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V],
    IsDomain (symmetricAlgebra K V)

end Specs.D05.M15.PolynomialBridge
