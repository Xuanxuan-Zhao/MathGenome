import MathGenome.Internal.Specs.D05.M04.Coordinates
import MathGenome.Internal.Specs.D05.M08.Evaluation
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Isomorphisms

/-! Independent specification of the presentation stage of K05.10.rational,
paper.tex:1483–1501. `Module.AEval' T` has the underlying K-space V, with
p acting by p(T). A basis indexed by `Fin n` includes n = 0. The relation
matrix is literally X I minus the coefficientwise constant matrix of T.
No cyclic decomposition or presentation certificate is assumed. -/

noncomputable section
open scoped BigOperators
open Polynomial Matrix
namespace Specs.D05.M10.Rational.Presentation

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {n : ℕ}

/-- The coordinate matrix, with columns the images of the basis vectors. -/
def operatorMatrix (b : Module.Basis (Fin n) K V) (T : Module.End K V) :
    Matrix (Fin n) (Fin n) K := LinearMap.toMatrix b b T

/-- The operator powers and matrix powers agree in the chosen coordinates. -/
def matrix_powers : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (T : Module.End K V) (j : ℕ) (v : V),
    (operatorMatrix b T ^ j) *ᵥ b.equivFun v = b.equivFun ((T ^ j) v)

/-- A constant vector polynomial, in the chosen coordinates. -/
def constant (b : Module.Basis (Fin n) K V) : V →ₗ[K] (Fin n → K[X]) where
  toFun v i := C (b.repr v i)
  map_add' v w := by ext i; simp
  map_smul' a v := by ext i; simp [smul_eq_mul, Polynomial.C_mul]

/-- The actual matrix X I - A over K[X]. -/
def relationMatrix (b : Module.Basis (Fin n) K V) (T : Module.End K V) :
    Matrix (Fin n) (Fin n) K[X] :=
  Matrix.diagonal (fun _ => X) - (operatorMatrix b T).map C

/-- Multiplication by X I - A, hence its range is (X I - A)K[X]^n. -/
def relationMap (b : Module.Basis (Fin n) K V) (T : Module.End K V) :
    (Fin n → K[X]) →ₗ[K[X]] (Fin n → K[X]) :=
  Matrix.toLin' (relationMatrix b T)

/-- Evaluation of a polynomial column at the operator, followed by reconstruction. -/
def phi (b : Module.Basis (Fin n) K V) (T : Module.End K V) :
    (Fin n → K[X]) →ₗ[K[X]] Module.AEval' T where
  toFun f := ∑ i, f i • Module.AEval'.of T (b i)
  map_add' f g := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' p f := by simp [Finset.smul_sum, smul_smul]

/-- The witness in the paper's telescoping identity. -/
def telescopingSum (b : Module.Basis (Fin n) K V) (T : Module.End K V)
    (j : ℕ) (v : V) : Fin n → K[X] :=
  ∑ l ∈ Finset.range j, ((X : K[X]) ^ (j - 1 - l)) • constant b ((T ^ l) v)

/-- The polynomial module action agrees with the upstream evaluation convention. -/
def polynomial_action : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p : K[X]) (v : V),
    p • Module.AEval'.of T v =
      Module.AEval'.of T (Specs.D05.M08.Evaluation.evaluation_value K V T p v)

/-- In particular the formal variable acts by T. -/
def variable_action : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (v : V),
    (X : K[X]) • Module.AEval'.of T v = Module.AEval'.of T (T v)

/-- Explicit additivity and K[X]-linearity of the displayed Phi. -/
def phi_linear : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (T : Module.End K V)
    (p : K[X]) (f g : Fin n → K[X]),
    phi b T (f + g) = phi b T f + phi b T g ∧
      phi b T (p • f) = p • phi b T f

/-- Evaluation fixes constant vector polynomials. -/
def phi_constant : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (T : Module.End K V) (v : V),
    phi b T (constant b v) = Module.AEval'.of T v

/-- Phi on every finite coefficient presentation is the paper's sum of T-powers. -/
def phi_expansion : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (T : Module.End K V)
    (s : Finset ℕ) (v : ℕ → V),
    phi b T (∑ j ∈ s, ((X : K[X]) ^ j) • constant b (v j)) =
      Module.AEval'.of T (∑ j ∈ s, (T ^ j) (v j))

/-- Arbitrary polynomial columns have a finite vector-coefficient expansion. -/
def finite_expansion : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (f : Fin n → K[X]),
    ∃ (s : Finset ℕ) (v : ℕ → V), f = ∑ j ∈ s, ((X : K[X]) ^ j) • constant b (v j)

def phi_surjective : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (T : Module.End K V),
    Function.Surjective (phi b T)

/-- The displayed telescoping identity, including j = 0. -/
def telescoping_identity : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (T : Module.End K V) (j : ℕ) (v : V),
    relationMap b T (telescopingSum b T j v) =
      ((X : K[X]) ^ j) • constant b v - constant b ((T ^ j) v)

/-- Equality with the image of the literal polynomial matrix, not a postulated relation. -/
def phi_kernel : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (T : Module.End K V),
    LinearMap.ker (phi b T) = LinearMap.range (relationMap b T)

/-- The induced K[X]-module isomorphism, specified on every representative. -/
def presentation_iso : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (T : Module.End K V),
    ∃ e : ((Fin n → K[X]) ⧸ LinearMap.range (relationMap b T)) ≃ₗ[K[X]] Module.AEval' T,
      ∀ f, e (Submodule.Quotient.mk f) = phi b T f

/-- The same presentation for any matrix A representing T in b. -/
def matrix_presentation : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (T : Module.End K V)
    (A : Matrix (Fin n) (Fin n) K), A = operatorMatrix b T →
    ∃ e : ((Fin n → K[X]) ⧸ LinearMap.range
      (Matrix.toLin' (Matrix.diagonal (fun _ => (X : K[X])) - A.map C))) ≃ₗ[K[X]]
        Module.AEval' T,
      ∀ f, e (Submodule.Quotient.mk f) = phi b T f

end Specs.D05.M10.Rational.Presentation
