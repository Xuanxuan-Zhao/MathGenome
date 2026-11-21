import MathGenome.Internal.Specs.D05.M03.MapAlgebra
import MathGenome.Internal.Specs.D05.Foundations.FormalPolynomials
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
Independent specifications for K05.08.evaluation, paper.tex:1123–1132.
Polynomials are the formal coefficient polynomials of the foundations interface.
The target is the canonical, possibly noncommutative endomorphism algebra, with
multiplication given by composition. No nontriviality instance on the target is
required. These assertions hold for arbitrary vector spaces, and in particular
for every finite-dimensional space in the chapter, including the zero space.
-/

noncomputable section

namespace Specs.D05.M08.Evaluation

open scoped BigOperators

def evaluation_type :=
  ∀ (K V : Type*) [Field K] [AddCommGroup V] [Module K V],
    Module.End K V → (Polynomial K →ₐ[K] Module.End K V)

/-- The canonical polynomial algebra homomorphism sending X to T. Its
coefficient-sum formula is an independent obligation below. -/
def evaluation_value : evaluation_type :=
  fun _ _ _ _ _ T => Polynomial.aeval T

def coefficient_sum : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p : Polynomial K),
    evaluation_value K V T p =
      ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j • T ^ j

/-- Every upper degree bound gives the paper's displayed coefficient formula.
The natural degree convention also covers the zero polynomial. -/
def coefficient_sum_of_bound : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p : Polynomial K) (d : ℕ),
    p.natDegree ≤ d →
    evaluation_value K V T p =
      ∑ j ∈ Finset.range (d + 1), p.coeff j • T ^ j

/-- Evaluation of any finite coefficient presentation, including empty sums. -/
def finite_expansion : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (s : Finset ℕ) (a : ℕ → K),
    evaluation_value K V T (∑ j ∈ s, Polynomial.monomial j (a j)) =
      ∑ j ∈ s, a j • T ^ j

def zero_padding : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p : Polynomial K) (d e : ℕ),
    p.natDegree ≤ d → d ≤ e →
    (∑ j ∈ Finset.range (d + 1), p.coeff j • T ^ j) =
      ∑ j ∈ Finset.range (e + 1), p.coeff j • T ^ j

def eval_zero : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V), evaluation_value K V T 0 = 0

def eval_add : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p q : Polynomial K),
    evaluation_value K V T (p + q) =
      evaluation_value K V T p + evaluation_value K V T q

def eval_smul : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (a : K) (p : Polynomial K),
    evaluation_value K V T (a • p) = a • evaluation_value K V T p

def eval_mul : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p q : Polynomial K),
    evaluation_value K V T (p * q) =
      evaluation_value K V T p * evaluation_value K V T q

def eval_one : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V), evaluation_value K V T 1 = LinearMap.id

def eval_constant : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (a : K),
    evaluation_value K V T (Polynomial.C a) = a • (LinearMap.id : Module.End K V)

def eval_variable : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V), evaluation_value K V T Polynomial.X = T

def eval_powers : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (j : ℕ),
    evaluation_value K V T (Polynomial.X ^ j) = T ^ j ∧
      T ^ 0 = (LinearMap.id : Module.End K V)

def polynomials_commute : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p q : Polynomial K),
    evaluation_value K V T p * evaluation_value K V T q =
      evaluation_value K V T q * evaluation_value K V T p

/-- The multiplication calculation with the scalar coefficient convolution
spelled out; k ranges over a finite upper bound for the product's support. -/
def product_convolution : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p q : Polynomial K),
    (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • T ^ i) *
        (∑ j ∈ Finset.range (q.natDegree + 1), q.coeff j • T ^ j) =
      ∑ k ∈ Finset.range ((p * q).natDegree + 1),
        (∑ ij ∈ Finset.antidiagonal k, p.coeff ij.1 * q.coeff ij.2) • T ^ k

def eval_apply : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p : Polynomial K) (v : V),
    evaluation_value K V T p v =
      ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j • (T ^ j) v

/-- The identity is the zero endomorphism on a zero space, and every
polynomial (including 1) evaluates to zero there. -/
def zero_space : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Subsingleton V]
    (T : Module.End K V) (p : Polynomial K),
    (LinearMap.id : Module.End K V) = 0 ∧ evaluation_value K V T p = 0

end Specs.D05.M08.Evaluation
