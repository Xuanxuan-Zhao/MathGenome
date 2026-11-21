import MathGenome.Internal.Specs.D05.M09.Diagonalizable
import MathGenome.Internal.Specs.D05.M08.Interpolation
import MathGenome.Internal.Specs.D05.M08.Evaluation
import MathGenome.Internal.Specs.D05.M06.Projection

/-! Independent statements for K05.13.algebraic_projections, paper.tex:2252–2262.
The list `a : Fin r → K` is injective and lists exactly the eigenvalues in K.
Diagonalizability is the upstream eigenbasis predicate, not an assumed
spanning/decomposition certificate. No inner product or characteristic restriction
is imposed. `iSup` is the algebraic sum of subspaces, with finite support.
-/
noncomputable section
namespace Specs.D05.M13.AlgebraicProjections
open scoped BigOperators

def projection_type :=
  ∀ (K V : Type*) [Field K] [AddCommGroup V] [Module K V],
    Module.End K V → (r : ℕ) → (Fin r → K) → Fin r → Module.End K V

/-- The literal Lagrange polynomial of the source, evaluated at the operator. -/
def projection_value : projection_type := fun K V _ _ _ T r a i =>
  Specs.D05.M08.Evaluation.evaluation_value K V T
    (Specs.D05.M08.Interpolation.lagrangePolynomial_value K r a i)

def denominators_nonzero : Prop :=
  ∀ {K : Type*} [Field K] {r : ℕ} (a : Fin r → K),
    Function.Injective a → ∀ i j, i ≠ j → a i - a j ≠ 0

/-- Includes zero vectors in the eigenspaces. -/
def action_on_eigenspace : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) {r : ℕ} (a : Fin r → K),
    Function.Injective a → ∀ (i j : Fin r) (v : V), v ∈ T.eigenspace (a j) →
      projection_value K V T r a i v = if i = j then v else 0

/-- The spanning fact is proved from the eigenbasis hypothesis. -/
def eigenspaces_span : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) {r : ℕ} (a : Fin r → K),
    Specs.D05.M09.Diagonalizable.diagonalizable_value K V T →
    (∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ) →
      (⨆ i, T.eigenspace (a i)) = ⊤

def sum_projections : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) {r : ℕ} (a : Fin r → K),
    Function.Injective a →
    Specs.D05.M09.Diagonalizable.diagonalizable_value K V T →
    (∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ) →
      (∑ i, projection_value K V T r a i) = LinearMap.id

def idempotent_projections : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) {r : ℕ} (a : Fin r → K),
    Function.Injective a →
    Specs.D05.M09.Diagonalizable.diagonalizable_value K V T →
    (∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ) →
      ∀ i, (projection_value K V T r a i) ^ 2 = projection_value K V T r a i

def distinct_projections_mul : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) {r : ℕ} (a : Fin r → K),
    Function.Injective a →
    Specs.D05.M09.Diagonalizable.diagonalizable_value K V T →
    (∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ) →
      ∀ i j, i ≠ j →
        projection_value K V T r a i * projection_value K V T r a j = 0

def range_projection : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) {r : ℕ} (a : Fin r → K),
    Function.Injective a →
    Specs.D05.M09.Diagonalizable.diagonalizable_value K V T →
    (∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ) →
      ∀ i, (projection_value K V T r a i).range = T.eigenspace (a i)

/-- "Along the other eigenspaces" specifies the kernel exactly. -/
def kernel_projection : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) {r : ℕ} (a : Fin r → K),
    Function.Injective a →
    Specs.D05.M09.Diagonalizable.diagonalizable_value K V T →
    (∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ) →
      ∀ i, (projection_value K V T r a i).ker = ⨆ j, ⨆ (_ : j ≠ i), T.eigenspace (a j)

/-- The constructed map really selects the first component of this sum. -/
def projection_apply_sum : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) {r : ℕ} (a : Fin r → K),
    Function.Injective a →
    Specs.D05.M09.Diagonalizable.diagonalizable_value K V T →
    (∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ) →
      ∀ i (u w : V), u ∈ T.eigenspace (a i) →
        w ∈ (⨆ j, ⨆ (_ : j ≠ i), T.eigenspace (a j)) →
          projection_value K V T r a i (u + w) = u

/-- In dimension zero the spectrum is empty and the empty sum is both zero
and the identity. Conversely an empty full spectrum for a diagonalizable
operator forces the space to be zero. -/
def zero_space : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Subsingleton V]
    (T : Module.End K V) (a : Fin 0 → K),
    (∀ μ, ¬ T.HasEigenvalue μ) ∧
    (∑ i : Fin 0, projection_value K V T 0 a i) = 0 ∧
    (∑ i : Fin 0, projection_value K V T 0 a i) = LinearMap.id

def empty_spectrum_iff : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) {r : ℕ} (a : Fin r → K),
    Specs.D05.M09.Diagonalizable.diagonalizable_value K V T →
    (∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ) →
      (r = 0 ↔ Subsingleton V)

end Specs.D05.M13.AlgebraicProjections
