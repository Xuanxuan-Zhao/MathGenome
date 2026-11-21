import MathGenome.Internal.Specs.D05.M13.AlgebraicProjections
import MathGenome.Internal.Specs.D05.M13.SpectralProjections

/-! K05.13.functional_calculus, paper.tex:2273–2282.
Functions have domain `Set.range a`, the finite set of listed scalar eigenvalues.
The list is injective and exhaustive in the spectral theorems; existence of
such a list is also an obligation. No inner product is imposed on algebraic
results. Diagonalizability is the upstream eigenbasis predicate. In the adjoint
results we reuse the established adjoint and orthogonal projections, including
both real self-adjoint and complex normal operators and zero-dimensional spaces.
-/
noncomputable section
namespace Specs.D05.M13.FunctionalCalculus
open scoped BigOperators

def functionalCalculus_type :=
  ∀ (K V : Type*) [Field K] [AddCommGroup V] [Module K V],
    Module.End K V → (r : ℕ) → (a : Fin r → K) → (Set.range a → K) → Module.End K V

/-- The literal finite sum from the manuscript, using the shared projections. -/
def functionalCalculus_value : functionalCalculus_type := fun K V _ _ _ T r a f =>
  ∑ i, f ⟨a i, ⟨i, rfl⟩⟩ •
    Specs.D05.M13.AlgebraicProjections.projection_value K V T r a i

def finite_spectrum : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    ∃ (r : ℕ) (a : Fin r → K), Function.Injective a ∧
      ∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ

def action_on_eigenspace : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) {r : ℕ} (a : Fin r → K), Function.Injective a →
    ∀ (f : Set.range a → K) (j : Fin r) (v : V), v ∈ T.eigenspace (a j) →
      functionalCalculus_value K V T r a f v = f ⟨a j, ⟨j, rfl⟩⟩ • v

def map_zero : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) {r : ℕ} (a : Fin r → K), functionalCalculus_value K V T r a 0 = 0

def map_add : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) {r : ℕ} (a : Fin r → K) (f g : Set.range a → K),
    functionalCalculus_value K V T r a (f + g) = functionalCalculus_value K V T r a f + functionalCalculus_value K V T r a g

def map_smul : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) {r : ℕ} (a : Fin r → K) (s : K) (f : Set.range a → K),
    functionalCalculus_value K V T r a (s • f) = s • functionalCalculus_value K V T r a f

def map_one : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) {r : ℕ} (a : Fin r → K), Function.Injective a →
    Specs.D05.M09.Diagonalizable.diagonalizable_value K V T →
    (∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ) →
    functionalCalculus_value K V T r a 1 = LinearMap.id

def map_mul : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) {r : ℕ} (a : Fin r → K), Function.Injective a →
    Specs.D05.M09.Diagonalizable.diagonalizable_value K V T →
    (∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ) →
    ∀ f g : Set.range a → K,
      functionalCalculus_value K V T r a (f * g) = functionalCalculus_value K V T r a f * functionalCalculus_value K V T r a g

def map_constant : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) {r : ℕ} (a : Fin r → K), Function.Injective a →
    Specs.D05.M09.Diagonalizable.diagonalizable_value K V T →
    (∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ) →
    ∀ s : K, functionalCalculus_value K V T r a (fun _ => s) = s • (LinearMap.id : Module.End K V)

def polynomial_agreement : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) {r : ℕ} (a : Fin r → K), Function.Injective a →
    Specs.D05.M09.Diagonalizable.diagonalizable_value K V T →
    (∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ) →
    ∀ p : Polynomial K, functionalCalculus_value K V T r a (fun μ => p.eval μ.val) =
      Specs.D05.M08.Evaluation.evaluation_value K V T p

def interpolation_formula : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) {r : ℕ} (a : Fin r → K) (f : Set.range a → K),
    functionalCalculus_value K V T r a f = Specs.D05.M08.Evaluation.evaluation_value K V T
      (∑ i, f ⟨a i, ⟨i, rfl⟩⟩ •
        Specs.D05.M08.Interpolation.lagrangePolynomial_value K r a i)

def depends_only_spectrum : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) {r : ℕ} (a : Fin r → K),
    (∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ) →
    ∀ f g : K → K, (∀ μ, T.HasEigenvalue μ → f μ = g μ) →
      functionalCalculus_value K V T r a (fun μ => f μ.val) = functionalCalculus_value K V T r a (fun μ => g μ.val)

def enumeration_independent : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) {r : ℕ} (a : Fin r → K), Function.Injective a →
    Specs.D05.M09.Diagonalizable.diagonalizable_value K V T →
    ∀ (hfull : ∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ)
      {s : ℕ} (b : Fin s → K), Function.Injective b →
    ∀ (hfullb : ∀ μ, T.HasEigenvalue μ ↔ ∃ j, b j = μ)
      (f : T.Eigenvalues → K),
      functionalCalculus_value K V T r a (fun μ => f ⟨μ.val, (hfull μ.val).mpr μ.property⟩) =
      functionalCalculus_value K V T s b
        (fun μ => f ⟨μ.val, (hfullb μ.val).mpr μ.property⟩)

def empty_sum : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (a : Fin 0 → K) (f : Set.range a → K),
    functionalCalculus_value K V T 0 a f = 0

def zero_space : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Subsingleton V]
    (T : Module.End K V) {r : ℕ} (a : Fin r → K) (f : Set.range a → K),
    functionalCalculus_value K V T r a f = 0 ∧
      functionalCalculus_value K V T r a 1 = LinearMap.id

def adjoint_conjugate : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V]
    (T : Module.End F V), _root_.D05.normalOperator T →
    Specs.D05.M09.Diagonalizable.diagonalizable_value F V T →
    ∀ {r : ℕ} (a : Fin r → F), Function.Injective a →
    (∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ) →
    ∀ f : Set.range a → F,
    _root_.LinearMap.adjoint (functionalCalculus_value F V T r a f) =
      functionalCalculus_value F V T r a (fun μ => star (f μ))

def real_adjoint_conjugate : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (T : Module.End ℝ V), _root_.D05.selfAdjoint T →
    ∀ {r : ℕ} (a : Fin r → ℝ), Function.Injective a →
    (∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ) →
    ∀ f : Set.range a → ℝ,
    _root_.LinearMap.adjoint (functionalCalculus_value ℝ V T r a f) =
      functionalCalculus_value ℝ V T r a (fun μ => star (f μ))

def complex_adjoint_conjugate : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V), _root_.D05.normalOperator T →
    ∀ {r : ℕ} (a : Fin r → ℂ), Function.Injective a →
    (∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ) →
    ∀ f : Set.range a → ℂ,
    _root_.LinearMap.adjoint (functionalCalculus_value ℂ V T r a f) =
      functionalCalculus_value ℂ V T r a (fun μ => star (f μ))

end Specs.D05.M13.FunctionalCalculus
