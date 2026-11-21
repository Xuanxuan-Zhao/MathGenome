import MathGenome.Internal.Specs.D05.M13.NormalBasic

/-!
Independent specifications for K05.13.self_adjoint_eigenvalues,
paper.tex:2183–2191. We use the shared algebraic adjoint, self-adjointness,
normality and unitary predicates. `D05.firstInner x y = inner F y x`
is the paper's first-slot-linear convention. Eigenspaces and eigenvalues are
Mathlib's canonical objects. All universal assertions allow zero spaces;
only the existence of the eigenvalue i requires a nonzero space.
-/

namespace Specs.D05.M13.SelfAdjointEigenvalues

universe u v

/-- The scalar in any nonzero self-adjoint eigenvector equation is fixed by conjugation. -/
def selfAdjoint_eigenvector_conj_eq : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V]
    (T : Module.End F V), _root_.D05.selfAdjoint T →
    ∀ (μ : F) (x : V), T.HasEigenvector μ x → μ = starRingEnd F μ

/-- Realness means membership in the actual embedded real field. -/
def complex_eigenvalue_real : Prop :=
  ∀ {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V),
    _root_.D05.selfAdjoint T → ∀ μ : ℂ, T.HasEigenvalue μ →
      ∃ r : ℝ, μ = (r : ℂ)

/-- Orthogonality in the paper's convention, for arbitrary vectors in distinct eigenspaces. -/
def selfAdjoint_eigenvectors_orthogonal : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V]
    (T : Module.End F V), _root_.D05.selfAdjoint T →
    ∀ (α β : F), α ≠ β → ∀ (x y : V),
      T x = α • x → T y = β • y → _root_.D05.firstInner (F := F) x y = 0

/-- The corresponding statement for whole eigenspace submodules, over R or C. -/
def selfAdjoint_eigenspaces_orthogonal : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V]
    (T : Module.End F V), _root_.D05.selfAdjoint T →
    ∀ (α β : F), α ≠ β → T.eigenspace α ≤ (T.eigenspace β).orthogonal

/-- In particular the same orthogonality holds for complex normal maps;
this statement also retains the real specialization. -/
def normal_eigenspaces_orthogonal : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V]
    (T : Module.End F V), _root_.D05.normalOperator T →
    ∀ (α β : F), α ≠ β → T.eigenspace α ≤ (T.eigenspace β).orthogonal

/-- Multiplication by i is a surjective inner-product isometry, including on the zero space. -/
def imaginary_multiple_unitary : Prop :=
  ∀ {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V],
    _root_.D05.IsUnitaryMap (Complex.I • (LinearMap.id : Module.End ℂ V))

def imaginary_multiple_normal : Prop :=
  ∀ {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V],
    _root_.D05.normalOperator (Complex.I • (LinearMap.id : Module.End ℂ V))

/-- The nonzero-space restriction is needed precisely for eigenvalue existence. -/
def imaginary_multiple_hasEigenvalue : Prop :=
  ∀ {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V],
    Module.End.HasEigenvalue (Complex.I • (LinearMap.id : Module.End ℂ V)) Complex.I

def imaginary_not_real : Prop := ¬ ∃ r : ℝ, Complex.I = (r : ℂ)

/-- The source's counterexample on every nonzero complex inner-product space. -/
def normal_nonreal_counterexample : Prop :=
  ∀ {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V],
    ∃ T : Module.End ℂ V, _root_.D05.IsUnitaryMap T ∧
      _root_.D05.normalOperator T ∧ T.HasEigenvalue Complex.I ∧
        ¬ ∃ r : ℝ, Complex.I = (r : ℂ)

end Specs.D05.M13.SelfAdjointEigenvalues
