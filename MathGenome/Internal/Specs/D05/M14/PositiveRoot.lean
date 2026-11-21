import MathGenome.Internal.Specs.D05.M14.PositiveRoot.Uniqueness
import MathGenome.Internal.Specs.D05.M13.FunctionalCalculus

/-! Independent statements for K05.14.positive_root, paper.tex:2425–2433.
The square is the product in the ordinary endomorphism algebra. Positivity
includes self-adjointness and uses the shared first-slot-linear inner product.
All statements allow zero-dimensional spaces and zero eigenvalues.
The finite functional calculus is the already specified sum of spectral
projections; no candidate implementation is imported here. -/

namespace Specs.D05.M14.PositiveRoot

open Module.End

def exists_positive_root : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : Module.End F V),
    _root_.D05.positiveSemidefinite T →
      ∃ S : Module.End F V, _root_.D05.positiveSemidefinite S ∧ S ^ 2 = T

/-- Existence and uniqueness among positive roots, with no selected root assumed. -/
def existsUnique_positive_root : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : Module.End F V),
    _root_.D05.positiveSemidefinite T →
      ∃! S : Module.End F V, _root_.D05.positiveSemidefinite S ∧ S ^ 2 = T

/-- The formula holds on every vector of the entire scalar-field eigenspace.
The real part identifies the real eigenvalue of a positive operator. -/
def root_on_eigenspace : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T S : Module.End F V),
    _root_.D05.positiveSemidefinite T → _root_.D05.positiveSemidefinite S →
    S ^ 2 = T → ∀ (μ : F) (v : V), v ∈ T.eigenspace μ →
      S v = (Real.sqrt (RCLike.re μ) : F) • v

/-- The paper's real-eigenvalue notation, including λ = 0. -/
def root_on_real_eigenspace : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T S : Module.End F V),
    _root_.D05.positiveSemidefinite T → _root_.D05.positiveSemidefinite S →
    S ^ 2 = T → ∀ (a : ℝ) (v : V), v ∈ T.eigenspace (a : F) →
      S v = (Real.sqrt a : F) • v

/-- The root is precisely the finite spectral functional calculus of sqrt.
The enumeration lists distinct scalar eigenvalues, not chosen eigenvectors. -/
def root_eq_functional_calculus : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T S : Module.End F V),
    _root_.D05.positiveSemidefinite T → _root_.D05.positiveSemidefinite S →
    S ^ 2 = T → ∀ {r : ℕ} (a : Fin r → F), Function.Injective a →
    (∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ) →
      S = Specs.D05.M13.FunctionalCalculus.functionalCalculus_value F V T r a
        (fun μ => (Real.sqrt (RCLike.re μ.val) : F))

/-- No diagonalizability certificate is assumed: positivity supplies the spectral
decomposition. Every exhaustive distinct enumeration gives a positive root. -/
def functional_calculus_is_positive_root : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : Module.End F V),
    _root_.D05.positiveSemidefinite T →
    ∀ {r : ℕ} (a : Fin r → F), Function.Injective a →
    (∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ) →
      let S := Specs.D05.M13.FunctionalCalculus.functionalCalculus_value F V T r a
        (fun μ => (Real.sqrt (RCLike.re μ.val) : F))
      _root_.D05.positiveSemidefinite S ∧ S ^ 2 = T

end Specs.D05.M14.PositiveRoot
