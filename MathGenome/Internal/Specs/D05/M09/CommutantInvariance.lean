import MathGenome.Internal.Specs.D05.M06.Invariant
import MathGenome.Internal.Specs.D05.M08.Evaluation
import MathGenome.Internal.Specs.D05.M09.Eigenspace

/-!
Independent statements for K05.09.commutant_invariance (paper.tex:1299–1301).
Multiplication is composition in the canonical endomorphism algebra. Polynomial
evaluation and invariance use the shared upstream definitions. No nonzero-space,
splitting, characteristic, or invertibility hypothesis is imposed. The algebraic
claims hold in arbitrary dimension, hence in the finite-dimensional setting of
Chapter 9. Generalized eigenspaces are treated at every natural exponent, and the
paper's choice of exponent `finrank K V` is stated explicitly as well.
-/

noncomputable section

namespace Specs.D05.M09.CommutantInvariance

open Specs.D05.M06.Invariant (invariant_value)
open Specs.D05.M08.Evaluation (evaluation_value)

/-- Commutation with T implies commutation with every power, including T^0 = I. -/
def commutes_powers : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (S T : Module.End K V), S * T = T * S →
      ∀ j : ℕ, S * T ^ j = T ^ j * S

/-- Commutation extends from T to every polynomial evaluated at T. -/
def commutes_polynomial : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (S T : Module.End K V), S * T = T * S →
      ∀ p : Polynomial K,
        S * evaluation_value K V T p = evaluation_value K V T p * S

/-- The polynomial used for generalized eigenspaces has its intended value. -/
def shifted_power_evaluation : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (μ : K) (k : ℕ),
    evaluation_value K V T ((Polynomial.X - Polynomial.C μ) ^ k) =
      (T - μ • (LinearMap.id : Module.End K V)) ^ k

/-- A commuting operator preserves every polynomial kernel. -/
def polynomial_kernel_invariant : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (S T : Module.End K V), S * T = T * S →
      ∀ p : Polynomial K,
        invariant_value K V (LinearMap.ker (evaluation_value K V T p)) S

/-- It also preserves every polynomial image. -/
def polynomial_image_invariant : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (S T : Module.End K V), S * T = T * S →
      ∀ p : Polynomial K,
        invariant_value K V (LinearMap.range (evaluation_value K V T p)) S

/-- Eigenspaces are over the same scalar field as S and T. -/
def eigenspace_invariant : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (S T : Module.End K V), S * T = T * S →
      ∀ μ : K, invariant_value K V (T.eigenspace μ) S

/-- Preservation of the kernels defining generalized eigenspaces, at every exponent. -/
def shifted_power_kernel_invariant : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (S T : Module.End K V), S * T = T * S →
      ∀ (μ : K) (k : ℕ),
        invariant_value K V
          (LinearMap.ker ((T - μ • (LinearMap.id : Module.End K V)) ^ k)) S

/-- The same preservation result for Mathlib's canonical generalized eigenspaces. -/
def genEigenspace_invariant : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (S T : Module.End K V), S * T = T * S →
      ∀ (μ : K) (k : ℕ), invariant_value K V (T.genEigenspace μ k) S

/-- The paper defines G_μ(T) as ker (T - μI)^(dim V), including dim V = 0. -/
def generalized_eigenspace_invariant : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S T : Module.End K V), S * T = T * S →
      ∀ μ : K, invariant_value K V
        (LinearMap.ker ((T - μ • (LinearMap.id : Module.End K V)) ^
          Module.finrank K V)) S

/-- In particular every polynomial kernel is invariant under T itself. -/
def self_polynomial_kernel_invariant : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p : Polynomial K),
    invariant_value K V (LinearMap.ker (evaluation_value K V T p)) T

/-- In particular every polynomial image is invariant under T itself. -/
def self_polynomial_image_invariant : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p : Polynomial K),
    invariant_value K V (LinearMap.range (evaluation_value K V T p)) T

end Specs.D05.M09.CommutantInvariance
