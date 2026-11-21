import MathGenome.Internal.Specs.D05.M08.Evaluation
import MathGenome.Internal.Specs.D05.M09.FieldDependence
import Mathlib.LinearAlgebra.Matrix.Block

/-! Independent specifications for polynomial spectral mapping,
`paper.tex:1350–1356`. Spectra below are sets of eigenvalues over the named
field. The chosen-basis formula is an equality of formal characteristic
polynomials, so it retains algebraic multiplicities. All finite dimensions,
including zero, are allowed. -/
noncomputable section
namespace Specs.D05.M09.CommutingSpectrum.PolynomialMapping
open Polynomial Module

def eigenvector_polynomial : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : End K V) (p : K[X]) (μ : K) (v : V),
    T v = μ • v → aeval T p v = p.eval μ • v

def spectral_inclusion : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : End K V) (p : K[X]),
    (p.eval '' {μ | T.HasEigenvalue μ}) ⊆ {μ | (aeval T p).HasEigenvalue μ}

/-- Both triangularity and the actual diagonal of the evaluated matrix. -/
def triangular_polynomial : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Basis (Fin n) K V) (T : End K V) (p : K[X]),
    (LinearMap.toMatrix b b T).IsUpperTriangular →
    (LinearMap.toMatrix b b (aeval T p)).IsUpperTriangular ∧
    ∀ j, LinearMap.toMatrix b b (aeval T p) j j =
      p.eval (LinearMap.toMatrix b b T j j)

def charpoly_in_triangular_basis : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (b : Basis (Fin n) K V)
    (T : End K V) (p : K[X]),
    (LinearMap.toMatrix b b T).IsUpperTriangular →
    (aeval T p).charpoly =
      ∏ j : Fin n, (X - C (p.eval (LinearMap.toMatrix b b T j j)))

def spectral_mapping : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : End K V) (p : K[X]),
    T.charpoly.Splits →
    {μ | (aeval T p).HasEigenvalue μ} = p.eval '' {μ | T.HasEigenvalue μ}

def complex_spectral_mapping : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : End ℂ V) (p : ℂ[X]),
    {μ | (aeval T p).HasEigenvalue μ} = p.eval '' {μ | T.HasEigenvalue μ}

/-- The empty product and empty spectrum in dimension zero. -/
def zero_dimensional : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : End K V) (p : K[X]),
    Module.finrank K V = 0 →
    (aeval T p).charpoly = 1 ∧ {μ | (aeval T p).HasEigenvalue μ} = ∅

def rotation_square : Prop :=
  ∀ (K : Type*) [Field K],
    aeval (Specs.D05.M09.FieldDependence.rotation K) (X ^ 2 : K[X]) =
      -(LinearMap.id : End K (Fin 2 → K))

/-- A concrete failure of equality without splitting, with both exact spectra. -/
def rotation_counterexample : Prop :=
  let R := Specs.D05.M09.FieldDependence.rotation ℝ
  let p : ℝ[X] := X ^ 2
  {μ | R.HasEigenvalue μ} = ∅ ∧
    aeval R p = -(LinearMap.id : End ℝ (Fin 2 → ℝ)) ∧
    {μ | (aeval R p).HasEigenvalue μ} = {-1} ∧
    {μ | (aeval R p).HasEigenvalue μ} ≠ p.eval '' {μ | R.HasEigenvalue μ}

end Specs.D05.M09.CommutingSpectrum.PolynomialMapping
