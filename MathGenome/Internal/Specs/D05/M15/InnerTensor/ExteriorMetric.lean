import MathGenome.Internal.Specs.D05.M15.ExteriorPairing
import MathGenome.Internal.Specs.D05.M15.WedgeSign
import MathGenome.Internal.Specs.D05.M12.OnBasis
import MathGenome.Internal.Specs.D05.M11.Nondegenerate
import Mathlib.LinearAlgebra.ExteriorPower.BilinForm

/-! Independent interface for paper.tex:2879–2884. No factorial normalization is
used. The positive form uses the manuscript's first-slot-linear convention.
The coordinate definition makes the increasing wedges of a chosen basis
orthonormal; its determinant formula will prove independence of that choice. -/
noncomputable section
namespace Specs.D05.M15.InnerTensor.ExteriorMetric

abbrev bilinear_type := {K V : Type*} → [Field K] → [AddCommGroup V] →
  [Module K V] → LinearMap.BilinForm K V → (p : ℕ) → LinearMap.BilinForm K (⋀[K]^p V)
abbrev bilinear_value : bilinear_type := fun B p => B.exteriorPower p

abbrev basisMetric_type := {F V I : Type*} → [RCLike F] → [AddCommGroup V] →
  [Module F V] → [Fintype I] → [LinearOrder I] → Module.Basis I F V →
  (p : ℕ) → (⋀[F]^p V) → (⋀[F]^p V) → F
abbrev basisMetric_value : basisMetric_type := fun b p x y =>
  D05.coordinateInner (fun s => (b.exteriorPower p).repr x s)
    (fun s => (b.exteriorPower p).repr y s)

abbrev metric_type := {F V : Type*} → [RCLike F] → [NormedAddCommGroup V] →
  [InnerProductSpace F V] → [FiniteDimensional F V] →
  (p : ℕ) → (⋀[F]^p V) → (⋀[F]^p V) → F
abbrev metric_value : metric_type := fun {F} {V} _ _ _ _ p =>
  basisMetric_value (stdOrthonormalBasis F V).toBasis p

def bilinear_elementary : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (p : ℕ) (x y : Fin p → V),
    bilinear_value B p (exteriorPower.ιMulti K p x) (exteriorPower.ιMulti K p y) =
      Matrix.det (fun i j => B (x i) (y j))

def bilinear_symmetric : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V), B.IsSymm → ∀ p, (bilinear_value B p).IsSymm

def bilinear_nondegenerate : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V),
    LinearMap.Nondegenerate B → ∀ p, LinearMap.Nondegenerate (bilinear_value B p)

def bilinear_unique : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (p : ℕ)
    (C : LinearMap.BilinForm K (⋀[K]^p V)),
    (∀ x y, C (exteriorPower.ιMulti K p x) (exteriorPower.ιMulti K p y) =
      Matrix.det (fun i j => B (x i) (y j))) → C = bilinear_value B p

def bilinear_degree_zero : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (a b : K),
    bilinear_value B 0 ((exteriorPower.zeroEquiv K V).symm a)
      ((exteriorPower.zeroEquiv K V).symm b) = a * b

/-- Positivity is proved on the actual exterior quotient, including zero spaces. -/
def positive_axioms : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] (p : ℕ), D05.IsFirstInnerProduct (metric_value (F := F) (V := V) p)

def positive_elementary : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] (p : ℕ) (x y : Fin p → V),
    metric_value p (exteriorPower.ιMulti F p x) (exteriorPower.ιMulti F p y) =
      Matrix.det (fun i j => D05.firstInner (F := F) (x i) (y j))

def orthonormal_wedges : Prop :=
  ∀ {F V I : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] [Fintype I] [LinearOrder I]
    (b : OrthonormalBasis I F V) (p : ℕ) (s t : Set.powersetCard I p),
    metric_value p (b.toBasis.exteriorPower p s) (b.toBasis.exteriorPower p t) =
      if s = t then 1 else 0

def basis_independent : Prop :=
  ∀ {F V I : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] [Fintype I] [LinearOrder I]
    (b : OrthonormalBasis I F V) (p : ℕ), basisMetric_value b.toBasis p = metric_value p

/-- Full uniqueness among positive first-slot-linear inner products. -/
def positive_unique : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] (p : ℕ) (h : (⋀[F]^p V) → (⋀[F]^p V) → F),
    D05.IsFirstInnerProduct h →
    (∀ x y, h (exteriorPower.ιMulti F p x) (exteriorPower.ιMulti F p y) =
      Matrix.det (fun i j => D05.firstInner (F := F) (x i) (y j))) → h = metric_value p

/-- Even without positivity or Hermitian symmetry, sesquilinearity and the
Gram rule determine the form on the two exterior quotients. -/
def sesquilinear_unique : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] (p : ℕ)
    (h : (⋀[F]^p V) →ₗ[F] (⋀[F]^p V) →ₗ⋆[F] F),
    (∀ x y, h (exteriorPower.ιMulti F p x) (exteriorPower.ιMulti F p y) =
      Matrix.det (fun i j => D05.firstInner (F := F) (x i) (y j))) →
    ∀ u v, h u v = metric_value p u v

def positive_degree_zero : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] (a b : F),
    metric_value 0 ((exteriorPower.zeroEquiv F V).symm a)
      ((exteriorPower.zeroEquiv F V).symm b) = a * starRingEnd F b

/-- The full range p > dim V is included; the form is the unique zero form. -/
def positive_above_dimension : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] (p : ℕ), Module.finrank F V < p →
    ∀ x y : ⋀[F]^p V, metric_value p x y = 0

end Specs.D05.M15.InnerTensor.ExteriorMetric
