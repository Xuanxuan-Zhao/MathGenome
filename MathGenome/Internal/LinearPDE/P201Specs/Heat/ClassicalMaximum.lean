import MathGenome.Internal.LinearPDE.P201Specs.Common.SpatialInterfaces
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-! Independent statements for paper.tex, §H03. All coefficients are restricted
only on the spatial interior and positive times. The time derivative is taken
within `Iic T`, and hence is the left derivative at the top face. -/
noncomputable section
open Set
open scoped ContDiff
namespace P201Specs.HeatMaximum

abbrev Point (n : ℕ) := Space n × ℝ
abbrev Function (n : ℕ) := Point n → ℝ

def closedCylinder {n : ℕ} (Ω : Domain n) (T : ℝ) : Set (Point n) :=
  closure (Ω : Set (Space n)) ×ˢ Icc 0 T

def activeCylinder {n : ℕ} (Ω : Domain n) (T : ℝ) : Set (Point n) :=
  (Ω : Set (Space n)) ×ˢ Ioc 0 T

def parabolicBoundary {n : ℕ} (Ω : Domain n) (T : ℝ) : Set (Point n) :=
  (closure (Ω : Set (Space n)) ×ˢ {0}) ∪
    (frontier (Ω : Set (Space n)) ×ˢ Icc 0 T)

def spatialFirst {n : ℕ} (u : Function n) (z : Point n) : Space n →L[ℝ] ℝ :=
  fderiv ℝ (fun x => u (x, z.2)) z.1

def spatialSecond {n : ℕ} (u : Function n) (z : Point n) :
    Space n →L[ℝ] Space n →L[ℝ] ℝ :=
  fderiv ℝ (fun x => spatialFirst u (x, z.2)) z.1

def timeDerivative {n : ℕ} (T : ℝ) (u : Function n) (z : Point n) : ℝ :=
  derivWithin (fun t => u (z.1, t)) (Iic T) z.2

/-- Spatial C² and time C¹ regularity on Ω × (0,T], with continuous
extensions of the function to the full closed cylinder. Joint continuity of
all the indicated spatial and temporal derivatives encodes C^{2,1}. -/
structure Classical {n : ℕ} (Ω : Domain n) (T : ℝ) (u : Function n) : Prop where
  continuous : ContinuousOn u (closedCylinder Ω T)
  spatial : ∀ t ∈ Ioc 0 T, ContDiffOn ℝ 2 (fun x => u (x,t)) Ω
  temporal : ∀ z ∈ activeCylinder Ω T,
    DifferentiableWithinAt ℝ (fun t => u (z.1,t)) (Iic T) z.2
  continuous_spatialFirst : ContinuousOn (spatialFirst u) (activeCylinder Ω T)
  continuous_spatialSecond : ContinuousOn (spatialSecond u) (activeCylinder Ω T)
  continuous_timeDerivative : ContinuousOn (timeDerivative T u) (activeCylinder Ω T)

structure Coefficients (n : ℕ) where
  a : Point n → Matrix (Fin n) (Fin n) ℝ
  b : Point n → (Fin n → ℝ)
  c : Point n → ℝ

/-- Uniform positive definiteness is expressed by its coordinate quadratic
form; no coefficient extension to the lateral or initial faces is imposed. -/
structure Admissible {n : ℕ} (Ω : Domain n) (T : ℝ) (C : Coefficients n) : Prop where
  continuous_a : ContinuousOn C.a (activeCylinder Ω T)
  continuous_b : ContinuousOn C.b (activeCylinder Ω T)
  continuous_c : ContinuousOn C.c (activeCylinder Ω T)
  symmetric : ∀ z ∈ activeCylinder Ω T, (C.a z).IsSymm
  elliptic : ∃ μ : ℝ, 0 < μ ∧ ∀ z ∈ activeCylinder Ω T, ∀ ξ : Fin n → ℝ,
    μ * (∑ i, (ξ i)^2) ≤ ∑ i, ∑ j, C.a z i j * ξ i * ξ j
  nonpositive : ∀ z ∈ activeCylinder Ω T, C.c z ≤ 0

def operator {n : ℕ} (C : Coefficients n) (T : ℝ) (u : Function n)
    (z : Point n) : ℝ :=
  timeDerivative T u z -
    (∑ i, ∑ j, C.a z i j * spatialSecond u z (coordinate n i) (coordinate n j)) -
    (∑ i, C.b z i * spatialFirst u z (coordinate n i)) - C.c z * u z

/-- Suprema are maxima here by compactness and continuity. -/
def maximum {n : ℕ} (u : Function n) (S : Set (Point n)) : ℝ := sSup (u '' S)

abbrev parabolicBoundaryType := {n : ℕ} → Domain n → ℝ → Set (Point n)

def maximumStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ (Ω : Domain n) (T : ℝ),
    Bornology.IsBounded (Ω : Set (Space n)) → (Ω : Set (Space n)).Nonempty → 0 < T →
    ∀ (C : Coefficients n), Admissible Ω T C → ∀ u : Function n,
    Classical Ω T u → (∀ z ∈ activeCylinder Ω T, operator C T u z ≤ 0) →
    maximum u (closedCylinder Ω T) ≤ max 0 (maximum u (parabolicBoundary Ω T))

def maximumZeroStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ (Ω : Domain n) (T : ℝ),
    Bornology.IsBounded (Ω : Set (Space n)) → (Ω : Set (Space n)).Nonempty → 0 < T →
    ∀ (C : Coefficients n), Admissible Ω T C →
    (∀ z ∈ activeCylinder Ω T, C.c z = 0) → ∀ u : Function n,
    Classical Ω T u → (∀ z ∈ activeCylinder Ω T, operator C T u z ≤ 0) →
    maximum u (closedCylinder Ω T) ≤ maximum u (parabolicBoundary Ω T)

def comparisonStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ (Ω : Domain n) (T : ℝ),
    Bornology.IsBounded (Ω : Set (Space n)) → (Ω : Set (Space n)).Nonempty → 0 < T →
    ∀ (C : Coefficients n), Admissible Ω T C → ∀ u v : Function n,
    Classical Ω T u → Classical Ω T v →
    (∀ z ∈ activeCylinder Ω T, operator C T u z ≤ operator C T v z) →
    (∀ z ∈ parabolicBoundary Ω T, u z ≤ v z) →
    ∀ z ∈ closedCylinder Ω T, u z ≤ v z

def uniquenessStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ (Ω : Domain n) (T : ℝ),
    Bornology.IsBounded (Ω : Set (Space n)) → (Ω : Set (Space n)).Nonempty → 0 < T →
    ∀ (C : Coefficients n), Admissible Ω T C → ∀ u v : Function n,
    Classical Ω T u → Classical Ω T v →
    (∀ z ∈ activeCylinder Ω T, operator C T u z = operator C T v z) →
    (∀ z ∈ parabolicBoundary Ω T, u z = v z) →
    Set.EqOn u v (closedCylinder Ω T)

end P201Specs.HeatMaximum
