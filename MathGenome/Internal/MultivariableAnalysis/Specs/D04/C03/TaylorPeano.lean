import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.HigherInterfaces
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Independent statements of d04:03:taylor-peano and its pointwise,
order-zero, dimension-zero and scalar scope in d04:03:scope.
Ambient functions represent their restrictions to the open domain. The shared
recursive predicate asserts derivative existence, not continuity of the top
derivative. The generic statements include every Euclidean source and target,
as well as the operator-valued targets used in the induction. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace Specs.D04.C03.TaylorPeano
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C03.HigherInterfaces.Model

/-- All positive orders under the original recursive pointwise hypothesis. -/
def taylorPeanoType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (k : ℕ), 1 ≤ k → ∀ (U : Set X) (f : X → Y) (a : X),
    TimesDifferentiableAt k U f a →
    taylorRemainder k f a =o[𝓝[≠] (0 : X)] (fun h => ‖h‖ ^ k)

/-- Order zero requires only continuity at the base point. The statement
includes the zero increment, where the remainder is zero. -/
def taylorPeano_zeroType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (f : X → Y) (a : X), ContinuousAt f a →
    taylorRemainder 0 f a =o[𝓝 (0 : X)] (fun h => ‖h‖ ^ 0)

/-- The remainder in the asymptotic assertion is the error in this exact
Taylor expansion, with the prescribed value at the zero increment. -/
def taylorPeano_expansionType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (k : ℕ) (f : X → Y) (a h : X),
    f (a+h) = taylorPolynomial k f a h + taylorRemainder k f a h ∧
      taylorRemainder k f a 0 = 0

/-- C^k near a is a sufficient special case, with no convexity or global
regularity assumption on the open neighborhood. -/
def taylorPeano_crOnType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (k : ℕ), 1 ≤ k → ∀ (U : Set X) (f : X → Y) (a : X),
    IsOpen U → a ∈ U → CrOn k U f →
    taylorRemainder k f a =o[𝓝[≠] (0 : X)] (fun h => ‖h‖ ^ k)

def taylorPeano_source_zeroType : Prop :=
  ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (k : ℕ) (f : E 0 → Y) (a h : E 0), taylorRemainder k f a h = 0

def taylorPeano_target_zeroType : Prop :=
  ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X],
  ∀ (k : ℕ) (f : X → E 0) (a h : X), taylorRemainder k f a h = 0

/-- Identification of the multilinear coefficients with ordinary derivatives
on the scalar real line, including the constant term. -/
def taylorPolynomial_scalarType : Prop :=
  ∀ (k : ℕ) (f : ℝ → ℝ) (a h : ℝ), taylorPolynomial k f a h =
    ∑ j ∈ Finset.range (k+1), iteratedDeriv j f a / (j.factorial : ℝ) * h^j

def taylorPeano_scalarType : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (U : Set ℝ) (f : ℝ → ℝ) (a : ℝ),
    TimesDifferentiableAt k U f a →
    (fun h => f (a+h) - ∑ j ∈ Finset.range (k+1),
      iteratedDeriv j f a / (j.factorial : ℝ) * h^j) =o[𝓝[≠] (0 : ℝ)] (fun h => |h|^k)

/-- The actual n=m=1 Euclidean objects have the same scalar Taylor
coefficients after taking their standard coordinates. The ordinary scalar
function here uses the centered coordinate t, so its derivatives are at 0. -/
def taylorPolynomial_one_coordinateType : Prop :=
  ∀ (k : ℕ) (U : Set (E 1)) (f : E 1 → E 1) (a h : E 1),
    TimesDifferentiableAt k U f a →
    taylorPolynomial k f a h 0 = ∑ j ∈ Finset.range (k+1),
      iteratedDeriv j (fun t : ℝ => f (a+t • standardBasis 1 0) 0) 0 /
        (j.factorial : ℝ) * (h 0)^j

def taylorPeano_one_coordinateType : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (U : Set (E 1)) (f : E 1 → E 1) (a : E 1),
    TimesDifferentiableAt k U f a →
    (fun t : ℝ => f (a+t • standardBasis 1 0) 0 - ∑ j ∈ Finset.range (k+1),
      iteratedDeriv j (fun s : ℝ => f (a+s • standardBasis 1 0) 0) 0 /
        (j.factorial : ℝ) * t^j) =o[𝓝[≠] (0 : ℝ)] (fun t => |t|^k)

def taylorPeano_one_coordinate_zeroType : Prop :=
  ∀ (f : E 1 → E 1) (a : E 1), ContinuousAt f a →
    (fun t : ℝ => f (a+t • standardBasis 1 0) 0 - f a 0) =o[𝓝 (0 : ℝ)]
      (fun _ => (1 : ℝ))

end Specs.D04.C03.TaylorPeano
