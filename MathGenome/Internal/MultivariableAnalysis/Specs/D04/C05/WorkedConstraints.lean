import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.ExtremaInterfaces
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.CriticalConeNecessity
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-! Independent statements for the complete worked example d04:05:worked-constraints.
All objectives and constraints below are literal Euclidean functions. The full
second differential uses the library's iterated total derivative. -/
noncomputable section
open Set
namespace Specs.D04.C05.WorkedConstraints
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C05.ExtremaInterfaces.Model
open Specs.D04.C05.CriticalConeNecessity
namespace Model

def sphere (n : ℕ) : Set (E n) := {x | ‖x‖ = 1}
def unit {n : ℕ} (v : E n) : E n := ‖v‖⁻¹ • v
def linearObjective {n : ℕ} (v x : E n) : ℝ := inner ℝ v x
def sphereLagrangian {n : ℕ} (v : E n) (lam : ℝ) (x : E n) : ℝ :=
  inner ℝ v x - lam * ‖x‖ ^ 2

def point (a b : ℝ) : E 2 := WithLp.toLp 2 ![a,b]
def disk : Set (E 2) := {x | x 0 ^ 2 + x 1 ^ 2 ≤ 1}
def diskConstraint (x : E 2) : ℝ := 1 - x 0 ^ 2 - x 1 ^ 2
def square : Set (E 2) := {x | 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1}
def cornerObjective (x : E 2) : ℝ := x 0 + x 1
def boxConstraints (x : E 2) : E 4 := WithLp.toLp 2 ![x 0,x 1,1-x 0,1-x 1]
def noEqualities (_ : E 2) : E 0 := 0

def boxMultipliers : Fin 4 → ℝ := ![1,1,0,0]
end Model
open Model

def sphere_compact_existenceType : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ v : E n,
    IsCompact (sphere n) ∧ (sphere n).Nonempty ∧
    ∃ a b, GlobalMinimumOn (sphere n) (linearObjective v) a ∧
      GlobalMaximumOn (sphere n) (linearObjective v) b

def sphere_constraint_derivativeType : Prop :=
  ∀ {n : ℕ} (x : E n),
    HasFDerivAt (fun y : E n => ‖y‖^2) (2 • innerSL ℝ x) x ∧
    (x ∈ sphere n → Function.Surjective (fderiv ℝ (fun y : E n => ‖y‖^2) x)) ∧
    ∀ z, fderiv ℝ (fun y : E n => ‖y‖^2) x z = 0 ↔ inner ℝ x z = 0

def sphere_extremaType : Prop :=
  ∀ {n : ℕ} (v : E n), v ≠ 0 →
    (-unit v) ∈ sphere n ∧ unit v ∈ sphere n ∧
    linearObjective v (-unit v) = -‖v‖ ∧ linearObjective v (unit v) = ‖v‖ ∧
    GlobalMinimumOn (sphere n) (linearObjective v) (-unit v) ∧
    GlobalMaximumOn (sphere n) (linearObjective v) (unit v) ∧
    (∀ x ∈ sphere n, -‖v‖ ≤ linearObjective v x ∧ linearObjective v x ≤ ‖v‖ ∧
      (linearObjective v x = -‖v‖ ↔ x = -unit v) ∧
      (linearObjective v x = ‖v‖ ↔ x = unit v)) ∧
    (∀ x, GlobalMinimumOn (sphere n) (linearObjective v) x ↔ x = -unit v) ∧
    (∀ x, GlobalMaximumOn (sphere n) (linearObjective v) x ↔ x = unit v)

/-- Exact quadratic growth holds globally on the sphere, even when n=1. -/
def sphere_growthType : Prop :=
  ∀ {n : ℕ} (v : E n), v ≠ 0 →
    StrictLocalMinimumOn (sphere n) (linearObjective v) (-unit v) ∧
    StrictLocalMaximumOn (sphere n) (linearObjective v) (unit v) ∧
    0 < ‖v‖/2 ∧ ∀ x ∈ sphere n,
      linearObjective v x = -‖v‖ + (‖v‖/2) * ‖x - (-unit v)‖^2 ∧
      linearObjective v x = ‖v‖ - (‖v‖/2) * ‖x - unit v‖^2

/-- All solutions of the regular multiplier equations, with fixed sign convention. -/
def sphere_multipliersType : Prop :=
  ∀ {n : ℕ} (v : E n), v ≠ 0 → ∀ x ∈ sphere n, ∀ lam : ℝ,
    (v = (2*lam) • x ↔
      (x = -unit v ∧ lam = -‖v‖/2) ∨ (x = unit v ∧ lam = ‖v‖/2)) ∧
    (fderiv ℝ (linearObjective v) x = lam • fderiv ℝ (fun y : E n => ‖y‖^2) x ↔
      v = (2*lam) • x)

def sphere_lagrangian_hessianType : Prop :=
  ∀ {n : ℕ} (v x : E n) (lam : ℝ) (z w : E n),
    iteratedFDeriv ℝ 2 (sphereLagrangian v lam) x ![z,w] =
      (-2*lam) * inner ℝ z w

/-- Restricting the Hessian to x-perp gives the positive and negative tests. -/
def sphere_hessian_classificationType : Prop :=
  ∀ {n : ℕ} (v : E n), v ≠ 0 → ∀ z : E n, z ≠ 0 →
    (inner ℝ (-unit v) z = 0 →
      0 < iteratedFDeriv ℝ 2 (sphereLagrangian v (-‖v‖/2)) (-unit v) ![z,z]) ∧
    (inner ℝ (unit v) z = 0 →
      iteratedFDeriv ℝ 2 (sphereLagrangian v (‖v‖/2)) (unit v) ![z,z] < 0)

def sphere_one_dimensionType : Prop :=
  (sphere 1 = {x : E 1 | x 0 = -1 ∨ x 0 = 1}) ∧
  ∀ a ∈ sphere 1,
    (∃ r > 0, ∀ x ∈ sphere 1, ‖x-a‖ < r → x = a) ∧
    ∀ f : E 1 → ℝ, StrictLocalMinimumOn (sphere 1) f a ∧
      StrictLocalMaximumOn (sphere 1) f a

def sphere_zero_objectiveType : Prop :=
  ∀ {n : ℕ} (a : E n), a ∈ sphere n →
    GlobalMinimumOn (sphere n) (linearObjective 0) a ∧
    GlobalMaximumOn (sphere n) (linearObjective 0) a

def singular_originType : Prop :=
  let S : Set (E 2) := {x | x 0 ^ 2 + x 1 ^ 2 = 0}
  S = {0} ∧
  (∀ f : E 2 → ℝ, GlobalMinimumOn S f 0 ∧ GlobalMaximumOn S f 0 ∧
    StrictLocalMinimumOn S f 0 ∧ StrictLocalMaximumOn S f 0) ∧
  (∀ lam : ℝ, fderiv ℝ (fun x : E 2 => x 0) 0 ≠
    lam • fderiv ℝ (fun x : E 2 => x 0 ^ 2 + x 1 ^ 2) 0)

def singular_axisType : Prop :=
  let S : Set (E 2) := {x | x 1 ^ 2 = 0}
  S = {x | x 1 = 0} ∧ ∀ a ∈ S,
    (∀ x ∈ S, x 1 = 0) ∧
    GlobalMinimumOn S (fun x => x 1) a ∧ GlobalMaximumOn S (fun x => x 1) a ∧
    fderiv ℝ (fun x : E 2 => x 1 ^ 2) a = 0 ∧
    (∀ lam : ℝ, fderiv ℝ (fun x : E 2 => x 1) a ≠
      lam • fderiv ℝ (fun x : E 2 => x 1 ^ 2) a)

def disk_extremaType : Prop :=
  disk = {x | ‖x‖ ≤ 1} ∧ disk = {x | 0 ≤ diskConstraint x} ∧
  GlobalMinimumOn disk (fun x => x 0) (point (-1) 0) ∧
  GlobalMaximumOn disk (fun x => x 0) (point 1 0) ∧
  (∀ x, GlobalMinimumOn disk (fun x => x 0) x ↔ x = point (-1) 0) ∧
  (∀ x, GlobalMaximumOn disk (fun x => x 0) x ↔ x = point 1 0) ∧
  ¬ StationaryPoint univ (fun x : E 2 => x 0) (point (-1) 0) ∧
  ¬ StationaryPoint univ (fun x : E 2 => x 0) (point 1 0)

def disk_multipliersType : Prop :=
  (0 : ℝ) ≤ 1/2 ∧
  diskConstraint (point (-1) 0) = 0 ∧ diskConstraint (point 1 0) = 0 ∧
  fderiv ℝ (fun x : E 2 => x 0) (point (-1) 0) =
    (1/2 : ℝ) • fderiv ℝ diskConstraint (point (-1) 0) ∧
  fderiv ℝ (fun x : E 2 => -x 0) (point 1 0) =
    (1/2 : ℝ) • fderiv ℝ diskConstraint (point 1 0)

def corner_constraintsType : Prop :=
  square = {x | ∀ i, 0 ≤ boxConstraints x i} ∧
  (∀ i : Fin 4, boxConstraints 0 i = 0 ↔ i = 0 ∨ i = 1) ∧
  (∀ i, 0 ≤ boxMultipliers i) ∧
  (∀ i, boxMultipliers i * boxConstraints 0 i = 0) ∧
  fderiv ℝ cornerObjective 0 =
    ∑ i : Fin 4, boxMultipliers i • fderiv ℝ (fun x => boxConstraints x i) 0 ∧
  criticalCone cornerObjective noEqualities boxConstraints 0 = {0}

def corner_growthType : Prop :=
  GlobalMinimumOn square cornerObjective 0 ∧
  StrictLocalMinimumOn square cornerObjective 0 ∧
  (∀ x ∈ square, Real.sqrt (x 0 ^ 2 + x 1 ^ 2) ≤ cornerObjective x) ∧
  ∃ c > 0, ∃ r > 0, ∀ x ∈ square, ‖x‖ < r →
    cornerObjective 0 + c * ‖x - 0‖^2 ≤ cornerObjective x

end Specs.D04.C05.WorkedConstraints
