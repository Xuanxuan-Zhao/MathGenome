import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.ActiveConstraintCoordinates
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.ExtremaInterfaces

/-! d04:05:active-constraints. Inequalities use the convention h ≥ 0.
The active index subtype is the one already used by constraint coordinates.
No convexity, existence of an optimizer, or further constraint qualification
is assumed. All finite dimensions, including empty constraint blocks, occur. -/
noncomputable section
open Set
namespace Specs.D04.C05.ActiveConstraints
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C05.ExtremaInterfaces.Model
open Specs.D04.C05.ActiveConstraintCoordinates

/-- The full covector identity, expressed on arbitrary ambient vectors. -/
def MultiplierEquation {n q s : ℕ} (f : E n → ℝ) (g : E n → E q)
    (h : E n → E s) (a : E n)
    (p : (Fin q → ℝ) × (Active h a → ℝ)) : Prop :=
  (∀ i, 0 ≤ p.2 i) ∧ ∀ v : E n,
    totalDerivative f a v =
      (∑ j, p.1 j * totalDerivative (fun x => g x j) a v) +
      ∑ i : Active h a, p.2 i * totalDerivative (fun x => h x i.val) a v

/-- Inactive multipliers are extended by zero, with no choice of active set. -/
def extendMultiplier {n s : ℕ} (h : E n → E s) (a : E n)
    (μ : Active h a → ℝ) (i : Fin s) : ℝ :=
  if hi : h a i = 0 then μ ⟨i, hi⟩ else 0

def lagrangian {n q s : ℕ} (f : E n → ℝ) (g : E n → E q)
    (h : E n → E s) (lam : Fin q → ℝ) (μ : Fin s → ℝ) (x : E n) : ℝ :=
  f x - (∑ j, lam j * g x j) - ∑ i, μ i * h x i

def active_constraints_minimumType : Prop :=
  ∀ {n q s : ℕ} (U : Set (E n)) (f : E n → ℝ) (g : E n → E q)
    (h : E n → E s) (c : E q) (a : E n),
    IsOpen U → CrOn 1 U f → CrOn 1 U g → CrOn 1 U h →
    LinearIndependent ℝ (constraintRows g h a) →
    LocalMinimumOn (Feasible U g h c) f a →
    ∃! p : (Fin q → ℝ) × (Active h a → ℝ), MultiplierEquation f g h a p

def active_constraints_extensionType : Prop :=
  ∀ {n q s : ℕ} (U : Set (E n)) (f : E n → ℝ) (g : E n → E q)
    (h : E n → E s) (a : E n)
    (p : (Fin q → ℝ) × (Active h a → ℝ)),
    IsOpen U → a ∈ U → CrOn 1 U f → CrOn 1 U g → CrOn 1 U h →
    MultiplierEquation f g h a p →
    let μ := extendMultiplier h a p.2
    (∀ i, 0 ≤ μ i) ∧ (∀ i, h a i ≠ 0 → μ i = 0) ∧
    (∀ i, μ i * h a i = 0) ∧
    (∀ v : E n, totalDerivative f a v =
      (∑ j, p.1 j * totalDerivative (fun x => g x j) a v) +
      ∑ i, μ i * totalDerivative (fun x => h x i) a v) ∧
    HasTotalDerivative U (lagrangian f g h p.1 μ) 0 a

/-- The maximum rule is the minimum rule for -f, with the same nonnegative
active multipliers and the Lagrangian -f - lamg - μh. -/
def active_constraints_maximumType : Prop :=
  ∀ {n q s : ℕ} (U : Set (E n)) (f : E n → ℝ) (g : E n → E q)
    (h : E n → E s) (c : E q) (a : E n),
    IsOpen U → CrOn 1 U f → CrOn 1 U g → CrOn 1 U h →
    LinearIndependent ℝ (constraintRows g h a) →
    LocalMaximumOn (Feasible U g h c) f a →
    ∃! p : (Fin q → ℝ) × (Active h a → ℝ),
      MultiplierEquation (fun x => -f x) g h a p

/-- With no active inequalities the equation and uniqueness reduce to the
equality multiplier rule, even when the list of inactive inequalities is nonempty. -/
def active_constraints_no_activeType : Prop :=
  ∀ {n q s : ℕ} (U : Set (E n)) (f : E n → ℝ) (g : E n → E q)
    (h : E n → E s) (c : E q) (a : E n),
    IsOpen U → CrOn 1 U f → CrOn 1 U g → CrOn 1 U h →
    LinearIndependent ℝ (constraintRows g h a) → (∀ i, h a i ≠ 0) →
    (LocalMinimumOn (Feasible U g h c) f a ∨
      LocalMaximumOn (Feasible U g h c) f a) →
    ∃! lam : Fin q → ℝ, ∀ v : E n,
      totalDerivative f a v = ∑ j, lam j * totalDerivative (fun x => g x j) a v

end Specs.D04.C05.ActiveConstraints
