import Mathlib.Data.Matrix.Mul
import Mathlib.Data.EReal.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
Canonical standard-form LPs from paper.tex §v05-01, Theorem 5.1.
All finite index types, including empty types, are permitted. Objectives are real;
values are in the complete extended real line. Thus an empty primal feasible set
has value +∞ and an empty dual feasible set has value −∞. Optimizing-direction
unboundedness means arbitrarily low/high feasible objective values. An optimal
point is feasible and attains the extended value at its real objective value.
No attainment or strong-duality assertion is assumed by these definitions.
-/
noncomputable section
open Matrix Set
universe u v
namespace VariationalNotes.Ch05.LinearProgramModels.Specs

def primalFeasibleType :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n],
    Matrix m n ℝ → (m → ℝ) → (n → ℝ) → Prop
def primalFeasible {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  (A : Matrix m n ℝ) (b : m → ℝ) (x : n → ℝ) : Prop :=
  A *ᵥ x = b ∧ ∀ i, 0 ≤ x i

def dualFeasibleType :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n],
    Matrix m n ℝ → (n → ℝ) → (m → ℝ) → Prop
def dualFeasible {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  (A : Matrix m n ℝ) (c : n → ℝ) (y : m → ℝ) : Prop :=
  ∀ i, (Aᵀ *ᵥ y) i ≤ c i

def primalObjectiveType := ∀ {n : Type u} [Fintype n], (n → ℝ) → (n → ℝ) → ℝ
def primalObjective {n : Type u} [Fintype n] (c x : n → ℝ) : ℝ :=
  c ⬝ᵥ x

def dualObjectiveType := ∀ {m : Type u} [Fintype m], (m → ℝ) → (m → ℝ) → ℝ
def dualObjective {m : Type u} [Fintype m] (b y : m → ℝ) : ℝ :=
  b ⬝ᵥ y

def primalValueType :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n],
    Matrix m n ℝ → (m → ℝ) → (n → ℝ) → EReal
def primalValue {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) : EReal :=
  sInf ((fun x => (primalObjective c x : EReal)) '' {x | primalFeasible A b x})

def dualValueType :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n],
    Matrix m n ℝ → (m → ℝ) → (n → ℝ) → EReal
def dualValue {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) : EReal :=
  sSup ((fun y => (dualObjective b y : EReal)) '' {y | dualFeasible A c y})

def PrimalUnboundedType :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n],
    Matrix m n ℝ → (m → ℝ) → (n → ℝ) → Prop
def PrimalUnbounded {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) : Prop :=
  ∀ r : ℝ, ∃ x, primalFeasible A b x ∧ primalObjective c x < r

def DualUnboundedType :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n],
    Matrix m n ℝ → (m → ℝ) → (n → ℝ) → Prop
def DualUnbounded {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) : Prop :=
  ∀ r : ℝ, ∃ y, dualFeasible A c y ∧ r < dualObjective b y

def PrimalOptimalType :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n],
    Matrix m n ℝ → (m → ℝ) → (n → ℝ) → (n → ℝ) → Prop
def PrimalOptimal {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (x : n → ℝ) : Prop :=
  primalFeasible A b x ∧ primalValue A b c = (primalObjective c x : EReal)

def DualOptimalType :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n],
    Matrix m n ℝ → (m → ℝ) → (n → ℝ) → (m → ℝ) → Prop
def DualOptimal {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (y : m → ℝ) : Prop :=
  dualFeasible A c y ∧ dualValue A b c = (dualObjective b y : EReal)

def PrimalAttainsType :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n],
    Matrix m n ℝ → (m → ℝ) → (n → ℝ) → ℝ → Prop
def PrimalAttains {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (p : ℝ) : Prop :=
  ∃ x, PrimalOptimal A b c x ∧ primalObjective c x = p

def DualAttainsType :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n],
    Matrix m n ℝ → (m → ℝ) → (n → ℝ) → ℝ → Prop
def DualAttains {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (p : ℝ) : Prop :=
  ∃ y, DualOptimal A b c y ∧ dualObjective b y = p

def gap_identity : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (x : n → ℝ) (y : m → ℝ),
  primalFeasible A b x →
  primalObjective c x - dualObjective b y = ∑ i, x i * (c i - (Aᵀ *ᵥ y) i)

def gap_nonnegative : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (x : n → ℝ) (y : m → ℝ),
  primalFeasible A b x → dualFeasible A c y →
  0 ≤ primalObjective c x - dualObjective b y

def weakDuality : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (x : n → ℝ) (y : m → ℝ),
  primalFeasible A b x → dualFeasible A c y →
  dualObjective b y ≤ primalObjective c x

def gap_eq_zero_iff : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (x : n → ℝ) (y : m → ℝ),
  primalFeasible A b x → dualFeasible A c y →
  (primalObjective c x - dualObjective b y = 0 ↔
    ∀ i, x i * (c i - (Aᵀ *ᵥ y) i) = 0)

def primalValue_le : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (x : n → ℝ),
  primalFeasible A b x → primalValue A b c ≤ (primalObjective c x : EReal)

def le_dualValue : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (y : m → ℝ),
  dualFeasible A c y → (dualObjective b y : EReal) ≤ dualValue A b c

def weakDuality_values : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ), dualValue A b c ≤ primalValue A b c

def primalValue_eq_top_iff : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ),
  primalValue A b c = ⊤ ↔ ¬ ∃ x, primalFeasible A b x

def dualValue_eq_bot_iff : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ),
  dualValue A b c = ⊥ ↔ ¬ ∃ y, dualFeasible A c y

def primalUnbounded_iff_value_eq_bot : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ),
  PrimalUnbounded A b c ↔ primalValue A b c = ⊥

def dualUnbounded_iff_value_eq_top : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ),
  DualUnbounded A b c ↔ dualValue A b c = ⊤

def primalOptimal_iff : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (x : n → ℝ),
  PrimalOptimal A b c x ↔ primalFeasible A b x ∧
    ∀ z, primalFeasible A b z → primalObjective c x ≤ primalObjective c z

def dualOptimal_iff : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (y : m → ℝ),
  DualOptimal A b c y ↔ dualFeasible A c y ∧
    ∀ z, dualFeasible A c z → dualObjective b z ≤ dualObjective b y

def primalAttains_value : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (p : ℝ),
  PrimalAttains A b c p → primalValue A b c = (p : EReal)

def dualAttains_value : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (p : ℝ),
  DualAttains A b c p → dualValue A b c = (p : EReal)

end VariationalNotes.Ch05.LinearProgramModels.Specs
