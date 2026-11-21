import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.Conjugates
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
Independent statements for paper.tex §v04-01, lines 1698–1711.
The marginal takes values in the full extended reals, even though the
perturbation function never takes minus infinity. The algebraic assertions
hold in arbitrary real vector spaces, hence in the locally convex Hausdorff
spaces of the manuscript. No topological regularity of Φ is required.
-/
noncomputable section
universe u v
namespace VariationalNotes.Ch04.Specs

open VariationalNotes.ConvexAnalysis.Specs

def marginal {X : Type u} {Y : Type v} (Φ : X × Y → WithTop ℝ) (u : Y) : EReal :=
  ⨅ x : X, toEReal (Φ (x, u))

def marginalType : Type (max u v + 1) :=
  ∀ {X : Type u} {Y : Type v}, (X × Y → WithTop ℝ) → Y → EReal

def primalValue {X : Type u} {Y : Type v} [Zero Y]
    (Φ : X × Y → WithTop ℝ) : EReal := marginal Φ 0

def primalValueType : Type (max u v + 1) :=
  ∀ {X : Type u} {Y : Type v} [Zero Y], (X × Y → WithTop ℝ) → EReal

/-- Full extended-real conjugacy. Finite dual evaluations make subtraction
unambiguous even at either infinite primal value. -/
def extendedConjugate {Y : Type v} [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    (f : Y → EReal) (y : Y →L[ℝ] ℝ) : EReal :=
  ⨆ u : Y, (y u : EReal) - f u

def extendedConjugateType : Type (v + 1) :=
  ∀ {Y : Type v} [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y],
    (Y → EReal) → (Y →L[ℝ] ℝ) → EReal

def marginalConjugate {X : Type u} {Y : Type v}
    [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    (Φ : X × Y → WithTop ℝ) (y : Y →L[ℝ] ℝ) : EReal :=
  extendedConjugate (marginal Φ) y

def marginalConjugateType : Type (max u v + 1) :=
  ∀ {X : Type u} {Y : Type v} [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y],
    (X × Y → WithTop ℝ) → (Y →L[ℝ] ℝ) → EReal

/-- The continuous product functional corresponding to (0,y) is y ∘ snd. -/
def perturbationDualObjective {X : Type u} {Y : Type v}
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    (Φ : X × Y → WithTop ℝ) (y : Y →L[ℝ] ℝ) : EReal :=
  -conjugate Φ (y.comp (ContinuousLinearMap.snd ℝ X Y))

def perturbationDualObjectiveType : Type (max u v + 1) :=
  ∀ {X : Type u} {Y : Type v}
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y],
    (X × Y → WithTop ℝ) → (Y →L[ℝ] ℝ) → EReal

def marginal_le_candidate : Prop :=
  ∀ {X : Type u} {Y : Type v} (Φ : X × Y → WithTop ℝ) (x : X) (u : Y),
    marginal Φ u ≤ toEReal (Φ (x, u))

/-- Records the infimum of an empty fiber as well, though vector spaces
always have a zero vector. -/
def marginal_empty : Prop :=
  ∀ {X : Type u} {Y : Type v} [IsEmpty X] (Φ : X × Y → WithTop ℝ) (u : Y),
    marginal Φ u = ⊤

def extendedConjugate_toEReal : Prop :=
  ∀ {Y : Type v} [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    (f : Y → WithTop ℝ) (y : Y →L[ℝ] ℝ),
    extendedConjugate (fun u => toEReal (f u)) y = conjugate f y

def marginal_convex_finite : Prop :=
  ∀ {X : Type u} {Y : Type v} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] (Φ : X × Y → WithTop ℝ),
    IsConvex Φ → ∀ (u v : Y) (r s : ℝ),
    marginal Φ u = (r : EReal) → marginal Φ v = (s : EReal) →
    ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
    marginal Φ (a • u + b • v) ≤ ((a * r + b * s : ℝ) : EReal)

/-- Either endpoint may be minus infinity; the other needs only one
finite candidate, not a finite infimum or an attained minimum. -/
def marginal_eq_bot_of_endpoint : Prop :=
  ∀ {X : Type u} {Y : Type v} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] (Φ : X × Y → WithTop ℝ),
    IsConvex Φ → ∀ u v : Y,
    ((marginal Φ u = ⊥ ∧ ∃ x : X, ∃ r : ℝ, Φ (x, v) = (r : WithTop ℝ)) ∨
     (marginal Φ v = ⊥ ∧ ∃ x : X, ∃ r : ℝ, Φ (x, u) = (r : WithTop ℝ))) →
    ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
    marginal Φ (a • u + b • v) = ⊥

end VariationalNotes.Ch04.Specs
