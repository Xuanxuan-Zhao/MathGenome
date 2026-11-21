import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.PerturbationModels
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.Subgradients

/-!
Independent specification of the conjugacy, weak bound, and support clauses of
paper.tex, Theorem `thm:perturbation-duality` (§v04-01, 1713–1741).
All infima and suprema use EReal. The canonical WithTop representative is used
only after excluding minus infinity, and its value bridge is an explicit target.
The algebraic results need fewer hypotheses than the manuscript; the final
package records the original locally convex Hausdorff setting and properness.
The lower-semicontinuity criterion is allocated to PerturbationExactness.
-/
noncomputable section
universe u v
namespace VariationalNotes.Ch04.Specs
open VariationalNotes.ConvexAnalysis.Specs

/-- Properness for a function which initially may take either infinite value. -/
def ExtendedProper {Y : Type v} (f : Y → EReal) : Prop :=
  (∀ u, f u ≠ ⊥) ∧ ∃ u, ∃ r : ℝ, f u = (r : EReal)
def ExtendedProperType : Type (v + 1) := ∀ {Y : Type v}, (Y → EReal) → Prop

/-- Under properness this is precisely v, with its codomain restricted to
(-∞,+∞]. The default is irrelevant under that hypothesis. -/
def marginalFunction {X : Type u} {Y : Type v} (Φ : X × Y → WithTop ℝ)
    (u : Y) : WithTop ℝ := (marginal Φ u).unbotD ⊤
def marginalFunctionType : Type (max u v + 1) :=
  ∀ {X : Type u} {Y : Type v}, (X × Y → WithTop ℝ) → Y → WithTop ℝ

def extendedBiconjugate {Y : Type v} [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    (f : Y → EReal) (u : Y) : EReal :=
  ⨆ y : Y →L[ℝ] ℝ, (y u : EReal) - extendedConjugate f y

def extendedBiconjugateType : Type (v + 1) :=
  ∀ {Y : Type v} [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y],
    (Y → EReal) → Y → EReal

def perturbationDualValue {X : Type u} {Y : Type v}
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    (Φ : X × Y → WithTop ℝ) : EReal :=
  ⨆ y : Y →L[ℝ] ℝ, perturbationDualObjective Φ y

def perturbationDualValueType : Type (max u v + 1) :=
  ∀ {X : Type u} {Y : Type v}
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y],
    (X × Y → WithTop ℝ) → EReal

def marginalFunction_representation : Prop :=
  ∀ {X : Type u} {Y : Type v} (Φ : X × Y → WithTop ℝ),
    (∀ u, marginal Φ u ≠ ⊥) → ∀ u,
      toEReal (marginalFunction Φ u) = marginal Φ u

def marginal_conjugate_identity : Prop :=
  ∀ {X : Type u} {Y : Type v}
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    (Φ : X × Y → WithTop ℝ) (y : Y →L[ℝ] ℝ),
    marginalConjugate Φ y = conjugate Φ (y.comp (ContinuousLinearMap.snd ℝ X Y))

/-- This identifies the full-extended-real biconjugate with the existing
WithTop interface whenever the latter is applicable. -/
def marginal_biconjugate_bridge : Prop :=
  ∀ {X : Type u} {Y : Type v} [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    (Φ : X × Y → WithTop ℝ), (∀ u, marginal Φ u ≠ ⊥) → ∀ u,
    extendedBiconjugate (marginal Φ) u = biconjugate (marginalFunction Φ) u

def perturbation_dual_bound : Prop :=
  ∀ {X : Type u} {Y : Type v}
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    (Φ : X × Y → WithTop ℝ) (p : ℝ), marginal Φ 0 = (p : EReal) →
    perturbationDualValue Φ = extendedBiconjugate (marginal Φ) 0 ∧
    extendedBiconjugate (marginal Φ) 0 ≤ (p : EReal) ∧
    perturbationDualValue Φ ≤ (p : EReal) ∧
    ∀ y, perturbationDualObjective Φ y ≤ (p : EReal)

def perturbation_attainment : Prop :=
  ∀ {X : Type u} {Y : Type v}
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    (Φ : X × Y → WithTop ℝ) (p : ℝ),
    (∀ u, marginal Φ u ≠ ⊥) → marginal Φ 0 = (p : EReal) →
    ∀ y : Y →L[ℝ] ℝ,
    ((perturbationDualObjective Φ y = (p : EReal) ∧
        perturbationDualValue Φ = (p : EReal)) ↔
      y ∈ subdifferential (marginalFunction Φ) 0) ∧
    (y ∈ subdifferential (marginalFunction Φ) 0 ↔
      ∀ u, ((p + y u : ℝ) : EReal) ≤ marginal Φ u)

/-- The complete algebraic part in the original setting. Dual attainment is
an equivalence for each functional, never an existence assumption. -/
def perturbation_duality_algebra : Prop :=
  ∀ {X : Type u} {Y : Type v}
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X] [LocallyConvexSpace ℝ X]
    [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [T2Space Y] [LocallyConvexSpace ℝ Y]
    (Φ : X × Y → WithTop ℝ), Proper Φ → IsConvex Φ →
    ExtendedProper (marginal Φ) → ∀ p : ℝ, marginal Φ 0 = (p : EReal) →
    (∀ y : Y →L[ℝ] ℝ,
      marginalConjugate Φ y = conjugate Φ (y.comp (ContinuousLinearMap.snd ℝ X Y))) ∧
    perturbationDualValue Φ = extendedBiconjugate (marginal Φ) 0 ∧
    extendedBiconjugate (marginal Φ) 0 ≤ (p : EReal) ∧
    (∀ y : Y →L[ℝ] ℝ,
      ((perturbationDualObjective Φ y = (p : EReal) ∧
          perturbationDualValue Φ = (p : EReal)) ↔
        y ∈ subdifferential (marginalFunction Φ) 0) ∧
      (y ∈ subdifferential (marginalFunction Φ) 0 ↔
        ∀ u, ((p + y u : ℝ) : EReal) ≤ marginal Φ u))

end VariationalNotes.Ch04.Specs
