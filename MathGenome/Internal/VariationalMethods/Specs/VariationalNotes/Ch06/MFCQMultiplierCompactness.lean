import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch06.LICQMultiplierUniqueness
import Mathlib.Topology.Compactness.Compact

/-! Independent statements for `prop:qualified-multiplier-sets`, paper.tex
§6.5. The coefficient of the objective is one, as in the shared KKT system.
The coefficient spaces have their usual finite product topology, equivalently
their finite-dimensional Euclidean topology. Either index family may be empty. -/
noncomputable section
universe u v w
namespace VariationalNotes.Ch06.MFCQMultiplierCompactnessSpecs
open Specs

def kktMultiplierSet {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X) :
    Set ((I → ℝ) × (J → ℝ)) :=
  {p | KKT U f g h x p.1 p.2}

def kktMultiplierSetType :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (_U : Set X) (_f : X → ℝ) (_g : I → X → ℝ) (_h : J → X → ℝ) (_x : X),
    Set ((I → ℝ) × (J → ℝ))

/-- Compactness is algebraic and does not require a minimum or regularity. -/
def kktMultiplierSet_isCompact_of_mfcq : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X),
    MFCQ U g h x → IsCompact (kktMultiplierSet U f g h x)

def kktMultiplierSet_nonempty_isCompact_of_mfcq : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X),
    SmoothConstraintData U f g h → IsLocalMinOn f (feasibleSet U g h) x →
    MFCQ U g h x →
    (kktMultiplierSet U f g h x).Nonempty ∧ IsCompact (kktMultiplierSet U f g h x)

/-- The complete proposition, with separate qualifications for its two clauses. -/
def qualified_multiplier_sets : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X),
    SmoothConstraintData U f g h → IsLocalMinOn f (feasibleSet U g h) x →
    (LICQ U g h x → ∃! p, p ∈ kktMultiplierSet U f g h x) ∧
    (MFCQ U g h x →
      (kktMultiplierSet U f g h x).Nonempty ∧ IsCompact (kktMultiplierSet U f g h x))

end VariationalNotes.Ch06.MFCQMultiplierCompactnessSpecs
