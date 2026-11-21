import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.DirectionalQuotients
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.Subgradients

/-! The support and relative-interior clauses of Proposition
`prop:directional-support`, paper.tex 1108–1161. The last statement retains
all clauses of the proposition under their respective hypotheses. -/
noncomputable section
open Set Filter Topology
universe u
namespace VariationalNotes.ConvexAnalysis.Specs

/-- The characterization holds even without local continuity. -/
def subdifferential_eq_directional_le : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → WithTop ℝ), Proper f → IsConvex f → ∀ x : E, f x < ⊤ →
    subdifferential f x = {y | ∀ d : E, (y d : EReal) ≤ directionalDerivative f x d}

/-- A witness attains the maximum, with every other subgradient below it.
This includes the zero direction and entails nonemptiness. -/
def directionalDerivative_max : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → WithTop ℝ), Proper f → IsConvex f → ∀ x : E,
    (∃ V : Set E, V ∈ 𝓝 x ∧ (∀ y ∈ V, f y < ⊤) ∧
      ContinuousOn (fun y => (f y).untopD 0) V) →
    ∀ d : E, ∃ y ∈ subdifferential f x,
      directionalDerivative f x d = (y d : EReal) ∧
      ∀ z ∈ subdifferential f x, z d ≤ y d

def subdifferential_nonempty : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → WithTop ℝ), Proper f → IsConvex f → ∀ x : E,
    (∃ V : Set E, V ∈ 𝓝 x ∧ (∀ y ∈ V, f y < ⊤) ∧
      ContinuousOn (fun y => (f y).untopD 0) V) →
    (subdifferential f x).Nonempty

def subdifferential_nonempty_relativeInterior : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → WithTop ℝ), Proper f → IsConvex f →
    ∀ x : E, x ∈ ConvexGeometry.Specs.relativeInterior (effectiveDomain f) →
    (subdifferential f x).Nonempty

/-- Full proposition: the extended-real limit for every finite point;
continuous finite sublinearity under the neighborhood hypothesis; support,
attainment, and relative-interior existence under their own hypotheses. -/
def directional_support : Prop :=
  directionalQuotient_eq.{u} ∧ directionalQuotient_monotone.{u} ∧
  directionalQuotient_tendsto.{u} ∧ directionalDerivative_continuous_sublinear.{u} ∧
  subdifferential_eq_directional_le.{u} ∧ directionalDerivative_max.{u} ∧
  subdifferential_nonempty.{u} ∧ subdifferential_nonempty_relativeInterior.{u}

end VariationalNotes.ConvexAnalysis.Specs
