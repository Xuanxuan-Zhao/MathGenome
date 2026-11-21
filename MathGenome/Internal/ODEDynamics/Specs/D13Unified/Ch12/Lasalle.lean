import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Omega

/-! Independent statement of paper.tex, Theorem d13:12:lasalle.
The field is C¹ on its original open state domain. The Lyapunov function
need only be C¹ on an open neighborhood of the compact set. -/
noncomputable section
open Set Filter
open scoped Topology

namespace Specs.D13Unified.Ch12.Lasalle
open _root_.D13Unified _root_.D13Unified.Ch06.StateDerivative
open Ch01.AutonomousParameters Ch11.Invariant Ch11.OmegaTopology
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual directional derivative, with no sign or vanishing assumption built in. -/
def lieDerivative (F : AutonomousODE E) (V : E → ℝ) (x : E) : ℝ :=
  (fderiv ℝ V x) (autonomousEvalValue F x)

def zeroSet (F : AutonomousODE E) (K : Set E) (V : E → ℝ) : Set E :=
  {x | x ∈ K ∧ lieDerivative F V x = 0}

/-- Points whose entire complete maximal orbit is contained in Z. This is
exactly the union of complete orbits in Z, since time zero is on every orbit. -/
def completeCore (F : AutonomousODE E) (Z : Set E) : Set E :=
  {x | x ∈ Z ∧ (flowInterval F x).carrier = univ ∧ ∀ t : ℝ, flow F t x ∈ Z}

/-- Compactness, full invariance, largest-subset property, forward completeness,
omega-limit containment and attraction, including K = ∅. -/
def InvariancePrinciple : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ (K : Set E), IsCompact K → positiveInvariantValue F K →
    ∀ (V : E → ℝ) (U : Set E), IsOpen U → K ⊆ U → ContDiffOn ℝ 1 V U →
    (∀ x ∈ K, lieDerivative F V x ≤ 0) →
    let Z := zeroSet F K V
    let M := completeCore F Z
    M ⊆ Z ∧ IsCompact M ∧ invariantValue F M ∧
      (∀ S : Set E, S ⊆ Z → invariantValue F S → S ⊆ M) ∧
      (K.Nonempty → M.Nonempty) ∧
      (∀ x ∈ K, Ici 0 ⊆ (flowInterval F x).carrier ∧
        (∀ t : ℝ, 0 ≤ t → flow F t x ∈ K) ∧
        (omegaValue F x).Nonempty ∧ omegaValue F x ⊆ M ∧
        Tendsto (fun t : ℝ => Metric.infDist (flow F t x) M) atTop (𝓝 0))

/-- In the singleton case convergence is convergence to the stated equilibrium.
No nonemptiness of K is assumed. -/
def SingletonConvergence : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ (K : Set E), IsCompact K → positiveInvariantValue F K →
    ∀ (V : E → ℝ) (U : Set E), IsOpen U → K ⊆ U → ContDiffOn ℝ 1 V U →
    (∀ x ∈ K, lieDerivative F V x ≤ 0) →
    ∀ p ∈ F.domain, autonomousEvalValue F p = 0 →
      completeCore F (zeroSet F K V) = {p} →
      ∀ x ∈ K, Ici 0 ⊆ (flowInterval F x).carrier ∧
        Tendsto (fun t : ℝ => flow F t x) atTop (𝓝 p)

end Specs.D13Unified.Ch12.Lasalle
