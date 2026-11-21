import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.LocalQuotientsArithmetic
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.Residue

/-! Independent statements for paper.tex:2264–2272, d12:09-01.
The coefficient uses the ordinary finite representative away from the divisor;
the sphere-valued function restores all removable values and pole values.
The finite signed-order assumption is local and already excludes a zero germ.
-/
noncomputable section
open Set Filter
open scoped Topology

namespace Specs.D12Complex.Ch09.LogarithmicDerivative.Objects
open _root_.D12Complex

def coefficient (F : ℂ → RiemannSphere) : ℂ → ℂ := logDeriv (scalarFinitePart F)

def filled (F : ℂ → RiemannSphere) : ℂ → RiemannSphere :=
  Ch07.LocalQuotientsArithmetic.Objects.fill (coefficient F)

end Specs.D12Complex.Ch09.LogarithmicDerivative.Objects

namespace Specs.D12Complex.Ch09.LogarithmicDerivative
open _root_.D12Complex Objects

def coefficient_type := (ℂ → RiemannSphere) → ℂ → ℂ
def coefficient_value : coefficient_type := fun F => logDeriv (scalarFinitePart F)
def filled_type := (ℂ → RiemannSphere) → ℂ → RiemannSphere
def filled_value : filled_type := fun F =>
  Ch07.LocalQuotientsArithmetic.Objects.fill (coefficient F)

def local_expansion_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere), ScalarMeromorphicOn Ω F →
  ∀ a ∈ Ω, ∀ m : ℤ, scalarSignedOrder F a = some m →
  ∃ r : ℝ, 0 < r ∧ Metric.ball a r ⊆ Ω ∧ ∃ h : ℂ → ℂ,
    HolomorphicOn (Metric.ball a r) h ∧
    ∀ z ∈ puncturedDisk a r, coefficient F z = (m : ℂ) / (z - a) + h z

def residue_eq_order_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere), ScalarMeromorphicOn Ω F →
  ∀ a ∈ Ω, ∀ m : ℤ, scalarSignedOrder F a = some m →
    Residue.residue (coefficient F) a = (m : ℂ) ∧
    Residue.differentialResidue (Residue.differential (coefficient F)) a = (m : ℂ)

def filled_meromorphic_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere), ScalarMeromorphicOn Ω F →
    ScalarMeromorphicOn Ω (filled F)

def local_pole_classification_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere), ScalarMeromorphicOn Ω F →
  ∀ a ∈ Ω, ∀ m : ℤ, scalarSignedOrder F a = some m →
    (filled F a = sphereInfty ↔ m ≠ 0) ∧
    (m ≠ 0 → PoleOfOrderAt (coefficient F) a 1) ∧
    (m = 0 → RemovableSingularityAt (coefficient F) a)

/-- Pointwise component hypothesis: zero components elsewhere are allowed. -/
def filled_poles_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere), ScalarMeromorphicOn Ω F →
  ∀ a ∈ Ω,
    ¬ EqOn F (fun _ => sphereFinite 0) (connectedComponentIn Ω a) →
    (filled F a = sphereInfty ↔ F a = sphereFinite 0 ∨ F a = sphereInfty) ∧
    (filled F a = sphereInfty → PoleOfOrderAt (scalarFinitePart (filled F)) a 1)

end Specs.D12Complex.Ch09.LogarithmicDerivative
