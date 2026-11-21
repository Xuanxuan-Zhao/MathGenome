import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.PeriodCriterion
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! Independent statements of M10.07 (paper.tex:2062–2109).
The integral, piecewise smoothness, intrinsic covectors and exterior derivative
are the shared upstream objects. A homotopy is only continuous. Parameters of
both paths can be arbitrary increasing intervals, including singletons.
-/
set_option autoImplicit false
noncomputable section

namespace SmoothManifolds.ClosedOneFormPeriodData
open ModelData AtlasData CovectorData PathIntegrationData
universe u

/-- Continuous fixed-endpoint homotopy after affine identification of the two
parameter intervals with the unit interval. No smoothness of H is required. -/
def EndpointHomotopic {M : Type u} [TopologicalSpace M]
    (γ η : ℝ → M) (a b c d : ℝ) : Prop :=
  ∃ H : unitInterval × unitInterval → M, Continuous H ∧
    (∀ s, H (0, s) = γ (a + (b-a) * s.val)) ∧
    (∀ s, H (1, s) = η (c + (d-c) * s.val)) ∧
    (∀ t, H (t, 0) = γ a) ∧
    (∀ t, H (t, 1) = γ b)

/-- A property of the actual path integral, kept distinct from closedness. -/
def HomotopyInvariant {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M) (α : CovectorField S) : Prop :=
  ∀ (γ η : ℝ → M) (a b c d : ℝ),
    PiecewiseSmoothOn S γ a b → PiecewiseSmoothOn S η c d →
    EndpointHomotopic γ η a b c d →
    pathIntegral S α γ a b = pathIntegral S α η c d

end SmoothManifolds.ClosedOneFormPeriodData

namespace Specs.SmoothManifolds.Integration.ClosedOneFormPeriods
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.CovectorData
  _root_.SmoothManifolds.BundleOperationsData _root_.SmoothManifolds.PathIntegrationData
  _root_.SmoothManifolds.PeriodData _root_.SmoothManifolds.ExteriorDerivativeData
  _root_.SmoothManifolds.ClosedOneFormPeriodData
universe u

def EndpointHomotopicType :=
  {M : Type u} → [TopologicalSpace M] →
    (ℝ → M) → (ℝ → M) → ℝ → ℝ → ℝ → ℝ → Prop

def EndpointHomotopicValue : EndpointHomotopicType :=
  @EndpointHomotopic

def HomotopyInvariantType :=
  {n : ℕ} → {k : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    (S : SmoothManifold n k M) → CovectorField S → Prop

def HomotopyInvariantValue : HomotopyInvariantType :=
  @HomotopyInvariant

def exact_homotopy_invarianceType : Prop :=
  ∀ {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M) (α : CovectorField S),
    Exact S α → HomotopyInvariant S α

def homotopy_invarianceType : Prop :=
  ∀ {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M) (C : CotangentBundle S) (α : OneForm C),
    HasExteriorDerivative C (oneField S α.field) 0 → HomotopyInvariant S α.field

def simply_connected_exactType : Prop :=
  ∀ {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M) (C : CotangentBundle S) (α : OneForm C),
    SimplyConnectedSpace M → HasExteriorDerivative C (oneField S α.field) 0 →
    Exact S α.field

/-- The componentwise statement includes the empty manifold and does not choose
a common basepoint or impose connectedness on M. -/
def componentwise_simply_connected_exactType : Prop :=
  ∀ {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M) (C : CotangentBundle S) (α : OneForm C),
    (∀ p : M, SimplyConnectedSpace (connectedComponent p)) →
    HasExteriorDerivative C (oneField S α.field) 0 → Exact S α.field

/-- Assembly lemma: this does not assert that an arbitrary smooth form has
homotopy invariant integral. That assertion for closed forms is the main target. -/
def exact_of_homotopy_invariantType : Prop :=
  ∀ {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M) (C : CotangentBundle S) (α : OneForm C),
    (∀ (p : M) (γ : Path p p), Path.Homotopic γ (Path.refl p)) →
    HomotopyInvariant S α.field → Exact S α.field

end Specs.SmoothManifolds.Integration.ClosedOneFormPeriods
