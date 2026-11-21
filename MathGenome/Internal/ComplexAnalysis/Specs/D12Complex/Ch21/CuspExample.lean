import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.Surfaces
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Analytic.Order
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Independent contracts for the singular cusp in paper.tex, d12:21-07.
The ambient space is the usual complex vector space ℂ × ℂ with its product
 topology. Embeddedness uses the usual parametric characterization: a chart
of the inherited subset topology whose inverse, followed by inclusion in the
ambient space, is holomorphic and has nonzero differential at the point.
For a one-dimensional complex source this is exactly a nonzero derivative.
No complex structure on the singular subset is postulated. -/
noncomputable section
open Filter
open scoped Topology

namespace Specs.D12Complex.Ch21.CuspExample

/-- The inherited affine subset, not an abstract normalization. -/
def affineCusp_type := Set (ℂ × ℂ)
def affineCusp_value : Set (ℂ × ℂ) := {p | p.2 ^ 2 = p.1 ^ 3}

def parametrization_type := ℂ → ℂ × ℂ
def parametrization_value : parametrization_type := fun t => (t ^ 2, t ^ 3)

def inverseParameter_type := (ℂ × ℂ) → ℂ
def inverseParameter_value : inverseParameter_type := fun p =>
  if p.1 = 0 then 0 else p.2 / p.1

/-- A regular local holomorphic parametrization of a relative neighborhood.
The open partial homeomorphism specifies the actual inherited topology;
its source contains the point and its target is open in ℂ. -/
def IsEmbeddedComplexCurveAt_type := Set (ℂ × ℂ) → (ℂ × ℂ) → Prop
def IsEmbeddedComplexCurveAt_value : IsEmbeddedComplexCurveAt_type := fun s p =>
  ∃ (q : s) (e : OpenPartialHomeomorph s ℂ),
    (q : ℂ × ℂ) = p ∧ q ∈ e.source ∧
    DifferentiableOn ℂ (fun t => (e.symm t : ℂ × ℂ)) e.target ∧
    deriv (fun t => (e.symm t : ℂ × ℂ)) (e q) ≠ 0

def parameter_surface_type : Prop :=
  ∃ S : _root_.D12Complex.Surfaces.RiemannSurface ℂ,
    S.atlas = {e | e.val = OpenPartialHomeomorph.refl ℂ}

def parametrization_polynomial_type : Prop :=
  ∃ P Q : Polynomial ℂ, ∀ t : ℂ,
    parametrization_value t = (P.eval t, Q.eval t)

def parametrization_holomorphic_type : Prop :=
  Differentiable ℂ parametrization_value

def parametrization_bijOn_type : Prop :=
  Set.BijOn parametrization_value Set.univ affineCusp_value

def inverse_left_type : Prop :=
  Function.LeftInverse inverseParameter_value parametrization_value

def inverse_right_type : Prop :=
  ∀ p ∈ affineCusp_value, parametrization_value (inverseParameter_value p) = p

def inverse_at_origin_type : Prop := inverseParameter_value (0, 0) = 0

def inverse_off_origin_type : Prop :=
  ∀ p ∈ affineCusp_value, p ≠ (0, 0) →
    inverseParameter_value p = p.2 / p.1

/-- The valuation identity, including zero germs via extended orders. -/
def cusp_orders_type : Prop :=
  ∀ (U : Set ℂ) (x y : ℂ → ℂ) (a : ℂ), a ∈ U →
    _root_.D12Complex.HolomorphicOn U x → _root_.D12Complex.HolomorphicOn U y →
    (∀ t ∈ U, (x t, y t) ∈ affineCusp_value) →
    2 • analyticOrderAt y a = 3 • analyticOrderAt x a

/-- All local holomorphic curves through the cusp origin have zero differential;
this includes constant curves and requires no injectivity assumption. -/
def cusp_curve_deriv_zero_type : Prop :=
  ∀ (U : Set ℂ) (x y : ℂ → ℂ) (a : ℂ), a ∈ U →
    _root_.D12Complex.HolomorphicOn U x → _root_.D12Complex.HolomorphicOn U y →
    x a = 0 → y a = 0 → (∀ t ∈ U, (x t, y t) ∈ affineCusp_value) →
    deriv x a = 0 ∧ deriv y a = 0

def not_embedded_at_origin_type : Prop :=
  ¬ IsEmbeddedComplexCurveAt_value affineCusp_value (0, 0)

end Specs.D12Complex.Ch21.CuspExample
