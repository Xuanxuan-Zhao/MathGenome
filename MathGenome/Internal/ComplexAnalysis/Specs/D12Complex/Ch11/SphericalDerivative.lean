import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.ChordalMetric
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.ScalarSphereBridge
import Mathlib.Analysis.Calculus.Deriv.Basic

noncomputable section
open scoped Topology
namespace D12Complex.SphericalDerivative
open D12Complex.Chordal

/-- The finite-coordinate spherical derivative. -/
def scalarDensity (f : ℂ → ℂ) (a : ℂ) : ℝ :=
  ‖deriv f a‖ / (1 + ‖f a‖ ^ 2)

/-- Use the reciprocal coordinate at infinity, with its actual holomorphic
extension value zero. This also assigns zero to constant infinity. -/
def sphericalDeriv (F : ℂ → RiemannSphere) (a : ℂ) : ℝ := by
  classical
  exact if F a = sphereInfty then scalarDensity (fun z => infinityCoordinate (F z)) a
  else scalarDensity (fun z => finiteCoordinate (F z)) a

end D12Complex.SphericalDerivative
namespace Specs.D12Complex.Ch11.SphericalDerivative
open _root_.D12Complex _root_.D12Complex.Chordal _root_.D12Complex.SphericalDerivative

def scalarDensity_type := (ℂ → ℂ) → ℂ → ℝ
def scalarDensity_value : scalarDensity_type := fun f a => ‖deriv f a‖ / (1 + ‖f a‖ ^ 2)
def sphericalDeriv_type := (ℂ → RiemannSphere) → ℂ → ℝ
def sphericalDeriv_value : sphericalDeriv_type := by
  classical
  exact fun F a => if F a = sphereInfty then scalarDensity (fun z => infinityCoordinate (F z)) a
  else scalarDensity (fun z => finiteCoordinate (F z)) a

def scalarDensity_inv_type : Prop := ∀ (f : ℂ → ℂ) (a : ℂ),
  DifferentiableAt ℂ f a → f a ≠ 0 →
  scalarDensity (fun z => (f z)⁻¹) a = scalarDensity f a

def sphericalDeriv_finite_type : Prop := ∀ (F : ℂ → RiemannSphere) (a : ℂ),
  F a ≠ sphereInfty →
  sphericalDeriv F a = scalarDensity (fun z => finiteCoordinate (F z)) a

def sphericalDeriv_reciprocal_chart_type : Prop :=
  ∀ (F : ℂ → RiemannSphere) (a : ℂ), PlaneSphereHolomorphicAt F a →
  F a ≠ sphereFinite 0 →
  sphericalDeriv F a = scalarDensity (fun z => infinityCoordinate (F z)) a

def sphericalDeriv_scalar_type : Prop := ∀ (f : ℂ → ℂ) (a : ℂ),
  sphericalDeriv (sphereFinite ∘ f) a = scalarDensity f a

def sphericalDeriv_pole_type : Prop := ∀ (F : ℂ → RiemannSphere) (a : ℂ),
  F a = sphereInfty →
  sphericalDeriv F a = ‖deriv (fun z => infinityCoordinate (F z)) a‖

/-- Both allowed coordinates give the same value wherever they apply. -/
def sphericalDeriv_in_chart_type : Prop :=
  ∀ (F : ℂ → RiemannSphere) (a : ℂ) (d : SphereCoordinate),
  PlaneSphereHolomorphicAt F a → F a ∈ (sphereCoordinate d).source →
  sphericalDeriv F a = scalarDensity (fun z => sphereCoordinate d (F z)) a

def sphericalDeriv_nonneg_type : Prop := ∀ (F : ℂ → RiemannSphere) (a : ℂ),
  0 ≤ sphericalDeriv F a

def sphericalDeriv_const_type : Prop := ∀ (p : RiemannSphere) (a : ℂ),
  sphericalDeriv (fun _ => p) a = 0

def sphericalDeriv_continuousOn_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere), PlaneSphereHolomorphicOn Ω F →
  ContinuousOn (sphericalDeriv F) Ω

/-- Explicit specialization to scalar meromorphic functions with their pole values. -/
def scalarMeromorphic_sphericalDeriv_continuousOn_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere), ScalarMeromorphicOn Ω F →
  ContinuousOn (sphericalDeriv F) Ω

def sphericalDeriv_chartRotation_type : Prop :=
  ∀ (F : ℂ → RiemannSphere) (a b : ℂ), PlaneSphereHolomorphicAt F b →
  sphericalDeriv (chartRotation a ∘ F) b = sphericalDeriv F b

def sphericalDeriv_reciprocal_type : Prop :=
  ∀ (F : ℂ → RiemannSphere) (b : ℂ), PlaneSphereHolomorphicAt F b →
  sphericalDeriv (reciprocal ∘ F) b = sphericalDeriv F b

/-- A differential statement of the line element, for every tangent vector
in the finite coordinate; the norm is the actual Euclidean L² norm. -/
def stereographic_line_element_type : Prop := ∀ (w v : ℂ),
  ∃ V : Euclidean3,
    HasDerivAt (fun t : ℝ => stereographic (sphereFinite (w + t • v))) V 0 ∧
    ‖V‖ = 2 * ‖v‖ / (1 + ‖w‖ ^ 2)

/-- Same line element in the reciprocal coordinate, including w=0 (the pole). -/
def reciprocal_line_element_type : Prop := ∀ (w v : ℂ),
  ∃ V : Euclidean3,
    HasDerivAt (fun t : ℝ => stereographic (infinityParametrization (w + t • v))) V 0 ∧
    ‖V‖ = 2 * ‖v‖ / (1 + ‖w‖ ^ 2)

end Specs.D12Complex.Ch11.SphericalDerivative
