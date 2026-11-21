import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.Meromorphic
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.SphereHolomorphic

/-! Independent statements for paper.tex:1861–1894. The scalar meromorphic
predicates retain their actual pole values, relative closedness, discreteness,
finite pole orders, and exclusion of identically infinite components. -/
noncomputable section
open Set
namespace Specs.D12Complex.Ch07.ScalarSphereBridge
open _root_.D12Complex

def plane_scalar_sphere_bridge_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere), IsDomain Ω →
    (PlaneSphereHolomorphicOn Ω F ↔
      ScalarMeromorphicOn Ω F ∨ EqOn F (fun _ => sphereInfty) Ω)

def sphere_scalar_sphere_bridge_type : Prop :=
  ∀ (U : Set RiemannSphere) (F : RiemannSphere → RiemannSphere),
    IsOpen U → IsConnected U →
    (SphereHolomorphicOn U F ↔
      ScalarMeromorphicOnSphere U F ∨ EqOn F (fun _ => sphereInfty) U)

/-- Explicitly expose the pole conclusions in the nonconstant-infinity case. -/
def plane_infinite_values_are_poles_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere), IsDomain Ω →
    PlaneSphereHolomorphicOn Ω F → ¬ EqOn F (fun _ => sphereInfty) Ω →
    IsClosed {z : Ω | F z = sphereInfty} ∧ IsDiscrete (scalarPoleSet Ω F) ∧
      ∀ a ∈ Ω, F a = sphereInfty → PoleAt (scalarFinitePart F) a

def sphere_infinite_values_are_poles_type : Prop :=
  ∀ (U : Set RiemannSphere) (F : RiemannSphere → RiemannSphere),
    IsOpen U → IsConnected U → SphereHolomorphicOn U F →
    ¬ EqOn F (fun _ => sphereInfty) U →
    IsClosed {p : U | F p = sphereInfty} ∧
    IsDiscrete {p | p ∈ U ∧ F p = sphereInfty} ∧
    ∀ (c : SphereCoordinate) (p : RiemannSphere), p ∈ U →
      p ∈ (sphereCoordinate c).source → F p = sphereInfty →
      PoleAt (scalarFinitePart (F ∘ (sphereCoordinate c).symm)) (sphereCoordinate c p)

/-- The original finite-valued assertion, expressed with a scalar function. -/
def finite_valued_sphere_holomorphic_constant_type : Prop :=
  ∀ f : RiemannSphere → ℂ,
    SphereHolomorphicOn univ (sphereFinite ∘ f) → ∃ c : ℂ, ∀ p, f p = c

/-- Equivalent formulation for sphere-valued maps with no infinite values. -/
def sphere_holomorphic_omitting_infty_constant_type : Prop :=
  ∀ F : RiemannSphere → RiemannSphere,
    SphereHolomorphicOn univ F → (∀ p, F p ≠ sphereInfty) →
      ∃ c : ℂ, ∀ p, F p = sphereFinite c

end Specs.D12Complex.Ch07.ScalarSphereBridge
