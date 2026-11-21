import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.ChordalMetric
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.ScalarSphereBridge
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

noncomputable section
open Set Filter Metric
open scoped Topology

namespace D12Complex.SphericalLimits

/-- Uniform convergence in the explicit chordal distance on every compact subset.
No arbitrary metric instance on the one-point compactification is used. -/
def SphericalLocallyUniformOn (f : ℕ → ℂ → RiemannSphere)
    (F : ℂ → RiemannSphere) (Ω : Set ℂ) : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n in atTop, ∀ z ∈ K, Chordal.chordal (F z) (f n z) < ε

end D12Complex.SphericalLimits

namespace Specs.D12Complex.Ch11.SphericalLimits
open _root_.D12Complex _root_.D12Complex.SphericalLimits

def SphericalLocallyUniformOn_type :=
  (ℕ → ℂ → RiemannSphere) → (ℂ → RiemannSphere) → Set ℂ → Prop

def SphericalLocallyUniformOn_value : SphericalLocallyUniformOn_type := fun f F Ω =>
  ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n in atTop, ∀ z ∈ K, Chordal.chordal (F z) (f n z) < ε

/-- Any compact source set whose limiting image avoids the chart pole has
uniformly bounded chart expressions eventually, and ordinary uniform convergence.
This includes every small closed neighborhood used in the local proof. -/
def chart_compact_convergence_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℕ → ℂ → RiemannSphere) (F : ℂ → RiemannSphere),
    IsOpen Ω → (∀ n, PlaneSphereHolomorphicOn Ω (f n)) →
    SphericalLocallyUniformOn f F Ω →
    ∀ (c : SphereCoordinate) (K : Set ℂ), IsCompact K → K ⊆ Ω →
      MapsTo F K (sphereCoordinate c).source →
      (∃ M : ℝ, 0 < M ∧ (∀ z ∈ K, ‖sphereCoordinate c (F z)‖ ≤ M) ∧
        ∀ᶠ n in atTop, ∀ z ∈ K,
          f n z ∈ (sphereCoordinate c).source ∧ ‖sphereCoordinate c (f n z)‖ ≤ M) ∧
      TendstoUniformlyOn (fun n z => sphereCoordinate c (f n z))
        (fun z => sphereCoordinate c (F z)) atTop K

/-- At each point, every available canonical target chart works on a small
closed disk. The approximants are eventually holomorphic in that chart on its
interior, uniformly bounded on the closed disk, and converge ordinarily there. -/
def chart_neighborhood_convergence_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℕ → ℂ → RiemannSphere) (F : ℂ → RiemannSphere),
    IsOpen Ω → (∀ n, PlaneSphereHolomorphicOn Ω (f n)) →
    SphericalLocallyUniformOn f F Ω →
    ∀ (a : ℂ), a ∈ Ω → ∀ c : SphereCoordinate,
      F a ∈ (sphereCoordinate c).source →
      ∃ r : ℝ, 0 < r ∧ closedBall a r ⊆ Ω ∧
        MapsTo F (closedBall a r) (sphereCoordinate c).source ∧
        (∃ M : ℝ, 0 < M ∧ (∀ z ∈ closedBall a r, ‖sphereCoordinate c (F z)‖ ≤ M) ∧
          ∀ᶠ n in atTop,
            HolomorphicOn (ball a r) (fun z => sphereCoordinate c (f n z)) ∧
            ∀ z ∈ closedBall a r,
              f n z ∈ (sphereCoordinate c).source ∧ ‖sphereCoordinate c (f n z)‖ ≤ M) ∧
        TendstoUniformlyOn (fun n z => sphereCoordinate c (f n z))
          (fun z => sphereCoordinate c (F z)) atTop (closedBall a r)

/-- The limit is holomorphic as an actual map into the sphere, with continuity
and holomorphic germs in the canonical coordinates. -/
def sphere_holomorphic_limit_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℕ → ℂ → RiemannSphere) (F : ℂ → RiemannSphere),
    IsOpen Ω → (∀ n, PlaneSphereHolomorphicOn Ω (f n)) →
    SphericalLocallyUniformOn f F Ω → PlaneSphereHolomorphicOn Ω F

/-- The original scalar conclusion on a domain, with all pole conditions of
the canonical scalar predicate and the constant infinity alternative. -/
def scalar_meromorphic_limit_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℕ → ℂ → RiemannSphere) (F : ℂ → RiemannSphere),
    IsDomain Ω → (∀ n, ScalarMeromorphicOn Ω (f n)) →
    SphericalLocallyUniformOn f F Ω →
      PlaneSphereHolomorphicOn Ω F ∧
        (ScalarMeromorphicOn Ω F ∨ EqOn F (fun _ => sphereInfty) Ω)

end Specs.D12Complex.Ch11.SphericalLimits
