import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.SphericalLimits

/-!
The finite holomorphic sequence clause of paper.tex:2437–2450, d12:11-06.
The hypotheses use the original weak holomorphy predicate and explicit chordal
convergence. The limit has no prescribed regularity. All conclusions concern
the original domain; values of the total representatives outside it are free.
-/

noncomputable section
open Set Filter

namespace Specs.D12Complex.Ch11.FiniteSphericalLimits
open _root_.D12Complex _root_.D12Complex.SphericalLimits

/-- A spherical limit of finite holomorphic functions on a domain is either
finite holomorphic everywhere, with ordinary convergence on every compact
subset, or is infinity everywhere. In particular, finite values and poles
cannot coexist in such a limit. -/
def finite_spherical_limit_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℕ → ℂ → ℂ) (F : ℂ → RiemannSphere),
    IsDomain Ω → (∀ n, HolomorphicOn Ω (f n)) →
    SphericalLocallyUniformOn (fun n z => sphereFinite (f n z)) F Ω →
    ((∀ z ∈ Ω, F z ≠ sphereInfty) ∧
      HolomorphicOn Ω (scalarFinitePart F) ∧
      (∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        TendstoUniformlyOn f (scalarFinitePart F) atTop K)) ∨
      EqOn F (fun _ => sphereInfty) Ω

end Specs.D12Complex.Ch11.FiniteSphericalLimits
