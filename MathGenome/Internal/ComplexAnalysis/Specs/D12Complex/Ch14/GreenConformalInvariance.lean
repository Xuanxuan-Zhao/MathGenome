import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.GreenRegularBoundary

/-! The conformal invariance assertion and complete simultaneous Green-function
statement of paper.tex:2681–2691, d12:14-07.  Neither conformal invariance nor
canonical existence assumes boundary regularity or a boundary extension of the
biholomorphism.  Total representatives are constrained only away from their
poles; continuous zero boundary values use the designated zero extension. -/
noncomputable section
open Set Filter
open scoped Topology

namespace Specs.D12Complex.Ch14.GreenConformalInvariance
open _root_.D12Complex

/-- Pulling back the canonical Green function by any biholomorphism of bounded
domains preserves it.  The arguments are ordered as pole, then variable. -/
def canonical_green_conformal_type : Prop :=
  ∀ (Ω V : Set ℂ) (F : ℂ → ℂ),
    IsDomain Ω → Bornology.IsBounded Ω → IsDomain V → Bornology.IsBounded V →
    IsBiholomorphism Ω V F → ∀ a ∈ Ω, ∀ z ∈ Ω \ {a},
      CanonicalGreen.canonicalGreen_value V (F a) (F z) =
        CanonicalGreen.canonicalGreen_value Ω a z

/-- The full d12:14-07 package, retaining the canonical witness, leastness,
symmetry, conformal invariance, every regular-point limit, and the complete
regular-domain characterization and Dirichlet formula.  Competing continuous
zero-boundary Green functions require no positivity hypothesis. -/
def green_function_package_type : Prop :=
  ∀ Ω : Set ℂ, IsDomain Ω → Bornology.IsBounded Ω →
    (∀ a ∈ Ω, IsLeastPositiveGreen Ω a (CanonicalGreen.canonicalGreen_value Ω a)) ∧
    (∀ a ∈ Ω, ∀ b ∈ Ω, a ≠ b →
      CanonicalGreen.canonicalGreen_value Ω a b =
        CanonicalGreen.canonicalGreen_value Ω b a) ∧
    (∀ (V : Set ℂ) (F : ℂ → ℂ), IsDomain V → Bornology.IsBounded V →
      IsBiholomorphism Ω V F → ∀ a ∈ Ω, ∀ z ∈ Ω \ {a},
        CanonicalGreen.canonicalGreen_value V (F a) (F z) =
          CanonicalGreen.canonicalGreen_value Ω a z) ∧
    (∀ a ∈ Ω, ∀ ξ : ℂ, BarrierSqueeze.RegularBoundaryPoint_value Ω ξ →
      Tendsto (CanonicalGreen.canonicalGreen_value Ω a) (𝓝[Ω] ξ) (𝓝 0)) ∧
    ((∀ ξ ∈ frontier Ω, BarrierSqueeze.RegularBoundaryPoint_value Ω ξ) →
      ∀ a ∈ Ω,
        IsZeroBoundaryGreen Ω a
          (GreenRegularBoundary.canonicalGreenZeroExtension_value Ω a) ∧
        EqOn (GreenRegularBoundary.canonicalGreenZeroExtension_value Ω a)
          (RegularGreen.regularGreen_value Ω a) (closure Ω \ {a}) ∧
        (∀ g : ℂ → ℝ, IsZeroBoundaryGreen Ω a g →
          EqOn g (GreenRegularBoundary.canonicalGreenZeroExtension_value Ω a)
            (closure Ω \ {a})) ∧
        RegularDirichlet.IsDirichletSolution_value Ω (fun ξ => Real.log ‖ξ - a‖)
          (RegularDirichlet.perronSolution_value Ω (fun ξ => Real.log ‖ξ - a‖)) ∧
        EqOn (CanonicalGreen.canonicalGreen_value Ω a)
          (fun z => RegularDirichlet.perronSolution_value Ω
            (fun ξ => Real.log ‖ξ - a‖) z - Real.log ‖z - a‖) (Ω \ {a}))

end Specs.D12Complex.Ch14.GreenConformalInvariance
