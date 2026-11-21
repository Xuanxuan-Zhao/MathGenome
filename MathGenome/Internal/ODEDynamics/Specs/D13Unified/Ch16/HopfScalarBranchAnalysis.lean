import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.HopfReturnExpansion

/-!
Independent scalar part of paper.tex:3697–3720. All spectral functions,
coefficients, and return errors are the canonical upstream objects.
No periodic orbit or section correspondence is a premise.
-/
noncomputable section
namespace Specs.D13Unified.Ch16.HopfScalarBranchAnalysis
open Set Filter
open CubicHomologicalElimination CubicNormalForm HopfReturnExpansion

/-- Original hypotheses, with the two Hopf nondegeneracy conditions. -/
structure SourceHypotheses (F : ℝ × ℂ → ℂ) (ω : ℝ) : Prop where
  regularity : ContDiffAt ℝ 5 F (0, 0)
  frequency_pos : 0 < ω
  eigenvalue : Module.End.HasEigenvalue
    (complexifiedLinearization F 0).toLin' (CubicHomologicalElimination.eigenvalue 0 ω)
  equilibrium : ∀ᶠ μ in nhds (0 : ℝ), F (μ, 0) = 0
  crossing : deriv (spectralReal F) 0 ≠ 0
  cubic : firstLyapunovCoefficient F ≠ 0

/-- Exactly the analytic portion of ReturnExpansion, for arbitrary supplied
P and Q. Positivity of the three scales is kept outside this predicate.
The coefficient identity is an upstream conclusion, not a branch certificate. -/
structure ReturnData (F : ℝ × ℂ → ℂ) (ω ε δ C : ℝ)
    (P Q : ℝ × ℝ → ℝ) : Prop where
  coefficient_zero : cubicReturnCoefficient F 0 = turnAngle * firstLyapunovCoefficient F / ω
  return_regular : ContDiffOn ℝ 2 P (returnBox δ ε)
  quotient_regular : ContDiffOn ℝ 2 Q (returnBox δ ε)
  error_regular : ContDiffOn ℝ 1 (returnError F P) (returnBox δ ε)
  at_zero : ∀ μ, |μ| < ε →
    P (0, μ) = 0 ∧ Q (0, μ) = linearReturnFactor F μ - 1
  bounds : ∀ q ∈ returnBox δ ε,
    P q = q.1 * (1 + Q q) ∧
    |returnError F P q| ≤ C * |q.1| ^ 4 ∧
    |deriv (fun r => returnError F P (r, q.2)) q.1| ≤ C * |q.1| ^ 3 ∧
    |deriv (fun μ => returnError F P (q.1, μ)) q.2| ≤ C * |q.1| ^ 4

/-- The leading coefficient in μ as a function of signed section radius. -/
def branchCoefficient (F : ℝ × ℂ → ℂ) : ℝ :=
  -firstLyapunovCoefficient F / deriv (spectralReal F) 0

/-- The analytic graph and both uniform estimates on one signed interval. -/
structure LocalBranch (F : ℝ × ℂ → ℂ) (P Q : ℝ × ℝ → ℝ)
    (d ε₀ : ℝ) (ψ : ℝ → ℝ) : Prop where
  regular : ContDiffOn ℝ 2 ψ (Ioo (-d) d)
  zero : ψ 0 = 0
  flat : deriv ψ 0 = 0
  parameter_bound : ∀ r, |r| < d → |ψ r| < ε₀
  quotient_zeros : ∀ r μ, |r| < d → |μ| < ε₀ → (Q (r, μ) = 0 ↔ μ = ψ r)
  fixed_points : ∀ r μ, 0 < r → r < d → |μ| < ε₀ → (P (r, μ) = r ↔ μ = ψ r)
  estimates : ∃ M > 0, ∀ r, |r| < d →
    |ψ r - branchCoefficient F * r ^ 2| ≤ M * |r| ^ 3 ∧
    |deriv ψ r - 2 * branchCoefficient F * r| ≤ M * r ^ 2
  slope : ∀ r ∈ Ioo 0 d, 0 < branchCoefficient F * deriv ψ r
  monotone : StrictMonoOn (fun r => branchCoefficient F * ψ r) (Ioo 0 d)

/-- A complete local scalar branch. ε₀ is the zero-graph parameter box;
ε₁ is smaller so that the entire relevant side is covered by positive radii.
The last two clauses quantify over all local fixed points, without choosing
an inverse branch or presupposing the required smallness of its radius. -/
def BranchDescription (F : ℝ × ℂ → ℂ) (P Q : ℝ × ℝ → ℝ)
    (d ε₀ ε₁ : ℝ) (ψ : ℝ → ℝ) : Prop :=
  LocalBranch F P Q d ε₀ ψ ∧
  (∀ μ, |μ| < ε₁ →
    ((∃! r, 0 < r ∧ r < d ∧ P (r, μ) = r) ↔
      spectralReal F μ * firstLyapunovCoefficient F < 0) ∧
    ((¬ spectralReal F μ * firstLyapunovCoefficient F < 0) →
      ∀ r, 0 < r → r < d → P (r, μ) ≠ r)) ∧
  (∀ ζ > 0, ∃ ν > 0, ν ≤ ε₁ ∧
    ∀ μ r, |μ| < ν → 0 < r → r < d → P (r, μ) = r →
      |r ^ 2 + deriv (spectralReal F) 0 / firstLyapunovCoefficient F * μ| ≤ ζ * |μ|) ∧
  (∀ τ, 0 < τ → τ < d → ∃ ν > 0, ν ≤ ε₁ ∧
    ∀ μ r, |μ| < ν → 0 < r → r < d → P (r, μ) = r → r < τ)

/-- Full assigned obligation, allowing any positive prescribed radius cutoff. -/
def ScalarBranchAnalysis : Prop :=
  ∀ F ω, SourceHypotheses F ω →
    ∀ ε δ C P Q, 0 < ε → 0 < δ → 0 < C → ReturnData F ω ε δ C P Q →
    ∀ cutoff, 0 < cutoff → cutoff ≤ δ →
      ∃ d > 0, ∃ ε₀ > 0, ∃ ε₁ > 0, ∃ ψ : ℝ → ℝ,
        d ≤ cutoff ∧ ε₀ ≤ ε ∧ ε₁ ≤ ε₀ ∧ BranchDescription F P Q d ε₀ ε₁ ψ

/-- Quantitative analytic portion, on an arbitrarily prescribed radius cutoff. -/
def LocalBranchAnalysis : Prop :=
  ∀ F ω, SourceHypotheses F ω →
    ∀ ε δ C P Q, 0 < ε → 0 < δ → 0 < C → ReturnData F ω ε δ C P Q →
    ∀ cutoff, 0 < cutoff → cutoff ≤ δ →
      ∃ d > 0, ∃ ε₀ > 0, ∃ ψ : ℝ → ℝ,
        d ≤ cutoff ∧ ε₀ ≤ ε ∧ LocalBranch F P Q d ε₀ ψ

/-- Standalone IFT layer, retaining the zero graph and flat first jet.
This is a proper subset of the full obligation, not a replacement for it. -/
def FlatImplicitGraph : Prop :=
  ∀ F ω, SourceHypotheses F ω →
    ∀ ε δ C P Q, 0 < ε → 0 < δ → 0 < C → ReturnData F ω ε δ C P Q →
      ∃ ψ : ℝ → ℝ, ContDiffAt ℝ 2 ψ 0 ∧ ψ 0 = 0 ∧ deriv ψ 0 = 0 ∧
        (∀ᶠ q in nhds (0 : ℝ × ℝ), Q q = 0 ↔ q.2 = ψ q.1)

end Specs.D13Unified.Ch16.HopfScalarBranchAnalysis
