import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.HopfReturnExpansion

/-!
The existence, uniqueness and amplitude clauses of paper.tex:3697–3733.
All fields and coordinates below are the canonical upstream constructions.
A periodic orbit is a trace of an actual complete, nonconstant ODE solution;
uniqueness compares traces, allowing time translation and repeated periods.
The full target has only the original family hypotheses. The separate scalar
and geometric statements below record its two remaining proof components.
-/
noncomputable section

namespace Specs.D13Unified.Ch16.HopfPeriodicBranch

open Set Filter
open CubicHomologicalElimination CubicNormalForm HopfReturnExpansion

/-- Original local hypotheses, with the positive imaginary spectral branch
constructed from the real linearization rather than chosen arbitrarily. -/
def SourceHypotheses (F : ℝ × ℂ → ℂ) (ω : ℝ) : Prop :=
  ContDiffAt ℝ 5 F (0, 0) ∧ 0 < ω ∧
  Module.End.HasEigenvalue (complexifiedLinearization F 0).toLin' (eigenvalue 0 ω) ∧
  (∀ᶠ μ in nhds (0 : ℝ), F (μ, 0) = 0) ∧
  deriv (spectralReal F) 0 ≠ 0 ∧ firstLyapunovCoefficient F ≠ 0

/-- Data supplied by the upstream return theorem. In particular this includes
an actual full turn, not an abstract map with a suggestive expansion. -/
structure ReturnData (F : ℝ × ℂ → ℂ) (ω ε ρ δ C : ℝ)
    (P Q : ℝ × ℝ → ℝ) : Prop where
  radius_lt : δ < ρ
  coordinates : CoordinateValidity F ε ρ
  smooth_map : ContDiffOn ℝ 2 P (returnBox δ ε)
  smooth_quotient : ContDiffOn ℝ 2 Q (returnBox δ ε)
  smooth_error : ContDiffOn ℝ 1 (returnError F P) (returnBox δ ε)
  at_zero : ∀ μ : ℝ, |μ| < ε →
    P (0, μ) = 0 ∧ Q (0, μ) = linearReturnFactor F μ - 1
  estimates : ∀ q ∈ returnBox δ ε,
    P q = q.1 * (1 + Q q) ∧
    |returnError F P q| ≤ C * |q.1| ^ 4 ∧
    |deriv (fun r => returnError F P (r, q.2)) q.1| ≤ C * |q.1| ^ 3 ∧
    |deriv (fun μ => returnError F P (q.1, μ)) q.2| ≤ C * |q.1| ^ 4
  turn : ∀ μ r : ℝ, |μ| < ε → 0 < r → r < δ →
    FullAngularTurn F ω μ r (P (r, μ)) ρ

/-- A branch on a fixed radius interval, with a possibly smaller parameter
interval for existence at every parameter on the bifurcating side. The
larger ε₀ is retained for the local implicit graph. -/
def BranchDescription (F : ℝ × ℂ → ℂ) (P Q : ℝ × ℝ → ℝ)
    (ε₀ δ₀ ε δ C : ℝ) (ψ : ℝ → ℝ) : Prop :=
  0 < ε ∧ ε ≤ ε₀ ∧ 0 < δ ∧ δ ≤ δ₀ ∧ 0 < C ∧
  ContDiffOn ℝ 2 ψ (Ioo (-δ) δ) ∧ ψ 0 = 0 ∧ deriv ψ 0 = 0 ∧
  (∀ r : ℝ, |r| < δ →
    |ψ r| < ε₀ ∧
    |ψ r + firstLyapunovCoefficient F / deriv (spectralReal F) 0 * r ^ 2|
      ≤ C * |r| ^ 3 ∧
    |deriv ψ r + 2 * firstLyapunovCoefficient F / deriv (spectralReal F) 0 * r|
      ≤ C * |r| ^ 2) ∧
  (∀ r μ : ℝ, 0 < r → r < δ → |μ| < ε₀ →
    (P (r, μ) = r ↔ Q (r, μ) = 0) ∧
    (Q (r, μ) = 0 ↔ μ = ψ r)) ∧
  (StrictMonoOn ψ (Ioo 0 δ) ∨ StrictAntiOn ψ (Ioo 0 δ)) ∧
  (∀ μ : ℝ, |μ| < ε →
    ((∃ r ∈ Ioo 0 δ, P (r, μ) = r) ↔
      spectralReal F μ * firstLyapunovCoefficient F < 0)) ∧
  (∀ μ r s : ℝ, |μ| < ε → r ∈ Ioo 0 δ → s ∈ Ioo 0 δ →
    P (r, μ) = r → P (s, μ) = s → r = s) ∧
  /- The little-o amplitude conclusion, explicitly quantified over the roots. -/
  (∀ η > 0, ∃ ζ > 0, ∀ μ r : ℝ,
    |μ| < min ε ζ → r ∈ Ioo 0 δ → P (r, μ) = r →
    |r ^ 2 + deriv (spectralReal F) 0 / firstLyapunovCoefficient F * μ|
      ≤ η * |μ|)

/-- A complete periodic solution with actual derivatives at every real time. -/
def IsPeriodicOrbit (f : ℂ → ℂ) (Γ : Set ℂ) : Prop :=
  ∃ (z : ℝ → ℂ) (T : ℝ), 0 < T ∧ Function.Periodic z T ∧
    (∀ t : ℝ, HasDerivAt z (f (z t)) t) ∧
    (∃ s t : ℝ, z s ≠ z t) ∧ Γ = range z

/-- Absence as well as uniqueness is stated: an existence-and-uniqueness iff
alone would not exclude multiple orbits on the opposite side. -/
def OrbitClassification (F : ℝ × ℂ → ℂ) (ε σ : ℝ) : Prop :=
  ∀ μ : ℝ, |μ| < ε →
    ((∃ Γ : Set ℂ, IsPeriodicOrbit (fun z => transformedField F (μ, z)) Γ ∧
        Γ ⊆ Metric.ball 0 σ) ↔ spectralReal F μ * firstLyapunovCoefficient F < 0) ∧
    (∀ Γ Δ : Set ℂ,
      IsPeriodicOrbit (fun z => transformedField F (μ, z)) Γ → Γ ⊆ Metric.ball 0 σ →
      IsPeriodicOrbit (fun z => transformedField F (μ, z)) Δ → Δ ⊆ Metric.ball 0 σ →
      Γ = Δ)

/-- Every contained orbit has a section fixed point, and every small fixed
point gives a contained orbit. The common σ is independent of μ. -/
def OrbitFixedPointBridge (F : ℝ × ℂ → ℂ) (P : ℝ × ℝ → ℝ)
    (ε δ σ : ℝ) : Prop :=
  ∀ μ : ℝ, |μ| < ε →
    (∀ Γ : Set ℂ,
      IsPeriodicOrbit (fun z => transformedField F (μ, z)) Γ → Γ ⊆ Metric.ball 0 σ →
      ∃ r ∈ Ioo 0 δ, (r : ℂ) ∈ Γ ∧ P (r, μ) = r) ∧
    (∀ r ∈ Ioo 0 δ, P (r, μ) = r →
      ∃! Γ : Set ℂ, IsPeriodicOrbit (fun z => transformedField F (μ, z)) Γ ∧
        (r : ℂ) ∈ Γ ∧ Γ ⊆ Metric.ball 0 σ)

/-- The conclusion applies also to the input field on a fixed open neighborhood
of zero. Each such orbit is the coordinate image of a normal-coordinate orbit. -/
def OriginalOrbitClassification (F : ℝ × ℂ → ℂ) (ε σ : ℝ) : Prop :=
  ∃ U : Set ℂ, IsOpen U ∧ 0 ∈ U ∧
    ∀ μ : ℝ, |μ| < ε →
      ((∃ Γ : Set ℂ, IsPeriodicOrbit (fun z => F (μ, z)) Γ ∧ Γ ⊆ U) ↔
        spectralReal F μ * firstLyapunovCoefficient F < 0) ∧
      (∀ Γ Δ : Set ℂ, IsPeriodicOrbit (fun z => F (μ, z)) Γ → Γ ⊆ U →
        IsPeriodicOrbit (fun z => F (μ, z)) Δ → Δ ⊆ U → Γ = Δ) ∧
      (∀ Γ : Set ℂ, IsPeriodicOrbit (fun z => F (μ, z)) Γ → Γ ⊆ U →
        ∃ Δ : Set ℂ, IsPeriodicOrbit (fun z => transformedField F (μ, z)) Δ ∧
          Δ ⊆ Metric.ball 0 σ ∧ Γ = coordinate F μ '' Δ)

/-- The actual scalar return is increasing on a local interval. Its iterates
are only used while every point of the finite itinerary stays in that interval. -/
def NoHigherReturnCycles (P : ℝ × ℝ → ℝ) (ε δ : ℝ) : Prop :=
  (∀ μ : ℝ, |μ| < ε → StrictMonoOn (fun r => P (r, μ)) (Ioo 0 δ)) ∧
  ∀ μ r : ℝ, ∀ n : ℕ, |μ| < ε → 0 < n →
    (∀ k ≤ n, ((fun s => P (s, μ))^[k]) r ∈ Ioo 0 δ) →
    ((fun s => P (s, μ))^[n]) r = r → P (r, μ) = r

/-- Full original-family target. No branch, return map, periodic solution,
monotonicity, or orbit-to-section certificate is assumed. -/
def PeriodicBranch : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ), SourceHypotheses F ω →
    ∃ ε₀ > 0, ∃ ρ > 0, ∃ δ₀ > 0, ∃ C₀ > 0,
    ∃ P Q : ℝ × ℝ → ℝ,
      ReturnData F ω ε₀ ρ δ₀ C₀ P Q ∧
      ∃ ε δ C : ℝ, ∃ ψ : ℝ → ℝ,
        BranchDescription F P Q ε₀ δ₀ ε δ C ψ ∧
        NoHigherReturnCycles P ε δ ∧
        ∃ σ > 0, σ < δ ∧
          OrbitFixedPointBridge F P ε δ σ ∧
          OrbitClassification F ε σ ∧ OriginalOrbitClassification F ε σ

/-- Generic local IFT statement used for the divided displacement. -/
def ImplicitGraph : Prop :=
  ∀ Q : ℝ × ℝ → ℝ, ContDiffAt ℝ 2 Q (0, 0) → Q (0, 0) = 0 →
    (fderiv ℝ Q (0, 0) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible →
    ∃ ψ : ℝ → ℝ, ContDiffAt ℝ 2 ψ 0 ∧ ψ 0 = 0 ∧
      (∀ᶠ q in nhds (0, 0), Q q = 0 ↔ q.2 = ψ q.1)

/-- An order lemma for a finite local itinerary; no global invariance of the
return domain is imposed. -/
def NoHigherCycles : Prop :=
  ∀ (f : ℝ → ℝ) (s : Set ℝ), MonotoneOn f s →
    ∀ (n : ℕ) (r : ℝ), 0 < n →
      (∀ k ≤ n, (f^[k]) r ∈ s) → (f^[n]) r = r → f r = r

/-- Proper subset of the full target: the upstream data are constructed from
exactly the original hypotheses. -/
def SourceReturnData : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ), SourceHypotheses F ω →
    ∃ ε > 0, ∃ ρ > 0, ∃ δ > 0, ∃ C > 0, ∃ P Q : ℝ × ℝ → ℝ,
      ReturnData F ω ε ρ δ C P Q

/-- Proper subset: the genuine divided displacement has its local C² zero
graph and the graph's first derivative at zero vanishes. -/
def SourceFlatImplicitGraph : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω ε ρ δ C : ℝ) (P Q : ℝ × ℝ → ℝ),
    SourceHypotheses F ω → 0 < ε → 0 < δ → ReturnData F ω ε ρ δ C P Q →
    ∃ ψ : ℝ → ℝ, ContDiffAt ℝ 2 ψ 0 ∧ ψ 0 = 0 ∧ deriv ψ 0 = 0 ∧
      (∀ᶠ q in nhds (0, 0), Q q = 0 ↔ q.2 = ψ q.1)

/-- Proper subset: monotonicity and cycle exclusion for the actual map,
with the necessary uniform domain shrink made explicit. -/
def SourceNoHigherReturnCycles : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω ε ρ δ C : ℝ) (P Q : ℝ × ℝ → ℝ),
    SourceHypotheses F ω → 0 < ε → 0 < δ → ReturnData F ω ε ρ δ C P Q →
    ∃ η > 0, ∃ d > 0, η ≤ ε ∧ d ≤ δ ∧ NoHigherReturnCycles P η d

end Specs.D13Unified.Ch16.HopfPeriodicBranch
