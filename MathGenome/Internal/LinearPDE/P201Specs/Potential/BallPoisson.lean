import MathGenome.Internal.LinearPDE.P201Specs.Potential.MeanValues

/-! Independent specification of paper.tex, Theorem `thm:pde-ball-poisson`,
853–898. Boundary data are actual continuous functions on the sphere, with
no prescribed extension off it. All derivatives are over ℝ. -/
noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

namespace P201Specs.BallPoisson

abbrev KernelType := {n : ℕ} → Space n → ℝ → Space n → Space n → ℝ

/-- The exact kernel, with omega n = |S^{n-1}| from the shared interface. -/
def kernel : KernelType := fun {n} a r x ζ =>
  (r ^ 2 - ‖x - a‖ ^ 2) / (r * omega n * ‖x - ζ‖ ^ n)

abbrev BoundaryValueType := {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] →
  (a : Space n) → (r : ℝ) → C(sphere a r, 𝕜) → Space n → 𝕜

/-- A measurable representative of boundary data; values off the sphere do
not contribute to surface integration. -/
def boundaryValue : BoundaryValueType := by
  classical
  exact fun a r g ζ => if h : ζ ∈ sphere a r then g ⟨ζ, h⟩ else 0

abbrev PoissonIntegralType := {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] →
  (a : Space n) → (r : ℝ) → C(sphere a r, 𝕜) → Space n → 𝕜

/-- The surface integral for real or complex data. -/
def poissonIntegral : PoissonIntegralType := fun a r g x =>
  ∫ ζ, kernel a r x ζ • boundaryValue a r g ζ ∂sphereSurface a r

/-- The specified continuous extension: Poisson integral inside, boundary
values on the sphere. Its value outside the closed ball is irrelevant. -/
def poissonExtension : PoissonIntegralType := by
  classical
  exact fun a r g x => if x ∈ ball a r then poissonIntegral a r g x else boundaryValue a r g x

/-- Strict positivity in the interior, in every dimension n ≥ 2. -/
def KernelPositiveStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (a : Space n) (r : ℝ), 0 < r →
    ∀ x ∈ ball a r, ∀ ζ ∈ sphere a r, 0 < kernel a r x ζ

/-- Harmonicity is the upstream C²/coordinate-Laplacian predicate. -/
def KernelHarmonicStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (a : Space n) (r : ℝ), 0 < r →
    ∀ ζ ∈ sphere a r,
      MeanValues.IsHarmonic ⟨ball a r, isOpen_ball⟩ (fun x => kernel a r x ζ)

/-- Integrability is explicit, so the totalized Bochner integral cannot
supply a spurious normalization. -/
def KernelMassStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (a : Space n) (r : ℝ), 0 < r →
    ∀ x ∈ ball a r, Integrable (kernel a r x) (sphereSurface a r) ∧
      (∫ ζ, kernel a r x ζ ∂sphereSurface a r) = 1

/-- The integral of any continuous datum is well-defined and harmonic. -/
def PoissonHarmonicStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (a : Space n) (r : ℝ), 0 < r → ∀ g : C(sphere a r, 𝕜),
    (∀ x ∈ ball a r, Integrable
      (fun ζ => kernel a r x ζ • boundaryValue a r g ζ) (sphereSurface a r)) ∧
    MeanValues.IsHarmonic ⟨ball a r, isOpen_ball⟩ (poissonIntegral a r g)

/-- Boundary convergence is along every approach from the interior. -/
def BoundaryLimitStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (a : Space n) (r : ℝ), 0 < r → ∀ (g : C(sphere a r, 𝕜))
    (ζ : sphere a r), Tendsto (poissonIntegral a r g)
      (𝓝[ball a r] (ζ : Space n)) (𝓝 (g ζ))

/-- Continuous extension with the exact trace, including all boundary points. -/
def ContinuousExtensionStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (a : Space n) (r : ℝ), 0 < r → ∀ g : C(sphere a r, 𝕜),
    ContinuousOn (poissonExtension a r g) (closedBall a r) ∧
      ∀ ζ : sphere a r, poissonExtension a r g ζ = g ζ

/-- Uniqueness imposes only interior harmonicity and continuity on the closed
ball, with no differentiability at the boundary. -/
def UniquenessStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (a : Space n) (r : ℝ), 0 < r → ∀ (g : C(sphere a r, 𝕜))
    (v : Space n → 𝕜),
    MeanValues.IsHarmonic ⟨ball a r, isOpen_ball⟩ v →
    ContinuousOn v (closedBall a r) → (∀ ζ : sphere a r, v ζ = g ζ) →
    EqOn v (poissonExtension a r g) (closedBall a r)

/-- Any harmonic function on any open neighborhood of the closed ball has
this representation. The integral formula itself is asserted in the interior. -/
def RepresentationStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (a : Space n) (r : ℝ), 0 < r → ∀ (Ω : Domain n) (u : Space n → 𝕜),
    closedBall a r ⊆ (Ω : Set _) → MeanValues.IsHarmonic Ω u →
    ∃ g : C(sphere a r, 𝕜), (∀ ζ : sphere a r, g ζ = u ζ) ∧
      EqOn u (poissonIntegral a r g) (ball a r) ∧
      EqOn u (poissonExtension a r g) (closedBall a r)

end P201Specs.BallPoisson
