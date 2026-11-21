import MathGenome.Internal.LinearPDE.P201Specs.Potential.BallGreen

/-! Poisson--Dirichlet on a ball, paper.tex:954–1022.
The source is a genuine compactly supported smooth test in the open ball.
Solutions are compared on the closed ball; their values elsewhere are immaterial. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff
namespace P201Specs.BallPoissonDirichlet

abbrev VolumePotentialType := {n : ℕ} → (a : Space n) → (r : ℝ) →
  Test ℝ ⟨ball a r, isOpen_ball⟩ → Space n → ℝ

def volumePotential : VolumePotentialType := fun a r f x =>
  ∫ y in ball a r, BallGreen.kernel a r x y * f y

/-- Interior classical equation and the exact continuous boundary trace. -/
def IsSolution {n : ℕ} (a : Space n) (r : ℝ)
    (f : Test ℝ ⟨ball a r, isOpen_ball⟩) (g : C(sphere a r, ℝ))
    (u : Space n → ℝ) : Prop :=
  ContDiffOn ℝ 2 u (ball a r) ∧ ContinuousOn u (closedBall a r) ∧
    (∀ x ∈ ball a r, -laplacian u x = f x) ∧ ∀ ζ : sphere a r, u ζ = g ζ

/-- Includes continuity through the entire boundary, not merely the interior. -/
def VolumePotentialStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (a : Space n) (r : ℝ), 0 < r →
    ∀ f : Test ℝ ⟨ball a r, isOpen_ball⟩,
      (∀ x ∈ closedBall a r, IntegrableOn
        (fun y => BallGreen.kernel a r x y * f y) (ball a r)) ∧
      ContDiffOn ℝ 2 (volumePotential a r f) (ball a r) ∧
      ContinuousOn (volumePotential a r f) (closedBall a r) ∧
      (∀ x ∈ ball a r, -laplacian (volumePotential a r f) x = f x) ∧
      ∀ ζ ∈ sphere a r, volumePotential a r f ζ = 0

def PoissonDirichletStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (a : Space n) (r : ℝ), 0 < r →
    ∀ (f : Test ℝ ⟨ball a r, isOpen_ball⟩) (g : C(sphere a r, ℝ)),
      ∃ u : Space n → ℝ, IsSolution a r f g u ∧
        (∀ x ∈ ball a r, u x =
          (∫ y in ball a r, BallGreen.kernel a r x y * f y) +
          ∫ ζ, BallPoisson.kernel a r x ζ • BallPoisson.boundaryValue a r g ζ
            ∂sphereSurface a r) ∧
        ∀ v : Space n → ℝ, IsSolution a r f g v → EqOn v u (closedBall a r)

/-- The same ordinary Green integral for real or complex scalar data. -/
abbrev ScalarVolumePotentialType := {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] →
  (a : Space n) → (r : ℝ) → Test 𝕜 ⟨ball a r, isOpen_ball⟩ → Space n → 𝕜

def scalarVolumePotential : ScalarVolumePotentialType := fun a r f x =>
  ∫ y in ball a r, BallGreen.kernel a r x y • f y

def ScalarIsSolution {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (a : Space n) (r : ℝ)
    (f : Test 𝕜 ⟨ball a r, isOpen_ball⟩) (g : C(sphere a r, 𝕜))
    (u : Space n → 𝕜) : Prop :=
  ContDiffOn ℝ 2 u (ball a r) ∧ ContinuousOn u (closedBall a r) ∧
    (∀ x ∈ ball a r, -laplacian u x = f x) ∧ ∀ ζ : sphere a r, u ζ = g ζ

def ScalarVolumePotentialStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (a : Space n) (r : ℝ), 0 < r → ∀ f : Test 𝕜 ⟨ball a r, isOpen_ball⟩,
      (∀ x ∈ closedBall a r, IntegrableOn
        (fun y => BallGreen.kernel a r x y • f y) (ball a r)) ∧
      ContDiffOn ℝ 2 (scalarVolumePotential a r f) (ball a r) ∧
      ContinuousOn (scalarVolumePotential a r f) (closedBall a r) ∧
      (∀ x ∈ ball a r, -laplacian (scalarVolumePotential a r f) x = f x) ∧
      ∀ ζ ∈ sphere a r, scalarVolumePotential a r f ζ = 0

def ScalarPoissonDirichletStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (a : Space n) (r : ℝ), 0 < r →
    ∀ (f : Test 𝕜 ⟨ball a r, isOpen_ball⟩) (g : C(sphere a r, 𝕜)),
      ∃ u : Space n → 𝕜, ScalarIsSolution a r f g u ∧
        (∀ x ∈ ball a r, u x =
          (∫ y in ball a r, BallGreen.kernel a r x y • f y) +
          ∫ ζ, BallPoisson.kernel a r x ζ • BallPoisson.boundaryValue a r g ζ
            ∂sphereSurface a r) ∧
        ∀ v : Space n → 𝕜, ScalarIsSolution a r f g v → EqOn v u (closedBall a r)

/-- The outward unit normal acts in the second kernel variable. -/
def NormalDerivativeStatement : Prop := BallGreen.NormalDerivativeStatement

end P201Specs.BallPoissonDirichlet
