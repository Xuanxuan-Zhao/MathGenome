import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.AutonomousParameters

/-! Independent statement of paper.tex, d13:03:uniform-box.
The closed time interval depends only on its fixed center and the chosen h.
State and parameter norms are arbitrary finite-dimensional real norms.
-/

noncomputable section
open Set Metric
open D13Unified

namespace Specs.D13Unified.Ch03.UniformBox

/-- The same closed interval is used for every permitted initial datum. -/
def commonInterval (s₀ h : ℝ) (hh : 0 ≤ h) : TimeInterval where
  carrier := Icc (s₀ - h / 2) (s₀ + h / 2)
  nonempty := ⟨s₀, by constructor <;> linarith⟩
  ordConnected := ordConnected_Icc

universe u v

/-- Uniform existence, confinement and uniqueness among paths in the box.
The solution predicate includes continuity, graph membership, all within
derivatives (hence one-sided endpoint derivatives), and the initial value.
No positivity assumptions on the radii are needed: membership in the nearby
open balls already forces their positivity for each selected datum. -/
def uniformBoxExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P]
    (F : ParameterODE E P) (s₀ : ℝ) (ξ₀ : E) (p₀ : P)
    (a b c M L : ℝ),
    0 ≤ M → 0 ≤ L →
    (∀ t ∈ Icc (s₀ - a) (s₀ + a), ∀ x ∈ closedBall ξ₀ b,
      ∀ p ∈ closedBall p₀ c, ((t, x), p) ∈ F.domain) →
    (∀ t ∈ Icc (s₀ - a) (s₀ + a), ∀ x ∈ closedBall ξ₀ b,
      ∀ p ∈ closedBall p₀ c,
      ‖Ch01.AutonomousParameters.parameterEvalValue F t x p‖ ≤ M) →
    (∀ t ∈ Icc (s₀ - a) (s₀ + a), ∀ x ∈ closedBall ξ₀ b,
      ∀ y ∈ closedBall ξ₀ b, ∀ p ∈ closedBall p₀ c,
      ‖Ch01.AutonomousParameters.parameterEvalValue F t x p -
        Ch01.AutonomousParameters.parameterEvalValue F t y p‖ ≤ L * ‖x - y‖) →
    ∀ (h : ℝ) (hh : 0 < h), h ≤ a → M * h ≤ b / 2 → L * h < 1 →
    ∀ (s : ℝ) (ξ : E) (p : P),
      s ∈ Ioo (s₀ - h / 2) (s₀ + h / 2) →
      ξ ∈ ball ξ₀ (b / 2) → p ∈ ball p₀ c →
      ∃ x : ℝ → E,
        Ch01.AutonomousParameters.parameterIVPOnValue F p
          (commonInterval s₀ h hh.le) x s ξ ∧
        MapsTo x (commonInterval s₀ h hh.le).carrier (closedBall ξ₀ b) ∧
        ∀ y : ℝ → E,
          Ch01.AutonomousParameters.parameterIVPOnValue F p
            (commonInterval s₀ h hh.le) y s ξ →
          MapsTo y (commonInterval s₀ h hh.le).carrier (closedBall ξ₀ b) →
          EqOn y x (commonInterval s₀ h hh.le).carrier

end Specs.D13Unified.Ch03.UniformBox
