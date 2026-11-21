import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch09.Frobenius

/-! Independent scope of paper.tex, Theorem d13:09:resonance.
The two roots are the complete pair, counted with multiplicity. The first
multiplier is holomorphic on the original disc. The second multiplier and
independence are asserted on a smaller disc with the very same logarithm.
-/
noncomputable section

namespace Specs.D13Unified.Ch09.Resonance
open Specs.D13Unified.Ch09.Indicial

/-- Vieta identities specify both roots, including when they coincide. -/
def AreIndicialRoots (E : Equation) (r₁ r₂ : ℂ) : Prop :=
  pZeroValue E = 1 - r₁ - r₂ ∧ qZeroValue E = r₁ * r₂

lemma slitDisc_mono {ρ R angle : ℝ} (h : ρ ≤ R) :
    slitDiscValue ρ angle ⊆ slitDiscValue R angle := by
  rintro z ⟨w, hw, rfl⟩
  exact ⟨w, ⟨Metric.ball_subset_ball h hw.1, hw.2⟩, rfl⟩

/-- Restriction preserves the coefficient functions, not just their germs. -/
def restrictEquation (E : Equation) (ρ : ℝ) (hρ : 0 < ρ) (hR : ρ ≤ E.radius) :
    Equation where
  radius := ρ
  radius_pos := hρ
  p := E.p
  q := E.q
  p_holomorphic := E.p_holomorphic.mono (Metric.ball_subset_ball hR)
  q_holomorphic := E.q_holomorphic.mono (Metric.ball_subset_ball hR)

/-- The smaller branch has exactly the original angle and logarithm. -/
def restrictBranch (E : Equation) (b : LogBranch E.radius)
    (ρ : ℝ) (hρ : 0 < ρ) (hR : ρ ≤ E.radius) :
    LogBranch (restrictEquation E ρ hρ hR).radius where
  angle := b.angle
  log := b.log
  holomorphic := b.holomorphic.mono (slitDisc_mono hR)
  exp_log := fun z hz => b.exp_log z (slitDisc_mono hR hz)

/-- No logarithmic coefficient is imposed to be zero in positive resonance. -/
def secondFunction (E : Equation) (L : LogBranch E.radius) (r₁ r₂ : ℂ)
    (m : ℕ) (a b : ℂ → ℂ) (c : ℂ) : ℂ → ℂ :=
  if m = 0 then
    fun z => (powerValue L r₁ z * a z) * L.log z + powerValue L r₁ z * b z
  else
    fun z => powerValue L r₂ z * b z + c * (powerValue L r₁ z * a z) * L.log z

def FirstSolution (E : Equation) (L : LogBranch E.radius) (r₁ : ℂ)
    (a : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ a (Metric.ball 0 E.radius) ∧ a 0 = 1 ∧
    solutionValue E L (fun z => powerValue L r₁ z * a z)

/-- A complete first solution, with the original convergence radius retained. -/
def firstSolutionType : Prop :=
  ∀ (E : Equation) (L : LogBranch E.radius) (r₁ r₂ : ℂ) (m : ℕ),
    AreIndicialRoots E r₁ r₂ → r₁ - r₂ = (m : ℂ) →
    ∃ a : ℂ → ℂ, FirstSolution E L r₁ a

/-- Full repeated/resonant conclusion, with actual equations and independence.
Holomorphy on an open disc includes the center and entails convergent Taylor
expansions there. All powers use the supplied branch, also after shrinking. -/
def resonanceType : Prop :=
  ∀ (E : Equation) (L : LogBranch E.radius) (r₁ r₂ : ℂ) (m : ℕ),
    AreIndicialRoots E r₁ r₂ → r₁ - r₂ = (m : ℂ) →
    ∃ a : ℂ → ℂ, FirstSolution E L r₁ a ∧
      ∃ (ρ : ℝ) (hρ : 0 < ρ) (hR : ρ < E.radius) (b : ℂ → ℂ) (c : ℂ),
        DifferentiableOn ℂ b (Metric.ball 0 ρ) ∧ (m ≠ 0 → b 0 = 1) ∧
        solutionValue (restrictEquation E ρ hρ hR.le) (restrictBranch E L ρ hρ hR.le)
          (secondFunction E L r₁ r₂ m a b c) ∧
        independentValue (restrictBranch E L ρ hρ hR.le)
          (fun z => powerValue L r₁ z * a z) (secondFunction E L r₁ r₂ m a b c)

end Specs.D13Unified.Ch09.Resonance
