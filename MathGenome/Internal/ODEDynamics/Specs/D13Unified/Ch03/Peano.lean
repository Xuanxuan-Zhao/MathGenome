import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.SolutionConcepts
import Mathlib.Topology.MetricSpace.ProperSpace

/-! Independent statements for paper.tex, d13:03:peano (lines 679–722).
The boxed statements need continuity only on the given closed box. They cover
any finite-dimensional real normed space, with no Lipschitz hypothesis. Included
endpoints use the same within derivatives as the shared solution predicates.
Nonnegativity of the state radius follows from `0 ≤ M`, `0 < h`, `M*h ≤ b`.
-/
noncomputable section
open Set Metric
namespace Specs.D13Unified.Ch03.Peano
universe u

def rightExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : ℝ × E → E) (s a b M h : ℝ) (ξ : E),
    ContinuousOn f (Icc s (s+a) ×ˢ closedBall ξ b) →
    (∀ p ∈ Icc s (s+a) ×ˢ closedBall ξ b, ‖f p‖ ≤ M) →
    0 ≤ M → 0 < h → h ≤ a → M*h ≤ b →
    ∃ x : ℝ → E, ContinuousOn x (Icc s (s+h)) ∧ x s = ξ ∧
      (∀ t ∈ Icc s (s+h), x t ∈ closedBall ξ b) ∧
      ∀ t ∈ Icc s (s+h), HasDerivWithinAt x (f (t, x t)) (Icc s (s+h)) t

def leftExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : ℝ × E → E) (s a b M h : ℝ) (ξ : E),
    ContinuousOn f (Icc (s-a) s ×ˢ closedBall ξ b) →
    (∀ p ∈ Icc (s-a) s ×ˢ closedBall ξ b, ‖f p‖ ≤ M) →
    0 ≤ M → 0 < h → h ≤ a → M*h ≤ b →
    ∃ x : ℝ → E, ContinuousOn x (Icc (s-h) s) ∧ x s = ξ ∧
      (∀ t ∈ Icc (s-h) s, x t ∈ closedBall ξ b) ∧
      ∀ t ∈ Icc (s-h) s, HasDerivWithinAt x (f (t, x t)) (Icc (s-h) s) t

/-- The box theorem in the canonical interval/ODE language. -/
def rightODEExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : _root_.D13Unified.ODE E)
    (s a b M h : ℝ) (ξ : E),
    (Icc s (s+a) ×ˢ closedBall ξ b) ⊆ F.domain →
    (∀ p ∈ Icc s (s+a) ×ˢ closedBall ξ b, ‖F.eval p.1 p.2‖ ≤ M) →
    0 ≤ M → ∀ hh : 0 < h, h ≤ a → M*h ≤ b →
    ∃ x : ℝ → E,
      _root_.Specs.D13Unified.Ch01.SolutionConcepts.ivpOnValue F
        ⟨Icc s (s+h), ⟨s, le_rfl, le_add_of_nonneg_right hh.le⟩, ordConnected_Icc⟩ x s ξ ∧
      ∀ t ∈ Icc s (s+h), x t ∈ closedBall ξ b

def leftODEExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : _root_.D13Unified.ODE E)
    (s a b M h : ℝ) (ξ : E),
    (Icc (s-a) s ×ˢ closedBall ξ b) ⊆ F.domain →
    (∀ p ∈ Icc (s-a) s ×ˢ closedBall ξ b, ‖F.eval p.1 p.2‖ ≤ M) →
    0 ≤ M → ∀ hh : 0 < h, h ≤ a → M*h ≤ b →
    ∃ x : ℝ → E,
      _root_.Specs.D13Unified.Ch01.SolutionConcepts.ivpOnValue F
        ⟨Icc (s-h) s, ⟨s, sub_le_self s hh.le, le_rfl⟩, ordConnected_Icc⟩ x s ξ ∧
      ∀ t ∈ Icc (s-h) s, x t ∈ closedBall ξ b

/-- Two-sided local existence in the actual open time-state domain, with full
C¹ regularity and initial data, using the canonical ODE and solution objects. -/
def localExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : _root_.D13Unified.ODE E) (s : ℝ) (ξ : E),
    (s, ξ) ∈ F.domain →
    ∃ (h : ℝ) (hh : 0 < h) (x : ℝ → E),
      _root_.Specs.D13Unified.Ch01.SolutionConcepts.classicalIVPOnValue F
        ⟨⟨Ioo (s-h) (s+h), ⟨s, sub_lt_self s hh, lt_add_of_pos_right s hh⟩, ordConnected_Ioo⟩,
          isOpen_Ioo⟩ x s ξ

end Specs.D13Unified.Ch03.Peano
