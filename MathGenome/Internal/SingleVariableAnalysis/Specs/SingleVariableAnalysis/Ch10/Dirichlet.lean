import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.OneEndpoint
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! K03.10.dirichlet, paper.tex:3078–3096. A real multiplier acts on either
canonical scalar field. All integrals are the existing proper Darboux values,
and convergence is the independent finite limit of those values. C¹ is
expressed on every regular closed truncation, with an interior real derivative
and a continuous derivative extension. There is no condition at a singularity.
The right statement includes +∞ and finite endpoints approached from below;
the left statement approaches a finite endpoint from above (and also covers -∞).
-/
namespace Specs.SingleVariableAnalysis.Ch10.Dirichlet
open _root_.SingleVariableAnalysis
open OneEndpoint
open Set

/-- Multiplication by a real function in the selected scalar field. -/
def weighted (k : ScalarKind) (f : ℝ → S.scalarValue k) (g : ℝ → ℝ) :
    ℝ → S.scalarValue k :=
  match k with
  | .real => fun x => (show ℝ from f x) * g x
  | .complex => fun x => (show ℂ from f x) * (g x : ℂ)

/-- The infinite and finite right-endpoint forms, with precisely cofinal limits. -/
def rightDirichlet : Prop :=
  ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k) (g g' : ℝ → ℝ)
    (a : ℝ) (b : WithTop ℝ) (hf : rightRegularValue k f a b) (C : ℝ),
    (∀ t : rightIndexValue a b, ‖rightTruncationValue k f a b hf t‖ ≤ C) →
    (∀ t : rightIndexValue a b,
      ContinuousOn g (Icc a t.val) ∧ ContinuousOn g' (Icc a t.val) ∧
      ∀ x ∈ Ioo a t.val, HasDerivAt g (g' x) x) →
    (MonotoneOn g {x | a ≤ x ∧ (x : WithTop ℝ) < b} ∨
      AntitoneOn g {x | a ≤ x ∧ (x : WithTop ℝ) < b}) →
    (∀ ε : ℝ, 0 < ε → ∃ r : rightIndexValue a b,
      ∀ t : rightIndexValue a b, r.val < t.val → |g t.val| < ε) →
    rightConvergesValue k (weighted k f g) a b

/-- Bounded accumulation is measured from the regular right endpoint.
The truncation direction is reversed, without linking endpoint parameters. -/
def leftDirichlet : Prop :=
  ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k) (g g' : ℝ → ℝ)
    (a : WithBot ℝ) (b : ℝ) (hf : leftRegularValue k f a b) (C : ℝ),
    (∀ t : leftIndexValue a b, ‖leftTruncationValue k f a b hf t‖ ≤ C) →
    (∀ t : leftIndexValue a b,
      ContinuousOn g (Icc t.val b) ∧ ContinuousOn g' (Icc t.val b) ∧
      ∀ x ∈ Ioo t.val b, HasDerivAt g (g' x) x) →
    (MonotoneOn g {x | a < (x : WithBot ℝ) ∧ x ≤ b} ∨
      AntitoneOn g {x | a < (x : WithBot ℝ) ∧ x ≤ b}) →
    (∀ ε : ℝ, 0 < ε → ∃ r : leftIndexValue a b,
      ∀ t : leftIndexValue a b, t.val < r.val → |g t.val| < ε) →
    leftConvergesValue k (weighted k f g) a b

end Specs.SingleVariableAnalysis.Ch10.Dirichlet
