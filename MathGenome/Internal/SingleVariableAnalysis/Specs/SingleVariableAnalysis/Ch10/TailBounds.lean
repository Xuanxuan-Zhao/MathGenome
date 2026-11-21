import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.Dirichlet

/-! K03.10.tail_bounds, paper.tex:3204–3226.
The scalar is exactly ℝ or ℂ. Proper values are Darboux integrals and infinite
values are independent finite limits of proper truncations. The C¹ hypothesis
uses a continuous derivative extension on each closed regular truncation;
no derivative of the accumulation of a merely integrable function is assumed.
-/
namespace Specs.SingleVariableAnalysis.Ch10.TailBounds
open _root_.SingleVariableAnalysis
open OneEndpoint Dirichlet Set

/-- C¹ regularity on the closed ray, with real increments. -/
def COneOnRay (g g' : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ t : rightIndexValue a ⊤,
    ContinuousOn g (Icc a t.val) ∧ ContinuousOn g' (Icc a t.val) ∧
    ∀ x ∈ Ioo a t.val, HasDerivAt g (g' x) x

/-- The real multiplier tends to zero along the ray. -/
def VanishesOnRay (g : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ r : rightIndexValue a ⊤,
    ∀ t : rightIndexValue a ⊤, r.val < t.val → |g t.val| < ε

/-- The sharper estimate when accumulation is bounded directly from the
chosen tail origin R. It supplies both proper and improper integrability. -/
def directTailBounds : Prop :=
  ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k) (g g' : ℝ → ℝ)
    (R : ℝ) (hf : rightRegularValue k f R ⊤) (C_R : ℝ),
    (∀ t : rightIndexValue R ⊤, ‖rightTruncationValue k f R ⊤ hf t‖ ≤ C_R) →
    COneOnRay g g' R → (∀ x ∈ Ici R, 0 ≤ g x) → AntitoneOn g (Ici R) →
    VanishesOnRay g R →
    (∀ S : ℝ, R ≤ S → ∃ h : I.scalarIntegrableValue k (weighted k f g) R S,
      ‖I.scalarIntegralValue k _ h‖ ≤ C_R * g R) ∧
    ∃ hc : rightConvergesValue k (weighted k f g) R ⊤,
      ‖rightIntegralValue k _ R ⊤ hc‖ ≤ C_R * g R

/-- Bounded accumulation from a gives convergence and quantitative bounds
for every S ≥ R ≥ a, including R = a and the singleton S = R. -/
def accumulationTailBounds : Prop :=
  ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k) (g g' : ℝ → ℝ)
    (a : ℝ) (hf : rightRegularValue k f a ⊤) (C : ℝ),
    (∀ t : rightIndexValue a ⊤, ‖rightTruncationValue k f a ⊤ hf t‖ ≤ C) →
    COneOnRay g g' a → (∀ x ∈ Ici a, 0 ≤ g x) → AntitoneOn g (Ici a) →
    VanishesOnRay g a →
    rightConvergesValue k (weighted k f g) a ⊤ ∧
    ∀ R : ℝ, a ≤ R →
      (∀ S : ℝ, R ≤ S → ∃ h : I.scalarIntegrableValue k (weighted k f g) R S,
        ‖I.scalarIntegralValue k _ h‖ ≤ 2 * C * g R) ∧
      ∃ hc : rightConvergesValue k (weighted k f g) R ⊤,
        ‖rightIntegralValue k _ R ⊤ hc‖ ≤ 2 * C * g R

end Specs.SingleVariableAnalysis.Ch10.TailBounds
