import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.Absolute
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp

/-! The convergence and tail part of K03.17.watson, paper.tex:4597–4636.
The asymptotic formula itself is allocated to Ch17.Watson. All integral
predicates below are independent endpoint limits of proper Darboux integrals.
The tail conclusion is stronger than needed: every fixed δ > 0 is allowed.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch17.WatsonTail
open _root_.SingleVariableAnalysis
open Ch10.OneEndpoint Ch10.SeveralEndpoints
open scoped BigOperators
abbrev Scalar := Ch01.Scalar.scalarValue

noncomputable instance scalarNormedSpace (k : ScalarKind) : NormedSpace ℝ (Scalar k) :=
  match k with
  | .real => inferInstanceAs (NormedSpace ℝ ℝ)
  | .complex => inferInstanceAs (NormedSpace ℝ ℂ)

/-- Real damping of a real or complex scalar function. -/
def damped (k : ScalarKind) (q : ℝ → Scalar k) (lam : ℝ) : ℝ → Scalar k :=
  fun t => Real.exp (-lam * t) • q t

def monomial (k : ScalarKind) (a : Scalar k) (β : ℝ) : ℝ → Scalar k :=
  fun t => (t ^ (β - 1)) • a

/-- The finite expansion and its next-order big-O error at 0+. -/
def localExpansion (k : ScalarKind) (N : ℕ) (α : ℝ)
    (a : Fin N → Scalar k) (q : ℝ → Scalar k) : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧ ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, 0 < t → t ≤ η →
    ‖q t - ∑ j : Fin N, (t ^ (α + (j : ℕ) - 1)) • a j‖ ≤
      D * t ^ (α + (N : ℝ) - 1)

def exponentialGrowth (k : ScalarKind) (q : ℝ → Scalar k) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ c A : ℝ, ∀ t : ℝ, A ≤ t → ‖q t‖ ≤ C * Real.exp (c * t)

/-- Exponential control of the absolute tail, with existence and the norm
bound for the scalar tail stated separately. No default integral is used. -/
def exponentialTail (k : ScalarKind) (q : ℝ → Scalar k) (δ : ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∃ L : ℝ, 0 < L ∧ ∀ lam : ℝ, L ≤ lam →
    ∃ T : Scalar k, ∃ A : ℝ,
      rightHasIntegralValue k (damped k q lam) δ ⊤ T ∧
      rightHasIntegralValue .real (fun t => ‖damped k q lam t‖) δ ⊤ A ∧
      ‖T‖ ≤ A ∧ A ≤ B * Real.exp (-lam * δ / 2)

def absoluteConvergence : Prop :=
  ∀ (k : ScalarKind) (N : ℕ) (α : ℝ) (a : Fin N → Scalar k) (q : ℝ → Scalar k),
    1 ≤ N → 0 < α → locallyIntegrableValue k q (0 : WithBot ℝ) ⊤ →
    localExpansion k N α a q → exponentialGrowth k q →
    ∃ L : ℝ, 0 < L ∧ ∀ lam : ℝ, L ≤ lam →
      Ch10.Absolute.absoluteValue k (damped k q lam) (0 : WithBot ℝ) ⊤ ∧
      convergesValue k (damped k q lam) (0 : WithBot ℝ) ⊤

def tailControl : Prop :=
  ∀ (k : ScalarKind) (q : ℝ → Scalar k),
    locallyIntegrableValue k q (0 : WithBot ℝ) ⊤ → exponentialGrowth k q →
    ∀ δ : ℝ, 0 < δ → exponentialTail k q δ

def retainedMonomialTails : Prop :=
  ∀ (k : ScalarKind) (N : ℕ) (α : ℝ) (a : Fin N → Scalar k),
    1 ≤ N → 0 < α → ∀ δ : ℝ, 0 < δ → ∀ j : Fin N,
      exponentialTail k (monomial k (a j) (α + (j : ℕ))) δ

end Specs.SingleVariableAnalysis.Ch17.WatsonTail
