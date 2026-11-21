import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.UniformImproper

/-! K03.14.uniform_comparison, paper.tex:3385–3407.
All values are limits of proper Darboux truncations. WithTop/WithBot cover
finite singular endpoints as well as infinity. The regular starting interval
may extend beyond the domination region: only each section's proper
integrability is required there. Parameter types include subtypes and the empty
type. The extended nonnegative supremum agrees with the usual supremum for
nonempty families, and is zero for the empty family.
-/
namespace Specs.SingleVariableAnalysis.Ch14.UniformComparison
open _root_.SingleVariableAnalysis
open Ch10.OneEndpoint Ch14.UniformImproper
open scoped ENNReal
universe u

/-- Right endpoints: domination begins at A, possibly later than the regular
start a. Each tail has its own finite improper value; the bound is pointwise
and also holds for the supremum over all parameters. -/
def rightComparison : Prop := ∀ (k : ScalarKind) (T : Type u)
    (f : ℝ → T → S.scalarValue k) (g : ℝ → ℝ)
    (a A : ℝ) (b : WithTop ℝ),
  a ≤ A → (A : WithTop ℝ) < b →
  rightFamilyRegularValue k T f a b →
  rightConvergesValue .real g A b →
  (∀ x : ℝ, A ≤ x → (x : WithTop ℝ) < b → 0 ≤ g x) →
  (∀ x : ℝ, A ≤ x → (x : WithTop ℝ) < b → ∀ t : T, ‖f x t‖ ≤ g x) →
  ∃ F : T → S.scalarValue k,
    rightUniformHasIntegralValue k T f a b F ∧
    ∀ R : ℝ, A ≤ R → (R : WithTop ℝ) < b →
      ∃ (G : ℝ) (H : T → S.scalarValue k),
        rightHasIntegralValue .real g R b G ∧ 0 ≤ G ∧
        (∀ t : T, rightHasIntegralValue k (fun x => f x t) R b (H t) ∧ ‖H t‖ ≤ G) ∧
        (⨆ t : T, ENNReal.ofReal ‖H t‖) ≤ ENNReal.ofReal G

/-- Left endpoints: domination is needed only between the singular endpoint a
and B. No common bound is imposed on the remaining regular segment [B,b]. -/
def leftComparison : Prop := ∀ (k : ScalarKind) (T : Type u)
    (f : ℝ → T → S.scalarValue k) (g : ℝ → ℝ)
    (a : WithBot ℝ) (B b : ℝ),
  B ≤ b → a < (B : WithBot ℝ) →
  leftFamilyRegularValue k T f a b →
  leftConvergesValue .real g a B →
  (∀ x : ℝ, a < (x : WithBot ℝ) → x ≤ B → 0 ≤ g x) →
  (∀ x : ℝ, a < (x : WithBot ℝ) → x ≤ B → ∀ t : T, ‖f x t‖ ≤ g x) →
  ∃ F : T → S.scalarValue k,
    leftUniformHasIntegralValue k T f a b F ∧
    ∀ R : ℝ, a < (R : WithBot ℝ) → R ≤ B →
      ∃ (G : ℝ) (H : T → S.scalarValue k),
        leftHasIntegralValue .real g a R G ∧ 0 ≤ G ∧
        (∀ t : T, leftHasIntegralValue k (fun x => f x t) a R (H t) ∧ ‖H t‖ ≤ G) ∧
        (⨆ t : T, ENNReal.ofReal ‖H t‖) ≤ ENNReal.ofReal G

end Specs.SingleVariableAnalysis.Ch14.UniformComparison
