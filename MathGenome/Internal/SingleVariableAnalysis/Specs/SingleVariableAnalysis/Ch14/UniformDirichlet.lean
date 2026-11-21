import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.UniformImproper
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.TailBounds

/-! K03.14.uniform_dirichlet, paper.tex:3407–3432.
The parameter type may be a subtype of ℝ, or any type, including the empty type.
All scalar integrals are the existing proper Darboux values or their finite
improper limits. No absolute convergence or parameter regularity is imposed.
-/
namespace Specs.SingleVariableAnalysis.Ch14.UniformDirichlet
open _root_.SingleVariableAnalysis
open Ch10.OneEndpoint Ch10.Dirichlet Ch10.TailBounds UniformImproper Set
universe u

/-- Uniform vanishing on a ray, in epsilon form. For nonnegative amplitudes
this is precisely sup_t g(R,t) → 0, also allowing unbounded early sections.
For signed amplitudes it is applied to their modulus. -/
def UniformRayVanishes {T : Type u} (g : ℝ → T → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ r : rightIndexValue a ⊤,
    ∀ R : rightIndexValue a ⊤, r.val < R.val → ∀ t : T, |g R.val t| < ε

/-- Both finite and infinite quantitative tails accompany uniform convergence.
The bounds include R = a and S = R. -/
def QuantitativeUniformTails (k : ScalarKind) (T : Type u)
    (F : ℝ → T → S.scalarValue k) (a : ℝ) (B : ℝ → T → ℝ) : Prop :=
  rightUniformConvergesValue k T F a ⊤ ∧
  ∀ t : T, ∀ R : ℝ, a ≤ R →
    (∀ S : ℝ, R ≤ S → ∃ h : I.scalarIntegrableValue k (fun x => F x t) R S,
      ‖I.scalarIntegralValue k _ h‖ ≤ B R t) ∧
    ∃ hc : rightConvergesValue k (fun x => F x t) R ⊤,
      ‖rightIntegralValue k _ R ⊤ hc‖ ≤ B R t

def uniformDirichlet : Prop :=
  ∀ (k : ScalarKind) (T : Type u) (f : ℝ → T → S.scalarValue k)
    (g g' : ℝ → T → ℝ) (a : ℝ)
    (hf : rightFamilyRegularValue k T f a ⊤) (C : ℝ),
    (∀ t : T, ∀ x : rightIndexValue a ⊤,
      ‖rightTruncationValue k (fun u => f u t) a ⊤ (hf.2 t) x‖ ≤ C) →
    (∀ t : T, COneOnRay (fun x => g x t) (fun x => g' x t) a) →
    (∀ t : T, ∀ x ∈ Ici a, 0 ≤ g x t) →
    (∀ t : T, AntitoneOn (fun x => g x t) (Ici a)) →
    UniformRayVanishes g a →
    QuantitativeUniformTails k T (fun x t => weighted k (fun u => f u t) (fun u => g u t) x)
      a (fun R t => 2 * C * g R t)

/-- A fixed sign is required on each spatial ray; the sign may depend on t.
Only the modulus needs the C¹, monotonicity and uniform vanishing properties. -/
def uniformDirichletFixedSign : Prop :=
  ∀ (k : ScalarKind) (T : Type u) (f : ℝ → T → S.scalarValue k)
    (g h' : ℝ → T → ℝ) (a : ℝ)
    (hf : rightFamilyRegularValue k T f a ⊤) (C : ℝ),
    (∀ t : T, ∀ x : rightIndexValue a ⊤,
      ‖rightTruncationValue k (fun u => f u t) a ⊤ (hf.2 t) x‖ ≤ C) →
    (∀ t : T, (∀ x ∈ Ici a, 0 ≤ g x t) ∨ (∀ x ∈ Ici a, g x t ≤ 0)) →
    (∀ t : T, COneOnRay (fun x => |g x t|) (fun x => h' x t) a) →
    (∀ t : T, AntitoneOn (fun x => |g x t|) (Ici a)) →
    UniformRayVanishes g a →
    QuantitativeUniformTails k T (fun x t => weighted k (fun u => f u t) (fun u => g u t) x)
      a (fun R t => 2 * C * |g R t|)

end Specs.SingleVariableAnalysis.Ch14.UniformDirichlet
