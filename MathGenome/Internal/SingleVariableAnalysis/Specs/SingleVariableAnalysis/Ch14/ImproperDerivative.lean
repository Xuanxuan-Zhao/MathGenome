import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.UniformImproper
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.ProperDerivative
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.ProperContinuity

/-!
K03.14.improper_derivative, paper.tex:3447–3484.
The truncations are the existing proper Darboux integrals, indexed by all
real R > a, and the improper limits are their cofinal limits at +∞.
An ambient representative of each truncation permits ordinary derivatives
inside the parameter interval without imposing any condition outside it.
D is an arbitrary endpoint extension of the derivative-integral family;
no integrability of ft at parameter endpoints is imposed. Its uniform
convergence includes the endpoints;
no continuity of their limit G is assumed. Both scalars use real increments.
The singleton parameter interval is included.
-/
namespace Specs.SingleVariableAnalysis.Ch14.ImproperDerivative

open Set _root_.SingleVariableAnalysis
open Ch10.OneEndpoint Ch14.UniformImproper

/-- The canonical real scalar action, also when the target is complex. -/
noncomputable instance scalarRealNormedSpace (k : ScalarKind) :
    NormedSpace ℝ (S.scalarValue k) :=
  match k with
  | .real => inferInstanceAs (NormedSpace ℝ ℝ)
  | .complex => inferInstanceAs (NormedSpace ℝ ℂ)

def improperDerivative : Prop :=
  ∀ (k : ScalarKind) (a c d : ℝ), c ≤ d →
    ∀ (f : ℝ → Icc c d → S.scalarValue k)
      (ft : ℝ → Ioo c d → S.scalarValue k)
      (hf : rightFamilyRegularValue k (Icc c d) f a ⊤)
      (hft : rightFamilyRegularValue k (Ioo c d) ft a ⊤)
      (FR D : rightIndexValue a ⊤ → ℝ → S.scalarValue k)
      (G : ℝ → S.scalarValue k),
    (∀ R (t : Icc c d), FR R t =
      rightTruncationValue k (fun x => f x t) a ⊤ (hf.2 t) R) →
    (∀ R, ContinuousOn (FR R) (Icc c d)) →
    (∀ R t (ht : t ∈ Ioo c d), HasDerivAt (FR R)
      (rightTruncationValue k (fun x => ft x ⟨t, ht⟩)
        a ⊤ (hft.2 ⟨t, ht⟩) R) t) →
    (∀ R (t : Ioo c d), D R t =
      rightTruncationValue k (fun x => ft x t) a ⊤ (hft.2 t) R) →
    (∀ ε : ℝ, 0 < ε → ∃ r : rightIndexValue a ⊤,
      ∀ R : rightIndexValue a ⊤, r.val < R.val →
        ∀ t ∈ Icc c d, dist (D R t) (G t) < ε) →
    (∃ (t₀ : Icc c d) (L : S.scalarValue k),
      rightHasIntegralValue k (fun x => f x t₀) a ⊤ L) →
    ∃ F : ℝ → S.scalarValue k,
      rightUniformHasIntegralValue k (Icc c d) f a ⊤ (fun t => F t) ∧
      (∀ t : Icc c d, rightHasIntegralValue k (fun x => f x t) a ⊤ (F t)) ∧
      ContinuousOn F (Icc c d) ∧
      ∀ t ∈ Ioo c d, HasDerivAt F (G t) t

/-- Apply this at each regular spatial truncation. Joint continuity supplies
proper integrability, continuity up to the parameter endpoints, and the proper
derivative formula. No parameter derivative at an endpoint is requested. -/
def rectangleProperAssumptions : Prop :=
  ∀ (k : ScalarKind) {a b c d : ℝ}, a ≤ b → c ≤ d →
    ∀ f ft : ℝ → Icc a b → S.scalarValue k,
    ProperDerivative.JointContinuous (Icc c d) f →
    ProperDerivative.JointContinuous (Icc c d) ft →
    (∀ t ∈ Ioo c d, ∀ x, HasDerivAt (fun s => f s x) (ft t x) t) →
    ∃ (hf : ∀ t : Icc c d,
        ProperDefinition.sectionIntegrableValue k (fun x t => f t.val x) t)
      (hft : ∀ t : Icc c d,
        ProperDefinition.sectionIntegrableValue k (fun x t => ft t.val x) t),
    ∀ F G : ℝ → S.scalarValue k,
      (∀ t : Icc c d, F t =
        ProperDefinition.familyValue k (fun x t => f t.val x) ⟨t, hf t⟩) →
      (∀ t : Icc c d, G t =
        ProperDefinition.familyValue k (fun x t => ft t.val x) ⟨t, hft t⟩) →
      ContinuousOn F (Icc c d) ∧ ∀ t ∈ Ioo c d, HasDerivAt F (G t) t

end Specs.SingleVariableAnalysis.Ch14.ImproperDerivative
