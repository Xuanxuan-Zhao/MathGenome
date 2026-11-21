import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.ProperDerivative
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Oriented

/-!
K03.14.moving_endpoints, paper.tex:3301–3334. All increments are real.
J is an arbitrary open parameter neighborhood; thus the hypotheses may be
restricted to a neighborhood of the parameter where the rule is used.
The spatial domain is exactly [L,U], and the endpoint images are contained in
it. No ordering of α and β is required, including at a crossing. Zero extension
is used only as the ambient representative required by the shared Darboux API.
The conclusions establish integrability, then differentiate every ambient
representative of the actual oriented Riemann integral family. They include
real and complex scalar values and degenerate spatial intervals.
-/
namespace Specs.SingleVariableAnalysis.Ch14.MovingEndpoints
open Set ProperDerivative
open Specs.SingleVariableAnalysis.Ch08

noncomputable def realSection {L U : ℝ} (f : ℝ → Icc L U → ℝ)
    (t : ℝ) : ℝ → ℝ :=
  ProperDefinition.sectionValue .real
    (fun x (_ : (univ : Set ℝ)) => f t x) ⟨0, mem_univ _⟩

def realMovingEndpoints : Prop :=
  ∀ {L U : ℝ}, L ≤ U → ∀ (J : Set ℝ), IsOpen J →
    ∀ (α β : ℝ → ℝ), ContDiffOn ℝ 1 α J → ContDiffOn ℝ 1 β J →
    ∀ (hα : ∀ t ∈ J, α t ∈ Icc L U) (hβ : ∀ t ∈ J, β t ∈ Icc L U)
      (f g : ℝ → Icc L U → ℝ),
      JointContinuous J f → JointContinuous J g →
      (∀ t ∈ J, ∀ x, HasDerivAt (fun s => f s x) (g t x) t) →
      ∃ (hf : ∀ t ∈ J, Oriented.realIntegrableValue (realSection f t) (α t) (β t))
        (hg : ∀ t ∈ J, Oriented.realIntegrableValue (realSection g t) (α t) (β t)),
        ∀ F G : ℝ → ℝ,
          (∀ t (ht : t ∈ J), F t = Oriented.realIntegralValue _ (hf t ht)) →
          (∀ t (ht : t ∈ J), G t = Oriented.realIntegralValue _ (hg t ht)) →
          ∀ t (ht : t ∈ J), HasDerivAt F
            ((deriv β t) • f t ⟨β t, hβ t ht⟩ -
              (deriv α t) • f t ⟨α t, hα t ht⟩ + G t) t

noncomputable def complexSection {L U : ℝ} (f : ℝ → Icc L U → ℂ)
    (t : ℝ) : ℝ → ℂ :=
  ProperDefinition.sectionValue .complex
    (fun x (_ : (univ : Set ℝ)) => f t x) ⟨0, mem_univ _⟩

def complexMovingEndpoints : Prop :=
  ∀ {L U : ℝ}, L ≤ U → ∀ (J : Set ℝ), IsOpen J →
    ∀ (α β : ℝ → ℝ), ContDiffOn ℝ 1 α J → ContDiffOn ℝ 1 β J →
    ∀ (hα : ∀ t ∈ J, α t ∈ Icc L U) (hβ : ∀ t ∈ J, β t ∈ Icc L U)
      (f g : ℝ → Icc L U → ℂ),
      JointContinuous J f → JointContinuous J g →
      (∀ t ∈ J, ∀ x, HasDerivAt (fun s => f s x) (g t x) t) →
      ∃ (hf : ∀ t ∈ J, Oriented.complexIntegrableValue (complexSection f t) (α t) (β t))
        (hg : ∀ t ∈ J, Oriented.complexIntegrableValue (complexSection g t) (α t) (β t)),
        ∀ F G : ℝ → ℂ,
          (∀ t (ht : t ∈ J), F t = Oriented.complexIntegralValue _ (hf t ht)) →
          (∀ t (ht : t ∈ J), G t = Oriented.complexIntegralValue _ (hg t ht)) →
          ∀ t (ht : t ∈ J), HasDerivAt F
            ((deriv β t) • f t ⟨β t, hβ t ht⟩ -
              (deriv α t) • f t ⟨α t, hα t ht⟩ + G t) t

end Specs.SingleVariableAnalysis.Ch14.MovingEndpoints
