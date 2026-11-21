import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.ProperOrder
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.UniformImproper

/-! K03.14.parameter_order, paper.tex:3486–3512.
All integrals are the shared proper Darboux integrals or finite limits of
those integrals. The parameter interval may be a singleton. The scalar is
exactly real or complex. The abstract version records section integrability
and the finite order identity explicitly, without imposing joint continuity.
-/
namespace Specs.SingleVariableAnalysis.Ch14.ParameterOrder
open _root_.SingleVariableAnalysis
open Ch10.OneEndpoint Ch14.UniformImproper Ch08.Integral
open Ch14.ProperOrder

/-- The proper truncation as an ambient function of the parameter. -/
noncomputable def truncatedFamily (k : ScalarKind) {a c d : ℝ}
    (f : ℝ → Set.Icc c d → S.scalarValue k)
    (h : rightFamilyRegularValue k (Set.Icc c d) f a ⊤)
    (R : rightIndexValue a ⊤) : ℝ → S.scalarValue k :=
  intervalExtension (fun t => rightTruncationValue k (fun x => f x t) a ⊤ (h.2 t) R)

/-- The parameter integral at regular spatial points. Its zero extension below
`a` is irrelevant; every value used in an integral carries proper integrability. -/
noncomputable def parameterIntegral (k : ScalarKind) {a c d : ℝ}
    (f : ℝ → Set.Icc c d → S.scalarValue k)
    (ht : ∀ x : ℝ, a ≤ x → scalarIntegrableValue k (intervalExtension (f x)) c d)
    (x : ℝ) : S.scalarValue k := by
  classical
  exact if hx : a ≤ x then scalarIntegralValue k (intervalExtension (f x)) (ht x hx)
    else 0

/-- A proper left outer integral and a finite right improper integral, with
both the has-value assertion and equality to the chosen improper value. -/
def orderConclusion (k : ScalarKind) {a c d : ℝ}
    (F : Set.Icc c d → S.scalarValue k) (H : ℝ → S.scalarValue k) : Prop :=
  ∃ hF : scalarIntegrableValue k (intervalExtension F) c d,
    rightHasIntegralValue k H a ⊤ (scalarIntegralValue k (intervalExtension F) hF) ∧
    ∃ hH : rightConvergesValue k H a ⊤,
      scalarIntegralValue k (intervalExtension F) hF = rightIntegralValue k H a ⊤ hH

/-- Other proper hypotheses may replace joint continuity. Neither the outer
proper integrability of the limit nor the improper convergence is assumed. -/
def abstractOrder : Prop := ∀ (k : ScalarKind) {a c d : ℝ}, c ≤ d →
  ∀ (f : ℝ → Set.Icc c d → S.scalarValue k) (F : Set.Icc c d → S.scalarValue k)
    (h : rightFamilyRegularValue k (Set.Icc c d) f a ⊤)
    (H : ℝ → S.scalarValue k)
    (ht : ∀ x : ℝ, a ≤ x → scalarIntegrableValue k (intervalExtension (f x)) c d),
    (∀ x (hx : a ≤ x), H x = scalarIntegralValue k (intervalExtension (f x)) (ht x hx)) →
    rightUniformHasIntegralValue k (Set.Icc c d) f a ⊤ F →
    (∀ R : rightIndexValue a ⊤,
      ∃ (hFR : scalarIntegrableValue k (truncatedFamily k f h R) c d)
        (hHR : scalarIntegrableValue k H a R.val),
        scalarIntegralValue k H hHR = scalarIntegralValue k (truncatedFamily k f h R) hFR) →
    orderConclusion (a := a) k F H

def continuousOrder : Prop := ∀ (k : ScalarKind) {a c d : ℝ}, c ≤ d →
  ∀ (f : ℝ → Set.Icc c d → S.scalarValue k) (F : Set.Icc c d → S.scalarValue k),
    (∀ R : rightIndexValue a ⊤,
      Continuous (fun p : Set.Icc a R.val × Set.Icc c d => f p.1.val p.2)) →
    rightUniformHasIntegralValue k (Set.Icc c d) f a ⊤ F →
    ∃ ht : ∀ x : ℝ, a ≤ x → scalarIntegrableValue k (intervalExtension (f x)) c d,
      orderConclusion (a := a) k F (parameterIntegral k f ht)

end Specs.SingleVariableAnalysis.Ch14.ParameterOrder
