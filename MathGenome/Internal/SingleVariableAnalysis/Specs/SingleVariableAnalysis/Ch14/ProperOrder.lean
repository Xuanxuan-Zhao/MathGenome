import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.ProperContinuity

/-!
K03.14.proper_order, paper.tex:3333–3356. The inner values are the shared
proper Darboux families. The outer integrands are extended by zero only to
supply ambient representatives for that same one-dimensional API. Every inner
and outer integrability assertion is included. Continuity is relative to the
compact rectangle; both inequalities on endpoints are non-strict.
-/
namespace Specs.SingleVariableAnalysis.Ch14.ProperOrder
open ProperDefinition
open Specs.SingleVariableAnalysis.Ch08

/-- Ambient representative of a function on a closed interval. -/
noncomputable def intervalExtension {E : Type*} [Zero E] {a b : ℝ}
    (g : Set.Icc a b → E) (x : ℝ) : E := by
  classical
  exact if hx : x ∈ Set.Icc a b then g ⟨x, hx⟩ else 0

def realOrder : Prop :=
  ∀ {a b c d : ℝ}, a ≤ b → c ≤ d →
    ∀ f : Set.Icc a b → Set.Icc c d → ℝ,
    Continuous (Function.uncurry f) →
    ∃ (hx : ∀ t, sectionIntegrableValue .real f t)
      (ht : ∀ x, sectionIntegrableValue .real (fun t x => f x t) x),
    let F := fun t => familyValue .real f ⟨t, hx t⟩
    let G := fun x => familyValue .real (fun t x => f x t) ⟨x, ht x⟩
    ∃ (hF : Integral.realIntegrableValue (intervalExtension F) c d)
      (hG : Integral.realIntegrableValue (intervalExtension G) a b),
      Integral.realIntegralValue _ hF = Integral.realIntegralValue _ hG

def complexOrder : Prop :=
  ∀ {a b c d : ℝ}, a ≤ b → c ≤ d →
    ∀ f : Set.Icc a b → Set.Icc c d → ℂ,
    Continuous (Function.uncurry f) →
    ∃ (hx : ∀ t, sectionIntegrableValue .complex f t)
      (ht : ∀ x, sectionIntegrableValue .complex (fun t x => f x t) x),
    let F := fun t => familyValue .complex f ⟨t, hx t⟩
    let G := fun x => familyValue .complex (fun t x => f x t) ⟨x, ht x⟩
    ∃ (hF : Integral.complexIntegrableValue (intervalExtension F) c d)
      (hG : Integral.complexIntegrableValue (intervalExtension G) a b),
      Integral.complexIntegralValue _ hF = Integral.complexIntegralValue _ hG

end Specs.SingleVariableAnalysis.Ch14.ProperOrder
