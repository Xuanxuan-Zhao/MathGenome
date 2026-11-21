import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.PiPeriod
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
Independent specification for K03.07.tan, paper.tex:1745–1761.
The natural domain is the nonzero set of the constructed cosine. Tangent
is a function on that subtype: it has no value at an excluded pole.
The quotient in the derivative assertion is an ambient representative,
tested only at points of the natural (open) domain. Limits use the
pullback of the indicated one-sided real approach to that same subtype.
Thus neither a finite value nor a finite limit is assigned at a pole.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch07.Tan
open Ch07.SinCos Ch07.PiPeriod
open Filter
open scoped Topology

def tangentDomainType : Type := Set ℝ
def tangentDomainValue : Set ℝ := {x | realSeriesCosValue x ≠ 0}
def tangentType : Type := tangentDomainValue → ℝ
def tangentValue : tangentDomainValue → ℝ := fun x => realSeriesSinValue x / realSeriesCosValue x

def domainDescription : Prop := ∀ x : ℝ,
  x ∈ tangentDomainValue ↔ ¬ ∃ k : ℤ, x = analyticPiValue / 2 + k * analyticPiValue

def poleExcluded : Prop := ∀ k : ℤ,
  analyticPiValue / 2 + k * analyticPiValue ∉ tangentDomainValue

def domainPeriod : Prop := ∀ x : ℝ,
  x + analyticPiValue ∈ tangentDomainValue ↔ x ∈ tangentDomainValue

def periodic : Prop := ∀ (x : ℝ) (hx : x ∈ tangentDomainValue)
  (hshift : x + analyticPiValue ∈ tangentDomainValue),
  tangentValue ⟨x + analyticPiValue, hshift⟩ = tangentValue ⟨x, hx⟩

def derivative : Prop := ∀ x : ℝ, x ∈ tangentDomainValue →
  HasDerivAt (fun t => realSeriesSinValue t / realSeriesCosValue t)
    (1 / realSeriesCosValue x ^ 2) x

/-- The derivative is the same for every ambient extension of natural tangent. -/
def extensionDerivative : Prop := ∀ (f : ℝ → ℝ),
  (∀ x : tangentDomainValue, f x = tangentValue x) →
  ∀ x : ℝ, x ∈ tangentDomainValue → HasDerivAt f (1 / realSeriesCosValue x ^ 2) x

def leftPoleLimit : Prop := ∀ k : ℤ,
  Tendsto tangentValue
    (comap (fun x : tangentDomainValue => (x : ℝ))
      (𝓝[<] (analyticPiValue / 2 + k * analyticPiValue))) atTop

def rightPoleLimit : Prop := ∀ k : ℤ,
  Tendsto tangentValue
    (comap (fun x : tangentDomainValue => (x : ℝ))
      (𝓝[>] (analyticPiValue / 2 + k * analyticPiValue))) atBot

end Specs.SingleVariableAnalysis.Ch07.Tan
