import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import Mathlib.Topology.Instances.Real.Lemmas

/-! Independent statements for K03.08.products (paper.tex:2088–2111).
All integrability predicates are the upstream proper Darboux predicates.
The range condition refers to the domain [a,b]; continuity of the outer
function is required only on the stated compact real interval. Reciprocals
are bounded away from zero on the actual range, with no sign restriction. -/
namespace Specs.SingleVariableAnalysis.Ch08.Products
open Specs.SingleVariableAnalysis.Ch08.Integral

def realProduct : Prop := ∀ {f g : ℝ → ℝ} {a b : ℝ},
  realIntegrableValue f a b → realIntegrableValue g a b →
    realIntegrableValue (fun x => f x * g x) a b

def complexProduct : Prop := ∀ {f g : ℝ → ℂ} {a b : ℝ},
  complexIntegrableValue f a b → complexIntegrableValue g a b →
    complexIntegrableValue (fun x => f x * g x) a b

def realComposition : Prop := ∀ {f : ℝ → ℝ} {a b c d : ℝ} {Φ : ℝ → ℝ},
  realIntegrableValue f a b → ContinuousOn Φ (Set.Icc c d) →
  (∀ x ∈ Set.Icc a b, f x ∈ Set.Icc c d) →
    realIntegrableValue (fun x => Φ (f x)) a b

def complexComposition : Prop := ∀ {f : ℝ → ℝ} {a b c d : ℝ} {Φ : ℝ → ℂ},
  realIntegrableValue f a b → ContinuousOn Φ (Set.Icc c d) →
  (∀ x ∈ Set.Icc a b, f x ∈ Set.Icc c d) →
    complexIntegrableValue (fun x => Φ (f x)) a b

def realReciprocal : Prop := ∀ {f : ℝ → ℝ} {a b d : ℝ},
  realIntegrableValue f a b → 0 < d → (∀ x ∈ Set.Icc a b, d ≤ |f x|) →
    realIntegrableValue (fun x => 1 / f x) a b

def complexReciprocal : Prop := ∀ {f : ℝ → ℂ} {a b d : ℝ},
  complexIntegrableValue f a b → 0 < d → (∀ x ∈ Set.Icc a b, d ≤ ‖f x‖) →
    complexIntegrableValue (fun x => 1 / f x) a b

end Specs.SingleVariableAnalysis.Ch08.Products
