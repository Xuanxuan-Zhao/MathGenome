import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Dirichlet
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.ZeroCovers
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.TaggedEquivalence

/-! K03.08.countable_changes, paper.tex:2281–2296.
The counterexample retains the exact exceptional set Q ∩ [0,1].
The equality statements require both Darboux integrals to exist; boundedness
is included in the shared integrability predicates. No existence conclusion
is inferred merely from agreement outside a length-zero set.
-/
namespace Specs.SingleVariableAnalysis.Ch08.CountableChanges

def modificationCounterexample : Prop :=
  let E : Set ℝ := {x | x ∈ Set.Icc (0 : ℝ) 1 ∧ ∃ q : ℚ, (q : ℝ) = x}
  E.Countable ∧ ZeroCovers.lengthZeroValue E ∧
    (∀ x : ℝ, Dirichlet.dirichletValue x ≠ 0 ↔ x ∈ E) ∧
    DarbouxSums.boundedOnIntervalValue (fun _ => 0) 0 1 ∧
    DarbouxSums.boundedOnIntervalValue Dirichlet.dirichletValue 0 1 ∧
    (∃ h : Integral.realIntegrableValue (fun _ => 0) 0 1,
      Integral.realIntegralValue _ h = 0) ∧
    ¬ Integral.realIntegrableValue Dirichlet.dirichletValue 0 1

def realIntegralEqOffLengthZero : Prop :=
  ∀ (f g : ℝ → ℝ) (a b : ℝ) (E : Set ℝ), ZeroCovers.lengthZeroValue E →
    ∀ (hf : Integral.realIntegrableValue f a b)
      (hg : Integral.realIntegrableValue g a b),
      (∀ x ∈ Set.Icc a b, x ∉ E → f x = g x) →
        Integral.realIntegralValue f hf = Integral.realIntegralValue g hg

def complexIntegralEqOffLengthZero : Prop :=
  ∀ (f g : ℝ → ℂ) (a b : ℝ) (E : Set ℝ), ZeroCovers.lengthZeroValue E →
    ∀ (hf : Integral.complexIntegrableValue f a b)
      (hg : Integral.complexIntegrableValue g a b),
      (∀ x ∈ Set.Icc a b, x ∉ E → f x = g x) →
        Integral.complexIntegralValue f hf = Integral.complexIntegralValue g hg

end Specs.SingleVariableAnalysis.Ch08.CountableChanges
