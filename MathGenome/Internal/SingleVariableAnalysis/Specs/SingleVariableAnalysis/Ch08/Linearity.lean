import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.TaggedEquivalence

/-! Independent statements of K03.08.linearity, paper.tex:2050–2067.
Finite families include the empty family; coefficients are arbitrary scalars.
Splitting uses the same function restricted by its interval arguments, retaining
closed endpoints and the singleton convention of the upstream integral. -/
namespace Specs.SingleVariableAnalysis.Ch08.Linearity
open _root_.SingleVariableAnalysis.Riemann
open scoped BigOperators

def realFiniteLinearity : Prop :=
  ∀ (n : ℕ) (α : Fin n → ℝ) (f : Fin n → ℝ → ℝ) {a b : ℝ}, a ≤ b →
    ∀ h : ∀ j, Integral.realIntegrableValue (f j) a b,
    ∃ H : Integral.realIntegrableValue (fun x => ∑ j, α j * f j x) a b,
      Integral.realIntegralValue _ H = ∑ j, α j * Integral.realIntegralValue (f j) (h j)

def complexFiniteLinearity : Prop :=
  ∀ (n : ℕ) (α : Fin n → ℂ) (f : Fin n → ℝ → ℂ) {a b : ℝ}, a ≤ b →
    ∀ h : ∀ j, Integral.complexIntegrableValue (f j) a b,
    ∃ H : Integral.complexIntegrableValue (fun x => ∑ j, α j * f j x) a b,
      Integral.complexIntegralValue _ H = ∑ j, α j * Integral.complexIntegralValue (f j) (h j)

def realSplit : Prop :=
  ∀ (f : ℝ → ℝ) {a c b : ℝ}, a ≤ c → c ≤ b →
    DarbouxSums.boundedOnIntervalValue f a b →
    (Integral.realIntegrableValue f a b ↔
      Integral.realIntegrableValue f a c ∧ Integral.realIntegrableValue f c b) ∧
    (∀ (h : Integral.realIntegrableValue f a b)
      (hl : Integral.realIntegrableValue f a c) (hr : Integral.realIntegrableValue f c b),
      Integral.realIntegralValue f h =
        Integral.realIntegralValue f hl + Integral.realIntegralValue f hr)

def complexSplit : Prop :=
  ∀ (f : ℝ → ℂ) {a c b : ℝ}, a ≤ c → c ≤ b →
    (∃ M : ℝ, ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M) →
    (Integral.complexIntegrableValue f a b ↔
      Integral.complexIntegrableValue f a c ∧ Integral.complexIntegrableValue f c b) ∧
    (∀ (h : Integral.complexIntegrableValue f a b)
      (hl : Integral.complexIntegrableValue f a c) (hr : Integral.complexIntegrableValue f c b),
      Integral.complexIntegralValue f h =
        Integral.complexIntegralValue f hl + Integral.complexIntegralValue f hr)

end Specs.SingleVariableAnalysis.Ch08.Linearity
