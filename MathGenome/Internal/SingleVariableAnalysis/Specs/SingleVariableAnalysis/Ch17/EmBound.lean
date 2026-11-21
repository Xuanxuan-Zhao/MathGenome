import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.EulerMaclaurin

/-! K03.17.em_bound, paper.tex:4468–4481.
The finite bound uses the same Bernoulli polynomials, closed derivative
families, and proper Darboux integral as the finite summation formula.
The supremum defining M is proved to be an attained maximum on [0,1].
The remainder is exactly minus `term`, so the factorial is outside the
unnormalized integral. Both integrability assertions are conclusions. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch17.EmBound
open Ch04.Higher Ch08.Integral Ch17.Bernoulli Ch17.EmRecursion

abbrev bernoulliMaximumType := ℕ → ℝ

def bernoulliMaximumValue : bernoulliMaximumType := fun n =>
  sSup ((fun t : ℝ => |(bernoulliPolynomialValue n).eval t|) '' Set.Icc 0 1)

/-- In particular M is finite, nonnegative, attained, and bounds every unit
interval value; there is no empty-set/default-supremum convention in use. -/
def bernoulliMaximumAttained : Prop := ∀ n : ℕ,
  0 ≤ bernoulliMaximumValue n ∧
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      |(bernoulliPolynomialValue n).eval t| = bernoulliMaximumValue n ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        |(bernoulliPolynomialValue n).eval u| ≤ bernoulliMaximumValue n

/-- Real-variable derivatives, including their continuous endpoint values.
The scalar parameter is instantiated only with ℝ and ℂ below. -/
def remainderBound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : (ℝ → E) → ℝ → ℝ → Prop)
    (J : (f : ℝ → E) → {a b : ℝ} → I f a b → E) : Prop :=
  ∀ (a b : ℤ), a < b → ∀ (m : ℕ), 1 ≤ m →
    ∀ (f : ℝ → E) (D : ℕ → ℝ → E),
    closedDerivativeFamilyValue (2 * m) f a b D →
    ∃ hR : I (rawIntegrand (2 * m) D) a b,
    ∃ hN : realIntegrableValue (fun x => ‖D (2 * m) x‖) a b,
      ‖-term J (2 * m) D hR‖ ≤
        (bernoulliMaximumValue (2 * m) / ((2 * m).factorial : ℝ)) *
          realIntegralValue (fun x => ‖D (2 * m) x‖) hN

def realRemainderBound : Prop := remainderBound realIntegrableValue (@realIntegralValue)
def complexRemainderBound : Prop := remainderBound complexIntegrableValue (@complexIntegralValue)

end Specs.SingleVariableAnalysis.Ch17.EmBound
