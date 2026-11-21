import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.EmRecursion

/-! K03.17.euler_maclaurin, paper.tex:4432–4471.
The scalar choices are exactly ℝ and ℂ. The closed derivative family is the
source C^(2m) condition, including continuous one-sided endpoint values.
Integrals are the proper Darboux integrals, with integrability asserted in
the conclusion. The range index r represents the paper's index r+1 = 1,…,m.
The shared Bernoulli convention has B₁ = −1/2 and uses Int.fract x = x−⌊x⌋. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch17.EulerMaclaurin
open scoped BigOperators
open Ch04.Higher Ch08.Integral Ch17.Bernoulli Ch17.EmRecursion

/-- The complete finite summation formula, including existence of both proper
integrals. `D j` is the jth derivative with its closed-interval extension. -/
def formula {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : (ℝ → E) → ℝ → ℝ → Prop)
    (J : (f : ℝ → E) → {a b : ℝ} → I f a b → E) : Prop :=
  ∀ (a b : ℤ), a < b → ∀ (m : ℕ), 1 ≤ m →
    ∀ (f : ℝ → E) (D : ℕ → ℝ → E),
    closedDerivativeFamilyValue (2 * m) f a b D →
    ∃ hf : I f a b, ∃ hR : I (rawIntegrand (2 * m) D) a b,
      trapezoid f a b = J f hf +
        (∑ r ∈ Finset.range m,
          (bernoulliNumberValue (2 * (r + 1)) / ((2 * (r + 1)).factorial : ℝ)) •
            (D (2 * (r + 1) - 1) b - D (2 * (r + 1) - 1) a)) -
        term J (2 * m) D hR

def realFormula : Prop := formula realIntegrableValue (@realIntegralValue)
def complexFormula : Prop := formula complexIntegrableValue (@complexIntegralValue)

end Specs.SingleVariableAnalysis.Ch17.EulerMaclaurin
