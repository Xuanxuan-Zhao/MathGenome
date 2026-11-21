import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.Primitive
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.ElementaryDerivatives
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.TrigInverses

/-!
K03.09.elementary_primitives, paper.tex:2533–2567.
The indefinite integrals are families of primitives, not definite integrals.
`formulaOn` records the derivative and the full family on every interval in
its stated domain, allowing included endpoints with the upstream continuity
convention. Equality is only on the interval; ambient extensions are arbitrary.
All elementary functions are the upstream series/inverse representatives.
Natural powers give the all-real interpretation of nonnegative integer powers.
The last proposition allows arbitrary constants on disjoint open pieces,
including the components separated by zeros or tangent poles.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch09.ElementaryPrimitives
open Set
open Ch07.ExpConstruction Ch07.LogConstruction Ch07.RealPowers Ch07.SinCos
open Ch07.TrigInverses

/-- Full meaning of a primitive table entry on a domain. -/
def formulaOn (F f : ℝ → ℝ) (D : Set ℝ) : Prop :=
  (∀ x ∈ D, HasDerivAt F (f x) x) ∧
  ∀ I : Set ℝ, I.OrdConnected → I ⊆ D →
    Primitive.continuousPrimitiveOnValue F f I ∧
    ∀ G : ℝ → ℝ, Primitive.continuousPrimitiveOnValue G f I ↔
      ∃ c : ℝ, ∀ x ∈ I, G x = F x + c

def powerPrimitive : Prop :=
  ∀ α : ℝ, α ≠ -1 → formulaOn
    (fun x => realPowerValue x (α + 1) / (α + 1))
    (fun x => realPowerValue x α) (Ioi 0)

def naturalPowerPrimitive : Prop :=
  ∀ n : ℕ, formulaOn (fun x => x ^ (n + 1) / ((n : ℝ) + 1))
    (fun x => x ^ n) univ

def reciprocalPrimitive : Prop :=
  formulaOn (fun x => seriesLogValue |x|) (fun x => 1 / x) {x | x ≠ 0}

def exponentialPrimitive : Prop :=
  ∀ a : ℝ, a ≠ 0 → formulaOn (fun x => realSeriesExpValue (a * x) / a)
    (fun x => realSeriesExpValue (a * x)) univ

def zeroExponentialPrimitive : Prop :=
  formulaOn (fun x => x) (fun x => realSeriesExpValue (0 * x)) univ

def sinePrimitive : Prop :=
  formulaOn realSeriesSinValue realSeriesCosValue univ

def negativeCosinePrimitive : Prop :=
  formulaOn (fun x => -realSeriesCosValue x) realSeriesSinValue univ

def arctangentPrimitive : Prop :=
  formulaOn principalArctanValue (fun x => 1 / (1 + x ^ 2)) univ

def arcsinePrimitive : Prop :=
  formulaOn principalArcsinValue (fun x => 1 / Real.sqrt (1 - x ^ 2)) {x | |x| < 1}

def tangentPrimitive : Prop :=
  formulaOn (fun x => -seriesLogValue |realSeriesCosValue x|)
    (fun x => realSeriesSinValue x / realSeriesCosValue x)
    {x | realSeriesCosValue x ≠ 0}

/-- The same family statement for complex-valued primitives, using real increments. -/
def complexFormulaOn (F f : ℝ → ℂ) (D : Set ℝ) : Prop :=
  (∀ x ∈ D, HasDerivAt F (f x) x) ∧
  ∀ I : Set ℝ, I.OrdConnected → I ⊆ D →
    Primitive.continuousPrimitiveOnValue F f I ∧
    ∀ G : ℝ → ℂ, Primitive.continuousPrimitiveOnValue G f I ↔
      ∃ c : ℂ, ∀ x ∈ I, G x = F x + c

/-- Every real table entry also describes its complex-valued primitive family. -/
def complexLift : Prop :=
  ∀ (F f : ℝ → ℝ) (D : Set ℝ), formulaOn F f D →
    complexFormulaOn (fun x => (F x : ℂ)) (fun x => (f x : ℂ)) D

def complexExponentialPrimitive : Prop :=
  ∀ a : ℂ, a ≠ 0 → complexFormulaOn
    (fun x => seriesExpValue (a * (x : ℂ)) / a)
    (fun x => seriesExpValue (a * (x : ℂ))) univ

def complexZeroExponentialPrimitive : Prop :=
  complexFormulaOn (fun x => (x : ℂ))
    (fun x => seriesExpValue ((0 : ℂ) * (x : ℂ))) univ

/-- Every assignment of constants on disjoint open pieces is allowed. -/
def independentComponentConstants : Prop :=
  ∀ (F f : ℝ → ℝ) (D : Set ℝ), formulaOn F f D →
  ∀ (ι : Type) (I : ι → Set ℝ), (∀ i, IsOpen (I i)) →
    (∀ i j, i ≠ j → Disjoint (I i) (I j)) → (∀ i, I i ⊆ D) →
    ∀ c : ι → ℝ, ∃ G : ℝ → ℝ,
      Primitive.isPrimitiveOnValue G f (⋃ i, I i) ∧
      ∀ i, ∀ x ∈ I i, G x = F x + c i

/-- Complex constants are likewise arbitrary on separate open components. -/
def independentComplexComponentConstants : Prop :=
  ∀ (F f : ℝ → ℂ) (D : Set ℝ), complexFormulaOn F f D →
  ∀ (ι : Type) (I : ι → Set ℝ), (∀ i, IsOpen (I i)) →
    (∀ i j, i ≠ j → Disjoint (I i) (I j)) → (∀ i, I i ⊆ D) →
    ∀ c : ι → ℂ, ∃ G : ℝ → ℂ,
      Primitive.isPrimitiveOnValue G f (⋃ i, I i) ∧
      ∀ i, ∀ x ∈ I i, G x = F x + c i

end Specs.SingleVariableAnalysis.Ch09.ElementaryPrimitives
