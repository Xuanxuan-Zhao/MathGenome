import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyLogModulus
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.Beurling

/-! Inner–outer factorization, the first paragraph of
`fa2:p4:hardy-factorization`. Outer means shift cyclicity in the canonical
coefficient Hardy space. The singular-measure classification is a separate goal. -/
noncomputable section
namespace ExpandedFA.PartIV.HardyInnerOuter.Spec
open HardyDiskSpec HardyLogModulus

/-- Every choice of the unimodular constant in the displayed formula is cyclic. -/
def ExponentialCyclicity : Prop := ∀ (f : H2), f ≠ 0 → ∀ c : ℂ, ‖c‖ = 1 →
  ∀ o : H2, Set.EqOn (eval o) (exponentialFactor (boundaryLog f) c) disk → IsOuter o

/-- An outer vector has only constant inner divisors. Products are analytic
products on the disk, not products of arbitrary coefficient representatives. -/
def NoInnerDivisor : Prop := ∀ o : H2, IsOuter o → ∀ j : H2, IsInner j →
  ∀ g : H2, (∀ z ∈ disk, eval o z = eval j z * eval g z) →
    ∃ a : ℂ, ‖a‖ = 1 ∧ j = lp.single 2 0 a

/-- Factorization with the actual exponential formula, for each phase choice. -/
def Factorization : Prop := ∀ f : H2, f ≠ 0 → ∀ c : ℂ, ‖c‖ = 1 →
  ∃ i o : H2, IsInner i ∧ IsOuter o ∧
    (∀ z ∈ disk, eval f z = eval i z * eval o z) ∧
    Set.EqOn (eval o) (exponentialFactor (boundaryLog f) c) disk

/-- The constants in the two factors are opposite. -/
def Uniqueness : Prop := ∀ (f i o j p : H2), f ≠ 0 →
  IsInner i → IsOuter o → IsInner j → IsOuter p →
  (∀ z ∈ disk, eval f z = eval i z * eval o z) →
  (∀ z ∈ disk, eval f z = eval j z * eval p z) →
  ∃ a : ℂ, ‖a‖ = 1 ∧ j = a • i ∧ p = a⁻¹ • o

/-- Every cyclic outer factor, including factors chosen independently of the
construction, has the stated logarithmic integral representation. -/
def OuterFormula : Prop := ∀ (f i o : H2), f ≠ 0 → IsInner i → IsOuter o →
  (∀ z ∈ disk, eval f z = eval i z * eval o z) →
  ∃ c : ℂ, ‖c‖ = 1 ∧
    Set.EqOn (eval o) (exponentialFactor (boundaryLog f) c) disk

end ExpandedFA.PartIV.HardyInnerOuter.Spec
