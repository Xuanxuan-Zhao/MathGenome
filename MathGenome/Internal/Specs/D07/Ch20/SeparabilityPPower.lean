import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.Separable

/-!
Independent specification for K07.20.separability_p_power,
paper.tex:5823–5831 (chapters/M07.20.tex:23–31).
Both generated fields are intermediate fields of the same arbitrary ambient
extension L/K with its specified embedding. Only the element a is assumed
algebraic; no algebraicity, finiteness or perfection of L/K is required.
The prime characteristic is positive, and the canonical `IsSeparable` predicate
means that the minimal polynomial of a over K is separable.
-/

universe u v

namespace Specs.D07.Ch20.SeparabilityPPower

/-- The Frobenius-power criterion, including both implications. -/
def SeparabilityCriterion : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (p : ℕ) [CharP K p], p.Prime → ∀ a : L, IsAlgebraic K a →
      (IsSeparable K a ↔
        IntermediateField.adjoin K {a ^ p} = IntermediateField.adjoin K {a})

end Specs.D07.Ch20.SeparabilityPPower
