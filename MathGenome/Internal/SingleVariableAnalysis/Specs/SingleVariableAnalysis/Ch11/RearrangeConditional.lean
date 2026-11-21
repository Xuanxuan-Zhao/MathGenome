import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.FiniteRearrangement
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.PositiveNegative
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.Limsup

/-!
Independent obligations for K03.11.rearrange_conditional, paper.tex:1097–1120.
All rearrangements are permutations of the original natural-number indices,
including zero terms. Conditional convergence and partial sums retain their
ordinary ordered meanings. Endpoints range over all of EReal; no boundedness
or distinctness hypothesis is imposed on the endpoints.
-/
namespace Specs.SingleVariableAnalysis.Ch11.RearrangeConditional

open Absolute PartialSums
open Specs.SingleVariableAnalysis.Ch01.SequenceLimit
open Specs.SingleVariableAnalysis.Ch01.Limsup

/-- Divergence here is a limit of the entire sequence of partial sums. -/
def positiveInfinityRearrangement : Prop :=
  ∀ a : ℕ → ℝ, realConditionallyConvergesValue a →
    ∃ π : Equiv.Perm ℕ,
      divergesToPosInfinityValue (realPartialSumValue (fun n => a (π n)))

def negativeInfinityRearrangement : Prop :=
  ∀ a : ℕ → ℝ, realConditionallyConvergesValue a →
    ∃ π : Equiv.Perm ℕ,
      divergesToNegInfinityValue (realPartialSumValue (fun n => a (π n)))

/-- Includes equal finite endpoints, equal infinite endpoints, and mixed endpoints. -/
def extendedRearrangement : Prop :=
  ∀ a : ℕ → ℝ, realConditionallyConvergesValue a →
    ∀ α β : EReal, α ≤ β → ∃ π : Equiv.Perm ℕ,
      sequenceLiminfValue (realPartialSumValue (fun n => a (π n))) = α ∧
      sequenceLimsupValue (realPartialSumValue (fun n => a (π n))) = β

/-- The equal finite endpoint case, supplied by the upstream finite-target theorem. -/
def finiteDiagonalRearrangement : Prop :=
  ∀ a : ℕ → ℝ, realConditionallyConvergesValue a →
    ∀ s : ℝ, ∃ π : Equiv.Perm ℕ,
      sequenceLiminfValue (realPartialSumValue (fun n => a (π n))) = (s : EReal) ∧
      sequenceLimsupValue (realPartialSumValue (fun n => a (π n))) = (s : EReal)

/-- The entire diagonal of the extended endpoint square. -/
def diagonalRearrangement : Prop :=
  ∀ a : ℕ → ℝ, realConditionallyConvergesValue a →
    ∀ x : EReal, ∃ π : Equiv.Perm ℕ,
      sequenceLiminfValue (realPartialSumValue (fun n => a (π n))) = x ∧
      sequenceLimsupValue (realPartialSumValue (fun n => a (π n))) = x

end Specs.SingleVariableAnalysis.Ch11.RearrangeConditional
