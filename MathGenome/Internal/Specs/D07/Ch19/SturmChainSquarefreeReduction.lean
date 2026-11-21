import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Basic.Real.Basic

/-!
Independent statements for the squarefree reduction in K07.19.sturm_chain,
paper.tex:5581–5595. The gcd is the normalized polynomial gcd (hence monic
for a nonzero input), and division is exact polynomial division by it.
Nonconstancy is expressed by positive natural degree, excluding zero.
All roots in these statements are real. No splitting or closedness
hypothesis is used.
-/

namespace Specs.D07.Ch19.SturmChainSquarefreeReduction

open Polynomial
open scoped Classical

/-- The specified divisor really is a monic greatest common divisor. -/
def MonicGcdSpecification : Prop :=
  ∀ f : Polynomial ℝ, 0 < f.natDegree →
    let d := gcd f f.derivative
    d.Monic ∧ d ∣ f ∧ d ∣ f.derivative ∧
      ∀ q : Polynomial ℝ, q ∣ f → q ∣ f.derivative → q ∣ d

def ReductionNonconstant : Prop :=
  ∀ f : Polynomial ℝ, 0 < f.natDegree →
    0 < (f / gcd f f.derivative).natDegree

def ReductionRoots : Prop :=
  ∀ f : Polynomial ℝ, 0 < f.natDegree → ∀ a : ℝ,
    (f / gcd f f.derivative).eval a = 0 ↔ f.eval a = 0

def ReductionSquarefree : Prop :=
  ∀ f : Polynomial ℝ, 0 < f.natDegree →
    Squarefree (f / gcd f f.derivative)

/-- Explicit irreducible-factor interpretation of squarefreeness. -/
def ReductionNoRepeatedIrreducible : Prop :=
  ∀ f : Polynomial ℝ, 0 < f.natDegree → ∀ p : Polynomial ℝ,
    Irreducible p → ¬ p ^ 2 ∣ f / gcd f f.derivative

def ReductionGcdOne : Prop :=
  ∀ f : Polynomial ℝ, 0 < f.natDegree →
    gcd (f / gcd f f.derivative) (f / gcd f f.derivative).derivative = 1

/-- Every real root is retained once, regardless of its multiplicity in f. -/
def ReductionMultiplicity : Prop :=
  ∀ f : Polynomial ℝ, 0 < f.natDegree → ∀ a : ℝ,
    (f / gcd f f.derivative).rootMultiplicity a = if f.eval a = 0 then 1 else 0

/-- The source statement for any chosen monic gcd, with its full universal
property as hypotheses. No special representative beyond monicity is required. -/
def ReductionForMonicGcd : Prop :=
  ∀ (f : Polynomial ℝ), 0 < f.natDegree → ∀ d : Polynomial ℝ,
    d.Monic → d ∣ f → d ∣ f.derivative →
    (∀ q : Polynomial ℝ, q ∣ f → q ∣ f.derivative → q ∣ d) →
    let s := f / d
    d * s = f ∧ 0 < s.natDegree ∧
      (∀ a : ℝ, s.eval a = 0 ↔ f.eval a = 0) ∧
      Squarefree s ∧ (∀ p : Polynomial ℝ, Irreducible p → ¬ p ^ 2 ∣ s) ∧
      gcd s s.derivative = 1 ∧
      ∀ a : ℝ, s.rootMultiplicity a = if f.eval a = 0 then 1 else 0

end Specs.D07.Ch19.SturmChainSquarefreeReduction
