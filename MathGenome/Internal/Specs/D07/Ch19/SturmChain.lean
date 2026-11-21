import MathGenome.Internal.Specs.D07.Ch19.SturmChainSquarefreeReduction
import Mathlib.Algebra.Polynomial.Sturm.Sequence
import Mathlib.Data.List.Chain

/-!
K07.19.sturm_chain, paper.tex:5581–5610. Lists are finite and use the
canonical signed Euclidean sequence, with no zero polynomial appended.
`DivisionLaws` records both the negative remainder recurrence and the
reconstruction identity, and requires a zero remainder at the last pair.
-/

namespace Specs.D07.Ch19.SturmChain

open Polynomial
open scoped Classical

/-- Division identities for every consecutive triple, and zero remainder
at the terminal pair. The empty and singleton cases have no pair to test. -/
def DivisionLaws {K : Type*} [Field K] : List (Polynomial K) → Prop
  | [] => True
  | [_] => True
  | [p, q] => p % q = 0
  | p :: q :: r :: rest =>
      r = -(p % q) ∧ p = (p / q) * q - r ∧ DivisionLaws (q :: r :: rest)

/-- Complete algebraic properties of the Sturm chain of s. -/
def ChainProperties (s : Polynomial ℝ) : Prop :=
  let L := sturmSeq s s.derivative
  (∃ tail, L = s :: s.derivative :: tail) ∧
  (∀ p ∈ L, p ≠ 0) ∧
  DivisionLaws L ∧
  L.IsChain (fun p q => q.degree < p.degree) ∧
  L.IsChain IsCoprime ∧
  (∃ c : ℝ, c ≠ 0 ∧ L.getLast? = some (C c)) ∧
  L.IsChain (fun p q => ∀ a : ℝ, ¬ (p.eval a = 0 ∧ q.eval a = 0))

def SignedDivisionIdentities : Prop :=
  ∀ p q : Polynomial ℝ, DivisionLaws (sturmSeq p q)

/-- Normalized gcds are unchanged by a signed Euclidean step. -/
def GcdInvariant : Prop :=
  ∀ p q : Polynomial ℝ, gcd q (-(p % q)) = gcd p q

def ChainOfCoprimeDerivative : Prop :=
  ∀ s : Polynomial ℝ, 0 < s.natDegree → gcd s s.derivative = 1 →
    ChainProperties s

/-- The source theorem with an arbitrary chosen monic greatest common divisor.
Its universal property is data about d, not an assumption about the chain. -/
def SturmChainForMonicGcd : Prop :=
  ∀ f : Polynomial ℝ, 0 < f.natDegree → ∀ d : Polynomial ℝ,
    d.Monic → d ∣ f → d ∣ f.derivative →
    (∀ q : Polynomial ℝ, q ∣ f → q ∣ f.derivative → q ∣ d) →
    let s := f / d
    d * s = f ∧ 0 < s.natDegree ∧
    (∀ a : ℝ, s.eval a = 0 ↔ f.eval a = 0) ∧
    Squarefree s ∧ gcd s s.derivative = 1 ∧
    (∀ a : ℝ, s.rootMultiplicity a = if f.eval a = 0 then 1 else 0) ∧
    ChainProperties s

end Specs.D07.Ch19.SturmChain
