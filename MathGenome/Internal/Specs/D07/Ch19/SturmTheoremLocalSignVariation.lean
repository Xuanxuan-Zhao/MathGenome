import MathGenome.Internal.Specs.D07.Ch19.SturmChain
import Mathlib.Data.List.SignVariations
import Mathlib.Topology.Instances.Real.Lemmas

/-! Local part of Sturm's theorem, paper.tex:5609–5658.
The list is arbitrary: it is not required to be definitionally the library's
Euclidean sequence. Zero entries at evaluation are deleted by `signVariations`.
-/
noncomputable section
namespace Specs.D07.Ch19.SturmTheoremLocalSignVariation
open Polynomial Filter
open scoped Topology

abbrev Poly := Polynomial ℝ

def variation (L : List Poly) (x : ℝ) : ℕ :=
  (L.map (fun p => p.eval x)).signVariations

def chainZeros (L : List Poly) : Set ℝ :=
  {x | ∃ p ∈ L, p.eval x = 0}

/-- The source's finite squarefree Sturm chain, including its stopping rule.
The final member is a nonzero constant; consecutive members have no common zero.
-/
def IsSturmChain (s : Poly) (L : List Poly) : Prop :=
  0 < s.natDegree ∧ Squarefree s ∧
  (∃ tail, L = s :: s.derivative :: tail) ∧
  (∀ p ∈ L, p ≠ 0) ∧ SturmChain.DivisionLaws L ∧
  (∃ a : ℝ, a ≠ 0 ∧ L.getLast? = some (C a)) ∧
  L.IsChain (fun p q => ∀ c : ℝ, ¬ (p.eval c = 0 ∧ q.eval c = 0))

def CanonicalChain : Prop :=
  ∀ s : Poly, 0 < s.natDegree → Squarefree s → gcd s s.derivative = 1 →
    IsSturmChain s (sturmSeq s s.derivative)

def FiniteChainZeros : Prop :=
  ∀ s L, IsSturmChain s L → (chainZeros L).Finite

def SignsLocallyConstant : Prop :=
  ∀ s L, IsSturmChain s L → ∀ c, c ∉ chainZeros L →
    ∀ᶠ x in 𝓝 c, ∀ p ∈ L, SignType.sign (p.eval x) = SignType.sign (p.eval c)

def SignsConstantOnInterval : Prop :=
  ∀ s L, IsSturmChain s L → ∀ a b : ℝ,
    (∀ x ∈ Set.uIcc a b, x ∉ chainZeros L) →
    ∀ p ∈ L, SignType.sign (p.eval a) = SignType.sign (p.eval b)

/-- Each internal zero has opposite nonzero neighbors. Throughout a whole
neighborhood, the two edges across this triple contribute exactly one change,
even where the middle value vanishes and is deleted. -/
def InternalZeroCancellation : Prop :=
  ∀ s L, IsSturmChain s L → ∀ pre p q r post c,
    L = pre ++ p :: q :: r :: post → q.eval c = 0 →
    p.eval c ≠ 0 ∧ r.eval c ≠ 0 ∧ p.eval c = -r.eval c ∧
    (∀ᶠ x in 𝓝 c,
      SignType.sign (p.eval x) = -SignType.sign (r.eval x) ∧
      variation [p, q, r] x = 1)

/-- All internal zeros in a suffix cancel simultaneously, provided its first
member is nonzero at c. No restriction on the number of vanishing members is
imposed, so this includes simultaneous nonadjacent internal zeros. -/
def TailLocalConstancy : Prop :=
  ∀ s L, IsSturmChain s L → ∀ pre p tail c,
    L = pre ++ p :: tail → p.eval c ≠ 0 →
    ∀ᶠ x in 𝓝 c, variation (p :: tail) x = variation (p :: tail) c

def NonrootLocalConstancy : Prop :=
  ∀ s L, IsSturmChain s L → ∀ c, s.eval c ≠ 0 →
    ∀ᶠ x in 𝓝 c, variation L x = variation L c

/-- At a simple root the deleted-zero value is the right-hand value; the
left-hand value is larger by one. These are eventual one-sided equalities,
not assertions merely about selected sequences approaching c. -/
def RootJump : Prop :=
  ∀ s L, IsSturmChain s L → ∀ c, s.eval c = 0 →
    (∀ᶠ x in 𝓝[<] c, variation L x = variation L c + 1) ∧
    (∀ᶠ x in 𝓝[>] c, variation L x = variation L c)

end Specs.D07.Ch19.SturmTheoremLocalSignVariation
