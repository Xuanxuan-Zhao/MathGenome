import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.OrderOfElement

/-!
Independent specification for K07.13.explicit_F4, paper.tex:4033–4045.
The objects here are the actual polynomial quotient over the two-element
prime field, with its canonical algebra map. No unrelated four-element model
or unspecified identification with an algebraic closure is used.
-/

noncomputable section

namespace Specs.D07.Ch13.ExplicitF4
open Polynomial

/-- The defining polynomial over the prime field. -/
def modulus : Polynomial (ZMod 2) := X ^ 2 + X + 1

/-- The canonical quotient F₂[X]/(X²+X+1), with its inherited ring operations. -/
abbrev F4 := AdjoinRoot modulus

/-- The residue class of X. -/
def u : F4 := AdjoinRoot.root modulus

/-- Coordinates in the ordered basis (1,u); their arithmetic is in ZMod 2. -/
def coord (ab : ZMod 2 × ZMod 2) : F4 :=
  algebraMap (ZMod 2) F4 ab.1 + algebraMap (ZMod 2) F4 ab.2 * u

def ModulusType := Polynomial (ZMod 2)
def FieldType := Type
def GeneratorType := F4

def EvaluationValues : Prop := ∀ a : ZMod 2, modulus.eval a = 1

def MonicDegree : Prop := modulus.Monic ∧ modulus.natDegree = 2

def Irreducibility : Prop := Irreducible modulus

def FieldCardinality : Prop := IsField F4 ∧ Finite F4 ∧ Nat.card F4 = 4

/-- Both existence and uniqueness of all two-term coordinates. -/
def UniqueCoordinates : Prop := Function.Bijective coord

def Enumeration : Prop := ∀ x : F4, x = 0 ∨ x = 1 ∨ x = u ∨ x = u + 1

/-- The displayed four elements are pairwise distinct. -/
def Distinctness : Prop := List.Pairwise (· ≠ ·) ([0, 1, u, u + 1] : List F4)

def ArithmeticIdentities : Prop :=
  u ^ 2 = u + 1 ∧ u * (u + 1) = 1 ∧ (u + 1) ^ 2 = u

def CoordinateAddition : Prop := ∀ a b c d : ZMod 2,
  coord (a, b) + coord (c, d) = coord (a + c, b + d)

/-- Expansion followed by the relation u²=u+1 determines every product. -/
def CoordinateMultiplication : Prop := ∀ a b c d : ZMod 2,
  coord (a, b) * coord (c, d) = coord (a * c + b * d, a * d + b * c + b * d)

/-- The nonzero elements are exactly 1,u,u² and u has order three. -/
def MultiplicativeGenerator : Prop :=
  u ^ 3 = 1 ∧ orderOf u = 3 ∧
    ∀ x : F4, x ≠ 0 ↔ ∃ i : Fin 3, x = u ^ (i : ℕ)

end Specs.D07.Ch13.ExplicitF4
