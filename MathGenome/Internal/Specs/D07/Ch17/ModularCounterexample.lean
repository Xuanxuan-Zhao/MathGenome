import MathGenome.Internal.Specs.D07.Ch17.SubrepresentationsQuotients
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Independent specification of paper.tex:4863–4883.
The coordinates are the source's ordered basis e₁,e₂. The group Cₚ is
Multiplicative (ZMod p), so its identity is the additive residue zero.
All results include p = 2. No semisimplicity premise is assumed. -/
namespace Specs.D07.Ch17.ModularCounterexample

open scoped Matrix

abbrev Space (p : ℕ) := Fin 2 → ZMod p
abbrev Cyclic (p : ℕ) := Multiplicative (ZMod p)

def e₁ (p : ℕ) : Space p := ![1, 0]
def e₂ (p : ℕ) : Space p := ![0, 1]

def nilpotentValue (p : ℕ) : Module.End (ZMod p) (Space p) :=
  Matrix.toLin' !![0, 1; 0, 0]

def jordanValue (p : ℕ) : Module.End (ZMod p) (Space p) :=
  1 + nilpotentValue p

/-- The actual line Ke₁, rather than just an unspecified invariant subspace. -/
def lineValue (p : ℕ) : Submodule (ZMod p) (Space p) :=
  Submodule.span (ZMod p) {e₁ p}

/-- Explicit residue action. Its homomorphism laws are the elementary shear
identities; the substantive conclusions below are separate propositions. -/
def actionValue (p : ℕ) : Representation (ZMod p) (Cyclic p) (Space p) where
  toFun g := 1 + g.toAdd • nilpotentValue p
  map_one' := by
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    funext i
    fin_cases i <;>
      simp [nilpotentValue, Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_two,
        Module.End.mul_apply] <;> ring

abbrev Invariant (p : ℕ) [Fact p.Prime] (W : Submodule (ZMod p) (Space p)) : Prop :=
  Specs.D07.Ch17.SubrepresentationsQuotients.invariantValue
    (ZMod p) (Cyclic p) (Space p) (actionValue p) W

def MatrixIdentification : Prop :=
  ∀ p : ℕ, LinearMap.toMatrix' (nilpotentValue p) = !![0, 1; 0, 0] ∧
    LinearMap.toMatrix' (jordanValue p) = !![1, 1; 0, 1]

def NilpotentSquare : Prop :=
  ∀ p : ℕ, nilpotentValue p ^ 2 = 0

def JordanPowers : Prop :=
  ∀ (p : ℕ) (a : ℕ),
    jordanValue p ^ a = 1 + (a : ZMod p) • nilpotentValue p

def JordanPrimePower : Prop :=
  ∀ p : ℕ, jordanValue p ^ p = 1

def ActionFormula : Prop :=
  ∀ (p : ℕ) (g : Cyclic p) (v : Space p),
    actionValue p g v = ![v 0 + g.toAdd * v 1, v 1]

def GeneratorAndIntegerPowers : Prop :=
  ∀ p : ℕ, actionValue p (Multiplicative.ofAdd (1 : ZMod p)) = jordanValue p ∧
    (∀ k : ℤ,
      (actionValue p).toHomUnits (Multiplicative.ofAdd (k : ZMod p)) =
        ((actionValue p).toHomUnits (Multiplicative.ofAdd (1 : ZMod p))) ^ k) ∧
    (∀ k m : ℤ,
      ((actionValue p).toHomUnits (Multiplicative.ofAdd (1 : ZMod p))) ^
        (k + m * (p : ℤ)) =
      ((actionValue p).toHomUnits (Multiplicative.ofAdd (1 : ZMod p))) ^ k)

def InvariantFixedLine : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    Module.finrank (ZMod p) (Space p) = 2 ∧
    Module.finrank (ZMod p) (lineValue p) = 1 ∧
    lineValue p ≠ ⊥ ∧ lineValue p ≠ ⊤ ∧ Invariant p (lineValue p) ∧
    ∀ g v, v ∈ lineValue p → actionValue p g v = v

/-- A slightly stronger classification also records the zero and full spaces. -/
def InvariantSubspaces : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : Submodule (ZMod p) (Space p)),
    Invariant p W ↔ W = ⊥ ∨ W = lineValue p ∨ W = ⊤

def UniqueInvariantLine : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : Submodule (ZMod p) (Space p)),
    (Invariant p W ∧ Module.finrank (ZMod p) W = 1) ↔ W = lineValue p

def NoInvariantComplement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : Submodule (ZMod p) (Space p)),
    Invariant p W → ¬ IsCompl (lineValue p) W

/-- Reducibility is witnessed by Ke₁; indecomposability rules out every
internal sum of two nonzero invariant summands, not only two chosen lines. -/
def ReducibleIndecomposable : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    (∃ U : Submodule (ZMod p) (Space p), Invariant p U ∧ U ≠ ⊥ ∧ U ≠ ⊤) ∧
    ¬ ∃ A B : Submodule (ZMod p) (Space p),
      Invariant p A ∧ Invariant p B ∧ A ≠ ⊥ ∧ B ≠ ⊥ ∧ IsCompl A B

end Specs.D07.Ch17.ModularCounterexample
