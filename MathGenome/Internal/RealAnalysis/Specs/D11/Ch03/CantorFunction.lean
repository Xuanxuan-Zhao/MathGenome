import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.CantorSet
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Order.IntermediateValue

/-! The canonical digit construction for paper.tex:1090–1114.
Digits are indexed from zero, so digit `n` has weight `b ^ (-(n+1))`.
The supremum includes zero, giving the constant zero extension below [0,1]. -/
noncomputable section
open Set

namespace D11.Ch03.CantorStaircase

def ternary (a : ℕ → Bool) : ℝ :=
  Real.ofDigits (fun n => cond (a n) (2 : Fin 3) 0)

def binary (a : ℕ → Bool) : ℝ :=
  Real.ofDigits (fun n => cond (a n) (1 : Fin 2) 0)

/-- Values of the digit map at Cantor points to the left of `x`, with zero adjoined. -/
def lowerValues (x : ℝ) : Set ℝ := {0} ∪ binary '' {a | ternary a ≤ x}

/-- The monotone, constant-on-gaps extension of the binary digit map. -/
def staircase (x : ℝ) : ℝ := sSup (lowerValues x)

end D11.Ch03.CantorStaircase

namespace Specs.D11.Ch03.CantorFunction
open _root_.D11.Ch03.CantorStaircase

abbrev Gamma_type := ℝ → ℝ
def Gamma_value : Gamma_type := staircase

def maps_unit_interval : Prop := MapsTo Gamma_value (Icc 0 1) (Icc 0 1)
def monotone : Prop := Monotone Gamma_value
def continuous : Prop := ContinuousOn Gamma_value (Icc 0 1)
def endpoints : Prop := Gamma_value 0 = 0 ∧ Gamma_value 1 = 1

def surjective : Prop := SurjOn Gamma_value (Icc 0 1) (Icc 0 1)

/-- Surjectivity already holds on the fixed middle-thirds Cantor set. -/
def cantor_surjective : Prop := SurjOn Gamma_value
  Specs.D11.Ch03.CantorSet.C_value (Icc 0 1)

def digit_formula : Prop := ∀ a : ℕ → Bool,
  Gamma_value (∑' n, (if a n then (2 : ℝ) else 0) / 3 ^ (n + 1)) =
    ∑' n, (if a n then (1 : ℝ) else 0) / 2 ^ (n + 1)

/-- This states constancy on every connected component, including all gaps. -/
def constant_on_components : Prop := ∀ x ∈ Icc (0 : ℝ) 1 \ Specs.D11.Ch03.CantorSet.C_value,
  ∀ y ∈ connectedComponentIn (Icc (0 : ℝ) 1 \ Specs.D11.Ch03.CantorSet.C_value) x,
    Gamma_value y = Gamma_value x

/-- The endpoint value is the constant interpolated value on each deleted interval. -/
def constant_on_gap_closure : Prop := ∀ a b : ℝ,
  a ∈ Specs.D11.Ch03.CantorSet.C_value → b ∈ Specs.D11.Ch03.CantorSet.C_value →
  a < b → Disjoint (Ioo a b) Specs.D11.Ch03.CantorSet.C_value →
  ∀ x ∈ Icc a b, Gamma_value x = Gamma_value a

end Specs.D11.Ch03.CantorFunction
