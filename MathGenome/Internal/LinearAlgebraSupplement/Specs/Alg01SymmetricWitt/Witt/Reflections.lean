import Mathlib.LinearAlgebra.QuadraticForm.Radical

namespace Specs.Alg01SymmetricWitt.Witt.Reflections

universe u v

variable {k : Type u} {V : Type v} [Field k] [Invertible (2 : k)]
  [AddCommGroup V] [Module k V]

/-- The reflection formula, using the normalized associated bilinear form. -/
def reflectionFormula (q : QuadraticForm k V) (w x : V) : V :=
  x - (2 * q.associated x w / q w) • w

/-- An isometry is a reflection if it has the stated formula for a vector of nonzero value. -/
def IsReflection (q : QuadraticForm k V) (s : q.IsometryEquiv q) : Prop :=
  ∃ w : V, q w ≠ 0 ∧ ∀ x, s x = reflectionFormula q w x

def reflectionIsometry : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [Invertible (2 : k)]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (q : QuadraticForm k V), q.Nondegenerate →
    ∀ w : V, q w ≠ 0 →
    ∃ s : q.IsometryEquiv q, (∀ x, s x = reflectionFormula q w x) ∧ Function.Involutive s

def moveByReflections : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [Invertible (2 : k)]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (q : QuadraticForm k V), q.Nondegenerate →
    ∀ (x y : V) {a : k}, q x = a → q y = a → a ≠ 0 →
    ∃ e : q.IsometryEquiv q, e x = y ∧
      (e = QuadraticMap.IsometryEquiv.refl q ∨ IsReflection q e ∨
        ∃ s t : q.IsometryEquiv q, IsReflection q s ∧ IsReflection q t ∧ e = s.trans t)

end Specs.Alg01SymmetricWitt.Witt.Reflections
