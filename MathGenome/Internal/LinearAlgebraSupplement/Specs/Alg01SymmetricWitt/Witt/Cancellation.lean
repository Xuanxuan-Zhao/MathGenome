import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.LinearAlgebra.QuadraticForm.Radical

namespace Specs.Alg01SymmetricWitt.Witt.Cancellation

universe u v w x y

/-- Witt cancellation of a common nondegenerate orthogonal summand. -/
def cancel : Prop :=
  ∀ {k : Type u} {U : Type v} {V : Type w} {W : Type x}
    [Field k] [Invertible (2 : k)]
    [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (qU : QuadraticForm k U) (qV : QuadraticForm k V) (qW : QuadraticForm k W),
    qU.Nondegenerate → qV.Nondegenerate → qW.Nondegenerate →
      (qU.prod qW).Equivalent (qV.prod qW) → qU.Equivalent qV

/-- Witt cancellation of two isometric nondegenerate orthogonal summands. -/
def cancelEquivalent : Prop :=
  ∀ {k : Type u} {U : Type v} {V : Type w} {W : Type x} {W' : Type y}
    [Field k] [Invertible (2 : k)]
    [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [AddCommGroup W'] [Module k W'] [FiniteDimensional k W']
    (qU : QuadraticForm k U) (qV : QuadraticForm k V)
    (qW : QuadraticForm k W) (qW' : QuadraticForm k W'),
    qU.Nondegenerate → qV.Nondegenerate → qW.Nondegenerate → qW'.Nondegenerate →
      qW.Equivalent qW' → (qU.prod qW).Equivalent (qV.prod qW') → qU.Equivalent qV

end Specs.Alg01SymmetricWitt.Witt.Cancellation
