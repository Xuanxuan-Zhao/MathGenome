import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.WeakNullstellensatz
import Mathlib.RingTheory.Jacobson.Ring

/-!
The weak Nullstellensatz over arbitrary fields. Mathlib's Zariski lemma
applies because fields are Jacobson rings. The quotient by a maximal ideal
is a field and inherits finite type from the original algebra.
-/
namespace P103.Ch06.WeakNullstellensatz

open P103.Specs.Ch06.WeakNullstellensatz

universe u v

theorem finite_type_field : finite_type_fieldType.{u,v} := by
  intro k K _ _ _ _
  exact finite_of_finite_type_of_isJacobsonRing k K

theorem maximal_quotient_finite : maximal_quotient_finiteType.{u,v} := by
  intro k A _ _ _ _ m hm
  let : m.IsMaximal := hm
  let := Ideal.Quotient.field m
  exact finite_type_field k (A ⧸ m)

end P103.Ch06.WeakNullstellensatz
