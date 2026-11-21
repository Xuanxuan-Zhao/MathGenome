import MathGenome.Internal.Specs.D07.Ch12.MinpolyDivisibility
import Mathlib.FieldTheory.Minpoly.Field

/-!
# Minimal polynomial divisibility and the evaluation kernel

K07.12.minpoly_divisibility, paper.tex:3591–3597.

Over a field, division by the monic minimal polynomial leaves a remainder
of smaller degree. If the dividend vanishes at α, so does that remainder;
minimality forces it to be zero. Mathlib's `minpoly.dvd_iff` proves this
criterion (including the converse by multiplicativity of evaluation).
Ideal extensionality then identifies the kernel with the principal ideal.
-/

universe u v

namespace D07.Ch12.MinpolyDivisibility

open Specs.D07.Ch12.MinpolyDivisibility

theorem evaluationZeroIffDivisible : EvaluationZeroIffDivisible.{u, v} := by
  intro K L _ _ _ α _ f
  exact minpoly.dvd_iff.symm

theorem evaluationKernel : EvaluationKernel.{u, v} := by
  intro K L _ _ _ α hα
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  exact evaluationZeroIffDivisible K L α hα f

end D07.Ch12.MinpolyDivisibility
