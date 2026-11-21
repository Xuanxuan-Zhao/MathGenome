import MathGenome.Internal.Specs.D07.Ch20.TraceNormTowers
import Mathlib.RingTheory.Norm.Transitivity

/-!
Trace and norm transitivity for arbitrary finite field towers.
The library trace theorem uses the product-basis block trace calculation.
The norm theorem uses the restriction-of-scalars determinant identity.
Both apply to the multiplication-operator definitions without separability.
-/

universe u v w

namespace D07.Ch20.TraceNormTowers

theorem trace_tower : Specs.D07.Ch20.TraceNormTowers.TraceTower.{u, v, w} := by
  intro K M L _ _ _ _ _ _ _ _ _ a
  exact (Algebra.trace_trace (R := K) (S := M) (T := L) a).symm

theorem norm_tower : Specs.D07.Ch20.TraceNormTowers.NormTower.{u, v, w} := by
  intro K M L _ _ _ _ _ _ _ _ _ a
  exact (Algebra.norm_norm (R := K) (S := M) (a := a)).symm

end D07.Ch20.TraceNormTowers
