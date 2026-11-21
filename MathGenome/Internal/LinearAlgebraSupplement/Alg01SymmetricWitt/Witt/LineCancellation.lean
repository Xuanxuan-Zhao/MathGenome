import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Witt.Reflections
import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Witt.LineCancellation

namespace Alg01SymmetricWitt.Witt.LineCancellation

open QuadraticMap

universe u v w

variable {k : Type u} {U : Type v} {V : Type w} [Field k]
  [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]

private abbrev lineForm (a : k) : QuadraticForm k k :=
  a • (QuadraticMap.sq (R := k) : QuadraticForm k k)

private theorem generator_value (q : QuadraticForm k U) (a : k) :
    (q.prod (lineForm a)) (0, 1) = a := by
  change q 0 + a * (1 * 1) = a
  simp

variable [Invertible (2 : k)]

private theorem associated_prod_apply (qU : QuadraticForm k U) (qV : QuadraticForm k V)
    (x y : U × V) : (qU.prod qV).associated x y =
      qU.associated x.1 y.1 + qV.associated x.2 y.2 := by
  simp only [associated_prod, LinearMap.add_apply, LinearMap.compl₁₂_apply,
    LinearMap.fst_apply, LinearMap.snd_apply]

/-- The orthogonal sum of two nondegenerate forms is nondegenerate. -/
theorem nondegenerate_prod {qU : QuadraticForm k U} {qV : QuadraticForm k V}
    (hU : qU.Nondegenerate) (hV : qV.Nondegenerate) : (qU.prod qV).Nondegenerate := by
  apply (Coordinates.nondegenerate_iff_associated_separatingLeft _).2
  intro x hx
  apply Prod.ext
  · apply (Coordinates.nondegenerate_iff_associated_separatingLeft _).1 hU
    intro y
    simpa only [associated_prod_apply, map_zero, add_zero] using hx (y, 0)
  · apply (Coordinates.nondegenerate_iff_associated_separatingLeft _).1 hV
    intro y
    simpa only [associated_prod_apply, map_zero, zero_add] using hx (0, y)

private theorem associated_line (a x y : k) : (lineForm a).associated x y = a * (x * y) := by
  rw [lineForm, map_smul, associated_sq]
  rfl

private theorem nondegenerate_line {a : k} (ha : a ≠ 0) : (lineForm a).Nondegenerate := by
  apply (Coordinates.nondegenerate_iff_associated_separatingLeft _).2
  intro x hx
  have h : a * x = 0 := by simpa only [associated_line, mul_one] using hx 1
  exact (mul_eq_zero.mp h).resolve_left ha

private theorem second_eq_zero_of_fixes_generator {qU : QuadraticForm k U}
    {qV : QuadraticForm k V} {a : k} (ha : a ≠ 0)
    (e : (qU.prod (lineForm a)).IsometryEquiv (qV.prod (lineForm a)))
    (he : e (0, 1) = (0, 1)) (x : U) : (e (x, 0)).2 = 0 := by
  have h := (Coordinates.preservesQuadraticIffBilinear _ _ e.toLinearEquiv).mp e.map_app
    (x, 0) (0, 1)
  simp only [IsometryEquiv.coe_toLinearEquiv, he, associated_prod_apply, map_zero,
    associated_line, mul_one, zero_add] at h
  exact (mul_eq_zero.mp h).resolve_left ha

/-- Cancels a line of nonzero value by aligning its generator and restricting to its complement. -/
theorem cancelLine [FiniteDimensional k U] [FiniteDimensional k V]
    (qU : QuadraticForm k U) (qV : QuadraticForm k V)
    (_hU : qU.Nondegenerate) (hV : qV.Nondegenerate) {a : k} (ha : a ≠ 0)
    (e : (qU.prod (a • (QuadraticMap.sq : QuadraticForm k k))).IsometryEquiv
      (qV.prod (a • (QuadraticMap.sq : QuadraticForm k k)))) :
    qU.Equivalent qV := by
  obtain ⟨s, hs, _⟩ := Reflections.moveByReflections (qV.prod (lineForm a))
    (nondegenerate_prod hV (nondegenerate_line ha)) (e (0, 1)) (0, 1)
    ((e.map_app _).trans (generator_value qU a)) (generator_value qV a) ha
  let g := e.trans s
  have hg : g (0, 1) = (0, 1) := hs
  have hg_inv : g.symm (0, 1) = (0, 1) := (g.symm_apply_eq).2 hg.symm
  have forward_pair (x : U) : ((g (x, 0)).1, 0) = g (x, 0) :=
    Prod.ext rfl (second_eq_zero_of_fixes_generator ha g hg x).symm
  have inverse_pair (y : V) : ((g.symm (y, 0)).1, 0) = g.symm (y, 0) :=
    Prod.ext rfl (second_eq_zero_of_fixes_generator ha g.symm hg_inv y).symm
  let forward := (LinearMap.fst k V k).comp (g.toLinearMap.comp (LinearMap.inl k U k))
  let inverse := (LinearMap.fst k U k).comp (g.symm.toLinearMap.comp (LinearMap.inl k V k))
  refine ⟨{ toLinearEquiv := ?_, map_app' := ?_ }⟩
  · refine { forward with invFun := inverse, left_inv := ?_, right_inv := ?_ }
    · intro x
      change (g.symm ((g (x, 0)).1, 0)).1 = x
      rw [forward_pair, g.symm_apply_apply]
    · intro y
      change (g ((g.symm (y, 0)).1, 0)).1 = y
      rw [inverse_pair, g.apply_symm_apply]
  · intro x
    change qV (g (x, 0)).1 = qU x
    have h := g.map_app (x, 0)
    rw [← forward_pair x] at h
    simpa only [prod_apply, map_zero, add_zero] using h

end Alg01SymmetricWitt.Witt.LineCancellation
