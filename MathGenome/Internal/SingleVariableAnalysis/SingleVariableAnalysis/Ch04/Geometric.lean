import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Peano
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Geometric

/-!
# Tangents and instantaneous velocities

K03.04.geometric (paper.tex:783–793). The affine approximation follows from
the first-order Peano equivalence. Conversely any slope with little-o error
is a derivative, so uniqueness of derivatives forces the same slope. This
also proves uniqueness of the entire affine function through the base value.
For interval domains, interiority supplies all sufficiently small increments;
we retain the domain in the error filter and compare functions only on I.
The velocity conclusions express the same derivative using displacement
and elapsed real time, including for complex-valued paths.
-/

namespace SingleVariableAnalysis

open Filter
open scoped Topology
universe u

section RealNormedTarget
variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem affine_tangent_iff (f : ℝ → F) (L : F) (a : ℝ)
    (hd : HasRealIncrementDerivative f L a) (v : F) :
    Asymptotics.IsLittleO (𝓝[≠] (0 : ℝ))
      (fun h => f (a + h) - (f a + (a + h - a) • v)) (fun h : ℝ => h) ↔ v = L := by
  have heq : (fun h => f (a + h) - (f a + (a + h - a) • v)) =
      (fun h => f (a + h) - f a - h • v) := by
    funext h
    rw [add_sub_cancel_left, sub_add_eq_sub_sub]
  rw [heq, ← derivative_iff_remainder_littleO]
  constructor
  · intro hv
    exact ((hasRealIncrementDerivative_iff_hasDerivAt f v a).mp hv).unique
      ((hasRealIncrementDerivative_iff_hasDerivAt f L a).mp hd)
  · rintro rfl
    exact hd

theorem tangent_unique (f : ℝ → F) (a : ℝ) (hd : DifferentiableAt ℝ f a) :
    let l : ℝ → F := fun x => f a + (x - a) • deriv f a
    l a = f a ∧
    Asymptotics.IsLittleO (𝓝[≠] (0 : ℝ))
      (fun h => f (a + h) - l (a + h)) (fun h : ℝ => h) ∧
    ∀ m : ℝ → F, (∃ v : F, ∀ x : ℝ, m x = f a + (x - a) • v) →
      Asymptotics.IsLittleO (𝓝[≠] (0 : ℝ))
        (fun h => f (a + h) - m (a + h)) (fun h : ℝ => h) → m = l := by
  have hd' := (hasRealIncrementDerivative_iff_hasDerivAt f (deriv f a) a).mpr hd.hasDerivAt
  refine ⟨by simp, (affine_tangent_iff f (deriv f a) a hd' _).mpr rfl, ?_⟩
  rintro m ⟨v, hm⟩ herr
  have hv : v = deriv f a := (affine_tangent_iff f (deriv f a) a hd' v).mp
    (by simpa only [hm] using herr)
  funext x
  exact (hm x).trans (by rw [hv])

/-- At an interior point the restriction on increments is a neighborhood of
zero. Removing zero therefore gives the ordinary punctured neighborhood. -/
private theorem interior_increment_filter (I : Set ℝ) (a : ℝ) (ha : a ∈ interior I) :
    𝓝[{h : ℝ | a + h ∈ I} \ {0}] (0 : ℝ) = 𝓝[≠] (0 : ℝ) := by
  have hI : {h : ℝ | a + h ∈ I} ∈ 𝓝 (0 : ℝ) := by
    have hc : ContinuousAt (fun h : ℝ => a + h) 0 := continuousAt_const.add continuousAt_id
    exact hc (by simpa only [add_zero] using mem_interior_iff_mem_nhds.mp ha)
  rw [Set.sdiff_eq, nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds hI)]

theorem within_affine_tangent_iff (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ)
    (ha : a ∈ interior I) (hd : HasRealIncrementDerivativeWithin f L I a) (v : F) :
    Asymptotics.IsLittleO (𝓝[{h : ℝ | a + h ∈ I} \ {0}] (0 : ℝ))
      (fun h => f (a + h) - (f a + (a + h - a) • v)) (fun h : ℝ => h) ↔ v = L := by
  rw [interior_increment_filter I a ha]
  exact affine_tangent_iff f L a
    ((hasRealIncrementDerivative_iff_hasDerivAt f L a).mpr
      ((withinDerivative_interior_iff f L I a ha).mp hd)) v

theorem within_tangent_unique (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ)
    (ha : a ∈ interior I) (hd : HasRealIncrementDerivativeWithin f L I a) :
    let l : ℝ → F := fun x => f a + (x - a) • L
    l a = f a ∧
    Asymptotics.IsLittleO (𝓝[{h : ℝ | a + h ∈ I} \ {0}] (0 : ℝ))
      (fun h => f (a + h) - l (a + h)) (fun h : ℝ => h) ∧
    ∀ m : ℝ → F, (∃ v : F, ∀ x ∈ I, m x = f a + (x - a) • v) →
      Asymptotics.IsLittleO (𝓝[{h : ℝ | a + h ∈ I} \ {0}] (0 : ℝ))
        (fun h => f (a + h) - m (a + h)) (fun h : ℝ => h) → Set.EqOn m l I := by
  refine ⟨by simp, (within_affine_tangent_iff f L I a ha hd L).mpr rfl, ?_⟩
  rintro m ⟨v, hm⟩ herr
  have heq : (fun h => f (a + h) - m (a + h)) =ᶠ[
      𝓝[{h : ℝ | a + h ∈ I} \ {0}] (0 : ℝ)]
      (fun h => f (a + h) - (f a + (a + h - a) • v)) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [hm (a + h) hh.1]
  have hv := (within_affine_tangent_iff f L I a ha hd v).mp
    (herr.congr' heq Filter.EventuallyEq.rfl)
  intro x hx
  exact (hm x hx).trans (by rw [hv])

theorem instantaneous_velocity_iff (f : ℝ → F) (v : F) (t : ℝ) :
    HasRealIncrementDerivative f v t ↔
      Tendsto (fun h : ℝ => h⁻¹ • (f (t + h) - f t)) (𝓝[≠] (0 : ℝ)) (𝓝 v) := by
  rw [hasRealIncrementDerivative_iff_hasDerivAt, hasDerivAt_iff_tendsto_slope_zero]

theorem within_instantaneous_velocity_iff (f : ℝ → F) (v : F) (I : Set ℝ) (t : ℝ) :
    HasRealIncrementDerivativeWithin f v I t ↔
      Tendsto (fun h : ℝ => h⁻¹ • (f (t + h) - f t))
        (𝓝[{h : ℝ | t + h ∈ I} \ {0}] (0 : ℝ)) (𝓝 v) := by
  exact relativePuncturedLimit_filter_iff _ _ _ _

end RealNormedTarget

theorem real_affine_tangent_iff (f : ℝ → ℝ) (L a : ℝ)
    (hd : HasRealIncrementDerivative f L a) (v : ℝ) :
    ScalarLittleO (𝓝[≠] (0 : ℝ))
      (fun h => f (a + h) - (f a + v * (a + h - a))) (fun h : ℝ => h) ↔ v = L := by
  simpa only [scalarLittleO_iff_isLittleO, smul_eq_mul, mul_comm] using
    affine_tangent_iff f L a hd v

theorem complex_affine_tangent_iff (f : ℝ → ℂ) (L : ℂ) (a : ℝ)
    (hd : HasRealIncrementDerivative f L a) (v : ℂ) :
    ScalarLittleO (𝓝[≠] (0 : ℝ))
      (fun h => f (a + h) - (f a + v * ((a + h - a : ℝ) : ℂ)))
      (fun h : ℝ => (h : ℂ)) ↔ v = L := by
  simpa only [ScalarLittleO, Asymptotics.isLittleO_iff, Complex.norm_real,
    Complex.real_smul, mul_comm] using affine_tangent_iff f L a hd v

theorem real_instantaneous_velocity (f : ℝ → ℝ) (t : ℝ)
    (hd : DifferentiableAt ℝ f t) :
    Tendsto (fun h : ℝ => (f (t + h) - f t) / h)
      (𝓝[≠] (0 : ℝ)) (𝓝 (deriv f t)) := by
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hd.hasDerivAt.tendsto_slope_zero

theorem complex_instantaneous_velocity (f : ℝ → ℂ) (t : ℝ)
    (hd : DifferentiableAt ℝ f t) :
    Tendsto (fun h : ℝ => (f (t + h) - f t) / (h : ℂ))
      (𝓝[≠] (0 : ℝ)) (𝓝 (deriv f t)) := by
  simpa only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using
    hd.hasDerivAt.tendsto_slope_zero

end SingleVariableAnalysis
