import MathGenome.Internal.D05.M02.VectorSpace
import MathGenome.Internal.Specs.D05.M03.LinearMap

/-! K05.03.linear_map: the defining identities and their elementary consequences. -/

namespace D05.M03.LinearMap

open scoped BigOperators ComplexConjugate

/-- Linear maps use Mathlib's canonical structure over the common field. -/
abbrev linearMap (K V W : Type*) [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] := V →ₗ[K] W

theorem linearMap_iff_axioms : Specs.D05.M03.LinearMap.linearMap_iff_axioms := by
  intro K V W _ _ _ _ _ t
  constructor
  · rintro ⟨T, rfl⟩
    exact ⟨T.map_add, T.map_smul⟩
  · rintro ⟨hadd, hsmul⟩
    exact ⟨{ toFun := t, map_add' := hadd, map_smul' := hsmul }, rfl⟩

theorem map_finite_combination : Specs.D05.M03.LinearMap.map_finite_combination := by
  intro K V W I _ _ _ _ _ T s a v
  rw [_root_.map_sum]
  exact Finset.sum_congr rfl (fun i _ => T.map_smul (a i) (v i))

theorem map_finsupp_combination : Specs.D05.M03.LinearMap.map_finsupp_combination := by
  intro K V W I _ _ _ _ _ T a v
  exact map_finite_combination T a.support a v

theorem map_zero : Specs.D05.M03.LinearMap.map_zero := by
  intro K V W _ _ _ _ _ T
  exact _root_.map_zero T

theorem map_neg : Specs.D05.M03.LinearMap.map_neg := by
  intro K V W _ _ _ _ _ T v
  exact _root_.map_neg T v

theorem conjugation_real_linear : Specs.D05.M03.LinearMap.conjugation_real_linear := by
  exact ⟨Complex.conjAe.toLinearMap, fun _ => rfl⟩

theorem conjugation_not_complex_linear :
    Specs.D05.M03.LinearMap.conjugation_not_complex_linear := by
  rintro ⟨T, hT⟩
  have h := T.map_smul Complex.I (1 : ℂ)
  simp only [hT, smul_eq_mul, mul_one, map_one, Complex.conj_I] at h
  have him := congrArg Complex.im h
  simp at him
  exact (ne_of_lt (lt_trans neg_one_lt_zero zero_lt_one)) him

end D05.M03.LinearMap
