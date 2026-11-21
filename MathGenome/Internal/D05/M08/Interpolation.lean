import MathGenome.Internal.Specs.D05.M08.Interpolation
import MathGenome.Internal.D05.Foundations.RootBound
import Mathlib.LinearAlgebra.Lagrange

/-! K05.08.interpolation: evaluation and its explicit Lagrange inverse over
any field. Injectivity below uses the accepted distinct-root bound. -/

noncomputable section

namespace D05.M08.Interpolation

open Polynomial
open scoped BigOperators

abbrev lagrangePolynomial : Specs.D05.M08.Interpolation.lagrangePolynomial_type :=
  Specs.D05.M08.Interpolation.lagrangePolynomial_value

abbrev evaluation : Specs.D05.M08.Interpolation.evaluation_type :=
  Specs.D05.M08.Interpolation.evaluation_value

abbrev interpolationSum : Specs.D05.M08.Interpolation.interpolationSum_type :=
  Specs.D05.M08.Interpolation.interpolationSum_value

/-- The library factors are exactly the scalar fractions in the source. -/
theorem lagrangePolynomial_eq_basis {K : Type*} [Field K] {r : ℕ}
    (a : Fin r → K) (i : Fin r) :
    lagrangePolynomial K r a i = Lagrange.basis Finset.univ a i := rfl

/-- Identify the explicit sum as a polynomial, without changing its domain. -/
theorem interpolationSum_eq_interpolate {K : Type*} [Field K] {r : ℕ}
    (a c : Fin r → K) :
    interpolationSum K r a c = Lagrange.interpolate Finset.univ a c := by
  simp only [interpolationSum, Specs.D05.M08.Interpolation.interpolationSum_value,
    LinearMap.coe_mk, AddHom.coe_mk, Lagrange.interpolate_apply,
    Polynomial.smul_eq_C_mul, lagrangePolynomial_eq_basis]

theorem denominators_nonzero : Specs.D05.M08.Interpolation.denominators_nonzero := by
  intro K _ r a ha i j hij
  exact sub_ne_zero.mpr (ha.ne hij)

theorem basis_degree : Specs.D05.M08.Interpolation.basis_degree := by
  intro K _ r a ha i
  rw [← lagrangePolynomial, lagrangePolynomial_eq_basis,
    Lagrange.degree_basis ha.injOn (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin]
  exact_mod_cast Nat.sub_lt (Nat.zero_lt_of_lt i.isLt) Nat.zero_lt_one

theorem basis_evaluation : Specs.D05.M08.Interpolation.basis_evaluation := by
  intro K _ r a ha i j
  change (lagrangePolynomial K r a i).eval (a j) = _
  rw [lagrangePolynomial_eq_basis]
  split_ifs with h
  · subst j
    exact Lagrange.eval_basis_self ha.injOn (Finset.mem_univ i)
  · exact Lagrange.eval_basis_of_ne h (Finset.mem_univ j)

theorem interpolation_degree : Specs.D05.M08.Interpolation.interpolation_degree := by
  intro K _ r a ha c
  change (interpolationSum K r a c).degree < _
  rw [interpolationSum_eq_interpolate]
  simpa using Lagrange.degree_interpolate_lt (s := Finset.univ) c ha.injOn

theorem interpolation_evaluation : Specs.D05.M08.Interpolation.interpolation_evaluation := by
  intro K _ r a ha c j
  change (interpolationSum K r a c).eval (a j) = _
  rw [interpolationSum_eq_interpolate]
  exact Lagrange.eval_interpolate_at_node c ha.injOn (Finset.mem_univ j)

/-- A nonzero polynomial in `degreeLT K r` cannot have all r distinct nodes
as roots. This also covers r = 0, since its degree condition forces zero. -/
theorem eq_zero_of_evaluations_zero {K : Type*} [Field K] {r : ℕ}
    (a : Fin r → K) (ha : Function.Injective a)
    (p : Polynomial.degreeLT K r) (hp : ∀ i, (p : Polynomial K).eval (a i) = 0) :
    (p : Polynomial K) = 0 := by
  classical
  by_contra hn
  have hroot := D05.Foundations.RootBound.distinctRootBound K
    (p : Polynomial K) hn (Finset.univ.image a) (by
      intro b hb
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
      exact hp i)
  have hcard : (Finset.univ.image a).card = r := by
    rw [Finset.card_image_of_injective _ ha, Finset.card_univ, Fintype.card_fin]
  rw [hcard] at hroot
  have hdegree := (Polynomial.natDegree_lt_iff_degree_lt hn).mpr
    (Polynomial.mem_degreeLT.mp p.property)
  exact (Nat.not_le_of_gt hdegree) hroot

theorem evaluation_injective : Specs.D05.M08.Interpolation.evaluation_injective := by
  intro K _ r a ha p q hpq
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply eq_zero_of_evaluations_zero a ha (p - q)
  intro i
  have h := congrFun hpq i
  change (p : Polynomial K).eval (a i) = (q : Polynomial K).eval (a i) at h
  simpa only [Submodule.coe_sub, Polynomial.eval_sub, sub_eq_zero] using h

theorem reconstruction : Specs.D05.M08.Interpolation.reconstruction := by
  intro K _ r a ha p
  let q : Polynomial.degreeLT K r :=
    ⟨interpolationSum K r a (evaluation K r a p),
      Polynomial.mem_degreeLT.mpr (interpolation_degree K r a ha _)⟩
  have h : evaluation K r a q = evaluation K r a p := by
    funext j
    exact interpolation_evaluation K r a ha _ j
  exact congrArg Subtype.val (evaluation_injective K r a ha h)

theorem evaluation_isomorphism : Specs.D05.M08.Interpolation.evaluation_isomorphism := by
  intro K _ r a ha
  let e : Polynomial.degreeLT K r ≃ₗ[K] D05.Foundations.CoordinateModule K r := {
    evaluation K r a with
    invFun := fun c => ⟨interpolationSum K r a c,
      Polynomial.mem_degreeLT.mpr (interpolation_degree K r a ha c)⟩
    left_inv := fun p => Subtype.ext (reconstruction K r a ha p)
    right_inv := fun c => funext (fun j => interpolation_evaluation K r a ha c j)
  }
  exact ⟨e, rfl, fun _ => rfl⟩

theorem empty_case : Specs.D05.M08.Interpolation.empty_case := by
  intro K _ a
  have hzero : ∀ p : Polynomial.degreeLT K 0, (p : Polynomial K) = 0 := by
    intro p
    have hp := Polynomial.mem_degreeLT.mp p.property
    exact Polynomial.degree_eq_bot.mp (by simpa using hp)
  refine ⟨?_, hzero, ?_, ?_⟩
  · apply le_antisymm _ bot_le
    intro p hp
    exact hzero ⟨p, hp⟩
  · intro c
    exact Subsingleton.elim c 0
  · intro c
    change ∑ i : Fin 0, c i • lagrangePolynomial K 0 a i = 0
    exact Finset.sum_empty

end D05.M08.Interpolation
