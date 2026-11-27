import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.RealNormObstruction
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.Complex

import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.CyclicDegreeTwo
set_option autoImplicit false

namespace GaloisFormalization.GH.RealNormObstruction

open Model CyclicDegreeTwo
open Classical
open scoped Algebra CyclicDegreeTwo

universe u v

noncomputable section

local notation "G" => (ℂ ≃ₐ[ℝ] ℂ)
local notation "Coeffs" => (Additive ℂˣ)

private instance : Algebra.IsQuadraticExtension ℝ ℂ := ⟨Complex.finrank_real_complex⟩

private abbrev upG : G ≃* (ULift.{u} G) :=
  { Equiv.ulift.symm with map_mul' := fun _ _ => rfl }

private abbrev upA : Coeffs ≃+ (ULift.{v} Coeffs) :=
  { Equiv.ulift.symm with map_add' := fun _ _ => rfl }

/-- Transport cohomology across the universe lifts of the group and its coefficients. -/
private def descend (n : ℕ) : ContinuousH (ULift.{u} G) (ULift.{v} Coeffs) n ≃+ ContinuousH G Coeffs n :=
  let down := continuousCohomologyMap upG.toMonoidHom continuous_uliftUp
    upA.symm.toAddMonoidHom (fun _ _ => rfl) n
  let up := continuousCohomologyMap upG.symm.toMonoidHom continuous_uliftDown
    upA.toAddMonoidHom (fun _ _ => rfl) n
  { down.toAddMonoidHom with
    invFun := up
    left_inv := by
      intro x
      obtain ⟨c, rfl⟩ := (continuousCoboundaries (ULift.{u} G) (ULift.{v} Coeffs) n).mkQ_surjective x
      rfl
    right_inv := by
      intro x
      obtain ⟨c, rfl⟩ := (continuousCoboundaries G Coeffs n).mkQ_surjective x
      rfl }

private abbrev s : (ULift.{u} G) := ULift.up Complex.conjAe

private theorem conj_ne_one : Complex.conjAe ≠ (1 : G) := by
  intro h
  have him := congrArg (fun f : G => (f Complex.I).im) h
  norm_num at him

private theorem s_ne_one : (s : (ULift.{u} G)) ≠ 1 :=
  fun h => conj_ne_one (congrArg ULift.down h)

private theorem card_lifted_galois : Nat.card (ULift.{u} G) = 2 := by
  rw [Nat.card_congr (Equiv.ulift : (ULift.{u} G) ≃ G), IsGalois.card_aut_eq_finrank,
    Complex.finrank_real_complex]

private theorem conjugation_generates : Subgroup.zpowers (s : (ULift.{u} G)) = ⊤ :=
  zpowers_eq_top_of_prime_card card_lifted_galois s_ne_one

private theorem conjugation_order : orderOf (s : (ULift.{u} G)) = 2 := by
  rw [← Nat.card_zpowers, conjugation_generates, Subgroup.card_top, card_lifted_galois]

/-- Interpret a lifted additive coefficient as the underlying complex number. -/
private def asComplex (a : (ULift.{v} Coeffs)) : ℂ := a.down.toMul

private theorem asComplex_injective : Function.Injective (asComplex.{v}) :=
  fun _ _ h => ULift.ext (Units.ext h)

private def negativeOne : Invariants (ULift.{u} G) (ULift.{v} Coeffs) :=
  ⟨ULift.up (Additive.ofMul (-(1 : ℂˣ))), by
    rw [mem_fixedCoefficients]
    intro g _
    apply asComplex_injective
    change g.down (-1) = -1
    simp⟩

private theorem invariant_real (a : Invariants (ULift.{u} G) (ULift.{v} Coeffs)) :
    ((asComplex a.val).re : ℂ) = asComplex a.val := by
  have hfix := (mem_fixedCoefficients (ULift.{u} G) (ULift.{v} Coeffs) ⊤ a.val).mp a.property s (Subgroup.mem_top s)
  have h := congrArg (fun b => (asComplex b).im) hfix
  change -(asComplex a.val).im = (asComplex a.val).im at h
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im]
    linarith

private theorem norm_asComplex (a : (ULift.{v} Coeffs)) :
    asComplex (norm (s : (ULift.{u} G)) conjugation_generates a).val =
      ((Algebra.norm ℝ (asComplex a) : ℝ) : ℂ) := by
  rw [norm_val, Algebra.norm_complex_apply, Complex.normSq_eq_conj_mul_self]
  have hsum :
      (∑ i : Fin (orderOf (s : (ULift.{u} G))), s ^ (i : ℕ) • a) =
        ∑ i : Fin 2, s.{u} ^ (i : ℕ) • a :=
    Fintype.sum_equiv (finCongr conjugation_order) _ _ (fun _ => rfl)
  rw [hsum, Fin.sum_univ_two]
  change asComplex (s.{u} ^ (0 : ℕ) • a + s.{u} ^ (1 : ℕ) • a) = _
  rw [pow_zero, one_smul, pow_one]
  change asComplex a * Complex.conjAe (asComplex a) = _
  rw [mul_comm, Complex.conjAe_coe]

private theorem mem_norm_range_iff (a : Invariants (ULift.{u} G) (ULift.{v} Coeffs)) :
    a ∈ LinearMap.range (norm (s : (ULift.{u} G)) conjugation_generates) ↔ 0 < (asComplex a.val).re := by
  constructor
  · rintro ⟨b, rfl⟩
    rw [norm_asComplex, Complex.ofReal_re, Algebra.norm_complex_apply, Complex.normSq_pos]
    exact (b.down.toMul).ne_zero
  · intro ha
    let b : ℂˣ := Units.mk0 (Real.sqrt (asComplex a.val).re : ℂ)
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 ha).ne')
    refine ⟨ULift.up (Additive.ofMul b), Subtype.ext (asComplex_injective ?_)⟩
    rw [norm_asComplex, Algebra.norm_complex_apply]
    change ((Complex.normSq (Real.sqrt (asComplex a.val).re : ℂ) : ℝ) : ℂ) = _
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt ha.le, invariant_real]

private theorem negativeOne_class_ne_zero :
    (LinearMap.range (norm (A := ULift.{v} Coeffs) s.{u} conjugation_generates)).mkQ
      negativeOne ≠ 0 := by
  intro h
  have hmem := (Submodule.Quotient.mk_eq_zero _).mp h
  have hpos := (mem_norm_range_iff (negativeOne.{u,v})).mp hmem
  change 0 < (-1 : ℂ).re at hpos
  norm_num at hpos

/-- The two cosets correspond to the signs of the real invariant units. -/
private theorem normQuotient_card :
    Nat.card (NormQuotient s.{u} conjugation_generates (ULift.{v} Coeffs)) = 2 := by
  let image := LinearMap.range (norm (A := ULift.{v} Coeffs) s.{u} conjugation_generates)
  apply (Nat.card_eq_two_iff' (0 : NormQuotient s.{u} conjugation_generates (ULift.{v} Coeffs))).mpr
  refine ⟨image.mkQ negativeOne, negativeOne_class_ne_zero, ?_⟩
  intro x hx
  obtain ⟨a, rfl⟩ := image.mkQ_surjective x
  have hnonpos : (asComplex a.val).re ≤ 0 := by
    apply le_of_not_gt
    intro hpos
    exact hx ((Submodule.Quotient.mk_eq_zero image).mpr ((mem_norm_range_iff a).mpr hpos))
  have hne : (asComplex a.val).re ≠ 0 := by
    intro h
    have ha := invariant_real a
    rw [h, Complex.ofReal_zero] at ha
    exact a.val.down.toMul.ne_zero ha.symm
  have hneg := lt_of_le_of_ne hnonpos hne
  apply sub_eq_zero.mp
  rw [← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  change a - negativeOne ∈ LinearMap.range (norm s.{u} conjugation_generates)
  apply (mem_norm_range_iff _).mpr
  change 0 < (asComplex a.val * (((-(1 : ℂˣ))⁻¹ : ℂˣ) : ℂ)).re
  simpa using (neg_pos.mpr hneg)

private theorem power_eq_conjugation (i : Fin (orderOf s.{u})) :
    s.{u} ^ (i : ℕ) = s ↔ (i : ℕ) = 1 := by
  have horder := conjugation_order.{u}
  have hi := i.isLt
  have h : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
  rcases h with h | h
  · simp [h, Ne.symm s_ne_one]
  · simp [h]

private theorem carry_negativeOne_apply (g h : ULift.{u} G) :
    ((carryCochain s.{u} conjugation_generates (negativeOne.{u,v})).val ![g, h]).down.toMul =
      if g = s ∧ h = s then -(1 : ℂˣ) else 1 := by
  obtain ⟨i, rfl⟩ := (powerEquiv s.{u} conjugation_generates).surjective g
  obtain ⟨j, rfl⟩ := (powerEquiv s.{u} conjugation_generates).surjective h
  simp only [powerEquiv_apply, carryCochain_apply_pow, power_eq_conjugation]
  have horder := conjugation_order.{u}
  have hi := i.isLt
  have hj := j.isLt
  by_cases hboth : (i : ℕ) = 1 ∧ (j : ℕ) = 1
  · have hcarry : ¬ (i : ℕ) + (j : ℕ) < orderOf s.{u} := by omega
    rw [ite_eq_right hcarry, ite_eq_left hboth]
    rfl
  · have hcarry : (i : ℕ) + (j : ℕ) < orderOf s.{u} := by omega
    rw [ite_eq_left hcarry, ite_eq_right hboth]
    rfl

/-- The real norm obstruction, using the supplied cyclic comparison. -/
theorem real_norm_obstruction_conditional.{u',v'}
    (cyclic : CyclicDegreeTwo.Specification.EquivalenceWithCarry.{u',v'})
    (_orderOne : CyclicDegreeTwo.Specification.OrderOneTriviality.{u',v'})
    (_field : CyclicDegreeTwo.Specification.FieldEquivalence.{u',v'}) :
    Specification := by
  classical
  -- The premise is given at arbitrary universes, so apply it to the lifted action.
  obtain ⟨e, he⟩ := cyclic (ULift.{u'} G) (ULift.{v'} Coeffs) s.{u'} conjugation_generates
  obtain ⟨lifted, hlifted, hclass⟩ := he negativeOne
  let c := continuousCocycleMap upG.toMonoidHom continuous_uliftUp
    upA.symm.toAddMonoidHom (fun _ _ => rfl) 2 lifted
  have hcard : Nat.card (ContinuousMulH G ℂˣ 2) = 2 :=
    (Nat.card_congr ((descend 2).symm.trans e).toEquiv).trans normQuotient_card
  have hnonzero : continuousMulClass G ℂˣ 2 (Multiplicative.ofAdd c) ≠ 1 := by
    change descend 2 (continuousClass (ULift.{u'} G) (ULift.{v'} Coeffs) 2 lifted) ≠ 0
    rw [← hclass]
    intro h
    apply negativeOne_class_ne_zero
    apply e.symm.injective
    apply (descend 2).injective
    simpa only [map_zero] using h
  refine ⟨hcard, c, ?_, hnonzero, ?_⟩
  · intro g h
    change (lifted.val.val (fun i => ULift.up (![g, h] i))).down.toMul = _
    have htuple : (fun i => ULift.up (![g, h] i)) = ![ULift.up g, ULift.up h] := by
      funext i
      fin_cases i <;> rfl
    rw [htuple, hlifted, carry_negativeOne_apply]
    simp [s]
  · obtain ⟨x, _, hx⟩ := (Nat.card_eq_two_iff' (1 : ContinuousMulH G ℂˣ 2)).mp hcard
    intro y hy
    exact (hx y hy).trans (hx _ hnonzero).symm

end

end GaloisFormalization.GH.RealNormObstruction

theorem _root_.«GaloisFormalization».«GH».«RealNormObstruction».«real_norm_obstruction» : _root_.«GaloisFormalization».«GH».«RealNormObstruction».«Specification» :=
  @_root_.«GaloisFormalization».«GH».«RealNormObstruction».«real_norm_obstruction_conditional».{0, 0} (@_root_.«GaloisFormalization».«GH».«cyclic_degree_two».{0, 0}) (@_root_.«GaloisFormalization».«GH».«cyclic_degree_two_order_one».{0, 0}) (@_root_.«GaloisFormalization».«GH».«cyclic_field_degree_two».{0, 0})
