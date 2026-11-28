import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.CoxeterDynamics
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.SinkCycle
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Periodicity and sign change for a positive-definite Coxeter operator. -/

open scoped BigOperators Matrix

universe u v r

namespace RepTheorySurvey.Quiver.CoxeterDynamics

open Forms SimpleReflections SinkCycle

variable {Q : Type u} [Quiver.{v} Q] [Fintype Q] [Fintype (RM03.Arrow Q)]

private theorem int_quadratic_matrix (h : ¬ RM03.HasOrientedCycle Q) (d : Q → ℤ) :
    2 * titsForm d = d ⬝ᵥ (polarizationMatrix ℤ *ᵥ d) := by
  rw [← eulerForm_add_swap_eq_pairing h, two_mul]
  rfl

theorem integralLevel_finite : CoxeterDynamicsSpec.IntegralLevelFinite Q := by
  intro h hpos b
  have hmatrix : (polarizationMatrix (Q := Q) ℤ).PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      exact polarizationMatrix_transpose ℤ
    · intro d hd
      rw [star_trivial, ← int_quadratic_matrix h]
      apply mul_pos (by decide)
      have hd' : (fun i : Q => (d i : ℝ)) ≠ 0 := by
        intro hz
        apply hd
        funext i
        have hi : (d i : ℝ) = 0 := congrFun hz i
        change d i = 0
        exact_mod_cast hi
      have hp := hpos _ hd'
      rw [real_titsForm_intCast] at hp
      exact_mod_cast hp
  refine (hmatrix.finite_setOfPred_dotProduct_mulVec_le (2 * b)).subset ?_
  intro d hd
  change titsForm d = b at hd
  change d ⬝ᵥ (polarizationMatrix ℤ *ᵥ d) ≤ 2 * b
  rw [← int_quadratic_matrix h, hd]

theorem integralLevel_bounded : CoxeterDynamicsSpec.IntegralLevelBounded Q := by
  intro h hp b
  have hfinite := (integralLevel_finite (Q := Q) h hp b).prod
    (Set.finite_univ : (Set.univ : Set Q).Finite)
  obtain ⟨B, hB⟩ := (hfinite.image (fun p : (Q → ℤ) × Q => |p.1 p.2|)).bddAbove
  refine ⟨max 0 B, le_max_left _ _, fun d hd i => ?_⟩
  exact (hB ⟨(d, i), ⟨hd, Set.mem_univ i⟩, rfl⟩).trans (le_max_right _ _)

theorem coxeter_onlyZeroFixed : CoxeterDynamicsSpec.OnlyZeroFixed Q := by
  classical
  intro h hpos number hn x hx
  let E := eulerMatrix number ℝ
  have hdet : IsUnit E.det := by
    dsimp [E]
    rw [eulerMatrix_det]
    exact isUnit_one
  have hEC : E * coxeterMatrix number ℝ = -Eᵀ := by
    rw [coxeterMatrix_eq number ℝ h hn]
    change E * (-E⁻¹ * Eᵀ) = -Eᵀ
    rw [neg_mul, mul_neg, Matrix.mul_nonsing_inv_cancel_left E _ hdet]
  have hB : polarizationMatrix ℝ *ᵥ x = 0 := by
    rw [← eulerMatrix_add_transpose number ℝ, Matrix.add_mulVec]
    have heq := congrArg (fun A : Matrix Q Q ℝ => A *ᵥ x) hEC
    change (E * coxeterMatrix number ℝ) *ᵥ x = (-Eᵀ) *ᵥ x at heq
    rw [← Matrix.mulVec_mulVec, coxeterMatrix_mulVec, hx, Matrix.neg_mulVec] at heq
    change E *ᵥ x + Eᵀ *ᵥ x = 0
    rw [heq, neg_add_cancel]
  by_contra hxne
  have hquad := real_quadratic_matrix h x
  rw [hB, dotProduct_zero] at hquad
  exact (mul_pos (by norm_num) (hpos x hxne)).ne' hquad

private theorem coxeterPrefix_preservesTitsForm (h : ¬ RM03.HasOrientedCycle Q)
    (number : Q ≃ Fin (Fintype.card Q)) (m : ℕ) (d : Q → ℤ) :
    titsForm (coxeterPrefix number ℤ m d) = titsForm d := by
  induction m with
  | zero => rfl
  | succ m ih =>
    by_cases hm : m < Fintype.card Q
    · rw [coxeterPrefix_step number ℤ ⟨m, hm⟩, simpleReflection_preservesTitsForm h]
      exact ih
    · simpa only [coxeterPrefix, SinkCycleSpec.coxeterPrefix, dite_eq_right hm] using ih

private theorem coxeter_pow_preservesTitsForm (h : ¬ RM03.HasOrientedCycle Q)
    (number : Q ≃ Fin (Fintype.card Q)) (m : ℕ) (d : Q → ℤ) :
    titsForm (((coxeter number ℤ) ^ m) d) = titsForm d := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', LinearEquiv.mul_apply]
    exact (coxeterPrefix_preservesTitsForm h number (Fintype.card Q) _).trans ih

omit [Fintype (RM03.Arrow Q)] in
private theorem coxeter_pow_intCast (number : Q ≃ Fin (Fintype.card Q)) (m : ℕ)
    (d : Q → ℤ) :
    ((coxeter number ℝ) ^ m) (fun i => (d i : ℝ)) =
      fun i => (((coxeter number ℤ) ^ m) d i : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [pow_succ', LinearEquiv.mul_apply, ih]
    exact coxeterPrefix_intCast number (Fintype.card Q) _

private theorem linearEquiv_eq_of_single {ι : Type u} [Finite ι] [DecidableEq ι]
    {R : Type r} [CommRing R] {f g : (ι → R) ≃ₗ[R] (ι → R)}
    (h : ∀ i : ι, f (Pi.single i 1) = g (Pi.single i 1)) : f = g := by
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun R ι).ext
  intro i
  simpa only [Pi.basisFun_apply, LinearEquiv.coe_coe] using h i

theorem coxeter_finiteOrder : CoxeterDynamicsSpec.FiniteOrder Q := by
  classical
  intro h hpos number _
  let columns (f : (Q → ℤ) ≃ₗ[ℤ] (Q → ℤ)) (i : Q) : Q → ℤ := f (Pi.single i 1)
  have hcolumns : Function.Injective columns := fun _ _ heq =>
    linearEquiv_eq_of_single (congrFun heq)
  have hlevels :
      {v : Q → (Q → ℤ) | ∀ i, titsForm (v i) = titsForm (Pi.single i 1 : Q → ℤ)}.Finite :=
    Set.Finite.pi' fun i => integralLevel_finite (Q := Q) h hpos
      (titsForm (Pi.single i 1 : Q → ℤ))
  have hpowers : (↑(Submonoid.powers (coxeter number ℤ)) : Set ((Q → ℤ) ≃ₗ[ℤ] (Q → ℤ))).Finite := by
    refine (hlevels.preimage (f := columns) hcolumns.injOn).subset ?_
    intro f hf
    obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hf
    exact fun i => coxeter_pow_preservesTitsForm h number m (Pi.single i 1)
  obtain ⟨m, hm, hInt⟩ := (finite_powers.mp hpowers).exists_pow_eq_one
  refine ⟨m, hm, hInt, linearEquiv_eq_of_single ?_⟩
  intro i
  have hcast := coxeter_pow_intCast number m (Pi.single i 1 : Q → ℤ)
  have hsingle : (fun j => ((Pi.single i 1 : Q → ℤ) j : ℝ)) = Pi.single i (1 : ℝ) := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  simpa only [hInt, hsingle, LinearEquiv.coe_one, id_eq] using hcast

theorem coxeter_negativeCoordinateReal : CoxeterDynamicsSpec.NegativeCoordinateReal Q := by
  intro h hpos number hn x hx hxnonneg
  obtain ⟨p, hp, _, hperiod⟩ := coxeter_finiteOrder (Q := Q) h hpos number hn
  let C := coxeter number ℝ
  let y := ∑ m ∈ Finset.range p, (C ^ m) x
  have hcycle : (C ^ p) x = x := by rw [show C ^ p = 1 from hperiod]; rfl
  have hfixed : C y = y := by
    calc
      C y = ∑ m ∈ Finset.range p, (C ^ (m + 1)) x := by
        dsimp only [y]
        rw [map_sum]
        simp only [pow_succ', LinearEquiv.mul_apply]
      _ = y := by
        have hsum := (Finset.sum_range_succ' (fun m : ℕ => (C ^ m) x) p).symm.trans
          (Finset.sum_range_succ (fun m : ℕ => (C ^ m) x) p)
        rw [pow_zero, LinearEquiv.coe_one, id_eq, hcycle] at hsum
        exact add_right_cancel hsum
  have hy := coxeter_onlyZeroFixed (Q := Q) h hpos number hn y hfixed
  by_contra! hnonneg
  apply hx
  funext i
  change x i = 0
  have hsum : ∑ m ∈ Finset.range p, (C ^ m) x i = 0 := by
    simpa only [y, Finset.sum_apply, Pi.zero_apply] using congrFun hy i
  have hterm : (C ^ (0 : ℕ)) x i ≤ ∑ m ∈ Finset.range p, (C ^ m) x i :=
    Finset.single_le_sum (fun m _ => hnonneg m i) (Finset.mem_range.mpr hp)
  rw [hsum, pow_zero, LinearEquiv.coe_one, id_eq] at hterm
  exact le_antisymm hterm (hxnonneg i)

theorem coxeter_negativeCoordinateIntegral : CoxeterDynamicsSpec.NegativeCoordinateIntegral Q := by
  intro h hpos number hn x hx hxnonneg
  have hcast : (fun i => (x i : ℝ)) ≠ 0 := by
    intro hz
    apply hx
    funext i
    have hi : (x i : ℝ) = 0 := congrFun hz i
    change x i = 0
    exact_mod_cast hi
  obtain ⟨m, i, hi⟩ := coxeter_negativeCoordinateReal (Q := Q) h hpos number hn
    (fun i => (x i : ℝ)) hcast (fun i => by exact_mod_cast hxnonneg i)
  rw [coxeter_pow_intCast] at hi
  change (((coxeter number ℤ) ^ m) x i : ℝ) < 0 at hi
  refine ⟨m, i, ?_⟩
  exact_mod_cast hi

theorem fullSinkCycle : CoxeterDynamicsSpec.FullSinkCycle.{u, v, r} Q := by
  intro h
  refine ⟨exists_sinkNumbering h, fun number hn => ⟨endpointsAt_zero number,
    quiverAt_isSink hn, endpointsAt_succ hn, endpointsAt_card number, ?_, ?_⟩⟩
  · intro R _
    exact ⟨eulerMatrix_isUnit number R, coxeterMatrix_eq number R h hn⟩
  · intro hpos
    exact ⟨coxeter_finiteOrder h hpos number hn, coxeter_onlyZeroFixed h hpos number hn,
      coxeter_negativeCoordinateReal h hpos number hn,
      coxeter_negativeCoordinateIntegral h hpos number hn⟩

end RepTheorySurvey.Quiver.CoxeterDynamics
