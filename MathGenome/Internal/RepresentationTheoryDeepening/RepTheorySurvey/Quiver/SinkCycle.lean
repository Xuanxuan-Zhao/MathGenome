import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.SinkCycle
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.SimpleReflections
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Quivers.AcyclicFiniteness
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Order.Extension.Linear

/-! A sink cycle in a finite acyclic quiver and its Coxeter operator. -/

open scoped BigOperators Matrix

universe u v r

namespace RepTheorySurvey.Quiver.SinkCycle

open Forms SimpleReflections

abbrev IsSinkNumbering := @SinkCycleSpec.IsSinkNumbering
noncomputable abbrev endpointsAt := @SinkCycleSpec.endpointsAt
noncomputable abbrev reverseIncident := @SinkCycleSpec.reverseIncident
noncomputable abbrev quiverAt := @SinkCycleSpec.quiverAt
noncomputable abbrev coxeterPrefix := @SinkCycleSpec.coxeterPrefix
noncomputable abbrev coxeter := @SinkCycleSpec.coxeter
noncomputable abbrev coxeterMatrix := @SinkCycleSpec.coxeterMatrix
noncomputable abbrev eulerMatrix := @SinkCycleSpec.eulerMatrix

section Orientation

variable {Q : Type u} [Quiver.{v} Q] [Fintype Q]

theorem exists_sinkNumbering [Fintype (RM03.Arrow Q)] (h : ¬ RM03.HasOrientedCycle Q) :
    ∃ number : Q ≃ Fin (Fintype.card Q), IsSinkNumbering number := by
  let : PartialOrder Q := {
    le := fun i j => Quiver.Reachable j i
    le_refl := Quiver.Reachable.refl
    le_trans := fun _ _ _ hab hbc => hbc.trans hab
    le_antisymm := by
      intro i j hij hji
      obtain ⟨p⟩ := hij
      obtain ⟨q⟩ := hji
      by_contra hne
      have hp : p.length ≠ 0 := fun hz => hne (p.eq_of_length_zero hz).symm
      exact h (RM03.hasOrientedCycle_iff_exists_closed_path.mpr
        ⟨j, p.comp q, by rw [Quiver.Path.length_comp]; omega⟩) }
  let : Fintype (LinearExtension Q) := ‹Fintype Q›
  let orderNumber : LinearExtension Q ≃o Fin (Fintype.card Q) :=
    (Fintype.orderIsoFinOfCardEq (LinearExtension Q) rfl).symm
  let number : Q ≃ Fin (Fintype.card Q) := orderNumber.toEquiv
  refine ⟨number, ?_⟩
  rintro ⟨s, t, a⟩
  have hle : number t ≤ number s :=
    orderNumber.monotone (toLinearExtension.monotone a.reachable)
  refine lt_of_le_of_ne hle (fun heq => ?_)
  have hts : t = s := number.injective heq
  subst t
  exact (noLoop h s).false a

theorem endpointsAt_zero (number : Q ≃ Fin (Fintype.card Q)) (a : RM03.Arrow Q) :
    endpointsAt number 0 a = (a.1, a.2.1) := by
  simp [endpointsAt, SinkCycleSpec.endpointsAt]

theorem endpointsAt_card (number : Q ≃ Fin (Fintype.card Q)) (a : RM03.Arrow Q) :
    endpointsAt number (Fintype.card Q) a = (a.1, a.2.1) := by
  simp [endpointsAt, SinkCycleSpec.endpointsAt, (number a.1).isLt, (number a.2.1).isLt]

theorem quiverAt_isSink {number : Q ≃ Fin (Fintype.card Q)} (h : IsSinkNumbering number)
    (i : Fin (Fintype.card Q)) (j : Q) :
    IsEmpty ((quiverAt number i.val).Hom (number.symm i) j) := by
  refine ⟨fun ⟨a, ha, _⟩ => ?_⟩
  have hts : (number a.2.1 : ℕ) < (number a.1 : ℕ) := h a
  change (endpointsAt number i.val a).1 = number.symm i at ha
  unfold endpointsAt SinkCycleSpec.endpointsAt at ha
  split at ha
  · rename_i horient
    have heq : number a.1 = i := by simpa using congrArg number ha
    have hval := congrArg Fin.val heq
    omega
  · rename_i horient
    have heq : number a.2.1 = i := by simpa using congrArg number ha
    have hval := congrArg Fin.val heq
    omega

theorem endpointsAt_succ {number : Q ≃ Fin (Fintype.card Q)} (h : IsSinkNumbering number)
    (i : Fin (Fintype.card Q)) (a : RM03.Arrow Q) :
    endpointsAt number (i.val + 1) a =
      reverseIncident (number.symm i) (endpointsAt number i.val a) := by
  have hts : (number a.2.1 : ℕ) < (number a.1 : ℕ) := h a
  have hsource : a.1 = number.symm i ↔ (number a.1 : ℕ) = i.val := by
    rw [← Fin.ext_iff, ← number.apply_eq_iff_eq, number.apply_symm_apply]
  have htarget : a.2.1 = number.symm i ↔ (number a.2.1 : ℕ) = i.val := by
    rw [← Fin.ext_iff, ← number.apply_eq_iff_eq, number.apply_symm_apply]
  unfold endpointsAt SinkCycleSpec.endpointsAt reverseIncident SinkCycleSpec.reverseIncident
  split <;> split
  all_goals
    rename_i hafter hbefore
    simp only [hbefore, ite_true, ite_false, hsource, htarget]
  · rw [ite_eq_right (by omega)]
  · rw [ite_eq_left (by omega)]
    rfl
  · rw [ite_eq_left (by omega)]
    rfl
  · rw [ite_eq_right (by omega)]

end Orientation

section Matrices

variable {Q : Type u} [Quiver.{v} Q] [Fintype Q] (number : Q ≃ Fin (Fintype.card Q))
variable (R : Type r) [CommRing R]

theorem coxeterPrefix_step (i : Fin (Fintype.card Q)) (x : Q → R) :
    coxeterPrefix number R (i.val + 1) x =
      simpleReflection R (number.symm i) (coxeterPrefix number R i.val x) := by
  rw [coxeterPrefix, SinkCycleSpec.coxeterPrefix, dite_eq_left i.isLt]
  rfl

theorem coxeterPrefix_intCast (m : ℕ) (x : DimensionVector Q) :
    coxeterPrefix number ℝ m (fun i => (x i : ℝ)) =
      fun i => (coxeterPrefix number ℤ m x i : ℝ) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    by_cases hm : m < Fintype.card Q
    · rw [coxeterPrefix_step number ℝ ⟨m, hm⟩, coxeterPrefix_step number ℤ ⟨m, hm⟩, ih]
      exact simpleReflection_intCast _ _
    · simpa only [coxeterPrefix, SinkCycleSpec.coxeterPrefix, dite_eq_right hm] using ih

theorem coxeterMatrix_mulVec (x : Q → R) :
    coxeterMatrix number R *ᵥ x = coxeter number R x := by
  classical
  exact LinearMap.toMatrix'_mulVec (coxeter number R).toLinearMap x

theorem eulerMatrix_det :
    open Classical in (eulerMatrix number R).det = 1 := by
  classical
  let : LinearOrder Q := LinearOrder.lift' number number.injective
  let : DecidableEq Q := Classical.decEq Q
  have hlower : (eulerMatrix number R).IsLowerTriangular := by
    intro i j hij
    change number i < number j at hij
    have hne : i ≠ j := fun heq => hij.ne (congrArg number heq)
    simp [eulerMatrix, SinkCycleSpec.eulerMatrix, hne, not_lt_of_gt hij]
  rw [Matrix.det_of_isLowerTriangular _ hlower]
  simp [eulerMatrix, SinkCycleSpec.eulerMatrix]

theorem eulerMatrix_isUnit :
    open Classical in IsUnit (eulerMatrix number R) := by
  classical
  rw [Matrix.isUnit_iff_isUnit_det, eulerMatrix_det]
  exact isUnit_one

theorem eulerMatrix_add_transpose :
    eulerMatrix number R + (eulerMatrix number R)ᵀ = polarizationMatrix R := by
  classical
  ext i j
  rcases lt_trichotomy (number i) (number j) with h | h | h
  · have hne : i ≠ j := fun heq => h.ne (congrArg number heq)
    simp [eulerMatrix, SinkCycleSpec.eulerMatrix, polarizationMatrix_apply_of_ne hne,
      hne, hne.symm, h, not_lt_of_gt h, edgeMultiplicity_comm j i]
  · obtain rfl := number.injective h
    simp [eulerMatrix, SinkCycleSpec.eulerMatrix, polarizationMatrix_apply_self, one_add_one_eq_two]
  · have hne : j ≠ i := fun heq => h.ne (congrArg number heq)
    simp [eulerMatrix, SinkCycleSpec.eulerMatrix, polarizationMatrix_apply_of_ne hne.symm,
      hne, hne.symm, h, not_lt_of_gt h]

private theorem coxeterPrefix_step_apply_of_ne (m : ℕ) (j : Q) (h : (number j : ℕ) ≠ m)
    (x : Q → R) : coxeterPrefix number R (m + 1) x j = coxeterPrefix number R m x j := by
  by_cases hm : m < Fintype.card Q
  · rw [coxeterPrefix_step number R ⟨m, hm⟩]
    exact simpleReflection_apply_ne (fun heq => h (by simp [heq])) _
  · rw [coxeterPrefix, SinkCycleSpec.coxeterPrefix, dite_eq_right hm]

private theorem coxeterPrefix_apply_before (m : ℕ) (j : Q) (h : m ≤ (number j : ℕ))
    (x : Q → R) : coxeterPrefix number R m x j = x j := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [coxeterPrefix_step_apply_of_ne number R m j (by omega), ih (by omega)]

private theorem coxeterPrefix_apply_after (m n : ℕ) (j : Q)
    (hj : (number j : ℕ) < m) (hmn : m ≤ n) (x : Q → R) :
    coxeterPrefix number R n x j = coxeterPrefix number R m x j := by
  induction n with
  | zero => rw [show m = 0 by omega]
  | succ n ih =>
    by_cases heq : m = n + 1
    · subst m
      rfl
    · rw [coxeterPrefix_step_apply_of_ne number R n j (by omega), ih (by omega)]

private theorem coxeter_mulVec_equation (h : ¬ RM03.HasOrientedCycle Q) (x : Q → R) :
    eulerMatrix number R *ᵥ coxeter number R x = -(eulerMatrix number R)ᵀ *ᵥ x := by
  classical
  funext i
  let y := coxeter number R x
  let z := coxeterPrefix number R (number i).val x
  let a : Q → R := fun j => (edgeMultiplicity i j : R)
  have hdiag : a i = 0 := by simp [a, edgeMultiplicity_self h]
  have hupdate : y i = -x i + ∑ j, a j * z j := by
    change coxeterPrefix number R (Fintype.card Q) x i = _
    rw [coxeterPrefix_apply_after number R ((number i).val + 1) _ i (by omega)
      (number i).isLt x]
    rw [coxeterPrefix_step, Equiv.symm_apply_apply, simpleReflection_apply_self h,
      coxeterPrefix_apply_before number R _ i le_rfl x]
  have hsum : ∑ j, a j * z j =
      (∑ j, if number j < number i then a j * y j else 0) +
      ∑ j, if number i < number j then a j * x j else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rcases lt_trichotomy (number j) (number i) with hj | hj | hj
    · have hz : z j = y j := (coxeterPrefix_apply_after number R _ _ j hj
          (Nat.le_of_lt (number i).isLt) x).symm
      simp [hz, hj, not_lt_of_gt hj]
    · obtain rfl := number.injective hj
      simp [hdiag]
    · have hz : z j = x j := coxeterPrefix_apply_before number R _ j hj.le x
      simp [hz, hj, not_lt_of_gt hj]
  have hrow (j : Q) : eulerMatrix number R i j * y j =
      (if j = i then y i else 0) - (if number j < number i then a j * y j else 0) := by
    by_cases hj : j = i
    · subst j
      simp [eulerMatrix, SinkCycleSpec.eulerMatrix]
    · by_cases hn : number j < number i <;>
        simp [eulerMatrix, SinkCycleSpec.eulerMatrix, a, hj, Ne.symm hj, hn]
  have hcol (j : Q) : eulerMatrix number R j i * x j =
      (if j = i then x i else 0) - (if number i < number j then a j * x j else 0) := by
    by_cases hj : j = i
    · subst j
      simp [eulerMatrix, SinkCycleSpec.eulerMatrix]
    · by_cases hn : number i < number j <;>
        simp [eulerMatrix, SinkCycleSpec.eulerMatrix, a, hj, hn, edgeMultiplicity_comm j i]
  change (eulerMatrix number R *ᵥ y) i = _
  rw [Matrix.neg_mulVec]
  simp only [Matrix.mulVec, dotProduct, Pi.neg_apply, Matrix.transpose_apply, hrow, hcol,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hsum] at hupdate
  linear_combination hupdate

theorem coxeterMatrix_eq [Fintype (RM03.Arrow Q)] (h : ¬ RM03.HasOrientedCycle Q)
    (_hn : IsSinkNumbering number) :
    open Classical in
      coxeterMatrix number R = -(eulerMatrix number R)⁻¹ * (eulerMatrix number R)ᵀ := by
  classical
  let E := eulerMatrix number R
  let C := coxeterMatrix number R
  have hdet : IsUnit E.det := by
    dsimp [E]
    rw [eulerMatrix_det]
    exact isUnit_one
  have heq : E * C = -Eᵀ := by
    apply Matrix.ext_iff_mulVec.mpr
    intro x
    change (eulerMatrix number R * coxeterMatrix number R) *ᵥ x = -Eᵀ *ᵥ x
    rw [← Matrix.mulVec_mulVec, coxeterMatrix_mulVec]
    exact coxeter_mulVec_equation number R h x
  calc
    C = E⁻¹ * (E * C) := (Matrix.nonsing_inv_mul_cancel_left _ _ hdet).symm
    _ = -E⁻¹ * Eᵀ := by rw [heq, mul_neg, neg_mul]

end Matrices

end RepTheorySurvey.Quiver.SinkCycle
