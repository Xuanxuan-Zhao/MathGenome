import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.LinearProgramStandardForm
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch05.LinearProgramModels
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Fintype.EquivFin

noncomputable section
open Matrix Set
universe u v w
namespace VariationalNotes.Ch05.LinearProgramStandardForm
variable {ι : Type u} {κ : Type v} {ν : Type w}
variable [Fintype ι] [Fintype κ] [Fintype ν]
local instance : DecidableEq ν := Classical.decEq _

omit [Fintype κ] in
lemma standard_mulVec_ineq (P : Problem ι κ ν) (q : (ν ⊕ (ν ⊕ ι)) → ℝ) (i : ι) :
    (standardMatrix P *ᵥ q) (.inl i) =
      (P.ineq *ᵥ decode q) i + q (.inr (.inr i)) := by
  classical
  simp [mulVec, dotProduct, standardMatrix, decode, Fintype.sum_sum_type,
    neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg, mul_add, mul_neg,
    Finset.sum_add_distrib, add_assoc]

omit [Fintype κ] in
lemma standard_mulVec_eqn (P : Problem ι κ ν) (q : (ν ⊕ (ν ⊕ ι)) → ℝ) (i : κ) :
    (standardMatrix P *ᵥ q) (.inr i) = (P.eqn *ᵥ decode q) i := by
  classical
  simp [mulVec, dotProduct, standardMatrix, decode, Fintype.sum_sum_type,
    neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg, mul_add, mul_neg,
    Finset.sum_add_distrib]

theorem decode_lift : Specs.decode_lift.{u,v,w} := by
  intro ι κ ν _ _ _ P x
  funext j
  simp only [decode, lift, Sum.elim_inl, Sum.elim_inr]
  rcases le_total (x j) 0 with h | h
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
    simp
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    simp

theorem standard_feasible_iff : Specs.standard_feasible_iff.{u,v,w} := by
  intro ι κ ν _ _ _ P q
  constructor
  · rintro ⟨hEq, hnonneg⟩
    have hi (i : ι) : (P.ineq *ᵥ decode q) i + q (.inr (.inr i)) = P.ineqBound i := by
      simpa only [standard_mulVec_ineq, standardBound, Sum.elim_inl] using
        congrFun hEq (.inl i)
    refine ⟨hnonneg, ⟨fun i => ?_, ?_⟩, fun i => ?_⟩
    · linarith [hnonneg (.inr (.inr i)), hi i]
    · funext i
      simpa only [standard_mulVec_eqn, standardBound, Sum.elim_inr] using
        congrFun hEq (.inr i)
    · linarith [hi i]
  · rintro ⟨hnonneg, hfeas, hslack⟩
    refine ⟨?_, hnonneg⟩
    funext r
    cases r with
    | inl i => simp [standard_mulVec_ineq, standardBound, hslack]
    | inr i => simpa [standard_mulVec_eqn, standardBound] using congrFun hfeas.2 i

theorem lift_feasible : Specs.lift_feasible.{u,v,w} := by
  intro ι κ ν _ _ _ P x hx
  apply (standard_feasible_iff P (lift P x)).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro j
    rcases j with j | (j | i)
    · exact le_max_right _ _
    · exact le_max_right _ _
    · exact sub_nonneg.mpr (hx.1 i)
  · rw [decode_lift P x]
    exact hx
  · intro i
    rw [decode_lift P x]
    rfl

theorem feasible_correspondence : Specs.feasible_correspondence.{u,v,w} := by
  intro ι κ ν _ _ _ P x
  constructor
  · intro hx
    exact ⟨lift P x, lift_feasible P x hx, decode_lift P x⟩
  · rintro ⟨q, hq, rfl⟩
    exact ((standard_feasible_iff P q).mp hq).2.1

theorem objective_preserved : Specs.objective_preserved.{u,v,w} := by
  intro ι κ ν _ _ _ P q
  simp [LinearProgramModels.Specs.primalObjective, objective, standardCost, decode,
    dotProduct, Fintype.sum_sum_type, neg_mul, Finset.sum_neg_distrib,
    sub_eq_add_neg, mul_add, mul_neg, Finset.sum_add_distrib]

theorem objective_range_eq : Specs.objective_range_eq.{u,v,w} := by
  intro ι κ ν _ _ _ P
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨lift P x, lift_feasible P x hx, by rw [objective_preserved, decode_lift]⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨decode q, ((standard_feasible_iff P q).mp hq).2.1,
      (objective_preserved P q).symm⟩

theorem value_preserved : Specs.value_preserved.{u,v,w} := by
  intro ι κ ν _ _ _ P
  unfold value LinearProgramModels.Specs.primalValue
  congr 1
  rw [← Set.image_image, objective_range_eq P, Set.image_image]

theorem optimal_correspondence : Specs.optimal_correspondence.{u,v,w} := by
  intro ι κ ν _ _ _ P q
  unfold LinearProgramModels.Specs.PrimalOptimal
  rw [← value_preserved, objective_preserved]
  exact ⟨fun h => ⟨h.1, ((standard_feasible_iff P q).mp h.1).2.1, h.2⟩,
    fun h => ⟨h.1, h.2.2⟩⟩

theorem attainment_correspondence : Specs.attainment_correspondence.{u,v,w} := by
  intro ι κ ν _ _ _ P p
  constructor
  · rintro ⟨x, hx, hp, hobj⟩
    have hobj' : LinearProgramModels.Specs.primalObjective (standardCost P) (lift P x) = p := by
      rw [objective_preserved, decode_lift, hobj]
    refine ⟨lift P x, ⟨lift_feasible P x hx, ?_⟩, hobj'⟩
    rw [← value_preserved, hp, hobj']
  · rintro ⟨q, ⟨hq, hp⟩, hobj⟩
    refine ⟨decode q, ((standard_feasible_iff P q).mp hq).2.1, ?_, ?_⟩
    · rw [value_preserved, hp, hobj]
    · rw [← objective_preserved, hobj]

omit [Fintype ν] in
lemma standard_transpose_pos (P : Problem ι κ ν) (y : ι → ℝ) (z : κ → ℝ) (j : ν) :
    ((standardMatrix P)ᵀ *ᵥ joinDual y z) (.inl j) =
      (P.ineqᵀ *ᵥ y + P.eqnᵀ *ᵥ z) j := by
  classical
  simp [mulVec, dotProduct, standardMatrix, joinDual, Fintype.sum_sum_type]

omit [Fintype ν] in
lemma standard_transpose_neg (P : Problem ι κ ν) (y : ι → ℝ) (z : κ → ℝ) (j : ν) :
    ((standardMatrix P)ᵀ *ᵥ joinDual y z) (.inr (.inl j)) =
      -(P.ineqᵀ *ᵥ y + P.eqnᵀ *ᵥ z) j := by
  classical
  simp [mulVec, dotProduct, standardMatrix, joinDual, Fintype.sum_sum_type,
    neg_mul, Finset.sum_neg_distrib, add_comm]

omit [Fintype ν] in
lemma standard_transpose_slack (P : Problem ι κ ν) (y : ι → ℝ) (z : κ → ℝ) (i : ι) :
    ((standardMatrix P)ᵀ *ᵥ joinDual y z) (.inr (.inr i)) = y i := by
  classical
  simp [mulVec, dotProduct, standardMatrix, joinDual, Fintype.sum_sum_type]

theorem dual_feasible_iff : Specs.dual_feasible_iff.{u,v,w} := by
  intro ι κ ν _ _ _ P y z
  constructor
  · intro h
    refine ⟨fun i => ?_, funext fun j => ?_⟩
    · simpa [standard_transpose_slack, standardCost] using h (.inr (.inr i))
    · have hpos : (P.ineqᵀ *ᵥ y + P.eqnᵀ *ᵥ z) j ≤ P.cost j := by
        simpa [standard_transpose_pos, standardCost] using h (.inl j)
      have hneg : -(P.ineqᵀ *ᵥ y + P.eqnᵀ *ᵥ z) j ≤ -P.cost j := by
        simpa [standard_transpose_neg, standardCost] using h (.inr (.inl j))
      linarith
  · rintro ⟨hy, hEq⟩ j
    rcases j with j | (j | i)
    · simpa only [standard_transpose_pos, standardCost, Sum.elim_inl] using
        (congrFun hEq j).le
    · simpa only [standard_transpose_neg, standardCost, Sum.elim_inr, Sum.elim_inl,
        Pi.neg_apply] using (neg_le_neg (congrFun hEq j).ge)
    · simpa [standard_transpose_slack, standardCost] using hy i

theorem dual_objective_preserved : Specs.dual_objective_preserved.{u,v,w} := by
  intro ι κ ν _ _ _ P y z
  simp [LinearProgramModels.Specs.dualObjective, dualObjective, standardBound, joinDual]

omit [Fintype ι] [Fintype κ] in
lemma joinDual_restrict (r : (ι ⊕ κ) → ℝ) :
    joinDual (fun i => r (.inl i)) (fun i => r (.inr i)) = r := by
  funext i
  cases i <;> rfl

lemma dual_objective_range_eq (P : Problem ι κ ν) :
    ((fun yz : (ι → ℝ) × (κ → ℝ) => dualObjective P yz.1 yz.2) ''
      {yz | dualFeasible P yz.1 yz.2}) =
    (LinearProgramModels.Specs.dualObjective (standardBound P) ''
      {r | LinearProgramModels.Specs.dualFeasible (standardMatrix P) (standardCost P) r}) := by
  ext t
  constructor
  · rintro ⟨⟨y, z⟩, h, rfl⟩
    exact ⟨joinDual y z, (dual_feasible_iff P y z).mpr h,
      dual_objective_preserved P y z⟩
  · rintro ⟨r, hr, rfl⟩
    refine ⟨⟨fun i => r (.inl i), fun i => r (.inr i)⟩, ?_, ?_⟩
    · apply (dual_feasible_iff P _ _).mp
      rwa [joinDual_restrict]
    · change dualObjective P _ _ = _
      rw [← dual_objective_preserved, joinDual_restrict]

theorem dual_value_preserved : Specs.dual_value_preserved.{u,v,w} := by
  intro ι κ ν _ _ _ P
  unfold dualValue LinearProgramModels.Specs.dualValue
  congr 1
  rw [← Set.image_image, dual_objective_range_eq P, Set.image_image]

theorem dual_attainment_correspondence :
    Specs.dual_attainment_correspondence.{u,v,w} := by
  intro ι κ ν _ _ _ P p
  constructor
  · rintro ⟨y, z, h, hp, hobj⟩
    have hobj' : LinearProgramModels.Specs.dualObjective (standardBound P) (joinDual y z) = p := by
      rw [dual_objective_preserved, hobj]
    refine ⟨joinDual y z, ⟨(dual_feasible_iff P y z).mpr h, ?_⟩, hobj'⟩
    rw [← dual_value_preserved, hp, hobj']
  · rintro ⟨r, ⟨hr, hp⟩, hobj⟩
    refine ⟨(fun i => r (.inl i)), (fun i => r (.inr i)), ?_, ?_, ?_⟩
    · apply (dual_feasible_iff P _ _).mp
      rwa [joinDual_restrict]
    · rw [dual_value_preserved, hp, hobj]
    · rw [← dual_objective_preserved, joinDual_restrict, hobj]

/-- Coordinates of an affine functional, with its constant term retained. -/
lemma affine_coordinates (a : (ν → ℝ) →ᵃ[ℝ] ℝ) (x : ν → ℝ) :
    a x = (∑ j, a.linear (Pi.single j 1) * x j) + a 0 := by
  classical
  have h : a.linear x = ∑ j, a.linear (Pi.single j 1) * x j := by
    conv_lhs => rw [pi_eq_sum_univ' x, map_sum]
    simp [mul_comm]
  have ha := congrFun a.decomp x
  simpa only [Pi.add_apply, LinearMap.coe_ofClass] using ha.trans (congrArg (fun t => t + a 0) h)

theorem polyhedron_representation : Specs.polyhedron_representation.{w} := by
  intro ν _ C hC
  classical
  obtain ⟨s, rfl⟩ := hC
  let a : Fin s.card → ((ν → ℝ) →ᵃ[ℝ] ℝ) := fun i => (s.equivFin.symm i).val
  refine ⟨s.card, (fun i j => (a i).linear (Pi.single j 1)), (fun i => -(a i) 0), ?_⟩
  ext x
  change (∀ f ∈ s, f x ≤ 0) ↔ ∀ i, (∑ j, (a i).linear (Pi.single j 1) * x j) ≤ -(a i) 0
  constructor
  · intro hx i
    have hi := hx (a i) (s.equivFin.symm i).property
    rw [affine_coordinates (a i) x] at hi
    linarith
  · intro hx f hf
    let i := s.equivFin ⟨f, hf⟩
    have heq : a i = f := by simp [a, i]
    have hi := hx i
    have ha := affine_coordinates (a i) x
    rw [heq] at hi ha
    linarith

theorem polyhedron_standard_form : Specs.polyhedron_standard_form.{w} := by
  intro ν _ C c hC
  obtain ⟨m, A, b, hC⟩ := polyhedron_representation C hC
  let P : Problem (Fin m) Empty ν := ⟨A, b, 0, 0, c⟩
  have hP : {x | feasible P x} = C := by
    ext x
    simp [P, feasible, hC]
  refine ⟨m, P, rfl, hP, ?_⟩
  have h := objective_range_eq P
  rw [hP] at h
  exact h

end VariationalNotes.Ch05.LinearProgramStandardForm
