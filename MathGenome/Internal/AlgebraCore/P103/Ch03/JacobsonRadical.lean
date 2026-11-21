import MathGenome.Internal.AlgebraCore.Specs.P103.Ch03.JacobsonRadical

namespace P103.Ch03.JacobsonRadical

open P103.Specs.Ch03.JacobsonRadical

def jacobson : jacobsonType := jacobsonValue

theorem maximal_intersection : maximal_intersectionType := by
  intro R _
  exact Ring.jacobson_eq_sInf_isMaximal R

theorem annihilates_simple : annihilates_simpleType := by
  intro R M _ _ _ _ x hx
  apply Module.mem_annihilator.mpr
  intro m
  by_cases hm : m = 0
  · simp [hm]
  · have hmax := IsSimpleModule.ker_toSpanSingleton_isMaximal R hm
    have hker : x ∈ LinearMap.ker (LinearMap.toSpanSingleton R M m) :=
      (Ring.jacobson_le_of_isMaximal _ (R := R)) hx
    exact hker

theorem simple_annihilator_intersection : simple_annihilator_intersectionType := by
  intro R _
  apply le_antisymm
  · exact le_iInf fun M => le_iInf fun _ => le_iInf fun _ =>
      le_iInf fun _ => fun x hx => annihilates_simple R M x hx
  · intro x hx
    rw [maximal_intersection R, Ideal.mem_sInf]
    intro L hL
    have : IsSimpleModule R (R ⧸ L) :=
      isSimpleModule_iff_isCoatom.mpr hL.1
    change x ∈ simpleIntersection R at hx
    simp only [simpleIntersection, Ideal.mem_iInf] at hx
    have ha : x ∈ Module.annihilator R (R ⧸ L) :=
      hx (R ⧸ L) inferInstance inferInstance inferInstance
    have hz := Module.mem_annihilator.mp ha (L.mkQ 1)
    rw [← map_smul, smul_eq_mul, mul_one] at hz
    simpa using hz

theorem two_sided : two_sidedType := by
  intro R _
  infer_instance

theorem mul_mem : mul_memType := by
  intro R _ x r hx
  exact ⟨(radical R).mul_mem_left r hx, (radical R).mul_mem_right r hx⟩

private theorem exists_left_inverse {R : Type u} [Ring R] (a : R)
    (ha : a - 1 ∈ radical R) : ∃ b, b * a = 1 := by
  obtain ⟨b, hb⟩ := Ideal.exists_mul_sub_mem_of_sub_one_mem_jacobson (I := (⊥ : Ideal R)) a
    (by simpa only [Ideal.jacobson_bot] using ha)
  exact ⟨b, sub_eq_zero.mp hb⟩

theorem one_sub_isUnit : one_sub_isUnitType := by
  intro R _ a ha
  obtain ⟨b, hb⟩ := exists_left_inverse (1 - a) (by simpa using (radical R).neg_mem ha)
  have hba : b - 1 = b * a := by
    rw [mul_sub, mul_one] at hb
    exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp hb).trans (add_comm _ _))
  have hbJ : b - 1 ∈ radical R := hba ▸ (radical R).mul_mem_left b ha
  obtain ⟨c, hc⟩ := exists_left_inverse b hbJ
  have hc_eq : c = 1 - a := left_inv_eq_right_inv hc hb
  exact isUnit_iff_exists.mpr ⟨b, hc_eq ▸ hc, hb⟩

theorem unit_criterion : unit_criterionType := by
  intro R _ x
  constructor
  · intro hx r
    exact one_sub_isUnit R (r * x) ((radical R).mul_mem_left r hx)
  · intro h
    change x ∈ Ring.jacobson R
    rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff]
    intro r
    obtain ⟨z, _, hz⟩ := isUnit_iff_exists.mp (h (-r))
    refine ⟨z, ?_⟩
    change z * r * x + z - 1 = 0
    simpa only [neg_mul, sub_neg_eq_add, mul_add, mul_one, ← mul_assoc,
      add_comm (z * r * x) z, sub_eq_zero] using hz

theorem left_eq_right : left_eq_rightType := by
  intro R _
  ext x
  change x ∈ radical R ↔ MulOpposite.op x ∈ sInf {L : Ideal Rᵐᵒᵖ | L.IsMaximal}
  rw [← Ring.jacobson_eq_sInf_isMaximal]
  change x ∈ radical R ↔ MulOpposite.op x ∈ radical Rᵐᵒᵖ
  constructor
  · intro hx
    apply (unit_criterion Rᵐᵒᵖ _).mpr
    intro r
    have hu := (one_sub_isUnit R (x * MulOpposite.unop r)
      ((radical R).mul_mem_right _ hx)).op
    simpa using hu
  · intro hx
    apply (unit_criterion R x).mpr
    intro r
    have hu := (one_sub_isUnit Rᵐᵒᵖ (MulOpposite.op x * MulOpposite.op r)
      ((radical Rᵐᵒᵖ).mul_mem_right _ hx)).unop
    simpa using hu

theorem zero_ring : zero_ringType := by
  intro R _ _
  constructor
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro L hL
    exact hL.ne_top (Subsingleton.elim _ _)
  · exact Subsingleton.elim _ _

end P103.Ch03.JacobsonRadical
