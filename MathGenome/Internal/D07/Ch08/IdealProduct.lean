import MathGenome.Internal.Specs.D07.Ch08.IdealProduct
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Products of two-sided ideals, K07.08.ideal_product. -/

universe u

namespace D07.Ch08.IdealProduct

open Specs.D07.Ch08.IdealProduct

/-- The canonical product consists precisely of finite sums of ordered
products. This identification already holds for left ideals. -/
theorem mem_product_iff_finite_sum {R : Type u} [Ring R] (I J : Ideal R) (x : R) :
    x ∈ I * J ↔ FiniteProductSum I J x := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha b hb
      exact ⟨[(⟨a, ha⟩, ⟨b, hb⟩)], by simp⟩
    · intro a b ha hb
      obtain ⟨as, has⟩ := ha
      obtain ⟨bs, hbs⟩ := hb
      exact ⟨as ++ bs, by simp [has, hbs]⟩
  · rintro ⟨terms, rfl⟩
    induction terms with
    | nil => exact (I * J).zero_mem
    | cons p ps ih =>
      exact (I * J).add_mem (Ideal.mul_mem_mul p.1.property p.2.property) ih

theorem productDescription : ProductDescription.{u} := by
  intro R _ I J _ hJ
  let : J.IsTwoSided := hJ
  exact ⟨inferInstance, mem_product_iff_finite_sum I J⟩

theorem productClosure : ProductClosure.{u} := by
  intro R _ I J hI hJ
  obtain ⟨hP, hmem⟩ := productDescription R I J hI hJ
  refine ⟨(hmem 0).mp (I * J).zero_mem, ?_, ?_, ?_, ?_⟩
  · intro x y hx hy
    exact (hmem _).mp ((I * J).add_mem ((hmem _).mpr hx) ((hmem _).mpr hy))
  · intro x hx
    exact (hmem _).mp ((I * J).neg_mem ((hmem _).mpr hx))
  · intro r x hx
    exact (hmem _).mp ((I * J).mul_mem_left r ((hmem _).mpr hx))
  · intro x r hx
    exact (hmem _).mp (hP.mul_mem_of_left r ((hmem _).mpr hx))

theorem productLeIntersection : ProductLeIntersection.{u} := by
  intro R _ I J hI _
  let : I.IsTwoSided := hI
  exact Ideal.mul_le_inf

theorem leftDistributivity : LeftDistributivity.{u} := by
  intro R _ I J K _ _ _
  exact Ideal.mul_sup I J K

theorem rightDistributivity : RightDistributivity.{u} := by
  intro R _ I J K _ _ _
  exact Ideal.sup_mul I J K

theorem associativity : Associativity.{u} := by
  intro R _ I J K _ _ _
  exact Ideal.mul_assoc

theorem tripleProductDescription : TripleProductDescription.{u} := by
  intro R _ I J K _ _ _ x
  have h : x ∈ (I * J) * K ↔ FiniteTripleSum I J K x := by
    constructor
    · intro hx
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro a ha c hc
        change FiniteTripleSum I J K (a * c)
        refine Submodule.smul_induction_on ha ?_ ?_
        · intro a ha b hb
          exact ⟨[(⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩)], by simp⟩
        · intro a b ha hb
          obtain ⟨as, has⟩ := ha
          obtain ⟨bs, hbs⟩ := hb
          exact ⟨as ++ bs, by simp [has, hbs, add_mul]⟩
      · intro a b ha hb
        obtain ⟨as, has⟩ := ha
        obtain ⟨bs, hbs⟩ := hb
        exact ⟨as ++ bs, by simp [has, hbs]⟩
    · rintro ⟨terms, rfl⟩
      induction terms with
      | nil => exact ((I * J) * K).zero_mem
      | cons p ps ih =>
        exact ((I * J) * K).add_mem
          (Ideal.mul_mem_mul (Ideal.mul_mem_mul p.1.property p.2.1.property)
            p.2.2.property) ih
  exact ⟨h, by rw [← Ideal.mul_assoc]; exact h⟩

theorem integerCounterexample : IntegerCounterexample := by
  dsimp [IntegerCounterexample]
  refine ⟨?_, inf_idem _, ?_⟩
  · simpa using Ideal.span_singleton_mul_span_singleton (2 : ℤ) 2
  · intro h
    have h2 : (2 : ℤ) ∈ (Ideal.span {4} : Ideal ℤ) := by
      rw [h, inf_idem]
      exact Ideal.mem_span_singleton_self 2
    norm_num [Ideal.mem_span_singleton] at h2

/- The triangular example uses the inherited ring structure of a genuine
unital subring of M₂(ℤ), with no assumed commutativity. -/
private def triangularSubring : Subring (Matrix (Fin 2) (Fin 2) ℤ) where
  carrier := {A | A 1 0 = 0}
  zero_mem' := rfl
  one_mem' := by simp
  add_mem' := by
    intro A B hA hB
    change A 1 0 = 0 at hA
    change B 1 0 = 0 at hB
    change A 1 0 + B 1 0 = 0
    rw [hA, hB, add_zero]
  neg_mem' := by
    intro A hA
    change A 1 0 = 0 at hA
    change -(A 1 0) = 0
    rw [hA, neg_zero]
  mul_mem' := by
    intro A B hA hB
    change A 1 0 = 0 at hA
    change B 1 0 = 0 at hB
    change (A * B) 1 0 = 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, hA, hB]

private abbrev Triangular := ↥triangularSubring

private theorem lowerEntry (a : Triangular) : a.val 1 0 = 0 := a.property

/-- The top row is a two-sided ideal in the triangular ring. -/
private def topRow : Ideal Triangular where
  carrier := {a | a.val 1 1 = 0}
  zero_mem' := rfl
  add_mem' := by
    intro a b ha hb
    change a.val 1 1 = 0 at ha
    change b.val 1 1 = 0 at hb
    change a.val 1 1 + b.val 1 1 = 0
    rw [ha, hb, add_zero]
  smul_mem' := by
    intro r a ha
    change a.val 1 1 = 0 at ha
    change (r.val * a.val) 1 1 = 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, lowerEntry, ha]

private theorem topRow_twoSided : topRow.IsTwoSided := by
  constructor
  intro a r ha
  change (a.val * r.val) 1 1 = 0
  change a.val 1 1 = 0 at ha
  simp [Matrix.mul_apply, Fin.sum_univ_two, lowerEntry, ha]

/-- The right column is a two-sided ideal in the triangular ring. -/
private def rightColumn : Ideal Triangular where
  carrier := {a | a.val 0 0 = 0}
  zero_mem' := rfl
  add_mem' := by
    intro a b ha hb
    change a.val 0 0 = 0 at ha
    change b.val 0 0 = 0 at hb
    change a.val 0 0 + b.val 0 0 = 0
    rw [ha, hb, add_zero]
  smul_mem' := by
    intro r a ha
    change a.val 0 0 = 0 at ha
    change (r.val * a.val) 0 0 = 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, lowerEntry, ha]

private theorem rightColumn_twoSided : rightColumn.IsTwoSided := by
  constructor
  intro a r ha
  change (a.val * r.val) 0 0 = 0
  change a.val 0 0 = 0 at ha
  simp [Matrix.mul_apply, Fin.sum_univ_two, lowerEntry, ha]

private def e00 : Triangular := ⟨Matrix.single 0 0 1, by change (Matrix.single 0 0 (1 : ℤ)) 1 0 = 0; simp⟩
private def e01 : Triangular := ⟨Matrix.single 0 1 1, by change (Matrix.single 0 1 (1 : ℤ)) 1 0 = 0; simp⟩

private theorem reversedProduct_eq_bot : rightColumn * topRow = ⊥ := by
  apply le_antisymm _ bot_le
  apply Ideal.mul_le.mpr
  intro a ha b hb
  rw [Ideal.mem_bot]
  apply Subtype.ext
  change a.val 0 0 = 0 at ha
  change b.val 1 1 = 0 at hb
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, lowerEntry, ha, hb]

theorem noncommutativeCounterexample : NoncommutativeCounterexample := by
  refine ⟨Triangular, inferInstance, topRow, rightColumn,
    topRow_twoSided, rightColumn_twoSided, ?_⟩
  have h00 : e00 ∈ topRow := by change (Matrix.single 0 0 (1 : ℤ)) 1 1 = 0; simp
  have h01 : e01 ∈ rightColumn := by change (Matrix.single 0 1 (1 : ℤ)) 0 0 = 0; simp
  have hp : e00 * e01 = e01 := by
    apply Subtype.ext
    change Matrix.single 0 0 (1 : ℤ) * Matrix.single 0 1 1 = Matrix.single 0 1 1
    simp
  have hm : e01 ∈ topRow * rightColumn := hp ▸ Ideal.mul_mem_mul h00 h01
  intro heq
  rw [heq, reversedProduct_eq_bot, Ideal.mem_bot] at hm
  have hentry := congrArg (fun a : Triangular => a.val 0 1) hm
  norm_num [e01] at hentry

end D07.Ch08.IdealProduct
