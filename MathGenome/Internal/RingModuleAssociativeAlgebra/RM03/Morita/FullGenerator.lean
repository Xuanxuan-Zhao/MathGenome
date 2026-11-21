import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Morita.FullGenerator
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.RingTheory.TwoSidedIdeal.BigOperators

/-! The full-idempotent criterion for a generator of right modules. -/

universe u v

namespace RM03.Morita

open MulOpposite

variable {R : Type u} [Ring R]

private theorem mul_mem_span_singleton (a x b : R) :
    a * x * b ∈ TwoSidedIdeal.span ({x} : Set R) := by
  let I := TwoSidedIdeal.span ({x} : Set R)
  exact I.mul_mem_right (a * x) b
    (I.mul_mem_left a x (TwoSidedIdeal.subset_span (Set.mem_singleton x)))

private theorem exists_list_of_mem_span_singleton {x z : R}
    (hz : z ∈ TwoSidedIdeal.span ({x} : Set R)) :
    ∃ t : List (R × R), (t.map fun c => c.1 * x * c.2).sum = z := by
  let term : R × R → R := fun c => c.1 * x * c.2
  change ∃ t : List (R × R), (t.map term).sum = z
  refine TwoSidedIdeal.span_induction (p := fun y _ => ∃ t : List (R × R), (t.map term).sum = y)
    ?_ ?_ ?_ ?_ ?_ ?_ hz
  · intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact ⟨[(1, 1)], by simp [term]⟩
  · exact ⟨[], rfl⟩
  · rintro _ _ _ _ ⟨t, rfl⟩ ⟨s, rfl⟩
    exact ⟨t ++ s, by rw [List.map_append, List.sum_append]⟩
  · rintro _ _ ⟨t, rfl⟩
    refine ⟨t.map (fun c => (-c.1, c.2)), ?_⟩
    rw [List.map_map]
    change (t.map fun c => (-c.1) * x * c.2).sum = _
    simpa only [term, neg_mul, neg_one_mul, one_mul] using
      (List.sum_map_mul_left t term (-1))
  · rintro a _ _ ⟨t, rfl⟩
    refine ⟨t.map (fun c => (a * c.1, c.2)), ?_⟩
    rw [List.map_map]
    change (t.map fun c => (a * c.1) * x * c.2).sum = _
    simpa only [term, mul_assoc] using
      (List.sum_map_mul_left t term a)
  · rintro b _ _ ⟨t, rfl⟩
    refine ⟨t.map (fun c => (c.1, c.2 * b)), ?_⟩
    rw [List.map_map]
    change (t.map fun c => c.1 * x * (c.2 * b)).sum = _
    simpa only [term, mul_assoc] using
      (List.sum_map_mul_right t term b)

/-- Fullness is equivalent to a finite expression for 1 as a sum of products r e s. -/
theorem full_iff_sum (e : Idempotent R) :
    IsFull e ↔ ∃ (n : ℕ) (r s : Fin n → R), (∑ i, r i * e.val * s i) = 1 := by
  rw [IsFull, ← TwoSidedIdeal.one_mem_iff]
  constructor
  · intro h
    obtain ⟨t, ht⟩ := exists_list_of_mem_span_singleton h
    refine ⟨t.length, fun i => (t[i.val]).1, fun i => (t[i.val]).2, ?_⟩
    rw [← List.sum_ofFn, List.ofFn_getElem_eq_map t (fun c => c.1 * e.val * c.2)]
    exact ht
  · rintro ⟨n, r, s, hs⟩
    rw [← hs]
    exact TwoSidedIdeal.finsetSum_mem _ _ _ fun i _ => mul_mem_span_singleton (r i) e.val (s i)

/-- A full idempotent gives a surjection from a direct sum of copies of eR onto any right module. -/
theorem full_quotients (e : Idempotent R) (he : IsFull e) (M : Type v)
    [AddCommGroup M] [Module Rᵐᵒᵖ M] :
    ∃ (J : Type (max u v)) (f : (J →₀ rightIdeal e) →ₗ[Rᵐᵒᵖ] M),
      Function.Surjective f := by
  classical
  obtain ⟨n, r, s, hs⟩ := (full_iff_sum e).mp he
  let g : M × ULift.{u} (Fin n) → rightIdeal e →ₗ[Rᵐᵒᵖ] M := fun c =>
    { toFun := fun x => op (r c.2.down * x.val) • c.1
      map_add' := by
        intro x y
        change op (r c.2.down * (x.val + y.val)) • c.1 = _
        rw [mul_add, op_add, add_smul]
      map_smul' := by
        intro a x
        change op (r c.2.down * (x.val * a.unop)) • c.1 =
          a • (op (r c.2.down * x.val) • c.1)
        rw [← mul_assoc, op_mul, mul_smul]
        rfl }
  refine ⟨M × ULift.{u} (Fin n), Finsupp.lsum ℤ g, ?_⟩
  intro m
  refine ⟨∑ i : Fin n, Finsupp.single (m, ULift.up i) (op (s i) • rightGenerator e), ?_⟩
  calc
    _ = ∑ i, op (r i * e.val * s i) • m := by
      simp only [map_sum, Finsupp.lsum_single, g, LinearMap.coe_mk, AddHom.coe_mk,
        rightIdeal_op_smul_val, unop_op, rightGenerator, mul_assoc]
    _ = m := by rw [← Finset.sum_smul, ← Finset.op_sum, hs, op_one, one_smul]

/-- The right ideal eR is a generator exactly when e is full. -/
theorem generator_iff_full (e : Idempotent R) :
    P103.Morita.IsGenerator R (rightIdeal e) ↔ IsFull e := by
  classical
  constructor
  · intro h
    obtain ⟨J, f, hf⟩ := h R
    obtain ⟨w, hw⟩ := hf 1
    rw [IsFull, ← TwoSidedIdeal.one_mem_iff, ← hw]
    clear hw
    let I := TwoSidedIdeal.span ({e.val} : Set R)
    change f w ∈ I
    induction w using Finsupp.induction_linear with
    | zero => rw [map_zero]; exact I.zero_mem
    | add w z hw hz => rw [map_add]; exact I.add_mem hw hz
    | single j x =>
      let g : rightIdeal e →ₗ[Rᵐᵒᵖ] R := f.comp (Finsupp.lsingle j)
      change g x ∈ I
      have hx : op x.val • rightGenerator e = x := Subtype.ext x.property
      have hg := g.map_smul (op x.val) (rightGenerator e)
      rw [hx] at hg
      change g x = g (rightGenerator e) * x.val at hg
      have hx' : g x = g (rightGenerator e) * e.val * x.val := by
        rw [mul_assoc, x.property, hg]
      rw [hx']
      exact mul_mem_span_singleton (g (rightGenerator e)) e.val x.val
  · intro h M _ _
    exact full_quotients e h M

end RM03.Morita
