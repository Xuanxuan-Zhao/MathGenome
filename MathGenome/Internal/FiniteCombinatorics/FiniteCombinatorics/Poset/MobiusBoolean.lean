import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Poset.MobiusProduct
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Poset.MobiusBoolean
import Mathlib.Data.Nat.Choose.Sum

/-! Boolean subset intervals, `paper.tex`, p204:W09. We use all subsets
of a fixed finite set, so no finiteness assumption on the ambient type
is needed. Alternating sums on a Boolean interval are powerset sums;
their cancellation proves the defining Möbius recurrence. -/

noncomputable section
open Classical
open scoped FiniteCombinatorics.Poset

namespace FiniteCombinatorics.Poset.IncidenceFunction

private theorem signed_sum_boolean_interval {α : Type*} (U : Finset α)
    (x z : BooleanPoset U) (h : x ≤ z) :
    (∑ y ∈ Finset.Icc x z, (-1 : ℤ) ^ (y.val \ x.val).card) =
      if x = z then 1 else 0 := by
  have hs : (∑ y ∈ Finset.Icc x z, (-1 : ℤ) ^ (y.val \ x.val).card) =
      ∑ v ∈ (z.val \ x.val).powerset, (-1 : ℤ) ^ v.card := by
    refine Finset.sum_bij (fun y _ => y.val \ x.val) ?_ ?_ ?_ ?_
    · intro y hy
      apply Finset.mem_powerset.mpr
      intro a ha
      obtain ⟨hay, hax⟩ := Finset.mem_sdiff.mp ha
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_Icc.mp hy).2 hay, hax⟩
    · intro y hy w hw he
      apply Subtype.ext
      have hyx : x.val ⊆ y.val := (Finset.mem_Icc.mp hy).1
      have hwx : x.val ⊆ w.val := (Finset.mem_Icc.mp hw).1
      calc
        y.val = x.val ∪ (y.val \ x.val) := (Finset.union_sdiff_of_subset hyx).symm
        _ = x.val ∪ (w.val \ x.val) := by rw [he]
        _ = w.val := Finset.union_sdiff_of_subset hwx
    · intro v hv
      have hv' := Finset.mem_powerset.mp hv
      have hvz : v ⊆ z.val := fun a ha => (Finset.mem_sdiff.mp (hv' ha)).1
      let y : BooleanPoset U := ⟨x.val ∪ v,
        Finset.mem_powerset.mpr (Finset.union_subset
          (Finset.mem_powerset.mp x.property)
          (hvz.trans (Finset.mem_powerset.mp z.property)))⟩
      refine ⟨y, Finset.mem_Icc.mpr ⟨Finset.subset_union_left,
        Finset.union_subset h hvz⟩, ?_⟩
      change (x.val ∪ v) \ x.val = v
      ext a
      have hn : a ∈ v → a ∉ x.val := fun ha => (Finset.mem_sdiff.mp (hv' ha)).2
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto
    · intro y hy
      rfl
  rw [hs, Finset.sum_powerset_neg_one_pow_card]
  have he : z.val \ x.val = ∅ ↔ x = z := by
    rw [Finset.sdiff_eq_empty_iff_subset]
    exact ⟨fun hz => le_antisymm h hz, fun he => he ▸ Finset.Subset.rfl⟩
  simp only [he]

/-- The Boolean formula in any subinterval of the finite powerset poset. -/
theorem mobius_boolean_interval_int {α : Type*} (U : Finset α)
    (x z : BooleanPoset U) (h : x ≤ z) :
    mobius ℤ (BooleanPoset U) x z = (-1 : ℤ) ^ (z.val \ x.val).card := by
  let f : IncidenceFunction ℤ (BooleanPoset U) :=
    { toFun := fun x z => if x ≤ z then (-1 : ℤ) ^ (z.val \ x.val).card else 0
      eq_zero_of_not_le' := fun _ _ h => ite_eq_right h }
  have hd : ∀ x, f x x = 1 := by
    intro x
    simp [f]
  have hr : ∀ x z, x < z → f x z = -∑ y ∈ Finset.Ico x z, f x y := by
    intro x z hxz
    have hs : (∑ y ∈ Finset.Icc x z, f x y) = 0 := by
      calc
        (∑ y ∈ Finset.Icc x z, f x y) =
            ∑ y ∈ Finset.Icc x z, (-1 : ℤ) ^ (y.val \ x.val).card := by
          apply Finset.sum_congr rfl
          intro y hy
          exact ite_eq_left (Finset.mem_Icc.mp hy).1
        _ = 0 := by
          rw [signed_sum_boolean_interval U x z hxz.le, ite_eq_right hxz.ne]
    rw [Finset.Icc_eq_cons_Ico hxz.le, Finset.sum_cons] at hs
    exact eq_neg_of_add_eq_zero_left hs
  have hf := mobius_unique ℤ (BooleanPoset U) f hd hr
  have hv := congrArg (fun g : IncidenceFunction ℤ (BooleanPoset U) => g x z) hf
  exact hv.symm.trans (ite_eq_left h)

/-- Integer Möbius values on `S ⊆ T`, in the finite poset of subsets of `T`. -/
theorem mobius_boolean_int (α : Type*) (S T : Finset α) (h : S ⊆ T) :
    mobius ℤ (BooleanPoset T)
      ⟨S, Finset.mem_powerset.mpr h⟩
      ⟨T, Finset.mem_powerset.mpr Finset.Subset.rfl⟩ =
        (-1 : ℤ) ^ (T \ S).card :=
  mobius_boolean_interval_int T _ _ h

/-- Ring coefficients are obtained by mapping the integer Möbius values. -/
theorem mobius_boolean_intCast (R α : Type*) [CommRing R]
    (S T : Finset α) (h : S ⊆ T) :
    (mobius ℤ (BooleanPoset T)
      ⟨S, Finset.mem_powerset.mpr h⟩
      ⟨T, Finset.mem_powerset.mpr Finset.Subset.rfl⟩ : R) =
    mobius R (BooleanPoset T)
      ⟨S, Finset.mem_powerset.mpr h⟩
      ⟨T, Finset.mem_powerset.mpr Finset.Subset.rfl⟩ :=
  mobius_intCast R (BooleanPoset T) _ _

/-- The Boolean formula over every commutative coefficient ring. -/
theorem mobius_boolean (R α : Type*) [CommRing R]
    (S T : Finset α) (h : S ⊆ T) :
    mobius R (BooleanPoset T)
      ⟨S, Finset.mem_powerset.mpr h⟩
      ⟨T, Finset.mem_powerset.mpr Finset.Subset.rfl⟩ =
        (-1 : R) ^ (T \ S).card := by
  rw [← mobius_boolean_intCast R α S T h, mobius_boolean_int α S T h,
    Int.cast_pow, Int.cast_neg, Int.cast_one]

end FiniteCombinatorics.Poset.IncidenceFunction
