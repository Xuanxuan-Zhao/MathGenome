import MathGenome.Internal.Specs.D07.Ch08.IdealGeneration
import MathGenome.Internal.D07.Ch08.IdealDefinition

/-! K07.08.ideal_generation: finite sums and the universal property. -/

universe u
namespace D07.Ch08.IdealGeneration

open scoped BigOperators
open Specs.D07.Ch08.IdealGeneration
open Specs.D07.Ch08.IdealDefinition

variable {R : Type u} [Ring R] {S : Set R}

/-- Concatenating two finite presentations gives a presentation of their sum. -/
lemma twoSidedSums_add {x y : R} (hx : TwoSidedSums S x) (hy : TwoSidedSums S y) :
    TwoSidedSums S (x + y) := by
  obtain ⟨m, r, s, t, hs, rfl⟩ := hx
  obtain ⟨n, r', s', t', hs', rfl⟩ := hy
  refine ⟨m + n, Fin.addCases r r', Fin.addCases s s', Fin.addCases t t', ?_, ?_⟩
  · intro i
    exact Fin.addCases (fun j => by simpa using hs j)
      (fun j => by simpa using hs' j) i
  · simp [Fin.sum_univ_add]

lemma twoSidedSums_zero : TwoSidedSums S (0 : R) := by
  refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_⟩
  · intro i
    exact i.elim0
  · simp

lemma twoSidedSums_generator {x : R} (hx : x ∈ S) : TwoSidedSums S x := by
  exact ⟨1, fun _ => 1, fun _ => x, fun _ => 1, fun _ => hx, by simp⟩

lemma twoSidedSums_neg {x : R} (hx : TwoSidedSums S x) : TwoSidedSums S (-x) := by
  obtain ⟨m, r, s, t, hs, rfl⟩ := hx
  exact ⟨m, fun i => -r i, s, t, hs, by simp [Finset.sum_neg_distrib]⟩

lemma twoSidedSums_mul_left (a : R) {x : R} (hx : TwoSidedSums S x) :
    TwoSidedSums S (a * x) := by
  obtain ⟨m, r, s, t, hs, rfl⟩ := hx
  exact ⟨m, fun i => a * r i, s, t, hs, by simp [Finset.mul_sum, mul_assoc]⟩

lemma twoSidedSums_mul_right (b : R) {x : R} (hx : TwoSidedSums S x) :
    TwoSidedSums S (x * b) := by
  obtain ⟨m, r, s, t, hs, rfl⟩ := hx
  exact ⟨m, r, s, fun i => t i * b, hs, by simp [Finset.sum_mul, mul_assoc]⟩

theorem generatedIdealFormula : GeneratedIdealFormula.{u} := by
  intro R _ S x
  constructor
  · intro hx
    induction hx using TwoSidedIdeal.span_induction with
    | mem x hx => exact twoSidedSums_generator hx
    | zero => exact twoSidedSums_zero
    | add x y hx hy ihx ihy => exact twoSidedSums_add ihx ihy
    | neg x hx ih => exact twoSidedSums_neg ih
    | left_absorb a x hx ih => exact twoSidedSums_mul_left a ih
    | right_absorb b x hx ih => exact twoSidedSums_mul_right b ih
  · rintro ⟨m, r, s, t, hs, rfl⟩
    apply sum_mem
    intro i _
    exact (TwoSidedIdeal.span S).mul_mem_right _ _
      ((TwoSidedIdeal.span S).mul_mem_left _ _ (TwoSidedIdeal.subset_span (hs i)))

theorem leastTwoSidedIdeal : LeastTwoSidedIdeal.{u} := by
  intro R _ S
  refine ⟨(D07.Ch08.IdealDefinition.twoSidedIdealCharacterization R _).mp inferInstance,
    TwoSidedIdeal.subset_span, ?_⟩
  intro H hH
  obtain ⟨I, rfl⟩ := (D07.Ch08.IdealDefinition.leftIdealCharacterization R H).mp hH.1
  let : I.IsTwoSided :=
    (D07.Ch08.IdealDefinition.twoSidedIdealCharacterization R I).mpr hH
  constructor
  · intro h x hx
    exact h (TwoSidedIdeal.subset_span hx)
  · intro h x hx
    have h' : S ⊆ (I.toTwoSided : Set R) := fun y hy => by simpa using h hy
    have hx' := ((TwoSidedIdeal.span_le (I := I.toTwoSided)).mpr h') hx
    simpa using hx'

theorem intersectionCharacterization : IntersectionCharacterization.{u} := by
  intro R _ S
  apply TwoSidedIdeal.ext
  intro x
  simpa only [TwoSidedIdeal.mem_sInf, Set.mem_ofPred_eq] using
    (TwoSidedIdeal.mem_span_iff (s := S) (x := x))

/-- Forgetting the last factors is valid when all of them equal one. -/
lemma leftSums_to_twoSidedSums {x : R} (hx : LeftSums S x) : TwoSidedSums S x := by
  obtain ⟨m, r, s, hs, rfl⟩ := hx
  exact ⟨m, r, s, fun _ => 1, hs, by simp⟩

/-- Appending presentations of sums in a left ideal. -/
lemma leftSums_add {x y : R} (hx : LeftSums S x) (hy : LeftSums S y) :
    LeftSums S (x + y) := by
  obtain ⟨m, r, s, hs, rfl⟩ := hx
  obtain ⟨n, r', s', hs', rfl⟩ := hy
  refine ⟨m + n, Fin.addCases r r', Fin.addCases s s', ?_, ?_⟩
  · intro i
    exact Fin.addCases (fun j => by simpa using hs j)
      (fun j => by simpa using hs' j) i
  · simp [Fin.sum_univ_add]

lemma leftSums_zero : LeftSums S (0 : R) := by
  refine ⟨0, Fin.elim0, Fin.elim0, ?_, ?_⟩
  · intro i
    exact i.elim0
  · simp

lemma leftSums_generator {x : R} (hx : x ∈ S) : LeftSums S x := by
  exact ⟨1, fun _ => 1, fun _ => x, fun _ => hx, by simp⟩

lemma leftSums_mul_left (a : R) {x : R} (hx : LeftSums S x) : LeftSums S (a * x) := by
  obtain ⟨m, r, s, hs, rfl⟩ := hx
  exact ⟨m, fun i => a * r i, s, hs, by simp [Finset.mul_sum, mul_assoc]⟩

theorem leftIdealFormula : LeftIdealFormula.{u} := by
  intro R _ S x
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact leftSums_generator hx
    | zero => exact leftSums_zero
    | add x y hx hy ihx ihy => exact leftSums_add ihx ihy
    | smul a x hx ih => exact leftSums_mul_left a ih
  · rintro ⟨m, r, s, hs, rfl⟩
    exact (Ideal.span S).sum_mem fun i _ => (Ideal.span S).mul_mem_left _
      (Ideal.subset_span (hs i))

theorem commutativeFormula : CommutativeFormula.{u} := by
  intro R _ S x
  constructor
  · intro hx
    obtain ⟨m, r, s, t, hs, rfl⟩ := (generatedIdealFormula R S x).mp hx
    refine ⟨m, fun i => r i * t i, s, hs, ?_⟩
    apply Finset.sum_congr rfl
    intro i _
    exact mul_right_comm _ _ _
  · intro hx
    exact (generatedIdealFormula R S x).mpr (leftSums_to_twoSidedSums hx)

theorem emptyGeneration : EmptyGeneration.{u} := by
  intro R _
  refine ⟨le_antisymm ?_ bot_le, Ideal.span_empty⟩
  exact TwoSidedIdeal.span_le.mpr (Set.empty_subset _)

theorem singleProductsNotAddClosed : SingleProductsNotAddClosed := by
  refine ⟨⟨1, 2, 1, by simp, by norm_num⟩,
    ⟨1, 3, 1, by simp, by norm_num⟩, ?_⟩
  rintro ⟨r, s, t, hs, heq⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl
  · have h : (2 : ℤ) ∣ 5 := ⟨r * t, by calc
      5 = r * 2 * t := heq
      _ = 2 * (r * t) := by ring⟩
    norm_num at h
  · have h : (3 : ℤ) ∣ 5 := ⟨r * t, by calc
      5 = r * 3 * t := heq
      _ = 3 * (r * t) := by ring⟩
    norm_num at h

end D07.Ch08.IdealGeneration

