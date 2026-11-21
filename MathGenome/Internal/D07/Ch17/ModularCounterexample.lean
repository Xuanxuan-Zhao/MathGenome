import MathGenome.Internal.Specs.D07.Ch17.ModularCounterexample
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The modular Jordan-block counterexample, including its complete invariant
subspace lattice. All coordinates and subspaces are those fixed in the Specs. -/
namespace D07.Ch17.ModularCounterexample

open Specs.D07.Ch17.ModularCounterexample
open scoped Matrix

@[simp] theorem nilpotent_apply (p : ℕ) (v : Space p) :
    nilpotentValue p v = ![v 1, 0] := by
  funext i
  fin_cases i <;>
    simp [nilpotentValue, dotProduct, Fin.sum_univ_two]

@[simp] theorem jordan_apply (p : ℕ) (v : Space p) :
    jordanValue p v = ![v 0 + v 1, v 1] := by
  funext i
  fin_cases i <;> simp [jordanValue, Matrix.vecHead, Matrix.vecTail]

theorem matrix_identification : MatrixIdentification := by
  intro p
  constructor
  · simp [nilpotentValue]
  · simp only [jordanValue, map_add, LinearMap.toMatrix'_one,
      nilpotentValue, LinearMap.toMatrix'_toLin']
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem nilpotent_square : NilpotentSquare := by
  intro p
  apply LinearMap.ext
  intro v
  simp [pow_two, Module.End.mul_apply]

theorem jordan_powers : JordanPowers := by
  intro p a
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, ih]
    apply LinearMap.ext
    intro v
    funext i
    fin_cases i <;>
      simp [Module.End.mul_apply, Matrix.vecHead, Matrix.vecTail, Nat.cast_add,
        jordanValue] <;> ring

theorem jordan_prime_power : JordanPrimePower := by
  intro p
  rw [jordan_powers]
  simp

theorem action_formula : ActionFormula := by
  intro p g v
  change (1 + g.toAdd • nilpotentValue p) v = _
  funext i
  fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail]

theorem generator_and_integer_powers : GeneratorAndIntegerPowers := by
  intro p
  have hk (k : ℤ) :
      (actionValue p).toHomUnits (Multiplicative.ofAdd (k : ZMod p)) =
      ((actionValue p).toHomUnits (Multiplicative.ofAdd (1 : ZMod p))) ^ k := by
    have hc : Multiplicative.ofAdd (k : ZMod p) =
        (Multiplicative.ofAdd (1 : ZMod p)) ^ k := by
      rw [← ofAdd_zsmul]
      simp
    rw [hc, map_zpow]
  refine ⟨?_, hk, ?_⟩
  · change 1 + (1 : ZMod p) • nilpotentValue p = _
    simp [jordanValue]
  · intro k m
    rw [← hk, ← hk]
    simp

@[simp] theorem mem_line_iff (p : ℕ) (v : Space p) :
    v ∈ lineValue p ↔ v 1 = 0 := by
  rw [lineValue, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    simp [e₁]
  · intro h
    refine ⟨v 0, ?_⟩
    funext i
    fin_cases i <;> simp [e₁, h]

@[simp] theorem first_basis_mem (p : ℕ) : e₁ p ∈ lineValue p := by
  simp [e₁]

@[simp] theorem first_basis_ne_zero (p : ℕ) [Fact p.Prime] : e₁ p ≠ 0 := by
  intro h
  have := congrFun h 0
  simpa [e₁] using this

@[simp] theorem second_basis_not_mem (p : ℕ) [Fact p.Prime] :
    e₂ p ∉ lineValue p := by
  simp [e₂]

theorem line_ne_bot (p : ℕ) [Fact p.Prime] : lineValue p ≠ ⊥ := by
  intro h
  have hm := first_basis_mem p
  rw [h, Submodule.mem_bot] at hm
  exact first_basis_ne_zero p hm

theorem line_ne_top (p : ℕ) [Fact p.Prime] : lineValue p ≠ ⊤ := by
  intro h
  exact second_basis_not_mem p (h ▸ Submodule.mem_top)

theorem line_fixed (p : ℕ) (g : Cyclic p) (v : Space p)
    (hv : v ∈ lineValue p) : actionValue p g v = v := by
  have hv1 := (mem_line_iff p v).mp hv
  rw [action_formula]
  funext i
  fin_cases i <;> simp [hv1]

theorem line_invariant (p : ℕ) [Fact p.Prime] : Invariant p (lineValue p) := by
  intro g v hv
  rwa [line_fixed p g v hv]

theorem space_dimension (p : ℕ) [Fact p.Prime] :
    Module.finrank (ZMod p) (Space p) = 2 := by
  simp [Space, Module.finrank_pi]

theorem line_dimension (p : ℕ) [Fact p.Prime] :
    Module.finrank (ZMod p) (lineValue p) = 1 :=
  finrank_span_singleton (first_basis_ne_zero p)

theorem invariant_fixed_line : InvariantFixedLine := by
  intro p _
  exact ⟨space_dimension p, line_dimension p, line_ne_bot p, line_ne_top p,
    line_invariant p, line_fixed p⟩

/-- Subtracting x from the generator action extracts the nilpotent part. -/
theorem nilpotent_mem_of_invariant (p : ℕ) [Fact p.Prime]
    (W : Submodule (ZMod p) (Space p)) (hW : Invariant p W)
    (v : Space p) (hv : v ∈ W) : nilpotentValue p v ∈ W := by
  have hm := W.sub_mem (hW (Multiplicative.ofAdd (1 : ZMod p)) v hv) hv
  simpa [actionValue, add_sub_cancel_left] using hm

/-- Every nonzero invariant subspace contains the same nonzero vector e₁.
If the second coordinate is nonzero, use N(v); otherwise rescale v itself. -/
theorem line_le_of_nonzero_invariant (p : ℕ) [Fact p.Prime]
    (W : Submodule (ZMod p) (Space p)) (hW : Invariant p W) (h0 : W ≠ ⊥) :
    lineValue p ≤ W := by
  obtain ⟨v, hv, hv0⟩ := W.ne_bot_iff.mp h0
  suffices he : e₁ p ∈ W by
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr he)
  by_cases h1 : v 1 = 0
  · have hc : v 0 ≠ 0 := by
      intro hc
      apply hv0
      funext i
      fin_cases i <;> simp [hc, h1]
    have he : (v 0)⁻¹ • v = e₁ p := by
      funext i
      fin_cases i <;> simp [e₁, h1, hc]
    exact he ▸ W.smul_mem (v 0)⁻¹ hv
  · have he : (v 1)⁻¹ • nilpotentValue p v = e₁ p := by
      funext i
      fin_cases i <;> simp [e₁, h1]
    exact he ▸ W.smul_mem (v 1)⁻¹ (nilpotent_mem_of_invariant p W hW v hv)

theorem unique_invariant_line : UniqueInvariantLine := by
  intro p _ W
  constructor
  · rintro ⟨hW, hd⟩
    have h0 : W ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hd
      exact Nat.zero_ne_one hd
    exact (Submodule.eq_of_le_of_finrank_eq
      (line_le_of_nonzero_invariant p W hW h0) (by rw [line_dimension, hd])).symm
  · rintro rfl
    exact ⟨line_invariant p, line_dimension p⟩

theorem invariant_subspaces : InvariantSubspaces := by
  intro p _ W
  constructor
  · intro hW
    by_cases h0 : W = ⊥
    · exact Or.inl h0
    by_cases ht : W = ⊤
    · exact Or.inr (Or.inr ht)
    have hlt := Submodule.finrank_lt ht
    rw [space_dimension] at hlt
    have hpos : Module.finrank (ZMod p) W ≠ 0 := by
      intro hz
      exact h0 (Submodule.finrank_eq_zero.mp hz)
    have hd : Module.finrank (ZMod p) W = 1 := by omega
    exact Or.inr (Or.inl ((unique_invariant_line p W).mp ⟨hW, hd⟩))
  · rintro (rfl | rfl | rfl)
    · intro g v hv
      have : v = 0 := by simpa only [Submodule.mem_bot] using hv
      simp [this]
    · exact line_invariant p
    · intro _ _ _
      exact Submodule.mem_top

theorem no_invariant_complement : NoInvariantComplement := by
  intro p _ W hW hc
  by_cases h0 : W = ⊥
  · subst W
    exact line_ne_top p (eq_top_of_isCompl_bot hc)
  · have hle := line_le_of_nonzero_invariant p W hW h0
    exact line_ne_bot p (hc.disjoint.mono_right hle).eq_bot_of_self

theorem reducible_indecomposable : ReducibleIndecomposable := by
  intro p _
  refine ⟨⟨lineValue p, line_invariant p, line_ne_bot p, line_ne_top p⟩, ?_⟩
  rintro ⟨A, B, hA, hB, hA0, hB0, hc⟩
  have hdis : Disjoint (lineValue p) (lineValue p) :=
    hc.disjoint.mono (line_le_of_nonzero_invariant p A hA hA0)
      (line_le_of_nonzero_invariant p B hB hB0)
  exact line_ne_bot p hdis.eq_bot_of_self

end D07.Ch17.ModularCounterexample
