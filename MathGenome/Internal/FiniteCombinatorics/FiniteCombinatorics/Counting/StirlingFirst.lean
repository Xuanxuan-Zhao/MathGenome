import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Action.PermutationCycles
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Counting.StirlingFirst
import Mathlib.GroupTheory.Perm.Option

namespace FiniteCombinatorics.StirlingFirst
open Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
universe u v
variable {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]

omit [Fintype Y] in
/-- A map preserving permutation edges preserves complete cyclic orbits. -/
theorem sameCycle_map_of_edges (σ : Perm X) (τ : Perm Y) (f : X → Y)
    (hf : ∀ x, τ.SameCycle (f x) (f (σ x))) {x y : X} (h : σ.SameCycle x y) :
    τ.SameCycle (f x) (f y) := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => exact SameCycle.refl _ _
  | succ n ih =>
    rw [pow_succ', mul_apply]
    exact ih.trans (hf _)

noncomputable def cycleQuotientEquiv (σ : Perm X) :
    Quotient (SameCycle.setoid σ) ≃ {C // C ∈ Permutation.cycles σ} := by
  classical
  let f : Quotient (SameCycle.setoid σ) → {C // C ∈ Permutation.cycles σ} :=
    Quotient.lift (fun x => ⟨Permutation.cyclicOrbit σ x,
      Permutation.cyclicOrbit_mem_cycles σ x⟩)
      (fun x y h => Subtype.ext ((Permutation.cyclicOrbit_eq_iff σ x y).2 h))
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b
    induction a using Quotient.inductionOn with | _ x =>
      induction b using Quotient.inductionOn with | _ y =>
        intro h
        exact Quotient.sound ((Permutation.cyclicOrbit_eq_iff σ x y).1
          (congrArg Subtype.val h))
  · rintro ⟨C, hC⟩
    obtain ⟨x, hx⟩ := (Permutation.mem_cycles σ C).1 hC
    exact ⟨Quotient.mk _ x, Subtype.ext hx⟩

theorem totalCycles_eq_card_quotient (σ : Perm X) :
    Permutation.totalCycles σ = Fintype.card (Quotient (SameCycle.setoid σ)) := by
  classical
  rw [Permutation.totalCycles_eq_card, Fintype.card_congr (cycleQuotientEquiv σ),
    Fintype.card_coe]

/-- An injective map on complete cyclic orbits, surjective up to the orbit relation,
induces a bijection of orbit quotients. -/
noncomputable def quotientEquivOfRepresentatives
    (σ : Perm X) (τ : Perm Y) (f : X → Y)
    (hf : ∀ x y, σ.SameCycle x y ↔ τ.SameCycle (f x) (f y))
    (hs : ∀ y, ∃ x, τ.SameCycle (f x) y) :
    Quotient (SameCycle.setoid σ) ≃ Quotient (SameCycle.setoid τ) := by
  let qf : Quotient (SameCycle.setoid σ) → Quotient (SameCycle.setoid τ) :=
    Quotient.map f (fun {_ _} h => (hf _ _).1 h)
  refine Equiv.ofBijective qf ⟨?_, ?_⟩
  · intro a b
    induction a using Quotient.inductionOn with | _ x =>
      induction b using Quotient.inductionOn with | _ y =>
        intro h
        exact Quotient.sound ((hf x y).2 (Quotient.exact h))
  · intro b
    induction b using Quotient.inductionOn with | _ y =>
      obtain ⟨x, hx⟩ := hs y
      exact ⟨Quotient.mk _ x, Quotient.sound hx⟩

omit [Fintype X] in
@[simp] theorem optionCongr_pow_some (σ : Perm X) (n : ℕ) (x : X) :
    (σ.optionCongr ^ n) (some x) = some ((σ ^ n) x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ', mul_apply, ih, optionCongr_apply, Option.map_some]

@[simp] theorem sameCycle_optionCongr_some (σ : Perm X) (x y : X) :
    SameCycle σ.optionCongr (some x) (some y) ↔ σ.SameCycle x y := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n : ℤ), by simpa using hn⟩
  · exact sameCycle_map_of_edges σ σ.optionCongr some
      (fun x => by simpa using (SameCycle.refl σ.optionCongr (some x)).apply_right)

noncomputable def optionCycleQuotientEquiv (σ : Perm X) :
    Option (Quotient (SameCycle.setoid σ)) ≃
      Quotient (SameCycle.setoid σ.optionCongr) := by
  let qf : Quotient (SameCycle.setoid σ) → Quotient (SameCycle.setoid σ.optionCongr) :=
    Quotient.map some (fun {_ _} h => (sameCycle_optionCongr_some σ _ _).2 h)
  let f : Option (Quotient (SameCycle.setoid σ)) →
      Quotient (SameCycle.setoid σ.optionCongr) :=
    fun o => o.elim (Quotient.mk _ none) qf
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b h
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b =>
        induction b using Quotient.inductionOn with | _ y =>
          have hh : SameCycle σ.optionCongr none (some y) := Quotient.exact h
          have he := hh.eq_of_left rfl
          cases he
    | some a =>
      cases b with
      | none =>
        induction a using Quotient.inductionOn with | _ x =>
          have hh : SameCycle σ.optionCongr (some x) none := Quotient.exact h
          have he := hh.eq_of_right rfl
          cases he
      | some b =>
        congr 1
        induction a using Quotient.inductionOn with | _ x =>
          induction b using Quotient.inductionOn with | _ y =>
            exact Quotient.sound ((sameCycle_optionCongr_some σ x y).1 (Quotient.exact h))
  · intro b
    induction b using Quotient.inductionOn with | _ y =>
      cases y with
      | none => exact ⟨none, rfl⟩
      | some y => exact ⟨some (Quotient.mk _ y), rfl⟩

theorem totalCycles_optionCongr (σ : Perm X) :
    Permutation.totalCycles σ.optionCongr = Permutation.totalCycles σ + 1 := by
  rw [totalCycles_eq_card_quotient, totalCycles_eq_card_quotient,
    ← Fintype.card_congr (optionCycleQuotientEquiv σ), Fintype.card_option]

/-- Insert the new point immediately before `a`. -/
noncomputable def insertPoint (σ : Perm X) (a : X) : Perm (Option X) :=
  swap none (some a) * σ.optionCongr

omit [Fintype X] in
@[simp] theorem insertPoint_none (σ : Perm X) (a : X) :
    insertPoint σ a none = some a := by simp [insertPoint]

omit [Fintype X] in
@[simp] theorem insertPoint_some (σ : Perm X) (a x : X) :
    insertPoint σ a (some x) = if σ x = a then none else some (σ x) := by
  by_cases h : σ x = a <;> simp [insertPoint, h, swap_apply_def]

theorem sameCycle_insertPoint_some (σ : Perm X) (a x y : X) :
    (insertPoint σ a).SameCycle (some x) (some y) ↔ σ.SameCycle x y := by
  have hproj : ∀ z : Option X,
      σ.SameCycle (z.getD a) ((insertPoint σ a z).getD a) := by
    intro z
    cases z with
    | none => simp only [insertPoint_none, Option.getD_none, Option.getD_some]; rfl
    | some x =>
      by_cases h : σ x = a
      · simp only [insertPoint_some, h, ite_true, Option.getD_some, Option.getD_none]
        simpa [h] using (SameCycle.refl σ x).apply_right
      · simp only [insertPoint_some, h, ite_false, Option.getD_some]
        exact (SameCycle.refl σ x).apply_right
  constructor
  · exact sameCycle_map_of_edges (insertPoint σ a) σ (fun z => z.getD a) hproj
  · apply sameCycle_map_of_edges σ (insertPoint σ a) some
    intro z
    by_cases h : σ z = a
    · have h1 : (insertPoint σ a).SameCycle (some z) none := by
        simpa [h] using (SameCycle.refl (insertPoint σ a) (some z)).apply_right
      have h2 : (insertPoint σ a).SameCycle none (some a) := by
        simpa using (SameCycle.refl (insertPoint σ a) none).apply_right
      simpa [h] using h1.trans h2
    · simpa [h] using (SameCycle.refl (insertPoint σ a) (some z)).apply_right

noncomputable def insertPointCycleQuotientEquiv (σ : Perm X) (a : X) :
    Quotient (SameCycle.setoid σ) ≃ Quotient (SameCycle.setoid (insertPoint σ a)) :=
  quotientEquivOfRepresentatives σ (insertPoint σ a) some
    (fun x y => (sameCycle_insertPoint_some σ a x y).symm)
    (by
      intro y
      cases y with
      | none =>
        refine ⟨a, ?_⟩
        have h : (insertPoint σ a).SameCycle none (some a) := by
          simpa using (SameCycle.refl (insertPoint σ a) none).apply_right
        exact h.symm
      | some y => exact ⟨y, SameCycle.refl _ _⟩)

theorem totalCycles_insertPoint (σ : Perm X) (a : X) :
    Permutation.totalCycles (insertPoint σ a) = Permutation.totalCycles σ := by
  rw [totalCycles_eq_card_quotient, totalCycles_eq_card_quotient]
  exact (Fintype.card_congr (insertPointCycleQuotientEquiv σ a)).symm

/-- The number of permutations of `X` with exactly `k` complete cycles. -/
noncomputable def count (X : Type u) [Fintype X] (k : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Perm X)).filter
    (fun σ => Permutation.totalCycles σ = k)).card

theorem count_eq_sum (k : ℕ) :
    count X k = ∑ σ : Perm X, if Permutation.totalCycles σ = k then 1 else 0 := by
  classical
  simp [count, Finset.sum_boole]

theorem count_option_succ (k : ℕ) :
    count (Option X) (k + 1) = count X k + Fintype.card X * count X (k + 1) := by
  classical
  let : DecidableEq X := Classical.decEq X
  let : DecidableEq (Option X) := Classical.decEq (Option X)
  rw [count_eq_sum]
  calc
    _ = ∑ p : Option X × Perm X,
        if Permutation.totalCycles (decomposeOption.symm p) = k + 1 then 1 else 0 :=
      (decomposeOption.symm.sum_comp _).symm
    _ = count X k + Fintype.card X * count X (k + 1) := by
      rw [Fintype.sum_prod_type]
      simp only [Fintype.sum_option]
      have hnone : ∀ σ : Perm X,
          Permutation.totalCycles (decomposeOption.symm (none, σ)) =
            Permutation.totalCycles σ + 1 := by
        intro σ
        have he : decomposeOption.symm (none, σ) = σ.optionCongr := by
          ext x
          simp
        rw [he]
        exact totalCycles_optionCongr σ
      have hsome : ∀ (a : X) (σ : Perm X),
          Permutation.totalCycles (decomposeOption.symm (some a, σ)) =
            Permutation.totalCycles σ := by
        intro a σ
        exact totalCycles_insertPoint σ a
      simp only [hnone, hsome, Nat.add_right_cancel_iff]
      simp [count]

theorem sameCycle_permCongr (e : X ≃ Y) (σ : Perm X) (x y : X) :
    (e.permCongr σ).SameCycle (e x) (e y) ↔ σ.SameCycle x y := by
  constructor
  · intro h
    have hh := sameCycle_map_of_edges (e.permCongr σ) σ e.symm
      (fun z => by simpa using (SameCycle.refl σ (e.symm z)).apply_right) h
    simpa using hh
  · exact sameCycle_map_of_edges σ (e.permCongr σ) e
      (fun z => by simpa using (SameCycle.refl (e.permCongr σ) (e z)).apply_right)

theorem totalCycles_permCongr (e : X ≃ Y) (σ : Perm X) :
    Permutation.totalCycles (e.permCongr σ) = Permutation.totalCycles σ := by
  rw [totalCycles_eq_card_quotient, totalCycles_eq_card_quotient]
  symm
  apply Fintype.card_congr
  exact quotientEquivOfRepresentatives σ (e.permCongr σ) e
    (fun x y => (sameCycle_permCongr e σ x y).symm)
    (fun y => ⟨e.symm y, by simp only [apply_symm_apply]; rfl⟩)

theorem count_congr (e : X ≃ Y) (k : ℕ) : count X k = count Y k := by
  classical
  let : DecidableEq X := Classical.decEq X
  let : DecidableEq Y := Classical.decEq Y
  rw [count_eq_sum, count_eq_sum]
  apply Fintype.sum_equiv e.permCongr
  intro σ
  rw [totalCycles_permCongr]

theorem totalCycles_pos [Nonempty X] (σ : Perm X) : 0 < Permutation.totalCycles σ := by
  obtain ⟨x⟩ := ‹Nonempty X›
  rw [Permutation.totalCycles_eq_card]
  exact Finset.card_pos.mpr ⟨Permutation.cyclicOrbit σ x,
    Permutation.cyclicOrbit_mem_cycles σ x⟩

theorem count_zero_of_nonempty [Nonempty X] : count X 0 = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro σ _ hσ
  exact (Nat.ne_of_gt (totalCycles_pos σ)) hσ

@[simp] theorem count_empty [IsEmpty X] (k : ℕ) : count X k = if k = 0 then 1 else 0 := by
  classical
  by_cases hk : k = 0
  · subst k
    simp [count]
  · simp [count, hk, Ne.symm hk]

/-- The permutation interpretation of the unsigned first Stirling numbers,
for any finite type, including the empty type. -/
theorem count_eq_natStirlingFirst (k : ℕ) :
    count X k = Nat.stirlingFirst (Fintype.card X) k := by
  classical
  have hall : ∀ (α : Type u) [Fintype α], ∀ k,
      count α k = Nat.stirlingFirst (Fintype.card α) k := by
    intro α hα
    refine Fintype.induction_empty_option
      (P := fun β _ => ∀ k, count β k = Nat.stirlingFirst (Fintype.card β) k)
      ?_ ?_ ?_ α
    · intro β γ _ e ih k
      let : Fintype β := Fintype.ofEquiv γ e.symm
      rw [← count_congr e, ← Fintype.card_congr e]
      exact ih k
    · intro k
      cases k <;> simp
    · intro β _ ih k
      cases k with
      | zero => simp [count_zero_of_nonempty]
      | succ k =>
        rw [count_option_succ, ih k, ih (k + 1), Fintype.card_option,
          Nat.stirlingFirst_succ_succ]
        exact Nat.add_comm _ _
  exact hall X k

/-- The unsigned first Stirling array, defined by counting permutations of `Fin n`. -/
noncomputable def stirlingFirst (n k : ℕ) : ℕ := count (Fin n) k

theorem stirlingFirst_eq_natStirlingFirst (n k : ℕ) :
    stirlingFirst n k = Nat.stirlingFirst n k := by
  simpa [stirlingFirst] using (count_eq_natStirlingFirst (X := Fin n) k)

theorem count_eq_stirlingFirst (k : ℕ) :
    count X k = stirlingFirst (Fintype.card X) k := by
  rw [count_eq_natStirlingFirst, stirlingFirst_eq_natStirlingFirst]

@[simp] theorem stirlingFirst_zero_zero : stirlingFirst 0 0 = 1 := by
  rw [stirlingFirst_eq_natStirlingFirst, Nat.stirlingFirst_zero]

@[simp] theorem stirlingFirst_zero_succ (k : ℕ) : stirlingFirst 0 (k + 1) = 0 := by
  rw [stirlingFirst_eq_natStirlingFirst, Nat.stirlingFirst_zero_succ]

@[simp] theorem stirlingFirst_succ_zero (n : ℕ) : stirlingFirst (n + 1) 0 = 0 := by
  rw [stirlingFirst_eq_natStirlingFirst, Nat.stirlingFirst_succ_zero]

theorem stirlingFirst_eq_zero_of_lt (n k : ℕ) (h : n < k) : stirlingFirst n k = 0 := by
  rw [stirlingFirst_eq_natStirlingFirst]
  exact Nat.stirlingFirst_eq_zero_of_lt h

/-- A permutation either has the new point as its own cycle, or has it inserted
into one of the old cycles at one of the `n` available positions. -/
theorem stirlingFirst_succ_succ (n k : ℕ) :
    stirlingFirst (n + 1) (k + 1) = stirlingFirst n k + n * stirlingFirst n (k + 1) := by
  simp only [stirlingFirst_eq_natStirlingFirst, Nat.stirlingFirst_succ_succ]
  exact Nat.add_comm _ _

end FiniteCombinatorics.StirlingFirst
