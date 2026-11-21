import MathGenome.Internal.ExtremalOptimization.Specs.P205.Ramsey.Infinite
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Choose
import Lean.Elab.Tactic.Omega

universe u v

namespace P205.Ramsey

/-- An auxiliary version for total colorings of finsets, on an arbitrary infinite
set. Only the values at cardinality `k` constrain the homogeneous set. -/
private theorem infinite_homogeneous_total {X : Type u} {C : Type v} [Finite C]
    (k : ℕ) (c : Finset X → C) (S : Set X) (hS : S.Infinite) :
    ∃ H : Set X, H ⊆ S ∧ H.Infinite ∧
      ∃ d : C, ∀ t : Finset X, (↑t : Set X) ⊆ H → t.card = k → c t = d := by
  classical
  induction k generalizing c S with
  | zero =>
      refine ⟨S, Set.Subset.rfl, hS, c ∅, ?_⟩
      intro t _ ht
      rw [Finset.card_eq_zero.mp ht]
  | succ k ih =>
      -- A state records an infinite reservoir; each step removes its chosen point.
      let State := {T : Set X // T.Infinite}
      have step (s : State) :
          ∃ x : X, x ∈ s.val ∧ ∃ t : State,
            t.val ⊆ s.val \ {x} ∧ ∃ d : C,
              ∀ U : Finset X, (↑U : Set X) ⊆ t.val → U.card = k →
                c (insert x U) = d := by
        obtain ⟨x, hx⟩ := s.property.nonempty
        obtain ⟨T, hT, hTi, d, hd⟩ :=
          ih (fun U => c (insert x U)) (s.val \ {x})
            (s.property.sdiff (Set.finite_singleton x))
        exact ⟨x, hx, ⟨T, hTi⟩, hT, d, hd⟩
      choose x hx next hnext d hd using step
      let seq : ℕ → State := fun n => Nat.rec ⟨S, hS⟩ (fun _ s => next s) n
      have seq_succ (n : ℕ) : seq (n + 1) = next (seq n) := rfl
      have nested (n : ℕ) : (seq (n + 1)).val ⊆ (seq n).val := by
        rw [seq_succ]
        exact fun _ h => (hnext (seq n) h).1
      have nested_le {i j : ℕ} (hij : i ≤ j) : (seq j).val ⊆ (seq i).val := by
        induction j, hij using Nat.le_induction with
        | base => exact Set.Subset.rfl
        | succ j _ h => exact (nested j).trans h
      let a : ℕ → X := fun n => x (seq n)
      have ha (n : ℕ) : a n ∈ (seq n).val := hx (seq n)
      have later {i j : ℕ} (hij : i < j) : a j ∈ (seq (i + 1)).val :=
        nested_le hij (ha j)
      have absent (i : ℕ) : a i ∉ (seq (i + 1)).val := by
        rw [seq_succ]
        intro h
        exact (hnext (seq i) h).2 rfl
      have a_injective : Function.Injective a := by
        intro i j hij
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact absent i (hij ▸ later hlt)
        · exact absent j (hij ▸ later hgt)
      -- Retain infinitely many indices with the same induced color.
      obtain ⟨b, hb⟩ := Finite.exists_infinite_fiber (fun n => d (seq n))
      let I : Set ℕ := {n | d (seq n) = b}
      have hI : I.Infinite := Set.infinite_coe_iff.mp hb
      refine ⟨a '' I, ?_, hI.image a_injective.injOn, b, ?_⟩
      · rintro y ⟨i, _, rfl⟩
        exact nested_le (Nat.zero_le i) (ha i)
      · intro t ht hcard
        have htne : t.Nonempty := Finset.card_pos.mp (by omega)
        have hex : ∃ i : ℕ, i ∈ I ∧ a i ∈ t := by
          obtain ⟨y, hy⟩ := htne
          obtain ⟨i, hi, hai⟩ := ht hy
          exact ⟨i, hi, hai.symm ▸ hy⟩
        -- Use the earliest index represented in `t`. No order on `X` is needed.
        let i := Nat.find hex
        have hi : i ∈ I ∧ a i ∈ t := Nat.find_spec hex
        have htail : (↑(t.erase (a i)) : Set X) ⊆ (seq (i + 1)).val := by
          intro y hy
          obtain ⟨hne, hyt⟩ := Finset.mem_erase.mp hy
          obtain ⟨j, hj, hay⟩ := ht hyt
          have hij : i ≤ j := Nat.find_min' hex ⟨hj, hay.symm ▸ hyt⟩
          have hneij : i ≠ j := by
            intro heq
            exact hne (hay ▸ congrArg a heq.symm)
          exact hay ▸ later (by omega : i < j)
        have htailcard : (t.erase (a i)).card = k := by
          have := Finset.card_erase_add_one hi.2
          omega
        have hcolor := hd (seq i) (t.erase (a i)) (by
          rw [← seq_succ]
          exact htail) htailcard
        rw [Finset.insert_erase hi.2] at hcolor
        exact hcolor.trans hi.1

/-- Infinite Ramsey on any infinite ground set. -/
theorem infinite_ramsey : Specs.InfiniteRamsey.{u} := by
  classical
  intro X k r _ hr c S hS
  let total : Finset X → Fin r := fun t =>
    if ht : t.card = k then c ⟨t, ht⟩ else ⟨0, hr⟩
  obtain ⟨H, hHS, hH, d, hd⟩ := infinite_homogeneous_total k total S hS
  refine ⟨H, hHS, hH, d, ?_⟩
  intro t ht
  simpa [total, t.property] using hd t.val ht t.property

/-- The natural-number instance, including `k = 1` and `r = 1`. -/
theorem infinite_ramsey_nat : Specs.InfiniteRamseyNat := by
  intro k r hk hr c
  obtain ⟨H, _, hH, hc⟩ :=
    infinite_ramsey ℕ k r hk hr c Set.univ Set.infinite_univ
  exact ⟨H, hH, hc⟩

/-- For a nonempty color set, a set smaller than the arity is homogeneous. -/
theorem homogeneous_of_card_lt : Specs.HomogeneousOfCardLt.{u} := by
  classical
  intro X k r hr c t ht
  refine ⟨⟨0, hr⟩, ?_⟩
  intro s hs
  have hsub : s.val ⊆ t := hs
  have := Finset.card_le_card hsub
  have := s.property
  omega

end P205.Ramsey
