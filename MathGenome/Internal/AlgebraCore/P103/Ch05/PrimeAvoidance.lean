import MathGenome.Internal.AlgebraCore.Specs.P103.Ch05.PrimeAvoidance
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Algebra.Algebra.Basic
import Lean.Elab.Tactic.Omega

namespace P103.Ch05

/-- In a nonempty index type, a set with at most two indices fits in a pair.
The two indices may coincide, and need not belong to the set. -/
lemma exists_subset_pair_of_card_le_two {ι : Type*} [DecidableEq ι] [Nonempty ι]
    (s : Finset ι) (h : s.card ≤ 2) : ∃ a b, s ⊆ {a, b} := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨Classical.arbitrary ι, Classical.arbitrary ι, by simp⟩
  obtain ⟨a, ha⟩ := hs
  have he : (s.erase a).card ≤ 1 := by
    rw [Finset.card_erase_of_mem ha]
    omega
  obtain ⟨b, hb⟩ := Finset.card_le_one_iff_subset_singleton.mp he
  refine ⟨a, b, ?_⟩
  intro i hi
  by_cases hia : i = a
  · simp [hia]
  · have hib := hb (Finset.mem_erase.mpr ⟨hia, hi⟩)
    simp only [Finset.mem_singleton] at hib
    simp [hib]

/-- Finite prime avoidance with at most two nonprime ideals, including lists of
length one or two and families with repetitions or contained or unit ideals. -/
theorem finitePrimeAvoidance : Specs.P103.Ch05.finitePrimeAvoidanceType := by
  classical
  intro R _ n hn J I hcount hcover
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨a, b, hab⟩ := exists_subset_pair_of_card_le_two
    (Finset.univ.filter (fun i => ¬ (I i).IsPrime)) hcount
  have hp : ∀ i ∈ (Finset.univ : Finset (Fin n)), i ≠ a → i ≠ b → (I i).IsPrime := by
    intro i _ hia hib
    by_contra hi
    have hm := hab (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    exact hm.elim hia hib
  obtain ⟨i, _, hi⟩ := (Ideal.subset_union_prime a b hp).mp (by simpa using hcover)
  exact ⟨i, hi⟩

/-- Finite avoidance when the ring contains an infinite field. Ideals are
subspaces for the scalar action induced by the specified unital embedding. -/
theorem infiniteFieldAvoidance : Specs.P103.Ch05.infiniteFieldAvoidanceType := by
  classical
  intro R _ k _ _ f _hf n _hn J I hcover
  letI : Algebra k R := f.toAlgebra
  let U : Submodule k R := J.restrictScalars k
  let p (i : Fin n) : Submodule k U :=
    ((I i).restrictScalars k).comap U.subtype
  by_contra! hnone
  have hp : ∀ i, p i ≠ ⊤ := by
    intro i heq
    apply hnone i
    intro x hx
    have hm : (⟨x, hx⟩ : U) ∈ p i := by rw [heq]; trivial
    exact hm
  obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover x.property)
  exact hx i hi

end P103.Ch05
