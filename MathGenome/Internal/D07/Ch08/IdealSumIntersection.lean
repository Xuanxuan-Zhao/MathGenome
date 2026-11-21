import MathGenome.Internal.Specs.D07.Ch08.IdealSumIntersection
import Mathlib.Tactic.NormNum

/-! The ideal lattice, K07.08.ideal_sum_intersection (paper.tex:1357–1366). -/

universe u

namespace D07.Ch08.IdealSumIntersection

open Specs.D07.Ch08.IdealSumIntersection

theorem arbitraryIntersections : ArbitraryIntersections.{u} := by
  intro R _ S hS
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · intro a r ha
    apply Ideal.mem_sInf.mpr
    intro I hI
    exact (hS I hI).mul_mem_of_left r (Ideal.mem_sInf.mp ha hI)
  · intro x
    exact Ideal.mem_sInf
  · intro K
    exact le_sInf_iff

theorem emptyIntersection : EmptyIntersection.{u} := by
  intro R _
  simp

theorem binaryIntersection : BinaryIntersection.{u} := by
  intro R _ I J hI hJ
  refine ⟨⟨?_⟩, fun _ => Iff.rfl, fun _ => le_inf_iff⟩
  intro a r ha
  exact ⟨hI.mul_mem_of_left r ha.1, hJ.mul_mem_of_left r ha.2⟩

theorem sumDescription : SumDescription.{u} := by
  intro R _ I J hI hJ
  refine ⟨⟨?_⟩, fun _ => Submodule.mem_sup⟩
  intro a r ha
  obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.mp ha
  rw [add_mul]
  exact Submodule.mem_sup.mpr
    ⟨i * r, hI.mul_mem_of_left r hi, j * r, hJ.mul_mem_of_left r hj, rfl⟩

theorem sumLeastUpperBound : SumLeastUpperBound.{u} := by
  intro R _ I J _ _
  exact ⟨le_sup_left, le_sup_right, fun _ => sup_le_iff⟩

theorem unionCounterexample : UnionCounterexample := by
  dsimp [UnionCounterexample]
  have h2 : (2 : ℤ) ∈ (↑(Ideal.span {2} : Ideal ℤ) : Set ℤ) ∪
      ↑(Ideal.span {3} : Ideal ℤ) :=
    Or.inl (Ideal.mem_span_singleton_self 2)
  have h3 : (3 : ℤ) ∈ (↑(Ideal.span {2} : Ideal ℤ) : Set ℤ) ∪
      ↑(Ideal.span {3} : Ideal ℤ) :=
    Or.inr (Ideal.mem_span_singleton_self 3)
  have h5 : (5 : ℤ) ∉ (↑(Ideal.span {2} : Ideal ℤ) : Set ℤ) ∪
      ↑(Ideal.span {3} : Ideal ℤ) := by
    norm_num [Set.mem_union, Ideal.mem_span_singleton]
  refine ⟨h2, h3, h5, ?_⟩
  rintro ⟨K, hK⟩
  have h2K : (2 : ℤ) ∈ K := by rw [← hK] at h2; exact h2
  have h3K : (3 : ℤ) ∈ K := by rw [← hK] at h3; exact h3
  apply h5
  rw [← hK]
  exact K.add_mem h2K h3K

theorem chainUnion : ChainUnion.{u} := by
  intro R _ S hne hchain hS
  have hmem : ∀ x : R, x ∈ sSup S ↔ ∃ I ∈ S, x ∈ I :=
    fun _ => Submodule.mem_sSup_of_directed hne hchain.directedOn
  refine ⟨sSup S, ⟨?_⟩, ?_, fun _ => sSup_le_iff⟩
  · intro a r ha
    obtain ⟨I, hI, haI⟩ := (hmem a).mp ha
    exact (hmem (a * r)).mpr ⟨I, hI, (hS I hI).mul_mem_of_left r haI⟩
  · ext x
    simp only [Set.mem_sUnion, Set.mem_image]
    constructor
    · intro hx
      obtain ⟨I, hI, hxI⟩ := (hmem x).mp hx
      exact ⟨I, ⟨I, hI, rfl⟩, hxI⟩
    · rintro ⟨_, ⟨I, hI, rfl⟩, hxI⟩
      exact (hmem x).mpr ⟨I, hI, hxI⟩

end D07.Ch08.IdealSumIntersection
