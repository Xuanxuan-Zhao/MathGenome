import MathGenome.Internal.Specs.D05.M09.SimultaneousDiagonal.Finite
import MathGenome.Internal.D05.M09.MinpolyCriterion
import MathGenome.Internal.D05.M09.CommutantInvariance
import MathGenome.Internal.D05.M08.RestrictionMinpoly
import Mathlib.Algebra.Polynomial.Splits

/-! Finite simultaneous diagonalization over the original field. -/

noncomputable section

namespace D05.M09.SimultaneousDiagonal.Finite

open Polynomial

/-- A monic divisor of a product of distinct linear factors is itself such
a product. Divisibility bounds its root multiset by the original finite set. -/
theorem monic_divisor_distinct_linear_factors {K : Type*} [Field K]
    (p : K[X]) (hp : p.Monic) (s : Finset K)
    (hdiv : p ∣ ∏ a ∈ s, (X - C a)) :
    ∃ t : Finset K, p = ∏ a ∈ t, (X - C a) := by
  classical
  have hne : (∏ a ∈ s, (X - C a)) ≠ 0 := (monic_prod_X_sub_C id s).ne_zero
  have hsplit : (∏ a ∈ s, (X - C a)).Splits := by
    apply Splits.prod
    intro a _
    exact Splits.X_sub_C a
  have hroots : p.roots ≤ s.val := by
    simpa only [roots_prod_X_sub_C] using roots.le_of_dvd hne hdiv
  have hn : p.roots.Nodup := Multiset.nodup_of_le hroots s.nodup
  refine ⟨⟨p.roots, hn⟩, ?_⟩
  exact (hsplit.of_dvd hne hdiv).eq_prod_roots_of_monic hp

/-- Use annihilator divisibility, then apply the distinct-linear-factor
criterion to the restriction's own minimal polynomial. -/
theorem restriction_diagonalizable :
    Specs.D05.M09.SimultaneousDiagonal.Finite.restriction_diagonalizable := by
  intro K V _ _ _ _ U S hU hS
  obtain ⟨s, hs⟩ := MinpolyCriterion.diagonalizable_iff_distinct_linear_factors S |>.mp hS
  have hd := M08.RestrictionMinpoly.restriction_minpoly_dvd U S hU
  change minpoly K (S.restrict hU) ∣ minpoly K S at hd
  change minpoly K S = _ at hs
  rw [hs] at hd
  apply (MinpolyCriterion.diagonalizable_iff_distinct_linear_factors (S.restrict hU)).mpr
  exact monic_divisor_distinct_linear_factors _ (M08.Minpoly.monic _) s hd

theorem eigenspace_restriction_diagonalizable :
    Specs.D05.M09.SimultaneousDiagonal.Finite.eigenspace_restriction_diagonalizable := by
  intro K V _ _ _ _ S T hST hS a
  have hU := CommutantInvariance.eigenspace_invariant S T hST.eq a
  exact ⟨hU, restriction_diagonalizable (T.eigenspace a) S hU hS⟩

/-- Extract a finite basis from the spanning set of common eigenvectors.
Zero may belong to the spanning set; independence excludes it from the basis. -/
theorem eigenbasis_of_common_eigenvectors_span
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : ι → Module.End K V)
    (hspan : ⊤ ≤ Submodule.span K {v : V | ∀ i, ∃ a : K, T i v = a • v}) :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) K V) (μ : ι → Fin d → K),
      ∀ i j, T i (b j) = μ i j • b j := by
  classical
  let S : Set V := {v | ∀ i, ∃ a : K, T i v = a • v}
  let b := Module.Basis.ofSpan hspan
  let I := LinearIndepOn.extend (linearIndepOn_empty K id) (Set.empty_subset S)
  have : Finite I := b.linearIndependent.finite
  let _ : Fintype I := Fintype.ofFinite I
  have hb : ∀ j, ∀ i, ∃ a : K, T i (b j) = a • b j := by
    intro j
    exact Module.Basis.ofSpan_subset hspan ⟨j, rfl⟩
  choose eigenvalue hEigenvalue using hb
  let e := Fintype.equivFin I
  refine ⟨Fintype.card I, b.reindex e, (fun i j => eigenvalue (e.symm j) i), ?_⟩
  intro i j
  simpa using hEigenvalue (e.symm j) i

/-- Induct on the number of operators. A basis vector of the first operator
lies in one of its eigenspaces. Apply induction to the remaining restrictions
there, then use their basis to show this vector lies in the common span. -/
theorem fin_common_eigenbasis {K : Type*} [Field K] (n : ℕ) :
    ∀ {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (T : Fin n → Module.End K V),
      (∀ i j, Commute (T i) (T j)) →
      (∀ i, Diagonalizable.diagonalizable K V (T i)) →
      ∃ (d : ℕ) (b : Module.Basis (Fin d) K V) (μ : Fin n → Fin d → K),
        ∀ i j, T i (b j) = μ i j • b j := by
  classical
  induction n with
  | zero =>
    intro V _ _ _ T _ _
    exact ⟨Module.finrank K V, Module.finBasis K V, (fun i => Fin.elim0 i),
      fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro V _ _ _ T hC hD
    obtain ⟨d, b, μ, hb⟩ := hD 0
    apply eigenbasis_of_common_eigenvectors_span T
    let S : Set V := {v | ∀ i, ∃ a : K, T i v = a • v}
    have hle : Submodule.span K (Set.range b) ≤ Submodule.span K S := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      let U := (T 0).eigenspace (μ k)
      have hU (i : Fin n) : ∀ x ∈ U, T i.succ x ∈ U :=
        CommutantInvariance.eigenspace_invariant (T i.succ) (T 0) (hC i.succ 0).eq (μ k)
      let R : Fin n → Module.End K U := fun i => (T i.succ).restrict (hU i)
      have hRC : ∀ i j, Commute (R i) (R j) := by
        intro i j
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        exact congrArg (fun f : Module.End K V => f (x : V)) (hC i.succ j.succ).eq
      have hRD : ∀ i, Diagonalizable.diagonalizable K U (R i) := by
        intro i
        exact restriction_diagonalizable U (T i.succ) (hU i) (hD i.succ)
      obtain ⟨e, c, ν, hc⟩ := ih R hRC hRD
      have hcS (j : Fin e) : (c j : V) ∈ S := by
        intro i
        refine Fin.cases ?_ (fun l => ?_) i
        · exact ⟨μ k, Module.End.mem_eigenspace_iff.mp (c j).property⟩
        · exact ⟨ν l j, congrArg (fun x : U => (x : V)) (hc l j)⟩
      have hcspan : Submodule.span K (Set.range c) ≤
          (Submodule.span K S).comap U.subtype := by
        apply Submodule.span_le.mpr
        rintro _ ⟨j, rfl⟩
        exact Submodule.subset_span (hcS j)
      exact hcspan (c.mem_span ⟨b k, Module.End.mem_eigenspace_iff.mpr (hb k)⟩)
    rw [b.span_eq] at hle
    exact hle

theorem finite_common_eigenbasis :
    Specs.D05.M09.SimultaneousDiagonal.Finite.finite_common_eigenbasis := by
  intro K V ι _ _ _ _ _ T hC hD
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  have hC' (i j : Fin (Fintype.card ι)) :
      Commute (T (e.symm i)) (T (e.symm j)) := by
    by_cases hij : e.symm i = e.symm j
    · rw [hij]
    · exact hC hij
  obtain ⟨d, b, μ, hb⟩ := fin_common_eigenbasis (K := K) (Fintype.card ι)
    (fun i => T (e.symm i)) hC' (fun i => hD (e.symm i))
  exact ⟨d, b, (fun i j => μ (e i) j), fun i j => by simpa using hb (e i) j⟩

theorem empty_family_common_eigenbasis :
    Specs.D05.M09.SimultaneousDiagonal.Finite.empty_family_common_eigenbasis := by
  intro K V ι _ _ _ _ _ T
  exact ⟨Module.finrank K V, Module.finBasis K V, (fun i => isEmptyElim i),
    fun i => isEmptyElim i⟩

theorem zero_space_common_eigenbasis :
    Specs.D05.M09.SimultaneousDiagonal.Finite.zero_space_common_eigenbasis := by
  intro K V ι _ _ _ _ _ T
  exact ⟨Module.Basis.empty V, (fun _ j => Fin.elim0 j), fun _ j => Fin.elim0 j⟩

end D05.M09.SimultaneousDiagonal.Finite
