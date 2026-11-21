import MathGenome.Internal.Specs.D05.M10.Semisimple
import MathGenome.Internal.D05.M08.Minpoly
import MathGenome.Internal.D05.M09.MinpolyCriterion
import MathGenome.Internal.D05.M10.Semisimple.ScalarExtension

/-! K05.10.semisimple: invariant complements and the minimal polynomial.
Mathlib's polynomial-module semisimplicity criterion applies over arbitrary
fields. We connect it to the paper's pointwise invariant-subspace definition
and express squarefreeness explicitly as absence of irreducible squares.
The scalar-extension paragraph is proved in the imported prerequisite module.
-/

noncomputable section

namespace D05.M10.Semisimple

open Polynomial

/-- The paper's invariant-complement definition, also for arbitrary dimension. -/
abbrev semisimple (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) : Prop :=
  Specs.D05.M10.Semisimple.semisimple_value K V T

/-- Check the pointwise predicate against Mathlib's actual invariant lattice. -/
theorem semisimple_iff_isSemisimple {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (T : Module.End K V) :
    semisimple K V T ↔ T.IsSemisimple := by
  exact Module.End.isSemisimple_iff.symm

theorem invariant_iff_polynomial_stable :
    Specs.D05.M10.Semisimple.invariant_iff_polynomial_stable := by
  intro K V _ _ _ T U
  constructor
  · intro h p v hv
    exact Polynomial.aeval_apply_smul_mem_of_le_comap hv p T h
  · intro h v hv
    simpa only [aeval_X] using h X v hv

theorem semisimple_iff_module : Specs.D05.M10.Semisimple.semisimple_iff_module := by
  intro K V _ _ _ T
  exact semisimple_iff_isSemisimple T

theorem semisimple_iff_squarefree :
    Specs.D05.M10.Semisimple.semisimple_iff_squarefree := by
  intro K V _ _ _ _ T
  rw [show Specs.D05.M10.Semisimple.semisimple_value K V T ↔ T.IsSemisimple from
    semisimple_iff_isSemisimple T]
  constructor
  · exact Module.End.IsSemisimple.minpoly_squarefree
  · intro h
    exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero h (minpoly.aeval K T)

theorem semisimple_iff_no_repeated_irreducible :
    Specs.D05.M10.Semisimple.semisimple_iff_no_repeated_irreducible := by
  intro K V _ _ _ _ T
  exact (semisimple_iff_squarefree T).trans
    (squarefree_iff_no_irreducibles (M08.Minpoly.ne_zero T))

theorem zero_space : Specs.D05.M10.Semisimple.zero_space := by
  intro K V _ _ _ _ _ T
  refine ⟨(semisimple_iff_squarefree T).mpr ?_, M08.Minpoly.zero_space T⟩
  rw [M08.Minpoly.zero_space T]
  exact squarefree_one

/-- Monic squarefree polynomials have a literal finite set of monic
irreducible factors. Normalization removes the irrelevant unit factor. -/
theorem semisimple_iff_distinct_irreducible_factors :
    Specs.D05.M10.Semisimple.semisimple_iff_distinct_irreducible_factors := by
  intro K V _ _ _ _ T
  classical
  rw [semisimple_iff_squarefree T]
  constructor
  · intro h
    let factors := UniqueFactorizationMonoid.normalizedFactors (minpoly K T)
    have hn : factors.Nodup :=
      (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
        (M08.Minpoly.ne_zero T)).mp h
    refine ⟨⟨factors, hn⟩, ?_, ?_⟩
    · intro p hp
      have hi := (Polynomial.mem_normalizedFactors_iff (M08.Minpoly.ne_zero T)).mp hp
      exact ⟨hi.2.1, hi.1⟩
    · have he := Polynomial.leadingCoeff_mul_prod_normalizedFactors (minpoly K T)
      have hm : (minpoly K T).Monic := M08.Minpoly.monic T
      rw [hm.leadingCoeff, C_1, one_mul] at he
      simp only [Finset.prod, Multiset.map_id']
      change minpoly K T = (UniqueFactorizationMonoid.normalizedFactors (minpoly K T)).prod
      exact he.symm
  · rintro ⟨s, hs, he⟩
    rw [he]
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hpq
      apply (hs p hp).2.isRelPrime_iff_not_dvd.mpr
      intro hd
      exact hpq (Polynomial.eq_of_monic_of_associated (hs p hp).1 (hs q hq).1
        ((hs p hp).2.associated_of_dvd (hs q hq).2 hd))
    · intro p hp
      exact (hs p hp).2.squarefree

/-- Repeated roots in the base field would give a squared linear divisor.
This implication does not assume a perfect field. -/
theorem roots_nodup_of_squarefree {K : Type*} [Field K]
    {p : Polynomial K} (hp : Squarefree p) : p.roots.Nodup := by
  classical
  apply Multiset.nodup_iff_count_le_one.mpr
  intro a
  rw [Polynomial.count_roots]
  by_contra hn
  have htwo : 2 ≤ rootMultiplicity a p := Nat.succ_le_of_lt (lt_of_not_ge hn)
  have hd : (X - C a) ^ 2 ∣ p := (le_rootMultiplicity_iff hp.ne_zero).mp htwo
  exact (irreducible_X_sub_C a).not_isUnit (hp (X - C a) (by simpa [pow_two] using hd))

/-- Splitting is the precise extra condition that turns distinct irreducibles
into distinct linear factors over the original field. -/
theorem distinct_linear_factors_iff_squarefree_and_splits {K : Type*} [Field K]
    {p : Polynomial K} (hm : p.Monic) :
    (∃ s : Finset K, p = ∏ a ∈ s, (X - C a)) ↔ Squarefree p ∧ p.Splits := by
  classical
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨(separable_prod_X_sub_C_iff'.mpr (fun _ _ _ _ h => h)).squarefree,
      Splits.prod (fun a _ => Splits.X_sub_C a)⟩
  · rintro ⟨hs, ht⟩
    refine ⟨⟨p.roots, roots_nodup_of_squarefree hs⟩, ?_⟩
    exact ht.eq_prod_roots_of_monic hm

theorem diagonalizable_iff_semisimple_and_splits :
    Specs.D05.M10.Semisimple.diagonalizable_iff_semisimple_and_splits := by
  intro K V _ _ _ _ T
  rw [M09.MinpolyCriterion.diagonalizable_iff_distinct_linear_factors T,
    semisimple_iff_squarefree T]
  exact distinct_linear_factors_iff_squarefree_and_splits (M08.Minpoly.monic T)

end D05.M10.Semisimple
