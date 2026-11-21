import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.RedundantEquationExample

namespace AdvCommAlg.Smooth.Redundant

universe u
noncomputable section
open MvPolynomial Specs.AdvCommAlg.Smooth.Redundant

theorem ideal_equality : idealEquality.{u} := by
  intro A _
  have hr : Set.range (equations A) =
      ({X 0, X 0 ^ 2} : Set (MvPolynomial (Fin 1) A)) := by
    ext p
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases j <;> simp [equations]
    · rintro (rfl | rfl)
      · exact ⟨0, by simp [equations]⟩
      · exact ⟨1, by simp [equations]⟩
  refine ⟨congrArg Ideal.span hr, ?_⟩
  rw [relationIdeal, hr]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro p hp
    rcases hp with rfl | hp
    · exact Ideal.subset_span (Set.mem_singleton _)
    · rw [Set.mem_singleton_iff] at hp
      rw [hp, pow_two]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
  · apply Ideal.span_mono
    intro p hp
    rcases hp with rfl
    exact Set.mem_insert _ _

private theorem variable_zero (A : Type u) [CommRing A] :
    Ideal.Quotient.mk (relationIdeal A) (X 0 : MvPolynomial (Fin 1) A) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span ⟨0, by simp [equations]⟩

theorem quotient_identification : quotientIdentification.{u} := by
  intro A _
  let f : MvPolynomial (Fin 1) A →ₐ[A] A := aeval (fun _ => 0)
  have hk : relationIdeal A ≤ RingHom.ker f.toRingHom := by
    rw [(ideal_equality A).2, Ideal.span_le]
    intro p hp
    rcases hp with rfl
    simp [f, RingHom.mem_ker]
  let g : Quotient A →ₐ[A] A := Ideal.Quotient.liftₐ (relationIdeal A) f (fun p hp => hk hp)
  have hcomp : (Algebra.ofId A (Quotient A)).comp f = Ideal.Quotient.mkₐ A (relationIdeal A) := by
    ext i
    fin_cases i
    simp [f, variable_zero]
  have hleft : Function.LeftInverse (algebraMap A (Quotient A)) g := by
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change algebraMap A (Quotient A) (f p) = Ideal.Quotient.mk (relationIdeal A) p
    exact DFunLike.congr_fun hcomp p
  have hright : Function.RightInverse (algebraMap A (Quotient A)) g := by
    intro a
    exact g.commutes a
  refine ⟨AlgEquiv.ofBijective g ⟨hleft.injective, hright.surjective⟩, ?_⟩
  intro p
  rfl

theorem smooth_example : smoothExample.{u} := by
  intro A _
  obtain ⟨e, _⟩ := quotient_identification A
  exact Algebra.Smooth.of_equiv e.symm

theorem matrix_entries : matrixEntries.{u} := by
  intro A _ q
  constructor
  · ext i j
    fin_cases i
    fin_cases j <;>
      simp [redundantMatrix, residueMatrix, equations, variable_zero]
  · ext i j
    fin_cases i
    fin_cases j
    simp [singleMatrix, residueMatrix]

theorem rank_comparison : rankComparison.{u} := by
  intro A _ q
  have hs : (redundantMatrix q).mulVec.Surjective := by
    intro v
    refine ⟨![v 0, 0], ?_⟩
    rw [(matrix_entries A q).1]
    ext i
    fin_cases i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hr : (redundantMatrix q).rank = 1 := by
    simpa using Matrix.mulVec_surjective_iff_rank_eq_card.mp hs
  refine ⟨hr, by omega, ?_⟩
  rw [(matrix_entries A q).2, Matrix.rank_one]
  simp

theorem warning_example : warningExample.{u} := by
  intro A _
  refine ⟨smooth_example A, (ideal_equality A).2, ?_⟩
  intro q
  exact (rank_comparison A q).2

theorem zero_case : zeroCase.{u} := by
  intro A _ _
  infer_instance

end
end AdvCommAlg.Smooth.Redundant
