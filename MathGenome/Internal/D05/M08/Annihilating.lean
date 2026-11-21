import MathGenome.Internal.Specs.D05.M08.Annihilating
import MathGenome.Internal.D05.M08.Evaluation
import MathGenome.Internal.D05.M03.HomDimension
import Mathlib.Algebra.Polynomial.BigOperators

/-! K05.08.annihilating: the annihilator ideal and its nonzero finite relation. -/

noncomputable section
namespace D05.M08.Annihilating
open scoped BigOperators

/-- Polynomials annihilating T form the kernel ideal of its evaluation map. -/
def annihilator (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) : Ideal (Polynomial K) :=
  RingHom.ker (Evaluation.evaluation K V T).toRingHom

theorem mem_annihilator : Specs.D05.M08.Annihilating.mem_annihilator := by
  intro K V _ _ _ T p
  rfl

theorem add_mem : Specs.D05.M08.Annihilating.add_mem := by
  intro K V _ _ _ T p q hp hq
  exact (annihilator K V T).add_mem hp hq

theorem neg_mem : Specs.D05.M08.Annihilating.neg_mem := by
  intro K V _ _ _ T p hp
  exact (annihilator K V T).neg_mem hp

theorem mul_mem : Specs.D05.M08.Annihilating.mul_mem := by
  intro K V _ _ _ T p q hp
  exact (annihilator K V T).mul_mem_left q hp

theorem end_dimension : Specs.D05.M08.Annihilating.end_dimension := by
  intro K V _ _ _ _
  simpa [pow_two] using
    D05.M03.HomDimension.hom_dimension (Module.finBasis K V) (Module.finBasis K V)

theorem powers_dependent : Specs.D05.M08.Annihilating.powers_dependent := by
  intro K V _ _ _ _ T h
  have hc := h.fintype_card_le_finrank
  rw [Fintype.card_fin, end_dimension] at hc
  exact (Nat.not_succ_le_self _) hc

theorem powers_relation : Specs.D05.M08.Annihilating.powers_relation := by
  intro K V _ _ _ _ T
  obtain ⟨a, ha, j, hj⟩ := Fintype.not_linearIndependent_iff.mp (powers_dependent T)
  exact ⟨a, ⟨j, hj⟩, ha⟩

theorem exists_nonzero_annihilator :
    Specs.D05.M08.Annihilating.exists_nonzero_annihilator := by
  intro K V _ _ _ _ T
  classical
  let N := (Module.finrank K V) ^ 2
  obtain ⟨a, ⟨j, hj⟩, ha⟩ := powers_relation T
  let p : Polynomial K := ∑ i : Fin (N + 1), Polynomial.monomial (i : ℕ) (a i)
  have hcoeff (i : Fin (N + 1)) : p.coeff (i : ℕ) = a i := by
    simp [p, Polynomial.coeff_monomial, Fin.val_inj]
  refine ⟨p, ?_, ?_, ?_⟩
  · intro hp
    apply hj
    rw [← hcoeff j, hp, Polynomial.coeff_zero]
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    exact (Polynomial.natDegree_monomial_le (a i)).trans (Nat.le_of_lt_succ i.isLt)
  · apply (mem_annihilator T p).mpr
    change Polynomial.aeval T p = 0
    simpa [p, map_sum, Polynomial.aeval_monomial, Algebra.smul_def] using ha

theorem ideal_ne_bot : Specs.D05.M08.Annihilating.ideal_ne_bot := by
  intro K V _ _ _ _ T h
  obtain ⟨p, hp, _, hm⟩ := exists_nonzero_annihilator T
  rw [h] at hm
  exact hp hm

theorem zero_dimension : Specs.D05.M08.Annihilating.zero_dimension := by
  intro K V _ _ _ _ T h
  have hzero := D05.M02.Dimension.dimension_zero_iff_zero_space.mp h
  let : Subsingleton V := ⟨fun x y => (hzero x).trans (hzero y).symm⟩
  refine ⟨(Evaluation.zero_space T 1).1, fun p => (Evaluation.zero_space T p).2, ?_⟩
  apply top_unique
  intro p _
  exact (mem_annihilator T p).mpr (Evaluation.zero_space T p).2

end D05.M08.Annihilating
