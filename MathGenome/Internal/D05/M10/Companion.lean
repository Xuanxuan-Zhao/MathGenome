import MathGenome.Internal.Specs.D05.M10.Companion
import MathGenome.Internal.D05.M10.Cyclic
import MathGenome.Internal.D05.M08.CayleyHamilton
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

/-! Companion matrices of monic positive-degree polynomials, K05.10.companion.
The regular representation of the actual quotient algebra supplies the
multiplication operator, with its specified column coordinates. -/

noncomputable section

namespace D05.M10.Companion

open Polynomial

abbrev multiplication : Specs.D05.M10.Companion.multiplication_type :=
  Specs.D05.M10.Companion.multiplication_value

abbrev quotientBasis : Specs.D05.M10.Companion.quotientBasis_type :=
  Specs.D05.M10.Companion.quotientBasis_value

abbrev companionMatrix : Specs.D05.M10.Companion.companionMatrix_type :=
  Specs.D05.M10.Companion.companionMatrix_value

theorem multiplication_apply : Specs.D05.M10.Companion.multiplication_apply := by
  intro K _ d z
  rfl

theorem residue_basis : Specs.D05.M10.Companion.residue_basis := by
  intro K _ d hd _ i
  rw [map_pow]
  exact (AdjoinRoot.powerBasis' hd).basis_eq_pow i

/-- The minpoly of the quotient generator is the given monic modulus,
without imposing irreducibility or a domain structure on the quotient. -/
theorem root_minpoly {K : Type*} [Field K] (d : K[X]) (hd : d.Monic) :
    minpoly K (AdjoinRoot.root d) = d := by
  rw [AdjoinRoot.minpoly_root hd.ne_zero, hd.leadingCoeff, inv_one, map_one, mul_one]

theorem matrix_representation : Specs.D05.M10.Companion.matrix_representation := by
  intro K _ d hd _
  have hm : (AdjoinRoot.powerBasis' hd).minpolyGen = d := by
    rw [PowerBasis.minpolyGen_eq]
    exact root_minpoly d hd
  change LinearMap.toMatrix (AdjoinRoot.powerBasis' hd).basis
    (AdjoinRoot.powerBasis' hd).basis
    (Algebra.lmul K (AdjoinRoot d) (AdjoinRoot.root d)) = _
  rw [← Algebra.leftMulMatrix_apply]
  ext i j
  change Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hd).basis (AdjoinRoot.root d) i j =
    if (j : ℕ) + 1 = d.natDegree then -d.coeff (i : ℕ)
    else if (i : ℕ) = (j : ℕ) + 1 then 1 else 0
  simpa only [hm, AdjoinRoot.powerBasis'_gen, AdjoinRoot.powerBasis'_dim,
    Matrix.of_apply] using congrArg
    (fun M : Matrix (Fin d.natDegree) (Fin d.natDegree) K => M i j)
    (AdjoinRoot.powerBasis' hd).leftMulMatrix

theorem matrix_entries : Specs.D05.M10.Companion.matrix_entries := by
  intro K _ d _ _
  refine ⟨?_, ?_, ?_⟩
  · intro i j hj hij
    simp [Specs.D05.M10.Companion.companionMatrix_value, Nat.ne_of_lt hj, hij]
  · intro i j hj
    simp [Specs.D05.M10.Companion.companionMatrix_value, hj]
  · intro i j hj hij
    simp [Specs.D05.M10.Companion.companionMatrix_value, hj, hij]

theorem size_one : Specs.D05.M10.Companion.size_one := by
  intro K _ c
  have hn : (X + C c : K[X]).natDegree = 1 := natDegree_X_add_C c
  refine ⟨hn, ?_⟩
  intro i j
  have hi : (i : ℕ) = 0 := by have := i.isLt; omega
  have hj : (j : ℕ) = 0 := by have := j.isLt; omega
  simp [Specs.D05.M10.Companion.companionMatrix_value, hn, hi, hj]

/-- Polynomial evaluation commutes with the regular representation.
This formula simultaneously controls evaluation at 1 and at every residue. -/
theorem evaluation_formula : Specs.D05.M10.Companion.evaluation_formula := by
  intro K _ d p z
  change aeval (Algebra.lmul K (AdjoinRoot d) (AdjoinRoot.root d)) p z = _
  rw [Polynomial.aeval_algHom_apply, AdjoinRoot.aeval_eq]
  rfl

theorem one_cyclic : Specs.D05.M10.Companion.one_cyclic := by
  intro K _ d _ _
  apply top_unique
  intro z _
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  have h := Cyclic.eval_mem_cyclic (multiplication K d) 1 p
  change Specs.D05.M08.Evaluation.evaluation_value K (AdjoinRoot d)
    (multiplication K d) p 1 ∈ _ at h
  rw [evaluation_formula d p 1, mul_one] at h
  exact h

theorem one_annihilator_ideal : Specs.D05.M10.Companion.one_annihilator_ideal := by
  intro K _ d _ _
  ext p
  rw [Cyclic.mem_annihilator, evaluation_formula, mul_one,
    AdjoinRoot.mk_eq_zero, Ideal.mem_span_singleton]

theorem one_annihilator : Specs.D05.M10.Companion.one_annihilator := by
  intro K _ d hd hpos
  let : FiniteDimensional K (AdjoinRoot d) := hd.finite_adjoinRoot
  exact Foundations.IdealsGcd.monic_generators_eq
    (Cyclic.monic_generator (multiplication K d) 1).1 hd
    ((Cyclic.monic_generator (multiplication K d) 1).2.symm.trans
      (one_annihilator_ideal d hd hpos))

theorem annihilates_iff_one : Specs.D05.M10.Companion.annihilates_iff_one := by
  intro K _ d _ _ p
  constructor
  · intro h
    exact congrArg (fun f : Module.End K (AdjoinRoot d) => f 1) h
  · intro h
    have hp : AdjoinRoot.mk d p = 0 := by
      rw [evaluation_formula d p 1, mul_one] at h
      exact h
    ext z
    rw [evaluation_formula, hp, zero_mul, LinearMap.zero_apply]

theorem minimal_polynomial : Specs.D05.M10.Companion.minimal_polynomial := by
  intro K _ d hd _
  change minpoly K (Algebra.lmul K (AdjoinRoot d) (AdjoinRoot.root d)) = d
  rw [minpoly.algHom_eq (Algebra.lmul K (AdjoinRoot d)) Algebra.lmul_injective]
  exact root_minpoly d hd

/-- Cayley–Hamilton and equality of monic degrees identify chi with d. -/
theorem characteristic_polynomial : Specs.D05.M10.Companion.characteristic_polynomial := by
  intro K _ d hd hpos
  let : FiniteDimensional K (AdjoinRoot d) := hd.finite_adjoinRoot
  have hdvd := M08.CayleyHamilton.minpoly_divides_charpoly (multiplication K d)
  rw [minimal_polynomial d hd hpos] at hdvd
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le hd
    (M08.Charpoly.monic (multiplication K d)) hdvd
  rw [M08.Charpoly.natDegree]
  exact le_of_eq (AdjoinRoot.powerBasis' hd).finrank

theorem matrix_polynomials : Specs.D05.M10.Companion.matrix_polynomials := by
  intro K _ d hd hpos
  let : FiniteDimensional K (AdjoinRoot d) := hd.finite_adjoinRoot
  rw [← matrix_representation d hd hpos]
  constructor
  · rw [Specs.D05.M04.MatrixOfMap.matrixOfMap_value, LinearMap.minpoly_toMatrix]
    exact minimal_polynomial d hd hpos
  · rw [Specs.D05.M04.MatrixOfMap.matrixOfMap_value, LinearMap.charpoly_toMatrix]
    exact characteristic_polynomial d hd hpos

end D05.M10.Companion
