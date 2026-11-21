import MathGenome.Internal.Specs.D07.Ch19.ResultantDefinition

universe u
namespace D07.Ch19.ResultantDefinition
open Polynomial Module
open Specs.D07.Ch19.ResultantDefinition

theorem rowBlocks : RowBlocks.{u} := by
  intro R _ f g n m
  constructor
  · intro i
    have h : (⟨i.val, by omega⟩ : Fin (n + m)).rev = i.rev.natAdd n := by
      apply Fin.ext
      simp only [Fin.val_rev, Fin.val_natAdd]
      omega
    simp [rowPolynomial, h, Fin.val_rev, Nat.sub_sub, Nat.add_comm]
  · intro i
    have h : (⟨m + i.val, by omega⟩ : Fin (n + m)).rev = i.rev.castAdd m := by
      apply Fin.ext
      simp only [Fin.val_rev, Fin.val_castAdd]
      omega
    simp [rowPolynomial, h, Fin.val_rev, Nat.sub_sub, Nat.add_comm]

theorem determinantDefinition : DeterminantDefinition.{u} := by
  intro R _ f g n m
  rfl

theorem ordinaryDefinition : OrdinaryDefinition.{u} := by
  intro R _ f g hf hg
  rfl

theorem emptyDeterminant : EmptyDeterminant.{u} := by
  intro R _ f g
  haveI : IsEmpty (Fin (0 + 0)) := inferInstanceAs (IsEmpty (Fin 0))
  exact Matrix.det_isEmpty

/-- Coefficients beyond the stated degree vanish, including a zero polynomial. -/
lemma shiftedCoefficient {R : Type u} [CommRing R] (p : R[X]) (d : ℕ)
    (hp : p.natDegree ≤ d) (k t : ℕ) :
    (X ^ k * p).coeff t = if t ∈ Set.Icc k (k + d) then p.coeff (t - k) else 0 := by
  rw [coeff_X_pow_mul']
  simp only [Set.mem_Icc]
  by_cases h : k ≤ t
  · simp only [h, true_and, ite_true]
    split_ifs with h'
    · rfl
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  · simp [h]

theorem sylvesterBridge : SylvesterBridge.{u} := by
  intro R _ f g n m hf hg
  ext i j
  change (rowPolynomial f g n m i).coeff (j.rev : ℕ) =
    Polynomial.sylvester f g n m j.rev i.rev
  generalize hi : i.rev = k
  induction k using Fin.addCases with
  | left k =>
    simp only [rowPolynomial, hi, Fin.addCases_left, Polynomial.sylvester, Matrix.of_apply]
    exact shiftedCoefficient g m hg k j.rev
  | right k =>
    simp only [rowPolynomial, hi, Fin.addCases_right, Polynomial.sylvester, Matrix.of_apply]
    exact shiftedCoefficient f n hf k j.rev

theorem resultantBridge : ResultantBridge.{u} := by
  intro R _ f g n m hf hg
  rw [fixedResultant, sylvesterBridge R f g n m hf hg]
  change ((Polynomial.sylvester f g n m).transpose.submatrix
    (Fin.revPerm : Equiv.Perm (Fin (n + m))) Fin.revPerm).det = _
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
  rfl

theorem combinationFormula : CombinationFormula.{u} := by
  intro R _ f g n m hf hg A B
  change f * (A : R[X]) + g * (B : R[X]) = _
  rw [mul_comm f, mul_comm g]

theorem matrixRepresentation : MatrixRepresentation.{u} := by
  intro R _ f g n m hf hg
  ext i j
  simp only [LinearMap.toMatrix_apply, sourceBasis, targetBasis, Basis.map_apply,
    Basis.reindex_apply, Basis.repr_reindex, Fin.revPerm_symm]
  change (combinationMap f g hf hg
    ((LinearEquiv.prodComm R R[X]_n R[X]_m) (degreeLT.basisProd R n m j.rev)) : R[X]).coeff
      (i.rev : ℕ) = (rowPolynomial f g n m j).coeff (i.rev : ℕ)
  generalize hj : j.rev = k
  induction k using Fin.addCases with
  | left k =>
    simp [rowPolynomial, hj, degreeLT.basisProd_castAdd, combinationMap, mul_comm]
  | right k =>
    simp [rowPolynomial, hj, degreeLT.basisProd_natAdd, combinationMap, mul_comm]

theorem swapSign : SwapSign.{u} := by
  intro R _ f g n m hf hg
  rw [resultantBridge R g f m n hg hf, resultantBridge R f g n m hf hg]
  simpa only [Nat.mul_comm m n] using Polynomial.resultant_comm g f m n

theorem constantResultant : ConstantResultant.{u} := by
  intro R _ f c n hf hc hn
  rw [ordinaryResultant, natDegree_C,
    resultantBridge R f (C c) f.natDegree 0 le_rfl (by simp),
    Polynomial.resultant_C_zero_right, hn]

end D07.Ch19.ResultantDefinition
