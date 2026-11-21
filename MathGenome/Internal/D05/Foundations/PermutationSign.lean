import MathGenome.Internal.Specs.D05.Foundations.PermutationSign

noncomputable section

namespace D05.Foundations.PermutationSign

open D05.Foundations

/-- Convert the product of pairwise signs to a count of inversions. -/
theorem signIdentification : D05.Specs.PermutationSign.signIdentification := by
  intro n σ
  have h := congrArg (fun u : ℤˣ => (u : ℤ)) σ.sign_eq_prod_prod_Ioi
  simp only [Units.coe_prod, Units.val_one, Units.val_neg, apply_ite] at h
  rw [h]
  unfold permutationSign inversionCount
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_const, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro j hj
  have hne : σ i ≠ σ j := σ.injective.ne (Finset.mem_Ioi.mp hj).ne
  rcases lt_or_gt_of_ne hne with hij | hji
  · simp [hij, not_lt_of_gt hij]
  · simp [hji, not_lt_of_gt hji]

theorem signMultiplicative : D05.Specs.PermutationSign.signMultiplicative := by
  intro n σ τ
  rw [signIdentification n (σ * τ), signIdentification n σ,
    signIdentification n τ, Equiv.Perm.sign_mul, Units.val_mul]

theorem signTransposition : D05.Specs.PermutationSign.signTransposition := by
  intro n i j hij
  rw [signIdentification, Equiv.Perm.sign_swap hij]
  rfl

theorem productPermutation : D05.Specs.PermutationSign.productPermutation := by
  intro R _ n σ x
  have h := σ.prod_Ioi_comp_eq_sign_mul_prod
    (f := fun i j => x j - x i) (fun i j => (neg_sub (x i) (x j)).symm)
  rw [signIdentification n σ]
  exact h

theorem scalarPolynomialPermutation : D05.Specs.PermutationSign.scalarPolynomialPermutation := by
  intro R _ n σ
  have h := productPermutation (FormalPolynomial R n) n σ (fun i => MvPolynomial.X i)
  simpa [vandermondePolynomial, vandermondeProduct, map_prod, map_sub] using h

theorem polynomialPermutation : D05.Specs.PermutationSign.polynomialPermutation := by
  exact scalarPolynomialPermutation ℤ

theorem scalarPolynomialMap : D05.Specs.PermutationSign.scalarPolynomialMap := by
  intro R _ n
  simp [vandermondePolynomial, vandermondeProduct, map_prod, map_sub]

theorem scalarSignLaws : D05.Specs.PermutationSign.scalarSignLaws := by
  intro R _ n σ τ
  constructor
  · rw [signMultiplicative, Int.cast_mul]
  · intro i j hij
    rw [signTransposition n i j hij]
    simp

theorem emptyCase : D05.Specs.PermutationSign.emptyCase := by
  constructor
  · intro σ
    simp [inversionCount, permutationSign]
  · intro R _
    simp [vandermondePolynomial, vandermondeProduct]

end D05.Foundations.PermutationSign
