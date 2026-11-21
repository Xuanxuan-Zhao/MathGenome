import MathGenome.Internal.Specs.D07.Ch15.GenericUnsolvabilitySymmetricRationalFixedField
import MathGenome.Internal.D07.Ch12.SplittingDegreeBoundFactorialInequality
import MathGenome.Internal.D07.Ch14.ArtinFixedField
import MathGenome.Internal.D07.Ch19.SymmetricFunctions
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic

universe u v
noncomputable section
namespace D07.Ch15.GenericUnsolvabilitySymmetricRationalFixedField
open Specs.D07.Ch15.GenericUnsolvabilitySymmetricRationalFixedField

variable (K : Type u) [Field K] (n : ℕ)

private theorem fraction_ext {f g : Rational K n ≃ₐ[K] Rational K n}
    (h : ∀ p : MvPolynomial (Fin n) K,
      f (algebraMap _ _ p) = g (algebraMap _ _ p)) : f = g := by
  have hring : f.toRingHom = g.toRingHom := IsFractionRing.ringHom_ext h
  exact AlgEquiv.ext (fun z => DFunLike.congr_fun hring z)

@[simp] theorem variablePerm_algebraMap (π : Equiv.Perm (Fin n))
    (p : MvPolynomial (Fin n) K) :
    variablePerm K n π (algebraMap _ _ p) = algebraMap _ _ (MvPolynomial.rename π p) := by
  exact IsFractionRing.algEquivOfAlgEquiv_algebraMap _ _

@[simp] theorem variablePerm_root (π : Equiv.Perm (Fin n)) (i : Fin n) :
    variablePerm K n π (root K n i) = root K n (π i) := by
  simp [root]

@[simp] theorem variablePerm_one : variablePerm K n 1 = AlgEquiv.refl := by
  apply fraction_ext
  intro p
  simp

@[simp] theorem variablePerm_mul (π τ : Equiv.Perm (Fin n)) :
    variablePerm K n (π * τ) = variablePerm K n π * variablePerm K n τ := by
  apply fraction_ext
  intro p
  simp only [variablePerm_algebraMap, AlgEquiv.mul_apply]
  rw [MvPolynomial.rename_rename]
  rfl

def permutationHom : Equiv.Perm (Fin n) →* (Rational K n ≃ₐ[K] Rational K n) where
  toFun := variablePerm K n
  map_one' := variablePerm_one K n
  map_mul' := variablePerm_mul K n

@[simp] theorem root_injective : Function.Injective (root K n) := by
  intro i j h
  apply MvPolynomial.X_injective (R := K)
  exact (IsFractionRing.injective (MvPolynomial (Fin n) K) (Rational K n)) h

theorem variablePerm_injective : Function.Injective (variablePerm K n) := by
  intro π τ h
  apply Equiv.ext
  intro i
  apply root_injective K n
  simpa using DFunLike.congr_fun h (root K n i)

theorem action : Action.{u} := by
  intro K _ n
  exact ⟨variablePerm_one K n, variablePerm_mul K n,
    variablePerm_root K n, variablePerm_injective K n⟩

private theorem aeval_root :
    MvPolynomial.aeval (root K n) =
      IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K) (Rational K n) := by
  ext i
  simp [root]

theorem root_independence : RootIndependence.{u} := by
  intro K _ n
  rw [AlgebraicIndependent, aeval_root]
  exact IsFractionRing.injective _ _

theorem roots_generate : RootsGenerate.{u} := by
  intro K _ n
  apply top_unique
  intro z _
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin n) K) z
  rw [IntermediateField.mem_adjoin_range_iff]
  exact ⟨p, q, by simp [aeval_root]⟩

@[simp] theorem variablePerm_elementaryNat (π : Equiv.Perm (Fin n)) (j : ℕ) :
    variablePerm K n π (elementaryNat K n j) = elementaryNat K n j := by
  simpa [elementaryNat] using congrArg
    (algebraMap (MvPolynomial (Fin n) K) (Rational K n))
    (MvPolynomial.esymm_isSymmetric (Fin n) K j π)

theorem coefficients_le_fixed : coefficients K n ≤ fixedField K n := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨i, rfl⟩ π
  exact variablePerm_elementaryNat K n π (i.val + 1)

theorem elementary_independence : ElementaryIndependence.{u} := by
  intro K _ n
  let f : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
    (MvPolynomial.symmetricSubalgebra (Fin n) K).val.comp
      (MvPolynomial.esymmAlgHom (Fin n) K n)
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (MvPolynomial.esymmAlgHom_fin_injective K le_rfl)
  have he : MvPolynomial.aeval (elementary K n) =
      (IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K) (Rational K n)).comp f := by
    ext i
    simp [f, MvPolynomial.esymmAlgHom, elementary, elementaryNat]
  rw [AlgebraicIndependent, he]
  exact (IsFractionRing.injective _ _).comp hf

theorem root_transport : RootTransport.{u, v} := by
  intro K M _ _ _ n x hx
  refine ⟨hx.aevalEquivField, ?_⟩
  intro i
  simp only [root, AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe,
    MvPolynomial.aeval_X]

set_option backward.isDefEq.respectTransparency false in
theorem coefficient_transport : CoefficientTransport.{u, v} := by
  intro K M _ _ _ n s hs
  let he := elementary_independence K n
  refine ⟨hs.aevalEquivField.symm.trans he.aevalEquivField, ?_⟩
  intro i
  have hsi : hs.aevalEquivField (root K n i) =
      ⟨s i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩ := by
    apply Subtype.ext
    simp [root]
  change (((hs.aevalEquivField.symm.trans he.aevalEquivField) _) : Rational K n) = _
  simp only [AlgEquiv.trans_apply, ← hsi, AlgEquiv.symm_apply_apply]
  simp [root]

theorem factorization : Factorization.{u} := by
  intro K _ n
  have h := D07.Ch19.SymmetricFunctions.formal_vieta K n
  apply_fun Polynomial.map (algebraMap (MvPolynomial (Fin n) K) (Rational K n)) at h
  simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_one] at h
  change _ = ∏ i : Fin n, (Polynomial.X - Polynomial.C (algebraMap _ _ (MvPolynomial.X i)))
  rw [h]
  simp only [genericPolynomial, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_one,
    Polynomial.map_C, Polynomial.map_X]
  change (∑ j : Fin (n + 1), (-1) ^ j.val *
    (Polynomial.C (elementaryNat K n j.val) * Polynomial.X ^ (n - j.val))) = _
  exact (Finset.sum_range (fun j : ℕ => (-1 : Polynomial (Rational K n)) ^ j *
    (Polynomial.C (elementaryNat K n j) * Polynomial.X ^ (n - j)))).symm

private theorem polynomial_monic : (genericPolynomial K n).Monic := by
  apply (Polynomial.monic_map_iff (f := algebraMap (coefficients K n) (Rational K n))).mp
  rw [factorization K n]
  exact Polynomial.monic_prod_X_sub_C _ _

private theorem polynomial_degree : (genericPolynomial K n).natDegree = n := by
  rw [← Polynomial.natDegree_map (algebraMap (coefficients K n) (Rational K n)),
    factorization K n]
  simp

private theorem polynomial_separable : (genericPolynomial K n).Separable := by
  apply (Polynomial.separable_map (algebraMap (coefficients K n) (Rational K n))).mp
  rw [factorization K n]
  exact Polynomial.separable_prod_X_sub_C_iff.mpr (root_injective K n)

private theorem root_mem_rootSet (i : Fin n) :
    root K n i ∈ (genericPolynomial K n).rootSet (Rational K n) := by
  rw [Polynomial.mem_rootSet_of_ne (polynomial_monic K n).ne_zero]
  rw [← Polynomial.eval_map_algebraMap, factorization K n, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

private theorem polynomial_splitting : Polynomial.IsSplittingField
    (coefficients K n) (Rational K n) (genericPolynomial K n) := by
  apply isSplittingField_iff_intermediateField.mpr
  constructor
  · rw [factorization K n]
    exact Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C _
  · apply top_unique
    rw [← IntermediateField.adjoin_eq_top_of_adjoin_eq_top K (E := coefficients K n)
      (roots_generate K n)]
    apply IntermediateField.adjoin.mono
    rintro _ ⟨i, rfl⟩
    exact root_mem_rootSet K n i

theorem separable_splitting_field : SeparableSplittingField.{u} := by
  intro K _ n _
  exact ⟨polynomial_monic K n, polynomial_degree K n,
    polynomial_separable K n, polynomial_splitting K n⟩

private theorem degree_upper_bound :
    Module.finrank (coefficients K n) (Rational K n) ≤ n.factorial := by
  have hs : Specs.D07.Ch12.SplittingDefinition.splittingFieldValue
      (coefficients K n) (Rational K n) (genericPolynomial K n) :=
    (D07.Ch12.SplittingDefinition.library_characterization _ _ _
      (polynomial_monic K n).ne_zero).mpr (polynomial_splitting K n)
  obtain ⟨d, hd, hbound⟩ :=
    D07.Ch12.SplittingDegreeBoundFactorialInequality.factorial_inequality _ _ _ hs
  rw [Module.finrank_eq_of_rank_eq hd]
  simpa only [polynomial_degree] using hbound

def permutationSubgroup : Subgroup (Rational K n ≃ₐ[K] Rational K n) :=
  (permutationHom K n).range

private theorem subgroup_fixedField :
    IntermediateField.fixedField (permutationSubgroup K n) = fixedField K n := by
  ext z
  simp only [IntermediateField.mem_fixedField_iff, permutationSubgroup,
    MonoidHom.mem_range, fixedField]
  constructor
  · intro h π
    exact h _ ⟨π, rfl⟩
  · rintro h _ ⟨π, rfl⟩
    exact h π

private theorem subgroup_card : Nat.card (permutationSubgroup K n) = n.factorial := by
  calc
    Nat.card (permutationSubgroup K n) = Nat.card (Equiv.Perm (Fin n)) :=
      Nat.card_congr (MonoidHom.ofInjective (variablePerm_injective K n)).toEquiv.symm
    _ = n.factorial := by simp [Fintype.card_perm]

set_option backward.isDefEq.respectTransparency false in
private theorem artin_fixed_degree :
    FiniteDimensional (fixedField K n) (Rational K n) ∧
    Module.finrank (fixedField K n) (Rational K n) = n.factorial := by
  have : Finite (permutationSubgroup K n) :=
    Set.finite_range (permutationHom K n) |>.to_subtype
  have h := D07.Ch14.ArtinFixedField.subgroup_artin K (Rational K n) (permutationSubgroup K n)
  have hh : FiniteDimensional (IntermediateField.fixedField (permutationSubgroup K n))
      (Rational K n) ∧
      Module.finrank (IntermediateField.fixedField (permutationSubgroup K n))
        (Rational K n) = n.factorial := ⟨h.1, h.2.2.1.trans (subgroup_card K n)⟩
  rw [← subgroup_fixedField K n]
  exact hh

theorem fixed_field_equality : FixedFieldEquality.{u} := by
  intro K _ n _
  let := polynomial_splitting K n
  let := Polynomial.IsSplittingField.finiteDimensional (Rational K n) (genericPolynomial K n)
  apply IntermediateField.eq_of_le_of_finrank_le' (coefficients_le_fixed K n)
  rw [(artin_fixed_degree K n).2]
  exact degree_upper_bound K n

theorem degree : Degree.{u} := by
  intro K _ n hn
  let := polynomial_splitting K n
  refine ⟨Polynomial.IsSplittingField.finiteDimensional (Rational K n) (genericPolynomial K n),
    IsGalois.of_separable_splitting_field (polynomial_separable K n), ?_⟩
  rw [fixed_field_equality K n hn]
  exact (artin_fixed_degree K n).2

/-- The given permutation itself, with its scalar field enlarged to E. -/
def permutationOverCoefficients :
    Equiv.Perm (Fin n) →* (Rational K n ≃ₐ[coefficients K n] Rational K n) where
  toFun π := { (variablePerm K n π).toRingEquiv with
    commutes' := fun a => coefficients_le_fixed K n a.2 π }
  map_one' := by ext z; exact DFunLike.congr_fun (variablePerm_one K n) z
  map_mul' π τ := by ext z; exact DFunLike.congr_fun (variablePerm_mul K n π τ) z

private theorem permutationOverCoefficients_bijective (hn : 1 ≤ n) :
    Function.Bijective (permutationOverCoefficients K n) := by
  constructor
  · intro π τ h
    apply variablePerm_injective K n
    exact AlgEquiv.ext fun z => DFunLike.congr_fun h z
  · intro σ
    have : Finite (permutationSubgroup K n) :=
      Set.finite_range (permutationHom K n) |>.to_subtype
    have hEF : coefficients K n = IntermediateField.fixedField (permutationSubgroup K n) :=
      (fixed_field_equality K n hn).trans (subgroup_fixedField K n).symm
    let σF : Rational K n ≃ₐ[IntermediateField.fixedField (permutationSubgroup K n)] Rational K n :=
      { σ.toRingEquiv with
        commutes' := fun a => σ.commutes ⟨a.val, by rw [hEF]; exact a.2⟩ }
    obtain ⟨g, hg⟩ :=
      (D07.Ch14.ArtinFixedField.subgroup_artin K (Rational K n)
        (permutationSubgroup K n)).2.2.2 σF
    obtain ⟨π, hπ⟩ := g.2
    refine ⟨π, AlgEquiv.ext fun z => ?_⟩
    change variablePerm K n π z = σ z
    exact (DFunLike.congr_fun hπ z).trans (hg z).symm

theorem automorphism_group : AutomorphismGroup.{u} := by
  intro K _ n hn
  refine ⟨MulEquiv.ofBijective (permutationOverCoefficients K n)
    (permutationOverCoefficients_bijective K n hn), ?_⟩
  intro π z
  rfl


/-- The alternating expression with leading term displayed separately. -/
theorem genericPolynomial_expansion :
    genericPolynomial K n = Polynomial.X ^ n + ∑ i : Fin n, (-1) ^ (i.val + 1) *
      (Polynomial.C (⟨elementary K n i,
        IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩ : coefficients K n) *
        Polynomial.X ^ (n - (i.val + 1))) := by
  unfold genericPolynomial
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, Nat.sub_zero, Fin.val_succ]
  have hc : coefficient K n 0 = 1 := by
    apply Subtype.ext
    simp [coefficient, elementaryNat]
  rw [hc, Polynomial.C_1, one_mul, one_mul]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem coefficient_polynomial_transport : CoefficientPolynomialTransport.{u, v} := by
  intro K M _ _ _ n s hs
  obtain ⟨e, he⟩ := coefficient_transport K M n s hs
  refine ⟨e, he, ?_⟩
  rw [genericPolynomial_expansion]
  simp only [tuplePolynomial, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_neg, Polynomial.map_one,
    Polynomial.map_C]
  apply congrArg (fun q : Polynomial (coefficients K n) => Polynomial.X ^ n + q)
  apply Finset.sum_congr rfl
  intro i _
  have hei : e ⟨s i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩ =
      (⟨elementary K n i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩ : coefficients K n) :=
    Subtype.ext (he i)
  exact congrArg (fun a : coefficients K n =>
    (-1 : Polynomial (coefficients K n)) ^ (i.val + 1) *
      (Polynomial.C a * Polynomial.X ^ (n - (i.val + 1)))) hei


end D07.Ch15.GenericUnsolvabilitySymmetricRationalFixedField
