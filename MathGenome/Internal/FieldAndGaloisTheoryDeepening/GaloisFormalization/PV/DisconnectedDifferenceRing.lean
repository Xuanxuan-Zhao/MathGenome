import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotRing
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.RationalDilationConstants
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.DisconnectedDifferenceRing
import Mathlib.Algebra.Polynomial.RingDivision

namespace GaloisFormalization.PV.DisconnectedDifference

/-- The polynomial quotient over the rational function field by `X² - 1`. -/
abbrev QuotientRing (C : Type*) [Field C] := Specs.DisconnectedDifference.quotientRing C

/-- The image of the indeterminate in the quotient. -/
noncomputable def quotientRoot (C : Type*) [Field C] : QuotientRing C :=
  Specs.DisconnectedDifference.quotientRoot C

/-- The unit `(1, -1)` in the product model. -/
noncomputable def solutionUnit (C : Type*) [Field C] : (RatFunc C × RatFunc C)ˣ :=
  Specs.DisconnectedDifference.solutionUnit C

/-- The difference operator that dilates the coefficients and exchanges the two factors. -/
noncomputable def productOperator {C : Type*} [Field C] (q : Cˣ) :
    Operator .difference (RatFunc C × RatFunc C) :=
  Specs.DisconnectedDifference.productOperator q

/-- The rank-one system `σ(y) = -y`. -/
noncomputable def negativeSystem (C : Type*) [Field C] : LinearSystem .difference (RatFunc C) 1 :=
  Specs.DisconnectedDifference.negativeSystem C

/-- The rank-one matrix of the scalar solution in the product model. -/
noncomputable def fundamentalMatrix (C : Type*) [Field C] :
    Matrix.GeneralLinearGroup (Fin 1) (RatFunc C × RatFunc C) :=
  Specs.DisconnectedDifference.fundamentalMatrix C

section
variable {C : Type*} [Field C]

local notation "k" => RatFunc C
local notation "S" => RatFunc C × RatFunc C

@[simp]
theorem productOperator_apply (q : Cˣ) (x : S) :
    productOperator q x = (rationalDilation q x.2, rationalDilation q x.1) := rfl

@[simp]
theorem productOperator_solutionUnit (q : Cˣ) :
    productOperator q (solutionUnit C : S) = -(solutionUnit C : S) := by
  change (rationalDilation q (-1), rationalDilation q 1) = (-(1 : k), -(-1 : k))
  simp

theorem productIdempotents : Specs.DisconnectedDifference.productIdempotents := by
  intro C _ q
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Prod.ext_iff]
  · simp [Prod.ext_iff]
  · ext <;> simp
  · ext <;> simp
  · ext <;> simp
  · ext <;> simp
  · change productOperator q (1, 0) = (0, 1)
    simp
  · change productOperator q (0, 1) = (1, 0)
    simp

theorem product_isExtension (q : Cˣ) :
    (rationalDilationOperator q).IsExtension (productOperator q) :=
  ⟨fun _ => rfl, fun _ _ h => congrArg Prod.fst h⟩

theorem product_isSimple (q : Cˣ) : (productOperator q).IsSimple := by
  refine ⟨inferInstance, fun I hI => ?_⟩
  by_cases h : I = ⊥
  · exact Or.inl h
  right
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ I, x ≠ (0 : S) := by
    by_contra! hzero
    apply h
    exact bot_unique fun x hx => Ideal.mem_bot.mpr (hzero x hx)
  have hswap₁ : (1, 0) ∈ I → (0, 1) ∈ I := by
    intro hmem
    have hm : productOperator q _ ∈ I := hI.apply_mem hmem
    simpa only [productOperator_apply, map_zero, map_one] using hm
  have hswap₂ : (0, 1) ∈ I → (1, 0) ∈ I := by
    intro hmem
    have hm : productOperator q _ ∈ I := hI.apply_mem hmem
    simpa only [productOperator_apply, map_zero, map_one] using hm
  have hpair : (1, 0) ∈ I ∧ (0, 1) ∈ I := by
    by_cases ha : x.1 = 0
    · have hb : x.2 ≠ 0 := fun hb => hx0 (Prod.ext ha hb)
      have he : (0, 1) ∈ I := by
        have heq : ((0, x.2⁻¹) : S) * x = (0, 1) := by ext <;> simp [hb]
        exact heq ▸ I.mul_mem_left (0, x.2⁻¹) hx
      exact ⟨hswap₂ he, he⟩
    · have he : (1, 0) ∈ I := by
        have heq : ((x.1⁻¹, 0) : S) * x = (1, 0) := by ext <;> simp [ha]
        exact heq ▸ I.mul_mem_left (x.1⁻¹, 0) hx
      exact ⟨he, hswap₁ he⟩
  apply (Ideal.eq_top_iff_one I).mpr
  have hsum : ((1, 0) : S) + (0, 1) = 1 := by ext <;> simp
  exact hsum ▸ I.add_mem hpair.1 hpair.2

@[simp]
theorem negativeSystem_coefficient (i j : Fin 1) :
    (negativeSystem C).coefficientMatrix i j = (-1 : k) := rfl

@[simp]
theorem fundamentalMatrix_entry (i j : Fin 1) :
    (fundamentalMatrix C).val i j = (solutionUnit C : S) := rfl

private theorem isFundamental_of_entry {R : Type*} [CommRing R] [Algebra k R]
    {E : Operator .difference R} {Y : Matrix.GeneralLinearGroup (Fin 1) R}
    (h : E (Y.val 0 0) = -Y.val 0 0) : (negativeSystem C).IsFundamental E Y := by
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  simpa [LinearSystem.mapCoefficients, Matrix.mul_apply] using h

private theorem add_solution_mul_half [CharZero C] :
    (1 + (solutionUnit C : S)) * algebraMap k S (2 : k)⁻¹ = (1, 0) := by
  change (1 + ((1, -1) : S)) * ((2 : k)⁻¹, (2 : k)⁻¹) = (1, 0)
  ext <;> simp [one_add_one_eq_two]

private theorem sub_solution_mul_half [CharZero C] :
    (1 - (solutionUnit C : S)) * algebraMap k S (2 : k)⁻¹ = (0, 1) := by
  change (1 - ((1, -1) : S)) * ((2 : k)⁻¹, (2 : k)⁻¹) = (0, 1)
  ext <;> simp [one_add_one_eq_two]

private theorem diagonal_mul_idempotents (a b : k) :
    algebraMap k S a * (1, 0) + algebraMap k S b * (0, 1) = (a, b) := by
  change ((a, a) : S) * (1, 0) + (b, b) * (0, 1) = (a, b)
  ext <;> simp

private theorem entry_mem_matrixGeneratedSubalgebra
    {R : Type*} [CommRing R] [Algebra k R] (Y : Matrix.GeneralLinearGroup (Fin 1) R) :
    Y.val 0 0 ∈ matrixGeneratedSubalgebra k Y :=
  Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨(0, 0), rfl⟩)

theorem product_matrixGeneratedSubalgebra [CharZero C] :
    matrixGeneratedSubalgebra k (fundamentalMatrix C) = ⊤ := by
  let A := matrixGeneratedSubalgebra k (fundamentalMatrix C)
  have hu : (solutionUnit C : S) ∈ A :=
    entry_mem_matrixGeneratedSubalgebra (fundamentalMatrix C)
  have hhalf := A.algebraMap_mem (2 : k)⁻¹
  have h₁ : (1, 0) ∈ A :=
    add_solution_mul_half (C := C) ▸ A.mul_mem (A.add_mem A.one_mem hu) hhalf
  have h₂ : (0, 1) ∈ A :=
    sub_solution_mul_half (C := C) ▸ A.mul_mem (A.sub_mem A.one_mem hu) hhalf
  apply top_unique
  rintro ⟨a, b⟩ _
  rw [← diagonal_mul_idempotents a b]
  exact A.add_mem (A.mul_mem (A.algebraMap_mem a) h₁) (A.mul_mem (A.algebraMap_mem b) h₂)

theorem productPicardVessiot : Specs.DisconnectedDifference.productPicardVessiot := by
  intro C _ _ _ q hq
  have hfund : (negativeSystem C).IsFundamental (productOperator q) (fundamentalMatrix C) :=
    isFundamental_of_entry (productOperator_solutionUnit q)
  refine ⟨rationalDilation_isBaseField q hq, rationalDilation_constantSubfield q hq, fun _ => rfl,
    productOperator_apply q, productOperator_solutionUnit q, ?_, rfl, hfund,
    product_matrixGeneratedSubalgebra⟩
  exact ⟨product_isExtension q, product_isSimple q, fundamentalMatrix C, hfund,
    product_matrixGeneratedSubalgebra⟩

open Polynomial

local notation "Q" => QuotientRing C
local notation "p₀" => (X ^ 2 - 1 : Polynomial (RatFunc C))

private noncomputable def quotientEval (a : k) (ha : a ^ 2 = 1) : Q →ₐ[k] k :=
  AdjoinRoot.liftAlgHom p₀ (AlgHom.id k k) a (by simp [ha])

private noncomputable def quotientProductHom : Q →ₐ[k] S :=
  (quotientEval 1 (by simp)).prod (quotientEval (-1) (by simp))

private theorem quotientProductHom_mk (p : Polynomial k) :
    quotientProductHom (C := C) (AdjoinRoot.mk p₀ p) = (p.eval 1, p.eval (-1)) := rfl

private theorem quotientProductHom_root :
    quotientProductHom (C := C) (quotientRoot C) = (solutionUnit C : S) := by
  change quotientProductHom (C := C) (AdjoinRoot.mk p₀ X) = (1, -1)
  rw [quotientProductHom_mk]
  simp

private theorem map_add_root_mul_half [CharZero C]
    (f : Q →ₐ[k] S) (hf : f (quotientRoot C) = (solutionUnit C : S)) :
    f ((1 + quotientRoot C) * algebraMap k Q (2 : k)⁻¹) = (1, 0) := by
  rw [map_mul, map_add, map_one, hf, f.commutes]
  exact add_solution_mul_half

private theorem map_sub_root_mul_half [CharZero C]
    (f : Q →ₐ[k] S) (hf : f (quotientRoot C) = (solutionUnit C : S)) :
    f ((1 - quotientRoot C) * algebraMap k Q (2 : k)⁻¹) = (0, 1) := by
  rw [map_mul, map_sub, map_one, hf, f.commutes]
  exact sub_solution_mul_half

private theorem quotientProductHom_injective [CharZero C] :
    Function.Injective (quotientProductHom (C := C)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x
  induction x using AdjoinRoot.induction_on with
  | ih p =>
    rw [quotientProductHom_mk, AdjoinRoot.mk_eq_zero]
    intro hp
    have hpos : X - Polynomial.C (1 : k) ∣ p :=
      dvd_iff_isRoot.mpr (congrArg Prod.fst hp)
    have hneg : X - Polynomial.C (-1 : k) ∣ p :=
      dvd_iff_isRoot.mpr (congrArg Prod.snd hp)
    have htwo : IsUnit ((1 : k) - (-1)) := by
      simp [one_add_one_eq_two]
    have hcop := isCoprime_X_sub_C_of_isUnit_sub htwo
    have hfactor : (X - Polynomial.C (1 : k)) * (X - Polynomial.C (-1 : k)) = p₀ := by
      simpa [mul_comm] using (sq_sub_sq (X : Polynomial k) 1).symm
    exact hfactor ▸ hcop.mul_dvd hpos hneg

private theorem quotientProductHom_surjective [CharZero C] :
    Function.Surjective (quotientProductHom (C := C)) := by
  rintro ⟨a, b⟩
  let f := quotientProductHom (C := C)
  have hp := map_add_root_mul_half f quotientProductHom_root
  have hm := map_sub_root_mul_half f quotientProductHom_root
  refine ⟨algebraMap k Q a * ((1 + quotientRoot C) * algebraMap k Q (2 : k)⁻¹) +
    algebraMap k Q b * ((1 - quotientRoot C) * algebraMap k Q (2 : k)⁻¹), ?_⟩
  change f _ = (a, b)
  simpa only [map_add, map_mul, f.commutes, hp, hm] using diagonal_mul_idempotents a b

/-- The two evaluations identify the polynomial quotient with the product over the base. -/
noncomputable def quotientToProduct (C : Type*) [Field C] [CharZero C] :
    QuotientRing C ≃ₐ[RatFunc C] RatFunc C × RatFunc C :=
  AlgEquiv.ofBijective quotientProductHom
    ⟨quotientProductHom_injective, quotientProductHom_surjective⟩

@[simp]
theorem quotientToProduct_mk [CharZero C] (p : Polynomial k) :
    quotientToProduct C (AdjoinRoot.mk p₀ p) = (p.eval 1, p.eval (-1)) :=
  quotientProductHom_mk p

@[simp]
theorem quotientToProduct_root [CharZero C] :
    quotientToProduct C (quotientRoot C) = (solutionUnit C : S) :=
  quotientProductHom_root

/-- The quotient operator is the dilation with exchanged factors, transported to the quotient. -/
noncomputable def quotientOperator [CharZero C] (q : Cˣ) : Operator .difference Q :=
  let e := (quotientToProduct C).toRingEquiv
  Operator.difference ((e.trans (productOperator q).toRingEquiv).trans e.symm)

theorem quotientOperator_commutes [CharZero C] (q : Cˣ) :
    (quotientOperator q).Commutes (productOperator q) (quotientToProduct C) := by
  intro x
  change quotientToProduct C ((quotientToProduct C).symm
    (productOperator q (quotientToProduct C x))) = _
  exact (quotientToProduct C).apply_symm_apply _

@[simp]
theorem quotientRoot_sq : quotientRoot C ^ 2 = 1 := by
  have h := AdjoinRoot.eval₂_root p₀
  simpa only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_one, sub_eq_zero,
    quotientRoot, Specs.DisconnectedDifference.quotientRoot] using h

@[simp]
theorem quotientOperator_root [CharZero C] (q : Cˣ) :
    quotientOperator q (quotientRoot C) = -quotientRoot C := by
  apply (quotientToProduct C).injective
  rw [quotientOperator_commutes q (quotientRoot C), map_neg, quotientToProduct_root]
  exact productOperator_solutionUnit q

private theorem quotient_isExtension [CharZero C] (q : Cˣ) :
    (rationalDilationOperator q).IsExtension (quotientOperator q) := by
  constructor
  · intro x
    apply (quotientToProduct C).injective
    simp only [quotientOperator_commutes q (algebraMap k Q x), AlgEquiv.commutes]
    exact (product_isExtension q).1 x
  · intro x y h
    apply (product_isExtension q).2
    simpa only [AlgEquiv.commutes] using congrArg (quotientToProduct C) h

private theorem quotient_isSimple [CharZero C] (q : Cˣ) :
    (quotientOperator q).IsSimple := by
  let e := quotientToProduct C
  refine ⟨e.toEquiv.nontrivial, fun I hI => ?_⟩
  let J := I.comap e.symm.toRingHom
  have hcomm : (productOperator q).Commutes (quotientOperator q) e.symm :=
    (quotientOperator_commutes q).inverse (f := e.toEquiv)
  have hJ : (productOperator q).IsStable (J : Set S) := by
    constructor
    · intro x hx
      change e.symm (productOperator q x) ∈ I
      rw [hcomm x]
      exact hI.apply_mem hx
    · intro x hx
      change e.symm ((productOperator q).toRingEquiv.symm x) ∈ I
      rw [hcomm.difference_symm x]
      exact hI.symm_apply_mem hx
  have hmap : J.map e.symm.toRingHom = I :=
    Ideal.map_comap_of_surjective _ e.symm.surjective I
  rcases (product_isSimple q).2 J hJ with h | h
  · left
    rw [h, Ideal.map_bot] at hmap
    exact hmap.symm
  · right
    rw [h, Ideal.map_top] at hmap
    exact hmap.symm

private noncomputable def quotientFundamentalMatrix (C : Type*) [Field C] :
    Matrix.GeneralLinearGroup (Fin 1) (QuotientRing C) :=
  Units.map (Matrix.uniqueRingEquiv (m := Fin 1) (A := QuotientRing C)).symm.toMonoidHom
    (Units.mkOfMulEqOne (quotientRoot C) (quotientRoot C) (by
      simpa only [pow_two] using (quotientRoot_sq (C := C))))

private theorem quotient_matrixGeneratedSubalgebra :
    matrixGeneratedSubalgebra k (quotientFundamentalMatrix C) = ⊤ := by
  apply top_unique
  rw [← AdjoinRoot.adjoinRoot_eq_top (f := p₀)]
  apply Algebra.adjoin_le
  exact Set.singleton_subset_iff.mpr
    (entry_mem_matrixGeneratedSubalgebra (quotientFundamentalMatrix C))

theorem quotientPresentation : Specs.DisconnectedDifference.quotientPresentation := by
  intro C _ _ _ q _
  let E := quotientOperator q
  let e := quotientToProduct C
  let Y := quotientFundamentalMatrix C
  have hfund : (negativeSystem C).IsFundamental E Y :=
    isFundamental_of_entry (quotientOperator_root q)
  have hgen : matrixGeneratedSubalgebra (RatFunc C) Y = ⊤ :=
    quotient_matrixGeneratedSubalgebra
  refine ⟨E, e, quotientOperator_commutes q, quotientToProduct_mk, quotientToProduct_root,
    map_add_root_mul_half e.toAlgHom quotientToProduct_root,
    map_sub_root_mul_half e.toAlgHom quotientToProduct_root,
    quotientRoot_sq, quotientOperator_root q, ?_, Y, rfl, hfund, hgen⟩
  exact ⟨quotient_isExtension q, quotient_isSimple q, Y, hfund, hgen⟩

open scoped nonZeroDivisors

private theorem product_isUnit_of_nonZeroDivisor (x : S) (hx : x ∈ S⁰) : IsUnit x := by
  have h := mem_nonZeroDivisors_iff_left.mp hx
  have h₁ : x.1 ≠ 0 := by
    intro hz
    have hzero : x * (1, 0) = 0 := by ext <;> simp [hz]
    have := congrArg Prod.fst (h (1, 0) hzero)
    exact one_ne_zero this
  have h₂ : x.2 ≠ 0 := by
    intro hz
    have hzero : x * (0, 1) = 0 := by ext <;> simp [hz]
    have := congrArg Prod.snd (h (0, 1) hzero)
    exact one_ne_zero this
  apply IsUnit.of_mul_eq_one (x.1⁻¹, x.2⁻¹)
  ext <;> simp [h₁, h₂]

theorem quotientTotal : Specs.DisconnectedDifference.quotientTotal := by
  intro C _ _
  apply (IsFractionRing.self_iff_bijective _).mp
  apply IsFractionRing.self_iff_nonZeroDivisors_le_isUnit.mpr
  intro x hx
  let e := (quotientToProduct C).toRingEquiv
  have he : e x ∈ (RatFunc C × RatFunc C)⁰ :=
    (Operator.ringEquiv_mem_nonZeroDivisors_iff e x).mpr hx
  have hu := (product_isUnit_of_nonZeroDivisor (e x) he).map e.symm.toRingHom
  change IsUnit (e.symm (e x)) at hu
  rwa [RingEquiv.symm_apply_apply] at hu

theorem quotientNoFieldEmbedding : Specs.DisconnectedDifference.quotientNoFieldEmbedding := by
  intro C _ _ F _ f hf
  let e := (quotientToProduct C).symm
  let g : RatFunc C × RatFunc C →+* F := f.comp e.toRingHom
  have hg : Function.Injective g := hf.comp e.injective
  have h₁ : g (1, 0) ≠ 0 := (injective_iff_map_eq_zero g).mp hg _ |>.mt (by
    simp [Prod.ext_iff])
  have h₂ : g (0, 1) ≠ 0 := (injective_iff_map_eq_zero g).mp hg _ |>.mt (by
    simp [Prod.ext_iff])
  apply mul_ne_zero h₁ h₂
  rw [← map_mul, show ((1, 0) : RatFunc C × RatFunc C) * (0, 1) = 0 by ext <;> simp, map_zero]

end

end GaloisFormalization.PV.DisconnectedDifference
