import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.AmitsurComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.AmitsurExactness
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Exactness of the augmented Amitsur complex by contraction after scalar extension. -/

open CategoryTheory
open scoped BigOperators TensorProduct ZeroObject

namespace DerivedFormalization.Descent.AmitsurExactness

universe u v w

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
variable (M : ModuleCat.{max u v w} A)

open AmitsurAlgebras (TensorPower factor liftFactors)

private abbrev ExtendedPower (n : ℕ) := B ⊗[A] TensorPower A B n

/-- Insert a unit among the old factors, leaving the extra left factor fixed. -/
private noncomputable def insert {n : ℕ} (i : Fin (n + 1)) :
    ExtendedPower A B n →ₐ[A] ExtendedPower A B (n + 1) :=
  Algebra.TensorProduct.map (AlgHom.id A B) (AmitsurAlgebras.map i.succAbove)

/-- Send the first old factor to the extra left factor and retain the remaining factors. -/
private noncomputable def merge (n : ℕ) :
    ExtendedPower A B (n + 1) →ₐ[A] ExtendedPower A B n :=
  Algebra.TensorProduct.productMap Algebra.TensorProduct.includeLeft
    (liftFactors (Fin.cases Algebra.TensorProduct.includeLeft
      (fun j ↦ Algebra.TensorProduct.includeRight.comp (factor A B j))))

private theorem merge_insert_zero (n : ℕ) :
    (merge A B n).comp (insert A B (0 : Fin (n + 1))) = AlgHom.id A _ := by
  apply Algebra.TensorProduct.ext
  · simp [AlgHom.comp_assoc, insert, merge]
  · change ((merge A B n).comp (insert A B 0)).comp Algebra.TensorProduct.includeRight =
      (AlgHom.id A _).comp Algebra.TensorProduct.includeRight
    apply AmitsurAlgebras.hom_ext
    intro j
    apply AlgHom.ext
    intro b
    change merge A B n (insert A B 0 (1 ⊗ₜ[A] factor A B j b)) =
      1 ⊗ₜ[A] factor A B j b
    simp [merge, insert, Algebra.TensorProduct.includeRight_apply]

private theorem merge_insert_succ {n : ℕ} (i : Fin (n + 1)) :
    (merge A B (n + 1)).comp (insert A B i.succ) =
      (insert A B i).comp (merge A B n) := by
  apply Algebra.TensorProduct.ext
  · simp [AlgHom.comp_assoc, insert, merge]
  · change ((merge A B (n + 1)).comp (insert A B i.succ)).comp
      Algebra.TensorProduct.includeRight =
        ((insert A B i).comp (merge A B n)).comp Algebra.TensorProduct.includeRight
    apply AmitsurAlgebras.hom_ext
    intro j
    apply AlgHom.ext
    intro b
    change merge A B (n + 1) (insert A B i.succ (1 ⊗ₜ[A] factor A B j b)) =
      insert A B i (merge A B n (1 ⊗ₜ[A] factor A B j b))
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · simp [merge, insert, Algebra.TensorProduct.includeLeft_apply]
    · simp [merge, insert]

private abbrev ExtendedTerm (n : ℕ) := ExtendedPower A B n ⊗[A] M

private noncomputable def extendedFace {n : ℕ} (i : Fin (n + 1)) :
    ExtendedTerm A B M n →ₗ[A] ExtendedTerm A B M (n + 1) :=
  (insert A B i).toLinearMap.rTensor M

private noncomputable def contraction (n : ℕ) :
    ExtendedTerm A B M (n + 1) →ₗ[A] ExtendedTerm A B M n :=
  (merge A B n).toLinearMap.rTensor M

private theorem contraction_face_zero (n : ℕ) :
    (contraction A B M n).comp (extendedFace A B M (0 : Fin (n + 1))) = LinearMap.id := by
  rw [contraction, extendedFace, ← LinearMap.rTensor_comp]
  change ((merge A B n).comp (insert A B 0)).toLinearMap.rTensor M = _
  rw [merge_insert_zero]
  exact TensorProduct.map_id

private theorem contraction_face_succ {n : ℕ} (i : Fin (n + 1)) :
    (contraction A B M (n + 1)).comp (extendedFace A B M i.succ) =
      (extendedFace A B M i).comp (contraction A B M n) := by
  simp only [contraction, extendedFace, ← LinearMap.rTensor_comp]
  change ((merge A B (n + 1)).comp (insert A B i.succ)).toLinearMap.rTensor M =
    ((insert A B i).comp (merge A B n)).toLinearMap.rTensor M
  rw [merge_insert_succ]

private noncomputable def extendedDifferential (n : ℕ) :
    ExtendedTerm A B M n →ₗ[A] ExtendedTerm A B M (n + 1) :=
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • extendedFace A B M i

private theorem contraction_augmentation (x : ExtendedTerm A B M 0) :
    contraction A B M 0 (extendedDifferential A B M 0 x) = x := by
  have h := LinearMap.congr_fun (contraction_face_zero A B M 0) x
  change contraction A B M 0 (extendedFace A B M (0 : Fin 1) x) = x at h
  unfold extendedDifferential
  rw [Fin.sum_univ_one]
  simpa using h

private theorem contraction_identity (n : ℕ) (x : ExtendedTerm A B M (n + 1)) :
    contraction A B M (n + 1) (extendedDifferential A B M (n + 1) x) +
      extendedDifferential A B M n (contraction A B M n x) = x := by
  have hz : contraction A B M (n + 1) (extendedFace A B M 0 x) = x :=
    LinearMap.congr_fun (contraction_face_zero A B M (n + 1)) x
  have hs (i : Fin (n + 1)) :
      contraction A B M (n + 1) (extendedFace A B M i.succ x) =
        extendedFace A B M i (contraction A B M n x) :=
    LinearMap.congr_fun (contraction_face_succ A B M i) x
  have sign (i : Fin (n + 1)) : (-1 : ℤ) ^ (i.succ : ℕ) = -((-1 : ℤ) ^ (i : ℕ)) := by
    rw [Fin.val_succ, pow_succ, mul_neg_one]
  calc
    _ = (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          contraction A B M (n + 1) (extendedFace A B M i x)) +
        (∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
          extendedFace A B M i (contraction A B M n x)) := by
      simp only [extendedDifferential, LinearMap.sum_apply, LinearMap.smul_apply, map_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ ↦ map_zsmul (contraction A B M (n + 1)) _ _
    _ = _ := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_zsmul, hz, sign, hs]
      have cancel :
          (∑ i : Fin (n + 1), -((-1 : ℤ) ^ (i : ℕ)) •
            extendedFace A B M i (contraction A B M n x)) =
          -(∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
            extendedFace A B M i (contraction A B M n x)) := by
        calc
          _ = ∑ i : Fin (n + 1), -(((-1 : ℤ) ^ (i : ℕ)) •
                extendedFace A B M i (contraction A B M n x)) :=
            Finset.sum_congr rfl fun i _ ↦
              neg_zsmul (extendedFace A B M i (contraction A B M n x)) ((-1 : ℤ) ^ (i : ℕ))
          _ = _ := Finset.sum_neg_distrib fun i : Fin (n + 1) ↦
            (-1 : ℤ) ^ (i : ℕ) • extendedFace A B M i (contraction A B M n x)
      rw [cancel, add_assoc]
      exact (congrArg (x + ·) (neg_add_cancel _)).trans (add_zero x)

open AmitsurComplex (Degree) in
private abbrev OriginalTerm : ℕ → ModuleCat.{max u v w} A
  | 0 => M
  | p + 1 => Degree A B M p

private noncomputable def originalDifferential : (n : ℕ) → OriginalTerm A B M n →ₗ[A]
    OriginalTerm A B M (n + 1)
  | 0 => (AmitsurComplex.augmentation A B M).hom
  | p + 1 => (AmitsurComplex.differential A B M p).hom

/-- Reassociate the tensor products, using the tensor unit in the augmented degree. -/
private noncomputable def comparison : (n : ℕ) →
    B ⊗[A] OriginalTerm A B M n ≃ₗ[A] ExtendedTerm A B M n
  | 0 => ((TensorProduct.lid A M).symm.lTensor B).trans
      ((((AmitsurAlgebras.emptyEquiv A B).symm.toLinearEquiv.rTensor M).lTensor B).trans
        (TensorProduct.assoc A B (TensorPower A B 0) M).symm)
  | p + 1 => (TensorProduct.assoc A B (TensorPower A B (p + 1)) M).symm

private theorem comparison_face (p : ℕ) (i : Fin (p + 2))
    (x : B ⊗[A] OriginalTerm A B M (p + 1)) :
    extendedFace A B M i (comparison A B M (p + 1) x) =
      comparison A B M (p + 2) (((AmitsurComplex.coface A B M i).hom.lTensor B) x) := by
  have h : (extendedFace A B M i).comp (comparison A B M (p + 1)).toLinearMap =
      (comparison A B M (p + 2)).toLinearMap.comp
        ((AmitsurComplex.coface A B M i).hom.lTensor B) := by
    apply TensorProduct.ext'
    intro b y
    induction y using TensorProduct.inductionOn with
    | tmul c m =>
      change extendedFace A B M i (comparison A B M (p + 1) (b ⊗ₜ[A] (c ⊗ₜ[A] m))) =
        comparison A B M (p + 2)
          (((AmitsurComplex.coface A B M i).hom.lTensor B) (b ⊗ₜ[A] (c ⊗ₜ[A] m)))
      have hface : (AmitsurComplex.coface A B M i).hom (c ⊗ₜ[A] m) =
          AmitsurAlgebras.coface i c ⊗ₜ[A] m := AmitsurComplex.coface_tmul A B M i c m
      simp [comparison, extendedFace, insert, hface, AmitsurAlgebras.coface]
    | add y z hy hz => simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hy hz
  exact LinearMap.congr_fun h x

private theorem comparison_differential (n : ℕ) :
    (extendedDifferential A B M n).comp (comparison A B M n).toLinearMap =
      (comparison A B M (n + 1)).toLinearMap.comp ((originalDifferential A B M n).lTensor B) := by
  cases n with
  | zero =>
    apply TensorProduct.ext'
    intro b m
    change extendedDifferential A B M 0 (comparison A B M 0 (b ⊗ₜ[A] m)) =
      comparison A B M 1 (((AmitsurComplex.augmentation A B M).hom.lTensor B) (b ⊗ₜ[A] m))
    have haug : (AmitsurComplex.augmentation A B M).hom m = 1 ⊗ₜ[A] m :=
      AmitsurComplex.augmentation_apply A B M m
    simp [extendedDifferential, comparison, extendedFace, insert, haug]
  | succ p =>
    apply LinearMap.ext
    intro x
    change extendedDifferential A B M (p + 1) (comparison A B M (p + 1) x) =
      comparison A B M (p + 2) (((AmitsurComplex.differential A B M p).hom.lTensor B) x)
    simp only [extendedDifferential, AmitsurComplex.differential, ModuleCat.hom_sum,
      ModuleCat.hom_zsmul, ← LinearMap.coe_lTensorHom, map_sum, map_zsmul, LinearMap.sum_apply,
      LinearMap.smul_apply]
    simp only [LinearMap.coe_lTensorHom]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact congrArg ((-1 : ℤ) ^ (i : ℕ) • ·) (comparison_face A B M p i x)

private theorem originalDifferential_sq (n : ℕ) :
    (originalDifferential A B M (n + 1)).comp (originalDifferential A B M n) = 0 := by
  cases n with
  | zero => exact congrArg ModuleCat.Hom.hom (AmitsurComplex.augmentation_comp_differential A B M)
  | succ p => exact congrArg ModuleCat.Hom.hom (AmitsurComplex.differential_sq A B M p)

private theorem originalDifferential_exact [Module.FaithfullyFlat A B] (n : ℕ) :
    Function.Exact (originalDifferential A B M n) (originalDifferential A B M (n + 1)) := by
  apply Module.FaithfullyFlat.lTensor_reflects_exact A B
  intro x
  constructor
  · intro hx
    let e := comparison A B M
    let y := contraction A B M n (e (n + 1) x)
    refine ⟨(e n).symm y, (e (n + 1)).injective ?_⟩
    have h₁ := LinearMap.congr_fun (comparison_differential A B M n) ((e n).symm y)
    have h₂ := LinearMap.congr_fun (comparison_differential A B M (n + 1)) x
    change extendedDifferential A B M n (e n ((e n).symm y)) = _ at h₁
    change extendedDifferential A B M (n + 1) (e (n + 1) x) =
      e (n + 2) ((originalDifferential A B M (n + 1)).lTensor B x) at h₂
    rw [LinearEquiv.apply_symm_apply] at h₁
    rw [hx, map_zero] at h₂
    have h := contraction_identity A B M n (e (n + 1) x)
    rw [h₂, map_zero, zero_add] at h
    exact h₁.symm.trans h
  · rintro ⟨y, rfl⟩
    rw [← LinearMap.lTensor_comp_apply, originalDifferential_sq, LinearMap.lTensor_zero,
      LinearMap.zero_apply]

private theorem augmentation_injective [Module.FaithfullyFlat A B] :
    Function.Injective (AmitsurComplex.augmentation A B M) := by
  change Function.Injective (originalDifferential A B M 0)
  apply (Module.FaithfullyFlat.lTensor_injective_iff_injective A B
    (originalDifferential A B M 0)).1
  intro x y h
  apply (comparison A B M 0).injective
  have hx := LinearMap.congr_fun (comparison_differential A B M 0) x
  have hy := LinearMap.congr_fun (comparison_differential A B M 0) y
  change extendedDifferential A B M 0 (comparison A B M 0 x) =
    comparison A B M 1 ((originalDifferential A B M 0).lTensor B x) at hx
  change extendedDifferential A B M 0 (comparison A B M 0 y) =
    comparison A B M 1 ((originalDifferential A B M 0).lTensor B y) at hy
  rw [h, ← hy] at hx
  exact (contraction_augmentation A B M _).symm.trans
    ((congrArg (contraction A B M 0) hx).trans (contraction_augmentation A B M _))

private theorem exactAt_iff_function_exact
    (K : CochainComplex (ModuleCat.{w} A) ℤ) (q : ℤ) :
    K.ExactAt q ↔ Function.Exact (K.d (q - 1) q) (K.d q (q + 1)) := by
  rw [K.exactAt_iff' (q - 1) q (q + 1)
    (ComplexShape.prev_eq' _ (ComplexShape.up_mk _ _ (by omega)))
    (ComplexShape.next_eq' _ (ComplexShape.up_mk _ _ rfl))]
  exact ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _

/-- For a faithfully flat extension, the augmented Amitsur complex is exact in every degree. -/
theorem exactAt [Module.FaithfullyFlat A B] (M : ModuleCat.{max u v w} A) (q : ℤ) :
    (AmitsurComplex.complex A B M).ExactAt q := by
  cases q with
  | ofNat p =>
    apply (exactAt_iff_function_exact A _ _).2
    cases p with
    | zero =>
      change Function.Exact ((AmitsurComplex.complex A B M).d (-1) 0)
        ((AmitsurComplex.complex A B M).d (↑(0 : ℕ)) (↑(0 : ℕ) + 1))
      rw [AmitsurComplex.complex_d_neg_one, AmitsurComplex.complex_d_ofNat]
      exact originalDifferential_exact A B M 0
    | succ p =>
      have hprev : Int.ofNat (p + 1) - 1 = (p : ℤ) := by
        change (↑(p + 1) : ℤ) - 1 = ↑p
        omega
      rw [hprev]
      change Function.Exact ((AmitsurComplex.complex A B M).d (p : ℤ) (↑p + 1))
        ((AmitsurComplex.complex A B M).d (↑(p + 1) : ℤ) (↑(p + 1) + 1))
      rw [AmitsurComplex.complex_d_ofNat, AmitsurComplex.complex_d_ofNat]
      exact originalDifferential_exact A B M (p + 1)
  | negSucc n =>
    cases n with
    | zero =>
      apply (exactAt_iff_function_exact A _ _).2
      intro x
      change (AmitsurComplex.complex A B M).d (-1) 0 x = 0 ↔ _
      rw [AmitsurComplex.complex_d_neg_one]
      constructor
      · intro hx
        have hx0 : x = 0 := augmentation_injective A B M (hx.trans (map_zero _).symm)
        subst x
        exact ⟨0, map_zero _⟩
      · rintro ⟨y, rfl⟩
        exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
          ((AmitsurComplex.complex A B M).d_comp_d (-2) (-1) 0)) y
    | succ n =>
      apply HomologicalComplex.ExactAt.of_isZero
      rw [AmitsurComplex.complex_X_of_lt A B M _ (by omega)]
      exact Limits.isZero_zero _

/-- Exactness for the augmented Amitsur complex with coefficients in any universe. -/
theorem lifted_exactAt [Module.FaithfullyFlat A B] (L : ModuleCat.{w} A) (q : ℤ) :
    ((AmitsurComplex.liftedFunctor A B).obj L).ExactAt q :=
  exactAt A B ((ModuleCat.uliftFunctor.{max u v} A).obj L) q

end DerivedFormalization.Descent.AmitsurExactness
