import MathGenome.Internal.Specs.D05.M15.PolynomialPolarization.FormProducts
import MathGenome.Internal.D05.M15.PolynomialPolarization.ShuffleProduct
import MathGenome.Internal.D05.M15.PolynomialBridge
import MathGenome.Internal.D05.M15.SymmetricBasis.PairingContractions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
open scoped Classical DirectSum
namespace D05.M15.PolynomialPolarization.FormProducts
open Specs.D05.M15.Symmetric Specs.D05.M15.SymmetricBasis
open Specs.D05.M15.SymmetricBasis.PerfectPairing
open Specs.D05.M15.SymmetricBasis.PairingContractions
open Specs.D05.M15.PolynomialPolarization.ShuffleProduct
open Specs.D05.M15.PolynomialPolarization.FormProducts
open D05.M15.SymmetricBasis.PerfectPairing
universe u v
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

private theorem factorial_ne_zero [CharZero K] (p : ℕ) : (p.factorial : K) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p)

theorem permanent_isomorphism :
    Specs.D05.M15.PolynomialPolarization.FormProducts.permanent_isomorphism :=
  ShuffleProduct.permanent_isomorphism

theorem graded_algebra_isomorphism :
    Specs.D05.M15.PolynomialPolarization.FormProducts.graded_algebra_isomorphism :=
  ShuffleProduct.graded_algebra_isomorphism

theorem normalization : Specs.D05.M15.PolynomialPolarization.FormProducts.normalization :=
  ShuffleProduct.normalization

theorem averaged_symmetric :
    Specs.D05.M15.PolynomialPolarization.FormProducts.averaged_symmetric := by
  intro K V _ _ _ p q B C x τ
  change ((p+q).factorial : K)⁻¹ * _ = ((p+q).factorial : K)⁻¹ * _
  congr 1
  exact ShuffleProduct.permutation_sum_symmetric _ x τ

theorem averaged_diagonal :
    Specs.D05.M15.PolynomialPolarization.FormProducts.averaged_diagonal := by
  intro K V _ _ _ _ p q B C v
  simp only [Specs.D05.M15.PolynomialPolarization.ShuffleProduct.averagedProduct,
    _root_.smul_apply, MultilinearMap.domDomCongr_apply,
    ShuffleProduct.blockProduct_apply, Function.comp_def, _root_.sum_apply,
    Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (factorial_ne_zero _), one_mul]

/-- The binomial coefficient as a field element, without natural-number division. -/
theorem factorial_ratio [CharZero K] (p q : ℕ) :
    (((p+q).factorial : K) / ((p.factorial : K) * (q.factorial : K))) =
      ((p+q).choose p : K) := by
  apply (div_eq_iff (mul_ne_zero (factorial_ne_zero p) (factorial_ne_zero q))).mpr
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right p q)
  rw [Nat.add_sub_cancel_left] at h
  have hc := congrArg (fun n : ℕ => (n : K)) h
  simpa only [Nat.cast_mul, mul_assoc] using hc.symm

theorem shuffle_diagonal : Specs.D05.M15.PolynomialPolarization.FormProducts.shuffle_diagonal := by
  intro K V _ _ _ _ p q B C v
  rw [normalization B C]
  change _ * Specs.D05.M15.PolynomialPolarization.ShuffleProduct.averagedProduct B C (fun _ => v) = _
  rw [averaged_diagonal, factorial_ratio]
  exact (mul_assoc _ _ _).symm

theorem normalized_diagonal_mul :
    Specs.D05.M15.PolynomialPolarization.FormProducts.normalized_diagonal_mul := by
  intro K V _ _ _ _ p q B C v
  unfold normalizedDiagonal _root_.D05.M15.PolynomialPolarization.rawDiagonal
  rw [normalization B C, _root_.smul_apply, smul_eq_mul, averaged_diagonal]
  field_simp [factorial_ne_zero (K := K) (p+q), factorial_ne_zero (K := K) p,
    factorial_ne_zero (K := K) q]

/-- Evaluation of a permanent map is the canonical permanent pairing. -/
theorem permanent_map_pairing (p : ℕ)
    (R : symmetricPower K (Module.Dual K V) p →ₗ[K] symmetricForms K V p)
    (hR : IsPermanentMap p R) (a : symmetricPower K (Module.Dual K V) p)
    (x : Fin p → V) : (R a).val x = pairing p a (elementary K V p x) := by
  have h : (formEvaluation x).comp R = (pairing (K := K) (V := V) p).flip (elementary K V p x) := by
    apply power_ext p
    intro φ
    exact (hR φ x).trans (pairing_elementary p φ x).symm
  exact LinearMap.congr_fun h a

theorem insertion : Specs.D05.M15.PolynomialPolarization.FormProducts.insertion := by
  intro K V _ _ _ p v C hC R S hR hS a x
  rw [permanent_map_pairing p R hR, permanent_map_pairing (p+1) S hS]
  have h := D05.M15.SymmetricBasis.PairingContractions.adjoint v p C
    (D05.M15.SymmetricBasis.PairingContractions.multiplicationMap v p) hC
    (D05.M15.SymmetricBasis.PairingContractions.multiplicationMap_bridge v p)
    (pairing p) (pairing (p+1)) (pairing_elementary p) (pairing_elementary (p+1)) a
    (elementary K V p x)
  rw [D05.M15.SymmetricBasis.PairingContractions.multiplication_formula v p _
    (D05.M15.SymmetricBasis.PairingContractions.multiplicationMap_bridge v p) x] at h
  exact h

theorem normalized_insertion :
    Specs.D05.M15.PolynomialPolarization.FormProducts.normalized_insertion := by
  intro K V _ _ _ _ p v C hC R S hR hS a x
  change (p.factorial : K)⁻¹ * (R (C a)).val x =
    (p+1 : ℕ) • (((p+1).factorial : K)⁻¹ * (S a).val (Fin.cons v x))
  rw [insertion p v C hC R S hR hS, nsmul_eq_mul, Nat.factorial_succ, Nat.cast_mul]
  have hp : (p.factorial : K) ≠ 0 := factorial_ne_zero p
  have hn : ((p+1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero p)
  field_simp



/-- Averaging is bilinear in the two symmetric forms. -/
theorem averaged_smul {p q : ℕ} (a b : K) (B : symmetricForms K V p)
    (C : symmetricForms K V q) :
    Specs.D05.M15.PolynomialPolarization.ShuffleProduct.averagedProduct (a • B) (b • C) =
      (a * b) • Specs.D05.M15.PolynomialPolarization.ShuffleProduct.averagedProduct B C := by
  ext x
  simp only [Specs.D05.M15.PolynomialPolarization.ShuffleProduct.averagedProduct,
    _root_.smul_apply, _root_.sum_apply, MultilinearMap.domDomCongr_apply,
    ShuffleProduct.blockProduct_apply, Submodule.coe_smul_of_tower, smul_eq_mul]
  simp only [← Finset.mul_sum, mul_assoc, mul_left_comm]

/-- Rescale the permanent isomorphism by precisely the inverse degree factorial. -/
def averagedEquiv [CharZero K] [FiniteDimensional K V] (p : ℕ) :
    symmetricPower K (Module.Dual K V) p ≃ₗ[K] symmetricForms K V p :=
  (ShuffleProduct.permanentEquiv p).trans
    (LinearEquiv.smulOfNeZero K (symmetricForms K V p) (p.factorial : K)⁻¹
      (inv_ne_zero (factorial_ne_zero p)))

@[simp] theorem averagedEquiv_apply [CharZero K] [FiniteDimensional K V] (p : ℕ)
    (a : symmetricPower K (Module.Dual K V) p) :
    averagedEquiv p a = (p.factorial : K)⁻¹ • ShuffleProduct.permanentEquiv p a := rfl

theorem product_correspondence :
    Specs.D05.M15.PolynomialPolarization.FormProducts.product_correspondence := by
  intro K V _ _ _ _ _
  refine ⟨ShuffleProduct.permanentEquiv, averagedEquiv, ShuffleProduct.powerMul,
    ShuffleProduct.permanentEquiv_elementary, (fun _ _ => rfl), ?_⟩
  intro p q a b
  refine ⟨ShuffleProduct.powerMul_inclusion p q a b,
    ShuffleProduct.permanentEquiv_mul p q a b, ?_⟩
  simp only [averagedEquiv_apply, Submodule.coe_smul_of_tower]
  rw [ShuffleProduct.permanentEquiv_mul, normalization, averaged_smul,
    smul_smul]
  congr 1
  field_simp [factorial_ne_zero (K := K) (p+q), factorial_ne_zero (K := K) p,
    factorial_ne_zero (K := K) q]

/-- The elementary permanent has p! identical summands on a diagonal. -/
theorem permanent_diagonal (p : ℕ) (φ : Fin p → Module.Dual K V) (v : V) :
    permanent φ (fun _ => v) = (p.factorial : K) * ∏ i, φ i v := by
  simp [permanent, Fintype.card_perm]

theorem polynomial_evaluation :
    Specs.D05.M15.PolynomialPolarization.FormProducts.polynomial_evaluation := by
  intro K V _ _ _ _ p R hR a v
  let L : symmetricPower K (Module.Dual K V) p →ₗ[K] K :=
    (p.factorial : K)⁻¹ • ((formEvaluation (fun _ => v)).comp R)
  let M : symmetricPower K (Module.Dual K V) p →ₗ[K] K :=
    ((LinearMap.proj (R := K) (φ := fun _ : V => K) v).comp
      (Specs.D05.M15.PolynomialBridge.evaluation K V).toLinearMap).comp
      (powerInclusion (K := K) (V := Module.Dual K V) p)
  have h : L = M := by
    apply power_ext p
    intro φ
    change (p.factorial : K)⁻¹ * (R (elementary K (Module.Dual K V) p φ)).val
      (fun _ => v) = Specs.D05.M15.PolynomialBridge.evaluation K V
        (powerInclusion (K := K) (V := Module.Dual K V) p
          (elementary K (Module.Dual K V) p φ)) v
    rw [hR, permanent_diagonal, D05.M15.SymmetricBasis.inclusion_elementary,
      map_prod, Finset.prod_apply]
    rw [← mul_assoc, inv_mul_cancel₀ (factorial_ne_zero p), one_mul]
    apply Finset.prod_congr rfl
    intro i _
    exact (_root_.D05.M15.PolynomialBridge.evaluation_generator (φ i) v).symm
  exact LinearMap.congr_fun h a

theorem degree_zero : Specs.D05.M15.PolynomialPolarization.FormProducts.degree_zero := by
  intro K V _ _ _ R hR c v
  have h (x : Fin 0 → V) :
      (R (c • elementary K (Module.Dual K V) 0 (fun i => Fin.elim0 i))).val x = c := by
    rw [map_smul]
    change c * (R (elementary K (Module.Dual K V) 0 (fun i => Fin.elim0 i))).val x = c
    rw [hR]
    simp [permanent]
  exact ⟨h _, by simpa [normalizedDiagonal, _root_.D05.M15.PolynomialPolarization.rawDiagonal] using h (fun _ => v)⟩

theorem linear_form_correction :
    Specs.D05.M15.PolynomialPolarization.FormProducts.linear_form_correction := by
  intro K _ _
  constructor
  · intro V _ _ B C v
    simpa using shuffle_diagonal B C v
  · let B : symmetricForms K K 1 :=
      ⟨MultilinearMap.mkPiRing K (Fin 1) 1, by
        intro x σ
        congr 1
        funext i
        exact congrArg x (Subsingleton.elim _ _)⟩
    refine ⟨B, B, 1, ?_⟩
    rw [shuffle_diagonal]
    simp [B, MultilinearMap.mkPiRing_apply]


@[simp] theorem normalizedEvaluation_single (p : ℕ) (B : symmetricForms K V p) :
    normalizedEvaluation (formSingle p B) = normalizedDiagonal B.val := by
  rw [formSingle, normalizedEvaluation, DirectSum.toModule_lof]
  rfl

theorem diagonal_algebra_map :
    Specs.D05.M15.PolynomialPolarization.FormProducts.diagonal_algebra_map := by
  intro K V _ _ _ _ _
  obtain ⟨A, AK, E, R, hAdd, hSmul, hR, hE, hProd, hUnit⟩ :=
    (ShuffleProduct.graded_algebra_isomorphism (K := K) (V := V))
  let standardAdd : AddCommGroup (formAlgebra K V) := inferInstance
  let standardModule : Module K (formAlgebra K V) := inferInstance
  letI := A
  letI := AK
  let F : formAlgebra K V →ₐ[K] (V → K) :=
    (Specs.D05.M15.PolynomialBridge.evaluation K V).comp E.symm.toAlgHom
  have hsingle (p : ℕ) (B : symmetricForms K V p) :
      F (formSingle p B) = normalizedDiagonal B.val := by
    let a := (R p).symm B
    have ha : E (powerInclusion (K := K) (V := Module.Dual K V) p a) = formSingle p B := by
      simpa only [a, LinearEquiv.apply_symm_apply] using hE p a
    rw [← ha]
    change Specs.D05.M15.PolynomialBridge.evaluation K V
      (E.symm (E (powerInclusion (K := K) (V := Module.Dual K V) p a))) = _
    rw [AlgEquiv.symm_apply_apply]
    funext v
    simpa only [a, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
      (polynomial_evaluation p (R p).toLinearMap (hR p) a v).symm
  have hFsmul (c : K) (x : formAlgebra K V) :
      F (@SMul.smul K (formAlgebra K V) AK.toSMul c x) = c • F x :=
    by
      have hs := @Algebra.smul_def' K (formAlgebra K V) _ A.toSemiring AK c x
      calc
        F (@SMul.smul K (formAlgebra K V) AK.toSMul c x) =
            F (AK.algebraMap c * x) := congrArg F hs
        _ = c • F x := by
          rw [map_mul, F.commutes, ← Algebra.smul_def]
  have heval (x : formAlgebra K V) : F x = normalizedEvaluation x := by
    letI := standardAdd
    letI := standardModule
    let L : formAlgebra K V →ₗ[K] (V → K) :=
      { toFun := F
        map_add' := by
          intro x y
          change F (formAdd x y) = F x + F y
          rw [← hAdd, map_add]
        map_smul' := by
          intro c x
          change F (formSmul c x) = c • F x
          rw [← hSmul]
          exact hFsmul c x }
    have h : L = normalizedEvaluation := by
      apply DirectSum.linearMap_ext
      intro p
      apply LinearMap.ext
      intro B
      change F (formSingle p B) = normalizedEvaluation (formSingle p B)
      rw [hsingle, normalizedEvaluation_single]
    exact LinearMap.congr_fun h x
  refine ⟨A, AK, F, hAdd, hSmul, hProd, heval, ?_, ?_⟩
  · exact (D05.M15.PolynomialBridge.evaluation_injective (Module.finBasis K V)).comp
      E.symm.injective
  · intro f
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨E.symm x, hx⟩
    · rintro ⟨a, ha⟩
      refine ⟨E a, ?_⟩
      change Specs.D05.M15.PolynomialBridge.evaluation K V (E.symm (E a)) = f
      rw [AlgEquiv.symm_apply_apply, ha]

end D05.M15.PolynomialPolarization.FormProducts
