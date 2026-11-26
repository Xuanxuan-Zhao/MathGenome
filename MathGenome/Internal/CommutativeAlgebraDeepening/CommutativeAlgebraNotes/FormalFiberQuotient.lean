import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ExcellenceDefinitions
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.FormalFiberQuotient
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-! Completion of the quotient and the canonical identification of formal fibres. -/

universe u

open scoped TensorProduct

namespace CommutativeAlgebraNotes.Excellence

open IsLocalRing (maximalIdeal)
open AdicCompletion

section CompletionComparison

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (S : Type u) [CommRing S] [Algebra R S]

/-- The module and ring filtrations on an algebra have the same quotients. -/
private def completionCoordinateEquiv (n : ℕ) :
    (S ⧸ (I ^ n • ⊤ : Submodule R S)) ≃ₗ[R]
      S ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Ideal S) :=
  (Submodule.quotEquivOfEq _ _ (by
    rw [Ideal.smul_top_eq_map, Ideal.map_pow, Ideal.smul_eq_mul, Ideal.mul_top])).trans
    (Submodule.Quotient.restrictScalarsEquiv R _)

@[simp]
private theorem completionCoordinateEquiv_mk (n : ℕ) (s : S) :
    completionCoordinateEquiv I S n (Submodule.Quotient.mk s) =
      Submodule.Quotient.mk s := rfl

private theorem completionCoordinateEquiv_factor {m n : ℕ} (hmn : m ≤ n)
    (x : S ⧸ (I ^ n • ⊤ : Submodule R S)) :
    AdicCompletion.transitionMap (I.map (algebraMap R S)) S hmn
        (completionCoordinateEquiv I S n x) =
      completionCoordinateEquiv I S m (AdicCompletion.transitionMap I S hmn x) := by
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

private def completionChange :
    AdicCompletion I S →ₗ[R] AdicCompletion (I.map (algebraMap R S)) S where
  toFun x := ⟨fun n => completionCoordinateEquiv I S n (x.val n), fun hmn => by
    rw [completionCoordinateEquiv_factor I S hmn, x.property hmn]⟩
  map_add' x y := AdicCompletion.ext fun n => map_add (completionCoordinateEquiv I S n) _ _
  map_smul' r x := AdicCompletion.ext fun n => map_smul (completionCoordinateEquiv I S n) _ _

private theorem completionChange_bijective : Function.Bijective (completionChange I S) := by
  constructor
  · intro x y h
    exact AdicCompletion.ext fun n =>
      (completionCoordinateEquiv I S n).injective (congrArg (fun z => z.val n) h)
  · intro y
    let x : AdicCompletion I S :=
      ⟨fun n => (completionCoordinateEquiv I S n).symm (y.val n), fun hmn => by
        apply (completionCoordinateEquiv I S _).injective
        rw [← completionCoordinateEquiv_factor I S hmn, LinearEquiv.apply_symm_apply,
          LinearEquiv.apply_symm_apply, y.property hmn]⟩
    exact ⟨x, AdicCompletion.ext fun n => (completionCoordinateEquiv I S n).apply_symm_apply _⟩

private noncomputable def completionTensor :
    S ⊗[R] AdicCompletion I R →ₗ[R] AdicCompletion (I.map (algebraMap R S)) S :=
  completionChange I S ∘ₗ (AdicCompletion.ofTensorProduct I S).restrictScalars R ∘ₗ
    (TensorProduct.comm R S (AdicCompletion I R)).toLinearMap

private theorem completionTensor_eval (n : ℕ) (s : S) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ (I.map (algebraMap R S)) n (completionTensor I S (s ⊗ₜ[R] x)) =
      Ideal.Quotient.mk _ s *
        Ideal.quotientMap _ (algebraMap R S)
          (Ideal.map_le_iff_le_comap.mp (by rw [Ideal.map_pow])) (AdicCompletion.evalₐ I n x) := by
  let J := I.map (algebraMap R S)
  -- Choose a representative in `R` for the coordinate of `x`.
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  have hJ : J ^ n • (⊤ : Ideal S) ≤ J ^ n := Ideal.mul_le_left
  rw [← hr, Ideal.quotientMap_mk, ← AdicCompletion.factor_eval_eq_evalₐ J _ hJ]
  change Ideal.Quotient.factor hJ (completionCoordinateEquiv I S n
    ((AdicCompletion.ofTensorProduct I S (x ⊗ₜ[R] s)).val n)) = _
  rw [AdicCompletion.ofTensorProduct_tmul, AdicCompletion.smul_eval,
    AdicCompletion.val_smul_eq_evalₐ_smul, ← hr]
  change Ideal.Quotient.factor hJ
    (completionCoordinateEquiv I S n (Ideal.Quotient.mk (I ^ n) r • Submodule.Quotient.mk s)) = _
  rw [Module.Quotient.mk_smul_mk, completionCoordinateEquiv_mk]
  change Ideal.Quotient.factor hJ (Ideal.Quotient.mk _ (r • s)) = _
  rw [Ideal.Quotient.factor_mk, Algebra.smul_def, map_mul, mul_comm]

private noncomputable def completionTensorEquiv [IsNoetherianRing R] [Module.Finite R S] :
    S ⊗[R] AdicCompletion I R ≃ₐ[S] AdicCompletion (I.map (algebraMap R S)) S := by
  let e := LinearEquiv.ofBijective (completionTensor I S)
    ((completionChange_bijective I S).comp
      ((AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I S).comp
        (TensorProduct.comm R S (AdicCompletion I R)).bijective))
  have hmul (a b : S ⊗[R] AdicCompletion I R) :
      completionTensor I S (a * b) = completionTensor I S a * completionTensor I S b := by
    revert a b
    apply LinearMap.map_mul_of_map_mul_tmul
    intro s₁ s₂ x₁ x₂
    apply AdicCompletion.ext_evalₐ
    intro n
    simp only [completionTensor_eval, map_mul]
    ac_rfl
  refine { __ := e, map_mul' := hmul, commutes' := fun s => ?_ }
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ _ n (completionTensor I S (s ⊗ₜ[R] 1)) =
    AdicCompletion.evalₐ _ n (AdicCompletion.of _ S s)
  rw [completionTensor_eval, AdicCompletion.evalₐ_of, map_one, map_one, mul_one]

end CompletionComparison

/-- The formal fibre at `q` is canonically the generic fibre of the completed
quotient. The coordinate and pure-tensor formulas specify both comparison maps. -/
theorem formalFiberQuotient : Specs.formalFiberQuotientType.{u} := by
  intro A _ _ _ q _
  let _ := Specs.formalFiberQuotientAlgebra q
  let D := A ⧸ q
  let C := AdicCompletion (maximalIdeal A) A
  let T := AdicCompletion (Specs.quotientMaximalIdeal q) D
  let K := q.ResidueField
  let F := FractionRing D
  let c : D ⊗[A] C ≃ₐ[D] T := completionTensorEquiv (maximalIdeal A) D
  let f : C →ₐ[A] T :=
    (c.toAlgHom.restrictScalars A).comp Algebra.TensorProduct.includeRight
  let e₁ : FormalFiber A q ≃ₐ[K] K ⊗[D] (D ⊗[A] C) :=
    (Algebra.TensorProduct.cancelBaseChange A D K K C).symm
  let e₂ : K ⊗[D] (D ⊗[A] C) ≃ₐ[K] K ⊗[D] T :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) c
  let e₃ : K ⊗[D] T ≃ₐ[D] F ⊗[D] T :=
    Algebra.TensorProduct.congr (Specs.residueFieldToFractionRing q) (AlgEquiv.refl : T ≃ₐ[D] T)
  let e : FormalFiber A q ≃+* T ⊗[D] F :=
    (e₁.trans e₂).toRingEquiv.trans
      (e₃.trans (Algebra.TensorProduct.comm D F T)).toRingEquiv
  have he (k : K) (x : C) :
      e (k ⊗ₜ[A] x) = f x ⊗ₜ[D] Specs.residueFieldToFractionRing q k := by
    simp [e, e₁, e₂, e₃, f]
  let eAlg : FormalFiber A q ≃ₐ[K] T ⊗[D] F :=
    { __ := e
      commutes' k := by
        change e (k ⊗ₜ[A] (1 : C)) = (1 : T) ⊗ₜ[D] Specs.residueFieldToFractionRing q k
        rw [he, map_one] }
  refine ⟨f, eAlg, ?_, he⟩
  intro x n
  change AdicCompletion.evalₐ _ n (completionTensor (maximalIdeal A) D (1 ⊗ₜ[A] x)) = _
  rw [completionTensor_eval, map_one, one_mul]
  rfl

end CommutativeAlgebraNotes.Excellence
