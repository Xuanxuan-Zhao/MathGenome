import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Polynomial
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.TensorAlgebras

namespace AdvCommAlg.Differentials
open scoped TensorProduct
open KaehlerDifferential TensorProduct
noncomputable section
universe u v w z
section Pushout
variable (A : Type u) (B₁ : Type v) (B₂ : Type w) (C : Type z)
  [CommRing A] [CommRing B₁] [CommRing B₂] [CommRing C]
  [Algebra A B₁] [Algebra A B₂] [Algebra A C]
  [Algebra B₁ C] [Algebra B₂ C] [IsScalarTower A B₁ C] [IsScalarTower A B₂ C]
  [Algebra.IsPushout A B₁ B₂ C]

private def projectionRight : Ω[C⁄A] →ₗ[C] C ⊗[B₂] Ω[B₂⁄A] :=
  (tensorKaehlerEquiv A B₁ B₂ C).symm.toLinearMap.comp (map A B₁ C C)

private lemma projectionRight_right (b : B₂) :
    projectionRight A B₁ B₂ C (D A C (algebraMap B₂ C b)) = 1 ⊗ₜ D A B₂ b := by
  apply (tensorKaehlerEquiv A B₁ B₂ C).injective
  simp [projectionRight, map_D]

private lemma projectionRight_left (b : B₁) :
    projectionRight A B₁ B₂ C (D A C (algebraMap B₁ C b)) = 0 := by
  simp [projectionRight, map_D]

/-- Differentials of a pushout are the direct sum of the extended factor differentials. -/
theorem pushout_differentials :
    ∃ e : Ω[C⁄A] ≃ₗ[C] (C ⊗[B₁] Ω[B₁⁄A]) × (C ⊗[B₂] Ω[B₂⁄A]),
      (∀ b : B₁, e (D A C (algebraMap B₁ C b)) = (1 ⊗ₜ D A B₁ b, 0)) ∧
      (∀ b : B₂, e (D A C (algebraMap B₂ C b)) = (0, 1 ⊗ₜ D A B₂ b)) := by
  have : Algebra.IsPushout A B₂ B₁ C := Algebra.IsPushout.symm inferInstance
  let f := (projectionRight A B₂ B₁ C).prod (projectionRight A B₁ B₂ C)
  let g := (mapBaseChange A B₁ C).coprod (mapBaseChange A B₂ C)
  have hf₁ (b : B₁) : f (D A C (algebraMap B₁ C b)) = (1 ⊗ₜ D A B₁ b, 0) := by
    simp [f, projectionRight_right, projectionRight_left]
  have hf₂ (b : B₂) : f (D A C (algebraMap B₂ C b)) = (0, 1 ⊗ₜ D A B₂ b) := by
    simp [f, projectionRight_right, projectionRight_left]
  have hg₁ (b : B₁) : g (1 ⊗ₜ D A B₁ b, 0) = D A C (algebraMap B₁ C b) := by
    simp [g, mapBaseChange_tmul, map_D]
  have hg₂ (b : B₂) : g (0, 1 ⊗ₜ D A B₂ b) = D A C (algebraMap B₂ C b) := by
    simp [g, mapBaseChange_tmul, map_D]
  have hgf : g.comp f = LinearMap.id := by
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    intro c
    change g (f (D A C c)) = D A C c
    induction c using (Algebra.IsPushout.out (R := A) (S := B₁) (R' := B₂) (S' := C)).inductionOn with
    | tmul b =>
      change g (f (D A C (algebraMap B₂ C b))) = D A C (algebraMap B₂ C b)
      rw [hf₂, hg₂]
    | add x y hx hy => simp only [map_add, hx, hy]
    | smul b c hc =>
      rw [Algebra.smul_def, Derivation.leibniz]
      simp only [map_add, map_smul, hc, hf₁, hg₁]
  have hfg : f.comp g = LinearMap.id := by
    apply LinearMap.prod_ext
    · apply LinearMap.restrictScalars_injective B₁
      apply TensorProduct.ext'
      intro c x
      obtain ⟨x, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective A B₁ x
      induction x with
      | tmul b d =>
        simp [g, mapBaseChange_tmul, Derivation.tensorProductTo_tmul, map_D, f,
          projectionRight_right, projectionRight_left, smul_tmul']
      | add x y hx hy => simp only [map_add, tmul_add, hx, hy]
    · apply LinearMap.restrictScalars_injective B₂
      apply TensorProduct.ext'
      intro c x
      obtain ⟨x, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective A B₂ x
      induction x with
      | tmul b d =>
        simp [g, mapBaseChange_tmul, Derivation.tensorProductTo_tmul, map_D, f,
          projectionRight_right, projectionRight_left, smul_tmul']
      | add x y hx hy => simp only [map_add, tmul_add, hx, hy]
  exact ⟨{ f with invFun := g
                  left_inv := fun x => LinearMap.congr_fun hgf x
                  right_inv := fun x => LinearMap.congr_fun hfg x }, hf₁, hf₂⟩
end Pushout
/-- KD-18, with the two structural images displayed explicitly. -/
theorem tensor_algebra_differentials :
    Specs.AdvCommAlg.Differentials.tensorAlgebraDifferentials.{u,v,w} := by
  intro A B₁ B₂ _ _ _ _ _
  letI : Algebra B₂ (B₁ ⊗[A] B₂) := Algebra.TensorProduct.rightAlgebra
  obtain ⟨e, h₁, h₂⟩ := pushout_differentials A B₁ B₂ (B₁ ⊗[A] B₂)
  refine ⟨e, fun b₁ b₂ => ?_⟩
  have ht : b₁ ⊗ₜ[A] b₂ =
      algebraMap B₁ (B₁ ⊗[A] B₂) b₁ * algebraMap B₂ (B₁ ⊗[A] B₂) b₂ := by
    simp [Algebra.TensorProduct.right_algebraMap_apply]
  rw [ht, Derivation.leibniz, map_add, map_smul, map_smul, h₁, h₂]
  simp

/-- KD-18 for B[Xᵢ]; the free summand has basis the variable differentials. -/
theorem polynomial_algebra_differentials :
    Specs.AdvCommAlg.Differentials.polynomialAlgebraDifferentials.{u,v,w} := by
  intro A B ι _ _ _
  letI : Algebra (MvPolynomial ι A) (MvPolynomial ι B) := MvPolynomial.algebraMvPolynomial
  obtain ⟨e, h₁, h₂⟩ := pushout_differentials A B (MvPolynomial ι A) (MvPolynomial ι B)
  let b := (polynomialBasis A ι).baseChange (MvPolynomial ι B)
  let e' := e.trans ((LinearEquiv.refl (MvPolynomial ι B) _).prodCongr b.repr)
  refine ⟨e', ?_, ?_⟩
  · intro a
    have ha := h₁ a
    change e (D A (MvPolynomial ι B) (MvPolynomial.C a)) = _ at ha
    simp [e', ha]
  · intro i
    have hx : algebraMap (MvPolynomial ι A) (MvPolynomial ι B) (MvPolynomial.X i) =
        MvPolynomial.X i := by
      simp
    have hb : b i = 1 ⊗ₜ D A (MvPolynomial ι A) (MvPolynomial.X i) := by
      simp [b, polynomialBasis, Module.Basis.baseChange_apply]
    have he := h₂ (MvPolynomial.X i)
    rw [hx] at he
    simp [e', he, ← hb]
end
end AdvCommAlg.Differentials
