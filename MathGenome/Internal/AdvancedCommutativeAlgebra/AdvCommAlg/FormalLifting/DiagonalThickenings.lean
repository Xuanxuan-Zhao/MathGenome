import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.DiagonalThickenings
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.IdealThickenings
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.Permanence
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.EtaleDifferentials
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Diagonal

noncomputable section
open scoped TensorProduct

namespace AdvCommAlg.FormalLifting.DiagonalThickenings

open Specs.AdvCommAlg.FormalLifting.DiagonalThickenings
open Specs.AdvCommAlg.Differentials (diagonalIdeal)

universe u v w
variable (A : Type u) (B : Type v) (D : Type w)
    [CommRing A] [CommRing B] [CommRing D]
    [Algebra A B] [Algebra B D] [Algebra A D] [IsScalarTower A B D]

/-- Extend just the first tensor factor. -/
def mixedTensorMap : B ⊗[A] B →ₐ[B] D ⊗[A] B :=
  Algebra.TensorProduct.map (Algebra.ofId B D) (AlgHom.id A B)

/-- Evaluation d ⊗ b ↦ d b_D. -/
def mixedEvaluation : D ⊗[A] B →ₐ[D] D :=
  Algebra.TensorProduct.lift (AlgHom.id D D) (IsScalarTower.toAlgHom A B D)
    (fun _ _ => Commute.all _ _)

/-- The extended diagonal ideal is exactly the kernel of evaluation.
This is a direct tensor calculation and uses no flatness. -/
lemma extended_diagonal_eq_kernel :
    (diagonalIdeal A B).map (mixedTensorMap A B D).toRingHom =
      RingHom.ker (mixedEvaluation A B D) := by
  let K := (diagonalIdeal A B).map (mixedTensorMap A B D).toRingHom
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    have h : ((mixedEvaluation A B D).restrictScalars A).comp
        ((mixedTensorMap A B D).restrictScalars A) =
        (IsScalarTower.toAlgHom A B D).comp (Algebra.TensorProduct.lmul' A) := by
      ext <;> simp [mixedEvaluation, mixedTensorMap]
    have hx' : Algebra.TensorProduct.lmul' A x = 0 := hx
    change mixedEvaluation A B D (mixedTensorMap A B D x) = 0
    simpa [hx'] using AlgHom.congr_fun h x
  · have hsub (x : D ⊗[A] B) :
        x - mixedEvaluation A B D x ⊗ₜ[A] (1 : B) ∈ K := by
      induction x using TensorProduct.inductionOn with
      | tmul d b =>
        have hmem : mixedTensorMap A B D ((1 : B) ⊗ₜ[A] b - b ⊗ₜ[A] (1 : B)) ∈ K :=
          Ideal.mem_map_of_mem _ (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal A b)
        have heq : d ⊗ₜ[A] b - mixedEvaluation A B D (d ⊗ₜ[A] b) ⊗ₜ[A] (1 : B) =
            (d ⊗ₜ[A] (1 : B)) *
              mixedTensorMap A B D ((1 : B) ⊗ₜ[A] b - b ⊗ₜ[A] (1 : B)) := by
          simp [mixedTensorMap, mixedEvaluation, mul_sub,
            Algebra.TensorProduct.tmul_mul_tmul]
        rw [heq]
        exact K.mul_mem_left _ hmem
      | add x y hx hy =>
        simpa only [map_add, TensorProduct.add_tmul, ← sub_add_sub_comm] using K.add_mem hx hy
    intro x hx
    have hx' : mixedEvaluation A B D x = 0 := hx
    change x ∈ K
    simpa [hx'] using hsub x

/-- Extending scalars in the power quotient gives the mixed tensor quotient. -/
def mixedQuotientEquiv (n : ℕ) :
    D ⊗[B] Parts A B n ≃ₐ[D]
      (D ⊗[A] B) ⧸ (RingHom.ker (mixedEvaluation A B D)) ^ (n + 1) := by
  let e := Algebra.TensorProduct.cancelBaseChange A B D D B
  refine (Algebra.TensorProduct.tensorQuotientEquiv (R := B) D (B ⊗[A] B) D
    ((diagonalIdeal A B) ^ (n + 1))).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  change _ = Ideal.map e.toRingHom
    (Ideal.map (Algebra.TensorProduct.includeRight (R := B) (A := D)).toRingHom _)
  rw [Ideal.map_map, ← extended_diagonal_eq_kernel A B D, Ideal.map_pow]
  have hm : (mixedTensorMap A B D).toRingHom =
      e.toRingHom.comp (Algebra.TensorProduct.includeRight (R := B) (A := D)).toRingHom := by
    apply RingHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul b c => simp [e, mixedTensorMap, Algebra.smul_def]
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  rw [hm]

lemma mixedQuotientEquiv_tmul (n : ℕ) (d : D) (b c : B) :
    mixedQuotientEquiv A B D n (d ⊗ₜ[B] Ideal.Quotient.mk _ (b ⊗ₜ[A] c)) =
      Ideal.Quotient.mk _ ((d * algebraMap B D b) ⊗ₜ[A] c) := by
  simp [mixedQuotientEquiv, Algebra.smul_def, mul_comm]

/-- Extend the second factor B → D. -/
def secondTensorMap : D ⊗[A] B →ₐ[D] D ⊗[A] D :=
  Algebra.TensorProduct.map (AlgHom.id D D) (IsScalarTower.toAlgHom A B D)

/-- This is the base change of B → D along its right-factor map to D ⊗[A] B. -/
lemma secondTensorMap_formallyEtale (hEt : FormallyEtale B D) :
    @Algebra.FormallyEtale (D ⊗[A] B) (D ⊗[A] D) _ _
      (secondTensorMap A B D).toRingHom.toAlgebra := by
  let : Algebra.FormallyEtale B D := (formallyEtale_iff B D).mp hEt
  let : Algebra B (D ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let : Module B (D ⊗[A] B) := Algebra.toModule
  let : Algebra (D ⊗[A] B) (D ⊗[A] D) :=
    (secondTensorMap A B D).toRingHom.toAlgebra
  let e₁ := Algebra.TensorProduct.comm B (D ⊗[A] B) D
  let e₂ := Algebra.TensorProduct.congr (AlgEquiv.refl : D ≃ₐ[B] D)
    (Algebra.TensorProduct.commRight A B D).symm
  let e₃ := Algebra.TensorProduct.cancelBaseChange A B D D D
  let e₄ := Algebra.TensorProduct.comm A D D
  let eRing := e₁.toRingEquiv.trans (e₂.toRingEquiv.trans
    (e₃.toRingEquiv.trans e₄.toRingEquiv))
  have he (d₁ : D) (b : B) (d₂ : D) :
      eRing ((d₁ ⊗ₜ[A] b) ⊗ₜ[B] d₂) = d₁ ⊗ₜ[A] (algebraMap B D b * d₂) := by
    simp [eRing, e₁, e₂, e₃, e₄, Algebra.smul_def]
  let e : ((D ⊗[A] B) ⊗[B] D) ≃ₐ[D ⊗[A] B] D ⊗[A] D :=
    { eRing with
      commutes' := by
        intro s
        change eRing (s ⊗ₜ[B] (1 : D)) = secondTensorMap A B D s
        induction s using TensorProduct.inductionOn with
        | tmul d b => simp [he, secondTensorMap]
        | add x y hx hy => simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) hx hy }
  exact Algebra.FormallyEtale.of_equiv e

lemma secondTensorMap_comap :
    (diagonalIdeal A D).comap (secondTensorMap A B D).toRingHom =
      RingHom.ker (mixedEvaluation A B D) := by
  have h : (Algebra.TensorProduct.lmul' A (S := D)).comp
      ((secondTensorMap A B D).restrictScalars A) =
      (mixedEvaluation A B D).restrictScalars A := by
    ext <;> simp [secondTensorMap, mixedEvaluation]
  ext x
  change Algebra.TensorProduct.lmul' A (secondTensorMap A B D x) = 0 ↔
    mixedEvaluation A B D x = 0
  exact iff_of_eq (congrArg (· = 0) (AlgHom.congr_fun h x))

lemma comparison_tmul (n : ℕ) (d : D) (b c : B) :
    comparison A B D n (d ⊗ₜ[B] Ideal.Quotient.mk _ (b ⊗ₜ[A] c)) =
      Ideal.Quotient.mk _ ((d * algebraMap B D b) ⊗ₜ[A] algebraMap B D c) := by
  change Ideal.Quotient.mk _ (d ⊗ₜ[A] (1 : D)) *
    Ideal.Quotient.mk _ (algebraMap B D b ⊗ₜ[A] algebraMap B D c) = _
  rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- The canonical map is invertible in every nonnegative order. -/
theorem all_orders : allOrders.{u,v,w} := by
  intro A B D _ _ _ _ _ _ _ hEt n
  let : Algebra (D ⊗[A] B) (D ⊗[A] D) :=
    (secondTensorMap A B D).toRingHom.toAlgebra
  have hform : FormallyEtale (D ⊗[A] B) (D ⊗[A] D) :=
    (formallyEtale_iff _ _).mpr (secondTensorMap_formallyEtale A B D hEt)
  have hsurj : Function.Surjective
      ((Ideal.Quotient.mk (diagonalIdeal A D)).comp
        (algebraMap (D ⊗[A] B) (D ⊗[A] D))) := by
    intro q
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨Algebra.TensorProduct.lmul' A t ⊗ₜ[A] (1 : B), ?_⟩
    apply Ideal.Quotient.eq.mpr
    change Algebra.TensorProduct.lmul' A
      (secondTensorMap A B D (Algebra.TensorProduct.lmul' A t ⊗ₜ[A] (1 : B)) - t) = 0
    simp [secondTensorMap]
  have hbij := powerMap_bijective hform (diagonalIdeal A D) hsurj (n + 1) (by omega)
  have hK : RingHom.ker (mixedEvaluation A B D) =
      Specs.AdvCommAlg.FormalLifting.Thickenings.baseIdeal
        (A := D ⊗[A] B) (diagonalIdeal A D) :=
    (secondTensorMap_comap A B D).symm
  let e := (mixedQuotientEquiv A B D n).trans
    (Ideal.quotientEquivAlgOfEq D (congrArg (· ^ (n + 1)) hK))
  have he (d : D) (b c : B) :
      e (d ⊗ₜ[B] Ideal.Quotient.mk _ (b ⊗ₜ[A] c)) =
        Ideal.Quotient.mk _ ((d * algebraMap B D b) ⊗ₜ[A] c) := by
    simp [e, mixedQuotientEquiv_tmul]
  have hc : ∀ x, Specs.AdvCommAlg.FormalLifting.Thickenings.powerMap
      (A := D ⊗[A] B) (diagonalIdeal A D) (n + 1) (e x) = comparison A B D n x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul d q =>
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective q
      induction t using TensorProduct.inductionOn with
      | tmul b c =>
        rw [he, comparison_tmul]
        rfl
      | add x y hx hy =>
        simpa only [map_add, TensorProduct.tmul_add] using congrArg₂ (· + ·) hx hy
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  have hh := hbij.comp e.bijective
  simpa only [Function.comp_def, hc] using hh

lemma cotangentInclusion_D (b : B) :
    cotangentInclusion A B (KaehlerDifferential.D A B b) =
      Ideal.Quotient.mk _ ((1 : B) ⊗ₜ[A] b - b ⊗ₜ[A] (1 : B)) := rfl

/-- The restriction of the first-order ring map is exactly the natural
map on differentials, under the actual diagonal inclusions. -/
lemma first_order_square :
    (comparison A B D 1).toLinearMap.comp (extendedCotangentInclusion A B D) =
      (cotangentInclusion A D).comp (KaehlerDifferential.mapBaseChange A B D) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro d q
  change comparison A B D 1 (d ⊗ₜ[B] cotangentInclusion A B q) =
    cotangentInclusion A D (KaehlerDifferential.mapBaseChange A B D (d ⊗ₜ[B] q))
  have hq : q ∈ Submodule.span B (Set.range (KaehlerDifferential.D A B)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  revert d
  refine Submodule.span_induction (R := B) (M := KaehlerDifferential A B) ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨b, rfl⟩ d
    rw [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D,
      map_smul, cotangentInclusion_D, cotangentInclusion_D]
    simp only [map_sub, TensorProduct.tmul_sub]
    rw [comparison_tmul, comparison_tmul]
    simp only [map_one, mul_one]
    rw [Algebra.smul_def]
    change Ideal.Quotient.mk ((diagonalIdeal A D) ^ 2) (d ⊗ₜ[A] algebraMap B D b) -
      Ideal.Quotient.mk ((diagonalIdeal A D) ^ 2) ((d * algebraMap B D b) ⊗ₜ[A] (1 : D)) =
      Ideal.Quotient.mk ((diagonalIdeal A D) ^ 2) (d ⊗ₜ[A] (1 : D)) *
        (Ideal.Quotient.mk ((diagonalIdeal A D) ^ 2) ((1 : D) ⊗ₜ[A] algebraMap B D b) -
          Ideal.Quotient.mk ((diagonalIdeal A D) ^ 2) (algebraMap B D b ⊗ₜ[A] (1 : D)))
    rw [mul_sub, ← map_mul, ← map_mul]
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  · intro d
    simp
  · intro x y _ _ hx hy d
    simpa only [map_add, TensorProduct.tmul_add] using congrArg₂ (· + ·) (hx d) (hy d)
  · intro b q _ hq d
    simpa only [map_smul, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul'] using hq (b • d)

/-- Under KD-03 the induced map of square-zero diagonal ideals is FL-11.
Injectivity of the scalar-extended inclusion follows from this square and
the FL-11 isomorphism, without a flatness hypothesis. -/
theorem first_order : firstOrder.{u,v,w} := by
  intro A B D _ _ _ _ _ _ _ hEt
  obtain ⟨e, he, _⟩ := etale_differentials A B D hEt
  have hsq := first_order_square A B D
  change (comparison A B D 1).toLinearMap.comp (extendedCotangentInclusion A B D) =
    (cotangentInclusion A D).comp (Specs.AdvCommAlg.Differentials.towerMapUValue A B D) at hsq
  rw [← he] at hsq
  refine ⟨e, he, ?_, hsq⟩
  intro x y hxy
  apply e.injective
  apply (diagonalIdeal A D).cotangentToQuotientSquare_injective
  have hh := congrArg (comparison A B D 1) hxy
  change cotangentInclusion A D (e x) = cotangentInclusion A D (e y)
  change ((comparison A B D 1).toLinearMap.comp (extendedCotangentInclusion A B D)) x =
    ((comparison A B D 1).toLinearMap.comp (extendedCotangentInclusion A B D)) y at hh
  rw [hsq] at hh
  exact hh

end AdvCommAlg.FormalLifting.DiagonalThickenings
