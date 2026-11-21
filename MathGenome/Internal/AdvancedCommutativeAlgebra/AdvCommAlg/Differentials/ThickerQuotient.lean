import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.SurjectiveBase
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Polynomial
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.ThickerQuotient
import Mathlib.RingTheory.Polynomial.Quotient

namespace AdvCommAlg.Differentials
universe u v w z
noncomputable section
open TensorProduct
open Specs.AdvCommAlg.Differentials (restrictionMap powerQuotientAlgebra)

/-- A derivation lowers the ideal-adic filtration by one. -/
theorem derivation_ideal_power (A : Type u) (B : Type v) (M : Type w)
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M]
    [Module B M] [Module A M] [IsScalarTower A B M]
    (d : Derivation A B M) (I : Ideal B) (n : ℕ) {x : B}
    (hx : x ∈ I ^ (n + 1)) : d x ∈ I ^ n • (⊤ : Submodule B M) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [d.leibniz]
      apply Submodule.add_mem
      · exact Submodule.smul_mem_smul ha trivial
      · have hd := ih ha
        have hmem := Submodule.smul_mem_smul hb hd
        simpa [smul_smul, ← pow_succ'] using hmem
    · intro a b ha hb
      simpa only [map_add] using Submodule.add_mem _ ha hb

/-- Descent of a derivation that kills the quotient ideal. -/
def quotientDerivation (A : Type u) (B : Type v) (M : Type w)
    [CommRing A] [CommRing B] [Algebra A B] (J : Ideal B)
    [AddCommGroup M] [Module A M] [Module B M] [Module (B ⧸ J) M]
    [IsScalarTower A B M] [IsScalarTower B (B ⧸ J) M]
    (d : Derivation A B M) (hd : ∀ x ∈ J, d x = 0) : Derivation A (B ⧸ J) M where
  toLinearMap := (J.restrictScalars A).liftQ d.toLinearMap (by intro x hx; exact hd x hx)
  map_one_eq_zero' := d.map_one_eq_zero
  leibniz' x y := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    change d (x * y) = Ideal.Quotient.mk J x • d y + Ideal.Quotient.mk J y • d x
    simpa only [← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul] using
      d.leibniz x y

@[simp] theorem quotientDerivation_mk (A : Type u) (B : Type v) (M : Type w)
    [CommRing A] [CommRing B] [Algebra A B] (J : Ideal B)
    [AddCommGroup M] [Module A M] [Module B M] [Module (B ⧸ J) M]
    [IsScalarTower A B M] [IsScalarTower B (B ⧸ J) M]
    (d : Derivation A B M) (hd : ∀ x ∈ J, d x = 0) (x : B) :
    quotientDerivation A B M J d hd (Ideal.Quotient.mk J x) = d x := rfl

/-- Differential generators also determine maps after extending scalars. -/
theorem tensor_differential_ext (A : Type u) (B : Type v) (T : Type w) (M : Type z)
    [CommRing A] [CommRing B] [CommRing T] [Algebra A B] [Algebra B T]
    [AddCommGroup M] [Module T M]
    (f g : T ⊗[B] KaehlerDifferential A B →ₗ[T] M)
    (h : ∀ b, f (1 ⊗ₜ[B] KaehlerDifferential.D A B b) =
      g (1 ⊗ₜ[B] KaehlerDifferential.D A B b)) : f = g := by
  have h' : ∀ x : KaehlerDifferential A B, ∀ t : T,
      f (t ⊗ₜ[B] x) = g (t ⊗ₜ[B] x) := by
    intro x
    have hx : x ∈ Submodule.span B (Set.range (KaehlerDifferential.D A B)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      intro t
      simpa only [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
        congrArg (fun y => t • y) (h b)
    | zero => intro t; simp
    | add x y _ _ hx hy =>
      intro t
      simpa only [tmul_add, map_add] using congrArg₂ (· + ·) (hx t) (hy t)
    | smul r x _ hx =>
      intro t
      simpa only [TensorProduct.smul_tmul] using hx (r • t)
  apply LinearMap.ext
  intro x
  induction x with
  | tmul t x => exact h' x t
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

@[simp] theorem restrictionMap_differential (A : Type u) (B : Type v) (C : Type w)
    (T : Type z) [CommRing A] [CommRing B] [CommRing C] [CommRing T]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [Algebra B T] [Algebra C T] [IsScalarTower B C T] (t : T) (b : B) :
    restrictionMap A B C T (t ⊗ₜ[B] KaehlerDifferential.D A B b) =
      t ⊗ₜ[C] KaehlerDifferential.D A C (algebraMap B C b) := by
  simp [restrictionMap, LinearMap.liftBaseChange_tmul,
    KaehlerDifferential.map_D, TensorProduct.smul_tmul', smul_eq_mul]

/-- The universal derivation with coefficients reduced modulo I^n descends
through B/I^(n+1). -/
def thickerDerivation (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B) (n : ℕ) :
    letI := powerQuotientAlgebra B I n
    Derivation A (B ⧸ I ^ (n + 1))
      ((B ⧸ I ^ n) ⊗[B] KaehlerDifferential A B) := by
  letI := powerQuotientAlgebra B I n
  let T := B ⧸ I ^ n
  let M := T ⊗[B] KaehlerDifferential A B
  let d : Derivation A B M :=
    (TensorProduct.mk B T (KaehlerDifferential A B) 1).compDer
      (KaehlerDifferential.D A B)
  apply quotientDerivation A B M (I ^ (n + 1)) d
  intro x hx
  have hd := derivation_ideal_power A B M d I n hx
  refine Submodule.smul_induction_on (p := fun m : M => m = 0) hd ?_ ?_
  · intro r hr m _
    have hz : algebraMap B T r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
    rw [← IsScalarTower.algebraMap_smul T r m, hz, zero_smul]
  · intro x y hx hy
    rw [hx, hy, add_zero]

@[simp] theorem thickerDerivation_mk (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B) (n : ℕ) (b : B) :
    letI := powerQuotientAlgebra B I n
    thickerDerivation A B I n (Ideal.Quotient.mk (I ^ (n + 1)) b) =
      1 ⊗ₜ[B] KaehlerDifferential.D A B b := rfl

/-- The canonical thicker-quotient map is invertible. -/
theorem thicker_quotient : Specs.AdvCommAlg.Differentials.thickerQuotient.{u,v} := by
  intro A B _ _ _ I n _hn
  letI := powerQuotientAlgebra B I n
  let C := B ⧸ I ^ (n + 1)
  let T := B ⧸ I ^ n
  let f := restrictionMap A B C T
  let g := (thickerDerivation A B I n).liftKaehlerDifferential.liftBaseChange T
  have hgf : g.comp f = LinearMap.id := by
    apply tensor_differential_ext A B T
    intro b
    simp [g, f, LinearMap.liftBaseChange_tmul, C, T]
  have hfg : f.comp g = LinearMap.id := by
    apply tensor_differential_ext A C T
    intro c
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    simp [g, f, LinearMap.liftBaseChange_tmul, C, T]
  exact ⟨{ f with
    invFun := g
    left_inv := fun x => LinearMap.congr_fun hgf x
    right_inv := fun x => LinearMap.congr_fun hfg x }, rfl⟩

/-- The example in KD-15, with its actual quotient rings and generators. -/
theorem thicker_polynomial_example :
    Specs.AdvCommAlg.Differentials.thickerPolynomialExample.{u} := by
  intro k _
  let P := Polynomial k
  let I : Ideal P := Ideal.span {Polynomial.X}
  let T := P ⧸ I ^ 1
  let C := P ⧸ I ^ (1 + 1)
  letI := powerQuotientAlgebra P I 1
  let q : T ≃ₐ[k] k :=
    (Ideal.quotientEquivAlgOfEq k
      (by simp [I] : I ^ 1 = Ideal.span ({Polynomial.X - Polynomial.C (0 : k)} : Set P))).trans
      (Polynomial.quotientSpanXSubCAlgEquiv 0)
  let e : T ⊗[P] KaehlerDifferential k P ≃ₗ[T] T :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl T T)
      (KaehlerDifferential.polynomialEquiv k)).trans
      (TensorProduct.AlgebraTensorModule.rid P T T)
  let e₁ := (e.restrictScalars k).trans q.toLinearEquiv
  obtain ⟨r, hr⟩ := thicker_quotient k P I 1 (by rfl)
  let e₂ := (r.symm.restrictScalars k).trans e₁
  have hgen : e₁ (1 ⊗ₜ[P] KaehlerDifferential.D k P Polynomial.X) = 1 := by
    simp [e₁, e, q, P, T]
  have hcomp : ∀ x, e₂ (restrictionMap k P C T x) = e₁ x := by
    intro x
    change e₁ (r.symm (restrictionMap k P C T x)) = e₁ x
    rw [← hr]
    simp
  refine ⟨e₁, e₂, hgen, ?_, hcomp, ?_⟩
  · rw [← restrictionMap_differential k P C T 1 Polynomial.X, hcomp]
    exact hgen
  · apply subsingleton_of_surjective k T
    intro t
    refine ⟨q t, ?_⟩
    apply q.injective
    simp

end
end AdvCommAlg.Differentials
