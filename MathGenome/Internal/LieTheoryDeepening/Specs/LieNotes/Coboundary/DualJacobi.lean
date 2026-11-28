import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Coboundary.Basic
import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel

/-! The exterior and tensor forms of the co-Jacobi identity. -/

open scoped TensorProduct

namespace Specs.LieNotes.Coboundary

universe u v
variable {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M]

/-- Exterior multiplication of a bivector by a vector on the right. -/
noncomputable def wedgeWithVectorValue :
    ⋀[k]^2 M →ₗ[k] M →ₗ[k] ⋀[k]^3 M :=
  (exteriorPower.wedge k M 2 1).compl₂ (exteriorPower.oneEquiv k M).symm.toLinearMap

/-- The degree-two part of the degree-one exterior derivation induced by `δ`.
Moving a vector past a bivector has sign `(-1)^(1*2) = 1`. -/
noncomputable def cobracketDifferentialValue (δ : M →ₗ[k] ⋀[k]^2 M) :
    ⋀[k]^2 M →ₗ[k] ⋀[k]^3 M :=
  let f : M →ₗ[k] M →ₗ[k] ⋀[k]^3 M := (wedgeWithVectorValue (k := k) (M := M)).comp δ
  exteriorPower.alternatingMapLinearEquiv
    { toMultilinearMap := by
        let toMulti (g : M →ₗ[k] M →ₗ[k] ⋀[k]^3 M) :
            MultilinearMap k (fun _ : Fin 2 => M) (⋀[k]^3 M) :=
          ((MultilinearMap.ofSubsingletonₗ k k M (⋀[k]^3 M) (0 : Fin 1)).toLinearMap.comp
            g).uncurryLeft
        exact toMulti f - toMulti f.flip
      map_eq_zero_of_eq' := by
        intro v i j h hij
        have hv : v 0 = v 1 := by
          fin_cases i <;> fin_cases j
          · exact (hij rfl).elim
          · exact h
          · exact h.symm
          · exact (hij rfl).elim
        change f (v 0) (v 1) - f (v 1) (v 0) = 0
        rw [hv, sub_self] }

/-- Rotate a left-associated triple tensor by `(a,b,c) ↦ (b,c,a)`. -/
def tensorCycleValue : M ⊗[k] M ⊗[k] M ≃ₗ[k] M ⊗[k] M ⊗[k] M :=
  (TensorProduct.assoc k M M M).trans (TensorProduct.comm k M (M ⊗[k] M))

private theorem finThree_cases (j : Fin 3) : j = 0 ∨ j = 1 ∨ j = 2 := by
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

private theorem finThree_ne01 : (0 : Fin 3) ≠ 1 := by decide
private theorem finThree_ne02 : (0 : Fin 3) ≠ 2 := by decide
private theorem finThree_ne12 : (1 : Fin 3) ≠ 2 := by decide

private def tensorTripleMultilinear :
    MultilinearMap k (fun _ : Fin 3 => M) (M ⊗[k] M ⊗[k] M) where
  toFun v := (v 0 ⊗ₜ[k] v 1) ⊗ₜ[k] v 2
  map_update_add' v i a b := by
    rcases finThree_cases i with rfl | rfl | rfl <;>
      simp only [Function.update_self, Function.update_of_ne finThree_ne01,
        Function.update_of_ne finThree_ne02, Function.update_of_ne finThree_ne12,
        Function.update_of_ne finThree_ne01.symm, Function.update_of_ne finThree_ne02.symm,
        Function.update_of_ne finThree_ne12.symm, TensorProduct.add_tmul, TensorProduct.tmul_add]
  map_update_smul' v i c a := by
    rcases finThree_cases i with rfl | rfl | rfl <;>
      simp only [Function.update_self, Function.update_of_ne finThree_ne01,
        Function.update_of_ne finThree_ne02, Function.update_of_ne finThree_ne12,
        Function.update_of_ne finThree_ne01.symm, Function.update_of_ne finThree_ne02.symm,
        Function.update_of_ne finThree_ne12.symm, TensorProduct.smul_tmul', TensorProduct.tmul_smul]

private def alternatingTripleMultilinear :
    MultilinearMap k (fun _ : Fin 3 => M) (M ⊗[k] M ⊗[k] M) :=
  let f := tensorTripleMultilinear (k := k) (M := M)
  let C := tensorCycleValue (k := k) (M := M)
  (LinearMap.id + C.toLinearMap + (C.trans C).toLinearMap).compMultilinearMap
    (f - f.domDomCongr (Equiv.swap 0 1))

private theorem alternatingTripleMultilinear_apply (v : Fin 3 → M) :
    alternatingTripleMultilinear (k := k) v =
      (v 0 ⊗ₜ[k] v 1 ⊗ₜ[k] v 2 - v 1 ⊗ₜ[k] v 0 ⊗ₜ[k] v 2) +
      (v 1 ⊗ₜ[k] v 2 ⊗ₜ[k] v 0 - v 0 ⊗ₜ[k] v 2 ⊗ₜ[k] v 1) +
      (v 2 ⊗ₜ[k] v 0 ⊗ₜ[k] v 1 - v 2 ⊗ₜ[k] v 1 ⊗ₜ[k] v 0) := by
  simp [alternatingTripleMultilinear, tensorTripleMultilinear, tensorCycleValue,
    MultilinearMap.domDomCongr_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne]

/-- Unscaled antisymmetrization of a trivector in the ordinary tensor cube. -/
noncomputable def alternatingTensorThreeValue : ⋀[k]^3 M →ₗ[k] M ⊗[k] M ⊗[k] M :=
  exteriorPower.alternatingMapLinearEquiv
    { toMultilinearMap := alternatingTripleMultilinear
      map_eq_zero_of_eq' := by
        intro v i j h hij
        change alternatingTripleMultilinear (k := k) v = 0
        rw [alternatingTripleMultilinear_apply]
        rcases finThree_cases i with rfl | rfl | rfl <;>
          rcases finThree_cases j with rfl | rfl | rfl <;>
          first | exact (hij rfl).elim | (rw [h]; abel) }

/-- The standard quotient sending `a ⊗ b ⊗ c` to `a ∧ b ∧ c`. -/
noncomputable def exteriorQuotientThreeValue : M ⊗[k] M ⊗[k] M →ₗ[k] ⋀[k]^3 M :=
  TensorProduct.lift (wedgeWithVectorValue.comp (TensorProduct.lift wedge₂Value))

/-- The cyclic sum of the first-leg iteration of the skew tensor cobracket. -/
noncomputable def tensorCoJacobiValue (δ : M →ₗ[k] ⋀[k]^2 M) :
    M →ₗ[k] M ⊗[k] M ⊗[k] M :=
  let B := alternatingTensorValue.comp δ
  let C := tensorCycleValue (k := k) (M := M)
  (LinearMap.id + C.toLinearMap + (C.trans C).toLinearMap).comp
    ((TensorProduct.map B LinearMap.id).comp B)

-- Closed types for the independently checked declarations.
set_option linter.checkUnivs false

def WedgeWithVectorType :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    ⋀[k]^2 M →ₗ[k] M →ₗ[k] ⋀[k]^3 M

def CobracketDifferentialType :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    (M →ₗ[k] ⋀[k]^2 M) → ⋀[k]^2 M →ₗ[k] ⋀[k]^3 M

def TensorCycleType :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    M ⊗[k] M ⊗[k] M ≃ₗ[k] M ⊗[k] M ⊗[k] M

def AlternatingTensorThreeType :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    ⋀[k]^3 M →ₗ[k] M ⊗[k] M ⊗[k] M

def ExteriorQuotientThreeType :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    M ⊗[k] M ⊗[k] M →ₗ[k] ⋀[k]^3 M

def TensorCoJacobiType :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    (M →ₗ[k] ⋀[k]^2 M) → M →ₗ[k] M ⊗[k] M ⊗[k] M

def WedgeWithVectorWedgeTwoType : Prop :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    ∀ a b c : M, wedgeWithVectorValue (wedge₂Value a b) c = exteriorPower.ιMulti k 3 ![a, b, c]

def WedgeWithVectorEqVectorWedgeType : Prop :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    ∀ (p : ⋀[k]^2 M) (a : M),
      wedgeWithVectorValue p a =
        exteriorPower.wedge k M 1 2 ((exteriorPower.oneEquiv k M).symm a) p

def CobracketDifferentialWedgeTwoType : Prop :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    ∀ (δ : M →ₗ[k] ⋀[k]^2 M) (a b : M),
      cobracketDifferentialValue δ (wedge₂Value a b) =
        wedgeWithVectorValue (δ a) b - wedgeWithVectorValue (δ b) a

def TensorCycleTmulType : Prop :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    ∀ a b c : M, tensorCycleValue (a ⊗ₜ[k] b ⊗ₜ[k] c) = b ⊗ₜ[k] c ⊗ₜ[k] a

def AlternatingTensorThreeApplyType : Prop :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    ∀ v : Fin 3 → M,
      alternatingTensorThreeValue (exteriorPower.ιMulti k 3 v) =
        (v 0 ⊗ₜ[k] v 1 ⊗ₜ[k] v 2 - v 1 ⊗ₜ[k] v 0 ⊗ₜ[k] v 2) +
        (v 1 ⊗ₜ[k] v 2 ⊗ₜ[k] v 0 - v 0 ⊗ₜ[k] v 2 ⊗ₜ[k] v 1) +
        (v 2 ⊗ₜ[k] v 0 ⊗ₜ[k] v 1 - v 2 ⊗ₜ[k] v 1 ⊗ₜ[k] v 0)

def ExteriorQuotientThreeTmulType : Prop :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    ∀ a b c : M, exteriorQuotientThreeValue (a ⊗ₜ[k] b ⊗ₜ[k] c) =
      exteriorPower.ιMulti k 3 ![a, b, c]

def ExteriorQuotientThreeCompType : Prop :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    (exteriorQuotientThreeValue (k := k) (M := M)).comp alternatingTensorThreeValue =
      (6 : k) • LinearMap.id

def PairingCobracketDifferentialType : Prop :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    ∀ (δ : M →ₗ[k] ⋀[k]^2 M) (α β γ : Module.Dual k M) (p : ⋀[k]^2 M),
      exteriorPower.pairingDual k M 3 (exteriorPower.ιMulti k 3 ![α, β, γ])
        (cobracketDifferentialValue δ p) =
      exteriorPower.pairingDual k M 2 (wedge₂Value (dualBracketValue δ α β) γ) p +
        exteriorPower.pairingDual k M 2 (wedge₂Value (dualBracketValue δ β γ) α) p +
        exteriorPower.pairingDual k M 2 (wedge₂Value (dualBracketValue δ γ α) β) p

def TensorCoJacobiEqType : Prop :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    ∀ δ : M →ₗ[k] ⋀[k]^2 M,
      tensorCoJacobiValue δ =
        (alternatingTensorThreeValue.comp (cobracketDifferentialValue δ)).comp δ

def TensorCoJacobiApplyType : Prop :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    ∀ (δ : M →ₗ[k] ⋀[k]^2 M) (x : M),
      tensorCoJacobiValue δ x =
        let B := alternatingTensorValue.comp δ
        let t := TensorProduct.map B LinearMap.id (B x)
        t + tensorCycleValue t + tensorCycleValue (tensorCycleValue t)

def AlternatingTensorThreeInjectiveType : Prop :=
  ∀ {k : Type u} {M : Type v} [Field k] [AddCommGroup M] [Module k M] [CharZero k],
    Function.Injective (alternatingTensorThreeValue (k := k) (M := M))

def DualJacobiIffCobracketDifferentialType : Prop :=
  ∀ {k : Type u} {M : Type v} [Field k] [AddCommGroup M] [Module k M] [Module.Finite k M],
    ∀ δ : M →ₗ[k] ⋀[k]^2 M,
      dualJacobiValue δ ↔ (cobracketDifferentialValue δ).comp δ = 0

def TensorCoJacobiEqZeroIffType : Prop :=
  ∀ {k : Type u} {M : Type v} [Field k] [AddCommGroup M] [Module k M] [CharZero k],
    ∀ δ : M →ₗ[k] ⋀[k]^2 M,
      tensorCoJacobiValue δ = 0 ↔ (cobracketDifferentialValue δ).comp δ = 0

def DualJacobiIffTensorCoJacobiType : Prop :=
  ∀ {k : Type u} {M : Type v} [Field k] [AddCommGroup M] [Module k M]
    [CharZero k] [Module.Finite k M],
    ∀ δ : M →ₗ[k] ⋀[k]^2 M, dualJacobiValue δ ↔ tensorCoJacobiValue δ = 0

end Specs.LieNotes.Coboundary
