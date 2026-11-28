import MathGenome.Internal.LieTheoryDeepening.LieNotes.Coboundary.Basic
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Coboundary.DualJacobi
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! The Jacobi identity of the dual bracket in exterior and tensor form. -/

open scoped TensorProduct

namespace LieNotes.Coboundary

universe u v w

section Modules

variable {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M]

/-- Exterior multiplication of a bivector by a vector on the right. -/
noncomputable def wedgeWithVector : ⋀[k]^2 M →ₗ[k] M →ₗ[k] ⋀[k]^3 M :=
  Specs.LieNotes.Coboundary.wedgeWithVectorValue

/-- The induced degree-one exterior derivation on bivectors. -/
noncomputable def cobracketDifferential (δ : M →ₗ[k] ⋀[k]^2 M) :
    ⋀[k]^2 M →ₗ[k] ⋀[k]^3 M :=
  Specs.LieNotes.Coboundary.cobracketDifferentialValue δ

/-- The cyclic permutation `a ⊗ b ⊗ c ↦ b ⊗ c ⊗ a`. -/
def tensorCycle : M ⊗[k] M ⊗[k] M ≃ₗ[k] M ⊗[k] M ⊗[k] M :=
  Specs.LieNotes.Coboundary.tensorCycleValue

/-- Unscaled antisymmetrization of the exterior cube. -/
noncomputable def alternatingTensorThree : ⋀[k]^3 M →ₗ[k] M ⊗[k] M ⊗[k] M :=
  Specs.LieNotes.Coboundary.alternatingTensorThreeValue

/-- The canonical quotient from the ordinary tensor cube to the exterior cube. -/
noncomputable def exteriorQuotientThree : M ⊗[k] M ⊗[k] M →ₗ[k] ⋀[k]^3 M :=
  Specs.LieNotes.Coboundary.exteriorQuotientThreeValue

/-- The cyclic sum of the first-leg iteration of the skew tensor cobracket. -/
noncomputable def tensorCoJacobi (δ : M →ₗ[k] ⋀[k]^2 M) : M →ₗ[k] M ⊗[k] M ⊗[k] M :=
  Specs.LieNotes.Coboundary.tensorCoJacobiValue δ

private theorem wedge₂_linearMap_ext {N : Type w} [AddCommGroup N] [Module k N]
    {F G : ⋀[k]^2 M →ₗ[k] N} (h : ∀ a b : M, F (wedge₂ a b) = G (wedge₂ a b)) :
    F = G := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  have hv : (![v 0, v 1] : Fin 2 → M) = v := by
    funext i
    fin_cases i <;> rfl
  simpa only [LinearMap.compAlternatingMap_apply, wedge₂_apply, hv] using h (v 0) (v 1)

private theorem wedge₃_linearMap_ext {N : Type w} [AddCommGroup N] [Module k N]
    {F G : ⋀[k]^3 M →ₗ[k] N}
    (h : ∀ a b c : M,
      F (exteriorPower.ιMulti k 3 ![a, b, c]) = G (exteriorPower.ιMulti k 3 ![a, b, c])) :
    F = G := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  have hv : (![v 0, v 1, v 2] : Fin 3 → M) = v := by
    funext i
    fin_cases i <;> rfl
  simpa only [LinearMap.compAlternatingMap_apply, hv] using h (v 0) (v 1) (v 2)

@[simp]
theorem wedgeWithVector_wedge₂ (a b c : M) :
    wedgeWithVector (k := k) (wedge₂ a b) c = exteriorPower.ιMulti k 3 ![a, b, c] := by
  apply Subtype.ext
  change ((wedge₂ a b : ⋀[k]^2 M) : ExteriorAlgebra k M) *
    (((exteriorPower.oneEquiv k M).symm c : ⋀[k]^1 M) : ExteriorAlgebra k M) = _
  simp only [wedge₂_apply, exteriorPower.oneEquiv_symm_apply,
    exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_mul_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem wedgeThree_swap_first (a b c : M) :
    exteriorPower.ιMulti k 3 ![b, a, c] = -exteriorPower.ιMulti k 3 ![a, b, c] := by
  rw [← wedgeWithVector_wedge₂, ← wedgeWithVector_wedge₂, wedge₂_swap]
  exact LinearMap.congr_fun (map_neg wedgeWithVector (wedge₂ a b)) c

private theorem wedgeThree_swap_last (a b c : M) :
    exteriorPower.ιMulti k 3 ![a, c, b] = -exteriorPower.ιMulti k 3 ![a, b, c] := by
  have h := (exteriorPower.ιMulti k 3).map_add_swap
    ![a, c, b] (i := 1) (j := 2) (by decide)
  have hv : (![a, c, b] : Fin 3 → M) ∘ Equiv.swap 1 2 = ![a, b, c] := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at h
  exact eq_neg_of_add_eq_zero_left h

private theorem wedgeThree_cycle (a b c : M) :
    exteriorPower.ιMulti k 3 ![b, c, a] = exteriorPower.ιMulti k 3 ![a, b, c] := by
  rw [wedgeThree_swap_last b a c, wedgeThree_swap_first a b c, neg_neg]

/-- In degrees one and two, the two orders of exterior multiplication agree. -/
theorem wedgeWithVector_eq_vectorWedge (p : ⋀[k]^2 M) (a : M) :
    wedgeWithVector p a = exteriorPower.wedge k M 1 2 ((exteriorPower.oneEquiv k M).symm a) p := by
  have h : wedgeWithVector.flip a =
      exteriorPower.wedge k M 1 2 ((exteriorPower.oneEquiv k M).symm a) := by
    apply wedge₂_linearMap_ext
    intro b c
    change wedgeWithVector (wedge₂ b c) a = _
    rw [wedgeWithVector_wedge₂, wedgeThree_cycle a b c]
    apply Subtype.ext
    change _ = (((exteriorPower.oneEquiv k M).symm a : ⋀[k]^1 M) : ExteriorAlgebra k M) *
      ((wedge₂ b c : ⋀[k]^2 M) : ExteriorAlgebra k M)
    simp only [wedge₂_apply, exteriorPower.oneEquiv_symm_apply,
      exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_mul_ιMulti]
    congr 1
    funext i
    fin_cases i <;> rfl
  exact LinearMap.congr_fun h p

@[simp]
theorem cobracketDifferential_wedge₂ (δ : M →ₗ[k] ⋀[k]^2 M) (a b : M) :
    cobracketDifferential δ (wedge₂ a b) =
      wedgeWithVector (δ a) b - wedgeWithVector (δ b) a := by
  rw [wedge₂_apply]
  unfold cobracketDifferential Specs.LieNotes.Coboundary.cobracketDifferentialValue
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

@[simp]
theorem tensorCycle_tmul (a b c : M) :
    tensorCycle (k := k) (a ⊗ₜ[k] b ⊗ₜ[k] c) = b ⊗ₜ[k] c ⊗ₜ[k] a := by
  simp [tensorCycle, Specs.LieNotes.Coboundary.tensorCycleValue]

open private alternatingTripleMultilinear_apply
  from MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Coboundary.DualJacobi

theorem alternatingTensorThree_ιMulti (v : Fin 3 → M) :
    alternatingTensorThree (exteriorPower.ιMulti k 3 v) =
      (v 0 ⊗ₜ[k] v 1 ⊗ₜ[k] v 2 - v 1 ⊗ₜ[k] v 0 ⊗ₜ[k] v 2) +
      (v 1 ⊗ₜ[k] v 2 ⊗ₜ[k] v 0 - v 0 ⊗ₜ[k] v 2 ⊗ₜ[k] v 1) +
      (v 2 ⊗ₜ[k] v 0 ⊗ₜ[k] v 1 - v 2 ⊗ₜ[k] v 1 ⊗ₜ[k] v 0) := by
  unfold alternatingTensorThree Specs.LieNotes.Coboundary.alternatingTensorThreeValue
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact alternatingTripleMultilinear_apply v

@[simp]
theorem exteriorQuotientThree_tmul (a b c : M) :
    exteriorQuotientThree (a ⊗ₜ[k] b ⊗ₜ[k] c) = exteriorPower.ιMulti k 3 ![a, b, c] := by
  exact wedgeWithVector_wedge₂ a b c

theorem exteriorQuotientThree_comp_alternatingTensorThree :
    (exteriorQuotientThree (k := k) (M := M)).comp alternatingTensorThree =
      (6 : k) • LinearMap.id := by
  apply wedge₃_linearMap_ext
  intro a b c
  simp only [LinearMap.comp_apply, alternatingTensorThree_ιMulti, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_add, map_sub, exteriorQuotientThree_tmul,
    LinearMap.smul_apply, LinearMap.id_apply]
  rw [wedgeThree_cycle a b c, ← wedgeThree_cycle c a b,
    wedgeThree_cycle b a c, ← wedgeThree_cycle c b a, wedgeThree_swap_first a b c]
  rw [ofNat_smul_eq_nsmul]
  abel

/-- The three-form pairing on a bivector wedged with a vector is a cyclic sum. -/
private theorem pairing_wedgeWithVector (α β γ : Module.Dual k M) (p : ⋀[k]^2 M) (z : M) :
    exteriorPower.pairingDual k M 3 (exteriorPower.ιMulti k 3 ![α, β, γ])
      (wedgeWithVector p z) =
    γ z * exteriorPower.pairingDual k M 2 (wedge₂ α β) p +
      α z * exteriorPower.pairingDual k M 2 (wedge₂ β γ) p +
      β z * exteriorPower.pairingDual k M 2 (wedge₂ γ α) p := by
  let F := (exteriorPower.pairingDual k M 3
    (exteriorPower.ιMulti k 3 ![α, β, γ])).comp (wedgeWithVector.flip z)
  let G := γ z • exteriorPower.pairingDual k M 2 (wedge₂ α β) +
    α z • exteriorPower.pairingDual k M 2 (wedge₂ β γ) +
    β z • exteriorPower.pairingDual k M 2 (wedge₂ γ α)
  have h : F = G := by
    apply wedge₂_linearMap_ext
    intro a b
    dsimp only [F, G, LinearMap.comp_apply, LinearMap.flip_apply,
      LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    simp only [wedgeWithVector_wedge₂, exteriorPower.pairingDual_ιMulti_ιMulti,
      pairing_wedge₂_wedge₂, Matrix.det_fin_three, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  exact LinearMap.congr_fun h p

theorem pairing_cobracketDifferential (δ : M →ₗ[k] ⋀[k]^2 M)
    (α β γ : Module.Dual k M) (p : ⋀[k]^2 M) :
    exteriorPower.pairingDual k M 3 (exteriorPower.ιMulti k 3 ![α, β, γ])
      (cobracketDifferential δ p) =
    exteriorPower.pairingDual k M 2 (wedge₂ (dualBracket δ α β) γ) p +
      exteriorPower.pairingDual k M 2 (wedge₂ (dualBracket δ β γ) α) p +
      exteriorPower.pairingDual k M 2 (wedge₂ (dualBracket δ γ α) β) p := by
  let F := (exteriorPower.pairingDual k M 3
    (exteriorPower.ιMulti k 3 ![α, β, γ])).comp (cobracketDifferential δ)
  let G := exteriorPower.pairingDual k M 2 (wedge₂ (dualBracket δ α β) γ) +
    exteriorPower.pairingDual k M 2 (wedge₂ (dualBracket δ β γ) α) +
    exteriorPower.pairingDual k M 2 (wedge₂ (dualBracket δ γ α) β)
  have h : F = G := by
    apply wedge₂_linearMap_ext
    intro a b
    dsimp only [F, G, LinearMap.comp_apply, LinearMap.add_apply]
    simp only [cobracketDifferential_wedge₂, map_sub, pairing_wedgeWithVector,
      pairing_wedge₂_wedge₂, dualBracket_apply, ← wedge₂_apply]
    ring
  exact LinearMap.congr_fun h p

private theorem alternatingTensorThree_wedgeWithVector (p : ⋀[k]^2 M) (c : M) :
    alternatingTensorThree (wedgeWithVector p c) =
      (alternatingTensor p ⊗ₜ[k] c) +
        tensorCycle (alternatingTensor p ⊗ₜ[k] c) +
        tensorCycle (tensorCycle (alternatingTensor p ⊗ₜ[k] c)) := by
  let F := (alternatingTensorThree (k := k)).comp (wedgeWithVector.flip c)
  let C := tensorCycle (k := k) (M := M)
  let G := (LinearMap.id + C.toLinearMap + (C.trans C).toLinearMap).comp
      (((TensorProduct.mk k (M ⊗[k] M) M).flip c).comp alternatingTensor)
  have h : F = G := by
    apply wedge₂_linearMap_ext
    intro a b
    simp only [F, G, C, LinearMap.comp_apply, LinearMap.flip_apply, LinearMap.add_apply,
      LinearMap.id_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      TensorProduct.mk_apply, wedgeWithVector_wedge₂, alternatingTensorThree_ιMulti,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, alternatingTensor_wedge₂,
      map_sub, tensorCycle_tmul]
    abel
  exact LinearMap.congr_fun h p

/-- The cyclic sum in the tensor cube is exactly the antisymmetrized exterior differential. -/
theorem tensorCoJacobi_eq (δ : M →ₗ[k] ⋀[k]^2 M) :
    tensorCoJacobi δ = (alternatingTensorThree.comp (cobracketDifferential δ)).comp δ := by
  let B := alternatingTensor.comp δ
  let C := tensorCycle (k := k) (M := M)
  let F := (LinearMap.id + C.toLinearMap + (C.trans C).toLinearMap).comp
    ((TensorProduct.map B LinearMap.id).comp alternatingTensor)
  have h : F = alternatingTensorThree.comp (cobracketDifferential δ) := by
    apply wedge₂_linearMap_ext
    intro a b
    simp only [F, B, C, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply,
      LinearEquiv.coe_coe, LinearEquiv.trans_apply, alternatingTensor_wedge₂, map_sub,
      TensorProduct.map_tmul, cobracketDifferential_wedge₂,
      alternatingTensorThree_wedgeWithVector]
  exact congrArg (fun L : ⋀[k]^2 M →ₗ[k] M ⊗[k] M ⊗[k] M => L.comp δ) h

/-- Pointwise form used when cyclic co-Jacobi is computed in the tensor cube. -/
theorem tensorCoJacobi_apply (δ : M →ₗ[k] ⋀[k]^2 M) (x : M) :
    tensorCoJacobi δ x =
      let B := alternatingTensor.comp δ
      let t := TensorProduct.map B LinearMap.id (B x)
      t + tensorCycle t + tensorCycle (tensorCycle t) := rfl

end Modules

section Field

variable {K : Type u} {M : Type v} [Field K] [AddCommGroup M] [Module K M]

theorem alternatingTensorThree_injective [CharZero K] :
    Function.Injective (alternatingTensorThree (k := K) (M := M)) := by
  intro p q hpq
  have h := congrArg (exteriorQuotientThree (k := K) (M := M)) hpq
  change (exteriorQuotientThree.comp alternatingTensorThree) p =
    (exteriorQuotientThree.comp alternatingTensorThree) q at h
  rw [exteriorQuotientThree_comp_alternatingTensorThree] at h
  exact smul_right_injective _ (show (6 : K) ≠ 0 by norm_num) h

private theorem wedgeThree_eq_zero_of_pairing [Module.Finite K M] (p : ⋀[K]^3 M)
    (h : ∀ α β γ : Module.Dual K M,
      exteriorPower.pairingDual K M 3 (exteriorPower.ιMulti K 3 ![α, β, γ]) p = 0) :
    p = 0 := by
  let b := Module.finBasis K M
  have hf (f : Fin 3 → Module.Dual K M) :
      exteriorPower.pairingDual K M 3 (exteriorPower.ιMulti K 3 f) p = 0 := by
    have he : (![f 0, f 1, f 2] : Fin 3 → Module.Dual K M) = f := by
      funext i
      fin_cases i <;> rfl
    rw [← he]
    exact h (f 0) (f 1) (f 2)
  apply (b.exteriorPower 3).repr.injective
  ext s
  rw [exteriorPower.basis_repr_apply, map_zero, Finsupp.zero_apply]
  exact hf _

/-- The determinant-dual bracket satisfies Jacobi exactly when the exterior
differential vanishes on the image of the cobracket. -/
theorem dualJacobi_iff_cobracketDifferential [Module.Finite K M]
    (δ : M →ₗ[K] ⋀[K]^2 M) :
    dualJacobi δ ↔ (cobracketDifferential δ).comp δ = 0 := by
  have hp (α β γ : Module.Dual K M) (x : M) :
      exteriorPower.pairingDual K M 3 (exteriorPower.ιMulti K 3 ![α, β, γ])
        (cobracketDifferential δ (δ x)) =
      (dualBracket δ (dualBracket δ α β) γ +
        dualBracket δ (dualBracket δ β γ) α +
        dualBracket δ (dualBracket δ γ α) β) x := by
    rw [pairing_cobracketDifferential]
    rfl
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    change cobracketDifferential δ (δ x) = 0
    apply wedgeThree_eq_zero_of_pairing
    intro α β γ
    rw [hp, h α β γ, LinearMap.zero_apply]
  · intro h α β γ
    apply LinearMap.ext
    intro x
    rw [← hp]
    have hx : cobracketDifferential δ (δ x) = 0 := LinearMap.congr_fun h x
    rw [hx, map_zero, LinearMap.zero_apply]

/-- The cyclic tensor identity holds exactly when the exterior composite vanishes. -/
theorem tensorCoJacobi_eq_zero_iff [CharZero K] (δ : M →ₗ[K] ⋀[K]^2 M) :
    tensorCoJacobi δ = 0 ↔ (cobracketDifferential δ).comp δ = 0 := by
  rw [tensorCoJacobi_eq, LinearMap.comp_assoc]
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    apply alternatingTensorThree_injective
    rw [LinearMap.zero_apply, map_zero]
    exact LinearMap.congr_fun h x
  · intro h
    rw [h, LinearMap.comp_zero]

/-- Cyclic tensor co-Jacobi is equivalent to Jacobi for the determinant-dual bracket. -/
theorem dualJacobi_iff_tensorCoJacobi [CharZero K] [Module.Finite K M]
    (δ : M →ₗ[K] ⋀[K]^2 M) :
    dualJacobi δ ↔ tensorCoJacobi δ = 0 :=
  (dualJacobi_iff_cobracketDifferential δ).trans (tensorCoJacobi_eq_zero_iff δ).symm

end Field

end LieNotes.Coboundary
