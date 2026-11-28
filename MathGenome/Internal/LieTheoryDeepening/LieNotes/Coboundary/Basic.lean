import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Coboundary.Basic
import Mathlib.Tactic.FinCases

/-! Exterior operations and the Lie bialgebra cobracket of LD04. -/

open scoped TensorProduct

namespace LieNotes.Coboundary

universe u v

section Modules

variable {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M]

/-- The bilinear exterior product into the exterior square. -/
def wedge₂ : M →ₗ[k] M →ₗ[k] ⋀[k]^2 M :=
  Specs.LieNotes.Coboundary.wedge₂Value

theorem wedge₂_apply (a b : M) : wedge₂ (k := k) a b = exteriorPower.ιMulti k 2 ![a, b] := by
  change exteriorPower.ιMulti k 2 (Fin.cons a (fun _ => b)) = _
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp]
theorem wedge₂_self (a : M) : wedge₂ (k := k) a a = 0 := by
  rw [wedge₂_apply]
  exact (exteriorPower.ιMulti k 2).map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)

theorem wedge₂_swap (a b : M) : wedge₂ (k := k) b a = -wedge₂ (k := k) a b := by
  have h := (exteriorPower.ιMulti k 2).map_add_swap ![b, a] (i := 0) (j := 1) (by decide)
  have hv : (![b, a] : Fin 2 → M) ∘ Equiv.swap 0 1 = ![a, b] := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at h
  exact eq_neg_of_add_eq_zero_left (by simpa only [wedge₂_apply] using h)

/-- The map taking `a ∧ b` to the unscaled skew tensor `a ⊗ b - b ⊗ a`. -/
noncomputable def alternatingTensor : ⋀[k]^2 M →ₗ[k] M ⊗[k] M :=
  Specs.LieNotes.Coboundary.alternatingTensorValue

@[simp]
theorem alternatingTensor_wedge₂ (a b : M) :
    alternatingTensor (k := k) (wedge₂ a b) = a ⊗ₜ[k] b - b ⊗ₜ[k] a := by
  rw [wedge₂_apply]
  unfold alternatingTensor Specs.LieNotes.Coboundary.alternatingTensorValue
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- The operation dual to a proposed cobracket, bilinear in the two linear forms. -/
noncomputable def dualBracket (δ : M →ₗ[k] ⋀[k]^2 M) :
    Module.Dual k M →ₗ[k] Module.Dual k M →ₗ[k] Module.Dual k M :=
  (wedge₂ (k := k) (M := Module.Dual k M)).compr₂
    (δ.dualMap.comp (exteriorPower.pairingDual k M 2))

theorem dualBracket_apply (δ : M →ₗ[k] ⋀[k]^2 M) (α β : Module.Dual k M) (x : M) :
    dualBracket δ α β x =
      exteriorPower.pairingDual k M 2 (exteriorPower.ιMulti k 2 ![α, β]) (δ x) := by
  change exteriorPower.pairingDual k M 2 (wedge₂ α β) (δ x) = _
  rw [wedge₂_apply]

@[simp]
theorem dualBracket_self (δ : M →ₗ[k] ⋀[k]^2 M) (α : Module.Dual k M) :
    dualBracket δ α α = 0 := by
  change (δ.dualMap.comp (exteriorPower.pairingDual k M 2)) (wedge₂ α α) = 0
  rw [wedge₂_self, map_zero]

theorem dualBracket_swap (δ : M →ₗ[k] ⋀[k]^2 M) (α β : Module.Dual k M) :
    dualBracket δ β α = -dualBracket δ α β := by
  let f := δ.dualMap.comp (exteriorPower.pairingDual k M 2)
  change f (wedge₂ β α) = -f (wedge₂ α β)
  rw [wedge₂_swap, map_neg]

@[simp]
theorem pairing_wedge₂_wedge₂ (α β : Module.Dual k M) (a b : M) :
    exteriorPower.pairingDual k M 2 (wedge₂ α β) (wedge₂ a b) =
      α a * β b - α b * β a := by
  simp only [wedge₂_apply, exteriorPower.pairingDual_ιMulti_ιMulti, Matrix.det_fin_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [mul_comm (β a) (α b)]

/-- The cyclic Jacobi identity for the determinant-dual bracket. -/
noncomputable def dualJacobi (δ : M →ₗ[k] ⋀[k]^2 M) : Prop :=
  ∀ α β γ : Module.Dual k M,
    dualBracket δ (dualBracket δ α β) γ +
      dualBracket δ (dualBracket δ β γ) α +
      dualBracket δ (dualBracket δ γ α) β = 0

end Modules

section LieAlgebra

variable {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g]

/-- The adjoint action on the (n)th exterior power. -/
noncomputable def exteriorAdjoint (n : ℕ) : g →ₗ[k] Module.End k (⋀[k]^n g) :=
  Specs.LieNotes.Coboundary.exteriorAdjointValue n

theorem exteriorAdjoint_ιMulti (n : ℕ) (x : g) (v : Fin n → g) :
    exteriorAdjoint (k := k) n x (exteriorPower.ιMulti k n v) =
      ∑ i : Fin n, exteriorPower.ιMulti k n (Function.update v i ⁅x, v i⁆) := by
  change _root_.AdvancedHomologicalAlgebra.CE.wedgeDeriv n (LieAlgebra.ad k g x)
    (exteriorPower.ιMulti k n v) = _
  rw [_root_.AdvancedHomologicalAlgebra.CE.wedgeDeriv_wedge]
  simp only [LieAlgebra.ad_apply]

@[simp]
theorem exteriorAdjoint_wedge₂ (x y z : g) :
    exteriorAdjoint (k := k) 2 x (wedge₂ y z) = wedge₂ ⁅x, y⁆ z + wedge₂ y ⁅x, z⁆ := by
  simp only [wedge₂_apply, exteriorAdjoint_ιMulti, Fin.sum_univ_two]
  congr 1

@[simp]
theorem exteriorAdjoint_wedge₃ (x a b c : g) :
    exteriorAdjoint (k := k) 3 x (exteriorPower.ιMulti k 3 ![a, b, c]) =
      exteriorPower.ιMulti k 3 ![⁅x, a⁆, b, c] +
      exteriorPower.ιMulti k 3 ![a, ⁅x, b⁆, c] +
      exteriorPower.ιMulti k 3 ![a, b, ⁅x, c⁆] := by
  simp only [exteriorAdjoint_ιMulti, Fin.sum_univ_three]
  congr 2
  funext i
  fin_cases i <;> rfl

/-- The cocycle condition for the adjoint action on the exterior square. -/
noncomputable def isCobracketCocycle (δ : g →ₗ[k] ⋀[k]^2 g) : Prop :=
  ∀ x y : g, δ ⁅x, y⁆ = exteriorAdjoint 2 x (δ y) - exteriorAdjoint 2 y (δ x)

/-- A linear cobracket is a Lie bialgebra cobracket when it is a cocycle and its
dual bracket satisfies the Jacobi identity. -/
noncomputable def isLieBialgebraCobracket (δ : g →ₗ[k] ⋀[k]^2 g) : Prop :=
  isCobracketCocycle δ ∧ dualJacobi δ

/-- The coboundary associated to a bivector. -/
noncomputable def coboundary (r : ⋀[k]^2 g) : g →ₗ[k] ⋀[k]^2 g :=
  (exteriorAdjoint 2).flip r

@[simp]
theorem coboundary_apply (r : ⋀[k]^2 g) (x : g) :
    coboundary r x = exteriorAdjoint 2 x r := rfl

end LieAlgebra

section Field

variable {k : Type u} {M : Type v} [Field k] [CharZero k] [AddCommGroup M] [Module k M]

/-- The exterior square embeds in the tensor square by unscaled antisymmetrization. -/
theorem alternatingTensor_injective : Function.Injective (alternatingTensor (k := k) (M := M)) := by
  let q := TensorProduct.lift (wedge₂ (k := k) (M := M))
  have hq : q.comp alternatingTensor = (2 : k) • LinearMap.id := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change q (alternatingTensor (exteriorPower.ιMulti k 2 v)) =
      (2 : k) • exteriorPower.ιMulti k 2 v
    obtain ⟨a, b, rfl⟩ : ∃ a b : M, v = ![a, b] := by
      refine ⟨v 0, v 1, ?_⟩
      funext i
      fin_cases i <;> rfl
    rw [← wedge₂_apply, alternatingTensor_wedge₂, map_sub]
    change wedge₂ a b - wedge₂ b a = (2 : k) • wedge₂ a b
    rw [wedge₂_swap a b, sub_neg_eq_add, two_smul]
  intro x y hxy
  have h : (2 : k) • x = (2 : k) • y := by
    change ((2 : k) • LinearMap.id : Module.End k (⋀[k]^2 M)) x =
      ((2 : k) • LinearMap.id : Module.End k (⋀[k]^2 M)) y
    rw [← hq]
    exact congrArg q hxy
  exact smul_right_injective _ two_ne_zero h

end Field

end LieNotes.Coboundary
