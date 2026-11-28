import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ChevalleyEilenbergComplex
import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Mathlib.LinearAlgebra.Multilinear.Curry

/-! The shared operations of LD04. The defining formulas make sense over a
commutative ring, in particular over the characteristic-zero fields in the source. -/

open scoped TensorProduct

namespace Specs.LieNotes.Coboundary

open _root_.AdvancedHomologicalAlgebra.CE (wedgeDeriv wedgeDeriv_wedge)

universe u v

-- The closed types of the polymorphic definitions live in a maximum of two universes.
set_option linter.checkUnivs false

section Modules

variable {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M]

def WedgeTwoType :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    M →ₗ[k] M →ₗ[k] ⋀[k]^2 M

/-- The canonical exterior product as a bilinear map. -/
def wedge₂Value : M →ₗ[k] M →ₗ[k] ⋀[k]^2 M :=
  (MultilinearMap.ofSubsingletonₗ k k M (⋀[k]^2 M) (0 : Fin 1)).symm.toLinearMap.comp
    (exteriorPower.ιMulti k 2 (M := M)).toMultilinearMap.curryLeft

def WedgeTwoApplyType : Prop :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    ∀ (a b : M), wedge₂Value (k := k) a b = exteriorPower.ιMulti k 2 ![a, b]

def WedgeTwoSelfType : Prop :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    ∀ a : M, wedge₂Value (k := k) a a = 0

def WedgeTwoSwapType : Prop :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    ∀ a b : M, wedge₂Value (k := k) b a = -wedge₂Value (k := k) a b

def AlternatingTensorType :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    ⋀[k]^2 M →ₗ[k] M ⊗[k] M

/-- The unscaled antisymmetrization into the ordinary tensor square. -/
noncomputable def alternatingTensorValue : ⋀[k]^2 M →ₗ[k] M ⊗[k] M :=
  exteriorPower.alternatingMapLinearEquiv
    { toMultilinearMap :=
        ((MultilinearMap.ofSubsingletonₗ k k M (M ⊗[k] M) (0 : Fin 1)).toLinearMap.comp
          (TensorProduct.mk k M M - (TensorProduct.mk k M M).flip)).uncurryLeft
      map_eq_zero_of_eq' := by
        intro v i j h hij
        have h₀₁ : v 0 = v 1 := by
          revert i j
          simp only [Fin.forall_fin_two]
          exact ⟨⟨fun _ hn => (hn rfl).elim, fun h _ => h⟩,
            ⟨fun h _ => h.symm, fun _ hn => (hn rfl).elim⟩⟩
        change (v 0 ⊗ₜ[k] v 1) - (v 1 ⊗ₜ[k] v 0) = 0
        rw [h₀₁, sub_self] }

def AlternatingTensorApplyType : Prop :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    ∀ (a b : M), alternatingTensorValue (k := k) (wedge₂Value a b) =
      a ⊗ₜ[k] b - b ⊗ₜ[k] a

def DualBracketType :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    (M →ₗ[k] ⋀[k]^2 M) → Module.Dual k M →ₗ[k] Module.Dual k M →ₗ[k] Module.Dual k M

/-- Pair the exterior product of two linear forms with the cobracket. -/
noncomputable def dualBracketValue (δ : M →ₗ[k] ⋀[k]^2 M) :
    Module.Dual k M →ₗ[k] Module.Dual k M →ₗ[k] Module.Dual k M :=
  (wedge₂Value (k := k) (M := Module.Dual k M)).compr₂
    (δ.dualMap.comp (exteriorPower.pairingDual k M 2))

def DualBracketApplyType : Prop :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    ∀ (δ : M →ₗ[k] ⋀[k]^2 M) (α β : Module.Dual k M) (x : M),
      dualBracketValue δ α β x =
        exteriorPower.pairingDual k M 2 (exteriorPower.ιMulti k 2 ![α, β]) (δ x)

def DualBracketSelfType : Prop :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    ∀ (δ : M →ₗ[k] ⋀[k]^2 M) (α : Module.Dual k M), dualBracketValue δ α α = 0

def DualBracketSwapType : Prop :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    ∀ (δ : M →ₗ[k] ⋀[k]^2 M) (α β : Module.Dual k M),
      dualBracketValue δ β α = -dualBracketValue δ α β

def PairingWedgeTwoType : Prop :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    ∀ (α β : Module.Dual k M) (a b : M),
      exteriorPower.pairingDual k M 2 (wedge₂Value α β) (wedge₂Value a b) =
        α a * β b - α b * β a

def DualJacobiType :=
  ∀ {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M],
    (M →ₗ[k] ⋀[k]^2 M) → Prop

/-- Jacobi in the cyclic form for the alternating dual operation. -/
noncomputable def dualJacobiValue : (M →ₗ[k] ⋀[k]^2 M) → Prop := fun δ =>
  ∀ α β γ : Module.Dual k M,
    dualBracketValue δ (dualBracketValue δ α β) γ +
      dualBracketValue δ (dualBracketValue δ β γ) α +
      dualBracketValue δ (dualBracketValue δ γ α) β = 0

end Modules

section LieAlgebra

variable {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g]

def ExteriorAdjointType :=
  ∀ {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g],
    (n : ℕ) → g →ₗ[k] Module.End k (⋀[k]^n g)

/-- Apply the adjoint operator in each exterior slot and sum. -/
noncomputable def exteriorAdjointValue : (n : ℕ) → g →ₗ[k] Module.End k (⋀[k]^n g) := fun n =>
  { toFun := fun x => wedgeDeriv n (LieAlgebra.ad k g x)
    map_add' := by
      intro x y
      apply exteriorPower.linearMap_ext
      apply AlternatingMap.ext
      intro v
      change wedgeDeriv n (LieAlgebra.ad k g (x + y)) (exteriorPower.ιMulti k n v) =
        (wedgeDeriv n (LieAlgebra.ad k g x) + wedgeDeriv n (LieAlgebra.ad k g y))
          (exteriorPower.ιMulti k n v)
      simp [wedgeDeriv_wedge, ← Finset.sum_add_distrib]
    map_smul' := by
      intro c x
      apply exteriorPower.linearMap_ext
      apply AlternatingMap.ext
      intro v
      change wedgeDeriv n (LieAlgebra.ad k g (c • x)) (exteriorPower.ιMulti k n v) =
        (c • wedgeDeriv n (LieAlgebra.ad k g x)) (exteriorPower.ιMulti k n v)
      simp [wedgeDeriv_wedge, Finset.smul_sum] }

def ExteriorAdjointApplyType : Prop :=
  ∀ {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g],
    ∀ (n : ℕ) (x : g) (v : Fin n → g),
      exteriorAdjointValue (k := k) n x (exteriorPower.ιMulti k n v) =
        ∑ i : Fin n, exteriorPower.ιMulti k n (Function.update v i ⁅x, v i⁆)

def ExteriorAdjointWedgeTwoType : Prop :=
  ∀ {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g],
    ∀ (x y z : g), exteriorAdjointValue (k := k) 2 x (wedge₂Value y z) =
      wedge₂Value ⁅x, y⁆ z + wedge₂Value y ⁅x, z⁆

def ExteriorAdjointWedgeThreeType : Prop :=
  ∀ {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g],
    ∀ (x a b c : g),
      exteriorAdjointValue (k := k) 3 x (exteriorPower.ιMulti k 3 ![a, b, c]) =
        exteriorPower.ιMulti k 3 ![⁅x, a⁆, b, c] +
        exteriorPower.ιMulti k 3 ![a, ⁅x, b⁆, c] +
        exteriorPower.ιMulti k 3 ![a, b, ⁅x, c⁆]

def CobracketPredicateType :=
  ∀ {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g],
    (g →ₗ[k] ⋀[k]^2 g) → Prop

/-- The adjoint 1-cocycle identity for a proposed cobracket. -/
noncomputable def isCobracketCocycleValue : (g →ₗ[k] ⋀[k]^2 g) → Prop := fun δ =>
  ∀ x y : g, δ ⁅x, y⁆ = exteriorAdjointValue 2 x (δ y) - exteriorAdjointValue 2 y (δ x)

/-- A Lie bialgebra cobracket is a cocycle whose determinant-dual bracket obeys Jacobi. -/
noncomputable def isLieBialgebraCobracketValue : (g →ₗ[k] ⋀[k]^2 g) → Prop :=
  fun δ => isCobracketCocycleValue δ ∧ dualJacobiValue δ

def CoboundaryType :=
  ∀ {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g],
    ⋀[k]^2 g → g →ₗ[k] ⋀[k]^2 g

/-- Evaluate the exterior-square adjoint action at the chosen bivector. -/
noncomputable def coboundaryValue : ⋀[k]^2 g → g →ₗ[k] ⋀[k]^2 g := fun r =>
  (exteriorAdjointValue (k := k) 2).flip r

def CoboundaryApplyType : Prop :=
  ∀ {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g],
    ∀ (r : ⋀[k]^2 g) (x : g), coboundaryValue r x = exteriorAdjointValue 2 x r

end LieAlgebra

def AlternatingTensorInjectiveType : Prop :=
  ∀ {k : Type u} {M : Type v} [Field k] [CharZero k] [AddCommGroup M] [Module k M],
    Function.Injective (alternatingTensorValue (k := k) (M := M))

end Specs.LieNotes.Coboundary
