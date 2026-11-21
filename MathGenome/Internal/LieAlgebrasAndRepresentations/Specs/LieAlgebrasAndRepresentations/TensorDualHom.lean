import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! LA-A06, module part, source lines 414–459, with the arbitrary-field
convention at lines 168–171. The canonical Mathlib Lie module structures
are used throughout, so the action formulas also certify which structures
are intended. Only the final isomorphism assumes finite dimension. -/

universe u v w w₁ w₂

namespace Specs.LieAlgebrasAndRepresentations.TensorDualHom
open scoped TensorProduct

section LinearMaps
variable (k : Type u) [Field k]
variable (M : Type w) [AddCommGroup M] [Module k M]
variable (N : Type w₁) [AddCommGroup N] [Module k N]
variable (P : Type w₂) [AddCommGroup P] [Module k P]

/-- Evaluation, extended linearly from f ⊗ m ↦ f(m). -/
def evaluationLinear : (M →ₗ[k] N) ⊗[k] M →ₗ[k] N :=
  TensorProduct.lift (LinearMap.id : (M →ₗ[k] N) →ₗ[k] (M →ₗ[k] N))

/-- Composition, extended linearly from g ⊗ f ↦ g ∘ f. -/
def compositionLinear : (N →ₗ[k] P) ⊗[k] (M →ₗ[k] N) →ₗ[k] (M →ₗ[k] P) :=
  TensorProduct.lift (LinearMap.llcomp k M N P)

/-- Scalar evaluation; the coefficient field has the trivial action. -/
def dualEvaluationLinear : Module.Dual k M ⊗[k] M →ₗ[k] k :=
  evaluationLinear k M k
end LinearMaps

/-- These are representations on the original tensor, dual and Hom spaces. -/
def actionsExpected : Prop := ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]
  (M : Type w) [AddCommGroup M] [Module k M] [LieRingModule g M] [LieModule k g M]
  (N : Type w₁) [AddCommGroup N] [Module k N] [LieRingModule g N] [LieModule k g N],
  (∀ (x : g) (m : M) (n : N),
    ⁅x, m ⊗ₜ[k] n⁆ = ⁅x, m⁆ ⊗ₜ[k] n + m ⊗ₜ[k] ⁅x, n⁆) ∧
  (∀ (x : g) (φ : Module.Dual k M) (m : M), ⁅x, φ⁆ m = -φ ⁅x, m⁆) ∧
  (∀ (x : g) (f : M →ₗ[k] N) (m : M), ⁅x, f⁆ m = ⁅x, f m⁆ - f ⁅x, m⁆)

def evaluationExpected : Prop := ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]
  (M : Type w) [AddCommGroup M] [Module k M] [LieRingModule g M] [LieModule k g M]
  (N : Type w₁) [AddCommGroup N] [Module k N] [LieRingModule g N] [LieModule k g N],
  ∃ E : (M →ₗ[k] N) ⊗[k] M →ₗ⁅k,g⁆ N,
    E.toLinearMap = evaluationLinear k M N

def compositionExpected : Prop := ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]
  (M : Type w) [AddCommGroup M] [Module k M] [LieRingModule g M] [LieModule k g M]
  (N : Type w₁) [AddCommGroup N] [Module k N] [LieRingModule g N] [LieModule k g N]
  (P : Type w₂) [AddCommGroup P] [Module k P] [LieRingModule g P] [LieModule k g P],
  ∃ C : (N →ₗ[k] P) ⊗[k] (M →ₗ[k] N) →ₗ⁅k,g⁆ (M →ₗ[k] P),
    C.toLinearMap = compositionLinear k M N P

/-- Invariance is equivariance of scalar evaluation with trivial target. -/
def dualEvaluationExpected : Prop := ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]
  (M : Type w) [AddCommGroup M] [Module k M] [LieRingModule g M] [LieModule k g M],
  ∀ (x : g) (t : Module.Dual k M ⊗[k] M),
    dualEvaluationLinear k M ⁅x, t⁆ = 0

/-- The canonical rank-one operator map is equivariant in every dimension. -/
def dualTensorHomExpected : Prop := ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]
  (M : Type w) [AddCommGroup M] [Module k M] [LieRingModule g M] [LieModule k g M]
  (N : Type w₁) [AddCommGroup N] [Module k N] [LieRingModule g N] [LieModule k g N],
  ∃ F : Module.Dual k M ⊗[k] N →ₗ⁅k,g⁆ (M →ₗ[k] N),
    F.toLinearMap = dualTensorHom k M N

/-- The same map is an isomorphism when M alone is finite dimensional. -/
def finiteDualTensorHomExpected : Prop := ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]
  (M : Type w) [AddCommGroup M] [Module k M] [LieRingModule g M] [LieModule k g M]
  (N : Type w₁) [AddCommGroup N] [Module k N] [LieRingModule g N] [LieModule k g N] [FiniteDimensional k M],
  ∃ e : Module.Dual k M ⊗[k] N ≃ₗ⁅k,g⁆ (M →ₗ[k] N),
    e.toLinearEquiv.toLinearMap = dualTensorHom k M N

end Specs.LieAlgebrasAndRepresentations.TensorDualHom
