import MathGenome.Internal.Specs.D05.M03.HomDimension
import MathGenome.Internal.Specs.D05.M04.Trace
import MathGenome.Internal.Specs.D05.M15.TensorDualHom
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
Independent specifications for paper.tex:2816–2823.
All substantive trace-pairing assertions are for finite-dimensional spaces over
an arbitrary field, with no positivity, characteristic, or nonzero-dimension
assumption. Perfectness means that both maps to algebraic duals are bijective.
-/
namespace Specs.D05.M15.TensorDualHom.TracePairing

open scoped TensorProduct
open Specs.D05.M03.HomDimension (elementaryMap)

/-- The algebraic bilinear pairing, using the canonical endomorphism trace.
As with Mathlib's trace, the definition is total; perfectness is asserted only
under the finite-dimensional hypotheses below. -/
noncomputable def pairing (K V W : Type*) [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] :
    (V →ₗ[K] W) →ₗ[K] (W →ₗ[K] V) →ₗ[K] K :=
  ((LinearMap.llcomp K V W V).flip).compr₂ (LinearMap.trace K V)

def pairing_type :=
  (K V W : Type*) → [Field K] → [AddCommGroup V] → [Module K V] →
    [AddCommGroup W] → [Module K W] →
    (V →ₗ[K] W) →ₗ[K] (W →ₗ[K] V) →ₗ[K] K

noncomputable def pairing_value : pairing_type := pairing

def pairing_apply : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (S : V →ₗ[K] W) (T : W →ₗ[K] V),
    pairing K V W S T = LinearMap.trace K V (T.comp S)

/-- E_ai and F_jb pair by the two independent Kronecker deltas. -/
def matrix_unit_pairing : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {n m : ℕ}
    (e : Module.Basis (Fin n) K V) (f : Module.Basis (Fin m) K W)
    (a b : Fin m) (i j : Fin n),
    pairing K V W (elementaryMap e f a i) (elementaryMap f e j b) =
      (if i = j then (1 : K) else 0) * (if a = b then (1 : K) else 0)

/-- Actual bases, with reversed map indices so that their common product index
makes them dual. This includes empty product index types. -/
def dual_bases : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {n m : ℕ}
    (e : Module.Basis (Fin n) K V) (f : Module.Basis (Fin m) K W),
    ∃ E : Module.Basis (Fin m × Fin n) K (V →ₗ[K] W),
    ∃ F : Module.Basis (Fin m × Fin n) K (W →ₗ[K] V),
      (∀ p, E p = elementaryMap e f p.1 p.2) ∧
      (∀ p, F p = elementaryMap f e p.2 p.1) ∧
      ∀ p q, pairing K V W (E p) (F q) = if p = q then 1 else 0

def nondegenerate : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W],
    (∀ S : V →ₗ[K] W, (∀ T : W →ₗ[K] V, pairing K V W S T = 0) → S = 0) ∧
    (∀ T : W →ₗ[K] V, (∀ S : V →ₗ[K] W, pairing K V W S T = 0) → T = 0)

def perfect : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W],
    (pairing K V W).IsPerfPair

/-- Under the accepted tensor–Hom map, the trace pairing is precisely tensor
evaluation on elementary tensors. The duals are algebraic and no conjugation
is used, including over the complex field. Spanning determines the full pairing. -/
def rank_one_pairing : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (φ : Module.Dual K V) (ψ : Module.Dual K W) (v : V) (w : W),
    pairing K V W (TensorDualHom.phi K V W (φ ⊗ₜ[K] w))
      (TensorDualHom.phi K W V (ψ ⊗ₜ[K] v)) = ψ w * φ v

end Specs.D05.M15.TensorDualHom.TracePairing
