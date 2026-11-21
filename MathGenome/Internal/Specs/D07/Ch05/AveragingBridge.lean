import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Submodule.LinearMap

/-!
Independent specification of K07.05.averaging_bridge (paper.tex:930–945).
The family of linear operators is not required to preserve the identity.
There is no dimension or nontriviality assumption on the vector space.
Only the failure example needs a nonzero vector space.
-/

namespace Specs.D07.Ch05.AveragingBridge

universe u v w

noncomputable section

/-- The scalar denoted by `m = |G| · 1_K` in the source. -/
def orderScalar (K : Type u) [Field K] (G : Type w) [Fintype G] : K :=
  (Fintype.card G : K)

/-- The explicit zero branch is part of the source's convention. -/
def averagingScalar (K : Type u) [Field K] (G : Type w) [Fintype G] : K := by
  classical
  exact if orderScalar K G ≠ 0 then (orderScalar K G)⁻¹ else 0

variable {K : Type u} {E : Type v} {G : Type w}
  [Field K] [AddCommGroup E] [Module K E]

/-- The actual finite average, defined even when its order scalar vanishes. -/
def average [Fintype G] (ρ : G → E →ₗ[K] E) : E →ₗ[K] E :=
  averagingScalar K G • ∑ g : G, ρ g

/-- Vectors fixed by all members of the given family, as a linear subspace. -/
def fixedSubspace (ρ : G → E →ₗ[K] E) : Submodule K E where
  carrier := {x | ∀ g, ρ g x = x}
  zero_mem' := fun g => (ρ g).map_zero
  add_mem' := by
    intro x y hx hy g
    rw [map_add, hx g, hy g]
  smul_mem' := by
    intro c x hx g
    rw [map_smul, hx g]

/-- The two branches of the normalizing scalar, with no implicit division by zero. -/
def NormalizationCases : Prop :=
  ∀ (K : Type u) [Field K] (G : Type w) [Fintype G],
    (orderScalar K G ≠ 0 → averagingScalar K G = (orderScalar K G)⁻¹) ∧
    (orderScalar K G = 0 → averagingScalar K G = 0)

/-- Invariance of every image vector holds in every characteristic. -/
def InvariantImage : Prop :=
  ∀ (K : Type u) (E : Type v) (G : Type w)
    [Field K] [AddCommGroup E] [Module K E] [Group G] [Fintype G]
    (ρ : G → E →ₗ[K] E),
    (∀ g h, ρ (g * h) = (ρ g).comp (ρ h)) →
    ∀ (h : G) (x : E), ρ h (average ρ x) = average ρ x

/-- When `m` is nonzero the average is the identity on all fixed vectors. -/
def FixesFixedVectors : Prop :=
  ∀ (K : Type u) (E : Type v) (G : Type w)
    [Field K] [AddCommGroup E] [Module K E] [Group G] [Fintype G]
    (ρ : G → E →ₗ[K] E),
    orderScalar K G ≠ 0 →
    ∀ (x : E), (∀ g, ρ g x = x) → average ρ x = x

/-- Equality of endomorphisms, so this is `P² = P`, not merely invariance. -/
def IdempotentAverage : Prop :=
  ∀ (K : Type u) (E : Type v) (G : Type w)
    [Field K] [AddCommGroup E] [Module K E] [Group G] [Fintype G]
    (ρ : G → E →ₗ[K] E),
    (∀ g h, ρ (g * h) = (ρ g).comp (ρ h)) →
    orderScalar K G ≠ 0 → (average ρ).comp (average ρ) = average ρ

/-- The image is exactly the fixed subspace under the nonzero-order hypothesis. -/
def RangeAverage : Prop :=
  ∀ (K : Type u) (E : Type v) (G : Type w)
    [Field K] [AddCommGroup E] [Module K E] [Group G] [Fintype G]
    (ρ : G → E →ₗ[K] E),
    (∀ g h, ρ (g * h) = (ρ g).comp (ρ h)) →
    orderScalar K G ≠ 0 → LinearMap.range (average ρ) = fixedSubspace ρ

/-- In the zero-order branch both the coefficient and the actual map vanish. -/
def ZeroOrder : Prop :=
  ∀ (K : Type u) (E : Type v) (G : Type w)
    [Field K] [AddCommGroup E] [Module K E] [Group G] [Fintype G]
    (ρ : G → E →ₗ[K] E),
    orderScalar K G = 0 → averagingScalar K G = 0 ∧ average ρ = 0

/-- On every nonzero trivial representation in zero order, the fixed space is
nonzero, a fixed vector is not fixed by the average, and image equality fails.
Multiplicativity of the exhibited family is included explicitly. -/
def TrivialRepresentationFailure : Prop :=
  ∀ (K : Type u) (E : Type v) (G : Type w)
    [Field K] [AddCommGroup E] [Module K E] [Group G] [Fintype G] [Nontrivial E],
    orderScalar K G = 0 →
    let ρ : G → E →ₗ[K] E := fun _ => LinearMap.id
    (∀ g h, ρ (g * h) = (ρ g).comp (ρ h)) ∧
    fixedSubspace ρ = ⊤ ∧ fixedSubspace ρ ≠ ⊥ ∧
    (∃ x : E, x ≠ 0 ∧ (∀ g, ρ g x = x) ∧ average ρ x ≠ x) ∧
    LinearMap.range (average ρ) ≠ fixedSubspace ρ

end

end Specs.D07.Ch05.AveragingBridge
