import MathGenome.Internal.Specs.D07.Ch17.KernelsImages
import Mathlib.LinearAlgebra.Projection
import Mathlib.Algebra.CharP.Defs

/-!
Independent specification of K07.17.maschke_projection, paper.tex:4821–4853.
The spaces have arbitrary dimension, and may be zero. Finiteness is imposed
only on the group. Invariance uses the shared pointwise predicate.
-/
namespace Specs.D07.Ch17.MaschkeProjection

universe u v w

/-- Every invariant subspace has an invariant linear complement under the
exact nonzero-cardinality hypothesis of Maschke's theorem. -/
def InvariantComplement : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [Finite G] [AddCommGroup V] [Module K V],
    (Nat.card G : K) ≠ 0 → ∀ (ρ : Representation K G V) (U : Submodule K V),
      SubrepresentationsQuotients.invariantValue K G V ρ U →
        ∃ W : Submodule K V,
          SubrepresentationsQuotients.invariantValue K G V ρ W ∧ IsCompl U W

/-- The actual average in the paper, starting from any linear projection onto
U, is an equivariant idempotent projection, and its kernel is a complement.
Fintype supplies the finite sum; there is no basis or dimension assumption. -/
def AveragedProjection : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [Fintype G] [AddCommGroup V] [Module K V],
    (Fintype.card G : K) ≠ 0 → ∀ (ρ : Representation K G V) (U : Submodule K V),
      SubrepresentationsQuotients.invariantValue K G V ρ U →
      ∀ E : Module.End K V, (∀ x, E x ∈ U) → (∀ x ∈ U, E x = x) →
        let P : Module.End K V := (Fintype.card G : K)⁻¹ •
          ∑ g : G, (ρ g).comp (E.comp (ρ g⁻¹))
        (∀ x, P x ∈ U) ∧ (∀ x ∈ U, P x = x) ∧ P.comp P = P ∧
          ρ.IsIntertwiningMap ρ P ∧
          SubrepresentationsQuotients.invariantValue K G V ρ (LinearMap.ker P) ∧
          IsCompl U (LinearMap.ker P)

/-- Characteristic zero always satisfies the scalar hypothesis for a finite
group, including the trivial group. -/
def CharZeroCondition : Prop :=
  ∀ (K : Type u) (G : Type v) [Field K] [CharZero K] [Group G] [Finite G],
    (Nat.card G : K) ≠ 0

/-- In positive characteristic p the scalar hypothesis is precisely p ∤ |G|. -/
def PositiveCharCondition : Prop :=
  ∀ (K : Type u) (G : Type v) [Field K] [Group G] [Finite G]
    (p : ℕ) [CharP K p], 0 < p →
      ((Nat.card G : K) ≠ 0 ↔ ¬ p ∣ Nat.card G)

/-- When p divides |G| no scalar can normalize the average: |G| is zero
in K and has no multiplicative inverse. This makes no assertion about a
particular invariant subspace lacking a complement. -/
def NoNormalizationOfDvd : Prop :=
  ∀ (K : Type u) (G : Type v) [Field K] [Group G] [Finite G]
    (p : ℕ) [CharP K p], 0 < p → p ∣ Nat.card G →
      ¬ ∃ a : K, a * (Nat.card G : K) = 1

end Specs.D07.Ch17.MaschkeProjection
