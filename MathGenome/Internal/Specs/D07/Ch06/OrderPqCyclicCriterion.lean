import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
Independent statements for K07.06.order_pq_cyclic_criterion
(paper.tex:1068–1080). The model C_n is the additive residue group
`ZMod n`, written multiplicatively. The ambient group is finite, and
both primes and their strict inequality are explicit. The last case
asserts existence, without a uniqueness/classification claim.
-/
namespace Specs.D07.Ch06.OrderPqCyclicCriterion

universe u

/-- Every Sylow subgroup for the larger prime is normal. -/
def LargePrimeSylowNormal : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p q : ℕ),
    p.Prime → q.Prime → p < q → Nat.card G = p * q →
      ∀ Q : Sylow q G, Q.toSubgroup.Normal

/-- Without the divisibility, every group of this order is the cyclic model. -/
def CyclicOfNotDvd : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p q : ℕ),
    p.Prime → q.Prime → p < q → Nat.card G = p * q →
      ¬ p ∣ q - 1 → Nonempty (G ≃* Multiplicative (ZMod (p * q)))

/-- With the divisibility there is a nonabelian semidirect product of the
specified cyclic factors, with the required order. Nonabelianity is
expressed by an actual pair of elements that fail to commute. -/
def NonabelianSemidirectExists : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → p < q → p ∣ q - 1 →
    ∃ φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q)),
      Nat.card (SemidirectProduct (Multiplicative (ZMod q))
        (Multiplicative (ZMod p)) φ) = p * q ∧
      ∃ x y : SemidirectProduct (Multiplicative (ZMod q))
        (Multiplicative (ZMod p)) φ, x * y ≠ y * x

/-- The cyclic group exists in particular when the divisibility holds,
and indeed for every pair of primes in the statement. -/
def CyclicModelExists : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → p < q →
    Finite (Multiplicative (ZMod (p * q))) ∧
    Nat.card (Multiplicative (ZMod (p * q))) = p * q ∧
    IsCyclic (Multiplicative (ZMod (p * q)))

end Specs.D07.Ch06.OrderPqCyclicCriterion
