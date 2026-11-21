import MathGenome.Internal.Specs.D07.Ch06.PgroupDefinition
import Mathlib.Algebra.Group.Subgroup.Map

/-!
Independent statements for `K07.06.sylow_containment`, paper.tex:1024–1031.
At this point in the paper a Sylow subgroup means a subgroup of order
`p ^ a` when `|G| = p ^ a * m` and `p ∤ m`. No maximality definition
or equivalence with it is assumed. The conjugate is explicitly the image
of `Q` under `x ↦ g * x * g⁻¹`. Exponent zero is allowed throughout.
-/

namespace Specs.D07.Ch06.SylowContainment

universe u

/-- Every finite p-subgroup lies in a conjugate of any fixed Sylow subgroup. -/
def ContainedInConjugate : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p a m : ℕ),
    p.Prime → Nat.card G = p ^ a * m → ¬ p ∣ m →
    ∀ (P Q : Subgroup G),
      PgroupDefinition.finitePGroupValue p P → Nat.card Q = p ^ a →
      ∃ g : G, (P : Set G) ⊆ (fun x : G => g * x * g⁻¹) '' (Q : Set G)

/-- In particular, every p-subgroup is contained in some Sylow subgroup. -/
def ExistsSylowContaining : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p a m : ℕ),
    p.Prime → Nat.card G = p ^ a * m → ¬ p ∣ m →
    ∀ P : Subgroup G, PgroupDefinition.finitePGroupValue p P →
      ∃ S : Subgroup G, P ≤ S ∧ Nat.card S = p ^ a

end Specs.D07.Ch06.SylowContainment
