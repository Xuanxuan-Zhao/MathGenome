import MathGenome.Internal.D07.Ch05.OrbitStabilizerDefinitions
import MathGenome.Internal.Specs.D07.Ch05.OrbitStabilizerEquivalence
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Orbit–stabilizer as a bijection of sets

`K07.05.orbit_stabilizer_equivalence`, paper.tex:841–848.
Mathlib's quotient by a subgroup is the left-coset quotient: its relation
is `g⁻¹ * h ∈ H`, as expressed by `QuotientGroup.leftRel_apply`.
The inverse of the library's orbit-to-quotient equivalence has precisely
the source's direction and the required value on every representative.
-/

namespace D07.Ch05.OrbitStabilizerEquivalence

universe u v

open D07.Ch05.OrbitStabilizerDefinitions

/-- For any point of any group action, `g Stab(x) ↦ g • x` gives a
bijection of the left cosets onto the orbit. -/
theorem orbit_stabilizer_equivalence (G : Type u) (X : Type v)
    [Group G] [MulAction G X] (x : X) :
    ∃ e : (G ⧸ stabilizer G X x) ≃ ↥(orbit G X x),
      ∀ g : G, (e (QuotientGroup.mk g) : X) = g • x := by
  refine ⟨(MulAction.orbitEquivQuotientStabilizer G x).symm, ?_⟩
  intro g
  exact MulAction.orbitEquivQuotientStabilizer_symm_apply G x g

end D07.Ch05.OrbitStabilizerEquivalence
