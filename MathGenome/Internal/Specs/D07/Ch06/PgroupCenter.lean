import MathGenome.Internal.Specs.D07.Ch06.PgroupDefinition

/-!
Independent statements for `K07.06.pgroup_center` (paper.tex:982–989).
The shared finite-p-group predicate includes finiteness and p-power
cardinality. Primality and nontriviality are explicit hypotheses; no
commutativity is assumed. The center is the canonical subgroup of G.
-/

namespace Specs.D07.Ch06.PgroupCenter

universe u

/-- A nontrivial finite p-group has a nontrivial center. -/
def CenterNontrivial : Prop :=
  ∀ (G : Type u) [Group G] [Nontrivial G] (p : ℕ), p.Prime →
    PgroupDefinition.finitePGroupValue p G → Nontrivial (Subgroup.center G)

/-- The prime also divides the finite cardinality of that center. -/
def PrimeDvdCardCenter : Prop :=
  ∀ (G : Type u) [Group G] [Nontrivial G] (p : ℕ), p.Prime →
    PgroupDefinition.finitePGroupValue p G → p ∣ Nat.card (Subgroup.center G)

end Specs.D07.Ch06.PgroupCenter
