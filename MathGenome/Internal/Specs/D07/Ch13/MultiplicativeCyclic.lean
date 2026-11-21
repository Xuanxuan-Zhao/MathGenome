import MathGenome.Internal.Specs.D07.Ch12.FiniteMultiplicativeCyclic
import Mathlib.Data.Nat.Totient

/-!
Independent statements for `K07.13.multiplicative_cyclic`
(paper.tex:3915–3921; chapters/M07.13.tex:50–56).

The multiplicative group is the unit group, with the inherited operations.
The subgroup assertion permits an infinite ambient field and the trivial
subgroup. The finite-field assertion applies to any specified field K of
cardinality q, hence in particular to the chapter's chosen q-element base
and its embedded finite extensions. It makes no choice of a new field copy.
Generators are counted as elements whose integer powers give all the units.
`Finite K` ensures that `Nat.card` represents actual finite cardinality;
the case q = 2 (the trivial unit group) is included.
-/

namespace Specs.D07.Ch13.MultiplicativeCyclic

universe u

/-- Every finite subgroup of a field's multiplicative group is cyclic. -/
def FiniteMultiplicativeSubgroupIsCyclic : Prop :=
  Specs.D07.Ch12.FiniteMultiplicativeCyclic.FiniteMultiplicativeSubgroupIsCyclic.{u}

/-- The units of a q-element field form a cyclic group of order q-1,
with exactly totient (q-1) generating elements. -/
def FiniteFieldUnits : Prop :=
  ∀ (K : Type u) [Field K] [Finite K] (q : ℕ), Nat.card K = q →
    IsCyclic Kˣ ∧ Nat.card Kˣ = q - 1 ∧
      Nat.card {a : Kˣ // Subgroup.zpowers a = ⊤} = Nat.totient (q - 1)

end Specs.D07.Ch13.MultiplicativeCyclic
