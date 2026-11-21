import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ActionsDerivationsSemidirect
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.DerivedLowerSeries
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
LA-U06: source lines 1389–1397, with the arbitrary characteristic-zero field
convention at lines 1188–1190. The meaning of reductive is radical = center
(lines 4271–4272 and 4312–4317). A representation is a Lie homomorphism into
endomorphisms, as in A03. Complete reducibility is expressed by the invariant
complement property stated in C05 (lines 1356–1361).
-/

universe u v w
namespace Specs.LieAlgebrasAndRepresentations.ReductiveNonsemisimpleModule

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Invariance under the given representation, with no choice of an induced
Lie-module instance on the underlying vector space. -/
def Invariant {k : Type u} [Field k] {G : Type v} [LieRing G] [LieAlgebra k G]
    {M : Type w} [AddCommGroup M] [Module k M]
    (ρ : G →ₗ⁅k⁆ Module.End k M) (W : Submodule k M) : Prop :=
  ∀ x v, v ∈ W → ρ x v ∈ W

/-- Every invariant subspace has an invariant vector-space complement. -/
def CompletelyReducible {k : Type u} [Field k] {G : Type v}
    [LieRing G] [LieAlgebra k G] {M : Type w} [AddCommGroup M] [Module k M]
    (ρ : G →ₗ⁅k⁆ Module.End k M) : Prop :=
  ∀ W : Submodule k M, Invariant ρ W →
    ∃ U : Submodule k M, Invariant ρ U ∧ IsCompl W U

/-- The field itself has its commutator bracket, which vanishes. The formula
for the action makes the generator 1 act by exactly the 2 by 2 Jordan block
with a single 1 above the diagonal. Both spaces have their usual scalars. -/
def counterexample_type : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    Module.finrank k k = 1 ∧ Module.finrank k (k × k) = 2 ∧
    (∀ x y : k, ⁅x, y⁆ = 0) ∧
    LieAlgebra.radical k k = LieAlgebra.center k k ∧
    (∃ ρ : k →ₗ⁅k⁆ Module.End k (k × k),
      (∀ (x : k) (v : k × k), ρ x v = (x * v.2, 0)) ∧
      ρ 1 ≠ 0 ∧ (ρ 1) ^ 2 = 0 ∧ IsNilpotent (ρ 1) ∧
      ¬ CompletelyReducible ρ)

end Specs.LieAlgebrasAndRepresentations.ReductiveNonsemisimpleModule
