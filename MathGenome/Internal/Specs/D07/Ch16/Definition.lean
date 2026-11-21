import MathGenome.Internal.Specs.D07.Ch08.RingDefinition
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Submodule.Defs

/-!
Independent specification for K07.16.definition (paper.tex:2927–2943).

Scalars form an associative unital ring, with no commutativity or
nontriviality assumption. Vectors form an abelian group, with no
multiplication on vectors. All actions are on the left. `ModuleLaws` lists
only the four displayed source axioms; zero absorption is not assumed.
The characterization keeps the given additive structure and scalar action.
For fields the same structure is a vector space, including the zero space.

The integer action on an abelian group is the canonical `zsmul`, defined
by repeated addition and additive inverses. Existence and the forced value
of *every* integer-module action are specified separately. The final
characterization uses precisely the source definition of a left ideal:
an additive subgroup closed under multiplication by arbitrary ring
elements on the left (paper.tex:1297–1301).
-/

universe u v

namespace Specs.D07.Ch16.Definition

structure ModuleLaws (R : Type u) [Ring R] (M : Type v)
    [AddCommGroup M] [SMul R M] : Prop where
  one_smul : ∀ m : M, (1 : R) • m = m
  mul_smul : ∀ (r s : R) (m : M), (r * s) • m = r • (s • m)
  add_smul : ∀ (r s : R) (m : M), (r + s) • m = r • m + s • m
  smul_add : ∀ (r : R) (m n : M), r • (m + n) = r • m + r • n

/-- The source's four axioms are equivalent to the canonical module
structure on the same abelian group, retaining the supplied action. -/
def ModuleCharacterization : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] (s : SMul R M),
    @ModuleLaws R _ M _ s ↔ ∃ a : Module R M, a.toSMul = s

def ZeroSmul : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M]
    [Module R M] (m : M), (0 : R) • m = 0

def SmulZero : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M]
    [Module R M] (r : R), r • (0 : M) = 0

def NegSmul : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M]
    [Module R M] (r : R) (m : M), (-r) • m = -(r • m)

def SmulNeg : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M]
    [Module R M] (r : R) (m : M), r • (-m) = -(r • m)

/-- A vector space over a field is exactly a module over that field:
the same four action axioms and the same abelian group. -/
def VectorSpaceCharacterization : Prop :=
  ∀ (K : Type u) [Field K] (V : Type v) [AddCommGroup V] (s : SMul K V),
    @ModuleLaws K _ V _ s ↔ ∃ a : Module K V, a.toSMul = s

/-- Every abelian group admits an integer-module structure whose action
is its repeated-addition and negative-integer action. -/
def IntegerModuleExistence : Prop :=
  ∀ (M : Type v) [AddCommGroup M],
    ∃ a : Module ℤ M, ∀ (z : ℤ) (m : M), a.smul z m = z • m

/-- An arbitrary integer-module structure on the fixed abelian group has
precisely that canonical action; no choice of scalar action is left. -/
def IntegerModuleAction : Prop :=
  ∀ (M : Type v) [AddCommGroup M] (a : Module ℤ M) (z : ℤ) (m : M),
    a.smul z m = z • m

/-- The ring acts on its additive group by multiplication on the left. -/
def RegularModule : Prop :=
  ∀ (R : Type u) [Ring R],
    ∃ a : Module R R, ∀ r x : R, a.smul r x = r * x

/-- The left ideals are exactly the submodules of the canonical left
regular module. No right-absorption condition is imposed. -/
def LeftIdealCharacterization : Prop :=
  ∀ (R : Type u) [Ring R] (I : AddSubgroup R),
    (∀ r x : R, x ∈ I → r * x ∈ I) ↔
      ∃ N : Submodule R R, N.toAddSubgroup = I

end Specs.D07.Ch16.Definition
