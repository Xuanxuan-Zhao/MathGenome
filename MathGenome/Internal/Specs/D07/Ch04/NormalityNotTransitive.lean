import MathGenome.Internal.Specs.D07.Ch02.PermutationConvention
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.Perm

/-!
Independent specification of `K07.04.normality_not_transitive`
(paper.tex:738–746). In `Fin 4`, the paper's letters 1,2,3,4 are
represented by 0,1,2,3 respectively, as in `PermutationConvention.FiniteLabels`.
Multiplication is rightmost-first composition. The two sets below are
literal sets of permutations, rather than generated subgroups whose
carriers would still need to be identified.
-/

namespace Specs.D07.Ch04.NormalityNotTransitive

abbrev S4 := Equiv.Perm (Fin 4)

/-- The paper's `(12)(34)`. -/
def double12_34 : S4 := Equiv.swap 0 1 * Equiv.swap 2 3

/-- The paper's `(13)(24)`. -/
def double13_24 : S4 := Equiv.swap 0 2 * Equiv.swap 1 3

/-- The paper's `(14)(23)`. -/
def double14_23 : S4 := Equiv.swap 0 3 * Equiv.swap 1 2

/-- The paper's cycle `(123)`. -/
def cycle123 : S4 := Equiv.swap 0 1 * Equiv.swap 1 2

def vCarrier : Set S4 := {1, double12_34, double13_24, double14_23}

def hCarrier : Set S4 := {1, double12_34}

/-- Both specified sets are subgroups; normality holds in the two indicated
ambient groups and fails for `H` in the full symmetric group. The commutativity
assertion also records the source's description of `V` as abelian. -/
def Counterexample : Prop :=
  ∃ V H : Subgroup S4,
    (V : Set S4) = vCarrier ∧
    (H : Set S4) = hCarrier ∧
    H ≤ V ∧
    (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) ∧
    (H.subgroupOf V).Normal ∧ V.Normal ∧ ¬ H.Normal

/-- The explicit conjugate used in the paper to witness the failure. -/
def ConjugationWitness : Prop :=
  double12_34 ∈ hCarrier ∧
  cycle123 * double12_34 * cycle123⁻¹ = double14_23 ∧
  double14_23 ∉ hCarrier

end Specs.D07.Ch04.NormalityNotTransitive
