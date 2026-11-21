import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

/-!
Independent statements for K07.13.primitive_distinction, paper.tex:3923–3929.
`Algebra K L` records the chosen base embedding and `IntermediateField.adjoin`
is field generation inside that same L. The first statement holds even without
finiteness, so applies in particular to every specified embedded finite field.
The counterexample is constructed inside any algebraically closed overfield of
the fixed base ZMod 3, rather than identifying unrelated copies of F₉.
-/

namespace Specs.D07.Ch13.PrimitiveDistinction

universe u v

def MultiplicativeGeneratorIsFieldGenerator : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (a : Lˣ), Subgroup.zpowers a = ⊤ →
      IntermediateField.adjoin K ({(a : L)} : Set L) = ⊤

def QuadraticOverThree : Prop :=
  (∀ x : ZMod 3, Polynomial.eval x (Polynomial.X ^ 2 + 1) ≠ 0) ∧
    Irreducible (Polynomial.X ^ 2 + 1 : Polynomial (ZMod 3))

/-- The source's i²=-1 counterexample, with its actual field and unit orders.
The existential intermediate field is literally a subfield of the chosen Ω.
-/
def EmbeddedCounterexample : Prop :=
  ∀ (Ω : Type u) [Field Ω] [Algebra (ZMod 3) Ω] [IsAlgClosed Ω],
    ∃ (E : IntermediateField (ZMod 3) Ω) (i : Eˣ),
      Finite E ∧ Nat.card E = 9 ∧ Module.finrank (ZMod 3) E = 2 ∧
        Nat.card Eˣ = 8 ∧ (i : E) ^ 2 = -1 ∧
        IntermediateField.adjoin (ZMod 3) ({(i : E)} : Set E) = ⊤ ∧
        orderOf i = 4 ∧ Subgroup.zpowers i ≠ ⊤

end Specs.D07.Ch13.PrimitiveDistinction
