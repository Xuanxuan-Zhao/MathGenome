import MathGenome.Internal.Specs.D07.Ch13.IrreduciblesExist
import MathGenome.Internal.D07.Ch13.Existence
import MathGenome.Internal.D07.Ch13.MultiplicativeCyclic
import MathGenome.Internal.D07.Ch13.PrimitiveDistinction

/-!
K07.13.irreducibles_exist, paper.tex:3990–3997.
Construct the specified embedded root field in one algebraic closure of K.
Its unit-group generator generates that same field over K, so the degree of
its monic irreducible minimal polynomial is the constructed extension degree.
-/

universe u

namespace D07.Ch13.IrreduciblesExist

open IntermediateField

theorem monic_irreducible_of_every_positive_degree :
    Specs.D07.Ch13.IrreduciblesExist.MonicIrreducibleOfEveryPositiveDegree.{u} := by
  intro K _ _ n hn
  obtain ⟨Ω, hΩ, aΩ, _, halg, hclosed⟩ := D07.Ch12.AlgebraicClosure.existence K
  let := hΩ
  let := aΩ
  let := halg
  let := hclosed
  let E := Existence.rootField K Ω (Nat.card K) n
  have hE := Existence.embedded_existence K Ω (Nat.card K) n rfl hn
  let : Finite E := hE.1
  let : FiniteDimensional K E := hE.2.2.1
  have hdim : Module.finrank K E = n := hE.2.2.2.1
  have hcyclic : IsCyclic Eˣ :=
    (MultiplicativeCyclic.finite_field_units E (Nat.card E) rfl).1
  obtain ⟨a, ha⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyclic
  have hgen : IntermediateField.adjoin K ({(a : E)} : Set E) = ⊤ :=
    PrimitiveDistinction.multiplicativeGenerator_is_fieldGenerator K E a ha
  have hi : IsIntegral K (a : E) := IsIntegral.of_finite K (a : E)
  refine ⟨minpoly K (a : E), minpoly.monic hi, minpoly.irreducible hi, ?_⟩
  calc
    (minpoly K (a : E)).natDegree =
        Module.finrank K (IntermediateField.adjoin K {(a : E)}) :=
      (IntermediateField.adjoin.finrank hi).symm
    _ = Module.finrank K E := by rw [hgen, IntermediateField.finrank_top']
    _ = n := hdim

end D07.Ch13.IrreduciblesExist
