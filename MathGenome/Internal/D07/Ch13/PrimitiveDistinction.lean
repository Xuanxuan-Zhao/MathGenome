import MathGenome.Internal.Specs.D07.Ch13.PrimitiveDistinction
import MathGenome.Internal.D07.Ch11.LowDegreeIrreducible
import MathGenome.Internal.D07.Ch11.QuotientNormalForm
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
K07.13.primitive_distinction (paper.tex:3923–3929).
For a unit generator, zero and the integer powers give the whole field.
For the converse, choose a root x of X²+1 in the specified algebraically
closed ambient field. Irreducibility identifies its minimal polynomial;
the base-preserving quotient isomorphism gives |F₃(x)|=3² and degree two.
Its distinguished root generates that field, but its square is -1, so its
unit order is four, smaller than the eight units of the field.
-/

namespace D07.Ch13.PrimitiveDistinction

universe u v

open Polynomial IntermediateField
open Specs.D07.Ch13.PrimitiveDistinction

theorem multiplicativeGenerator_is_fieldGenerator :
    MultiplicativeGeneratorIsFieldGenerator.{u,v} := by
  intro K L _ _ _ a ha
  apply top_unique
  intro x _
  by_cases hx : x = 0
  · simp [hx]
  · have hm : Units.mk0 x hx ∈ Subgroup.zpowers a := by rw [ha]; trivial
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hm
    have hmem := (IntermediateField.adjoin K ({(a : L)} : Set L)).pow_mem
      (IntermediateField.mem_adjoin_simple_self K (a : L)) n
    simpa only [← Units.val_zpow_eq_zpow_val, hn, Units.val_mk0] using hmem

theorem quadratic_over_three : QuadraticOverThree := by
  have hr : ∀ x : ZMod 3, Polynomial.eval x (X ^ 2 + 1) ≠ 0 := by
    intro x
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    fin_cases x <;> decide
  refine ⟨hr, ?_⟩
  apply (D07.Ch11.LowDegreeIrreducible.degree_two_or_three_iff_no_root
    (ZMod 3) (X ^ 2 + 1) (Or.inl ?_)).mpr hr
  simpa using Polynomial.degree_X_pow_add_C (R := ZMod 3) (by decide : 0 < 2) 1

theorem embedded_counterexample : EmbeddedCounterexample.{u} := by
  intro Ω _ _ _
  let f : Polynomial (ZMod 3) := X ^ 2 + 1
  have hf : Irreducible f := quadratic_over_three.2
  have hm : f.Monic := by
    simpa [f] using (Polynomial.monic_X_pow_add_C (1 : ZMod 3) (by decide : 2 ≠ 0))
  have hd : f.degree = (2 : WithBot ℕ) := by
    simpa [f] using Polynomial.degree_X_pow_add_C (R := ZMod 3) (by decide : 0 < 2) 1
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero Ω f (by rw [hd]; decide)
  have hi : IsIntegral (ZMod 3) x := ⟨f, hm, hx⟩
  have hmin : minpoly (ZMod 3) x = f :=
    (minpoly.eq_of_irreducible_of_monic hf hx hm).symm
  let E : IntermediateField (ZMod 3) Ω := IntermediateField.adjoin (ZMod 3) {x}
  let j : E := AdjoinSimple.gen (ZMod 3) x
  have hj2 : j ^ 2 = -1 := by
    apply Subtype.ext
    have hs : x ^ 2 + 1 = 0 := by simpa [f] using hx
    exact eq_neg_of_add_eq_zero_left hs
  have hj0 : j ≠ 0 := by
    intro he
    simpa [he] using hj2
  let i : Eˣ := Units.mk0 j hj0
  have hquot : Finite (AdjoinRoot f) ∧
      Nat.card (AdjoinRoot f) = Nat.card (ZMod 3) ^ f.natDegree :=
    D07.Ch11.QuotientNormalForm.finiteCardinality (ZMod 3) f hf.ne_zero
  let e : AdjoinRoot f ≃ₐ[ZMod 3] E :=
    (AdjoinRoot.algEquivOfEq (ZMod 3) f _ hmin.symm).trans
      (adjoinRootEquivAdjoin (ZMod 3) hi)
  let : Finite (AdjoinRoot f) := hquot.1
  let : Finite E := Finite.of_equiv (AdjoinRoot f) e.toEquiv
  have hcard : Nat.card E = 9 := by
    rw [← Nat.card_congr e.toEquiv, hquot.2]
    norm_num [f]
  have hdim : Module.finrank (ZMod 3) E = 2 := by
    change Module.finrank (ZMod 3) ((ZMod 3)⟮x⟯) = 2
    rw [adjoin.finrank hi, hmin]
    norm_num [f]
  have hcardu : Nat.card Eˣ = 8 := by rw [Nat.card_units, hcard]
  have hgen : IntermediateField.adjoin (ZMod 3) ({(i : E)} : Set E) = ⊤ := by
    change IntermediateField.adjoin (ZMod 3) {j} = ⊤
    exact (eq_adjoin_of_eq_algebra_adjoin (ZMod 3) _ ⊤
      ((adjoin.powerBasis hi).adjoin_gen_eq_top).symm).symm
  have htwo : i ^ 2 ≠ 1 := by
    intro he
    have he' : (j : E) ^ 2 = 1 := congrArg Units.val he
    have hn : (-1 : E) ≠ 1 := by
      have hn3 : (-1 : ZMod 3) ≠ 1 := by decide
      intro h
      apply hn3
      apply (algebraMap (ZMod 3) E).injective
      simpa using h
    exact hn (hj2.symm.trans he')
  have hfour : i ^ 4 = 1 := by
    apply Units.ext
    change j ^ 4 = 1
    rw [show 4 = 2 * 2 from rfl, pow_mul, hj2]
    norm_num
  have hord : orderOf i = 4 := by
    apply orderOf_eq_of_pow_and_pow_div_prime (by decide : 0 < 4) hfour
    intro p hp hp4
    have hp2 : p = 2 := by
      have : p ∣ 2 ^ 2 := hp4
      exact (Nat.le_of_dvd (by decide : 0 < 2) (hp.dvd_of_dvd_pow this)).antisymm hp.two_le
    simpa [hp2] using htwo
  refine ⟨E, i, inferInstance, hcard, hdim, hcardu, hj2, hgen, hord, ?_⟩
  intro he
  have hec := orderOf_eq_card_of_zpowers_eq_top he
  rw [hord, hcardu] at hec
  norm_num at hec

end D07.Ch13.PrimitiveDistinction
