import MathGenome.Internal.Specs.D07.Ch20.PurelyInseparable
import MathGenome.Internal.D07.Ch12.EmbeddingExtension
import MathGenome.Internal.D07.Ch12.Inseparability

/-!
Pure inseparability (K07.20.purely_inseparable).
The power criterion agrees with Mathlib's canonical predicate. The separable
degree of a polynomial counts its distinct roots in any algebraically closed
field. A one-root minimal polynomial is a Frobenius binomial; its minimality
forces the exponent to be least. Finite-degree and uniqueness results apply
to arbitrary purely inseparable extensions, without separability assumptions.
The rational-function example reuses the accepted irreducibility and simple
extension results from K07.12.inseparability.
-/

universe u v w

namespace D07.Ch20.PurelyInseparable

open Polynomial
open Specs.D07.Ch20.PurelyInseparable

noncomputable section

theorem positive_characteristic : PositiveCharacteristic.{u, v} := by
  intro K L _ _ _ p _ hp
  let : ExpChar K p := ExpChar.prime hp
  constructor
  · intro h
    let := h
    exact ⟨inferInstance, (isPurelyInseparable_iff_pow_mem K p).mp h⟩
  · intro h
    exact (isPurelyInseparable_iff_pow_mem K p).mpr h.2

theorem characteristic_zero : CharacteristicZero.{u, v} := by
  intro K L _ _ _ _
  simpa only [Function.Surjective, pow_one, one_pow, exists_const, RingHom.mem_range] using
    (isPurelyInseparable_iff_pow_mem K 1 (E := L))

theorem algebraicity : Algebraicity.{u, v} := by
  intro K L _ _ _ h
  let := h
  infer_instance

theorem one_root_iff_power : OneRootIffPower.{u, v, w} := by
  classical
  intro K L Ω _ _ _ _ _ _ p _ hp a ha
  let : ExpChar K p := ExpChar.prime hp
  rw [← Polynomial.natSepDegree_eq_of_isAlgClosed Ω (f := minpoly K a)]
  exact minpoly.natSepDegree_eq_one_iff_pow_mem p

theorem power_iff_least_binomial : PowerIffLeastBinomial.{u, v} := by
  intro K L _ _ _ p _ hp a ha
  let : ExpChar K p := ExpChar.prime hp
  constructor
  · intro h
    obtain ⟨t, b, hm⟩ := (minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C p).mp
      ((minpoly.natSepDegree_eq_one_iff_pow_mem p).mpr h)
    have hb : algebraMap K L b = a ^ (p ^ t) := by
      have hz := minpoly.aeval K a
      rw [hm] at hz
      exact (sub_eq_zero.mp (by simpa only [map_sub, map_pow, aeval_X, aeval_C] using hz)).symm
    refine ⟨t, b, hb, ?_, hm⟩
    intro r hr ⟨c, hc⟩
    have hz : aeval a (X ^ (p ^ r) - C c) = 0 := by
      simp only [map_sub, map_pow, aeval_X, aeval_C, hc, sub_self]
    have hd := natDegree_le_natDegree
      (minpoly.min K a (monic_X_pow_sub_C c (pow_ne_zero _ hp.ne_zero)) hz)
    rw [hm, natDegree_X_pow_sub_C, natDegree_X_pow_sub_C] at hd
    exact (Nat.not_le_of_gt (Nat.pow_lt_pow_right hp.one_lt hr)) hd
  · rintro ⟨t, b, hb, _, _⟩
    exact ⟨t, b, hb⟩

theorem finite_degree : FiniteDegree.{u, v} := by
  intro K L _ _ _ p _ hp h _
  let : ExpChar K p := ExpChar.prime hp
  let := h
  exact IsPurelyInseparable.finrank_eq_pow K L p

theorem separable_pure_element : SeparablePureElement.{u, v} := by
  intro K L _ _ _ p _ hp a ha hs
  let : ExpChar K p := ExpChar.prime hp
  have hd := (minpoly.natSepDegree_eq_one_iff_pow_mem p).mpr ha
  rw [hs.natSepDegree_eq_natDegree] at hd
  exact minpoly.natDegree_eq_one_iff.mp hd

theorem separable_element_in_pure_extension : SeparableElementInPureExtension.{u, v} := by
  intro K L _ _ _ h
  let := h
  exact IsPurelyInseparable.inseparable K

theorem unique_embedding : UniqueEmbedding.{u, v, w} := by
  intro K L Ω _ _ _ _ _ h σ
  let := h
  obtain ⟨τ, _, hτ⟩ := D07.Ch12.EmbeddingExtension.extensionIntoAlgebraicallyClosed K L Ω σ
  have heq : τ.comp (algebraMap K L) = σ := by
    ext x
    exact hτ x
  refine ⟨τ, heq, ?_⟩
  intro τ' hτ'
  exact IsPurelyInseparable.injective_comp_algebraMap K L Ω (hτ'.trans heq.symm)

theorem example_root_exists : ExampleRootExists.{w} := by
  intro p _ Ω _ _ _
  obtain ⟨a, ha⟩ := D07.Ch12.Inseparability.example_root_exists p Ω
  exact ⟨a, by simpa [Specs.D07.Ch12.Inseparability.examplePolynomial, sub_eq_zero] using ha⟩

theorem rational_function_example : RationalFunctionExample.{v, w} := by
  intro p _ L Ω _ _ _ _ _ a ha
  let K := RatFunc (ZMod p)
  have hpure : IsPurelyInseparable K (IntermediateField.adjoin K {a}) :=
    (IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem K L p).mpr
      ⟨1, RatFunc.X, by simpa using ha.symm⟩
  have hroot : aeval a (Specs.D07.Ch12.Inseparability.examplePolynomial p) = 0 := by
    simp [Specs.D07.Ch12.Inseparability.examplePolynomial, ha]
  have hd : Module.finrank K (IntermediateField.adjoin K {a}) = p := by
    rw [IntermediateField.adjoin.finrank (D07.Ch12.Inseparability.example_integral p L a hroot),
      D07.Ch12.Inseparability.example_minpoly p L a hroot]
    exact D07.Ch12.Inseparability.example_natDegree p
  have hgt : 1 < Module.finrank K (IntermediateField.adjoin K {a}) := by
    rw [hd]
    exact (Fact.out : p.Prime).one_lt
  exact ⟨hpure, hd, hgt,
    D07.Ch12.Inseparability.example_unique_embedding p L Ω a hroot⟩

theorem example_embedding_is_inclusion : ExampleEmbeddingIsInclusion.{v, w} := by
  intro p _ L Ω _ _ _ _ a ha i f
  let K := RatFunc (ZMod p)
  let : IsPurelyInseparable K (IntermediateField.adjoin K {a}) :=
    (IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem K L p).mpr
      ⟨1, RatFunc.X, by simpa using ha.symm⟩
  exact Subsingleton.elim _ _

end

end D07.Ch20.PurelyInseparable
