import MathGenome.Internal.Specs.D07.Ch12.PerfectFields
import MathGenome.Internal.D07.Ch12.CharacteristicZeroSeparability
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Field.ULift

/-!
Perfect fields, K07.12.perfect_fields (paper.tex:3768–3776).

For the reverse direction of the extension criterion, use the abstract field
K[X]/(f). Its power basis makes it an algebraic extension. The separability
of its distinguished root gives separability of f after removing the nonzero
leading-coefficient normalization. A universe lift lets this construction test
the hypothesis in any larger extension universe.

The positive-characteristic equivalence uses the library's proved bridge
between perfect fields and bijective Frobenius. Its surjective-to-perfect
direction needs reducedness, which holds for fields. No perfectness or
algebraically closed ambient field is assumed in this construction.
-/

universe u v

namespace D07.Ch12.PerfectFields

open Specs.D07.Ch12.PerfectFields

abbrev IsPerfect : PerfectPredicateType.{u} := perfectPredicateValue

theorem perfect_iff_irreducible_separable : PerfectIffIrreducibleSeparable.{u} := by
  intro K _
  exact ⟨fun h f hf => h.separable_of_irreducible hf, fun h => ⟨fun hf => h _ hf⟩⟩

theorem algebraic_extension_separable : AlgebraicExtensionSeparable.{u, v} := by
  intro K L _ _ _ hK hL
  refine ⟨fun a => ?_⟩
  exact hK.separable_of_irreducible (minpoly.irreducible (hL.isAlgebraic a).isIntegral)

theorem equivalent_criteria : EquivalentCriteria.{u, v} := by
  intro K _
  constructor
  · intro h L _ _ hL
    exact algebraic_extension_separable K L
      ((perfect_iff_irreducible_separable K).mpr h) hL
  · intro h f hf
    letI : Fact (Irreducible f) := ⟨hf⟩
    letI : Module.Finite K (AdjoinRoot f) := (AdjoinRoot.powerBasis hf.ne_zero).finite
    letI : Algebra.IsAlgebraic K (AdjoinRoot f) := inferInstance
    let e : AdjoinRoot f ≃ₐ[K] ULift.{v} (AdjoinRoot f) := ULift.algEquiv.symm
    letI : Algebra.IsAlgebraic K (ULift.{v} (AdjoinRoot f)) := e.isAlgebraic
    letI : Algebra.IsSeparable K (ULift.{v} (AdjoinRoot f)) := h _ inferInstance
    have hs : IsSeparable K (AdjoinRoot.root f) := e.isSeparable_iff.mp
      (Algebra.IsSeparable.isSeparable K (e (AdjoinRoot.root f)))
    change (minpoly K (AdjoinRoot.root f)).Separable at hs
    rw [AdjoinRoot.minpoly_root hf.ne_zero] at hs
    exact hs.of_mul_left

theorem characteristic_zero_perfect : CharacteristicZeroPerfect.{u} := by
  intro K _ _
  apply (perfect_iff_irreducible_separable K).mpr
  exact CharacteristicZeroSeparability.irreducible_polynomial_separable K

theorem finite_field_perfect : FiniteFieldPerfect.{u} := by
  intro K _ _
  exact PerfectField.ofFinite

theorem perfect_iff_frobenius_surjective : PerfectIffFrobeniusSurjective.{u} := by
  intro K _ p _ hp
  letI : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero K p).resolve_right (Nat.ne_of_gt hp)⟩
  constructor
  · intro hK
    letI : PerfectField K := hK
    exact surjective_frobenius K p
  · intro h
    letI : PerfectRing K p := PerfectRing.ofSurjective K p h
    exact PerfectRing.toPerfectField K p

theorem frobenius_properties : FrobeniusProperties.{u} := by
  intro K _ p _ hp
  letI : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero K p).resolve_right (Nat.ne_of_gt hp)⟩
  exact ⟨(frobenius K p).map_add, (frobenius K p).map_mul, frobenius_inj K p⟩

end D07.Ch12.PerfectFields
