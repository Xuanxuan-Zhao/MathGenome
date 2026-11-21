import MathGenome.Internal.Specs.D07.Ch07.FgTorsionFinite
import MathGenome.Internal.D07.Ch07.FgAbelianExtension
import MathGenome.Internal.D07.Ch04.DirectProducts
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-! K07.07.fg_torsion_finite. The counterexample is a direct sum, with
the pointwise additive structure inherited from its finite-support functions. -/
namespace D07.Ch07.FgTorsionFinite

universe u
open Specs.D07.Ch07.FgTorsionFinite

theorem finite_of_fg_torsion : FiniteOfFgTorsion.{u} := by
  intro A _ _ hA
  exact AddCommGroup.finite_of_fg_isAddTorsion A hA

theorem torsion_iff_rank_zero : TorsionIffRankZero.{u} := by
  intro A _ _ r d hd E
  constructor
  · intro hA
    exact (FgAbelianExtension.finiteness_criterion A r d hd E).mp
      (finite_of_fg_torsion A hA)
  · intro hr
    have : Finite A := (FgAbelianExtension.finiteness_criterion A r d hd E).mpr hr
    exact isAddTorsion_of_finite

theorem finite_support_description : FiniteSupportDescription.{u} := by
  intro I p
  exact D07.Ch04.DirectProducts.direct_sum_identification I (fun _ => ZMod p)

theorem pointwise_operations : PointwiseOperations.{u} := by
  intro I p
  exact ⟨fun _ _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem annihilation : Annihilation.{u} := by
  intro I p _ b
  apply DirectSum.ext
  intro i
  change p • b i = (0 : ZMod p)
  exact ZModModule.char_nsmul_eq_zero p (b i)

theorem torsion_with_positive_annihilator : TorsionWithPositiveAnnihilator.{u} := by
  intro I p hp
  refine ⟨hp.pos, ?_, annihilation I p hp⟩
  intro b
  exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨p, hp.pos, annihilation I p hp b⟩

theorem coordinate_generator_values : CoordinateGeneratorValues.{u} := by
  classical
  intro I p i
  exact ⟨DirectSum.of_eq_same i 1,
    fun j hji => DirectSum.of_eq_of_ne i j 1 hji⟩

theorem coordinate_generators_injective : CoordinateGeneratorsInjective.{u} := by
  classical
  intro I p hp i j hij
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  by_contra hne
  have h := congrArg (fun b : PrimeSum I p => b i) hij
  rw [(coordinate_generator_values I p i).1,
    (coordinate_generator_values I p j).2 i hne] at h
  exact one_ne_zero h

theorem infinite_counterexample : InfiniteCounterexample.{u} := by
  intro I _ p hp
  exact Infinite.of_injective _ (coordinate_generators_injective I p hp)

theorem not_finitely_generated : NotFinitelyGenerated.{u} := by
  intro I _ p hp hfg
  have : AddGroup.FG (PrimeSum I p) := hfg
  have : Infinite (PrimeSum I p) := infinite_counterexample I p hp
  have : Finite (PrimeSum I p) :=
    finite_of_fg_torsion (PrimeSum I p) (torsion_with_positive_annihilator I p hp).2.1
  exact not_finite (PrimeSum I p)

end D07.Ch07.FgTorsionFinite
