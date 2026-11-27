import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.FiniteFieldKummer
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.KummerConnecting
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.IntegralDomain

namespace GaloisFormalization.GH.FiniteFieldKummer

open Specs.GaloisFormalization.GH.FiniteFieldKummer
open Specs.GaloisFormalization.GH.KummerConnecting (RootCohomology)
open Specs.GaloisFormalization.GH.KummerCoefficients (PowerClasses powerClass)

universe u v

theorem cohomologyCyclicOrder : CohomologyCyclicOrder.{u, v} := by
  intro k S _ _ _ _ _ _ _ p m _ hm hpm
  have hu : IsUnit (m : k) :=
    isUnit_iff_ne_zero.mpr ((CharP.cast_eq_zero_iff k p m).not.mpr hpm)
  obtain ⟨e, _⟩ := KummerConnecting.kummerIsomorphism (k := k) (S := S) hm hu
  have hCyclic : IsCyclic (PowerClasses k m) :=
    isCyclic_of_surjective (powerClass k m) (QuotientGroup.mk'_surjective _)
  refine ⟨e.isCyclic.mp hCyclic, ?_⟩
  rw [← Nat.card_congr e.toEquiv]
  change (powMonoidHom m : kˣ →* kˣ).range.index = _
  rw [IsCyclic.index_powMonoidHom_range, Nat.card_units, Nat.gcd_comm]

theorem cohomologySubsingletonOfGcdEqOne : CohomologySubsingletonOfGcdEqOne.{u, v} := by
  intro k S _ _ _ _ _ _ _ p m _ hm hpm hgcd
  have hCard : Nat.card (RootCohomology k S m) = 1 :=
    (cohomologyCyclicOrder (k := k) (S := S) hm hpm).2.trans hgcd
  exact (Nat.card_eq_one_iff_unique.mp hCard).1

theorem cohomologyOneSubsingleton : CohomologyOneSubsingleton.{u, v} := by
  intro k S _ _ _ _ _ _ _
  have hChar : ¬ ringChar k ∣ 1 := by
    intro h
    exact (one_ne_zero : (1 : k) ≠ 0) (by
      simpa only [Nat.cast_one] using (CharP.cast_eq_zero_iff k (ringChar k) 1).mpr h)
  exact cohomologySubsingletonOfGcdEqOne (k := k) (S := S) le_rfl hChar (Nat.gcd_one_left _)

end GaloisFormalization.GH.FiniteFieldKummer
