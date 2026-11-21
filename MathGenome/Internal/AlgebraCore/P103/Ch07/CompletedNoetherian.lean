import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.CompletedNoetherian
import MathGenome.Internal.AlgebraCore.P103.Ch07.CompletedQuotients
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.MvPowerSeries.Evaluation

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

universe u
namespace P103.Ch07.CompletedNoetherian
noncomputable section
open P103.Adic P103.Specs.Ch07.CompletedQuotients

/-- A finite-variable power series presentation proves Noetherianness without
assuming that ideals of the completion are closed. -/
theorem completed_noetherian :
    P103.Specs.Ch07.CompletedNoetherian.completed_noetherianType.{u} := by
  intro R _ _ I
  obtain ⟨n, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    I.fg_of_isNoetherianRing
  let S := Completion I R
  let J : Ideal S := extendedIdeal I
  have hc : IsAdicComplete J S := by
    apply (IsAdicComplete.map_algebraMap_iff I S (S := S)).mpr
    exact AdicCompletion.isAdicComplete (M := R) I.fg_of_isNoetherianRing
  let := hc
  let : WithIdeal R := ⟨⊥⟩
  let : WithIdeal S := ⟨J⟩
  have hd : DiscreteTopology R := is_bot_adic_iff.mp rfl
  let := hd
  have ht : CompleteSpace S ∧ T2Space S :=
    (IsAdic.isAdicComplete_iff (I := J) rfl).mp hc
  let := ht.1
  let := ht.2
  let φ : R →+* S := algebraMap R S
  let b : Fin n → S := fun i => φ (a i)
  have hb : MvPowerSeries.HasEval b := by
    constructor
    · intro i
      apply WithIdeal.isTopologicallyNilpotent_of_mem
      apply Ideal.mem_map_of_mem
      rw [← ha]
      exact Submodule.subset_span (Set.mem_range_self i)
    · simp [Filter.cofinite_eq_bot]
  let f : MvPowerSeries (Fin n) R →+* S :=
    MvPowerSeries.eval₂Hom (continuous_of_discreteTopology : Continuous φ) hb
  have hfC (r : R) : f (MvPowerSeries.C r) = φ r := by
    simp [f, MvPowerSeries.coe_eval₂Hom]
  have hfX (i : Fin n) : f (MvPowerSeries.X i) = b i := by
    simp [f, MvPowerSeries.coe_eval₂Hom]
  let K : Ideal (MvPowerSeries (Fin n) R) :=
    Ideal.span (Set.range MvPowerSeries.X)
  have hK : K.map f = J := by
    rw [Ideal.map_span]
    change Ideal.span (f '' Set.range MvPowerSeries.X) = I.map φ
    have ha' : Ideal.span (Set.range a) = I := ha
    rw [← congrArg (Ideal.map φ) ha', Ideal.map_span]
    congr 1
    rw [← Set.range_comp, ← Set.range_comp]
    exact congrArg Set.range (funext hfX)
  have hs : Function.Surjective f := by
    have : IsHausdorff (K.map f) S := hK.symm ▸ hc.toIsHausdorff
    apply surjective_of_mk_map_comp_surjective (I := K) f
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I 1 x)
    refine ⟨MvPowerSeries.C r, ?_⟩
    change Ideal.Quotient.mk (K.map f) (f (MvPowerSeries.C r)) =
      Ideal.Quotient.mk (K.map f) x
    rw [hfC]
    apply Ideal.Quotient.eq.mpr
    rw [hK]
    change φ r - x ∈ extendedIdeal I
    rw [← pow_one (extendedIdeal I),
      ← P103.Ch07.CompletedQuotients.projection_kernel R I 1]
    change AdicCompletion.evalₐ I 1 (φ r - x) = 0
    rw [map_sub]
    change Ideal.Quotient.mk (I ^ 1) r - AdicCompletion.evalₐ I 1 x = 0
    rw [hr, sub_self]
  exact isNoetherianRing_of_surjective (MvPowerSeries (Fin n) R) S f hs

end
end P103.Ch07.CompletedNoetherian
