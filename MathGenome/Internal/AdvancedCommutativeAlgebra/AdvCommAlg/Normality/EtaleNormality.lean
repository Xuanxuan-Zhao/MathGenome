import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.EtaleNormality
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.EtaleLocalNumerics
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.SerreCriterion
import Batteries.Tactic.OpenPrivate

/-! Ascent and faithfully flat descent of normality under étale maps.
The comparisons of depth, dimension and cotangent dimensions are made
at the prime of the target and its contraction in the source. -/
noncomputable section
universe u
namespace AdvCommAlg.Normality

open private ringSerreCondition_iff_local_depth from MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.SerreCriterion

/-- The local numerical comparisons transport regularity and library depth. -/
private theorem etale_local_regular_depth (A B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [Algebra.Etale A B] (q : PrimeSpectrum B) :
    let R := Localization.AtPrime (q.asIdeal.under A)
    let S := Localization.AtPrime q.asIdeal
    (ringKrullDim R = ringKrullDim S) ∧
    (IsRegularLocalRing R ↔ IsRegularLocalRing S) ∧
    (IsLocalRing.depth (ModuleCat.of R R) = IsLocalRing.depth (ModuleCat.of S S)) := by
  letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  obtain ⟨_, _, _, _, hdim, hdepth, hcot⟩ := (etale_local_numerics A B).2 q
  refine ⟨hdim, ?_, ?_⟩
  · rw [IsRegularLocalRing.iff_finrank_cotangentSpace,
      IsRegularLocalRing.iff_finrank_cotangentSpace, hcot.2, hdim]
  · rw [← Depth.depth_eq_libraryDepth, ← Depth.depth_eq_libraryDepth]
    exact hdepth

/-- SN-13: normality ascends along every étale map from a Noetherian ring. -/
theorem etale_normal_ascent : Specs.etaleNormalAscentType.{u} := by
  intro A B _ _ _ _ _ hA
  letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  refine ⟨inferInstance, ?_⟩
  obtain ⟨hR, hS⟩ := (serreCriterion A).mp hA
  apply (serreCriterion B).mpr
  constructor
  · intro q hq
    obtain ⟨hdim, hreg, _⟩ := etale_local_regular_depth A B q
    apply hreg.mp
    apply hR ⟨q.asIdeal.under A, inferInstance⟩
    apply WithBot.coe_le_coe.mp
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height (q.asIdeal.under A)
      (Localization.AtPrime (q.asIdeal.under A)), hdim,
      IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (Localization.AtPrime q.asIdeal)]
    exact WithBot.coe_le_coe.mpr hq
  · apply (ringSerreCondition_iff_local_depth B 2).mpr
    intro q
    obtain ⟨hdim, _, hdepth⟩ := etale_local_regular_depth A B q
    have hp := (ringSerreCondition_iff_local_depth A 2).mp hS
      ⟨q.asIdeal.under A, inferInstance⟩
    rwa [hdim, hdepth] at hp

/-- SN-13: faithful flatness supplies a prime over every base prime,
so the same comparisons give descent of normality. -/
theorem etale_normal_descent : Specs.etaleNormalDescentType.{u} := by
  intro A B _ _ _ _ _ _ hB
  obtain ⟨hnoeth, hB⟩ := hB
  letI := hnoeth
  obtain ⟨hR, hS⟩ := (serreCriterion B).mp hB
  apply (serreCriterion A).mpr
  constructor
  · intro p hp
    obtain ⟨q, rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
      (A := A) (B := B) p
    obtain ⟨hdim, hreg, _⟩ := etale_local_regular_depth A B q
    apply hreg.mpr
    apply hR q
    apply WithBot.coe_le_coe.mp
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal
      (Localization.AtPrime q.asIdeal), ← hdim,
      IsLocalization.AtPrime.ringKrullDim_eq_height (q.asIdeal.under A)
        (Localization.AtPrime (q.asIdeal.under A))]
    exact WithBot.coe_le_coe.mpr hp
  · apply (ringSerreCondition_iff_local_depth A 2).mpr
    intro p
    obtain ⟨q, rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
      (A := A) (B := B) p
    obtain ⟨hdim, _, hdepth⟩ := etale_local_regular_depth A B q
    have hq := (ringSerreCondition_iff_local_depth B 2).mp hS q
    change min (2 : WithBot ℕ∞)
      (ringKrullDim (Localization.AtPrime (q.asIdeal.under A))) ≤
      (IsLocalRing.depth (ModuleCat.of (Localization.AtPrime (q.asIdeal.under A))
        (Localization.AtPrime (q.asIdeal.under A))) : WithBot ℕ∞)
    rwa [hdim, hdepth]

end AdvCommAlg.Normality
