import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.DimensionBounds
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.ReducedDimensionOne
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.LocalProperties.Reduced

/-! CM-14: a reduced Noetherian ring of dimension one is Cohen–Macaulay.
Prime avoidance gives a nonzerodivisor in every positive-dimensional local
ring. Reducedness is used through the intersection of the minimal primes. -/

universe u
namespace AdvCommAlg.CohenMacaulay

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsReduced R]

omit [IsNoetherianRing R] in
/-- Avoiding the minimal primes in a reduced ring makes multiplication injective. -/
lemma isSMulRegular_of_avoids_minimalPrimes (x : R)
    (hx : ∀ p ∈ minimalPrimes R, x ∉ p) : IsSMulRegular R x := by
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro y hxy
  change x * y = 0 at hxy
  have hy : y ∈ sInf (minimalPrimes R) := by
    rw [Ideal.mem_sInf]
    intro p hp
    apply (hp.isPrime.mem_or_mem ?_).resolve_left (hx p hp)
    rw [hxy]
    exact p.zero_mem
  simpa only [Ideal.sInf_minimalPrimes, Ideal.radical_bot_of_isReduced,
    Ideal.mem_bot] using hy

section Local
variable [IsLocalRing R]

/-- In positive dimension the maximal ideal is not minimal, so finite prime
avoidance finds an element acting injectively on the ring. -/
lemma exists_regular_mem_maximalIdeal_of_dim_ne_zero (hd : ringKrullDim R ≠ 0) :
    ∃ x ∈ IsLocalRing.maximalIdeal R, IsSMulRegular R x := by
  classical
  have hm : IsLocalRing.maximalIdeal R ∉ minimalPrimes R := by
    intro h
    apply hd
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
      Ideal.height_eq_zero_iff.mpr h]
    rfl
  have hnot : ¬ ((IsLocalRing.maximalIdeal R : Ideal R) : Set R) ⊆
      ⋃ p ∈ minimalPrimes R, (p : Set R) := by
    intro h
    obtain ⟨p, hp, hmp⟩ := (Ideal.subset_union_prime_finite
      (minimalPrimes.finite_of_isNoetherianRing R) (f := id)
      (⊥ : Ideal R) ⊥ (fun p hp _ _ => hp.isPrime)).mp h
    have he : IsLocalRing.maximalIdeal R = p :=
      (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hp.isPrime.ne_top hmp
    exact hm (he ▸ hp)
  obtain ⟨x, hxm, hx⟩ := Set.not_subset.mp hnot
  refine ⟨x, hxm, isSMulRegular_of_avoids_minimalPrimes R x ?_⟩
  intro p hp hxp
  exact hx (Set.mem_biUnion hp hxp)

omit [IsNoetherianRing R] in
/-- A zero-dimensional reduced local ring is a field. -/
lemma isField_of_isReduced_dim_eq_zero (hd : ringKrullDim R = 0) : IsField R := by
  let : Ring.KrullDimLE 0 R := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hd
  exact Ring.KrullDimLE.isField_of_isReduced

/-- Local depth is one in the positive-dimensional case. -/
lemma depth_eq_one_of_isReduced_dim_eq_one (hd : ringKrullDim R = 1) :
    IsLocalRing.depth (ModuleCat.of R R) = 1 := by
  obtain ⟨x, hxm, hx⟩ := exists_regular_mem_maximalIdeal_of_dim_ne_zero R (by
    rw [hd]; exact one_ne_zero)
  have hreg : RingTheory.Sequence.IsRegular R [x] := by
    apply (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
      (M := R) (by simpa using hxm)).mpr
    exact (RingTheory.Sequence.isWeaklyRegular_singleton_iff R x).mpr hx
  have hlower : (1 : ℕ∞) ≤ IsLocalRing.depth (ModuleCat.of R R) := by
    rw [IsLocalRing.depth_eq_sSup_length_isRegular]
    exact le_sSup ⟨[x], hreg, by simpa using hxm, by simp⟩
  have hupper := Depth.depth_le_supportDim (R := R) R
  rw [Depth.depth_eq_libraryDepth (ModuleCat.of R R),
    Module.supportDim_self_eq_ringKrullDim, hd] at hupper
  exact le_antisymm (by exact_mod_cast hupper) hlower

theorem localCohenMacaulay_of_isReduced_dim_le_one (hd : ringKrullDim R ≤ 1) :
    LocalCohenMacaulay R R := by
  apply (localCohenMacaulay_self_iff R).mpr
  by_cases hz : ringKrullDim R = 0
  · have hu := Depth.depth_le_supportDim (R := R) R
    rw [Depth.depth_eq_libraryDepth (ModuleCat.of R R),
      Module.supportDim_self_eq_ringKrullDim, hz] at hu
    rw [hz]
    exact le_antisymm hu (by exact_mod_cast (zero_le : (0 : ℕ∞) ≤ IsLocalRing.depth (ModuleCat.of R R)))
  · have hdim : ringKrullDim R = 1 := by
      have hn : ringKrullDim R ≠ ⊥ := ne_of_gt
        (lt_of_lt_of_le (WithBot.bot_lt_coe 0) ringKrullDim_nonneg_of_nontrivial)
      rw [← WithBot.coe_unbot _ hn] at hd hz ⊢
      apply WithBot.coe_inj.mpr
      exact le_antisymm (WithBot.coe_le_coe.mp hd)
        (Order.one_le_iff_ne_zero.mpr (by simpa only [WithBot.coe_eq_zero] using hz))
    rw [depth_eq_one_of_isReduced_dim_eq_one R hdim, hdim]
    rfl

end Local

/-- All prime localizations have dimension at most one and remain reduced. -/
theorem cohenMacaulayRing_of_isReduced_dim_le_one (hd : ringKrullDim R ≤ 1) :
    CohenMacaulayRing R := by
  intro p
  apply localCohenMacaulay_of_isReduced_dim_le_one
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal]
  exact p.asIdeal.height_le_ringKrullDim_of_isPrime.trans hd

/-- The one-dimensional reduced-ring assertion of CM-14. -/
theorem cohenMacaulayRing_of_isReduced_dim_eq_one (hd : ringKrullDim R = 1) :
    CohenMacaulayRing R :=
  cohenMacaulayRing_of_isReduced_dim_le_one R hd.le

end AdvCommAlg.CohenMacaulay
