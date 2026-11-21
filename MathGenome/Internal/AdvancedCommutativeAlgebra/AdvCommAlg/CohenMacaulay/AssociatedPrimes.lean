import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.AssociatedPrimeBound
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.AssociatedPrimes
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! CM-03: associated primes and equidimension.
The associated-prime depth bound gives the dimension equality. A prime strictly
below an associated prime in the support would have strictly larger coheight,
contradicting that equality. Finiteness of dimension follows from the Noetherian
local hypotheses, rather than being an additional assumption. -/

universe u
namespace AdvCommAlg.CohenMacaulay

variable {R : Type u} [CommRing R]
    {M : Type u} [AddCommGroup M] [Module R M]

/-- Every chain above a support prime remains in the support. -/
lemma coheight_le_dimension_of_mem_support (p : PrimeSpectrum R)
    (hp : p ∈ Module.support R M) :
    (Order.coheight p : WithBot ℕ∞) ≤ dimension R M := by
  rw [Order.coheight_eq_krullDim_Ici]
  exact Order.krullDim_le_of_strictMono
    (fun q : Set.Ici p => (⟨q.1, Module.mem_support_mono q.2 hp⟩ : Module.support R M))
    (fun _ _ h => h)

/-- Quotient dimension is the coheight of the corresponding prime. -/
lemma dim_quotient_eq_coheight (p : PrimeSpectrum R) :
    ringKrullDim (R ⧸ p.asIdeal) = (Order.coheight p : WithBot ℕ∞) := by
  rw [Order.coheight_eq_krullDim_Ici, ringKrullDim_quotient]
  rfl

variable [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M] [Nontrivial M]

theorem dim_quotient_eq_dimension_of_associatedPrime
    (hCM : LocalCohenMacaulay R M) (p : Ideal R) (hp : p ∈ associatedPrimes R M) :
    ringKrullDim (R ⧸ p) = dimension R M := by
  have hs : (⟨p, hp.isPrime⟩ : PrimeSpectrum R) ∈ Module.support R M := by
    apply Module.mem_support_iff_of_finite.mpr
    exact Submodule.annihilator_top.symm.le.trans hp.annihilator_le
  apply le_antisymm
  · rw [dim_quotient_eq_coheight (⟨p, hp.isPrime⟩ : PrimeSpectrum R)]
    exact coheight_le_dimension_of_mem_support _ hs
  · rw [← (localCohenMacaulay_iff_sourceDepth R M).mp hCM]
    exact Depth.depth_le_dim_quotient_of_associatedPrime R M p hp

theorem minimal_support_of_associatedPrime
    (hCM : LocalCohenMacaulay R M) (p : PrimeSpectrum R)
    (hp : p.asIdeal ∈ associatedPrimes R M) :
    Minimal (fun q => q ∈ Module.support R M) p := by
  have hs : p ∈ Module.support R M := by
    apply Module.mem_support_iff_of_finite.mpr
    exact Submodule.annihilator_top.symm.le.trans hp.annihilator_le
  refine ⟨hs, fun q hq hqp => ?_⟩
  by_contra hn
  have hlt : q < p := lt_of_le_not_ge hqp hn
  have hch : Order.coheight p < Order.coheight q :=
    Order.coheight_strictAnti hlt (Order.coheight_lt_top p)
  have hd := dim_quotient_eq_dimension_of_associatedPrime hCM p.asIdeal hp
  rw [dim_quotient_eq_coheight p] at hd
  have hbound := coheight_le_dimension_of_mem_support q hq
  rw [← hd] at hbound
  exact (not_lt_of_ge (WithBot.coe_le_coe.mp hbound)) hch

/-- Minimal support primes are associated for finite modules over Noetherian
rings; this direction does not need the Cohen–Macaulay hypothesis. -/
theorem associatedPrime_of_minimal_support (p : PrimeSpectrum R)
    (hp : Minimal (fun q => q ∈ Module.support R M) p) :
    p.asIdeal ∈ associatedPrimes R M := by
  apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M
  refine ⟨⟨p.isPrime, Module.mem_support_iff_of_finite.mp hp.prop⟩, ?_⟩
  intro q hq hqp
  exact hp.le_of_le (y := ⟨q, hq.1⟩)
    (Module.mem_support_iff_of_finite.mpr hq.2) hqp

theorem associatedPrimes_eq_minimalPrimes_annihilator
    (hCM : LocalCohenMacaulay R M) :
    associatedPrimes R M = (Module.annihilator R M).minimalPrimes := by
  apply Set.Subset.antisymm
  · intro p hp
    have hs := minimal_support_of_associatedPrime hCM ⟨p, hp.isPrime⟩ hp
    refine ⟨⟨hp.isPrime, Module.mem_support_iff_of_finite.mp hs.prop⟩, ?_⟩
    intro q hq hqp
    exact hs.le_of_le (y := ⟨q, hq.1⟩)
      (Module.mem_support_iff_of_finite.mpr hq.2) hqp
  · exact Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M

/-- All irreducible components of the support have the common dimension d_R(M). -/
theorem dim_quotient_eq_dimension_of_minimal_support
    (hCM : LocalCohenMacaulay R M) (p : PrimeSpectrum R)
    (hp : Minimal (fun q => q ∈ Module.support R M) p) :
    ringKrullDim (R ⧸ p.asIdeal) = dimension R M :=
  dim_quotient_eq_dimension_of_associatedPrime hCM p.asIdeal
    (associatedPrime_of_minimal_support p hp)

end AdvCommAlg.CohenMacaulay
