import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.HomDetection
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace AdvCommAlg.Depth

open IsLocalRing TensorProduct

/-- A nonzero finite module over a local ring maps nontrivially to its residue field. -/
lemma exists_nonzero_map_residueField
    (R N : Type*) [CommRing R] [IsLocalRing R]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N] :
    ∃ f : N →ₗ[R] ResidueField R, f ≠ 0 := by
  let K := ResidueField R
  have hnt : Nontrivial (K ⊗[R] N) := by
    rw [← not_subsingleton_iff_nontrivial, IsLocalRing.subsingleton_tensorProduct]
    exact not_subsingleton N
  let := hnt
  obtain ⟨x, hx⟩ := exists_ne (0 : K ⊗[R] N)
  obtain ⟨d, hd⟩ := Module.Projective.exists_dual_ne_zero K hx
  let t : N →ₗ[R] K ⊗[R] N := TensorProduct.mk R K N 1
  have ht : Function.Surjective t :=
    TensorProduct.mk_surjective R N K Ideal.Quotient.mk_surjective
  refine ⟨(d.restrictScalars R).comp t, ?_⟩
  intro hz
  obtain ⟨n, hn⟩ := ht x
  apply hd
  have := LinearMap.congr_fun hz n
  simpa [hn] using this

/-- If the maximal ideal is associated to the target, every nonzero finite
source admits a nonzero map into that target. -/
lemma exists_nonzero_map_of_maximal_associated
    (R N M : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N]
    [AddCommGroup M] [Module R M]
    (hM : maximalIdeal R ∈ associatedPrimes R M) :
    ∃ f : N →ₗ[R] M, f ≠ 0 := by
  obtain ⟨d, hd⟩ := exists_nonzero_map_residueField R N
  obtain ⟨_, i, hi⟩ :=
    (isAssociatedPrime_iff_exists_injective_linearMap (maximalIdeal R) M).mp hM
  refine ⟨i.comp d, ?_⟩
  intro h
  apply hd
  ext n
  apply hi
  have hn : i (d n) = 0 := LinearMap.congr_fun h n
  exact hn.trans (map_zero i).symm

/-- Hom detects the intersection of the support of its source with the
associated primes of its target (DP-03, Hom-detection assertion). -/
theorem hom_detection : Specs.AdvCommAlg.Depth.HomDetection := by
  intro R _ _ N _ _ _ M _ _ _
  constructor
  · rintro ⟨f, hf⟩
    have : Nontrivial (LinearMap.range f) :=
      Submodule.nontrivial_iff_ne_bot.mpr (fun h => hf (LinearMap.range_eq_bot.mp h))
    obtain ⟨p, hp⟩ := associatedPrimes.nonempty R (LinearMap.range f)
    have hpM : p ∈ associatedPrimes R M :=
      hp.map_of_injective (LinearMap.range f).subtype Subtype.val_injective
    refine ⟨⟨p, hp.isPrime⟩, ?_, hpM⟩
    obtain ⟨_, y, hy⟩ := isAssociatedPrime_iff.mp hp
    obtain ⟨n, hn⟩ := y.property
    apply Module.mem_support_iff_exists_annihilator.mpr
    refine ⟨n, ?_⟩
    intro r hr
    change r ∈ p
    rw [hy, Submodule.mem_colon_singleton, Submodule.mem_bot]
    apply Subtype.ext
    change r • (y : M) = 0
    rw [← hn, ← f.map_smul, (Submodule.mem_annihilator_span_singleton n r).mp hr, f.map_zero]
  · rintro ⟨p, hpN, hpM⟩
    let Rₚ := Localization.AtPrime p.asIdeal
    let Nₚ := LocalizedModule p.asIdeal.primeCompl N
    let Mₚ := LocalizedModule p.asIdeal.primeCompl M
    have : Nontrivial Nₚ := Module.mem_support_iff.mp hpN
    have hM : maximalIdeal Rₚ ∈ associatedPrimes Rₚ Mₚ :=
      Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes hpM
    obtain ⟨h, hh⟩ := exists_nonzero_map_of_maximal_associated Rₚ Nₚ Mₚ hM
    let := Module.finitePresentation_of_finite R N
    let e := Module.FinitePresentation.linearEquivMapExtendScalars
      (M := N) (N := M) p.asIdeal.primeCompl
    have : Nontrivial (Nₚ →ₗ[Rₚ] Mₚ) := nontrivial_of_ne h 0 hh
    have hl : Nontrivial (LocalizedModule p.asIdeal.primeCompl (N →ₗ[R] M)) :=
      e.nontrivial
    have : Nontrivial (N →ₗ[R] M) := by
      by_contra hn
      have : Subsingleton (N →ₗ[R] M) := not_nontrivial_iff_subsingleton.mp hn
      have : Subsingleton (LocalizedModule p.asIdeal.primeCompl (N →ₗ[R] M)) := inferInstance
      exact not_subsingleton _ this
    exact exists_ne 0

end AdvCommAlg.Depth
