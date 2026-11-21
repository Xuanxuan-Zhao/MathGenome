import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.InvertibleMinor
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Localization
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.RelativeRank
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! The local relative-rank assertion of SM-09. -/
namespace AdvCommAlg.Smooth

universe u v
noncomputable section
open Specs.AdvCommAlg.Smooth
open Specs.AdvCommAlg.Smooth.RelativeRank
open scoped TensorProduct

/-- Relative rank is the dimension of the cotangent fiber. -/
abbrev relativeRank : relativeRankType.{u,v} := relativeRankValue

/-- Smooth cotangent fibers are finite-dimensional. -/
theorem finite_cotangent_fiber : finiteFiber.{u,v} := by
  intro A B _ _ _ hs q
  let : Algebra.Smooth A B := hs
  infer_instance

/-- The residue-fiber definition agrees with rank at a stalk. -/
theorem relativeRank_eq_rankAtStalk (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (hs : smoothValue A B)
    (q : PrimeSpectrum B) :
    relativeRank A B q = Module.rankAtStalk (KaehlerDifferential A B) q := by
  let : Algebra.Smooth A B := hs
  exact (Module.rankAtStalk_eq q).symm

/-- Finite projectivity of smooth differentials implies local constancy. -/
theorem relativeRank_locallyConstant : locallyConstantRank.{u,v} := by
  intro A B _ _ _ hs
  let : Algebra.Smooth A B := hs
  let : Module.FinitePresentation B (KaehlerDifferential A B) :=
    Module.finitePresentation_of_projective B (KaehlerDifferential A B)
  have h : relativeRankValue A B = Module.rankAtStalk (KaehlerDifferential A B) :=
    funext (relativeRank_eq_rankAtStalk A B hs)
  rw [h]
  exact Module.isLocallyConstant_rankAtStalk

/-- Localization of differentials transports rank at the corresponding primes. -/
theorem relativeRank_principal_chart : principalChartRank.{u,v} := by
  intro A B _ _ _ hs g n c P hP q
  let : Algebra.Smooth A B := hs
  obtain ⟨Q, _⟩ := (presentation_standard_smooth_iff_submersive P).mp hP
  have : Nontrivial (Localization.Away g) :=
    ⟨⟨0, 1, fun h => q.isPrime.one_notMem (h ▸ q.asIdeal.zero_mem)⟩⟩
  let : Algebra.Smooth A (Localization.Away g) := presentation_smooth P hP
  let : Module.Free (Localization.Away g)
      (KaehlerDifferential A (Localization.Away g)) := Q.free_kaehlerDifferential
  change relativeRank A B (q.comap (algebraMap B (Localization.Away g))) = n - c
  rw [relativeRank_eq_rankAtStalk A B hs]
  rw [← Module.rankAtStalk_isBaseChange
    (Differentials.differential_isBaseChange A B (Localization.Away g) (Submonoid.powers g)) q]
  rw [Module.rankAtStalk_eq_finrank_of_free]
  apply Module.finrank_eq_of_rank_eq
  simpa [Algebra.Presentation.dimension] using Q.rank_kaehlerDifferential

end
end AdvCommAlg.Smooth
