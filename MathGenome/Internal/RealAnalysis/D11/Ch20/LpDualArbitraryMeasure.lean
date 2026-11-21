import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.LpDualArbitraryMeasure
import MathGenome.Internal.RealAnalysis.D11.Ch20.FunctionalVisibleSigmafiniteSupport

/-! Arbitrary-measure Lp duality for 1 < p < ∞.

The visible-support theorem supplies a measurable sigma-finite set F on
which the functional depends. Local duality and extension by zero give an
ambient Lq density for its cutoff. Visibility identifies that cutoff with
the original functional. The finite-q norm theorem then gives isometry
and ordinary a.e. uniqueness on the original measure space.
-/
open MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace D11.Ch20.LpDualArbitraryMeasure
open LpDualSigmafiniteLocal

variable {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]

/-- Surjectivity obtained by restricting only to a functional-visible set;
the original positive measure need not be sigma-finite or semifinite. -/
lemma pairing_surjective (μ : Measure X) (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp1 : 1 < p) (hp : p ≠ ∞) :
    Function.Surjective (IntegralPairing.pairing (𝕜 := 𝕜) μ p q) := by
  intro ℓ
  obtain ⟨F, hF, hσF, hvisible⟩ :=
    FunctionalVisibleSigmafiniteSupport.functional_visible_sigmafinite_support μ p hp1 hp ℓ
  letI : SigmaFinite (μ.restrict F) := hσF
  obtain ⟨g, hg, _⟩ :=
    FunctionalVisibleSigmafiniteSupport.sigmaFinite_piece_density μ p q hp ℓ F hF
  refine ⟨g, ?_⟩
  ext f
  obtain ⟨fF, hfF, hℓ⟩ := hvisible f
  have hcut : fF = cutoffLp μ p F hF f :=
    Lp.ext (hfF.trans (cutoffLp_coe μ p F hF f).symm)
  exact (hg f).trans (hℓ.trans (congrArg ℓ hcut)).symm

/-- Scalar linearity is part of the fixed pairing's continuous linear map
type. Here its isometry and bijectivity hold on arbitrary positive measures. -/
theorem lp_dual_arbitrary_measure :
    Specs.D11.Ch20.LpDualArbitraryMeasure.lp_dual_arbitrary_measure := by
  intro X 𝕜 _ _ μ p q _ _ _ hp1 hp
  have hq : q ≠ ∞ :=
    (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).mpr hp1.ne'
  obtain ⟨hi, hinj⟩ := PairingNormFiniteQ.isometric_injection (𝕜 := 𝕜) μ p q hq
  exact ⟨hi, hinj, pairing_surjective μ p q hp1 hp⟩

/-- The equivalent density formulation retains integrability, the integral
identity, the exact norm, and uniqueness in the ordinary a.e. quotient. -/
theorem representation : Specs.D11.Ch20.LpDualArbitraryMeasure.representation := by
  intro X 𝕜 _ _ μ p q _ _ _ hp1 hp ℓ
  obtain ⟨_, hinj, hsurj⟩ := lp_dual_arbitrary_measure (𝕜 := 𝕜) μ p q hp1 hp
  obtain ⟨g, hg⟩ := hsurj ℓ
  have hq : q ≠ ∞ :=
    (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).mpr hp1.ne'
  refine ⟨g, ⟨fun f => ⟨(IntegralPairing.pairing_eq_integral μ p q g f).1, ?_⟩,
    ?_⟩, ?_⟩
  · exact (congrArg (fun L : Lp 𝕜 p μ →L[𝕜] 𝕜 => L f) hg).symm.trans
      (IntegralPairing.pairing_eq_integral μ p q g f).2
  · exact (PairingNormFiniteQ.norm_pairing μ p q hq g).symm.trans (congrArg norm hg)
  · intro k hk
    apply hinj
    calc
      Specs.D11.Ch20.IntegralPairing.pairing_value μ p q k = ℓ := by
        ext f
        exact (IntegralPairing.pairing_eq_integral μ p q k f).2.trans ((hk.1 f).2.symm)
      _ = Specs.D11.Ch20.IntegralPairing.pairing_value μ p q g := hg.symm

end D11.Ch20.LpDualArbitraryMeasure
