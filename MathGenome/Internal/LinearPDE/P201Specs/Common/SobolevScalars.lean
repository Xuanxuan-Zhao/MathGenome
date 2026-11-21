import MathGenome.Internal.LinearPDE.P201Specs.Common.SpatialInterfaces

/-! Real scalar transport on the actual closed weak-derivative graphs. -/
noncomputable section
open MeasureTheory
namespace P201Specs.SobolevScalars

/-- A family of constructed maps, with its equations on the existing spaces.
The zero-boundary spaces here are the full-H¹ closures from SpatialInterfaces. -/
structure ScalarTransport {n : ℕ} (Ω : Domain n) (K : Type) [RCLike K] where
  reMap : (k : ℕ) → H K Ω k →L[ℝ] H ℝ Ω k
  imMap : (k : ℕ) → H K Ω k →L[ℝ] H ℝ Ω k
  ofRealMap : (k : ℕ) → H ℝ Ω k →L[ℝ] H K Ω k
  re_coordinate : ∀ k u α,
    P102.U4.sobolevDerivative (hToW ℝ Ω k (reMap k u)) α =
      (RCLike.reCLM : K →L[ℝ] ℝ).compLp
        (P102.U4.sobolevDerivative (hToW K Ω k u) α)
  im_coordinate : ∀ k u α,
    P102.U4.sobolevDerivative (hToW ℝ Ω k (imMap k u)) α =
      (RCLike.imCLM : K →L[ℝ] ℝ).compLp
        (P102.U4.sobolevDerivative (hToW K Ω k u) α)
  ofReal_coordinate : ∀ k u α,
    P102.U4.sobolevDerivative (hToW K Ω k (ofRealMap k u)) α =
      (RCLike.ofRealCLM : ℝ →L[ℝ] K).compLp
        (P102.U4.sobolevDerivative (hToW ℝ Ω k u) α)
  re_underlying : ∀ k u, ∀ᵐ x ∂domainMeasure Ω,
    hUnderlying Ω k (reMap k u) x = RCLike.re (hUnderlying Ω k u x)
  im_underlying : ∀ k u, ∀ᵐ x ∂domainMeasure Ω,
    hUnderlying Ω k (imMap k u) x = RCLike.im (hUnderlying Ω k u x)
  ofReal_underlying : ∀ k u, ∀ᵐ x ∂domainMeasure Ω,
    hUnderlying Ω k (ofRealMap k u) x = (hUnderlying Ω k u x : K)
  reconstruction : ∀ k u, u = ofRealMap k (reMap k u) +
    (RCLike.I : K) • ofRealMap k (imMap k u)
  reZero : H10 K Ω →L[ℝ] H10 ℝ Ω
  imZero : H10 K Ω →L[ℝ] H10 ℝ Ω
  ofRealZero : H10 ℝ Ω →L[ℝ] H10 K Ω
  reZero_inclusion : ∀ u, (reZero u).val = reMap 1 u.val
  imZero_inclusion : ∀ u, (imZero u).val = imMap 1 u.val
  ofRealZero_inclusion : ∀ u, (ofRealZero u).val = ofRealMap 1 u.val
  harmonic_synthesis : ∀ a b : H ℝ Ω 1,
    (∀ v : H10 ℝ Ω, ellipticEnergyForm Ω (fun _ => 1) a v.val = 0) →
    (∀ v : H10 ℝ Ω, ellipticEnergyForm Ω (fun _ => 1) b v.val = 0) →
    ∀ v : H10 K Ω, ellipticEnergyForm Ω (fun _ => 1)
      (ofRealMap 1 a + (RCLike.I : K) • ofRealMap 1 b) v.val = 0
  harmonic_detection : ∀ u : H K Ω 1,
    (∀ v : H10 K Ω, ellipticEnergyForm Ω (fun _ => 1) u v.val = 0) →
    (∀ v : H10 ℝ Ω, ellipticEnergyForm Ω (fun _ => 1) (reMap 1 u) v.val = 0) ∧
    (∀ v : H10 ℝ Ω, ellipticEnergyForm Ω (fun _ => 1) (imMap 1 u) v.val = 0)

/-- No geometric, dimensional, or compatibility certificate is assumed. -/
def ScalarTransportStatement : Prop :=
  ∀ {n : ℕ} (Ω : Domain n) (K : Type) [RCLike K], Nonempty (ScalarTransport Ω K)

end P201Specs.SobolevScalars
