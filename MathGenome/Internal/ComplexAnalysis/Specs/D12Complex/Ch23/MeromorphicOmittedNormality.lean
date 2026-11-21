import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.SphericalCompleteness
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch10.TriplesCrossRatio

/-!
The normal-family assertion of paper.tex:4320–4337, d12:23-06.
The omitted values are fixed for the entire sequence and may include infinity.
Meromorphy, sphere maps and compact chordal convergence are the canonical
upstream objects. Values of total representatives outside Ω are unrestricted.
Finite sphere constants are scalar meromorphic; the separate infinity
alternative retains the source's exclusion of identically infinite scalar maps.
-/
noncomputable section
open Set Filter
open scoped Topology

namespace Specs.D12Complex.Ch23.MeromorphicOmittedNormality
open _root_.D12Complex _root_.D12Complex.Mobius
open _root_.D12Complex.SphericalLimits

/-- One fixed biholomorphic normalizer, with its specified inverse. -/
def normalizing_biholomorphism_type : Prop :=
  ∀ a b c : RiemannSphere, a ≠ b → a ≠ c → b ≠ c →
    let M := normalizedCoefficients a b c
    Regular M ∧
      SphereBiholomorphicPair (mobiusMap M) (mobiusMap (inverseCoefficients M)) ∧
      mobiusMap M a = sphereFinite 0 ∧
      mobiusMap M b = sphereFinite 1 ∧ mobiusMap M c = sphereInfty

/-- The normalized map has no poles and is an actual scalar holomorphic
function omitting zero and one, including at original poles of F. -/
def normalized_holomorphic_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere) (a b c : RiemannSphere),
    IsDomain Ω → a ≠ b → a ≠ c → b ≠ c → ScalarMeromorphicOn Ω F →
    (∀ z ∈ Ω, F z ≠ a) → (∀ z ∈ Ω, F z ≠ b) → (∀ z ∈ Ω, F z ≠ c) →
    let T := mobiusMap (normalizedCoefficients a b c)
    let g := scalarFinitePart (T ∘ F)
    HolomorphicOn Ω g ∧ EqOn (T ∘ F) (fun z => sphereFinite (g z)) Ω ∧
      (∀ z ∈ Ω, g z ≠ 0) ∧ (∀ z ∈ Ω, g z ≠ 1)

/-- Compactness of the sphere makes every continuous postcomposition preserve
uniform chordal convergence on compact subsets of the source. -/
def continuous_comp_spherical_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℕ → ℂ → RiemannSphere) (F : ℂ → RiemannSphere)
    (T : RiemannSphere → RiemannSphere),
    Continuous T → SphericalLocallyUniformOn f F Ω →
    SphericalLocallyUniformOn (fun n z => T (f n z)) (fun z => T (F z)) Ω

/-- The original sequential conclusion, with all scalar pole conditions and
the possible constant infinity limit. -/
def subsequence_type : Prop :=
  ∀ (Ω : Set ℂ) (a b c : RiemannSphere), IsDomain Ω →
    a ≠ b → a ≠ c → b ≠ c → ∀ f : ℕ → ℂ → RiemannSphere,
    (∀ n, ScalarMeromorphicOn Ω (f n)) →
    (∀ n, ∀ z ∈ Ω, f n z ≠ a) → (∀ n, ∀ z ∈ Ω, f n z ≠ b) →
    (∀ n, ∀ z ∈ Ω, f n z ≠ c) →
    ∃ (φ : ℕ → ℕ) (F : ℂ → RiemannSphere), StrictMono φ ∧
      (ScalarMeromorphicOn Ω F ∨ EqOn F (fun _ => sphereInfty) Ω) ∧
      SphericalLocallyUniformOn (f ∘ φ) F Ω

/-- The full meromorphic family omitting the same three values is normal. -/
def spherically_normal_type : Prop :=
  ∀ (Ω : Set ℂ) (a b c : RiemannSphere), IsDomain Ω → a ≠ b → a ≠ c → b ≠ c →
    SphericalCompleteness.SphericallyNormal Ω
      {F | ScalarMeromorphicOn Ω F ∧ (∀ z ∈ Ω, F z ≠ a) ∧
        (∀ z ∈ Ω, F z ≠ b) ∧ (∀ z ∈ Ω, F z ≠ c)}

end Specs.D12Complex.Ch23.MeromorphicOmittedNormality
