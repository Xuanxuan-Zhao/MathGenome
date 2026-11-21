import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.SphericalCompleteness

/-!
Montel–Carathéodory (paper.tex:4247–4277, d12:23-04).
The approximating functions are weakly holomorphic on the original plane domain
and omit precisely the two stated values. The finite limits have no omitted-value
condition. All convergence is on the original domain; representatives outside it
are unrestricted. The finite conclusion also supplies ordinary compact convergence.
-/
noncomputable section
open Set Filter
open scoped Topology

namespace Specs.D12Complex.Ch23.OmittedValueNormality
open _root_.D12Complex _root_.D12Complex.SphericalLimits

def bounded_center_subsequence_type : Prop :=
  ∀ (Ω : Set ℂ) (a : ℂ), IsDomain Ω → a ∈ Ω →
    ∀ F : ℕ → ℂ → ℂ, (∀ n, HolomorphicOn Ω (F n)) →
      (∀ n, ∀ z ∈ Ω, F n z ≠ 0) → (∀ n, ∀ z ∈ Ω, F n z ≠ 1) →
      (∀ n, ‖F n a‖ ≤ 1) →
      ∃ (φ : ℕ → ℕ) (h : ℂ → ℂ), StrictMono φ ∧ HolomorphicOn Ω h ∧
        TendstoLocallyUniformlyOn (fun n => F (φ n)) h atTop Ω

def frequently_bounded_center_subsequence_type : Prop :=
  ∀ (Ω : Set ℂ) (a : ℂ), IsDomain Ω → a ∈ Ω →
    ∀ F : ℕ → ℂ → ℂ, (∀ n, HolomorphicOn Ω (F n)) →
      (∀ n, ∀ z ∈ Ω, F n z ≠ 0) → (∀ n, ∀ z ∈ Ω, F n z ≠ 1) →
      (∃ᶠ n in atTop, ‖F n a‖ ≤ 1) →
      ∃ (φ : ℕ → ℕ) (h : ℂ → ℂ), StrictMono φ ∧ HolomorphicOn Ω h ∧
        TendstoLocallyUniformlyOn (fun n => F (φ n)) h atTop Ω

/-- Exact distance to infinity in the reciprocal coordinate, for nonzero values. -/
def chordal_infty_reciprocal_type : Prop :=
  ∀ z : ℂ, z ≠ 0 → Chordal.chordal sphereInfty (sphereFinite z) =
    ‖z⁻¹‖ / Real.sqrt (1 + ‖z⁻¹‖ ^ 2)

/-- The two reciprocal limits retain the zero limit and its infinity conclusion. -/
def reciprocal_limit_alternative_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℕ → ℂ → ℂ) (h : ℂ → ℂ), IsDomain Ω →
    (∀ n, HolomorphicOn Ω (F n)) → (∀ n, ∀ z ∈ Ω, F n z ≠ 0) →
    HolomorphicOn Ω h →
    TendstoLocallyUniformlyOn (fun n z => (F n z)⁻¹) h atTop Ω →
    ((∀ z ∈ Ω, h z ≠ 0) ∧ HolomorphicOn Ω (fun z => (h z)⁻¹) ∧
      TendstoLocallyUniformlyOn F (fun z => (h z)⁻¹) atTop Ω) ∨
    (EqOn h (fun _ => 0) Ω ∧
      SphericalLocallyUniformOn (fun n z => sphereFinite (F n z))
        (fun _ => sphereInfty) Ω)

/-- One strictly increasing subsequence; finite holomorphic or constant infinity. -/
def subsequence_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℕ → ℂ → ℂ), IsDomain Ω →
    (∀ n, HolomorphicOn Ω (F n)) →
    (∀ n, ∀ z ∈ Ω, F n z ≠ 0) → (∀ n, ∀ z ∈ Ω, F n z ≠ 1) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ h : ℂ → ℂ, HolomorphicOn Ω h ∧
        TendstoLocallyUniformlyOn (fun n => F (φ n)) h atTop Ω ∧
        SphericalLocallyUniformOn (fun n z => sphereFinite (F (φ n) z))
          (fun z => sphereFinite (h z)) Ω) ∨
       SphericalLocallyUniformOn (fun n z => sphereFinite (F (φ n) z))
         (fun _ => sphereInfty) Ω)

/-- Normality in the canonical sphere family, identifying representatives on Ω. -/
def spherically_normal_type : Prop :=
  ∀ (Ω : Set ℂ), IsDomain Ω →
    SphericalCompleteness.SphericallyNormal Ω
      {G | ∃ f : ℂ → ℂ, HolomorphicOn Ω f ∧
        (∀ z ∈ Ω, f z ≠ 0) ∧ (∀ z ∈ Ω, f z ≠ 1) ∧
        EqOn G (fun z => sphereFinite (f z)) Ω}

end Specs.D12Complex.Ch23.OmittedValueNormality
