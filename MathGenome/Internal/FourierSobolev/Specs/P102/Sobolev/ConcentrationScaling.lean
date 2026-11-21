import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.CriticalMorreyEmbeddings

/-! Independent statements for paper.tex:1929–1937, with the conventions at
paper.tex:47–61 and 1708–1712. The examples use ambient smooth representatives,
not pointwise values of arbitrary Lp representatives. Dimension is positive;
nonemptiness, but no boundary regularity or boundedness, is needed for the
common local construction, which applies in particular to every nonempty
bounded Lipschitz open set. Endpoint noncompactness is proved by other goals. -/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff ENNReal NNReal Topology
namespace P102.Sobolev.EndpointNoncompactness
open P102.U4

/-- The source family, with a general amplitude exponent. -/
def rescale {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : Space d → 𝕜) (x₀ : Space d) (a r : ℝ) (x : Space d) : 𝕜 :=
  r ^ a • φ (r⁻¹ • (x - x₀))

/-- One explicit sequence of scales strictly inside the available interior ball. -/
def scales (ρ : ℝ) (n : ℕ) : ℝ := ρ / (n + 2 : ℝ)

/-- Common concentration construction. These are obligations of an existential
witness below, not additional hypotheses on the domain. Normalizing the bump
at the origin does not restrict the source's choice of a nonzero bump. -/
structure ConcentrationFamily {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0) [Fact (1 ≤ (p : ℝ≥0∞))] where
  center : Space d
  center_mem : center ∈ Ω
  radius : ℝ
  radius_pos : 0 < radius
  ball_subset : Metric.ball center radius ⊆ Ω
  bump : Space d → 𝕜
  smooth : ContDiff ℝ (⊤ : ℕ∞) bump
  compact : HasCompactSupport bump
  support : tsupport bump ⊆ Metric.ball 0 1
  value_zero : bump 0 = 1
  U : ℝ → U4.Sobolev 𝕜 Ω 1 p
  representative : ∀ r, 0 < r → r < radius →
    IntegerEmbeddings.RepresentsOn (U r) (rescale bump center (1 - (d : ℝ) / p) r)
  derivative_representative : ∀ r, 0 < r → r < radius → ∀ i : Fin d,
    (sobolevDerivative (U r) (firstIndex i) : Space d → 𝕜) =ᵐ[
      volume.restrict (Ω : Set (Space d))]
      (fun x => fderiv ℝ (rescale bump center (1 - (d : ℝ) / p) r) x
        (coordinateVector d i))
  support_rescale : ∀ r, 0 < r → r < radius →
    tsupport (rescale bump center (1 - (d : ℝ) / p) r) ⊆ Ω
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  bounded_norm : ∀ r, 0 < r → r < radius → ‖U r‖ ≤ bound
  gradient_size : ℝ
  gradient_size_pos : 0 < gradient_size
  gradient_memLp : ∀ r, 0 < r → r < radius →
    MemLp (weakGradientOn (U r)) p (volume.restrict (Ω : Set (Space d)))
  gradient_fixed : ∀ r, 0 < r → r < radius →
    eLpNorm (weakGradientOn (U r)) p (volume.restrict (Ω : Set (Space d))) =
      ENNReal.ofReal gradient_size

namespace ScalingExpected

def Construction : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)),
    (Ω : Set (Space d)).Nonempty → ∀ (p : ℝ≥0), 1 ≤ p →
    ∀ [Fact (1 ≤ (p : ℝ≥0∞))], Nonempty (ConcentrationFamily 𝕜 Ω p)

def ScalarScaling : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (φ : Space d → 𝕜), Continuous φ →
    ∀ (x₀ : Space d) (a r : ℝ), 0 < r → ∀ (q : ℝ≥0∞),
    (eLpNorm (rescale φ x₀ a r) q volume).toReal =
      r ^ (a + (d : ℝ) / q.toReal) * (eLpNorm φ q volume).toReal

def DerivativeScaling : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {φ : Space d → 𝕜},
    ContDiff ℝ (⊤ : ℕ∞) φ → ∀ (x₀ : Space d) (a r : ℝ), 0 < r →
    ∀ (x z : Space d), fderiv ℝ (rescale φ x₀ a r) x z =
      r ^ (a - 1) • fderiv ℝ φ (r⁻¹ • (x - x₀)) z

def ScaleSequence : Prop :=
  ∀ ρ : ℝ, 0 < ρ → (∀ n, 0 < scales ρ n ∧ scales ρ n < ρ) ∧
    Tendsto (scales ρ) atTop (𝓝 0)

/-- On every small scale the ambient smooth representative has its actual
finite Lq norm, with the exact amplitude and Jacobian factors. -/
def FamilyScalarScaling : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (D : ConcentrationFamily 𝕜 Ω p),
    ∀ r : ℝ, 0 < r → r < D.radius → ∀ q : ℝ≥0∞,
      MemLp (rescale D.bump D.center (1 - (d : ℝ) / p) r) q
        (volume.restrict (Ω : Set (Space d))) ∧
      eLpNorm (rescale D.bump D.center (1 - (d : ℝ) / p) r) q
        (volume.restrict (Ω : Set (Space d))) =
        ENNReal.ofReal (r ^ (1 - (d : ℝ) / p + (d : ℝ) / q.toReal)) *
          eLpNorm D.bump q volume

end ScalingExpected
end P102.Sobolev.EndpointNoncompactness
