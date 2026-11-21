import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.NonlinearErgodicWeak

/-! Independent statements for the odd-map clause of
`paper.tex`, `fa2:p5:nonlinear-ergodic`, 22517–22560.
All maps act on the whole Hilbert space. The real inner product below is
the native restriction of scalars, with the original norm and topology. -/
noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace ExpandedFA.PartV.NonlinearErgodicOdd.Spec
universe u v

/-- The comparison applies to arbitrary odd nonexpansive maps, hence to
all iterates of T and its arithmetic average with the identity. -/
def OddMapComparison : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (R : H → H), NonlinearErgodicWeak.Spec.Nonexpansive R →
    (∀ x, R (-x) = -R x) →
    letI := ExpandedFA.Hilbert.Conventions.Spec.RealificationValue 𝕜 H
    ∀ x y : H,
      2 * |⟪x, y⟫_ℝ - ⟪R x, R y⟫_ℝ| ≤
        ‖x‖ ^ 2 + ‖y‖ ^ 2 - ‖R x‖ ^ 2 - ‖R y‖ ^ 2

/-- Uniformity in the orbit gap is essential: the same defect δ n works
for every i. This also supplies convergence of the orbit's squared norms. -/
def UniformOrbitComparison : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (R : H → H), NonlinearErgodicWeak.Spec.Nonexpansive R →
    (∀ x, R (-x) = -R x) → ∀ f : H,
    letI := ExpandedFA.Hilbert.Conventions.Spec.RealificationValue 𝕜 H
    ∃ (L : ℝ) (ell : ℕ → ℝ),
      Tendsto (fun n => ‖R^[n] f‖ ^ 2) atTop (𝓝 L) ∧
      Antitone (fun n => ‖R^[n] f‖ ^ 2) ∧
      (∀ n, 0 ≤ ‖R^[n] f‖ ^ 2 - L) ∧
      ∀ n i, |⟪R^[n] f, R^[n + i] f⟫_ℝ - ell i| ≤ ‖R^[n] f‖ ^ 2 - L

/-- Strong convergence of the averaged iterates. -/
def AveragedStrong : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H → H), NonlinearErgodicWeak.Spec.Nonexpansive T →
    (∃ p, T p = p) → (∀ x, T (-x) = -T x) → ∀ f : H,
    ∃ p, T p = p ∧
      NonlinearErgodicWeak.Spec.WeaklyConverges 𝕜
        (fun n => (NonlinearErgodicWeak.Spec.averaged 𝕜 T)^[n] f) p ∧
      Tendsto (fun n => ‖(NonlinearErgodicWeak.Spec.averaged 𝕜 T)^[n] f - p‖)
        atTop (𝓝 0)

/-- Strong convergence, with the fixed-point weak limits included explicitly. -/
def NonlinearErgodicOdd : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H → H), NonlinearErgodicWeak.Spec.Nonexpansive T →
    (∃ p, T p = p) → (∀ x, T (-x) = -T x) → ∀ f : H,
    (∃ p, T p = p ∧
      NonlinearErgodicWeak.Spec.WeaklyConverges 𝕜
        (fun n => (NonlinearErgodicWeak.Spec.averaged 𝕜 T)^[n] f) p ∧
      Tendsto (fun n => ‖(NonlinearErgodicWeak.Spec.averaged 𝕜 T)^[n] f - p‖)
        atTop (𝓝 0)) ∧
    (∃ q, T q = q ∧
      NonlinearErgodicWeak.Spec.WeaklyConverges 𝕜
        (NonlinearErgodicWeak.Spec.cesaro 𝕜 (fun j => T^[j] f)) q ∧
      Tendsto (fun n => ‖NonlinearErgodicWeak.Spec.cesaro 𝕜 (fun j => T^[j] f) n - q‖)
        atTop (𝓝 0))

/-- Norms converge to the norms of the already established weak limits.
The weak limits are arbitrary here, so the identification is explicit. -/
def NormConvergence : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H → H), NonlinearErgodicWeak.Spec.Nonexpansive T →
    (∃ p, T p = p) → (∀ x, T (-x) = -T x) → ∀ (f p q : H),
    NonlinearErgodicWeak.Spec.WeaklyConverges 𝕜
      (fun n => (NonlinearErgodicWeak.Spec.averaged 𝕜 T)^[n] f) p →
    NonlinearErgodicWeak.Spec.WeaklyConverges 𝕜
      (NonlinearErgodicWeak.Spec.cesaro 𝕜 (fun j => T^[j] f)) q →
    Tendsto (fun n => ‖(NonlinearErgodicWeak.Spec.averaged 𝕜 T)^[n] f‖)
      atTop (𝓝 ‖p‖) ∧
    Tendsto (fun n => ‖NonlinearErgodicWeak.Spec.cesaro 𝕜 (fun j => T^[j] f) n‖)
      atTop (𝓝 ‖q‖)

end ExpandedFA.PartV.NonlinearErgodicOdd.Spec
