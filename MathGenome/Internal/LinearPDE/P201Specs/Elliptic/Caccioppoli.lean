import MathGenome.Internal.LinearPDE.P201Specs.Common.SpatialInterfaces

/-! Independent formulation of paper.tex, Proposition `pde:elliptic-caccioppoli`.
The weak gradient is an ambient representative, identified locally with the
canonical Hilbert Sobolev gradient. No global H¹ or boundary regularity is used. -/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
namespace P201Specs.Caccioppoli

/-- Local H¹, represented by its scalar value and weak gradient: on every
relatively compact open subdomain both are represented by the shared H¹ space.
Values outside Ω are immaterial, as are changes on null sets inside Ω. -/
def IsLocalH1 {n : ℕ} (Ω : Domain n) (u : Space n → ℝ)
    (g : Space n → Space n) : Prop :=
  ∀ V : Domain n, IsCompact (closure (V : Set (Space n))) →
    closure (V : Set (Space n)) ⊆ Ω →
    ∃ w : H ℝ V 1,
      (hUnderlying V 1 w : Space n → ℝ) =ᵐ[domainMeasure V] u ∧
      (hGradient w : Space n → Space n) =ᵐ[domainMeasure V] g

/-- Local L² without any assumption on the total measure of Ω. -/
def IsLocalL2 {n : ℕ} (Ω : Domain n) (f : Space n → ℝ) : Prop :=
  ∀ V : Domain n, IsCompact (closure (V : Set (Space n))) →
    closure (V : Set (Space n)) ⊆ Ω → MemLp f 2 (domainMeasure V)

/-- A local operator-norm bound and real ellipticity. Symmetry is not required.
Only a neighborhood of the compact test support is constrained. The bounds
hold almost everywhere, as stipulated for measurable coefficients in the
elliptic chapter conventions (paper.tex:1214–1224). -/
def LocalBounds {n : ℕ} (Ω : Domain n)
    (A : Space n → Space n →L[ℝ] Space n) (η : Test ℝ Ω)
    (M lam : ℝ) : Prop :=
  ∃ V : Domain n, tsupport η ⊆ V ∧
    ∀ᵐ x ∂domainMeasure V, ‖A x‖ ≤ M ∧ ∀ ξ : Space n, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ

/-- Compact support and approximation make η²u an admissible Sobolev test.
The approximation converges in the full H¹ norm on the original Ω. -/
def CutoffAdmissibilityStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ (Ω : Domain n) (u : Space n → ℝ)
    (g : Space n → Space n), IsLocalH1 Ω u g → ∀ η : Test ℝ Ω,
    ∃ v : H10 ℝ Ω,
      (hZeroUnderlying Ω v : Space n → ℝ) =ᵐ[domainMeasure Ω]
        (fun x => η x ^ 2 * u x) ∧
      (hGradient v.val : Space n → Space n) =ᵐ[domainMeasure Ω]
        (fun x => (η x ^ 2) • g x + (2 * η x * u x) • gradient η x) ∧
      ∃ (φ : ℕ → Test ℝ Ω) (w : ℕ → H ℝ Ω 1),
        (∀ k, hUnderlying Ω 1 (w k) = P102.U4.testToDomainLp Ω 2 (φ k)) ∧
        Tendsto w atTop (𝓝 v.val)

/-- The exact energy estimate, with an explicit admissible constant.
The equation uses all compact smooth interior tests and the shared positive
weak sign. Its locally integrable flux is part of the meaning of weak solution. -/
def CaccioppoliStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ (Ω : Domain n)
    (A : Space n → Space n →L[ℝ] Space n) (u f : Space n → ℝ)
    (g : Space n → Space n),
    IsLocalH1 Ω u g → IsLocalL2 Ω f →
    IsDistributionalEllipticSolution Ω (fun x => A x (g x)) f →
    ∀ (η : Test ℝ Ω) (M lam : ℝ), 0 ≤ M → 0 < lam → LocalBounds Ω A η M lam →
      (∫ x in Ω, η x ^ 2 * ‖g x‖ ^ 2) ≤
        (4 * M ^ 2 / lam ^ 2) * (∫ x in Ω, ‖gradient η x‖ ^ 2 * |u x| ^ 2) +
          (2 / lam) * (∫ x in Ω, |η x ^ 2 * f x * u x|)

end P201Specs.Caccioppoli
