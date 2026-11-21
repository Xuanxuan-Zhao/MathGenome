import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.Flow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
Independent statements for paper.tex, thm:pde-transport-flow, 3643–3684.
The derivative in the PDE is the total real differential evaluated at
`(1,b)`, i.e. `u_t + b · ∇u`. A within differential is used at slab endpoints.
On a zero-length slab its normal component is unconstrained, as it should be.
No time differentiability or boundedness is imposed on the lower order data.
-/
noncomputable section
open Set
open scoped ContDiff
namespace P201Specs.Hyperbolic

/-- Continuity and continuous first spatial derivatives on the actual domain.
The slices are unrestricted in space for a slab, and open for a local field. -/
structure SpatialC1 {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (D : Set (ℝ × Space n)) (h : ℝ × Space n → 𝕜) : Prop where
  continuous : ContinuousOn h D
  spatial : ∃ dh : ℝ × Space n → Space n →L[ℝ] 𝕜,
    ContinuousOn dh D ∧ ∀ p ∈ D,
      HasFDerivWithinAt (fun y => h (p.1, y)) (dh p) {y | (p.1, y) ∈ D} p.2

/-- Classical C¹ PDE, using the directional total differential. On an open
set or a positive-length slab this is precisely the usual pointwise PDE.
The existential differential also covers the degenerate slab without choosing
an artificial value of `fderivWithin` in its normal direction. -/
def IsTransportSolutionOn {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (D : Set (ℝ × Space n)) (b : ℝ × Space n → Space n)
    (q f u : ℝ × Space n → 𝕜) : Prop :=
  ContDiffOn ℝ 1 u D ∧ ∀ p ∈ D,
    ∃ du : (ℝ × Space n) →L[ℝ] 𝕜,
      HasFDerivWithinAt u du D p ∧ du (1, b p) + q p * u p = f p

def IsTransportIVPOn {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (D : Set (ℝ × Space n)) (A : Set (Space n))
    (b : ℝ × Space n → Space n) (q f : ℝ × Space n → 𝕜)
    (g : Space n → 𝕜) (u : ℝ × Space n → 𝕜) : Prop :=
  IsTransportSolutionOn D b q f u ∧ ∀ y ∈ A, u (0, y) = g y

/-- Exactly the two-term formula in the source, with oriented integrals. -/
def transportFormula {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (X : ℝ → ℝ → Space n → Space n)
    (q f : ℝ × Space n → 𝕜) (g : Space n → 𝕜) (p : ℝ × Space n) : 𝕜 :=
  NormedSpace.exp (-(∫ r in (0 : ℝ)..p.1, q (r, X r p.1 p.2))) * g (X 0 p.1 p.2) +
    ∫ s in (0 : ℝ)..p.1,
      NormedSpace.exp (-(∫ r in s..p.1, q (r, X r p.1 p.2))) * f (s, X s p.1 p.2)

def homogeneousFormula {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (X : ℝ → ℝ → Space n → Space n) (g : Space n → 𝕜)
    (p : ℝ × Space n) : 𝕜 := g (X 0 p.1 p.2)

/-- Only points whose actual characteristic reaches time zero and the
initial-data set are admitted. No extension or rectangular replacement. -/
def transportDomain {n : ℕ} (b : LocalField n) (A : Set (Space n)) :
    Set (ℝ × Space n) :=
  {p | (0, p.1, p.2) ∈ localFlowDomain b ∧ localFlow b 0 p.1 p.2 ∈ A}

def SlabTransportProperties {n : ℕ} {T : ℝ} (b : SlabField n T)
    (X : ℝ → ℝ → Space n → Space n) : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (g : Space n → 𝕜), ContDiff ℝ 1 g →
    (IsTransportIVPOn (Icc 0 T ×ˢ univ) univ b.velocity (fun _ => 0) (fun _ => 0) g
        (homogeneousFormula X g) ∧
      ∀ u, IsTransportIVPOn (Icc 0 T ×ˢ univ) univ b.velocity
        (fun _ => 0) (fun _ => 0) g u →
        EqOn u (homogeneousFormula X g) (Icc 0 T ×ˢ univ)) ∧
    ∀ q f : ℝ × Space n → 𝕜,
      SpatialC1 (Icc 0 T ×ˢ univ) q → SpatialC1 (Icc 0 T ×ˢ univ) f →
      IsTransportIVPOn (Icc 0 T ×ˢ univ) univ b.velocity q f g
        (transportFormula X q f g) ∧
      ∀ u, IsTransportIVPOn (Icc 0 T ×ˢ univ) univ b.velocity q f g u →
        EqOn u (transportFormula X q f g) (Icc 0 T ×ˢ univ)

def LocalTransportProperties {n : ℕ} (b : LocalField n) : Prop :=
  ∀ (A : Set (Space n)), IsOpen A → (∀ y ∈ A, (0, y) ∈ b.domain) →
    ∀ (𝕜 : Type) [RCLike 𝕜] (g : Space n → 𝕜), ContDiffOn ℝ 1 g A →
      (IsTransportIVPOn (transportDomain b A) A b.velocity
          (fun _ => 0) (fun _ => 0) g (homogeneousFormula (localFlow b) g) ∧
        ∀ u, IsTransportIVPOn (transportDomain b A) A b.velocity
          (fun _ => 0) (fun _ => 0) g u →
          EqOn u (homogeneousFormula (localFlow b) g) (transportDomain b A)) ∧
      ∀ q f : ℝ × Space n → 𝕜,
        SpatialC1 b.domain q → SpatialC1 b.domain f →
        IsTransportIVPOn (transportDomain b A) A b.velocity q f g
          (transportFormula (localFlow b) q f g) ∧
        ∀ u, IsTransportIVPOn (transportDomain b A) A b.velocity q f g u →
          EqOn u (transportFormula (localFlow b) q f g) (transportDomain b A)

/-- Full source theorem, including the upstream flow/diffeomorphism assertions. -/
def transportFlowStatement : Prop :=
  (∀ n, 1 ≤ n → ∀ T : ℝ, 0 ≤ T → ∀ b : SlabField n T,
    ∃ X, SlabFlowProperties b X ∧ SlabTransportProperties b X) ∧
  (∀ n, 1 ≤ n → ∀ b : LocalField n, LocalFlowProperties b ∧ LocalTransportProperties b)

/-- Necessity of the formula among arbitrary classical solutions, with merely
continuous lower order coefficients. This is one part of the full theorem. -/
def slabRepresentationStatement : Prop :=
  ∀ n, 1 ≤ n → ∀ T : ℝ, 0 ≤ T → ∀ (b : SlabField n T) X,
    SlabFlowProperties b X → ∀ (𝕜 : Type) [RCLike 𝕜]
      (q f : ℝ × Space n → 𝕜) (g : Space n → 𝕜),
      ContinuousOn q (Icc 0 T ×ˢ univ) → ContinuousOn f (Icc 0 T ×ˢ univ) →
      ∀ u, IsTransportIVPOn (Icc 0 T ×ˢ univ) univ b.velocity q f g u →
        EqOn u (transportFormula X q f g) (Icc 0 T ×ˢ univ)

/-- Spatial-parameter differentiation of the inhomogeneous formula on a slab.
This is a proof obligation, not a coefficient assumption of the source theorem. -/
def slabFormulaRegularityStatement : Prop :=
  ∀ n, 1 ≤ n → ∀ T : ℝ, 0 ≤ T → ∀ (b : SlabField n T) X,
    SlabFlowProperties b X → ∀ (𝕜 : Type) [RCLike 𝕜]
      (g : Space n → 𝕜), ContDiff ℝ 1 g → ∀ q f : ℝ × Space n → 𝕜,
      SpatialC1 (Icc 0 T ×ˢ univ) q → SpatialC1 (Icc 0 T ×ˢ univ) f →
      ContDiffOn ℝ 1 (transportFormula X q f g) (Icc 0 T ×ˢ univ)

/-- The same proof obligation on the actual open local flow domain. -/
def localFormulaRegularityStatement : Prop :=
  ∀ n, 1 ≤ n → ∀ b : LocalField n, LocalFlowProperties b →
    ∀ A : Set (Space n), IsOpen A → (∀ y ∈ A, (0, y) ∈ b.domain) →
    ∀ (𝕜 : Type) [RCLike 𝕜] (g : Space n → 𝕜), ContDiffOn ℝ 1 g A →
    ∀ q f : ℝ × Space n → 𝕜, SpatialC1 b.domain q → SpatialC1 b.domain f →
      ContDiffOn ℝ 1 (transportFormula (localFlow b) q f g) (transportDomain b A)

def regularityAssemblyStatement : Prop :=
  slabFormulaRegularityStatement → localFormulaRegularityStatement → transportFlowStatement

/-- The homogeneous part of the source, with its complete flow assertions. -/
def homogeneousTransportStatement : Prop :=
  (∀ n, 1 ≤ n → ∀ T : ℝ, 0 ≤ T → ∀ b : SlabField n T,
    ∃ X, SlabFlowProperties b X ∧
      ∀ (𝕜 : Type) [RCLike 𝕜] (g : Space n → 𝕜), ContDiff ℝ 1 g →
        IsTransportIVPOn (Icc 0 T ×ˢ univ) univ b.velocity (fun _ => 0) (fun _ => 0) g
          (homogeneousFormula X g) ∧
        ∀ u, IsTransportIVPOn (Icc 0 T ×ˢ univ) univ b.velocity
          (fun _ => 0) (fun _ => 0) g u →
          EqOn u (homogeneousFormula X g) (Icc 0 T ×ˢ univ)) ∧
  (∀ n, 1 ≤ n → ∀ b : LocalField n, LocalFlowProperties b ∧
    ∀ A : Set (Space n), IsOpen A → (∀ y ∈ A, (0, y) ∈ b.domain) →
      ∀ (𝕜 : Type) [RCLike 𝕜] (g : Space n → 𝕜), ContDiffOn ℝ 1 g A →
        IsTransportIVPOn (transportDomain b A) A b.velocity
          (fun _ => 0) (fun _ => 0) g (homogeneousFormula (localFlow b) g) ∧
        ∀ u, IsTransportIVPOn (transportDomain b A) A b.velocity
          (fun _ => 0) (fun _ => 0) g u →
          EqOn u (homogeneousFormula (localFlow b) g) (transportDomain b A))

def localRepresentationStatement : Prop :=
  ∀ n, 1 ≤ n → ∀ b : LocalField n, LocalFlowProperties b →
    ∀ (𝕜 : Type) [RCLike 𝕜] (A : Set (Space n))
      (q f : ℝ × Space n → 𝕜) (g : Space n → 𝕜),
      ContinuousOn q b.domain → ContinuousOn f b.domain →
      ∀ u, IsTransportIVPOn (transportDomain b A) A b.velocity q f g u →
        EqOn u (transportFormula (localFlow b) q f g) (transportDomain b A)

end P201Specs.Hyperbolic
