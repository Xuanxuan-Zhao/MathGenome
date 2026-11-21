import MathGenome.Internal.FourierSobolev.Specs.P102.U4.RegularDerivatives
import Mathlib.Topology.Algebra.Group.ContinuousDiv

/-! Independent statements for the local-convolution part of
paper.tex:1339–1357. Tests are ambient zero extensions, and support means
topological support. No normalization, positivity, or whole-space assumption
is imposed. The zero extension of the *output* is only a representation;
all regularity and derivative assertions are on the full admissible set. -/

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ContDiff Distributions

namespace P102.U4

/-- The full set `{x | x - supp ρ ⊆ Ω}`. -/
def convolutionDomain {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) : Set (Space d) :=
  {x | ∀ z ∈ tsupport ρ, x - z ∈ Ω}

/-- A translated and reflected kernel, as a whole-space test. -/
def translatedKernel {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (x : Space d) :
    TestSpace 𝕜 (⊤ : Opens (Space d)) where
  toFun y := ρ (x - y)
  contDiff' := ρ.contDiff.comp (contDiff_const.sub contDiff_id)
  hasCompactSupport' := ρ.hasCompactSupport.comp_homeomorph (Homeomorph.subLeft x)
  tsupport_subset' := subset_univ _

/-- The admissibility condition supplies the support proof needed to pair with T. -/
def convolutionTest {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (x : Space d)
    (hx : x ∈ convolutionDomain Ω ρ) : TestSpace 𝕜 Ω where
  toFun := translatedKernel ρ x
  contDiff' := (translatedKernel ρ x).contDiff
  hasCompactSupport' := (translatedKernel ρ x).hasCompactSupport
  tsupport_subset' := by
    intro y hy
    have h : x - y ∈ tsupport ρ :=
      tsupport_comp_subset_preimage ρ (continuous_const.sub continuous_id) hy
    have hyΩ := hx (x - y) h
    change x - (x - y) ∈ (Ω : Set (Space d)) at hyΩ
    rwa [sub_sub_cancel] at hyΩ

/-- The scalar convolution, represented by zero outside its admissible domain. -/
def localConvolution {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (T : DistributionSpace 𝕜 Ω) (ρ : TestSpace 𝕜 (⊤ : Opens (Space d)))
    (x : Space d) : 𝕜 := by
  classical
  exact if hx : x ∈ convolutionDomain Ω ρ then T (convolutionTest ρ x hx) else 0

/-- The derivative kernel uses the same coordinate multi-index as the upstream interface. -/
def kernelPartial {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (α : MultiIndex d)
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) : TestSpace 𝕜 (⊤ : Opens (Space d)) :=
  testPartialWord ⊤ (α.sort (· ≤ ·)) ρ

namespace LocalConvolutionExpected

def DomainType := {d : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → Opens (Space d) →
  TestSpace 𝕜 (⊤ : Opens (Space d)) → Set (Space d)
def DomainValue : DomainType := @convolutionDomain

def TestType := {d : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → {Ω : Opens (Space d)} →
  (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) → (x : Space d) →
  x ∈ convolutionDomain Ω ρ → TestSpace 𝕜 Ω
def TestValue : TestType := @convolutionTest

def ConvolutionType := {d : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → {Ω : Opens (Space d)} →
  DistributionSpace 𝕜 Ω → TestSpace 𝕜 (⊤ : Opens (Space d)) → Space d → 𝕜
def ConvolutionValue : ConvolutionType := @localConvolution

def KernelPartialType := {d : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → MultiIndex d →
  TestSpace 𝕜 (⊤ : Opens (Space d)) → TestSpace 𝕜 (⊤ : Opens (Space d))
def KernelPartialValue : KernelPartialType := @kernelPartial

def OpenDomain : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))), IsOpen (convolutionDomain Ω ρ)

def AdmissibleTest : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (x : Space d)
    (hx : x ∈ convolutionDomain Ω ρ), ∀ y, convolutionTest ρ x hx y = ρ (x - y)

def Pairing : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (T : DistributionSpace 𝕜 Ω) (ρ : TestSpace 𝕜 (⊤ : Opens (Space d)))
    (x : Space d) (hx : x ∈ convolutionDomain Ω ρ),
    localConvolution T ρ x = T (convolutionTest ρ x hx)

def Smooth : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (T : DistributionSpace 𝕜 Ω) (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))),
    ContDiffOn ℝ (⊤ : ℕ∞) (localConvolution T ρ) (convolutionDomain Ω ρ)

def KernelDerivative : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (α : MultiIndex d)
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))),
    (∀ x, kernelPartial α ρ x = multiPartial ρ α x) ∧
    tsupport (kernelPartial α ρ) ⊆ tsupport ρ

def DerivativeDomain : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (α : MultiIndex d)
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))),
    convolutionDomain Ω ρ ⊆ convolutionDomain Ω (kernelPartial α ρ)

/-- Ordinary derivatives of the scalar function, at every point of U_ρ.
The RHS is defined on its own (possibly larger) admissible domain. -/
def Derivative : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (α : MultiIndex d)
    (T : DistributionSpace 𝕜 Ω) (ρ : TestSpace 𝕜 (⊤ : Opens (Space d)))
    (x : Space d), x ∈ convolutionDomain Ω ρ →
    multiPartial (localConvolution T ρ) α x = localConvolution T (kernelPartial α ρ) x

def RegularIntegral : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (f : Space d → 𝕜),
    LocallyIntegrableOn f Ω volume → ∀ (ρ : TestSpace 𝕜 (⊤ : Opens (Space d)))
    (x : Space d), x ∈ convolutionDomain Ω ρ →
    localConvolution (regularDistribution Ω f) ρ x = ∫ y in Ω, f y * ρ (x - y)

end LocalConvolutionExpected
end P102.U4
