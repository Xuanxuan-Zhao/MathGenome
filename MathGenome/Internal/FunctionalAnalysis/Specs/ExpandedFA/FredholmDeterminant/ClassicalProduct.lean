import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.ClassicalEntireSeries

/-! Multiplication stage of `fa2:p2:classical-fredholm-product`, including the
finite separable-kernel formula used in its proof. The determinant is the
original integral series. Finite positive Borel measures include all the finite
positive Radon measures of the source. Empty spaces, zero measures, and rank
zero are included. -/

open MeasureTheory Filter
open scoped Topology
universe u
namespace ExpandedFA.FredholmDeterminant.ClassicalProduct.Spec
open ClassicalDefinitions.Spec

namespace Data

/-- Restriction of the original scalar determinant to a closed parameter disk. -/
noncomputable def determinantOnDisk {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] (μ : Measure Q) (k : C(Q × Q, ℂ)) (R : ℝ)
    (hc : Continuous (FredholmDeterminantValue μ k)) :
    C(Metric.closedBall (0 : ℂ) R, ℂ) :=
  ⟨fun z => FredholmDeterminantValue μ k z, hc.comp continuous_subtype_val⟩

/-- Continuous integrand for composition, integrated in the Banach space of kernels. -/
def compositionIntegrand {Q : Type u} [TopologicalSpace Q]
    (k l : C(Q × Q, ℂ)) (t : Q) : C(Q × Q, ℂ) where
  toFun p := k (p.1, t) * l (t, p.2)
  continuous_toFun := (k.continuous.comp (continuous_fst.prodMk continuous_const)).mul
    (l.continuous.comp (continuous_const.prodMk continuous_snd))

noncomputable def compositionKernel {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] (μ : Measure Q) (k l : C(Q × Q, ℂ)) : C(Q × Q, ℂ) :=
  ∫ t, compositionIntegrand k l t ∂μ

noncomputable def productKernel {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] (μ : Measure Q) (k l : C(Q × Q, ℂ)) : C(Q × Q, ℂ) :=
  k + l - compositionKernel μ k l

/-- Finite separable kernels use ordinary products, with no complex conjugation. -/
noncomputable def separableKernel {Q : Type u} [TopologicalSpace Q] (N : ℕ)
    (a b : Fin N → C(Q, ℂ)) : C(Q × Q, ℂ) :=
  ∑ i, (a i).comp ⟨Prod.fst, continuous_fst⟩ * (b i).comp ⟨Prod.snd, continuous_snd⟩

noncomputable def pairingMatrix {Q : Type u} [TopologicalSpace Q] [MeasurableSpace Q]
    (μ : Measure Q) (N : ℕ) (a b : Fin N → C(Q, ℂ)) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => ∫ t, b i t * a j t ∂μ

end Data
open Data

/-- The epsilon-delta statement is uniform over every closed parameter disk. -/
def UniformKernelContinuity : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)) (R ε : ℝ),
    0 ≤ R → 0 < ε → ∃ δ > 0, ∀ l : C(Q × Q, ℂ), ‖l - k‖ < δ →
      ∀ z : ℂ, ‖z‖ ≤ R →
        ‖FredholmDeterminantValue μ l z - FredholmDeterminantValue μ k z‖ < ε

/-- Uniform convergence of kernels implies local uniform convergence of determinants. -/
def LocallyUniformKernelLimit : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : ℕ → C(Q × Q, ℂ)) (l : C(Q × Q, ℂ)),
    Tendsto k atTop (𝓝 l) → ∀ R : ℝ, 0 ≤ R →
      TendstoUniformlyOn (fun n z => FredholmDeterminantValue μ (k n) z)
        (FredholmDeterminantValue μ l) atTop (Metric.closedBall 0 R)

def CompositionFormula : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k l : C(Q × Q, ℂ)) (x y : Q),
    compositionKernel μ k l (x, y) = ∫ t, k (x, t) * l (t, y) ∂μ

def Multiplication : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k l : C(Q × Q, ℂ)),
    FredholmDeterminantValue μ (productKernel μ k l) 1 =
      FredholmDeterminantValue μ k 1 * FredholmDeterminantValue μ l 1

/-- The more general formula in the source substitutes arbitrary scalar multiples. -/
def ScalarMultiplication : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k l : C(Q × Q, ℂ)) (a b : ℂ),
    FredholmDeterminantValue μ (productKernel μ (a • k) (b • l)) 1 =
      FredholmDeterminantValue μ (a • k) 1 * FredholmDeterminantValue μ (b • l) 1

/-- Homogeneity of the defining determinants moves scalar multiplication into z. -/
def ScalarParameter : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)) (a z : ℂ),
    FredholmDeterminantValue μ (a • k) z = FredholmDeterminantValue μ k (a * z)

def FiniteRankFormula : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (N : ℕ) (a b : Fin N → C(Q, ℂ)) (z : ℂ),
    FredholmDeterminantValue μ (separableKernel N a b) z =
      (1 - z • pairingMatrix μ N a b).det

end ExpandedFA.FredholmDeterminant.ClassicalProduct.Spec
