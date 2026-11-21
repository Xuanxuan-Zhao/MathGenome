import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.ExceptionalSets
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Algebra.Order.Floor.Ring

/-! Independent statements for the lower-dimensional overlap estimate in
`d04:15:piecewise`. Content and integration are the Chapter 6 finite-box
content and Darboux integral. No measure-zero surrogate is used. -/
noncomputable section
open Set Topology
open scoped BigOperators ContDiff NNReal
namespace Specs.D04.C15.LowerDimensionalImagesHaveZeroContent
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.NullCovers.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model

/-- The domain is subdivided into boxes of side at most δ. Each image piece
has a covering box, with total k-content bounded uniformly by C δ^(k-d).
Allowing a bounded subset S of the rectangle is useful for restricted charts.
Degenerate source sides and d = 0 are included. -/
def quantitative_coverType : Prop :=
  ∀ {d k : ℕ}, d < k → ∀ (Q : Box d) (S : Set (E d)) (f : E d → E k)
    (L : ℝ≥0), S ⊆ carrier Q → LipschitzOnWith L f S →
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ (ι : Type) (_ : Fintype ι) (A : ι → Box d) (R : ι → Box k),
        carrier Q = ⋃ i, carrier (A i) ∧
        (∀ i, carrier (A i) ⊆ carrier Q) ∧
        (∀ i j, (A i).upper j - (A i).lower j ≤ δ) ∧
        (∀ i, f '' (S ∩ carrier (A i)) ⊆ carrier (R i)) ∧
        (∑ i, content (R i)) ≤ C * δ ^ (k - d)

def lipschitz_image_contentZeroType : Prop :=
  ∀ {d k : ℕ}, d < k → ∀ (S : Set (E d)) (f : E d → E k) (L : ℝ≥0),
    Bornology.IsBounded S → LipschitzOnWith L f S → ContentZero (f '' S)

def lipschitz_rectangleType : Prop :=
  ∀ {d k : ℕ}, d < k → ∀ (Q : Box d) (f : E d → E k) (L : ℝ≥0),
    LipschitzOnWith L f (carrier Q) →
    IsCompact (f '' carrier Q) ∧ ContentZero (f '' carrier Q)

/-- Regularity is local at every point of the compact parameter set; no
Lipschitz assumption on a noncompact chart is imposed. -/
def compact_C1_imageType : Prop :=
  ∀ {d k : ℕ}, d < k → ∀ (K : Set (E d)) (f : E d → E k),
    IsCompact K → (∀ x ∈ K, ContDiffAt ℝ 1 f x) →
    IsCompact (f '' K) ∧ ContentZero (f '' K)

/-- Local extendibility suffices, even if the given ambient representative
is irregular off K. This includes C¹ pieces up to a genuine boundary. -/
def compact_local_C1_imageType : Prop :=
  ∀ {d k : ℕ}, d < k → ∀ (K : Set (E d)) (f : E d → E k),
    IsCompact K →
    (∀ x ∈ K, ∃ (U : Set (E d)) (g : E d → E k),
      U ∈ nhds x ∧ ContDiffAt ℝ 1 g x ∧ EqOn g f (K ∩ U)) →
    IsCompact (f '' K) ∧ ContentZero (f '' K)

def finite_C1_imagesType : Prop :=
  ∀ {ι : Type} [Fintype ι] {k : ℕ} (d : ι → ℕ)
    (K : ∀ i, Set (E (d i))) (f : ∀ i, E (d i) → E k),
    (∀ i, d i < k) → (∀ i, IsCompact (K i)) →
    (∀ i x, x ∈ K i → ContDiffAt ℝ 1 (f i) x) →
    IsCompact (⋃ i, f i '' K i) ∧ ContentZero (⋃ i, f i '' K i)

def finite_local_C1_imagesType : Prop :=
  ∀ {ι : Type} [Fintype ι] {k : ℕ} (d : ι → ℕ)
    (K : ∀ i, Set (E (d i))) (f : ∀ i, E (d i) → E k),
    (∀ i, d i < k) → (∀ i, IsCompact (K i)) →
    (∀ i x, x ∈ K i → ∃ (U : Set (E (d i))) (g : E (d i) → E k),
      U ∈ nhds x ∧ ContDiffAt ℝ 1 g x ∧ EqOn g (f i) (K i ∩ U)) →
    IsCompact (⋃ i, f i '' K i) ∧ ContentZero (⋃ i, f i '' K i)

def finite_pointsType : Prop :=
  ∀ {k : ℕ}, 0 < k → ∀ (S : Set (E k)), S.Finite → ContentZero S

/-- The chart inverse is only used on its actual embedded target. Local
ambient inverse extensions supply Lipschitz control on the compact pieces. -/
def chart_overlapType : Prop :=
  ∀ {d k n : ℕ} {M : Set (E n)} (c : EmbeddedChart 1 k n M),
    d < k → k ≤ n → ∀ (K : Set (E d)) (f : E d → E n),
    IsCompact K → (∀ x ∈ K, ContDiffAt ℝ 1 f x) →
    f '' K ⊆ M ∩ c.ambient →
    IsCompact (c.invFun '' (f '' K)) ∧ ContentZero (c.invFun '' (f '' K))

def chart_local_overlapType : Prop :=
  ∀ {d k n : ℕ} {M : Set (E n)} (c : EmbeddedChart 1 k n M),
    d < k → k ≤ n → ∀ (K : Set (E d)) (f : E d → E n),
    IsCompact K →
    (∀ x ∈ K, ∃ (U : Set (E d)) (g : E d → E n),
      U ∈ nhds x ∧ ContDiffAt ℝ 1 g x ∧ EqOn g f (K ∩ U)) →
    f '' K ⊆ M ∩ c.ambient →
    IsCompact (c.invFun '' (f '' K)) ∧ ContentZero (c.invFun '' (f '' K))

/-- Any bounded coordinate coefficient supported on an overlap contributes
zero to the actual Riemann integral. This includes bounded continuous
coefficients multiplied by an overlap indicator. -/
def coefficient_integral_zeroType : Prop :=
  ∀ {k : ℕ}, 0 < k → ∀ (S : Set (E k)), ContentZero S →
    ∀ (Q : Box k) (a : E k → ℝ), Bounded a Q →
    (∀ x ∈ carrier Q, x ∉ S → a x = 0) →
    ∃ h : Integrable a Q, integral a Q h = 0

def coefficient_integral_unchangedType : Prop :=
  ∀ {k : ℕ}, 0 < k → ∀ (S : Set (E k)), ContentZero S →
    ∀ (Q : Box k) (a b : E k → ℝ) (ha : Integrable a Q), Bounded b Q →
    (∀ x ∈ carrier Q, x ∉ S → a x = b x) →
    ∃ hb : Integrable b Q, integral b Q hb = integral a Q ha
end Specs.D04.C15.LowerDimensionalImagesHaveZeroContent
