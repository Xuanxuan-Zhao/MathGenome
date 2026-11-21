import MathGenome.Internal.FourierSobolev.Specs.P102.U2.CZDecomposition
import MathGenome.Internal.FourierSobolev.Specs.P102.U2.WeakNorms
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.LinearAlgebra.Isomorphisms

/-! The weak endpoint stage of Theorem p102:U2-03, paper.tex:953–971.

Lebesgue integration and Lp classes use the same native Euclidean space as the
upstream decomposition. A.e. strong measurability accommodates completed
Lebesgue representatives. The off-support formula is required on every compact
set outside which the input vanishes a.e.; it imposes no pointwise choice of
support for an L² class. Only the integral difference condition is assumed.
In particular there is no pointwise size, differentiability, translation
invariance certificate, or assumed weak endpoint bound.

The bound is uniform in the operator and kernel: a *single function* of d, A,
and the L² operator norm works on the core and the full L¹ extension. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace P102.U2.CZWeak

abbrev Point := ExpandedFA.SingularIntegrals.CZ.Point
abbrev L1 (d : ℕ) := Lp ℂ 1 (volume : Measure (Point d))
abbrev L2 (d : ℕ) := Lp ℂ 2 (volume : Measure (Point d))
abbrev Classes (d : ℕ) := Point d →ₘ[volume] ℂ
abbrev Operator (d : ℕ) := L2 d →L[ℂ] L2 d
abbrev Extension (d : ℕ) := L1 d →ₗ[ℂ] Classes d

/-- The canonical inclusion of an Lp class into measurable a.e. classes. -/
def lpEmbed {d : ℕ} (p : ℝ≥0∞) : Lp ℂ p (volume : Measure (Point d)) →ₗ[ℂ] Classes d where
  toFun f := (f : Classes d)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The sum is realized inside measurable a.e. classes, rather than treating
pairs with different decompositions as different functions. -/
def sumMap (d : ℕ) : L1 d × L2 d →ₗ[ℂ] Classes d :=
  (lpEmbed 1).coprod (lpEmbed 2)

abbrev SumSpace (d : ℕ) := LinearMap.range (sumMap d)

def sumInput {d : ℕ} (f : L1 d) (g : L2 d) : SumSpace d :=
  ⟨sumMap d (f, g), ⟨(f, g), rfl⟩⟩

/-- Exactly the kernel hypotheses of the manuscript. An NNReal bound is a
finite nonnegative real bound on the supremum of the displayed integrals.
The integral in the off-support identity is the ordinary complex Lebesgue
integral; absolute existence is not an additional input hypothesis. -/
structure KernelHypotheses {d : ℕ} (T : Operator d) (K : Point d → ℂ) (A : ℝ≥0) : Prop where
  locallyIntegrable : LocallyIntegrableOn K ({0}ᶜ : Set (Point d)) volume
  offSupport : ∀ (b : Point d → ℂ) (h2 : MemLp b 2 volume) (S : Set (Point d)),
    IsCompact S → (∀ᵐ y ∂volume, y ∉ S → b y = 0) →
    ∀ᵐ x ∂volume, x ∉ S →
      T (h2.toLp b) x = ∫ y, K (x - y) * b y
  difference : ∀ h : Point d, h ≠ 0 →
    (∫⁻ z in {z : Point d | 2 * ‖h‖ < ‖z‖}, ‖K (z - h) - K z‖ₑ) ≤ (A : ℝ≥0∞)

/-- Weak (1,1) on the original domain; inputs are arbitrary representatives. -/
def CoreBound {d : ℕ} (T : Operator d) (C : ℝ) : Prop :=
  ∀ (f : Point d → ℂ), MemLp f 1 volume → ∀ h2 : MemLp f 2 volume,
    ∀ t : ℝ, 0 < t →
      volume {x | t < ‖T (h2.toLp f) x‖} ≤
        ENNReal.ofReal (C / t) * eLpNorm f 1 volume

/-- Agreement on the full intersection, as equality of measurable a.e. classes. -/
def Compatible {d : ℕ} (T : Operator d) (S : Extension d) : Prop :=
  ∀ (f : Point d → ℂ) (h1 : MemLp f 1 volume) (h2 : MemLp f 2 volume),
    S (h1.toLp f) = lpEmbed 2 (T (h2.toLp f))

def WeakBound {d : ℕ} (S : Extension d) (C : ℝ) : Prop :=
  ∀ (f : L1 d) (t : ℝ), 0 < t →
    volume {x | t < ‖S f x‖} ≤ ENNReal.ofReal (C / t) * ENNReal.ofReal ‖f‖

/-- This is global convergence in measure, even though Euclidean volume is
infinite, not merely convergence in measure on compact sets. -/
def MeasureContinuous {d : ℕ} (S : Extension d) : Prop :=
  ∀ (u : ℕ → L1 d) (f : L1 d), Tendsto u atTop (𝓝 f) →
    TendstoInMeasure volume (fun n => (S (u n) : Point d → ℂ)) atTop (S f)

/-- Every approximating core sequence has the same image limit. -/
def Approximates {d : ℕ} (T : Operator d) (S : Extension d) : Prop :=
  ∀ (u : ℕ → L1 d) (h2 : ∀ n, MemLp (u n : Point d → ℂ) 2 volume)
    (f : L1 d), Tendsto u atTop (𝓝 f) →
      TendstoInMeasure volume
        (fun n => (T ((h2 n).toLp (u n)) : Point d → ℂ)) atTop (S f)

/-- Uniqueness among all compatible linear weak-(1,1) extensions; a competing
extension need not use the same bound. -/
def UniqueWeakExtension {d : ℕ} (T : Operator d) (S : Extension d) : Prop :=
  ∀ S' : Extension d, Compatible T S' →
    (∃ D : ℝ, 0 ≤ D ∧ WeakBound S' D) → S' = S

/-- The action on L¹ + L² is independent of every choice of decomposition. -/
def CompatibleSum {d : ℕ} (T : Operator d) (S : Extension d) : Prop :=
  ∃! U : SumSpace d →ₗ[ℂ] Classes d,
    ∀ (f : L1 d) (g : L2 d), U (sumInput f g) = S f + lpEmbed 2 (T g)

end P102.U2.CZWeak

namespace Specs.P102.U2.CZWeakExtension
open _root_.P102.U2.CZWeak

/-- All original kernel hypotheses imply a uniform core bound. -/
def weak_core : Prop :=
  ∃ C : ℕ → ℝ≥0 → ℝ≥0 → ℝ≥0,
    ∀ (d : ℕ), 0 < d → ∀ (T : Operator d) (K : Point d → ℂ) (A : ℝ≥0),
      KernelHypotheses T K A → CoreBound T (C d A ‖T‖₊)

/-- The full assigned result. The same C bounds both the original action and
its extension, with no unproved endpoint certificate in the hypotheses. -/
def weak_extension : Prop :=
  ∃ C : ℕ → ℝ≥0 → ℝ≥0 → ℝ≥0,
    ∀ (d : ℕ), 0 < d → ∀ (T : Operator d) (K : Point d → ℂ) (A : ℝ≥0),
      KernelHypotheses T K A →
        CoreBound T (C d A ‖T‖₊) ∧
        ∃ S : Extension d, Compatible T S ∧ WeakBound S (C d A ‖T‖₊) ∧
          MeasureContinuous S ∧ Approximates T S ∧ UniqueWeakExtension T S ∧ CompatibleSum T S

/-- Auxiliary extension step, to be proved from a core bound, not assumed in
`weak_extension`. The harmless factor two can be absorbed into its uniform C. -/
def abstract_extension : Prop :=
  ∀ (d : ℕ) (T : Operator d) (C : ℝ), 0 ≤ C → CoreBound T C →
    ∃ S : Extension d, Compatible T S ∧ WeakBound S (2 * C) ∧
      MeasureContinuous S ∧ Approximates T S ∧ UniqueWeakExtension T S ∧ CompatibleSum T S

end Specs.P102.U2.CZWeakExtension
