import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hardy.AtomicHardySpace
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Topology.Algebra.Support

/-!
The full obligation of paper.tex:18432--18485. All functions are identified a.e.
in the accepted L¹ quotient. The p-norm is finite by `MemLp`; its real value
is therefore the usual norm. The series below converge in L¹, rather than
being merely formal expansions. The infimum is taken over ordinary sequences,
allowing repeated atoms, exactly as in the accepted infinity-atomic space.
No positive-dimension restriction is imposed on these affirmative results.
-/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
universe v

namespace ExpandedFA.Hardy.HardyPAtomsSpec

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev L1 (d : ℕ) (𝕜 : Type v) [RCLike 𝕜] :=
  AtomicHardySpaceSpec.L1 (𝕜 := 𝕜) (volume : Measure (Point d))
abbrev H1 (d : ℕ) (𝕜 : Type v) [RCLike 𝕜] :=
  AtomicHardySpaceSpec.HardyValue (𝕜 := 𝕜) (volume : Measure (Point d))
abbrev InfinityAtom (d : ℕ) (𝕜 : Type v) [RCLike 𝕜] :=
  AtomicHardySpaceSpec.AtomValue (𝕜 := 𝕜) (volume : Measure (Point d))

/-- Essential support and finite Lp size on the source's actual Euclidean ball.
Finite Lp membership is explicit, so `toReal` cannot hide an infinite norm. -/
def IsPAtom (d : ℕ) (p : ℝ) {𝕜 : Type v} [RCLike 𝕜] (a : L1 d 𝕜) : Prop :=
  MemLp a (ENNReal.ofReal p) volume ∧ (∫ x, a x) = 0 ∧
  ∃ c : Point d, ∃ r : ℝ, 0 < r ∧
    (∀ᵐ x ∂volume, x ∉ Metric.ball c r → a x = 0) ∧
    (eLpNorm a (ENNReal.ofReal p) volume).toReal ≤
      (volume.real (Metric.ball c r)) ^ (1 / p - 1)

abbrev PAtom (d : ℕ) (p : ℝ) (𝕜 : Type v) [RCLike 𝕜] :=
  {a : L1 d 𝕜 // IsPAtom d p a}

/-- The full p-atomic space as an actual subset of L¹. -/
def HasPAtomicSeries (d : ℕ) (p : ℝ) {𝕜 : Type v} [RCLike 𝕜]
    (f : L1 d 𝕜) : Prop :=
  ∃ a : ℕ → PAtom d p 𝕜, ∃ c : ℕ → 𝕜,
    Summable (fun j => ‖c j‖) ∧ HasSum (fun j => c j • (a j).val) f

def pAtomicNorm (d : ℕ) (p : ℝ) {𝕜 : Type v} [RCLike 𝕜] (f : L1 d 𝕜) : ℝ :=
  sInf {r : ℝ | ∃ a : ℕ → PAtom d p 𝕜, ∃ c : ℕ → 𝕜,
    Summable (fun j => ‖c j‖) ∧ HasSum (fun j => c j • (a j).val) f ∧
    (∑' j, ‖c j‖) = r}

/-- Quantitative, convergent infinity-atomic expansion, uniform in the atom
and in the real/complex scalar field. This is the principal difficult target. -/
def ExpansionBound : Prop :=
  ∀ (d : ℕ) (p : ℝ), 1 < p → ∃ C : ℝ, 0 < C ∧
    ∀ {𝕜 : Type v} [RCLike 𝕜] (a : PAtom d p 𝕜),
    ∃ b : ℕ → InfinityAtom d 𝕜, ∃ c : ℕ → 𝕜,
      Summable (fun j => ‖c j‖) ∧ HasSum (fun j => c j • (b j).val) a.val ∧
      (∑' j, ‖c j‖) ≤ C

def AtomBound : Prop :=
  ∀ (d : ℕ) (p : ℝ), 1 < p → ∃ C : ℝ, 0 < C ∧
    ∀ {𝕜 : Type v} [RCLike 𝕜] (a : PAtom d p 𝕜),
      ∃ h : H1 d 𝕜, AtomicHardySpaceSpec.EmbeddingValue volume h = a.val ∧ ‖h‖ ≤ C

def InfinityAtomsArePAtoms : Prop :=
  ∀ (d : ℕ) (p : ℝ), 1 < p → ∀ {𝕜 : Type v} [RCLike 𝕜]
    (a : InfinityAtom d 𝕜), IsPAtom d p a.val

/-- The bound for the source's ordinary functions, without assuming L¹
membership in addition to the stated finite-p and support hypotheses. -/
def RawAtomBound : Prop :=
  ∀ (d : ℕ) (p : ℝ), 1 < p → ∃ C : ℝ, 0 < C ∧
    ∀ {𝕜 : Type v} [RCLike 𝕜] (f : Point d → 𝕜),
    MemLp f (ENNReal.ofReal p) volume → (∫ x, f x) = 0 →
    (∃ c : Point d, ∃ r : ℝ, 0 < r ∧
      (∀ᵐ x ∂volume, x ∉ Metric.ball c r → f x = 0) ∧
      (eLpNorm f (ENNReal.ofReal p) volume).toReal ≤
        (volume.real (Metric.ball c r)) ^ (1 / p - 1)) →
    ∃ h : H1 d 𝕜, AtomicHardySpaceSpec.EmbeddingValue volume h =ᵐ[volume] f ∧ ‖h‖ ≤ C

def PAtomL1Bound : Prop :=
  ∀ (d : ℕ) (p : ℝ), 1 < p → ∀ {𝕜 : Type v} [RCLike 𝕜]
    (a : PAtom d p 𝕜), ‖a.val‖ ≤ 1

/-- Summable p-atomic coefficient sequences always define actual L¹ sums. -/
def PAtomicSynthesis : Prop :=
  ∀ (d : ℕ) (p : ℝ), 1 < p → ∀ {𝕜 : Type v} [RCLike 𝕜]
    (a : ℕ → PAtom d p 𝕜) (c : ℕ → 𝕜), Summable (fun j => ‖c j‖) →
    ∃ f : L1 d 𝕜, HasSum (fun j => c j • (a j).val) f ∧ ‖f‖ ≤ ∑' j, ‖c j‖

/-- Equality of spaces and both quantitative norm comparisons. -/
def EquivalentNorm : Prop :=
  ∀ (d : ℕ) (p : ℝ), 1 < p → ∃ C : ℝ, 0 < C ∧
    ∀ {𝕜 : Type v} [RCLike 𝕜] (f : L1 d 𝕜),
      ((∃ h : H1 d 𝕜, AtomicHardySpaceSpec.EmbeddingValue volume h = f) ↔
        HasPAtomicSeries d p f) ∧
      ∀ h : H1 d 𝕜, AtomicHardySpaceSpec.EmbeddingValue volume h = f →
        pAtomicNorm d p f ≤ ‖h‖ ∧ ‖h‖ ≤ C * pAtomicNorm d p f

/-- The source corollary for ordinary functions, with the actual L¹
representative bridge, rather than an extra assumed L¹ hypothesis. -/
def CompactMembership : Prop :=
  ∀ (d : ℕ) (p : ℝ), 1 < p → ∀ {𝕜 : Type v} [RCLike 𝕜]
    (f : Point d → 𝕜), MemLp f (ENNReal.ofReal p) volume →
    HasCompactSupport f → (∫ x, f x) = 0 →
      ∃ h : H1 d 𝕜, AtomicHardySpaceSpec.EmbeddingValue volume h =ᵐ[volume] f

/-- Explicit all-scalar zero-dimensional atomic expansion. -/
def ZeroDimensionExpansion : Prop :=
  ∀ (p : ℝ) {𝕜 : Type v} [RCLike 𝕜] (a : PAtom 0 p 𝕜),
    ∃ b : ℕ → InfinityAtom 0 𝕜, ∃ c : ℕ → 𝕜,
      Summable (fun j => ‖c j‖) ∧ HasSum (fun j => c j • (b j).val) a.val ∧
      (∑' j, ‖c j‖) ≤ 1

/-- All conclusions of the assigned source result, including an actual series. -/
def MainResult : Prop :=
  ExpansionBound.{v} ∧ AtomBound.{v} ∧ RawAtomBound.{v} ∧
    EquivalentNorm.{v} ∧ CompactMembership.{v}

def Assembly : Prop := ExpansionBound.{v} → MainResult.{v}

/-- Logical transport helpers keep the substantial analytic obligation above
visible. They do not replace its unconditional proof. -/
def ExpansionToBound : Prop := ExpansionBound.{v} → AtomBound.{v}
def BoundToExpansion : Prop := AtomBound.{v} → ExpansionBound.{v}
def BoundToRawAtomBound : Prop := AtomBound.{v} → RawAtomBound.{v}
def BoundToEquivalentNorm : Prop :=
  InfinityAtomsArePAtoms.{v} → AtomBound.{v} → EquivalentNorm.{v}
def BoundToCompactMembership : Prop := AtomBound.{v} → CompactMembership.{v}

end ExpandedFA.Hardy.HardyPAtomsSpec
