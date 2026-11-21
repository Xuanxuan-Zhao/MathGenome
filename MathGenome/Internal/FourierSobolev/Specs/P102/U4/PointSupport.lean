import MathGenome.Internal.FourierSobolev.Specs.P102.U4.DistributionSupport
import Mathlib.Data.Fintype.Pi

/-! Independent scope of paper.tex:1378–1389, p102:U4-03.
The indexing type contains distinct multisets of coordinate directions, rather
than coordinate words. The upstream `multiIndexCountsEquiv` identifies these
with the usual vectors in ℕ^d. All statements include dimension zero, both real
and complex scalar fields, and the zero distribution. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff Distributions
namespace P102.U4

/-- Distinct Euclidean multi-indices of total degree at most m. -/
abbrev BoundedMultiIndex (d m : ℕ) := {α : MultiIndex d // α.card ≤ m}

/-- Multiplicity vectors are bounded coordinatewise, so this is a finite type. -/
instance boundedMultiIndexFintype (d m : ℕ) : Fintype (BoundedMultiIndex d m) := by
  let f : BoundedMultiIndex d m → (Fin d → Fin (m + 1)) := fun α i =>
    ⟨α.val.count i, Nat.lt_succ_of_le ((Multiset.count_le_card i α.val).trans α.property)⟩
  exact Fintype.ofInjective f (by
    intro α β h
    apply Subtype.ext
    apply Multiset.ext.mpr
    intro i
    exact congrArg Fin.val (congrFun h i))

/-- Scalar-linear evaluation, with no conjugation for complex tests. -/
def pointMass {d : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (a : Space d) : DistributionSpace 𝕜 Ω where
  toFun φ := φ a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_eval_const _

/-- A finite sum of derivatives of the point mass, with no repeated indices. -/
def pointDerivativeSum {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (a : Space d) (m : ℕ) (c : BoundedMultiIndex d m → 𝕜) : DistributionSpace 𝕜 Ω :=
  ∑ α, c α • distributionPartial α.val (pointMass 𝕜 Ω a)

/-- The finite jet as an actual scalar-linear map on the canonical test space. -/
def testJet {d : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (a : Space d) (m : ℕ) : TestSpace 𝕜 Ω →ₗ[𝕜] (BoundedMultiIndex d m → 𝕜) :=
  LinearMap.pi fun α => ((pointMass 𝕜 Ω a).comp
    (testPartialWord Ω (α.val.sort (· ≤ ·)))).toLinearMap

namespace PointSupportExpected

/-- The finite indexing type is bijective with the usual degree-bounded
coordinate vectors, preserving every individual multiplicity. -/
def MultiIndexBridge : Prop :=
  ∀ d m : ℕ, ∃ e : BoundedMultiIndex d m ≃ {v : Fin d → ℕ // ∑ i, v i ≤ m},
    ∀ α i, (e α).val i = α.val.count i

def DiracType := {d : ℕ} → (𝕜 : Type) → [RCLike 𝕜] →
  (Ω : Opens (Space d)) → Space d → DistributionSpace 𝕜 Ω

def DiracValue : DiracType := @pointMass

def DerivativeFormula : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (a : Space d)
    (α : MultiIndex d) (φ : TestSpace 𝕜 Ω),
    distributionPartial α (pointMass 𝕜 Ω a) φ =
      (-1 : 𝕜) ^ α.card * multiPartial φ α a

/-- Existence under precisely the support hypothesis, without an assumed order,
annihilation certificate, or jet interpolation hypothesis. -/
def Representation : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (a : Space d),
    a ∈ Ω → ∀ S : DistributionSpace 𝕜 Ω,
    relativeSupport S ⊆ {a} →
    ∃ (m : ℕ) (c : BoundedMultiIndex d m → 𝕜), S = pointDerivativeSum Ω a m c

/-- Coefficients live only on the bounded, distinct multi-indices, so equality
of coefficient functions asserts exactly the source's fixed-order uniqueness. -/
def Uniqueness : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (a : Space d),
    a ∈ Ω → ∀ (m : ℕ) (c c' : BoundedMultiIndex d m → 𝕜),
    pointDerivativeSum Ω a m c = pointDerivativeSum Ω a m c' → c = c'

def ZeroRepresentation : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (a : Space d) (m : ℕ),
    pointDerivativeSum Ω a m (fun _ => (0 : 𝕜)) = 0

/-- Dimension zero is scalar evaluation at the sole point, of order zero. -/
def DimensionZero : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space 0)) (a : Space 0), a ∈ Ω →
    ∀ S : DistributionSpace 𝕜 Ω, ∃! c : 𝕜, S = c • pointMass 𝕜 Ω a

/-- The analytic finite-order lemma needed for existence. This is an obligation,
not an assumed certificate in the representation theorem. -/
def FiniteJetAnnihilation : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (a : Space d),
    a ∈ Ω → ∀ S : DistributionSpace 𝕜 Ω, relativeSupport S ⊆ {a} →
    ∃ m : ℕ, ∀ φ : TestSpace 𝕜 Ω,
      (∀ α : MultiIndex d, α.card ≤ m → multiPartial φ α a = 0) → S φ = 0

/-- Cutoff monomials realize the coordinate unit jets, on distinct multi-indices. -/
def JetInterpolation : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (a : Space d),
    a ∈ Ω → ∀ (m : ℕ) (α : MultiIndex d), α.card ≤ m →
    ∃ φ : TestSpace 𝕜 Ω, ∀ β : MultiIndex d, β.card ≤ m →
      multiPartial φ β a = if β = α then 1 else 0

/-- Algebraic assembly isolates the analytic and interpolation theorems. The final Representation and Uniqueness have no such premises. -/
def Assembly : Prop :=
  FiniteJetAnnihilation → JetInterpolation → Representation ∧ Uniqueness

end PointSupportExpected
end P102.U4
