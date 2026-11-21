import MathGenome.Internal.FourierSobolev.Specs.P102.U4.SobolevSpace

/-! Zero extension in the distribution-defined Sobolev spaces.  The support
hypothesis below is a property of the a.e. class, not of the selected Lp
representative.  The definition of W₀ is made for every p ≥ 1. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped Distributions ENNReal
namespace P102.U4

/-- The canonical inclusion of smooth compactly supported functions into Lp. -/
def testToDomainLp {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] : TestSpace 𝕜 Ω →ₗ[𝕜] DomainLp 𝕜 Ω p where
  toFun φ := (φ.continuous.memLp_of_hasCompactSupport (p := p) φ.hasCompactSupport).toLp φ
  map_add' φ ψ := by
    exact MemLp.toLp_add _ _
  map_smul' c φ := by
    exact MemLp.toLp_const_smul c _

/-- Smooth compactly supported classes in the canonical Sobolev space. -/
def smoothSobolevSubmodule {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (Ω : Opens (Space d)) (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Submodule 𝕜 (Sobolev 𝕜 Ω m p) :=
  (LinearMap.range (testToDomainLp Ω p)).comap (sobolevUnderlyingCLM Ω m p).toLinearMap

/-- W₀^{m,p}(Ω) is the norm closure of C_c^∞(Ω), including p = ∞. -/
def sobolevZeroSubmodule {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (Ω : Opens (Space d)) (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Submodule 𝕜 (Sobolev 𝕜 Ω m p) :=
  (smoothSobolevSubmodule 𝕜 Ω m p).topologicalClosure

abbrev SobolevZero {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (Ω : Opens (Space d)) (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :=
  ↥(sobolevZeroSubmodule 𝕜 Ω m p)

/-- Zero extension of an Lp class, using the open-set indicator. -/
def lpZeroExtension {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) (u : DomainLp 𝕜 Ω p) : DomainLp (d := d) 𝕜 ⊤ p :=
  (show MemLp ((Ω : Set (Space d)).indicator u) p
      (volume.restrict (↑(⊤ : Opens (Space d)) : Set (Space d))) by
    simpa using (memLp_indicator_iff_restrict Ω.isOpen.measurableSet.nullMeasurableSet).mpr
      (Lp.memLp u)).toLp _

/-- Compact support in Ω in the essential (representative-independent) sense. -/
def HasCompactSupportIn {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {p : ℝ≥0∞} (u : DomainLp 𝕜 Ω p) : Prop :=
  ∃ K : Compacts (Space d), (K : Set (Space d)) ⊆ Ω ∧
    ∀ᵐ x ∂volume.restrict (Ω : Set (Space d)), x ∉ K → u x = 0

namespace ZeroExtensionExpected

def SpaceType := {d : ℕ} → (𝕜 : Type) → [RCLike 𝕜] → (Ω : Opens (Space d)) →
  (m : ℕ) → (p : ℝ≥0∞) → [Fact (1 ≤ p)] → Type

def SpaceValue : SpaceType := @SobolevZero

def LpExtensionType := {d : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → (Ω : Opens (Space d)) →
  (p : ℝ≥0∞) → DomainLp 𝕜 Ω p → DomainLp (d := d) 𝕜 ⊤ p

def LpExtensionValue : LpExtensionType := @lpZeroExtension

/-- All smooth tests give Sobolev classes; the defining image is the intended one. -/
def SmoothInclusion : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d)) (m : ℕ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : TestSpace 𝕜 Ω),
    ∃ u : Sobolev 𝕜 Ω m p, sobolevUnderlying u = testToDomainLp Ω p φ

def Closure : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d)) (m : ℕ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)],
    (sobolevZeroSubmodule 𝕜 Ω m p : Set (Sobolev 𝕜 Ω m p)) =
      closure {u | ∃ φ : TestSpace 𝕜 Ω, sobolevUnderlying u = testToDomainLp Ω p φ}

def LpRepresentative : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) (u : DomainLp 𝕜 Ω p),
    (lpZeroExtension Ω p u : Space d → 𝕜) =ᵐ[volume] (Ω : Set (Space d)).indicator u

def LpIsometry : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ∃ E : DomainLp 𝕜 Ω p →ₗᵢ[𝕜] DomainLp (d := d) 𝕜 ⊤ p, ∀ u, E u = lpZeroExtension Ω p u

/-- The linear zero extension on W₀, with every coordinate and the exact norm. -/
def Extension : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d)) (m : ℕ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∃ E : SobolevZero 𝕜 Ω m p →ₗᵢ[𝕜] Sobolev (d := d) 𝕜 ⊤ m p,
      (∀ u, sobolevUnderlying (E u) = lpZeroExtension Ω p (sobolevUnderlying u.val)) ∧
      (∀ u α, sobolevDerivative (E u) α = lpZeroExtension Ω p (sobolevDerivative u.val α)) ∧
      (∀ u, ‖E u‖ = ∑ α : SobolevIndex d m, ‖sobolevDerivative u.val α‖)

/-- The local assertion assumes compact support, without assuming W₀ membership. -/
def CompactExtension : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d)) (m : ℕ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → ∀ u : Sobolev 𝕜 Ω m p,
    HasCompactSupportIn (sobolevUnderlying u) →
    ∃ v : Sobolev (d := d) 𝕜 ⊤ m p,
      sobolevUnderlying v = lpZeroExtension Ω p (sobolevUnderlying u) ∧
      (∀ α, sobolevDerivative v α = lpZeroExtension Ω p (sobolevDerivative u α)) ∧
      ‖v‖ = ‖u‖

end ZeroExtensionExpected
end P102.U4
