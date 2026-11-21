import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.OperatorDomains
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.BochnerLpCompleteness
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-! Maximal scalar multiplication, paper.tex:13937–13967.
All spaces use the accepted `MeasureTheory.Lp` a.e. quotient. The measure is
arbitrary. Scalar-valued functions are finite-valued; changing values on a null
set is covered by the representative laws below. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace ExpandedFA.Multiplication

variable {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜]

/-- The maximal domain, expressed using a representative of the Lp class. -/
def maximalDomain (μ : Measure Ω) (p : ℝ≥0∞) (a : Ω → 𝕜) :
    Submodule 𝕜 (Lp 𝕜 p μ) where
  carrier := {f | MemLp (fun x => a x * f x) p μ}
  zero_mem' := by
    apply (MemLp.zero : MemLp (0 : Ω → 𝕜) p μ).ae_eq
    filter_upwards [Lp.coeFn_zero 𝕜 p μ] with x hx
    change (0 : 𝕜) = a x * (0 : Lp 𝕜 p μ) x
    rw [hx]
    simp
  add_mem' := by
    intro f g hf hg
    apply (hf.add hg).ae_eq
    filter_upwards [Lp.coeFn_add f g] with x hx
    change a x * f x + a x * g x = a x * (f + g : Lp 𝕜 p μ) x
    rw [hx]
    exact (mul_add _ _ _).symm
  smul_mem' := by
    intro c f hf
    apply (hf.const_smul c).ae_eq
    filter_upwards [Lp.coeFn_smul c f] with x hx
    simp [hx, mul_left_comm]

/-- The operator includes its exact maximal domain. -/
def maximalMultiplier (μ : Measure Ω) (p : ℝ≥0∞) (a : Ω → 𝕜) :
    Unbounded.Operator 𝕜 (Lp 𝕜 p μ) (Lp 𝕜 p μ) where
  domain := maximalDomain μ p a
  toFun :=
    { toFun := fun f => f.2.toLp (fun x => a x * (f : Lp 𝕜 p μ) x)
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (f + g).2,
          Lp.coeFn_add (f.2.toLp _) (g.2.toLp _),
          MemLp.coeFn_toLp f.2, MemLp.coeFn_toLp g.2,
          Lp.coeFn_add (f : Lp 𝕜 p μ) (g : Lp 𝕜 p μ)] with x h₁ h₂ h₃ h₄ h₅
        simp_all [mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (c • f).2,
          Lp.coeFn_smul c (f.2.toLp _), MemLp.coeFn_toLp f.2,
          Lp.coeFn_smul c (f : Lp 𝕜 p μ)] with x h₁ h₂ h₃ h₄
        simp_all [mul_left_comm] }

/-- Classes vanishing a.e. outside E, for any exponent r. -/
def supportedLp (μ : Measure Ω) (r : ℝ≥0∞) (E : Set Ω) :
    Submodule 𝕜 (Lp 𝕜 r μ) where
  carrier := {f | ∀ᵐ x ∂μ, x ∉ E → f x = 0}
  zero_mem' := (Lp.coeFn_zero 𝕜 r μ).mono fun _ hx _ => hx
  add_mem' := by
    intro f g hf hg
    filter_upwards [hf, hg, Lp.coeFn_add f g] with x hx hy hfg
    intro hE
    change (f + g : Lp 𝕜 r μ) x = 0
    rw [hfg]
    simp [hx hE, hy hE]
  smul_mem' := by
    intro c f hf
    filter_upwards [hf, Lp.coeFn_smul c f] with x hx hcf
    intro hE
    simp [hcf, hx hE]

/-- The zero level set of the multiplier. -/
def zeroSet (a : Ω → 𝕜) : Set Ω := {x | a x = 0}

namespace MaximalLpMultiplierSpec

/-- Full, independently stated types and values of the four constructions. -/
def DomainType := ∀ {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜],
  (μ : Measure Ω) → (p : ℝ≥0∞) → (Ω → 𝕜) → Submodule 𝕜 (Lp 𝕜 p μ)
def domainValue : DomainType := @maximalDomain

def MultiplierType := ∀ {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜],
  (μ : Measure Ω) → (p : ℝ≥0∞) → (Ω → 𝕜) →
    Unbounded.Operator 𝕜 (Lp 𝕜 p μ) (Lp 𝕜 p μ)
def multiplierValue : MultiplierType := @maximalMultiplier

def SupportedType := ∀ {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜],
  (μ : Measure Ω) → (r : ℝ≥0∞) → Set Ω → Submodule 𝕜 (Lp 𝕜 r μ)
def supportedValue : SupportedType := @supportedLp

def ZeroSetType := ∀ {Ω 𝕜 : Type*} [RCLike 𝕜], (Ω → 𝕜) → Set Ω
def zeroSetValue : ZeroSetType := @zeroSet

def DomainLaw : Prop := ∀ {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
  (μ : Measure Ω) (p : ℝ≥0∞) (a : Ω → 𝕜) (f : Lp 𝕜 p μ),
  f ∈ (maximalMultiplier μ p a).domain ↔ MemLp (fun x => a x * f x) p μ

def ApplyLaw : Prop := ∀ {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
  (μ : Measure Ω) (p : ℝ≥0∞) (a : Ω → 𝕜) (f : (maximalMultiplier μ p a).domain),
  (maximalMultiplier μ p a f : Ω → 𝕜) =ᵐ[μ] fun x => a x * (f : Lp 𝕜 p μ) x

def SupportedLaw : Prop := ∀ {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
  (μ : Measure Ω) (r : ℝ≥0∞) (E : Set Ω) (f : Lp 𝕜 r μ),
  f ∈ supportedLp μ r E ↔ ∀ᵐ x ∂μ, x ∉ E → f x = 0

/-- Both the multiplier and the input may be replaced a.e. -/
def RepresentativesLaw : Prop := ∀ {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
  (μ : Measure Ω) (p : ℝ≥0∞) (a b f g : Ω → 𝕜),
  a =ᵐ[μ] b → f =ᵐ[μ] g →
  (MemLp (fun x => a x * f x) p μ ↔ MemLp (fun x => b x * g x) p μ)

def OperatorCongrLaw : Prop := ∀ {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
  (μ : Measure Ω) (p : ℝ≥0∞) (a b : Ω → 𝕜),
  a =ᵐ[μ] b → maximalMultiplier μ p a = maximalMultiplier μ p b

def ApplyRepresentativeLaw : Prop := ∀ {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
  (μ : Measure Ω) (p : ℝ≥0∞) (a : Ω → 𝕜) (f : (maximalMultiplier μ p a).domain)
  (g : Ω → 𝕜), (f : Lp 𝕜 p μ) =ᵐ[μ] g →
  (maximalMultiplier μ p a f : Ω → 𝕜) =ᵐ[μ] fun x => a x * g x

/-- Proved at the stronger range 1 ≤ p < ∞, including the source range 1 < p < ∞.
There is no finiteness, semifiniteness, or sigma-finiteness assumption on μ. -/
def DenseLaw : Prop := ∀ {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]
  (μ : Measure Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
  (a : Ω → 𝕜), Measurable a → Dense ((maximalMultiplier μ p a).domain : Set (Lp 𝕜 p μ))

/-- Closedness even holds at p = ∞ and does not require measurability of a. -/
def ClosedLaw : Prop := ∀ {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
  (μ : Measure Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : Ω → 𝕜),
  (maximalMultiplier μ p a).IsClosed

end MaximalLpMultiplierSpec
end ExpandedFA.Multiplication
