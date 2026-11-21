import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Rounding.RadixModel
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.Operations

/-! Rounded real primitives and per-primitive safety, paper.tex W02.
The general operations accept any real rounding map. The finite-format wrappers
restrict inputs to stored values; their real outputs are again representable.
Division and square root require explicit evidence of their mathematical domains.
-/
namespace NumAnalysis206.Rounding

/-- One rounding of the exact sum. -/
def roundedAdd : (ℝ → ℝ) → ℝ → ℝ → ℝ := Specs.roundedAddValue

/-- One rounding of the exact difference. -/
def roundedSub : (ℝ → ℝ) → ℝ → ℝ → ℝ := Specs.roundedSubValue

/-- One rounding of the exact product. -/
def roundedMul : (ℝ → ℝ) → ℝ → ℝ → ℝ := Specs.roundedMulValue

/-- The divisor must be nonzero before division is performed. -/
noncomputable def roundedDiv : (ℝ → ℝ) → (a b : ℝ) → b ≠ 0 → ℝ := Specs.roundedDivValue

/-- Fused multiply-add: exact product and sum, then one rounding. -/
def roundedFMA : (ℝ → ℝ) → ℝ → ℝ → ℝ → ℝ := Specs.roundedFMAValue

/-- One rounding of the real square root of a nonnegative argument. -/
noncomputable def roundedSqrt : (ℝ → ℝ) → (a : ℝ) → 0 ≤ a → ℝ := Specs.roundedSqrtValue

/-- Separate multiplication and addition perform two roundings. -/
def separateMulAdd : (ℝ → ℝ) → ℝ → ℝ → ℝ → ℝ := Specs.separateMulAddValue

/-- Abstract relative model, assumed only at exact results in the specified domain.
It imposes no radix-format restriction and assumes no algorithm error bound. -/
def RelativeModel : (ℝ → ℝ) → ℝ → Set ℝ → Prop := Specs.RelativeModelValue

/-- Safety concerns the exact result, not the input magnitudes. -/
def SafeAdd : Set ℝ → ℝ → ℝ → Prop := Specs.SafeAddValue

def SafeSub : Set ℝ → ℝ → ℝ → Prop := Specs.SafeSubValue

def SafeMul : Set ℝ → ℝ → ℝ → Prop := Specs.SafeMulValue

def SafeDiv : Set ℝ → ℝ → ℝ → Prop := Specs.SafeDivValue

/-- An FMA requires only its complete exact result to belong to the domain. -/
def SafeFMA : Set ℝ → ℝ → ℝ → ℝ → Prop := Specs.SafeFMAValue

/-- The nonnegative radicand is required; the range check is on its square root. -/
def SafeSqrt : Set ℝ → ℝ → Prop := Specs.SafeSqrtValue

/-- Each of the two executed primitives requires its own exact-result check. -/
def SafeSeparateMulAdd : (ℝ → ℝ) → Set ℝ → ℝ → ℝ → ℝ → Prop := Specs.SafeSeparateMulAddValue

/-- Stored inputs are their exact real values, with representability evidence. -/
def Stored : RadixFormat → Type := Specs.StoredValue

noncomputable def formatAdd : (P : RadixFormat) → Stored P → Stored P → ℝ := Specs.formatAddValue

noncomputable def formatSub : (P : RadixFormat) → Stored P → Stored P → ℝ := Specs.formatSubValue

noncomputable def formatMul : (P : RadixFormat) → Stored P → Stored P → ℝ := Specs.formatMulValue

noncomputable def formatDiv : (P : RadixFormat) → (a b : Stored P) → b.val ≠ 0 → ℝ := Specs.formatDivValue

noncomputable def formatFMA : (P : RadixFormat) → Stored P → Stored P → Stored P → ℝ := Specs.formatFMAValue

noncomputable def formatSqrt : (P : RadixFormat) → (a : Stored P) → 0 ≤ a.val → ℝ := Specs.formatSqrtValue

theorem relativeModel_error (round : ℝ → ℝ) (u : ℝ) (D : Set ℝ)
    (h : RelativeModel round u D) (z : ℝ) (hz : z ∈ D) :
    ∃ δ : ℝ, round z = z * (1 + δ) ∧ |δ| ≤ u :=
  h.2.2 z hz

theorem format_outputs_mem (P : RadixFormat) :
    (∀ a b : Stored P, formatAdd P a b ∈ F P) ∧
    (∀ a b : Stored P, formatSub P a b ∈ F P) ∧
    (∀ a b : Stored P, formatMul P a b ∈ F P) ∧
    (∀ (a b : Stored P) (hb : b.val ≠ 0), formatDiv P a b hb ∈ F P) ∧
    (∀ a b c : Stored P, formatFMA P a b c ∈ F P) ∧
    (∀ (a : Stored P) (ha : 0 ≤ a.val), formatSqrt P a ha ∈ F P) := by
  exact ⟨fun a b => fl_mem_F P (a.val + b.val),
    fun a b => fl_mem_F P (a.val - b.val),
    fun a b => fl_mem_F P (a.val * b.val),
    fun a b _ => fl_mem_F P (a.val / b.val),
    fun a b c => fl_mem_F P (a.val * b.val + c.val),
    fun a _ => fl_mem_F P (Real.sqrt a.val)⟩

end NumAnalysis206.Rounding
