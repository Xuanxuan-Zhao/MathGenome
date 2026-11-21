import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.RadixModel
import Mathlib.Analysis.Real.Sqrt

/-! Independent specifications for paper.tex, Definition W02 and its following
paragraph (lines 141–157), using the global stored-real convention (lines 65–69).
The relative bound is an abstract predicate, not an assertion that an arbitrary
rounding function satisfies it. Establishing it for the finite normal-safe domain
belongs to the separately allocated normal-rounding theorem.
-/
namespace NumAnalysis206.Rounding.Specs

/-- One rounding of the exact sum. -/
abbrev roundedAddType := (ℝ → ℝ) → ℝ → ℝ → ℝ
def roundedAddValue : roundedAddType := fun round a b => round (a + b)

/-- One rounding of the exact difference. -/
abbrev roundedSubType := (ℝ → ℝ) → ℝ → ℝ → ℝ
def roundedSubValue : roundedSubType := fun round a b => round (a - b)

/-- One rounding of the exact product. -/
abbrev roundedMulType := (ℝ → ℝ) → ℝ → ℝ → ℝ
def roundedMulValue : roundedMulType := fun round a b => round (a * b)

/-- The divisor must be nonzero before division is performed. -/
abbrev roundedDivType := (ℝ → ℝ) → (a b : ℝ) → b ≠ 0 → ℝ
noncomputable def roundedDivValue : roundedDivType := fun round a b _ => round (a / b)

/-- Fused multiply-add: exact product and sum, then one rounding. -/
abbrev roundedFMAType := (ℝ → ℝ) → ℝ → ℝ → ℝ → ℝ
def roundedFMAValue : roundedFMAType := fun round a b c => round (a * b + c)

/-- One rounding of the real square root of a nonnegative argument. -/
abbrev roundedSqrtType := (ℝ → ℝ) → (a : ℝ) → 0 ≤ a → ℝ
noncomputable def roundedSqrtValue : roundedSqrtType := fun round a _ => round (Real.sqrt a)

/-- Separate multiplication and addition perform two roundings. -/
abbrev separateMulAddType := (ℝ → ℝ) → ℝ → ℝ → ℝ → ℝ
def separateMulAddValue : separateMulAddType := fun round a b c => round (round (a * b) + c)

/-- Abstract relative model, assumed only at exact results in the specified domain.
It imposes no radix-format restriction and assumes no algorithm error bound. -/
abbrev RelativeModelType := (ℝ → ℝ) → ℝ → Set ℝ → Prop
def RelativeModelValue : RelativeModelType := fun round u D => 0 ≤ u ∧ u < 1 ∧
    ∀ z ∈ D, ∃ δ : ℝ, round z = z * (1 + δ) ∧ |δ| ≤ u

/-- Safety concerns the exact result, not the input magnitudes. -/
abbrev SafeAddType := Set ℝ → ℝ → ℝ → Prop
def SafeAddValue : SafeAddType := fun D a b => a + b ∈ D

abbrev SafeSubType := Set ℝ → ℝ → ℝ → Prop
def SafeSubValue : SafeSubType := fun D a b => a - b ∈ D

abbrev SafeMulType := Set ℝ → ℝ → ℝ → Prop
def SafeMulValue : SafeMulType := fun D a b => a * b ∈ D

abbrev SafeDivType := Set ℝ → ℝ → ℝ → Prop
def SafeDivValue : SafeDivType := fun D a b => b ≠ 0 ∧ a / b ∈ D

/-- An FMA requires only its complete exact result to belong to the domain. -/
abbrev SafeFMAType := Set ℝ → ℝ → ℝ → ℝ → Prop
def SafeFMAValue : SafeFMAType := fun D a b c => a * b + c ∈ D

/-- The nonnegative radicand is required; the range check is on its square root. -/
abbrev SafeSqrtType := Set ℝ → ℝ → Prop
def SafeSqrtValue : SafeSqrtType := fun D a => 0 ≤ a ∧ Real.sqrt a ∈ D

/-- Each of the two executed primitives requires its own exact-result check. -/
abbrev SafeSeparateMulAddType := (ℝ → ℝ) → Set ℝ → ℝ → ℝ → ℝ → Prop
def SafeSeparateMulAddValue : SafeSeparateMulAddType := fun round D a b c => a * b ∈ D ∧ round (a * b) + c ∈ D

/-- Stored inputs are their exact real values, with representability evidence. -/
abbrev StoredType := RadixFormat → Type
def StoredValue : StoredType := fun P => {x : ℝ // x ∈ FValue P}

abbrev formatAddType := (P : RadixFormat) → StoredValue P → StoredValue P → ℝ
noncomputable def formatAddValue : formatAddType := fun P a b => roundedAddValue (flValue P) a.val b.val

abbrev formatSubType := (P : RadixFormat) → StoredValue P → StoredValue P → ℝ
noncomputable def formatSubValue : formatSubType := fun P a b => roundedSubValue (flValue P) a.val b.val

abbrev formatMulType := (P : RadixFormat) → StoredValue P → StoredValue P → ℝ
noncomputable def formatMulValue : formatMulType := fun P a b => roundedMulValue (flValue P) a.val b.val

abbrev formatDivType := (P : RadixFormat) → (a b : StoredValue P) → b.val ≠ 0 → ℝ
noncomputable def formatDivValue : formatDivType := fun P a b hb => roundedDivValue (flValue P) a.val b.val hb

abbrev formatFMAType := (P : RadixFormat) → StoredValue P → StoredValue P → StoredValue P → ℝ
noncomputable def formatFMAValue : formatFMAType := fun P a b c => roundedFMAValue (flValue P) a.val b.val c.val

abbrev formatSqrtType := (P : RadixFormat) → (a : StoredValue P) → 0 ≤ a.val → ℝ
noncomputable def formatSqrtValue : formatSqrtType := fun P a ha => roundedSqrtValue (flValue P) a.val ha

/-- Extraction at one safe primitive; all range assumptions remain explicit. -/
def relativeModel_error : Prop :=
  ∀ (round : ℝ → ℝ) (u : ℝ) (D : Set ℝ), RelativeModelValue round u D →
    ∀ z ∈ D, ∃ δ : ℝ, round z = z * (1 + δ) ∧ |δ| ≤ u

/-- Outputs of all finite-format primitives are representable. -/
def format_outputs_mem : Prop := ∀ (P : RadixFormat),
  (∀ a b : StoredValue P, formatAddValue P a b ∈ FValue P) ∧
  (∀ a b : StoredValue P, formatSubValue P a b ∈ FValue P) ∧
  (∀ a b : StoredValue P, formatMulValue P a b ∈ FValue P) ∧
  (∀ (a b : StoredValue P) (hb : b.val ≠ 0), formatDivValue P a b hb ∈ FValue P) ∧
  (∀ a b c : StoredValue P, formatFMAValue P a b c ∈ FValue P) ∧
  (∀ (a : StoredValue P) (ha : 0 ≤ a.val), formatSqrtValue P a ha ∈ FValue P)

end NumAnalysis206.Rounding.Specs
