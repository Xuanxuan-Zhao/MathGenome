import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.LpDefinition
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.RCLike.Basic

/-! Independent interface for paper.tex:3361–3375.

The carrier explicitly requires ordinary measurability on the original sigma-algebra.
`raw_finite` and `raw_top` below require its identification with the previously
fixed raw spaces. The quotient relation is literally zero measure of the
inequality set; this set is measurable for these scalar representatives.
The scalar field can be either real or complex, and the measure is arbitrary.
No completeness, finiteness, sigma-finiteness, or local-null convention is used.
-/
open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace Specs.D11.Ch10.QuotientConstruction

variable {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- Ordinary measurable representatives of finite native p-norm.
The exact source-space comparisons are separate obligations below. -/
def rawSpace (μ : Measure X) (p : ℝ≥0∞) : Submodule 𝕜 (X → 𝕜) where
  carrier := {f | Measurable f ∧ MemLp f p μ}
  zero_mem' := ⟨measurable_const, MemLp.zero⟩
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := fun c _f hf => ⟨measurable_const.smul hf.1, hf.2.const_smul c⟩

abbrev Raw (μ : Measure X) (p : ℝ≥0∞) := ↥(rawSpace (𝕜 := 𝕜) μ p)

def nullRelation (μ : Measure X) (p : ℝ≥0∞) (f g : Raw (𝕜 := 𝕜) μ p) : Prop :=
  μ {x | f.val x ≠ g.val x} = 0

/-- Only the elementary filter equivalence proof is used to form the setoid. -/
def rawSetoid (μ : Measure X) (p : ℝ≥0∞) : Setoid (Raw (𝕜 := 𝕜) μ p) where
  r := nullRelation μ p
  iseqv := by
    have h (f g : Raw (𝕜 := 𝕜) μ p) : nullRelation μ p f g ↔
        (f.val =ᵐ[μ] g.val) := by
      change _ ↔ ∀ᵐ x ∂μ, f.val x = g.val x
      rw [ae_iff]
      rfl
    exact ⟨fun f => (h f f).mpr Filter.EventuallyEq.rfl,
      fun {f g} hfg => (h g f).mpr ((h f g).mp hfg).symm,
      fun {f g k} hfg hgk => (h f k).mpr (((h f g).mp hfg).trans ((h g k).mp hgk))⟩

/-- The actual quotient of the ordinary measurable raw functions. -/
def QuotientLp (μ : Measure X) (p : ℝ≥0∞) := Quotient (rawSetoid (𝕜 := 𝕜) μ p)

def classOf {μ : Measure X} {p : ℝ≥0∞} (f : Raw (𝕜 := 𝕜) μ p) :
    QuotientLp (𝕜 := 𝕜) μ p := Quotient.mk (rawSetoid μ p) f

/-- The independently specified value of the public quotient type. -/
def quotientLp_type := ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → ℝ≥0∞ → Type u

def quotientLp_value : quotientLp_type.{u} := @QuotientLp

/-- The source norm, using the earlier integral and essential-bound definitions. -/
def sourceNorm (μ : Measure X) (p : ℝ≥0∞) (f : X → 𝕜) : ℝ≥0∞ :=
  if p = ∞ then Specs.D11.Ch04.EssentialBounds.essentialSupNorm_value μ f
  else Specs.D11.Ch10.LpDefinition.powerNorm_value μ p.toReal f

-- Each assertion quantifies over the whole original exponent range.
def raw_finite : Prop := ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ) (_hp : 1 ≤ p)
  (f : X → 𝕜),
  f ∈ rawSpace μ (ENNReal.ofReal p) ↔ f ∈ Specs.D11.Ch10.LpDefinition.rawLp_value μ p

def raw_top : Prop := ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜),
  f ∈ rawSpace μ ∞ ↔ f ∈ Specs.D11.Ch10.LpDefinition.rawLInfinity_value μ

def sourceNorm_bridge : Prop := ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ≥0∞), 1 ≤ p →
  ∀ f : Raw (𝕜 := 𝕜) μ p, sourceNorm μ p f.val = eLpNorm f.val p μ

def measurable_exception : Prop := ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ≥0∞)
  (f g : Raw (𝕜 := 𝕜) μ p), MeasurableSet {x | f.val x ≠ g.val x}

def ordinary_relation : Prop := ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ≥0∞)
  (f g : Raw (𝕜 := 𝕜) μ p), nullRelation μ p f g ↔
    Specs.D11.Ch04.AeCommonException.aeEq_value μ f.val g.val

def relation_equivalence : Prop := ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ≥0∞),
  Equivalence (nullRelation (𝕜 := 𝕜) μ p)

def operations_compatible : Prop := ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ≥0∞)
  (f f' g g' : Raw (𝕜 := 𝕜) μ p), nullRelation μ p f f' → nullRelation μ p g g' →
  nullRelation μ p (f + g) (f' + g') ∧
    ∀ c : 𝕜, nullRelation μ p (c • f) (c • f')

def norm_congr : Prop := ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ≥0∞), 1 ≤ p →
  ∀ f g : Raw (𝕜 := 𝕜) μ p, nullRelation μ p f g →
    sourceNorm μ p f.val = sourceNorm μ p g.val

/-- Full normed-space construction with representative formulas and the required
linear isometric equivalence to native Lp. The structures are conclusions. -/
def quotient_construction : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ≥0∞)
    [Fact (1 ≤ p)],
    ∃ G : NormedAddCommGroup (QuotientLp (𝕜 := 𝕜) μ p),
    letI := G
    ∃ V : NormedSpace 𝕜 (QuotientLp (𝕜 := 𝕜) μ p),
    letI := V
    ∃ F : QuotientLp (𝕜 := 𝕜) μ p ≃ₗᵢ[𝕜] Lp 𝕜 p μ,
      (∀ f : Raw (𝕜 := 𝕜) μ p, F (classOf f) = f.property.2.toLp f.val) ∧
      (∀ f g : Raw (𝕜 := 𝕜) μ p, classOf (f + g) = classOf f + classOf g) ∧
      (∀ (c : 𝕜) (f : Raw (𝕜 := 𝕜) μ p), classOf (c • f) = c • classOf f) ∧
      (classOf (0 : Raw (𝕜 := 𝕜) μ p) = 0) ∧
      (∀ f : Raw (𝕜 := 𝕜) μ p, ‖classOf f‖ = (sourceNorm μ p f.val).toReal) ∧
      (∀ f g : Raw (𝕜 := 𝕜) μ p, classOf f = classOf g ↔ nullRelation μ p f g)

end Specs.D11.Ch10.QuotientConstruction
