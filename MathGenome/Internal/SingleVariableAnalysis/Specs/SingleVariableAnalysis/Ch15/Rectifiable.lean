import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.C1Variation

/-! Independent specification of K03.15.rectifiable, paper.tex:3665–3669.

An ambient function represents a path on the ordered closed interval precisely
when its restriction is continuous. Length is defined only with such a path
certificate, by the extended nonnegative supremum of the inscribed polygonal
chord sums. Rectifiability includes continuity as well as finite length.
The normed real vector space generality includes both manuscript scalars ℝ and ℂ;
all derivatives use real increments, with derivatives within the closed interval
encoding the available endpoint derivatives. The integral below is the project's
proper Darboux integral, with integrability proved in the conclusion.
-/
namespace Specs.SingleVariableAnalysis.Ch15.Rectifiable
open _root_.SingleVariableAnalysis.Riemann
open Specs.SingleVariableAnalysis.Ch08
open scoped BigOperators ENNReal
universe u

abbrev continuousPathType := {E : Type u} → [NormedAddCommGroup E] →
  (ℝ → E) → ℝ → ℝ → Prop

def continuousPathValue : continuousPathType := fun f a b =>
  a ≤ b ∧ ContinuousOn f (Set.Icc a b)

abbrev pathLengthType := {E : Type u} → [NormedAddCommGroup E] →
  (f : ℝ → E) → (a b : ℝ) → continuousPathValue f a b → ℝ≥0∞

noncomputable def pathLengthValue : pathLengthType := fun f a b _ =>
  ⨆ P : PartitionData a b,
    ∑ i : Fin P.n, ENNReal.ofReal ‖f (P.point i.succ) - f (P.point i.castSucc)‖

abbrev rectifiableType := {E : Type u} → [NormedAddCommGroup E] →
  (ℝ → E) → ℝ → ℝ → Prop

def rectifiableValue : rectifiableType := fun f a b =>
  ∃ hp : continuousPathValue f a b, pathLengthValue f a b hp < ⊤

def lengthEqVariation : Prop := ∀ {E : Type u} [NormedAddCommGroup E]
  (f : ℝ → E) (a b : ℝ) (hp : continuousPathValue f a b),
  pathLengthValue f a b hp = Variation.totalVariationValue f a b

def rectifiableIffContinuousBV : Prop := ∀ {E : Type u} [NormedAddCommGroup E]
  (f : ℝ → E) (a b : ℝ),
  rectifiableValue f a b ↔
    continuousPathValue f a b ∧ Variation.boundedVariationValue f a b

def rectifiableIffFiniteLength : Prop := ∀ {E : Type u} [NormedAddCommGroup E]
  (f : ℝ → E) (a b : ℝ) (hp : continuousPathValue f a b),
  rectifiableValue f a b ↔ pathLengthValue f a b hp < ⊤

def degenerateLength : Prop := ∀ {E : Type u} [NormedAddCommGroup E]
  (f : ℝ → E) (a : ℝ) (hp : continuousPathValue f a a),
  pathLengthValue f a a hp = 0

/-- No discontinuous function represents a path or a rectifiable path, even
if it has bounded variation. No point values are silently replaced by limits. -/
def discontinuousNotPath : Prop := ∀ {E : Type u} [NormedAddCommGroup E]
  (f : ℝ → E) (a b : ℝ), ¬ ContinuousOn f (Set.Icc a b) →
    ¬ continuousPathValue f a b ∧ ¬ rectifiableValue f a b

/-- C¹ functions yield continuous rectifiable paths with length equal to the
proper integral of speed, including the singleton interval. -/
def c1PathLength : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : ℝ → E) (a b : ℝ), a ≤ b →
    (∀ x ∈ Set.Icc a b, HasDerivWithinAt f (g x) (Set.Icc a b) x) →
    ContinuousOn g (Set.Icc a b) →
    ∃ hp : continuousPathValue f a b,
      ∃ hn : Integral.realIntegrableValue (fun x => ‖g x‖) a b,
        pathLengthValue f a b hp =
          ENNReal.ofReal (Integral.realIntegralValue (fun x => ‖g x‖) hn) ∧
        rectifiableValue f a b

end Specs.SingleVariableAnalysis.Ch15.Rectifiable
