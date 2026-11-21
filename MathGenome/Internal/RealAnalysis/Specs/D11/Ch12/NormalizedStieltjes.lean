import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.ScalarStieltjesCorrespondence

/-! Normalized Stieltjes correspondence, paper.tex:3915–3980.
All scalar measures have the Borel domain. Variation is the upstream classical
partition supremum; initial variation includes the limiting value zero at −∞.
No identification of arbitrary almost-everywhere representatives is used. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Specs.D11.Ch12.NormalizedStieltjes
open Specs.D11.Ch12.ScalarStieltjesCorrespondence

def atom_formula : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (F : ℝ → E), NBV_value F → ∀ x,
      stieltjesMeasure_value F {x} = F x - Function.leftLim F x

def variation_interval : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (F : ℝ → E), NBV_value F → ∀ a b : ℝ, a ≤ b →
      (stieltjesMeasure_value F).variation (Ioc a b) = variation_value F a b

def variation_initial : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (F : ℝ → E), NBV_value F → ∀ x,
      (stieltjesMeasure_value F).variation (Iic x) = initialVariation_value F x

/-- An explicit presentation with the endpoint F(−∞)=0. -/
def initial_variation_with_zero : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] (F : ℝ → E), NBV_value F → ∀ x,
    initialVariation_value F x =
      ⨆ a : ℝ, ⨆ (_ : a ≤ x), ‖F a‖ₑ + variation_value F a x

def variation_global : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (F : ℝ → E), NBV_value F →
      (stieltjesMeasure_value F).variation univ = globalVariation_value F

def corresponding_variation : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (F : ℝ → E), NBV_value F → ∀ ν : VectorMeasure ℝ E,
      (∀ a b : ℝ, a < b → ν (Ioc a b) = F b - F a) →
      (∀ a b : ℝ, a ≤ b → ν.variation (Ioc a b) = variation_value F a b) ∧
      (∀ x : ℝ, ν.variation (Iic x) = initialVariation_value F x) ∧
      (∀ x : ℝ, ν {x} = F x - Function.leftLim F x)

def cumulative_variation : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (ν : VectorMeasure ℝ E), IsFiniteMeasure ν.variation →
      (∀ a b : ℝ, a ≤ b → ν.variation (Ioc a b) =
        variation_value (cumulative_value ν) a b) ∧
      (∀ x : ℝ, ν.variation (Iic x) = initialVariation_value (cumulative_value ν) x)

abbrev normalization_type := {E : Type*} → [NormedAddCommGroup E] →
  (ℝ → E) → ℝ → ℝ → ℝ → E

def compactNormalization_value : normalization_type :=
  fun F a b x => F (max a (min b x)) - F a

abbrev rightNormalization_type := {E : Type*} → [NormedAddCommGroup E] →
  (ℝ → E) → ℝ → E
noncomputable def rightNormalization_value : rightNormalization_type :=
  fun F x => F.rightLim x - limUnder atBot F

noncomputable def compactRightNormalization_value : normalization_type :=
  fun F a b => compactNormalization_value (compactNormalization_value F a b).rightLim a b

def compact_values : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) {a b : ℝ}, a ≤ b →
    (∀ x, x ≤ a → compactNormalization_value F a b x = 0) ∧
    (∀ x ∈ Icc a b, compactNormalization_value F a b x = F x - F a) ∧
    (∀ x, b ≤ x → compactNormalization_value F a b x = F b - F a)

def compact_continuous : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (F : ℝ → E) {a b : ℝ}, a < b → BV_value F a b → ContinuousOn F (Icc a b) →
      NBV_value (compactNormalization_value F a b) ∧
      Continuous (compactNormalization_value F a b) ∧
      (∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b →
        stieltjesMeasure_value (compactNormalization_value F a b) (Ioc u v) = F v - F u) ∧
      (stieltjesMeasure_value (compactNormalization_value F a b)).variation (Ioc a b) =
        variation_value F a b

def right_normalization : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (F : ℝ → E), GloballyBV_value F →
      NBV_value (rightNormalization_value F) ∧
      (∀ x, Tendsto F (𝓝[>] x) (𝓝 (F.rightLim x))) ∧
      (∀ u v : ℝ, u < v →
        stieltjesMeasure_value (rightNormalization_value F) (Ioc u v) =
          F.rightLim v - F.rightLim u) ∧
      (∀ x, stieltjesMeasure_value (rightNormalization_value F) {x} =
        F.rightLim x - F.leftLim x)

/-- First take the right-limit representative of the constant extension,
then subtract its left-endpoint value. The right endpoint retains F(b).
This states the normalization explicitly, without claiming pointwise equality
with an arbitrary BV generator. -/
def compact_right_normalization : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (F : ℝ → E) {a b : ℝ}, a < b → BV_value F a b →
      NBV_value (compactRightNormalization_value F a b) ∧
      (∀ x ∈ Ico a b, compactRightNormalization_value F a b x =
        F.rightLim x - F.rightLim a) ∧
      compactRightNormalization_value F a b b = F b - F.rightLim a ∧
      (∀ x, x ≤ a → compactRightNormalization_value F a b x = 0) ∧
      (∀ x, b ≤ x → compactRightNormalization_value F a b x = F b - F.rightLim a)

def compact_right_variation_bound : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (F : ℝ → E) {a b : ℝ}, a < b → BV_value F a b →
      globalVariation_value (compactRightNormalization_value F a b) ≤ variation_value F a b

def signed_bijection : Prop :=
  ∃ e : {F : ℝ → ℝ // NBV_value F} ≃ SignedMeasure ℝ,
    (∀ F x, e F (Iic x) = F.val x) ∧
    (∀ ν x, (e.symm ν).val x = ν (Iic x)) ∧
    (∀ F,
      (∀ a b : ℝ, a < b → e F (Ioc a b) = F.val b - F.val a) ∧
      (∀ x : ℝ, e F {x} = F.val x - Function.leftLim F.val x) ∧
      (∀ a b : ℝ, a ≤ b → (e F).variation (Ioc a b) = variation_value F.val a b) ∧
      (∀ x : ℝ, (e F).variation (Iic x) = initialVariation_value F.val x))

def complex_bijection : Prop :=
  ∃ e : {F : ℝ → ℂ // NBV_value F} ≃ ComplexMeasure ℝ,
    (∀ F x, e F (Iic x) = F.val x) ∧
    (∀ ν x, (e.symm ν).val x = ν (Iic x)) ∧
    (∀ F,
      (∀ a b : ℝ, a < b → e F (Ioc a b) = F.val b - F.val a) ∧
      (∀ x : ℝ, e F {x} = F.val x - Function.leftLim F.val x) ∧
      (∀ a b : ℝ, a ≤ b → (e F).variation (Ioc a b) = variation_value F.val a b) ∧
      (∀ x : ℝ, (e F).variation (Iic x) = initialVariation_value F.val x))

end Specs.D11.Ch12.NormalizedStieltjes
