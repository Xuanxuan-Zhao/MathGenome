import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HausdorffYoung
import MathGenome.Internal.FourierSobolev.Specs.P102.U3.TemperedFourier

/-! Independent statement of paper.tex:1126–1132. ExponentPair means
1 ≤ p ≤ 2 and 1/p + 1/q = 1 in ENNReal, including (1, ∞).
FourierFamily includes contractivity, the integral formula on every L¹
intersection, and compatibility on arbitrary intersections. The additional
clauses specify the bilinear distributional transform for every input and
identify the p=2 endpoint with the common Plancherel map. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace P102.Specs.U3.HausdorffYoung
open ExpandedFA.PartIV.HausdorffYoung

abbrev Family (d : ℕ) :=
  FourierFamily (volume : Measure (Euclidean d)) volume (fun f => 𝓕 f)

def two : ExponentPair := ⟨2, 2, by norm_num, le_rfl, inferInstance⟩

def Statement : Prop := ∀ d : ℕ, ∃ F : Family d,
  (∀ (a : ExponentPair) (f : Lp (α := Euclidean d) ℂ a.p volume),
    TemperedFourier.fourierStrong_value d (TemperedFourier.regularLp_value f) =
      TemperedFourier.regularLp_value (F.operator a f)) ∧
  (∀ f : Lp (α := Euclidean d) ℂ 2 volume,
    F.operator two f = Plancherel.fourierL2_value (Euclidean d) ℂ f)

end P102.Specs.U3.HausdorffYoung
