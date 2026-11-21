import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.CantorDigitSurjection
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.HausdorffOuterMeasure

/-!
Independent statement of paper.tex:6156–6163, D11.22.cantor_exact_mass.
The set is the shared middle-thirds Cantor set in the ordinary real-line
metric, and the exponent is log 2 / log 3. The shared outer measure uses
coefficient-one diameter costs and arbitrary at most countable covers.
No measurability condition is imposed on covering sets or their images.
-/

noncomputable section

namespace Specs.D11.Ch22.CantorExactMass

def exact_mass : Prop :=
  HausdorffOuterMeasure.outerMeasureValue
    (Real.toNNReal CantorDigitSurjection.alpha_value) Ch03.CantorSet.C_value = 1

end Specs.D11.Ch22.CantorExactMass
