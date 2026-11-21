import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.RectifiableStieltjes
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! Independent statements for paper.tex:808–822 and its finite-union
consequence used in the finite-cycle Cauchy theorem. The paths and finite
polygonal length predicate are the canonical upstream objects. `volume` on
`ℂ` is planar Lebesgue measure, with the standard real inner product. -/

noncomputable section
open Set MeasureTheory

namespace Specs.D12Complex.Ch03.RectifiableTraceNull
open _root_.D12Complex _root_.D12Complex.Stieltjes

/-- No positive-length or nondegeneracy hypothesis is imposed. -/
def trace_volume_zero_type : Prop :=
  ∀ γ : ComplexPath, Rectifiable γ → volume γ.trace = 0

def trace_interior_empty_type : Prop :=
  ∀ γ : ComplexPath, Rectifiable γ → interior γ.trace = ∅

/-- The index set may be empty and the paths need not be distinct. -/
def finite_union_volume_zero_type : Prop :=
  ∀ {ι : Type} (s : Finset ι) (γ : ι → ComplexPath),
    (∀ i ∈ s, Rectifiable (γ i)) → volume (⋃ i ∈ s, (γ i).trace) = 0

def finite_union_interior_empty_type : Prop :=
  ∀ {ι : Type} (s : Finset ι) (γ : ι → ComplexPath),
    (∀ i ∈ s, Rectifiable (γ i)) → interior (⋃ i ∈ s, (γ i).trace) = ∅

end Specs.D12Complex.Ch03.RectifiableTraceNull
