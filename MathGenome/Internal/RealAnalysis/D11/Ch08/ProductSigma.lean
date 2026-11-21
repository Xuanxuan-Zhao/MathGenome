import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.ProductSigma
import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-!
The ordinary product sigma-algebra (paper.tex:2501–2515).
The native product is the supremum of the two projection comaps. Its
identification with rectangle generation is valid for arbitrary measurable
spaces: each full measurable-set family contains the whole space, so the
countable-spanning condition in the library's general generator theorem is
automatic. Neither nonemptiness nor any measure hypothesis is needed.
-/

open Set MeasurableSpace
open scoped MeasureTheory

universe u v

namespace D11.Ch08.ProductSigma

/-- The paper's ordinary product, using the shared native measurable spaces. -/
abbrev productSigma {X : Type u} {Y : Type v}
    (m : MeasurableSpace X) (n : MeasurableSpace Y) : MeasurableSpace (X × Y) :=
  m.prod n

theorem generated_rectangles : Specs.D11.Ch08.ProductSigma.generated_rectangles := by
  intro X Y m n
  let : MeasurableSpace X := m
  let : MeasurableSpace Y := n
  exact generateFrom_prod.symm

theorem rectangle_measurable : Specs.D11.Ch08.ProductSigma.rectangle_measurable := by
  intro X Y m n A B hA hB
  exact @MeasurableSet.prod X Y m n A B hA hB

theorem projections_measurable : Specs.D11.Ch08.ProductSigma.projections_measurable := by
  intro X Y m n
  exact ⟨@measurable_fst X Y m n, @measurable_snd X Y m n⟩

/-- Inclusion means inclusion of measurable subsets. Thus enlarging the
source sigma-algebra preserves measurability of both projections. -/
theorem le_iff_projections : Specs.D11.Ch08.ProductSigma.le_iff_projections := by
  intro X Y m n p
  change m.comap Prod.fst ⊔ n.comap Prod.snd ≤ p ↔ _
  rw [sup_le_iff, measurable_iff_comap_le, measurable_iff_comap_le]

theorem smallest : Specs.D11.Ch08.ProductSigma.smallest := by
  intro X Y m n
  exact ⟨projections_measurable m n,
    fun p hp => (le_iff_projections m n p).mpr hp⟩

end D11.Ch08.ProductSigma
