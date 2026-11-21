import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.SetSystems

/-!
Independent specification of paper.tex:2501–2515 (`D11.08.product_sigma`).
The factors are arbitrary measurable spaces, including empty spaces. The
canonical native product is used; rectangle generation and the least-property
below identify it with the paper's definition. No measure or completion occurs.
-/

open Set MeasurableSpace
open scoped MeasureTheory

universe u v

namespace Specs.D11.Ch08.ProductSigma

def productSigma_type :=
  ∀ {X : Type u} {Y : Type v},
    MeasurableSpace X → MeasurableSpace Y → MeasurableSpace (X × Y)

def productSigma_value : productSigma_type.{u, v} :=
  fun {_ _} m n => m.prod n

/-- Rectangles here are subsets of `X × Y`, obtained as the image of
the two families of measurable subsets under Cartesian product. -/
def generated_rectangles : Prop :=
  ∀ {X : Type u} {Y : Type v} (m : MeasurableSpace X) (n : MeasurableSpace Y),
    m.prod n = generateFrom
      (Set.image2 (fun (A : Set X) (B : Set Y) => A ×ˢ B)
        {A | MeasurableSet[m] A} {B | MeasurableSet[n] B})

def rectangle_measurable : Prop :=
  ∀ {X : Type u} {Y : Type v} (m : MeasurableSpace X) (n : MeasurableSpace Y)
    {A : Set X} {B : Set Y},
    MeasurableSet[m] A → MeasurableSet[n] B → MeasurableSet[m.prod n] (A ×ˢ B)

def projections_measurable : Prop :=
  ∀ {X : Type u} {Y : Type v} (m : MeasurableSpace X) (n : MeasurableSpace Y),
    @Measurable (X × Y) X (m.prod n) m Prod.fst ∧
    @Measurable (X × Y) Y (m.prod n) n Prod.snd

def le_iff_projections : Prop :=
  ∀ {X : Type u} {Y : Type v} (m : MeasurableSpace X) (n : MeasurableSpace Y)
    (p : MeasurableSpace (X × Y)),
    m.prod n ≤ p ↔
      @Measurable (X × Y) X p m Prod.fst ∧
      @Measurable (X × Y) Y p n Prod.snd

def smallest : Prop :=
  ∀ {X : Type u} {Y : Type v} (m : MeasurableSpace X) (n : MeasurableSpace Y),
    IsLeast {p : MeasurableSpace (X × Y) |
      @Measurable (X × Y) X p m Prod.fst ∧
      @Measurable (X × Y) Y p n Prod.snd} (m.prod n)

end Specs.D11.Ch08.ProductSigma
