import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.ProductSigma

/-!
Independent statements of paper.tex:2533–2547, `D11.08.measurable_pair`.
All three spaces and their sigma-algebras are arbitrary. The target uses
the shared ordinary product `m.prod n`; there is no measure, completion,
topology, or nonemptiness assumption.
-/

universe u v w

namespace Specs.D11.Ch08.MeasurablePair

/-- The component criterion for an arbitrary map into the product. -/
def measurable_iff_components : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type w}
    (m : MeasurableSpace X) (n : MeasurableSpace Y) (p : MeasurableSpace Z)
    (h : Z → X × Y),
    @Measurable Z (X × Y) p (m.prod n) h ↔
      @Measurable Z X p m (fun z => (h z).1) ∧
      @Measurable Z Y p n (fun z => (h z).2)

/-- The source's displayed map `h(z) = (u(z), v(z))`. -/
def pair_iff : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type w}
    (m : MeasurableSpace X) (n : MeasurableSpace Y) (p : MeasurableSpace Z)
    (f : Z → X) (g : Z → Y),
    @Measurable Z (X × Y) p (m.prod n) (fun z => (f z, g z)) ↔
      @Measurable Z X p m f ∧ @Measurable Z Y p n g

/-- Fixing the first coordinate gives a measurable map from the second factor. -/
def fixed_left : Prop :=
  ∀ {X : Type u} {Y : Type v}
    (m : MeasurableSpace X) (n : MeasurableSpace Y) (x : X),
    @Measurable Y (X × Y) n (m.prod n) (fun y => (x, y))

/-- Fixing the second coordinate gives a measurable map from the first factor. -/
def fixed_right : Prop :=
  ∀ {X : Type u} {Y : Type v}
    (m : MeasurableSpace X) (n : MeasurableSpace Y) (y : Y),
    @Measurable X (X × Y) m (m.prod n) (fun x => (x, y))

end Specs.D11.Ch08.MeasurablePair
