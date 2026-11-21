import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.MeasurableMapTests

/-! Independent statements for paper.tex:1204–1235 and 1463–1476.
The source sigma-algebra is arbitrary. Scalar targets carry their Borel
structures; the Euclidean target is the shared ℓ² space. The composition
statement has exactly one middle sigma-algebra. No measure or completion is
implicit. The indicator test records only the immediate boundary criterion;
the interval AC criterion and counterexample belong to Chapter 9. -/

open Set MeasurableSpace
open scoped MeasureTheory
universe u v w

namespace Specs.D11.Ch04.CompositionCoordinates

open _root_.D11.Ch03.BorelGenerators

def composition : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type w}
    (m : MeasurableSpace X) (n : MeasurableSpace Y) (p : MeasurableSpace Z)
    (f : X → Y) (g : Y → Z),
    @Measurable X Y m n f → @Measurable Y Z n p g →
      @Measurable X Z m p (g ∘ f)

/-- This general Borel statement includes real, complex, and extended-real
continuous scalar maps, with their ordinary topologies. -/
def continuous_borel : Prop :=
  ∀ {Y : Type v} {Z : Type w} [TopologicalSpace Y] [TopologicalSpace Z]
    (g : Y → Z), Continuous g → @Measurable Y Z (borel Y) (borel Z) g

def continuous_after_measurable : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace Y] [TopologicalSpace Z]
    (m : MeasurableSpace X) (f : X → Y) (g : Y → Z),
    @Measurable X Y m (borel Y) f → Continuous g →
      @Measurable X Z m (borel Z) (g ∘ f)

def euclidean_coordinates : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (d : ℕ) (f : X → Space d),
    @Measurable X (Space d) m (borel (Space d)) f ↔
      ∀ i : Fin d, @Measurable X ℝ m (borel ℝ) (fun x => f x i)

def complex_coordinates : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : X → ℂ),
    @Measurable X ℂ m (borel ℂ) f ↔
      @Measurable X ℝ m (borel ℝ) (fun x => (f x).re) ∧
      @Measurable X ℝ m (borel ℝ) (fun x => (f x).im)

/-- Euclidean tuples, including the empty tuple. Positive dimensions recover
exactly the paper's convention. -/
def finite_real_tuple : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (d : ℕ) (f : Fin d → X → ℝ),
    (∀ i, @Measurable X ℝ m (borel ℝ) (f i)) →
    @Measurable X (Space d) m (borel (Space d))
      (fun x => WithLp.toLp 2 (fun i => f i x))

def finite_complex_tuple : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (d : ℕ) (f : Fin d → X → ℂ),
    (∀ i, @Measurable X ℂ m (borel ℂ) (f i)) →
    @Measurable X (Fin d → ℂ) m (borel (Fin d → ℂ)) (fun x i => f i x)

def real_modulus : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : X → ℝ),
    @Measurable X ℝ m (borel ℝ) f →
    @Measurable X ℝ m (borel ℝ) (fun x => |f x|)

def complex_modulus : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : X → ℂ),
    @Measurable X ℂ m (borel ℂ) f →
    @Measurable X ℝ m (borel ℝ) (fun x => ‖f x‖)

def complex_conjugation : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : X → ℂ),
    @Measurable X ℂ m (borel ℂ) f →
    @Measurable X ℂ m (borel ℂ) (fun x => star (f x))

/-- All target indicators are tested with the same specified target
sigma-algebra. The equivalence includes the required necessary condition. -/
def indicator_test : Prop :=
  ∀ {X : Type u} {Y : Type v} (m : MeasurableSpace X) (n : MeasurableSpace Y)
    (f : X → Y),
    (∀ A : Set Y, MeasurableSet[n] A →
      @Measurable X ℝ m (borel ℝ) ((A.indicator (fun _ => (1 : ℝ))) ∘ f)) ↔
    ∀ A : Set Y, MeasurableSet[n] A → MeasurableSet[m] (f ⁻¹' A)

end Specs.D11.Ch04.CompositionCoordinates
