import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.SetSystems
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.BorelGenerators
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-! Independent statements for paper.tex:1174–1203. The source measurable
structures are arbitrary, including on empty types. Scalar targets have their
Borel structures, and EReal includes both infinities. The trace is the shared
native subtype/comap structure, without any completion. -/

open Set MeasurableSpace
open scoped MeasureTheory
universe u v
namespace Specs.D11.Ch04.MeasurableMapTests

def measurableMap_type :=
  ∀ {X : Type u} {Y : Type v}, MeasurableSpace X → MeasurableSpace Y → (X → Y) → Prop

def measurableMap_value : measurableMap_type.{u,v} :=
  fun {_ _} m n f => @Measurable _ _ m n f

def realMeasurable_type := ∀ {X : Type u}, MeasurableSpace X → (X → ℝ) → Prop

def realMeasurable_value : realMeasurable_type.{u} :=
  fun {_} m f => @Measurable _ ℝ m (borel ℝ) f

def complexMeasurable_type := ∀ {X : Type u}, MeasurableSpace X → (X → ℂ) → Prop

def complexMeasurable_value : complexMeasurable_type.{u} :=
  fun {_} m f => @Measurable _ ℂ m (borel ℂ) f

def extendedRealMeasurable_type := ∀ {X : Type u}, MeasurableSpace X → (X → EReal) → Prop

def extendedRealMeasurable_value : extendedRealMeasurable_type.{u} :=
  fun {_} m f => @Measurable _ EReal m (borel EReal) f

def traceMeasurableMap_type :=
  ∀ {X : Type u} {Y : Type v}, MeasurableSpace X → MeasurableSpace Y →
    (E : Set X) → (E → Y) → Prop

def traceMeasurableMap_value : traceMeasurableMap_type.{u,v} :=
  fun {_ _} m n E f => @Measurable E _ (m.comap Subtype.val) n f

def map_iff : Prop :=
  ∀ {X : Type u} {Y : Type v} (m : MeasurableSpace X) (n : MeasurableSpace Y) (f : X → Y),
    @Measurable X Y m n f ↔ ∀ B : Set Y, MeasurableSet[n] B → MeasurableSet[m] (f ⁻¹' B)

def trace_iff : Prop :=
  ∀ {X : Type u} {Y : Type v} (m : MeasurableSpace X) (n : MeasurableSpace Y)
    (E : Set X), MeasurableSet[m] E → ∀ f : E → Y,
    @Measurable E Y (m.comap Subtype.val) n f ↔
      ∀ B : Set Y, MeasurableSet[n] B →
        MeasurableSet[m] ((Subtype.val : E → X) '' (f ⁻¹' B))

def generator_test : Prop :=
  ∀ {X : Type u} {Y : Type v} (m : MeasurableSpace X) (n : MeasurableSpace Y)
    (C : Set (Set Y)) (f : X → Y), n = generateFrom C →
    (@Measurable X Y m n f ↔ ∀ B ∈ C, MeasurableSet[m] (f ⁻¹' B))

def real_lower_strict : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : X → ℝ),
    @Measurable X ℝ m (borel ℝ) f ↔
      ∀ a : ℝ, MeasurableSet[m] {x | f x < a}

def real_lower_strict_rat : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : X → ℝ),
    @Measurable X ℝ m (borel ℝ) f ↔
      ∀ q : ℚ, MeasurableSet[m] {x | f x < (q : ℝ)}

def real_lower_closed : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : X → ℝ),
    @Measurable X ℝ m (borel ℝ) f ↔
      ∀ a : ℝ, MeasurableSet[m] {x | f x ≤ a}

def real_lower_closed_rat : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : X → ℝ),
    @Measurable X ℝ m (borel ℝ) f ↔
      ∀ q : ℚ, MeasurableSet[m] {x | f x ≤ (q : ℝ)}

def real_upper_strict : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : X → ℝ),
    @Measurable X ℝ m (borel ℝ) f ↔
      ∀ a : ℝ, MeasurableSet[m] {x | f x > a}

def real_upper_strict_rat : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : X → ℝ),
    @Measurable X ℝ m (borel ℝ) f ↔
      ∀ q : ℚ, MeasurableSet[m] {x | f x > (q : ℝ)}

def real_upper_closed : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : X → ℝ),
    @Measurable X ℝ m (borel ℝ) f ↔
      ∀ a : ℝ, MeasurableSet[m] {x | f x ≥ a}

def real_upper_closed_rat : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : X → ℝ),
    @Measurable X ℝ m (borel ℝ) f ↔
      ∀ q : ℚ, MeasurableSet[m] {x | f x ≥ (q : ℝ)}

def ereal_lower_strict : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : X → EReal),
    @Measurable X EReal m (borel EReal) f ↔
      ∀ a : EReal, MeasurableSet[m] {x | f x < a}

def ereal_lower_strict_rat : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : X → EReal),
    @Measurable X EReal m (borel EReal) f ↔
      ∀ q : ℚ, MeasurableSet[m] {x | f x < ((q : ℝ) : EReal)}

def ereal_lower_closed : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : X → EReal),
    @Measurable X EReal m (borel EReal) f ↔
      ∀ a : EReal, MeasurableSet[m] {x | f x ≤ a}

def ereal_lower_closed_rat : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : X → EReal),
    @Measurable X EReal m (borel EReal) f ↔
      ∀ q : ℚ, MeasurableSet[m] {x | f x ≤ ((q : ℝ) : EReal)}

def ereal_upper_strict : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : X → EReal),
    @Measurable X EReal m (borel EReal) f ↔
      ∀ a : EReal, MeasurableSet[m] {x | f x > a}

def ereal_upper_strict_rat : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : X → EReal),
    @Measurable X EReal m (borel EReal) f ↔
      ∀ q : ℚ, MeasurableSet[m] {x | f x > ((q : ℝ) : EReal)}

def ereal_upper_closed : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : X → EReal),
    @Measurable X EReal m (borel EReal) f ↔
      ∀ a : EReal, MeasurableSet[m] {x | f x ≥ a}

def ereal_upper_closed_rat : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : X → EReal),
    @Measurable X EReal m (borel EReal) f ↔
      ∀ q : ℚ, MeasurableSet[m] {x | f x ≥ ((q : ℝ) : EReal)}

end Specs.D11.Ch04.MeasurableMapTests
