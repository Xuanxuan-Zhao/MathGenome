import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.ProductSigma
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.MeasurableMapTests

/-!
Independent statements for `D11.08.sections`, paper.tex:2516–2536.
The product is the shared ordinary product of measurable spaces. The left
section fixes an element of X and has domain Y; the right section fixes an
element of Y and has domain X. All parameters are allowed, including empty
factor spaces. There are no measures, completions, or exceptional parameters.

The general function statements allow an arbitrary measurable codomain.
The last three statements explicitly specialize to the paper's scalar Borel
codomains; EReal includes both infinities.
-/

open Set MeasurableSpace
open scoped MeasureTheory

universe u v w

namespace Specs.D11.Ch08.Sections

def set_section_left : Prop :=
  ∀ {X : Type u} {Y : Type v} (m : MeasurableSpace X) (n : MeasurableSpace Y)
    (E : Set (X × Y)),
    MeasurableSet[m.prod n] E → ∀ x : X, MeasurableSet[n] {y | (x, y) ∈ E}

def set_section_right : Prop :=
  ∀ {X : Type u} {Y : Type v} (m : MeasurableSpace X) (n : MeasurableSpace Y)
    (E : Set (X × Y)),
    MeasurableSet[m.prod n] E → ∀ y : Y, MeasurableSet[m] {x | (x, y) ∈ E}

def function_section_left : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type w}
    (m : MeasurableSpace X) (n : MeasurableSpace Y) (p : MeasurableSpace Z)
    (f : X × Y → Z),
    @Measurable (X × Y) Z (m.prod n) p f →
      ∀ x : X, @Measurable Y Z n p (fun y => f (x, y))

def function_section_right : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type w}
    (m : MeasurableSpace X) (n : MeasurableSpace Y) (p : MeasurableSpace Z)
    (f : X × Y → Z),
    @Measurable (X × Y) Z (m.prod n) p f →
      ∀ y : Y, @Measurable X Z m p (fun x => f (x, y))

def real_sections : Prop :=
  ∀ {X : Type u} {Y : Type v} (m : MeasurableSpace X) (n : MeasurableSpace Y)
    (f : X × Y → ℝ),
    @Measurable (X × Y) ℝ (m.prod n) (borel ℝ) f →
      (∀ x : X, @Measurable Y ℝ n (borel ℝ) (fun y => f (x, y))) ∧
      (∀ y : Y, @Measurable X ℝ m (borel ℝ) (fun x => f (x, y)))

def complex_sections : Prop :=
  ∀ {X : Type u} {Y : Type v} (m : MeasurableSpace X) (n : MeasurableSpace Y)
    (f : X × Y → ℂ),
    @Measurable (X × Y) ℂ (m.prod n) (borel ℂ) f →
      (∀ x : X, @Measurable Y ℂ n (borel ℂ) (fun y => f (x, y))) ∧
      (∀ y : Y, @Measurable X ℂ m (borel ℂ) (fun x => f (x, y)))

def extendedReal_sections : Prop :=
  ∀ {X : Type u} {Y : Type v} (m : MeasurableSpace X) (n : MeasurableSpace Y)
    (f : X × Y → EReal),
    @Measurable (X × Y) EReal (m.prod n) (borel EReal) f →
      (∀ x : X, @Measurable Y EReal n (borel EReal) (fun y => f (x, y))) ∧
      (∀ y : Y, @Measurable X EReal m (borel EReal) (fun x => f (x, y)))

end Specs.D11.Ch08.Sections
