import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral

/-!
Independent specification of K03.14.proper_definition, paper.tex:3248–3255.
The input is defined on exactly `[a,b] × T` (in curried form), for an arbitrary
set of real parameters. To use the shared Darboux API on ambient functions, a
section is extended by zero outside the closed integration interval. On that
interval it is exactly the input section; no regularity of this extension is
required. The integral family has as its domain the subtype of parameters with
Riemann-integrable sections. No continuity, uniformity, or integrability at other
parameters is assumed. The ordinary interval convention includes `a = b`.
-/

namespace Specs.SingleVariableAnalysis.Ch14.ProperDefinition

open _root_.SingleVariableAnalysis
open Specs.SingleVariableAnalysis.Ch01
open Specs.SingleVariableAnalysis.Ch08

abbrev sectionType := (k : ScalarKind) → {a b : ℝ} → {T : Set ℝ} →
  (Set.Icc a b → T → Scalar.scalarValue k) → T → ℝ → Scalar.scalarValue k

/-- Ambient representative of the section, agreeing at every point of `[a,b]`. -/
noncomputable def sectionValue : sectionType := by
  classical
  intro k a b T f t x
  exact if hx : x ∈ Set.Icc a b then f ⟨x, hx⟩ t else
    match k with
    | .real => (0 : ℝ)
    | .complex => (0 : ℂ)

abbrev sectionIntegrableType := (k : ScalarKind) → {a b : ℝ} → {T : Set ℝ} →
  (Set.Icc a b → T → Scalar.scalarValue k) → T → Prop

/-- This is the existing Riemann predicate, not a measure-integrability test. -/
def sectionIntegrableValue : sectionIntegrableType := fun k {a b} {_T} f t =>
  Integral.scalarIntegrableValue k (sectionValue k f t) a b

abbrev parametersType := (k : ScalarKind) → {a b : ℝ} → {T : Set ℝ} →
  (Set.Icc a b → T → Scalar.scalarValue k) → Set T

def parametersValue : parametersType := fun k {_a _b} {_T} f =>
  {t | sectionIntegrableValue k f t}

abbrev familyType := (k : ScalarKind) → {a b : ℝ} → {T : Set ℝ} →
  (f : Set.Icc a b → T → Scalar.scalarValue k) →
  parametersValue k f → Scalar.scalarValue k

noncomputable def familyValue : familyType := fun k {_a _b} {_T} f t =>
  Integral.scalarIntegralValue k (sectionValue k f t.val) t.property

def sectionOnInterval : Prop :=
  ∀ (k : ScalarKind) {a b : ℝ} {T : Set ℝ}
    (f : Set.Icc a b → T → Scalar.scalarValue k) (t : T) (x : Set.Icc a b),
    sectionValue k f t x.val = f x t

/-- The real domain consists of exactly the integrable parameters in `T`. -/
def domainExact : Prop :=
  ∀ (k : ScalarKind) {a b : ℝ} {T : Set ℝ}
    (f : Set.Icc a b → T → Scalar.scalarValue k) (t : ℝ),
    t ∈ (Subtype.val '' parametersValue k f) ↔
      ∃ ht : t ∈ T, sectionIntegrableValue k f ⟨t, ht⟩

def familyFormula : Prop :=
  ∀ (k : ScalarKind) {a b : ℝ} {T : Set ℝ}
    (f : Set.Icc a b → T → Scalar.scalarValue k) (t : T)
    (h : sectionIntegrableValue k f t),
    familyValue k f ⟨t, h⟩ = Integral.scalarIntegralValue k (sectionValue k f t) h

/-- The wording “if each section is integrable” gives a function on all of `T`. -/
def familyOnAll : Prop :=
  ∀ (k : ScalarKind) {a b : ℝ} {T : Set ℝ}
    (f : Set.Icc a b → T → Scalar.scalarValue k)
    (h : ∀ t : T, sectionIntegrableValue k f t),
    ∃ F : T → Scalar.scalarValue k, ∀ t : T,
      F t = familyValue k f ⟨t, h t⟩ ∧
      F t = Integral.scalarIntegralValue k (sectionValue k f t) (h t)

def domainAllIff : Prop :=
  ∀ (k : ScalarKind) {a b : ℝ} {T : Set ℝ}
    (f : Set.Icc a b → T → Scalar.scalarValue k),
    parametersValue k f = Set.univ ↔ ∀ t : T, sectionIntegrableValue k f t

/-- Singleton intervals inherit the upstream empty-sum convention. -/
def degenerateFamily : Prop :=
  ∀ (k : ScalarKind) (a : ℝ) {T : Set ℝ}
    (f : Set.Icc a a → T → Scalar.scalarValue k),
    parametersValue k f = Set.univ ∧
    ∀ t : parametersValue k f,
      familyValue k f t = (match k with
        | .real => (0 : ℝ)
        | .complex => (0 : ℂ))

end Specs.SingleVariableAnalysis.Ch14.ProperDefinition
