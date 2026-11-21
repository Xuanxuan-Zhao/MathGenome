import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.OneSided
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Complex.Basic

/-!
Independent specification of K03.02.big_o (paper.tex:432–437).
A filter fixes the common approach and domain. The norm is absolute value for
ℝ and modulus for ℂ; the statements are proved for normed fields, which include
both source scalar types. The five real approaches are also given explicitly.
No nonvanishing is required by the inequality definitions. Only the quotient
converses require an eventually nonzero denominator. Constants are finite reals.
-/

namespace Specs.SingleVariableAnalysis.Ch02.BigO

open Filter
open scoped Topology
open _root_.SingleVariableAnalysis
universe u v

def approachFilterType : Type := Set ℝ → RealApproach → Filter ℝ

def approachFilterValue : approachFilterType := fun E q => match q with
  | .punctured a => nhdsWithin a (E \ {a})
  | .right a => nhdsWithin a (E ∩ Set.Ioi a)
  | .left a => nhdsWithin a (E ∩ Set.Iio a)
  | .posInfinity => atTop ⊓ 𝓟 E
  | .negInfinity => atBot ⊓ 𝓟 E

def scalarBigOType : Type (max (u + 1) (v + 1)) :=
  {X : Type u} → {K : Type v} → [NormedField K] → Filter X → (X → K) → (X → K) → Prop

def scalarBigOValue : scalarBigOType.{u,v} := fun l f g =>
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in l, ‖f x‖ ≤ C * ‖g x‖

def scalarLittleOType : Type (max (u + 1) (v + 1)) :=
  {X : Type u} → {K : Type v} → [NormedField K] → Filter X → (X → K) → (X → K) → Prop

def scalarLittleOValue : scalarLittleOType.{u,v} := fun l f g =>
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x in l, ‖f x‖ ≤ ε * ‖g x‖

def eventuallyBoundedRatioType : Type (max (u + 1) (v + 1)) :=
  {X : Type u} → {K : Type v} → [NormedField K] → Filter X → (X → K) → (X → K) → Prop

def eventuallyBoundedRatioValue : eventuallyBoundedRatioType.{u,v} := fun l f g =>
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in l, ‖f x / g x‖ ≤ C

def approachEventuallyFilterIff : Prop :=
  ∀ (E : Set ℝ) (q : RealApproach) (P : ℝ → Prop),
    OneSided.approachEventuallyValue E q P ↔ ∀ᶠ x in approachFilterValue E q, P x

def scalarBigOIffIsBigO : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f g : X → K),
    scalarBigOValue l f g ↔ Asymptotics.IsBigO l f g

def scalarLittleOIffIsLittleO : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f g : X → K),
    scalarLittleOValue l f g ↔ Asymptotics.IsLittleO l f g

def scalarLittleOIsBigO : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f g : X → K),
    scalarLittleOValue l f g → scalarBigOValue l f g

def scalarBigOEventuallyZero : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f g : X → K),
    scalarBigOValue l f g → ∀ᶠ x in l, g x = 0 → f x = 0

def scalarLittleOEventuallyZero : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f g : X → K),
    scalarLittleOValue l f g → ∀ᶠ x in l, g x = 0 → f x = 0

def scalarBigOIffBoundedRatio : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f g : X → K),
    (∀ᶠ x in l, g x ≠ 0) →
      (scalarBigOValue l f g ↔ eventuallyBoundedRatioValue l f g)

def scalarLittleOIffRatioTendsto : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f g : X → K),
    (∀ᶠ x in l, g x ≠ 0) →
      (scalarLittleOValue l f g ↔ Tendsto (fun x => f x / g x) l (𝓝 0))

def realScalarBigOIff : Prop :=
  ∀ {X : Type u} (l : Filter X) (f g : X → ℝ),
    scalarBigOValue l f g ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in l, |f x| ≤ C * |g x|

def realScalarLittleOIff : Prop :=
  ∀ {X : Type u} (l : Filter X) (f g : X → ℝ),
    scalarLittleOValue l f g ↔ ∀ ε : ℝ, 0 < ε → ∀ᶠ x in l, |f x| ≤ ε * |g x|

def scalarBigOApproachIff : Prop :=
  ∀ {K : Type v} [NormedField K] (E : Set ℝ) (q : RealApproach) (f g : ℝ → K),
    scalarBigOValue (approachFilterValue E q) f g ↔
      ∃ C : ℝ, 0 ≤ C ∧ OneSided.approachEventuallyValue E q (fun x => ‖f x‖ ≤ C * ‖g x‖)

def scalarLittleOApproachIff : Prop :=
  ∀ {K : Type v} [NormedField K] (E : Set ℝ) (q : RealApproach) (f g : ℝ → K),
    scalarLittleOValue (approachFilterValue E q) f g ↔
      ∀ ε : ℝ, 0 < ε → OneSided.approachEventuallyValue E q (fun x => ‖f x‖ ≤ ε * ‖g x‖)

def scalarLittleORatioApproachIff : Prop :=
  ∀ {K : Type v} [NormedField K] (E : Set ℝ) (q : RealApproach) (f g : ℝ → K),
    OneSided.approachNontrivialValue E q →
    OneSided.approachEventuallyValue E q (fun x => g x ≠ 0) →
      (scalarLittleOValue (approachFilterValue E q) f g ↔
        OneSided.finiteApproachLimitValue (fun x => f x / g x) E q 0)

def scalarLittleOPuncturedIffRatioLimit : Prop :=
  ∀ {K : Type v} [NormedField K] (E : Set ℝ) (a : ℝ) (f g : ℝ → K),
    OneSided.approachEventuallyValue E (.punctured a) (fun x => g x ≠ 0) →
      (scalarLittleOValue (approachFilterValue E (.punctured a)) f g ↔
        RelativeLimit.relativePuncturedLimitValue (fun x => f x / g x) E a 0)

end Specs.SingleVariableAnalysis.Ch02.BigO
