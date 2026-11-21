import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.OneSided
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.ContinuousOn

/-!
Independent specification of K03.02.algebra (paper.tex:392–404).
All five real approaches use the upstream nontrivial epsilon definition.
Normed-field statements specialize to the canonical ℝ and ℂ, with modulus
represented by norm (real absolute value is also stated explicitly).
The metric finite-point statements include complex input domains.
Ambient functions represent maps on E; MapsTo records the exact target domain D.
Continuity is relative to D, rather than continuity on an ambient neighborhood.
-/
namespace Specs.SingleVariableAnalysis.Ch02.Algebra

open _root_.SingleVariableAnalysis
open scoped Topology
open Specs.SingleVariableAnalysis.Ch02.OneSided
open Specs.SingleVariableAnalysis.Ch02.RelativeLimit
universe u v w

def approachEventuallyAnd : Prop :=
  ∀ {E : Set ℝ} {q : RealApproach} {P Q : ℝ → Prop},
    approachEventuallyValue E q P → approachEventuallyValue E q Q →
      approachEventuallyValue E q (fun x => P x ∧ Q x)

def finiteApproachLimitLinearCombination : Prop :=
  ∀ {K : Type u} [NormedField K]
    (f g : ℝ → K) (E : Set ℝ) (q : RealApproach) (A B : K) (c d : K)
    (hf : finiteApproachLimitValue f E q A) (hg : finiteApproachLimitValue g E q B) ,
    finiteApproachLimitValue (fun x => c * f x + d * g x) E q (c * A + d * B)

def finiteApproachLimitMul : Prop :=
  ∀ {K : Type u} [NormedField K]
    (f g : ℝ → K) (E : Set ℝ) (q : RealApproach) (A B : K)
    (hf : finiteApproachLimitValue f E q A) (hg : finiteApproachLimitValue g E q B) ,
    finiteApproachLimitValue (fun x => f x * g x) E q (A * B)

def finiteApproachLimitDiv : Prop :=
  ∀ {K : Type u} [NormedField K]
    (f g : ℝ → K) (E : Set ℝ) (q : RealApproach) (A B : K)
    (hf : finiteApproachLimitValue f E q A) (hg : finiteApproachLimitValue g E q B) (hB : B ≠ 0) ,
    finiteApproachLimitValue (fun x => f x / g x) E q (A / B)

def finiteApproachLimitNorm : Prop :=
  ∀ {K : Type u} [NormedField K]
    (f : ℝ → K) (E : Set ℝ) (q : RealApproach) (A : K)
    (hf : finiteApproachLimitValue f E q A) ,
    finiteApproachLimitValue (fun x => ‖f x‖) E q ‖A‖

def finiteApproachLimitAbs : Prop :=
  ∀ (f : ℝ → ℝ) (E : Set ℝ) (q : RealApproach) (A : ℝ)
    (hf : finiteApproachLimitValue f E q A) ,
    finiteApproachLimitValue (fun x => |f x|) E q |A|

def finiteApproachLimitEventuallyNeZero : Prop :=
  ∀ {K : Type u} [NormedField K]
    (g : ℝ → K) (E : Set ℝ) (q : RealApproach) (B : K)
    (hg : finiteApproachLimitValue g E q B) (hB : B ≠ 0) ,
    approachEventuallyValue E q (fun x => g x ≠ 0)

def finiteApproachLimitCompContinuousWithinAt : Prop :=
  ∀ {Y : Type u} {Z : Type v} [MetricSpace Y] [MetricSpace Z]
    (f : ℝ → Y) (g : Y → Z) (E : Set ℝ) (D : Set Y) (q : RealApproach) (b : Y)
    (hb : b ∈ D) (hmap : Set.MapsTo f E D)
    (hf : finiteApproachLimitValue f E q b) (hg : ContinuousWithinAt g D b) ,
    finiteApproachLimitValue (fun x => g (f x)) E q (g b)

def finiteApproachLimitCompPunctured : Prop :=
  ∀ {Y : Type u} {Z : Type v} [MetricSpace Y] [MetricSpace Z]
    (f : ℝ → Y) (g : Y → Z) (E : Set ℝ) (D : Set Y) (q : RealApproach) (b : Y) (C : Z)
    (hmap : Set.MapsTo f E D) (hf : finiteApproachLimitValue f E q b)
    (hg : relativePuncturedLimitValue g D b C)
    (havoid : approachEventuallyValue E q (fun x => f x ≠ b)) ,
    finiteApproachLimitValue (fun x => g (f x)) E q C

def relativePuncturedLimitLinearCombination : Prop :=
  ∀ {X : Type u} {K : Type v} [MetricSpace X] [NormedField K]
    (f g : X → K) (E : Set X) (a : X) (A B : K) (c d : K)
    (ha : domainAccumulationValue E a)
    (hf : relativePuncturedLimitValue f E a A) (hg : relativePuncturedLimitValue g E a B) ,
    relativePuncturedLimitValue (fun x => c * f x + d * g x) E a (c * A + d * B)

def relativePuncturedLimitMul : Prop :=
  ∀ {X : Type u} {K : Type v} [MetricSpace X] [NormedField K]
    (f g : X → K) (E : Set X) (a : X) (A B : K)
    (ha : domainAccumulationValue E a)
    (hf : relativePuncturedLimitValue f E a A) (hg : relativePuncturedLimitValue g E a B) ,
    relativePuncturedLimitValue (fun x => f x * g x) E a (A * B)

def relativePuncturedLimitDiv : Prop :=
  ∀ {X : Type u} {K : Type v} [MetricSpace X] [NormedField K]
    (f g : X → K) (E : Set X) (a : X) (A B : K)
    (ha : domainAccumulationValue E a)
    (hf : relativePuncturedLimitValue f E a A) (hg : relativePuncturedLimitValue g E a B) (hB : B ≠ 0) ,
    relativePuncturedLimitValue (fun x => f x / g x) E a (A / B)

def relativePuncturedLimitNorm : Prop :=
  ∀ {X : Type u} {K : Type v} [MetricSpace X] [NormedField K]
    (f : X → K) (E : Set X) (a : X) (A : K) (ha : domainAccumulationValue E a)
    (hf : relativePuncturedLimitValue f E a A) ,
    relativePuncturedLimitValue (fun x => ‖f x‖) E a ‖A‖

def relativePuncturedLimitAbs : Prop :=
  ∀ {X : Type u} [MetricSpace X]
    (f : X → ℝ) (E : Set X) (a : X) (A : ℝ) (ha : domainAccumulationValue E a)
    (hf : relativePuncturedLimitValue f E a A) ,
    relativePuncturedLimitValue (fun x => |f x|) E a |A|

def relativePuncturedLimitEventuallyNeZero : Prop :=
  ∀ {X : Type u} {K : Type v} [MetricSpace X] [NormedField K]
    (g : X → K) (E : Set X) (a : X) (B : K) (ha : domainAccumulationValue E a)
    (hg : relativePuncturedLimitValue g E a B) (hB : B ≠ 0) ,
    ∀ᶠ x in puncturedDomainFilterValue E a, g x ≠ 0

def relativePuncturedLimitCompContinuousWithinAt : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type w}
    [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
    (f : X → Y) (g : Y → Z) (E : Set X) (D : Set Y) (a : X) (b : Y)
    (ha : domainAccumulationValue E a) (hb : b ∈ D) (hmap : Set.MapsTo f E D)
    (hf : relativePuncturedLimitValue f E a b) (hg : ContinuousWithinAt g D b) ,
    relativePuncturedLimitValue (fun x => g (f x)) E a (g b)

def relativePuncturedLimitCompPunctured : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type w}
    [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
    (f : X → Y) (g : Y → Z) (E : Set X) (D : Set Y) (a : X) (b : Y) (C : Z)
    (ha : domainAccumulationValue E a) (hmap : Set.MapsTo f E D)
    (hf : relativePuncturedLimitValue f E a b) (hg : relativePuncturedLimitValue g D b C)
    (havoid : ∀ᶠ x in puncturedDomainFilterValue E a, f x ≠ b) ,
    relativePuncturedLimitValue (fun x => g (f x)) E a C

end Specs.SingleVariableAnalysis.Ch02.Algebra
