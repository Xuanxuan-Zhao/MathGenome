import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.BigO

/-!
Independent specification of K03.02.o_algebra, paper.tex:449–456.

One filter records the common approach and domain. These propositions use the
upstream inequality definitions, including at zeros of comparison functions.
Normed fields include both source scalars ℝ and ℂ with their canonical norms.
Only division requires an eventually nonzero divisor. No nontriviality or
additional regularity hypothesis is needed for these rules of inequalities.
-/

namespace Specs.SingleVariableAnalysis.Ch02.OAlgebra

open Filter
open BigO (scalarBigOValue scalarLittleOValue)
universe u v

def bigOTrans : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f g h : X → K),
    scalarBigOValue l f g → scalarBigOValue l g h → scalarBigOValue l f h

def littleOTransBigO : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f g h : X → K),
    scalarLittleOValue l f g → scalarBigOValue l g h → scalarLittleOValue l f h

def bigOTransLittleO : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f g h : X → K),
    scalarBigOValue l f g → scalarLittleOValue l g h → scalarLittleOValue l f h

def bigOAdd : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f u g : X → K),
    scalarBigOValue l f g → scalarBigOValue l u g →
      scalarBigOValue l (fun x => f x + u x) g

def littleOAdd : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f u g : X → K),
    scalarLittleOValue l f g → scalarLittleOValue l u g →
      scalarLittleOValue l (fun x => f x + u x) g

def bigOMul : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f g u v : X → K),
    scalarBigOValue l f g → scalarBigOValue l u v →
      scalarBigOValue l (fun x => f x * u x) (fun x => g x * v x)

def littleOMulBigO : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f g u v : X → K),
    scalarLittleOValue l f g → scalarBigOValue l u v →
      scalarLittleOValue l (fun x => f x * u x) (fun x => g x * v x)

def bigOMulLittleO : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f g u v : X → K),
    scalarBigOValue l f g → scalarLittleOValue l u v →
      scalarLittleOValue l (fun x => f x * u x) (fun x => g x * v x)

def bigOConstMul : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f g : X → K) (c : K),
    scalarBigOValue l f g → scalarBigOValue l (fun x => c * f x) g

def littleOConstMul : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f g : X → K) (c : K),
    scalarLittleOValue l f g → scalarLittleOValue l (fun x => c * f x) g

def bigODiv : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f g v : X → K),
    (∀ᶠ x in l, v x ≠ 0) → scalarBigOValue l f g →
      scalarBigOValue l (fun x => f x / v x) (fun x => g x / v x)

def littleODiv : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f g v : X → K),
    (∀ᶠ x in l, v x ≠ 0) → scalarLittleOValue l f g →
      scalarLittleOValue l (fun x => f x / v x) (fun x => g x / v x)

end Specs.SingleVariableAnalysis.Ch02.OAlgebra
