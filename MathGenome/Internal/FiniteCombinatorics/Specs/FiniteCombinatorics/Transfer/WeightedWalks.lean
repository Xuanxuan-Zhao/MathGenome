import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Directed.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Transfer.GeometricMatrixSeries
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators

/-! Independent specification of the weighted-walk assertion of p204:W17.
The finite sets below consist of the shared endpoint-indexed walks, with their
original arc identities. Membership is specified to be exactly length `n`.
No acyclicity, nonempty vertex set, or restriction on loops/parallel arcs is used.
-/
noncomputable section
open scoped BigOperators
universe u v r
namespace Specs.FiniteCombinatorics.Transfer.WeightedWalks
open _root_.FiniteCombinatorics.Directed

/-- Canonical finite enumeration, splitting off the first arc. -/
def walks {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (G : Digraph V A) : (n : ℕ) → (x y : V) → Finset (Walk G x y) := by
  classical
  exact fun n => match n with
    | 0 => fun x y => if h : x = y then {h ▸ Walk.nil x} else ∅
    | n + 1 => fun x y => Finset.univ.biUnion fun z : V =>
        Finset.univ.biUnion fun a : Arc G x z =>
          (walks G n z y).image (Walk.cons a)

/-- Total weight of the original arcs with both specified incidences. -/
def adjacencyType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  {R : Type r} [CommRing R], Digraph V A → (A → R) → Matrix V V R

def adjacencyValue : adjacencyType := fun {_} {_} [_] [_] {_} [_] G w x y =>
  ∑ a : Arc G x y, w a.val

def walksType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A) (_n : ℕ) (x y : V), Finset (Walk G x y)

def seriesType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  {R : Type r} [CommRing R], Digraph V A → (A → R) → V → V → PowerSeries R

def seriesValue : seriesType := fun {_} {_} [_] [_] {_} [_] G w x y =>
  Series.ogfValue (fun n => ∑ p ∈ walks G n x y,
    _root_.FiniteCombinatorics.Directed.Spec.weight w p)

def membership : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A) (n : ℕ) (x y : V) (p : Walk G x y),
  p ∈ walks G n x y ↔ _root_.FiniteCombinatorics.Directed.Spec.length p = n

def power_weights : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  {R : Type r} [CommRing R] [DecidableEq V]
  (G : Digraph V A) (w : A → R) (n : ℕ) (x y : V),
  (adjacencyValue G w ^ n) x y =
    ∑ p ∈ walks G n x y, _root_.FiniteCombinatorics.Directed.Spec.weight w p

/-- Includes the degree-zero coefficient and the empty walk convention. -/
def series_coefficients : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  {R : Type r} [CommRing R] [DecidableEq V]
  (G : Digraph V A) (w : A → R) (n : ℕ) (x y : V),
  PowerSeries.coeff n (geometricSeriesValue (adjacencyValue G w) x y) =
    ∑ p ∈ walks G n x y, _root_.FiniteCombinatorics.Directed.Spec.weight w p

def series_identity : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  {R : Type r} [CommRing R] [DecidableEq V]
  (G : Digraph V A) (w : A → R) (x y : V),
  geometricSeriesValue (adjacencyValue G w) x y = seriesValue G w x y

open scoped Classical in
def zero_weights : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  {R : Type r} [CommRing R] (G : Digraph V A) (w : A → R) (x y : V),
  (∑ p ∈ walks G 0 x y, _root_.FiniteCombinatorics.Directed.Spec.weight w p) =
    if x = y then 1 else 0

end Specs.FiniteCombinatorics.Transfer.WeightedWalks
