import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Foundations
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-! Independent interfaces for paper.tex W56 and its following paragraph (2092–2111).
`Fin k` labels the k colors starting at zero; the labels are immaterial under bijections.
The natural chromatic number is the infimum of the natural counts admitting a coloring.
The existence and minimum specifications below ensure that this is an attained minimum.
-/

universe u v w x
noncomputable section
namespace Specs.FiniteCombinatorics.Graph.Coloring.Foundations

def ProperColoringType :=
  ∀ {V : Type u} [Finite V], SimpleGraph V → (α : Type v) → Type (max u v)
abbrev ProperColoringValue : ProperColoringType := fun {_} _ G α => G.Coloring α

def KColoringType := ∀ {V : Type u} [Finite V], SimpleGraph V → ℕ → Type u
abbrev KColoringValue : KColoringType := fun {_} _ G k => G.Coloring (Fin k)

def chromaticNumberType := ∀ {V : Type u} [Finite V], SimpleGraph V → ℕ
def chromaticNumberValue : chromaticNumberType :=
  fun {_} _ G => sInf {k : ℕ | Nonempty (G.Coloring (Fin k))}

def recolorType := ∀ {V : Type u} [Finite V] (G : SimpleGraph V)
  {α : Type v} {β : Type w}, (α ≃ β) → (G.Coloring α ≃ G.Coloring β)
def recolorValue : recolorType := fun {_} _ G {_} {_} e => G.recolorOfEquiv e

def transportType := ∀ {V : Type u} {W : Type v} [Finite V] [Finite W]
  {G : SimpleGraph V} {H : SimpleGraph W}, (G ≃g H) →
  (α : Type w) → (G.Coloring α ≃ H.Coloring α)
def transportValue : transportType :=
  fun {_} {_} _ _ {_} {_} e α => SimpleGraph.coloringCongr e (Equiv.refl α)

def coloring_validType : Prop := ∀ {V : Type u} [Finite V] (G : SimpleGraph V)
  {α : Type v} (c : ProperColoringValue G α) {a b : V}, G.Adj a b → c a ≠ c b

def coloring_from_functionType : Prop := ∀ {V : Type u} [Finite V] (G : SimpleGraph V)
  {α : Type v} (f : V → α), (∀ a b, G.Adj a b → f a ≠ f b) →
  ∃ c : ProperColoringValue G α, ∀ a, c a = f a

def kcoloring_iffType : Prop := ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (k : ℕ),
  Nonempty (KColoringValue G k) ↔ ∃ f : V → Fin k, ∀ a b, G.Adj a b → f a ≠ f b

def distinct_coloringType : Prop := ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  ∃ c : KColoringValue G (Nat.card V), Function.Injective c

def coloring_existsType : Prop := ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  ∃ k : ℕ, Nonempty (KColoringValue G k)

def chromaticNumber_minimumType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  Nonempty (KColoringValue G (chromaticNumberValue G)) ∧
    ∀ k : ℕ, Nonempty (KColoringValue G k) → chromaticNumberValue G ≤ k

def chromaticNumber_eq_mathlibType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  (chromaticNumberValue G : ℕ∞) = G.chromaticNumber

def chromaticNumber_eq_toNatType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  chromaticNumberValue G = G.chromaticNumber.toNat

def chromaticNumber_eq_zero_iffType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V), chromaticNumberValue G = 0 ↔ IsEmpty V

def chromaticNumber_eq_one_iffType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  chromaticNumberValue G = 1 ↔ G = ⊥ ∧ Nonempty V

def chromaticNumber_edgelessType : Prop :=
  ∀ {V : Type u} [Finite V] [Nonempty V], chromaticNumberValue (⊥ : SimpleGraph V) = 1

def recolor_applyType : Prop := ∀ {V : Type u} [Finite V] (G : SimpleGraph V)
  {α : Type v} {β : Type w} (e : α ≃ β) (c : ProperColoringValue G α) (a : V),
  recolorValue G e c a = e (c a)

def transport_applyType : Prop :=
  ∀ {V : Type u} {W : Type v} [Finite V] [Finite W]
  {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
  {α : Type w} (c : ProperColoringValue G α) (b : W),
  transportValue e α c b = c (e.symm b)

def colorable_iso_iffType : Prop :=
  ∀ {V : Type u} {W : Type v} [Finite V] [Finite W]
  {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (k : ℕ),
  Nonempty (KColoringValue G k) ↔ Nonempty (KColoringValue H k)

def chromaticNumber_isoType : Prop :=
  ∀ {V : Type u} {W : Type v} [Finite V] [Finite W]
  {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H),
  chromaticNumberValue G = chromaticNumberValue H

def colorable_relabel_iffType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V)
  {α : Type v} {β : Type w} (e : α ≃ β),
  Nonempty (ProperColoringValue G α) ↔ Nonempty (ProperColoringValue G β)

end Specs.FiniteCombinatorics.Graph.Coloring.Foundations
