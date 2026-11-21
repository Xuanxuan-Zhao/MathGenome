import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.ForwardPresentations

/-! W64 on an arbitrary ambient type and a finite specified ground.
A realization includes the stated independent-set recovery rule and recovers the
original presentation. Rank and closure are recovered only on subsets of the
ground, since their ambient extensions are not part of the input data.
No ground nonemptiness, positive rank, or circuit-family nonemptiness is assumed.
These statements do not import any candidate implementation. -/
namespace FiniteCombinatorics.Matroid
open Set
universe u
variable {α : Type u}

/-- The original hereditary system, including its ground, is preserved. -/
def IndependenceRealization {E : Set α} (S : IndependenceSystem E)
    (M : _root_.Matroid α) : Prop :=
  M.E = E ∧ M.Finite ∧ ∀ I, M.Indep I ↔ S.Indep I

def BasisRealization (E : Set α) (B : Set (Set α)) (M : _root_.Matroid α) : Prop :=
  M.E = E ∧ M.Finite ∧
    (∀ I, M.Indep I ↔ Expected.BasisIndependent E B I) ∧
    (∀ D, M.IsBase D ↔ D ∈ B)

def RankRealization (E : Set α) (r : Set α → ℤ) (M : _root_.Matroid α) : Prop :=
  M.E = E ∧ ∃ hM : M.Finite,
    (∀ I, M.Indep I ↔ Expected.RankIndependent E r I) ∧
    (∀ A, A ⊆ E → @Expected.rank α M hM A = r A)

def CircuitRealization (E : Set α) (C : Set (Set α)) (M : _root_.Matroid α) : Prop :=
  M.E = E ∧ M.Finite ∧
    (∀ I, M.Indep I ↔ Expected.CircuitIndependent E C I) ∧
    (∀ D, M.IsCircuit D ↔ D ∈ C)

def ClosureRealization (E : Set α) (c : Set α → Set α) (M : _root_.Matroid α) : Prop :=
  M.E = E ∧ M.Finite ∧
    (∀ I, M.Indep I ↔ Expected.ClosureIndependent E c I) ∧
    (∀ A, A ⊆ E → M.closure A = c A)

namespace Expected

/-- Each axiom system is equivalent to unique realization, with all recovery
rules included. In particular these are equivalences of the given data, not
merely assertions that the five axiom predicates are inhabited. -/
def independenceAxiomEquivalence : Prop :=
  ∀ {α : Type u} (E : Set α) (S : IndependenceSystem E),
    Augmentation S ↔ ∃! M : _root_.Matroid α, IndependenceRealization S M

def basisAxiomEquivalence : Prop :=
  ∀ {α : Type u} (E : Set α), E.Finite → ∀ B : Set (Set α),
    BasisPresentation E B ↔ ∃! M : _root_.Matroid α, BasisRealization E B M

def rankAxiomEquivalence : Prop :=
  ∀ {α : Type u} (E : Set α), E.Finite → ∀ r : Set α → ℤ,
    RankPresentation E r ↔ ∃! M : _root_.Matroid α, RankRealization E r M

def circuitAxiomEquivalence : Prop :=
  ∀ {α : Type u} (E : Set α), E.Finite → ∀ C : Set (Set α),
    CircuitPresentation E C ↔ ∃! M : _root_.Matroid α, CircuitRealization E C M

def closureAxiomEquivalence : Prop :=
  ∀ {α : Type u} (E : Set α), E.Finite → ∀ c : Set α → Set α,
    ClosurePresentation E c ↔ ∃! M : _root_.Matroid α, ClosureRealization E c M

/-- All presentations arise from the same matroid, and every way of reconstructing
that matroid's presentations returns that very matroid. Independence uses the
shared canonical constructor, rather than a new matroid representation. -/
def presentationRoundTrips : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite],
    (∃ h : Augmentation (fromMatroid M), ofAugmentation (fromMatroid M) h = M) ∧
    BasisPresentation M.E {B | M.IsBase B} ∧
    RankPresentation M.E (rank M) ∧
    CircuitPresentation M.E {C | M.IsCircuit C} ∧
    ClosurePresentation M.E M.closure ∧
    (∀ N, IndependenceRealization (fromMatroid M) N → N = M) ∧
    (∀ N, BasisRealization M.E {B | M.IsBase B} N → N = M) ∧
    (∀ N, RankRealization M.E (rank M) N → N = M) ∧
    (∀ N, CircuitRealization M.E {C | M.IsCircuit C} N → N = M) ∧
    (∀ N, ClosureRealization M.E M.closure N → N = M)

/-- The complete five-presentation theorem, including unique reconstruction and
all round trips, on finite grounds, including the empty ground. -/
def fivePresentationEquivalence : Prop :=
  independenceAxiomEquivalence.{u} ∧ basisAxiomEquivalence.{u} ∧
    rankAxiomEquivalence.{u} ∧ circuitAxiomEquivalence.{u} ∧
    closureAxiomEquivalence.{u} ∧ presentationRoundTrips.{u}

end Expected
end FiniteCombinatorics.Matroid
