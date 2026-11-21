import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.Foundation
import Mathlib.Data.Finset.Sort
import Mathlib.Basic.Real.Basic

/-! Independent specification of paper.tex W78 and the Chapter 12 conventions.
All sets use the canonical ambient type. Weights and the supplied tie order
are on the ground subtype, so no order or finiteness of the ambient type is
required. A linear order expresses the source's total tie order. -/
namespace FiniteCombinatorics.Matroid
open Set
universe u
variable {α : Type u} {E : Set α}

/-- Descending weight, then ascending in the supplied total tie order. -/
def WeightTieBefore (w : E → ℝ) (tie : LinearOrder E) (a b : E) : Prop :=
  w b < w a ∨ w a = w b ∧ @LE.le E tie.toLE a b

instance weightTieTrans (w : E → ℝ) (tie : LinearOrder E) :
    IsTrans E (WeightTieBefore w tie) where
  trans a b c hab hbc := by
    let := tie
    rcases hab with hab | ⟨hab, ht⟩ <;> rcases hbc with hbc | ⟨hbc, hu⟩
    · exact Or.inl (lt_trans hbc hab)
    · exact Or.inl (hbc ▸ hab)
    · exact Or.inl (hab.symm ▸ hbc)
    · exact Or.inr ⟨hab.trans hbc, le_trans ht hu⟩

instance weightTieAntisymm (w : E → ℝ) (tie : LinearOrder E) :
    Std.Antisymm (WeightTieBefore w tie) where
  antisymm a b hab hba := by
    let := tie
    rcases hab with hab | ⟨hab, ht⟩ <;> rcases hba with hba | ⟨hba, hu⟩
    · exact False.elim (lt_asymm hab hba)
    · exact False.elim ((ne_of_lt hab) hba)
    · exact False.elim ((ne_of_lt hba) hab)
    · exact le_antisymm ht hu

instance weightTieTotal (w : E → ℝ) (tie : LinearOrder E) :
    Std.Total (WeightTieBefore w tie) where
  total a b := by
    let := tie
    rcases lt_trichotomy (w a) (w b) with h | h | h
    · exact Or.inr (Or.inl h)
    · rcases le_total a b with ht | ht
      · exact Or.inl (Or.inr ⟨h, ht⟩)
      · exact Or.inr (Or.inr ⟨h.symm, ht⟩)
    · exact Or.inl (Or.inl h)

namespace Expected

/-- Each ground element occurs once, ordered by descending weight and then tie order. -/
noncomputable def greedyEnumeration (S : IndependenceSystem E) (w : E → ℝ)
    (tie : LinearOrder E) : List E := by
  classical
  letI := S.finite_ground.fintype
  exact Finset.univ.sort (WeightTieBefore w tie)

/-- The weight of a subset of E; values on arbitrary ambient sets ignore points off E. -/
noncomputable def subsetWeight (S : IndependenceSystem E) (w : E → ℝ)
    (A : Set α) : ℝ := by
  classical
  letI := S.finite_ground.fintype
  exact ∑ e : E, if (e : α) ∈ A then w e else 0

/-- One greedy step, including elements with negative weight. -/
noncomputable def greedyStep (S : IndependenceSystem E) (I : Set α) (e : E) : Set α := by
  classical
  exact if S.Indep (insert (e : α) I) then insert (e : α) I else I

/-- I_i: perform precisely the first i steps (saturating after the last element). -/
noncomputable def greedyState (S : IndependenceSystem E) (w : E → ℝ)
    (tie : LinearOrder E) (i : ℕ) : Set α :=
  ((greedyEnumeration S w tie).take i).foldl (greedyStep S) ∅

/-- Return I_n after scanning all n elements. -/
noncomputable def greedyOutput (S : IndependenceSystem E) (w : E → ℝ)
    (tie : LinearOrder E) : Set α :=
  greedyState S w tie (greedyEnumeration S w tie).length

/-- P_i is the set of elements in the first i positions, with P_0 empty. -/
noncomputable def greedyPrefix (S : IndependenceSystem E) (w : E → ℝ)
    (tie : LinearOrder E) (i : ℕ) : Set α :=
  {x | ∃ e ∈ (greedyEnumeration S w tie).take i, (e : α) = x}

/-- Feasibility includes maximality by inclusion, using the shared foundation predicate. -/
noncomputable def BasisOptimal (S : IndependenceSystem E) (w : E → ℝ)
    (I : Set α) : Prop :=
  MaximalIndependent S I ∧
    ∀ J, MaximalIndependent S J → subsetWeight S w J ≤ subsetWeight S w I

/-- Independent-set optimization allows all cardinalities. -/
noncomputable def IndependentOptimal (S : IndependenceSystem E) (w : E → ℝ)
    (I : Set α) : Prop :=
  S.Indep I ∧ ∀ J, S.Indep J → subsetWeight S w J ≤ subsetWeight S w I

/-- Zero-weight elements are retained. -/
def nonnegativeGround (w : E → ℝ) : Set α :=
  {x | ∃ hx : x ∈ E, 0 ≤ w ⟨x, hx⟩}

/-- Delete negative-weight elements; do not change the ambient type or independence test. -/
def nonnegativeRestriction (S : IndependenceSystem E) (w : E → ℝ) :
    IndependenceSystem (nonnegativeGround w) where
  finite_ground := S.finite_ground.subset (fun _ h => h.choose)
  Indep I := S.Indep I ∧ I ⊆ nonnegativeGround w
  empty_indep := ⟨S.empty_indep, empty_subset _⟩
  hereditary := fun {_ _} h hIJ => ⟨S.hereditary h.1 hIJ, hIJ.trans h.2⟩
  subset_ground := fun {_} h => h.2

/-- The unchanged weight function on the restricted ground. -/
def nonnegativeWeight (w : E → ℝ) (e : nonnegativeGround w) : ℝ :=
  w ⟨e.val, e.property.choose⟩

/-- Restrict the original tie order along the inclusion of the nonnegative ground. -/
@[instance_reducible] noncomputable def nonnegativeTie (w : E → ℝ) (tie : LinearOrder E) :
    LinearOrder (nonnegativeGround w) := by
  letI := tie
  exact LinearOrder.lift' (fun e : nonnegativeGround w =>
    (⟨e.val, e.property.choose⟩ : E)) (by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun x : E => (x : α)) h)

/-- Greedy on the nonnegative restriction, with the inherited weights and tie order. -/
noncomputable def nonnegativeGreedyOutput (S : IndependenceSystem E) (w : E → ℝ)
    (tie : LinearOrder E) : Set α :=
  greedyOutput (nonnegativeRestriction S w) (nonnegativeWeight w) (nonnegativeTie w tie)

def greedyEnumerationType := ∀ {α : Type u} {E : Set α}, IndependenceSystem E → (E → ℝ) → LinearOrder E → List E

def subsetWeightType := ∀ {α : Type u} {E : Set α}, IndependenceSystem E → (E → ℝ) → Set α → ℝ

def greedyStepType := ∀ {α : Type u} {E : Set α}, IndependenceSystem E → Set α → E → Set α

def greedyStateType := ∀ {α : Type u} {E : Set α}, IndependenceSystem E → (E → ℝ) → LinearOrder E → ℕ → Set α

def greedyOutputType := ∀ {α : Type u} {E : Set α}, IndependenceSystem E → (E → ℝ) → LinearOrder E → Set α

def greedyPrefixType := ∀ {α : Type u} {E : Set α}, IndependenceSystem E → (E → ℝ) → LinearOrder E → ℕ → Set α

def BasisOptimalType := ∀ {α : Type u} {E : Set α}, IndependenceSystem E → (E → ℝ) → Set α → Prop

def IndependentOptimalType := ∀ {α : Type u} {E : Set α}, IndependenceSystem E → (E → ℝ) → Set α → Prop

def nonnegativeGroundType := ∀ {α : Type u} {E : Set α}, (E → ℝ) → Set α

def nonnegativeRestrictionType := ∀ {α : Type u} {E : Set α}, IndependenceSystem E → (w : E → ℝ) → IndependenceSystem (nonnegativeGround w)

def nonnegativeWeightType := ∀ {α : Type u} {E : Set α}, (w : E → ℝ) → nonnegativeGround w → ℝ

def nonnegativeTieType := ∀ {α : Type u} {E : Set α}, (w : E → ℝ) → LinearOrder E → LinearOrder (nonnegativeGround w)

def nonnegativeGreedyOutputType := ∀ {α : Type u} {E : Set α}, IndependenceSystem E → (E → ℝ) → LinearOrder E → Set α

def greedyEnumeration_nodup : Prop :=
  ∀ {α : Type u} {E : Set α}, ∀ (S : IndependenceSystem E) (w : E → ℝ) (tie : LinearOrder E), (greedyEnumeration S w tie).Nodup

def greedyEnumeration_mem : Prop :=
  ∀ {α : Type u} {E : Set α}, ∀ (S : IndependenceSystem E) (w : E → ℝ) (tie : LinearOrder E), ∀ e : E, e ∈ greedyEnumeration S w tie

def greedyEnumeration_pairwise : Prop :=
  ∀ {α : Type u} {E : Set α}, ∀ (S : IndependenceSystem E) (w : E → ℝ) (tie : LinearOrder E), (greedyEnumeration S w tie).Pairwise (WeightTieBefore w tie)

def greedyState_zero : Prop :=
  ∀ {α : Type u} {E : Set α}, ∀ (S : IndependenceSystem E) (w : E → ℝ) (tie : LinearOrder E), greedyState S w tie 0 = ∅

def greedyState_succ : Prop :=
  ∀ {α : Type u} {E : Set α}, ∀ (S : IndependenceSystem E) (w : E → ℝ) (tie : LinearOrder E), ∀ (i : ℕ) (e : E), (greedyEnumeration S w tie)[i]? = some e →
    greedyState S w tie (i + 1) = greedyStep S (greedyState S w tie i) e

def greedyStep_accept : Prop :=
  ∀ {α : Type u} {E : Set α}, ∀ (S : IndependenceSystem E) (I : Set α) (e : E),
    S.Indep (insert (e : α) I) → greedyStep S I e = insert (e : α) I

def greedyStep_reject : Prop :=
  ∀ {α : Type u} {E : Set α}, ∀ (S : IndependenceSystem E) (I : Set α) (e : E),
    ¬ S.Indep (insert (e : α) I) → greedyStep S I e = I

def greedyPrefix_zero : Prop :=
  ∀ {α : Type u} {E : Set α}, ∀ (S : IndependenceSystem E) (w : E → ℝ) (tie : LinearOrder E), greedyPrefix S w tie 0 = ∅

def greedyPrefix_full : Prop :=
  ∀ {α : Type u} {E : Set α}, ∀ (S : IndependenceSystem E) (w : E → ℝ) (tie : LinearOrder E), greedyPrefix S w tie (greedyEnumeration S w tie).length = E

def subsetWeight_empty : Prop :=
  ∀ {α : Type u} {E : Set α}, ∀ (S : IndependenceSystem E) (w : E → ℝ), subsetWeight S w ∅ = 0

def nonnegativeRestriction_indep : Prop :=
  ∀ {α : Type u} {E : Set α}, ∀ (S : IndependenceSystem E) (w : E → ℝ) (I : Set α),
    (nonnegativeRestriction S w).Indep I ↔ S.Indep I ∧ I ⊆ nonnegativeGround w

def greedyOutput_empty : Prop :=
  ∀ {α : Type u} (S : IndependenceSystem (∅ : Set α))
    (w : (∅ : Set α) → ℝ) (tie : LinearOrder (∅ : Set α)), greedyOutput S w tie = ∅


end Expected
end FiniteCombinatorics.Matroid
