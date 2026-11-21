import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.Foundation
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Combinatorics.Matroid.Loop

/-! Indexed vector configurations, paper.tex W70.
Only the ground and its subfamilies are finite; the ambient vector space is arbitrary.
The common construction is specified by the canonical finite augmentation construction.
-/
namespace FiniteCombinatorics.Matroid
open Set Submodule
universe u v w
variable {α : Type u} {K : Type v} {V : Type w}
variable [Field K] [AddCommGroup V] [Module K V]

/-- A finite independence system on indices, without identifying equal columns. -/
def vectorSystem (K : Type v) [Field K] {V : Type w} [AddCommGroup V] [Module K V]
    (E : Set α) (hE : E.Finite) (v : α → V) : IndependenceSystem E where
  finite_ground := hE
  Indep I := I ⊆ E ∧ LinearIndepOn K v I
  empty_indep := ⟨empty_subset _, linearIndepOn_empty _ _⟩
  hereditary := fun {_ _} h hIJ => ⟨hIJ.trans h.1, h.2.mono hIJ⟩
  subset_ground := fun {_} h => h.1

/-- Dimension of the span of an independent indexed subfamily. -/
theorem linearIndepOn_finrank_image {v : α → V} {I : Set α}
    (hI : I.Finite) (hi : LinearIndepOn K v I) :
    Module.finrank K (span K (v '' I)) = I.ncard := by
  letI := hI.fintype
  rw [image_eq_range]
  simpa only [fintypeCard_eq_ncard] using
    (finrank_span_eq_card (b := fun x : I => v x) hi)

/-- The dimension comparison proves augmentation even with repeated or zero columns. -/
theorem vectorSystem_augmentation (E : Set α) (hE : E.Finite) (v : α → V) :
    Expected.Augmentation (vectorSystem K E hE v) := by
  intro I J hI hJ hcard
  have hIf := hE.subset hI.1
  have hJf := hE.subset hJ.1
  have hex : ∃ e ∈ J, v e ∉ span K (v '' I) := by
    by_contra! h
    have hle : span K (v '' J) ≤ span K (v '' I) :=
      span_le.mpr (by rintro _ ⟨e, he, rfl⟩; exact h e he)
    letI := Module.Finite.span_of_finite K (hIf.image v)
    have hd := Submodule.finrank_mono hle
    rw [linearIndepOn_finrank_image hJf hJ.2,
      linearIndepOn_finrank_image hIf hI.2] at hd
    exact (not_le_of_gt hcard) hd
  obtain ⟨e, heJ, he⟩ := hex
  have heI : e ∉ I := fun hi => he (subset_span ⟨e, hi, rfl⟩)
  exact ⟨e, ⟨heJ, heI⟩, insert_subset (hJ.1 heJ) hI.1, hI.2.insert he⟩

namespace Expected

/-- Canonical finite matroid of a family indexed by a specified ground. -/
def vectorMatroid (K : Type v) [Field K] {V : Type w} [AddCommGroup V] [Module K V]
    (E : Set α) (hE : E.Finite) (v : α → V) : _root_.Matroid α :=
  ofAugmentation (vectorSystem K E hE v) (vectorSystem_augmentation E hE v)

instance (E : Set α) (hE : E.Finite) (v : α → V) :
    (vectorMatroid K E hE v).Finite := ⟨hE⟩

/-- An indexed representation of a matroid, with exactly its given ground. -/
def Represents (K : Type v) [Field K] {V : Type w} [AddCommGroup V] [Module K V]
    (M : _root_.Matroid α) (v : α → V) : Prop :=
  ∀ I, M.Indep I ↔ I ⊆ M.E ∧ LinearIndepOn K v I

/-- Existence of an indexed representation over K. The ambient space need not be finite dimensional. -/
def Representable (K : Type v) [Field K] (M : _root_.Matroid α) : Prop :=
  ∃ (V : Type w) (_ : AddCommGroup V) (_ : Module K V) (v : α → V), Represents K M v

def vectorMatroidType := ∀ {α : Type u} (K : Type v) [Field K]
  {V : Type w} [AddCommGroup V] [Module K V],
  (E : Set α) → E.Finite → (α → V) → _root_.Matroid α

def RepresentsType := ∀ {α : Type u} (K : Type v) [Field K]
  {V : Type w} [AddCommGroup V] [Module K V], _root_.Matroid α → (α → V) → Prop

def RepresentableType := ∀ {α : Type u} (K : Type v) [Field K], _root_.Matroid α → Prop

def vectorGround : Prop := ∀ {α : Type u} (K : Type v) [Field K]
  {V : Type w} [AddCommGroup V] [Module K V]
  (E : Set α) (hE : E.Finite) (v : α → V), (vectorMatroid K E hE v).E = E

def vectorFinite : Prop := ∀ {α : Type u} (K : Type v) [Field K]
  {V : Type w} [AddCommGroup V] [Module K V]
  (E : Set α) (hE : E.Finite) (v : α → V), (vectorMatroid K E hE v).Finite

def vectorIndep : Prop := ∀ {α : Type u} (K : Type v) [Field K]
  {V : Type w} [AddCommGroup V] [Module K V]
  (E : Set α) (hE : E.Finite) (v : α → V) (I : Set α),
  (vectorMatroid K E hE v).Indep I ↔ I ⊆ E ∧ LinearIndepOn K v I

def vectorSpanFinite : Prop := ∀ {α : Type u} (K : Type v) [Field K]
  {V : Type w} [AddCommGroup V] [Module K V]
  (E : Set α) (hE : E.Finite) (v : α → V) (A : Set α), A ⊆ E →
  Module.Finite K (span K (v '' A))

def vectorRank : Prop := ∀ {α : Type u} (K : Type v) [Field K]
  {V : Type w} [AddCommGroup V] [Module K V]
  (E : Set α) (hE : E.Finite) (v : α → V) (A : Set α), A ⊆ E →
  rank (vectorMatroid K E hE v) A = (Module.finrank K (span K (v '' A)) : ℤ)

def vectorZeroLoop : Prop := ∀ {α : Type u} (K : Type v) [Field K]
  {V : Type w} [AddCommGroup V] [Module K V]
  (E : Set α) (hE : E.Finite) (v : α → V) (e : α), e ∈ E →
  ((vectorMatroid K E hE v).IsLoop e ↔ v e = 0)

def vectorProportionalDependent : Prop := ∀ {α : Type u} (K : Type v) [Field K]
  {V : Type w} [AddCommGroup V] [Module K V]
  (E : Set α) (hE : E.Finite) (v : α → V) (e f : α),
  e ∈ E → f ∈ E → e ≠ f → ∀ c : K, v f = c • v e →
  (vectorMatroid K E hE v).Dep {e, f}

def vectorRepeatedDependent : Prop := ∀ {α : Type u} (K : Type v) [Field K]
  {V : Type w} [AddCommGroup V] [Module K V]
  (E : Set α) (hE : E.Finite) (v : α → V) (e f : α),
  e ∈ E → f ∈ E → e ≠ f → v e = v f →
  (vectorMatroid K E hE v).Dep {e, f}

def vectorRepresents : Prop := ∀ {α : Type u} (K : Type v) [Field K]
  {V : Type w} [AddCommGroup V] [Module K V]
  (E : Set α) (hE : E.Finite) (v : α → V), Represents K (vectorMatroid K E hE v) v

def represents_iff_vectorMatroid : Prop := ∀ {α : Type u} (K : Type v) [Field K]
  {V : Type w} [AddCommGroup V] [Module K V]
  (M : _root_.Matroid α) [M.Finite] (v : α → V),
  Represents K M v ↔ M = vectorMatroid K M.E M.ground_finite v

def representsRank : Prop := ∀ {α : Type u} (K : Type v) [Field K]
  {V : Type w} [AddCommGroup V] [Module K V]
  (M : _root_.Matroid α) [M.Finite] (v : α → V), Represents K M v →
  ∀ A, A ⊆ M.E → rank M A = (Module.finrank K (span K (v '' A)) : ℤ)

def vectorRepresentable : Prop := ∀ {α : Type u} (K : Type v) [Field K]
  {V : Type w} [AddCommGroup V] [Module K V]
  (E : Set α) (hE : E.Finite) (v : α → V), Representable.{u,v,w} K (vectorMatroid K E hE v)

end Expected
end FiniteCombinatorics.Matroid
