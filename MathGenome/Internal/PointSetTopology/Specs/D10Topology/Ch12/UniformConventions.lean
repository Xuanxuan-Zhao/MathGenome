import Mathlib.Topology.UniformSpace.Equiv
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch04.ProperFilters

open Set Filter
open scoped Uniformity Topology SetRel
universe u v

/-! Exact conventions of paper.tex, Definitions 12.1, uniform-continuity, and Cauchy.
UniformSpace is the canonical representation. The reconstruction obligation below
checks all entourage axioms, including the special empty-space convention. -/
namespace Specs.D10Topology.Ch12.UniformConventions

def Uniformity (X : Type u) : Type u :=
  UniformSpace X

def UniformityType := (X : Type u) → Type u
def UniformityValue : UniformityType := @Uniformity

def relationInverse {X : Type u} (U : Set (X × X)) : Set (X × X) :=
  {p | (p.2, p.1) ∈ U}

def relationInverseType := {X : Type u} → Set (X × X) → Set (X × X)
def relationInverseValue : relationInverseType := @relationInverse

def relationComp {X : Type u} (U V : Set (X × X)) : Set (X × X) :=
  {p | ∃ y, (p.1, y) ∈ V ∧ (y, p.2) ∈ U}

def relationCompType := {X : Type u} → Set (X × X) → Set (X × X) → Set (X × X)
def relationCompValue : relationCompType := @relationComp

def entourageBall {X : Type u} (U : Set (X × X)) (x : X) : Set X :=
  {y | (x, y) ∈ U}

def entourageBallType := {X : Type u} → Set (X × X) → X → Set X
def entourageBallValue : entourageBallType := @entourageBall

def EntourageAxioms {X : Type u} (F : Filter (X × X)) : Prop :=
  (∀ U ∈ F, ∀ x : X, (x, x) ∈ U) ∧
  (∀ U ∈ F, relationInverse U ∈ F) ∧
  (∀ U ∈ F, ∃ V ∈ F, relationComp V V ⊆ U)

def EntourageAxiomsType := {X : Type u} → Filter (X × X) → Prop
def EntourageAxiomsValue : EntourageAxiomsType := @EntourageAxioms

def Separated {X : Type u} [UniformSpace X] : Prop :=
  ⋂₀ (𝓤 X).sets = diagonal X

def SeparatedType := {X : Type u} → [UniformSpace X] → Prop
def SeparatedValue : SeparatedType := @Separated

def EntourageContinuous {X : Type u} {Y : Type v} [UniformSpace X] [UniformSpace Y] (f : X → Y) : Prop :=
  ∀ V ∈ 𝓤 Y, (Prod.map f f) ⁻¹' V ∈ 𝓤 X

def EntourageContinuousType := {X : Type u} → {Y : Type v} → [UniformSpace X] → [UniformSpace Y] → (X → Y) → Prop
def EntourageContinuousValue : EntourageContinuousType := @EntourageContinuous

def UniformIsomorphism {X : Type u} {Y : Type v} [UniformSpace X] [UniformSpace Y] (e : X ≃ Y) : Prop :=
  EntourageContinuous e ∧ EntourageContinuous e.symm

def UniformIsomorphismType := {X : Type u} → {Y : Type v} → [UniformSpace X] → [UniformSpace Y] → (X ≃ Y) → Prop
def UniformIsomorphismValue : UniformIsomorphismType := @UniformIsomorphism

@[instance_reducible]
def inducedUniformity {X : Type u} {Y : Type v} [uY : UniformSpace Y] (f : X → Y) : UniformSpace X :=
  UniformSpace.comap f uY

def inducedUniformityType := {X : Type u} → {Y : Type v} → [UniformSpace Y] → (X → Y) → UniformSpace X
def inducedUniformityValue : inducedUniformityType := @inducedUniformity

def UniformEmbedding {X : Type u} {Y : Type v} [uX : UniformSpace X] [UniformSpace Y] (f : X → Y) : Prop :=
  Function.Injective f ∧ inducedUniformity f = uX

def UniformEmbeddingType := {X : Type u} → {Y : Type v} → [UniformSpace X] → [UniformSpace Y] → (X → Y) → Prop
def UniformEmbeddingValue : UniformEmbeddingType := @UniformEmbedding

def CauchyFilter {X : Type u} [UniformSpace X] (F : Filter X) : Prop :=
  F.NeBot ∧ ∀ U ∈ 𝓤 X, ∃ A ∈ F, A ×ˢ A ⊆ U

def CauchyFilterType := {X : Type u} → [UniformSpace X] → Filter X → Prop
def CauchyFilterValue : CauchyFilterType := @CauchyFilter

def Complete (X : Type u) [UniformSpace X] : Prop :=
  ∀ F : Filter X, CauchyFilter F → ∃ x : X, Specs.D10Topology.Ch04.ProperFilters.FilterConverges F x

def CompleteType := (X : Type u) → [UniformSpace X] → Prop
def CompleteValue : CompleteType := @Complete

def TotallyBoundedSpace (X : Type u) [UniformSpace X] : Prop :=
  ∀ U ∈ 𝓤 X, ∃ C : Set X, C.Finite ∧ (⋃ x ∈ C, entourageBall U x) = univ

def TotallyBoundedSpaceType := (X : Type u) → [UniformSpace X] → Prop
def TotallyBoundedSpaceValue : TotallyBoundedSpaceType := @TotallyBoundedSpace

def relationInverse_preimage : Prop :=
  ∀ {X : Type u} (U : Set (X × X)), relationInverse U = Prod.swap ⁻¹' U

def relationInverse_image : Prop :=
  ∀ {X : Type u} (U : Set (X × X)), relationInverse U = Prod.swap '' U

def relationComp_mathlib : Prop :=
  ∀ {X : Type u} (U V : Set (X × X)), relationComp U V = V ○ U

def entourageBall_mathlib : Prop :=
  ∀ {X : Type u} (U : Set (X × X)) (x : X), entourageBall U x = UniformSpace.ball x U

def uniformity_axioms : Prop :=
  ∀ {X : Type u} [UniformSpace X], EntourageAxioms (𝓤 X)

def uniformity_iff_axioms : Prop :=
  ∀ {X : Type u} (F : Filter (X × X)), EntourageAxioms F ↔ ∃! uX : Uniformity X, @uniformity X uX = F

def uniformity_proper : Prop :=
  ∀ {X : Type u} [UniformSpace X] [Nonempty X], (𝓤 X).NeBot

def uniformity_empty : Prop :=
  ∀ {X : Type u} [UniformSpace X] [IsEmpty X], (𝓤 X).sets = {∅}

def uniformity_empty_unique : Prop :=
  ∀ {X : Type u} [IsEmpty X] (uX vX : Uniformity X), uX = vX

def separated_iff_mathlib : Prop :=
  ∀ {X : Type u} [UniformSpace X], Separated (X := X) ↔ T0Space X

def entourageContinuous_iff_mathlib : Prop :=
  ∀ {X : Type u} {Y : Type v} [UniformSpace X] [UniformSpace Y] (f : X → Y), EntourageContinuous f ↔ UniformContinuous f

def uniformIsomorphism_iff_mathlib : Prop :=
  ∀ {X : Type u} {Y : Type v} [UniformSpace X] [UniformSpace Y] (e : X ≃ Y), UniformIsomorphism e ↔ ∃ h : X ≃ᵤ Y, h.toEquiv = e

def inducedUniformity_entourages : Prop :=
  ∀ {X : Type u} {Y : Type v} [UniformSpace Y] (f : X → Y) (U : Set (X × X)), U ∈ @uniformity X (inducedUniformity f) ↔ ∃ V ∈ 𝓤 Y, (Prod.map f f) ⁻¹' V ⊆ U

def subspaceUniformity_entourages : Prop :=
  ∀ {X : Type u} [UniformSpace X] (A : Set X) (U : Set (A × A)), U ∈ 𝓤 A ↔ ∃ V ∈ 𝓤 X, (Prod.map Subtype.val Subtype.val) ⁻¹' V ⊆ U

def uniformEmbedding_iff_mathlib : Prop :=
  ∀ {X : Type u} {Y : Type v} [UniformSpace X] [UniformSpace Y] (f : X → Y), UniformEmbedding f ↔ IsUniformEmbedding f

def uniformEmbedding_iff_range : Prop :=
  ∀ {X : Type u} {Y : Type v} [UniformSpace X] [UniformSpace Y] (f : X → Y),
  UniformEmbedding f ↔ ∃ e : X ≃ range f, UniformIsomorphism e ∧ ∀ x, (e x).val = f x

def cauchyFilter_iff_mathlib : Prop :=
  ∀ {X : Type u} [UniformSpace X] (F : Filter X), CauchyFilter F ↔ Cauchy F

def complete_iff_mathlib : Prop :=
  ∀ {X : Type u} [UniformSpace X], Complete X ↔ CompleteSpace X

def cauchyFilter_proper : Prop :=
  ∀ {X : Type u} [UniformSpace X] (F : Filter X), CauchyFilter F → F.NeBot

def no_proper_filter_empty : Prop :=
  ∀ {X : Type u} [IsEmpty X], IsEmpty (Specs.D10Topology.Ch04.ProperFilters.ProperFilter X)

def no_cauchyFilter_empty : Prop :=
  ∀ {X : Type u} [UniformSpace X] [IsEmpty X] (F : Filter X), ¬ CauchyFilter F

def complete_empty : Prop :=
  ∀ {X : Type u} [UniformSpace X] [IsEmpty X], Complete X

def entourageContinuous_empty : Prop :=
  ∀ {X : Type u} {Y : Type v} [UniformSpace X] [UniformSpace Y] [IsEmpty X] (f : X → Y), EntourageContinuous f

def totallyBoundedSpace_iff_mathlib : Prop :=
  ∀ {X : Type u} [UniformSpace X], TotallyBoundedSpace X ↔ TotallyBounded (univ : Set X)

def empty_finite_cover : Prop :=
  ∀ {X : Type u} [IsEmpty X] (U : Set (X × X)), (∅ : Set X).Finite ∧ (⋃ x ∈ (∅ : Set X), entourageBall U x) = univ

def totallyBoundedSpace_empty : Prop :=
  ∀ {X : Type u} [UniformSpace X] [IsEmpty X], TotallyBoundedSpace X

def uniformity_proper_iff_nonempty : Prop :=
  ∀ {X : Type u} [UniformSpace X], (𝓤 X).NeBot ↔ Nonempty X

end Specs.D10Topology.Ch12.UniformConventions
