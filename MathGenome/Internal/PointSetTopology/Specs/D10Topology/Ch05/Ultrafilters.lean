import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch04.ProperFilters
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Compactness
import Mathlib.Order.Filter.Ultrafilter.Defs
import Mathlib.Order.Filter.Cofinite

/-! Independent statements for d10:05:ultrafilter, alternative, extension,
and the free-filter assertion of d10:05:ultranet. No topology, separation,
or nonempty-type assumption is imposed on the algebraic statements. -/

open Set Filter
universe u v
namespace Specs.D10Topology.Ch05.Ultrafilters
open Specs.D10Topology.Ch04.ProperFilters
open Specs.D10Topology.Ch05.Compactness

/-- Maximality is by inclusion of member families, among proper filters. -/
def IsUltrafilter {X : Type u} (F : Filter X) : Prop :=
  F.NeBot ∧ ∀ G : Filter X, G.NeBot → FilterFiner G F → G = F

/-- The filter whose members are exactly the sets containing x. -/
def principalUltrafilter {X : Type u} (x : X) : Filter X := pure x

/-- Freeness is the empty-intersection condition; properness is stated separately. -/
def FreeFilter {X : Type u} (F : Filter X) : Prop := ⋂₀ F.sets = ∅

/-- The original generating family of complements of finite subsets. -/
def finiteComplements (X : Type u) : Set (Set X) :=
  {A | ∃ K : Set X, K.Finite ∧ A = Kᶜ}

def cofiniteFilter (X : Type u) : Filter X := GeneratedFilter (finiteComplements X)

def isUltrafilterType : Type (u + 1) := {X : Type u} → Filter X → Prop
def isUltrafilterValue : isUltrafilterType := @IsUltrafilter

def principalUltrafilterType : Type (u + 1) := {X : Type u} → X → Filter X
def principalUltrafilterValue : principalUltrafilterType := @principalUltrafilter

def freeFilterType : Type (u + 1) := {X : Type u} → Filter X → Prop
def freeFilterValue : freeFilterType := @FreeFilter

def finiteComplementsType : Type (u + 1) := (X : Type u) → Set (Set X)
def finiteComplementsValue : finiteComplementsType := finiteComplements

def cofiniteFilterType : Type (u + 1) := (X : Type u) → Filter X
def cofiniteFilterValue : cofiniteFilterType := cofiniteFilter

/-- This bridge must check both properness and maximality, including filter order. -/
def isUltrafilter_iff_mathlib : Prop :=
  ∀ {X : Type u} (F : Filter X),
    IsUltrafilter F ↔ ∃ U : Ultrafilter X, (U : Filter X) = F

def principalUltrafilter_mem : Prop :=
  ∀ {X : Type u} (x : X) (A : Set X), A ∈ principalUltrafilter x ↔ x ∈ A

def principalUltrafilter_isUltrafilter : Prop :=
  ∀ {X : Type u} (x : X), IsUltrafilter (principalUltrafilter x)

def no_ultrafilter_on_empty : Prop :=
  ∀ {X : Type u} [IsEmpty X] (F : Filter X), ¬ IsUltrafilter F

/-- Both exhaustiveness and mutual exclusion are explicit. -/
def ultrafilter_alternative : Prop :=
  ∀ {X : Type u} (F : Filter X), F.NeBot →
    (IsUltrafilter F ↔ ∀ A : Set X,
      (A ∈ F ∨ Aᶜ ∈ F) ∧ ¬ (A ∈ F ∧ Aᶜ ∈ F))

def ultrafilter_converges_at_cluster : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (F : Filter X), IsUltrafilter F →
    ∀ x : X, FilterClusters F x → FilterConverges F x

def ultrafilter_image : Prop :=
  ∀ {X : Type u} {Y : Type v} (f : X → Y) (F : Filter X),
    IsUltrafilter F → IsUltrafilter (ImageFilter f F)

def proper_filter_extension : Prop :=
  ∀ {X : Type u} (F : Filter X), F.NeBot →
    ∃ U : Filter X, IsUltrafilter U ∧ FilterFiner U F

def fip_ultrafilter_extension : Prop :=
  ∀ {X : Type u} (A : Set (Set X)), HasFIP A →
    ∃ U : Filter X, IsUltrafilter U ∧ A ⊆ U.sets

def finiteComplements_mem : Prop :=
  ∀ (X : Type u) (A : Set X), A ∈ finiteComplements X ↔ Aᶜ.Finite

def cofiniteFilter_eq_mathlib : Prop :=
  ∀ (X : Type u), cofiniteFilter X = (Filter.cofinite : Filter X)

def finiteComplements_fip : Prop :=
  ∀ (X : Type u) [Infinite X], HasFIP (finiteComplements X)

def cofiniteFilter_proper : Prop :=
  ∀ (X : Type u) [Infinite X], (cofiniteFilter X).NeBot

def cofinite_extension_free : Prop :=
  ∀ {X : Type u} (F : Filter X), FilterFiner F (cofiniteFilter X) → FreeFilter F

def cofinite_ultrafilter_extension_free : Prop :=
  ∀ {X : Type u} [Infinite X] (U : Filter X), IsUltrafilter U →
    FilterFiner U (cofiniteFilter X) → FreeFilter U

def exists_free_ultrafilter : Prop :=
  ∀ (X : Type u) [Infinite X], ∃ U : Filter X,
    IsUltrafilter U ∧ FilterFiner U (cofiniteFilter X) ∧ FreeFilter U

end Specs.D10Topology.Ch05.Ultrafilters
