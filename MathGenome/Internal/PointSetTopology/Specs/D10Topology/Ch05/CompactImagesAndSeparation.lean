import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Compactness
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch02.EmbeddingsAndCharacteristicMaps
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.QuotientMaps
import Mathlib.Topology.Order.Real

/-!
Independent statements for paper.tex d10:05:compact-image,
d10:05:compact-hausdorff, and d10:05:compact-bijection.
Compactness below is the source's open-cover property from the upstream
Specs. The domain of a continuous map need not be Hausdorff. All statements
permit empty spaces/compact subsets except the extreme-value assertion,
which explicitly requires a nonempty domain.
-/

open Set Topology
universe u v

namespace Specs.D10Topology.Ch05.CompactImagesAndSeparation
open Specs.D10Topology.Ch05.Compactness

def continuous_compact_image : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y), CoverCompact X → Continuous f → SubspaceCompact (range f)

def continuous_image_compact_subset : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (K : Set X),
    SubspaceCompact K → Continuous f → SubspaceCompact (f '' K)

def compact_point_separation : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X]
    (K : Set X), SubspaceCompact K → ∀ x : X, x ∉ K →
      ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ K ⊆ V ∧ Disjoint U V

def compact_subset_closed : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X]
    (K : Set X), SubspaceCompact K → IsClosed K

def disjoint_compact_separation : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X]
    (A B : Set X), SubspaceCompact A → SubspaceCompact B → Disjoint A B →
      ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧ Disjoint U V

def continuous_real_extrema : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [Nonempty X]
    (f : X → ℝ), CoverCompact X → Continuous f →
      ∃ xmin xmax : X, (∀ x, f xmin ≤ f x) ∧ (∀ x, f x ≤ f xmax)

def compact_to_hausdorff_closed : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (f : X → Y), CoverCompact X → Continuous f → IsClosedMap f

def compact_to_hausdorff_bijective : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (f : X → Y), CoverCompact X → Continuous f → Function.Bijective f → IsHomeomorph f

def compact_to_hausdorff_injective : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (f : X → Y), CoverCompact X → Continuous f → Function.Injective f → IsEmbedding f

def compact_to_hausdorff_surjective : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (f : X → Y), CoverCompact X → Continuous f → Function.Surjective f →
      _root_.D10Topology.Ch03.QuotientData.QuotientMap f

end Specs.D10Topology.Ch05.CompactImagesAndSeparation
