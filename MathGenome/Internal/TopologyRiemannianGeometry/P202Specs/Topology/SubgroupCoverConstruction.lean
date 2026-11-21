import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CoveringCriterion
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Subpath
import Mathlib.Topology.Bases

/-! The path-space construction in paper.tex, §1.7 (lines 364–426).

The total space is a dependent sum of quotients of endpoint-fixed path
classes. Thus endpoints are retained, and the second quotient identifies
exactly paths whose difference loop belongs to H. The topology is generated
by endpoint-extension sheets over open path connected sets whose loops die
in the ambient base. No covering, connectedness, or triviality certificate
is included in the definitions. -/
namespace P202Specs.Topology

open scoped unitInterval
universe u v
noncomputable section

variable {B : Type u} [TopologicalSpace B]

/-- Semilocal simple connectivity as stated in the source: only loops based
at the center of the neighborhood are required to die in the whole space. -/
def SemilocallySimplyConnected (B : Type u) [TopologicalSpace B] : Prop :=
  ∀ x : B, ∃ U : Set B, IsOpen U ∧ x ∈ U ∧
    ∀ a : SourcePath x x, (∀ t, a t ∈ U) → loopClass a = 1

/-- The eligible base neighborhoods used in the sheet construction. -/
def CoverNeighborhood (U : Set B) : Prop :=
  IsOpen U ∧ IsPathConnected U ∧
    ∀ x ∈ U, ∀ a : SourcePath x x, (∀ t, a t ∈ U) → loopClass a = 1

namespace SubgroupCover

variable (b : B) (H : Subgroup (Pi1 B b))

/-- Difference-loop relation at a fixed endpoint, in first-path-first order. -/
def classRel (z : B) (a c : PathClass b z) : Prop :=
  ofClass (a.trans c.symm) ∈ H

/-- This setoid uses just the path-groupoid laws, not local hypotheses. -/
def classSetoid (z : B) : Setoid (PathClass b z) where
  r := classRel b H z
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      change ofClass (a.trans a.symm) ∈ H
      rw [Path.Homotopic.Quotient.trans_symm]
      exact H.one_mem
    · intro a c h
      change ofClass (c.trans a.symm) ∈ H
      have heq : ofClass (c.trans a.symm) = (ofClass (a.trans c.symm))⁻¹ := by
        induction a using Path.Homotopic.Quotient.ind with | mk a =>
          induction c using Path.Homotopic.Quotient.ind with | mk c =>
            change ofClass (Path.Homotopic.Quotient.mk (c.trans a.symm)) =
              ofClass (Path.Homotopic.Quotient.mk (a.trans c.symm).symm)
            rw [Path.trans_symm, Path.symm_symm]
      rw [heq]
      exact H.inv_mem h
    · intro a c d hac hcd
      have heq : ofClass (a.trans d.symm) =
          ofClass (a.trans c.symm) * ofClass (c.trans d.symm) := by
        change ofClass (a.trans d.symm) =
          ofClass ((a.trans c.symm).trans (c.trans d.symm))
        apply congrArg ofClass
        simp only [Path.Homotopic.Quotient.trans_assoc,
          ← Path.Homotopic.Quotient.trans_assoc c.symm c,
          Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]
      change ofClass (a.trans d.symm) ∈ H
      rw [heq]
      exact H.mul_mem hac hcd

end SubgroupCover

/-- Paths from b, modulo the subgroup difference-loop relation, retaining
endpoints. This is the actual underlying set, before putting a topology on it. -/
def SubgroupCover (b : B) (H : Subgroup (Pi1 B b)) :=
  (z : B) × Quotient (SubgroupCover.classSetoid b H z)

namespace SubgroupCover

variable {b : B} (H : Subgroup (Pi1 B b))

/-- The class of an endpoint-fixed homotopy class. -/
def mkClass {z : B} (a : PathClass b z) : SubgroupCover b H :=
  ⟨z, Quotient.mk _ a⟩

/-- The class [a]_H of an actual path. -/
def mk {z : B} (a : SourcePath b z) : SubgroupCover b H :=
  mkClass H (Path.Homotopic.Quotient.mk a)

/-- Endpoint projection, defined without a continuity assumption. -/
def endpoint (q : SubgroupCover b H) : B := q.1

/-- The distinguished point is the class of the constant path at b. -/
def basepoint : SubgroupCover b H := mk H (Path.refl b)

/-- Extend a path class through U. No choice of representative or path to
an endpoint is built into this set. -/
def sheet {z : B} (a : PathClass b z) (U : Set B) : Set (SubgroupCover b H) :=
  {q | ∃ η : SourcePath z q.1, (∀ t, η t ∈ U) ∧
    mkClass H (a.trans (Path.Homotopic.Quotient.mk η)) = q}

/-- All the endpoint-extension sheets declared basic in the source. -/
def sheets : Set (Set (SubgroupCover b H)) :=
  {s | ∃ (z : B) (a : PathClass b z) (U : Set B), CoverNeighborhood U ∧ z ∈ U ∧ s = sheet H a U}

/-- This topology is constructed from sheets; its basis and covering properties
are conclusions, not inputs. -/
instance : TopologicalSpace (SubgroupCover b H) :=
  TopologicalSpace.generateFrom (sheets H)

/-- The prefix at time t, with its original initial point b. -/
def initialSegment {z : B} (a : SourcePath b z) (t : unitInterval) : SourcePath b (a t) :=
  (a.subpath 0 t).cast a.source.symm rfl

/-- The candidate path of classes associated to a, before proving continuity. -/
def prefixClasses {z : B} (a : SourcePath b z) (t : unitInterval) : SubgroupCover b H :=
  mk H (initialSegment a t)

end SubgroupCover

namespace SubgroupCoverExpected

/-- The equality relation is exactly the one in the source, not merely a
sufficient condition. Endpoints are part of the dependent-sum representation. -/
def quotientEquality : Prop :=
  ∀ (B : Type u) [TopologicalSpace B] (b z : B) (H : Subgroup (Pi1 B b))
    (a c : SourcePath b z),
    SubgroupCover.mk H a = SubgroupCover.mk H c ↔ loopClass (a.trans c.symm) ∈ H

/-- Every constructed point has an actual path representative. -/
def representatives : Prop :=
  ∀ (B : Type u) [TopologicalSpace B] (b : B) (H : Subgroup (Pi1 B b))
    (q : SubgroupCover b H), ∃ a : SourcePath b q.1, SubgroupCover.mk H a = q

/-- Eligible neighborhoods form a local basis under the original hypotheses. -/
def neighborhoodBasis : Prop :=
  ∀ (B : Type u) [TopologicalSpace B] [LocallyPathConnectedSpace B],
    SemilocallySimplyConnected B → ∀ (x : B) (V : Set B), IsOpen V → x ∈ V →
      ∃ U : Set B, x ∈ U ∧ U ⊆ V ∧ CoverNeighborhood U

/-- The generated topology has the declared sheets as a basis. -/
def sheetBasis : Prop :=
  ∀ (B : Type u) [TopologicalSpace B] [LocallyPathConnectedSpace B],
    SemilocallySimplyConnected B → ∀ (b : B) (H : Subgroup (Pi1 B b)),
      TopologicalSpace.IsTopologicalBasis (SubgroupCover.sheets H)

/-- Each basic sheet is homeomorphic to its given open base neighborhood,
and the homeomorphism is the endpoint projection. -/
def sheetHomeomorph : Prop :=
  ∀ (B : Type u) [TopologicalSpace B] [LocallyPathConnectedSpace B],
    SemilocallySimplyConnected B → ∀ (b z : B) (H : Subgroup (Pi1 B b))
      (a : PathClass b z) (U : Set B), CoverNeighborhood U → z ∈ U →
      ∃ e : SubgroupCover.sheet H a U ≃ₜ U,
        ∀ q, (e q).val = SubgroupCover.endpoint H q.val

/-- The actual endpoint map of the constructed topology is a surjective covering. -/
def covering : Prop :=
  ∀ (B : Type u) [TopologicalSpace B] [PathConnectedSpace B]
    [LocallyPathConnectedSpace B], SemilocallySimplyConnected B →
    ∀ (b : B) (H : Subgroup (Pi1 B b)), Covering (SubgroupCover.endpoint H)

/-- A prefix lift, including its endpoints and projection, in the constructed topology. -/
def prefixLift : Prop :=
  ∀ (B : Type u) [TopologicalSpace B] [LocallyPathConnectedSpace B],
    SemilocallySimplyConnected B → ∀ (b z : B) (H : Subgroup (Pi1 B b))
      (a : SourcePath b z),
      Continuous (SubgroupCover.prefixClasses H a) ∧
      SubgroupCover.prefixClasses H a 0 = SubgroupCover.basepoint H ∧
      SubgroupCover.prefixClasses H a 1 = SubgroupCover.mk H a ∧
      ∀ t, SubgroupCover.endpoint H (SubgroupCover.prefixClasses H a t) = a t

/-- Path connectedness of the constructed total space. -/
def pathConnected : Prop :=
  ∀ (B : Type u) [TopologicalSpace B] [PathConnectedSpace B]
    [LocallyPathConnectedSpace B], SemilocallySimplyConnected B →
    ∀ (b : B) (H : Subgroup (Pi1 B b)), PathConnectedSpace (SubgroupCover b H)

/-- Local path connectedness of the constructed total space. -/
def locallyPathConnected : Prop :=
  ∀ (B : Type u) [TopologicalSpace B] [PathConnectedSpace B]
    [LocallyPathConnectedSpace B], SemilocallySimplyConnected B →
    ∀ (b : B) (H : Subgroup (Pi1 B b)), LocallyPathConnectedSpace (SubgroupCover b H)

/-- The continuous pointed projection has precisely H as its image subgroup. -/
def imageSubgroup : Prop :=
  ∀ (B : Type u) [TopologicalSpace B] [PathConnectedSpace B]
    [LocallyPathConnectedSpace B], SemilocallySimplyConnected B →
    ∀ (b : B) (H : Subgroup (Pi1 B b))
      (hc : Continuous (SubgroupCover.endpoint H)),
      (⟨⟨SubgroupCover.endpoint H, hc⟩, rfl⟩ :
        PointedMap (SubgroupCover b H) B (SubgroupCover.basepoint H) b).induced.range = H

/-- The constructed cover for the trivial subgroup is simply connected. -/
def simplyConnected : Prop :=
  ∀ (B : Type u) [TopologicalSpace B] [PathConnectedSpace B]
    [LocallyPathConnectedSpace B], SemilocallySimplyConnected B →
    ∀ b : B, SimplyConnectedSpace (SubgroupCover b (⊥ : Subgroup (Pi1 B b)))

/-- A unique pointed continuous map over B from the constructed trivial-subgroup
cover to every connected pointed covering, including targets in any universe. -/
def universalProperty : Prop :=
  ∀ (B : Type u) (E : Type v) [TopologicalSpace B] [TopologicalSpace E]
    [PathConnectedSpace B] [LocallyPathConnectedSpace B] [ConnectedSpace E],
    SemilocallySimplyConnected B → ∀ (b : B) (e : E) (p : PointedMap E B e b),
      Covering p.map → ∃! L : C(SubgroupCover b (⊥ : Subgroup (Pi1 B b)), E),
        (∀ q, p.map (L q) = SubgroupCover.endpoint ⊥ q) ∧
        L (SubgroupCover.basepoint ⊥) = e

end SubgroupCoverExpected
end
end P202Specs.Topology
