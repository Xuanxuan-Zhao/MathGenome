import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationConventions
import Mathlib.Topology.Instances.Real.Lemmas

/-! Independent specifications for paper.tex, d10:07:shrinking and d10:07:hierarchy.
Regularity and normality have no implicit separation or nonemptiness assumption.
The real example uses only upper rays as generators; its exact opens are also specified. -/

open Set
open scoped Topology
universe u

namespace Specs.D10Topology.Ch07.ShrinkingHierarchy

def regular_iff_shrinking : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], RegularSpace X ↔
    ∀ (x : X) (U : Set X), IsOpen U → x ∈ U →
      ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ closure V ∧ closure V ⊆ U

def normal_iff_shrinking : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], NormalSpace X ↔
    ∀ (F U : Set X), IsClosed F → IsOpen U → F ⊆ U →
      ∃ V : Set X, IsOpen V ∧ F ⊆ V ∧ V ⊆ closure V ∧ closure V ⊆ U

def t2_implies_t1 : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], T2Space X → T1Space X

def t1_implies_t0 : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], T1Space X → T0Space X

def completelyRegular_implies_regular : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    SeparationConventions.completelyRegularValue X → RegularSpace X

def regular_t0_implies_t1 : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], RegularSpace X → T0Space X → T1Space X

def regular_t0_implies_t3 : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], RegularSpace X → T0Space X →
    SeparationConventions.t3Value X

def t3_implies_t2 : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], SeparationConventions.t3Value X → T2Space X

def normal_t1_implies_regular : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], NormalSpace X → T1Space X → RegularSpace X

def t4_implies_t3 : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    SeparationConventions.t4Value X → SeparationConventions.t3Value X

/-- Canonical topology of the counterexample on the actual real numbers. -/
def upperRayTopologyValue : TopologicalSpace ℝ :=
  TopologicalSpace.generateFrom (range (fun a : ℝ => Ioi a))

def upperRayTopologyType := TopologicalSpace ℝ

def upperRay_opens : Prop :=
  ∀ U : Set ℝ, IsOpen[upperRayTopologyValue] U ↔
    U = ∅ ∨ U = univ ∨ ∃ a : ℝ, U = Ioi a

def upperRay_normal : Prop := @NormalSpace ℝ upperRayTopologyValue

def upperRay_obstruction : Prop :=
  @IsClosed ℝ upperRayTopologyValue (Iic 0) ∧ (1 : ℝ) ∉ Iic (0 : ℝ) ∧
    ¬ ∃ U V : Set ℝ, IsOpen[upperRayTopologyValue] U ∧
      IsOpen[upperRayTopologyValue] V ∧ (1 : ℝ) ∈ U ∧ Iic (0 : ℝ) ⊆ V ∧
      Disjoint U V

def upperRay_not_regular : Prop := ¬ @RegularSpace ℝ upperRayTopologyValue

end Specs.D10Topology.Ch07.ShrinkingHierarchy
