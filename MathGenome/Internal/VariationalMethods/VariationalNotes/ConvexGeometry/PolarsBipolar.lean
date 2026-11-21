import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.Foundations
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.Separation
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.PolarsBipolar

open Set
open scoped Pointwise
noncomputable section
universe u
namespace VariationalNotes.ConvexGeometry

def supportFunction {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] (S : Set E) (l : E →L[ℝ] ℝ) : EReal :=
  Specs.supportFunction S l

def negativePolar {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] (S : Set E) : Set (E →L[ℝ] ℝ) :=
  Specs.negativePolar S

def primalPolar {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] (T : Set (E →L[ℝ] ℝ)) : Set E :=
  Specs.primalPolar T

def positiveDual {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] (S : Set E) : Set (E →L[ℝ] ℝ) :=
  Specs.positiveDual S

def primalPositiveDual {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] (T : Set (E →L[ℝ] ℝ)) : Set E :=
  Specs.primalPositiveDual T

def closedHalfspace {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] (l : E →L[ℝ] ℝ) (a : ℝ) : Set E :=
  Specs.closedHalfspace l a

def closedConicHull {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] (S : Set E) : Set E :=
  Specs.closedConicHull S

def normalCone {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] (C : Set E) (x : E) : Set (E →L[ℝ] ℝ) :=
  Specs.normalCone C x

section Basic
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

theorem supportFunction_empty :
  ∀ l : E →L[ℝ] ℝ, Specs.supportFunction (∅ : Set E) l = ⊥ := by
  intro l
  simp [Specs.supportFunction]

theorem negativePolar_supportFunction :
  ∀ (S : Set E) (l : E →L[ℝ] ℝ), l ∈ Specs.negativePolar S ↔ Specs.supportFunction S l ≤ 0 := by
  intro S l
  simp only [Specs.negativePolar, Set.mem_ofPred_eq, Specs.supportFunction, iSup_le_iff]
  simp

theorem positiveDual_eq_neg_polar :
  ∀ S : Set E, Specs.positiveDual S = -Specs.negativePolar S := by
  intro S
  ext l
  simp [Specs.positiveDual, Specs.negativePolar]

theorem primalPositiveDual_eq_neg_polar :
  ∀ T : Set (E →L[ℝ] ℝ), Specs.primalPositiveDual T = -Specs.primalPolar T := by
  intro T
  ext x
  simp [Specs.primalPositiveDual, Specs.primalPolar]

theorem empty_halfspace :
  Specs.closedHalfspace (0 : E →L[ℝ] ℝ) (-1) = ∅ := by
  ext x
  simp [Specs.closedHalfspace]

theorem normalCone_polar :
  ∀ (C : Set E) (x : E), Specs.normalCone C x = Specs.negativePolar ((fun z => z - x) '' C) := by
  intro C x
  ext l
  simp [Specs.normalCone, Specs.negativePolar]

end Basic

section Topological
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]

/-- The topological closure of the native, zero-containing conic hull. -/
def closedHullCone (S : Set E) : ProperCone ℝ E where
  toSubmodule := (PointedCone.hull ℝ S).closure
  isClosed' := isClosed_closure

theorem halfspace_properties :
  ∀ (l : E →L[ℝ] ℝ) (a : ℝ), IsClosed (Specs.closedHalfspace l a) ∧
    Convex ℝ (Specs.closedHalfspace l a) := by
  intro l a
  refine ⟨isClosed_le l.continuous continuous_const, ?_⟩
  exact (convex_Iic a).linear_preimage l.toLinearMap

theorem closedConicHull_properties :
  ∀ S : Set E, IsClosed (Specs.closedConicHull S) ∧ Specs.IsCone (Specs.closedConicHull S) ∧
    S ⊆ Specs.closedConicHull S ∧
    ∀ K : Set E, IsClosed K → Specs.IsCone K → S ⊆ K → Specs.closedConicHull S ⊆ K := by
  intro S
  let K := closedHullCone S
  refine ⟨isClosed_closure, ?_, ?_, ?_⟩
  · exact ⟨K.zero_mem, fun _ _ hx hy => K.add_mem hx hy,
      fun r hr _ hx => K.smul_mem hx hr⟩
  · exact fun x hx => subset_closure (PointedCone.subset_hull hx)
  · intro C hC hcone hSC
    apply closure_minimal _ hC
    exact (hull_properties S).2.2.2.2 C hcone hSC

theorem closedConicHull_empty :
  Specs.closedConicHull (∅ : Set E) = {0} := by
  change closure (PointedCone.hull ℝ (∅ : Set E) : Set E) = {0}
  simp

theorem polar_closedConicHull :
  ∀ S : Set E, Specs.negativePolar (Specs.closedConicHull S) = Specs.negativePolar S := by
  intro S
  ext l
  constructor
  · intro hl x hx
    exact hl x ((closedConicHull_properties S).2.2.1 hx)
  · intro hl
    have hc : IsCone {x : E | l x ≤ 0} := by
      refine ⟨by simp, ?_, ?_⟩
      · intro x y hx hy
        simpa using add_nonpos hx hy
      · intro r hr x hx
        simpa using mul_nonpos_of_nonneg_of_nonpos hr hx
    have hinc := (closedConicHull_properties S).2.2.2
      {x : E | l x ≤ 0} (isClosed_le l.continuous continuous_const) hc hl
    exact fun x hx => hinc hx

variable [LocallyConvexSpace ℝ E]

theorem halfspace_representation :
  ∀ C : Set E, IsClosed C → Convex ℝ C →
    C = ⋂ (l : E →L[ℝ] ℝ) (a : ℝ) (_ : C ⊆ Specs.closedHalfspace l a), Specs.closedHalfspace l a := by
  intro C hC hconv
  ext x
  simp only [Set.mem_iInter]
  constructor
  · intro hx l a hCa
    exact hCa hx
  · intro hx
    by_contra hnot
    obtain ⟨l, a, hlC, hlx⟩ := geometric_hahn_banach_closed_point hconv hC hnot
    exact (not_le_of_gt hlx) (hx l a (fun y hy => (hlC y hy).le))

theorem cone_bipolar :
  ∀ S : Set E, Specs.primalPolar (Specs.negativePolar S) = Specs.closedConicHull S := by
  intro S
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hnot
    obtain ⟨l, hlK, hlx⟩ := (closedHullCone S).hyperplane_separation_point hnot
    have hneg : -l ∈ Specs.negativePolar S := by
      intro y hy
      simpa using hlK y ((closedConicHull_properties S).2.2.1 hy)
    have h := hx (-l) hneg
    change -l x ≤ 0 at h
    linarith
  · intro x hx l hl
    have hlK : l ∈ Specs.negativePolar (Specs.closedConicHull S) :=
      (polar_closedConicHull S).symm ▸ hl
    exact hlK x hx

theorem cone_bipolar_empty :
  Specs.primalPolar (Specs.negativePolar (∅ : Set E)) = {0} := by
  rw [cone_bipolar, closedConicHull_empty]

theorem positive_bipolar :
  ∀ S : Set E, Specs.primalPositiveDual (Specs.positiveDual S) = Specs.closedConicHull S := by
  intro S
  rw [← cone_bipolar S]
  ext x
  constructor
  · intro hx l hl
    have hneg : -l ∈ Specs.positiveDual S := by
      intro y hy
      simpa using hl y hy
    simpa using hx (-l) hneg
  · intro hx l hl
    have hneg : -l ∈ Specs.negativePolar S := by
      intro y hy
      simpa using hl y hy
    simpa using hx (-l) hneg

theorem closed_cone_positive_bipolar :
  ∀ K : Set E, IsClosed K → Specs.IsCone K → Specs.primalPositiveDual (Specs.positiveDual K) = K := by
  intro K hK hcone
  rw [positive_bipolar K]
  exact Set.Subset.antisymm ((closedConicHull_properties K).2.2.2 K hK hcone Subset.rfl)
    (closedConicHull_properties K).2.2.1

end Topological
end VariationalNotes.ConvexGeometry
