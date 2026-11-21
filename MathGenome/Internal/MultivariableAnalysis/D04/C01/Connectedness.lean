import MathGenome.Internal.MultivariableAnalysis.D04.C01.ContinuousOperations
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.Connectedness
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.Fin.Tuple.Basic

/-! Connectedness, with universal pair-of-points conventions throughout.
The polygonal proof constructs finite chains in the upstream representation. -/
noncomputable section
open Set Topology
universe u v
namespace D04

theorem connected_image {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (A : Set X) (f : X → Y)
    (hA : IsPreconnected A) (hf : ContinuousOn f A) : IsPreconnected (f '' A) :=
  hA.image f hf

theorem interval_connected (I : Set ℝ) (hI : OrdConnected I) : IsPreconnected I :=
  hI.isPreconnected

theorem path_connected_space_connected {X : Type u} [TopologicalSpace X]
    (h : ∀ a b : X, Nonempty (Path a b)) : IsPreconnected (univ : Set X) := by
  apply isPreconnected_of_forall_pair
  intro a _ b _
  obtain ⟨p⟩ := h a b
  refine ⟨range p, subset_univ _, ?_, ?_, isPreconnected_range p.continuous⟩
  · exact ⟨0, p.source⟩
  · exact ⟨1, p.target⟩

theorem pathConnected_connected {n : ℕ} (A : Set (E n))
    (hA : PathConnected A) : Connected A := by
  have h : PreconnectedSpace A := preconnectedSpace_iff_univ.mpr
    (path_connected_space_connected hA)
  exact isPreconnected_iff_preconnectedSpace.mpr h

theorem convexSet_pathConnected {n : ℕ} (A : Set (E n))
    (hA : ConvexSet A) : PathConnected A := by
  intro a b
  exact (JoinedIn.of_segment_subset (hA.segment_subset a.property b.property)).joined_subtype

theorem connected_intermediate_value {X : Type u} [TopologicalSpace X]
    (A : Set X) (f : X → ℝ) (hA : IsPreconnected A) (hf : ContinuousOn f A)
    (a : X) (ha : a ∈ A) (b : X) (hb : b ∈ A) (c : ℝ)
    (hc : c ∈ uIcc (f a) (f b)) : ∃ x ∈ A, f x = c := by
  rcases le_total (f a) (f b) with hab | hba
  · exact hA.intermediate_value ha hb hf ((uIcc_of_le hab) ▸ hc)
  · exact hA.intermediate_value hb ha hf ((uIcc_of_ge hba) ▸ hc)

theorem relative_connected_image {n m : ℕ} (A : Set (E n)) (f : A → E m)
    (hA : Connected A) (hf : RelativeContinuous A f) : Connected (range f) := by
  let : PreconnectedSpace A := isPreconnected_iff_preconnectedSpace.mp hA
  exact isPreconnected_range ((relativeContinuous_iff A f).mp hf)

theorem relative_connected_intermediate_value {n : ℕ} (A : Set (E n)) (f : A → ℝ)
    (hA : Connected A) (hf : Continuous f) (a b : A) (c : ℝ)
    (hc : c ∈ uIcc (f a) (f b)) : ∃ x : A, f x = c := by
  let : PreconnectedSpace A := isPreconnected_iff_preconnectedSpace.mp hA
  obtain ⟨x, _, hx⟩ := connected_intermediate_value univ f isPreconnected_univ
    hf.continuousOn a (mem_univ _) b (mem_univ _) c hc
  exact ⟨x, hx⟩

/-- A zero-segment chain gives the constant polygonal path. -/
def polygonalPath_refl {n : ℕ} (U : Set (E n)) (a : U) : PolygonalPath U a a :=
  ⟨⟨0, fun _ => a.val⟩, rfl, rfl, fun i => Fin.elim0 i⟩

/-- Append one segment to a finite polygonal chain. -/
def polygonalPath_append_segment {n : ℕ} (U : Set (E n)) (a b c : U)
    (p : PolygonalPath U a b) (hbc : segment ℝ b.val c.val ⊆ U) :
    PolygonalPath U a c := by
  rcases p with ⟨⟨N, v⟩, hstart, hend, hseg⟩
  dsimp only at hstart hend hseg
  refine ⟨⟨N + 1, Fin.snoc v c.val⟩, ?_, ?_, ?_⟩
  · simpa using hstart
  · simp
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [hend] using hbc
    · simpa only [← Fin.castSucc_succ, Fin.snoc_castSucc] using hseg j

/-- Local convex balls propagate finite polygonal reachability. Both the
reachable set and its relative complement are open, so a connected domain
has just one such class. No nonempty-domain or positive-dimension assumption
is used: the basepoint is introduced only after the universal pair quantifier. -/
theorem open_connected_polygonallyConnected {n : ℕ} (U : Set (E n))
    (hU : Open U) (hconn : Connected U) : PolygonallyConnected U := by
  classical
  intro a b
  let P : Set (E n) := {x | ∃ hx : x ∈ U, Nonempty (PolygonalPath U a ⟨x, hx⟩)}
  have hPU : P ⊆ U := fun _ hx => hx.choose
  have haP : a.val ∈ P := ⟨a.property, ⟨polygonalPath_refl U a⟩⟩
  have extend (x y : E n) (hx : x ∈ P) (hy : y ∈ U)
      (hxy : segment ℝ x y ⊆ U) : y ∈ P := by
    obtain ⟨hxU, ⟨p⟩⟩ := hx
    exact ⟨hy, ⟨polygonalPath_append_segment U a ⟨x, hxU⟩ ⟨y, hy⟩ p hxy⟩⟩
  have hPo : IsOpen P := by
    rw [Metric.isOpen_iff]
    intro x hx
    obtain ⟨r, hr, hball⟩ := hU x (hPU hx)
    rw [ball_eq_metric] at hball
    refine ⟨r, hr, fun y hy => ?_⟩
    exact extend x y hx (hball hy)
      ((convex_ball x r).segment_subset (Metric.mem_ball_self hr) hy |>.trans hball)
  have hQo : IsOpen (U \ P) := by
    rw [Metric.isOpen_iff]
    rintro x ⟨hxU, hxP⟩
    obtain ⟨r, hr, hball⟩ := hU x hxU
    rw [ball_eq_metric] at hball
    refine ⟨r, hr, fun y hy => ⟨hball hy, ?_⟩⟩
    intro hyP
    apply hxP
    exact extend y x hyP hxU
      ((convex_ball x r).segment_subset hy (Metric.mem_ball_self hr) |>.trans hball)
  have hcover : U ⊆ P ∪ (U \ P) := by
    intro x hx
    by_cases hp : x ∈ P
    · exact Or.inl hp
    · exact Or.inr ⟨hx, hp⟩
  have hsub : U ⊆ P := hconn.subset_left_of_subset_union hPo hQo
    disjoint_sdiff_right hcover ⟨a.val, a.property, haP⟩
  obtain ⟨hb, hp⟩ := hsub b.property
  exact hp

end D04
