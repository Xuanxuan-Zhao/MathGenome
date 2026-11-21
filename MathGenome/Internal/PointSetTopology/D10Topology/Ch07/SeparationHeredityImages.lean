import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationHeredityImages
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.SeparationConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.Subspaces
import MathGenome.Internal.PointSetTopology.D10Topology.Ch02.ContinuityTests

/-!
Subspace heredity and closed-surjection preservation in paper.tex,
d10:07:heredity-products. Normality of a closed continuous image is proved
using complements of images of complements, without T1 or Hausdorffness.
-/

open Set Topology
universe u v

namespace D10Topology.Ch07

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

theorem subspace_t0 (A : Set X) (h : T0 X) : T0 A := by
  let := h
  exact IsEmbedding.subtypeVal.t0Space

theorem subspace_t1 (A : Set X) (h : T1 X) : T1 A := by
  let := h
  exact IsEmbedding.subtypeVal.t1Space

theorem subspace_t2 (A : Set X) (h : T2 X) : T2 A := by
  let := h
  exact IsEmbedding.subtypeVal.t2Space

theorem subspace_regular (A : Set X) (h : Regular X) : Regular A := by
  let := h
  exact IsInducing.subtypeVal.regularSpace

/-- Realize a relative closed set as a trace, then restrict its separator. -/
theorem subspace_completelyRegular (A : Set X) (h : CompletelyRegular X) :
    CompletelyRegular A := by
  intro F hF x hx
  obtain ⟨C, hC, rfl⟩ := (Ch03.subspace_closed_iff A F).mp hF
  obtain ⟨f, hf, hfx, hfC⟩ := h C hC x.val hx
  exact ⟨fun a : A => f a.val, Ch02.restriction_continuous f A hf,
    hfx, fun y hy => hfC y.val hy⟩

theorem subspace_normal_of_closed (A : Set X) (hA : IsClosed A) (h : Normal X) :
    Normal A := by
  let := h
  exact hA.isClosedEmbedding_subtypeVal.normalSpace

theorem subspace_t3 (A : Set X) (h : T3 X) : T3 A :=
  ⟨subspace_regular A h.1, subspace_t1 A h.2⟩

theorem subspace_tychonoff (A : Set X) (h : Tychonoff X) : Tychonoff A :=
  ⟨subspace_completelyRegular A h.1, subspace_t2 A h.2⟩

theorem subspace_t4_of_closed (A : Set X) (hA : IsClosed A) (h : T4 X) : T4 A :=
  ⟨subspace_normal_of_closed A hA h.1, subspace_t1 A h.2⟩

/-- The target neighborhoods consist of points whose entire fiber lies in
one of the source neighborhoods. Surjectivity makes every fiber nonempty. -/
theorem closed_surjection_normal (q : X → Y) (hq : Continuous q)
    (hc : IsClosedMap q) (hs : Function.Surjective q) (h : Normal X) : Normal Y := by
  apply (normal_iff_disjoint_open Y).mpr
  intro A B hA hB hAB
  have hd : Disjoint (q ⁻¹' A) (q ⁻¹' B) :=
    Set.disjoint_left.mpr fun _ hxA hxB => Set.disjoint_left.mp hAB hxA hxB
  obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ :=
    (normal_iff_disjoint_open X).mp h _ _ (hA.preimage hq) (hB.preimage hq) hd
  refine ⟨(q '' Uᶜ)ᶜ, (q '' Vᶜ)ᶜ, (hc _ hU.isClosed_compl).isOpen_compl,
    (hc _ hV.isClosed_compl).isOpen_compl, ?_, ?_, ?_⟩
  · rintro y hy ⟨x, hx, rfl⟩
    exact hx (hAU hy)
  · rintro y hy ⟨x, hx, rfl⟩
    exact hx (hBV hy)
  · apply Set.disjoint_left.mpr
    intro y hyU hyV
    obtain ⟨x, rfl⟩ := hs y
    have hxU : x ∈ U := by
      by_contra hx
      exact hyU ⟨x, hx, rfl⟩
    have hxV : x ∈ V := by
      by_contra hx
      exact hyV ⟨x, hx, rfl⟩
    exact Set.disjoint_left.mp hUV hxU hxV

/-- Continuity is unnecessary for preservation of T1 by a closed surjection. -/
theorem closed_surjection_t1 (q : X → Y) (hc : IsClosedMap q)
    (hs : Function.Surjective q) (h : T1 X) : T1 Y := by
  apply (t1_iff_closed_singletons Y).mpr
  intro y
  obtain ⟨x, rfl⟩ := hs y
  have hx := (t1_iff_closed_singletons X).mp h x
  simpa only [image_singleton] using hc {x} hx

theorem closed_surjection_t4 (q : X → Y) (hq : Continuous q)
    (hc : IsClosedMap q) (hs : Function.Surjective q) (h : T4 X) : T4 Y :=
  ⟨closed_surjection_normal q hq hc hs h.1, closed_surjection_t1 q hc hs h.2⟩

end D10Topology.Ch07
