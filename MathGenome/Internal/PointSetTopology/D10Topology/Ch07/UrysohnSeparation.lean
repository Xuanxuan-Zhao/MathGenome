import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.UrysohnSeparation
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.ShrinkingHierarchy
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Tactic.NormNum

/-! Urysohn separation and its two corollaries, with the paper's conventions. -/

open Set
universe u

namespace D10Topology.Ch07

variable (X : Type u) [TopologicalSpace X]

/-- Urysohn separation characterizes normality, without assuming T1. -/
theorem normal_iff_urysohn : Normal X ↔
    ∀ A B : Set X, IsClosed A → IsClosed B → Disjoint A B →
      ∃ f : X → unitInterval, Continuous f ∧
        (∀ x ∈ A, f x = 0) ∧ (∀ x ∈ B, f x = 1) := by
  constructor
  · intro hN A B hA hB hd
    let : NormalSpace X := hN
    obtain ⟨f, hfA, hfB, hfI⟩ := exists_continuous_zero_one_of_isClosed hA hB hd
    refine ⟨fun x => ⟨f x, hfI x⟩, f.continuous.subtype_mk _, ?_, ?_⟩
    · intro x hx
      exact Subtype.ext (hfA hx)
    · intro x hx
      exact Subtype.ext (hfB hx)
  · intro h
    apply (normal_iff_disjoint_open X).mpr
    intro A B hA hB hd
    obtain ⟨f, hf, hfA, hfB⟩ := h A B hA hB hd
    have hg : Continuous (fun x => (f x : ℝ)) := continuous_subtype_val.comp hf
    refine ⟨(fun x => (f x : ℝ)) ⁻¹' Iio (1 / 2 : ℝ),
      (fun x => (f x : ℝ)) ⁻¹' Ioi (1 / 2 : ℝ),
      isOpen_Iio.preimage hg, isOpen_Ioi.preimage hg, ?_, ?_, ?_⟩
    · intro x hx
      change (f x : ℝ) < (1 / 2 : ℝ)
      rw [hfA x hx]
      norm_num
    · intro x hx
      change (1 / 2 : ℝ) < (f x : ℝ)
      rw [hfB x hx]
      norm_num
    · apply Set.disjoint_left.mpr
      intro x hxU hxV
      change (f x : ℝ) < (1 / 2 : ℝ) at hxU
      change (1 / 2 : ℝ) < (f x : ℝ) at hxV
      exact lt_asymm hxU hxV

/-- A closed subset of an open set admits a continuous function with the
prescribed values on that closed subset and on the open set's complement. -/
theorem normal_closed_open_function (hN : Normal X)
    (F U : Set X) (hF : IsClosed F) (hU : IsOpen U) (hFU : F ⊆ U) :
    ∃ f : X → unitInterval, Continuous f ∧
      (∀ x ∈ F, f x = 1) ∧ (∀ x ∈ Uᶜ, f x = 0) := by
  have hd : Disjoint Uᶜ F := Set.disjoint_left.mpr fun x hxU hxF => hxU (hFU hxF)
  obtain ⟨f, hf, hfU, hfF⟩ :=
    (normal_iff_urysohn X).mp hN Uᶜ F hU.isClosed_compl hF hd
  exact ⟨f, hf, hfF, hfU⟩

/-- T4 means normal plus T1; Tychonoff means completely regular plus Hausdorff. -/
theorem t4_implies_tychonoff (h : T4 X) : Tychonoff X := by
  refine ⟨?_, t3_implies_t2 X (t4_implies_t3 X h)⟩
  let : T1Space X := h.2
  intro F hF x hx
  obtain ⟨f, hf, hfF, hfx⟩ := (normal_iff_urysohn X).mp h.1
    F {x} hF isClosed_singleton (Set.disjoint_singleton_right.mpr hx)
  exact ⟨f, hf, hfx x (mem_singleton x), hfF⟩

end D10Topology.Ch07
