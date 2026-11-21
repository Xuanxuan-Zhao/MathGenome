import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.RealTietze
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.Piecewise
import Mathlib.Tactic.NormNum

/-!
Real Tietze extension (paper.tex, d10:07:tietze-real), with no T1 or
boundedness assumption.

The forward direction uses Mathlib's unbounded real extension theorem.
Its construction uses an order homeomorphism from the reals to (-1,1)
and an interval-preserving extension, so the inverse is applied only
inside that open interval. The converse extends the continuous 0/1
function on the union of two disjoint closed sets, then separates them
by open inverse images. No nonemptiness assumption is used.
-/

open Set
universe u

namespace D10Topology.Ch07

/-- Continuous real-valued functions on closed subspaces of normal spaces
extend, with no restriction on their range. -/
theorem tietze_real {X : Type u} [TopologicalSpace X] (hN : NormalSpace X)
    (A : Set X) (hA : IsClosed A) (f : A → ℝ) (hf : Continuous f) :
    ∃ F : X → ℝ, Continuous F ∧ ∀ x : A, F x = f x := by
  let : NormalSpace X := hN
  obtain ⟨F, hF⟩ := (⟨f, hf⟩ : C(A, ℝ)).exists_restrict_eq hA
  exact ⟨F, F.continuous, fun x => congrArg (fun g : C(A, ℝ) => g x) hF⟩

/-- Normality is equivalent to extension of every continuous real-valued
function on every closed subspace. Normality does not include T1. -/
theorem normal_iff_real_tietze (X : Type u) [TopologicalSpace X] :
    NormalSpace X ↔
      ∀ (A : Set X), IsClosed A → ∀ (f : A → ℝ), Continuous f →
        ∃ F : X → ℝ, Continuous F ∧ ∀ x : A, F x = f x := by
  classical
  constructor
  · exact fun hN => tietze_real hN
  · intro h
    refine ⟨fun A B hA hB hd => ?_⟩
    let C : Set X := A ∪ B
    let s : Set C := (Subtype.val : C → X) ⁻¹' A
    have hs : IsClosed s := hA.preimage continuous_subtype_val
    have hcompl : sᶜ = (Subtype.val : C → X) ⁻¹' B := by
      ext x
      change x.val ∉ A ↔ x.val ∈ B
      constructor
      · intro hx
        exact x.property.elim (fun ha => (hx ha).elim) id
      · intro hb ha
        exact Set.disjoint_left.mp hd ha hb
    have hsopen : IsOpen s := by
      rw [← isClosed_compl_iff, hcompl]
      exact hB.preimage continuous_subtype_val
    have hsfrontier : frontier s = ∅ := (show IsClopen s from ⟨hs, hsopen⟩).frontier_eq
    let f : C → ℝ := fun x => if x.val ∈ A then 0 else 1
    have hf : Continuous f := by
      apply Continuous.if (f := fun _ => (0 : ℝ)) (g := fun _ => (1 : ℝ))
        (p := fun x : C => x.val ∈ A) _ continuous_const continuous_const
      intro x hx
      change x ∈ frontier s at hx
      rw [hsfrontier] at hx
      exact hx.elim
    obtain ⟨F, hF, hFf⟩ := h (A ∪ B) (hA.union hB) f hf
    refine ⟨F ⁻¹' Iio (1 / 2 : ℝ), F ⁻¹' Ioi (1 / 2 : ℝ),
      isOpen_Iio.preimage hF, isOpen_Ioi.preimage hF, ?_, ?_, ?_⟩
    · intro x hx
      change F x < (1 / 2 : ℝ)
      rw [hFf ⟨x, Or.inl hx⟩]
      simp [f, hx]
    · intro x hx
      have hxA : x ∉ A := fun ha => Set.disjoint_left.mp hd ha hx
      change (1 / 2 : ℝ) < F x
      rw [hFf ⟨x, Or.inr hx⟩]
      norm_num [f, hxA]
    · apply Set.disjoint_left.mpr
      intro x hx hy
      change F x < (1 / 2 : ℝ) at hx
      change (1 / 2 : ℝ) < F x at hy
      exact lt_asymm hx hy

end D10Topology.Ch07
