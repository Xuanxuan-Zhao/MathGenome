import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.Equicontinuity
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch16.SupSpace
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
K03.16.equicontinuity: family radii, pointwise bounds, and common bounds.
The definitions use the canonical continuous maps, so ℝ and ℂ are obtained
by ordinary specialization. The first compactness implication uses Mathlib's
compact-domain equicontinuity theorem after explicit metric bridges.
For the second, a finite internal net at error 1 and the sum of the finitely
many nonnegative center bounds give a common bound. No nonempty hypothesis
on either the domain or the family is needed.
-/
namespace SingleVariableAnalysis

universe u
variable {E : Type u} [NormedAddCommGroup E]

abbrev PointwiseEquicontinuousFamily (K : Set ℝ) (F : Set C(K, E)) : Prop :=
  Specs.SingleVariableAnalysis.Ch16.Equicontinuity.pointwiseEquicontinuousFamilyValue K F

abbrev UniformlyEquicontinuousFamily (K : Set ℝ) (F : Set C(K, E)) : Prop :=
  Specs.SingleVariableAnalysis.Ch16.Equicontinuity.uniformlyEquicontinuousFamilyValue K F

abbrev PointwiseBoundedFamily (K : Set ℝ) (F : Set C(K, E)) : Prop :=
  Specs.SingleVariableAnalysis.Ch16.Equicontinuity.pointwiseBoundedFamilyValue K F

abbrev UniformlyBoundedFamily (K : Set ℝ) (F : Set C(K, E)) : Prop :=
  Specs.SingleVariableAnalysis.Ch16.Equicontinuity.uniformlyBoundedFamilyValue K F

/-- Family membership is exactly the subtype index in Mathlib equicontinuity. -/
theorem pointwiseEquicontinuousFamily_iff (K : Set ℝ) (F : Set C(K, E)) :
    PointwiseEquicontinuousFamily K F ↔ Equicontinuous (fun f : F => (f.val : K → E)) := by
  constructor
  · intro h x
    apply Metric.equicontinuousAt_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hball⟩ := h x ε hε
    refine ⟨δ, hδ, fun y hy f => ?_⟩
    simpa only [dist_eq_norm, norm_sub_rev] using hball y hy f.val f.property
  · intro h x ε hε
    obtain ⟨δ, hδ, hball⟩ := Metric.equicontinuousAt_iff.mp (h x) ε hε
    refine ⟨δ, hδ, fun y hy f hf => ?_⟩
    simpa only [dist_eq_norm, norm_sub_rev] using hball y hy ⟨f, hf⟩

/-- A single positive radius controls every pair and every family member. -/
theorem uniformlyEquicontinuousFamily_iff (K : Set ℝ) (F : Set C(K, E)) :
    UniformlyEquicontinuousFamily K F ↔
      UniformEquicontinuous (fun f : F => (f.val : K → E)) := by
  rw [Metric.uniformEquicontinuous_iff]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hball⟩ := h ε hε
    exact ⟨δ, hδ, fun x y hxy f => by
      simpa only [dist_eq_norm] using hball x y hxy f.val f.property⟩
  · intro h ε hε
    obtain ⟨δ, hδ, hball⟩ := h ε hε
    exact ⟨δ, hδ, fun x y hxy f hf => by
      simpa only [dist_eq_norm] using hball x y hxy ⟨f, hf⟩⟩

/-- Compactness upgrades the radius at each point to a radius for all pairs. -/
theorem compact_uniformEquicontinuity (K : Set ℝ) (hK : IsCompact K)
    (F : Set C(K, E)) (hF : PointwiseEquicontinuousFamily K F) :
    UniformlyEquicontinuousFamily K F := by
  let : CompactSpace K := supSpace_compact_subtype hK
  exact (uniformlyEquicontinuousFamily_iff K F).mpr
    (CompactSpace.uniformEquicontinuous_of_equicontinuous
      ((pointwiseEquicontinuousFamily_iff K F).mp hF))

/-- Pointwise boundedness of an equicontinuous family becomes a finite common bound. -/
theorem compact_uniformBoundedness (K : Set ℝ) (hK : IsCompact K)
    (F : Set C(K, E)) (hF : PointwiseEquicontinuousFamily K F)
    (hb : PointwiseBoundedFamily K F) : UniformlyBoundedFamily K F := by
  classical
  let : CompactSpace K := supSpace_compact_subtype hK
  obtain ⟨δ, hδ, hball⟩ := compact_uniformEquicontinuity K hK F hF 1 zero_lt_one
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp
    (isCompact_univ : IsCompact (Set.univ : Set K)).totallyBounded δ hδ
  let centers : Finset K := ht.toFinset
  have hnet : ∀ x : K, ∃ y ∈ centers, dist x y < δ := by
    intro x
    simpa only [Set.mem_iUnion, Metric.mem_ball, centers, Set.Finite.mem_toFinset, exists_prop]
      using hcover (Set.mem_univ x)
  choose M hMpos hM using hb
  refine ⟨1 + ∑ y ∈ centers, M y, ?_, ?_⟩
  · exact add_nonneg zero_le_one (Finset.sum_nonneg fun y _ => hMpos y)
  · intro f hf x
    obtain ⟨y, hy, hxy⟩ := hnet x
    have hsum : M y ≤ ∑ z ∈ centers, M z :=
      Finset.single_le_sum (fun z _ => hMpos z) hy
    calc
      ‖f x‖ ≤ ‖f x - f y‖ + ‖f y‖ := by
        calc
          ‖f x‖ = ‖(f x - f y) + f y‖ := by rw [sub_add_cancel]
          _ ≤ ‖f x - f y‖ + ‖f y‖ := norm_add_le _ _
      _ ≤ 1 + M y := add_le_add (hball x y hxy f hf).le (hM y f hf)
      _ ≤ 1 + ∑ z ∈ centers, M z := add_le_add le_rfl hsum

end SingleVariableAnalysis
