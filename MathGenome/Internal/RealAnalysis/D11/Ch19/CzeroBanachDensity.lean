import MathGenome.Internal.RealAnalysis.D11.Ch19.CcCzero
import MathGenome.Internal.RealAnalysis.D11.Ch18.CompactCutoff
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.CzeroBanachDensity

/-!
# The uniform Banach space C0 and density of Cc

The native C0 norm is induced by its bounded-continuous-map embedding.
Its completeness is the closed-range completeness theorem in that interface.
For density, a real cutoff equal to one on a compact norm level of f gives
the compactly supported function x ↦ φ(x) • f(x).
-/

namespace D11.Ch19

universe u v

def ccInclusion : Specs.D11.Ch19.CzeroBanachDensity.ccInclusionType.{u, v} :=
  Specs.D11.Ch19.CzeroBanachDensity.ccInclusionValue

def ccSubspace : Specs.D11.Ch19.CzeroBanachDensity.ccSubspaceType.{u, v} :=
  Specs.D11.Ch19.CzeroBanachDensity.ccSubspaceValue

theorem czero_bounded (X : Type u) [TopologicalSpace X] (𝕜 : Type v) [RCLike 𝕜]
    (f : Czero X 𝕜) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C :=
  ⟨‖f‖, norm_nonneg _, f.toBCF.norm_coe_le_norm⟩

theorem czero_norm_eq (X : Type u) [TopologicalSpace X] (𝕜 : Type v) [RCLike 𝕜]
    (f : Czero X 𝕜) : ‖f‖ = sInf {C : ℝ | 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C} :=
  BoundedContinuousFunction.norm_eq f.toBCF

theorem czero_norm_le_iff (X : Type u) [TopologicalSpace X] (𝕜 : Type v) [RCLike 𝕜]
    (f : Czero X 𝕜) (C : ℝ) (hC : 0 ≤ C) :
    ‖f‖ ≤ C ↔ ∀ x, ‖f x‖ ≤ C :=
  BoundedContinuousFunction.norm_le hC

theorem czero_scalar_operations (X : Type u) [TopologicalSpace X]
    (𝕜 : Type v) [RCLike 𝕜] (f g : Czero X 𝕜) (a : 𝕜) :
    (∀ x, (0 : Czero X 𝕜) x = 0) ∧
    (∀ x, (f + g) x = f x + g x) ∧
    (∀ x, (a • f) x = a * f x) ∧ ‖a • f‖ = ‖a‖ * ‖f‖ :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, norm_smul a f⟩

theorem czero_complete (X : Type u) [TopologicalSpace X] (𝕜 : Type v) [RCLike 𝕜] :
    CompleteSpace (Czero X 𝕜) := inferInstance

@[simp]
theorem cc_inclusion_apply (X : Type u) [TopologicalSpace X] (𝕜 : Type v) [RCLike 𝕜]
    (g : Cc X 𝕜) (x : X) : ccInclusion X 𝕜 g x = g x := rfl

theorem cc_inclusion_injective (X : Type u) [TopologicalSpace X]
    (𝕜 : Type v) [RCLike 𝕜] : Function.Injective (ccInclusion X 𝕜) := by
  intro f g h
  exact DFunLike.ext _ _ (fun x => congrArg (fun k : Czero X 𝕜 => k x) h)

theorem cc_subspace_mem_iff (X : Type u) [TopologicalSpace X]
    (𝕜 : Type v) [RCLike 𝕜] (f : Czero X 𝕜) :
    f ∈ ccSubspace X 𝕜 ↔ IsCompact (closure {x | f x ≠ 0}) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact g.hasCompactSupport
  · intro hf
    exact ⟨⟨f.toContinuousMap, hf⟩, rfl⟩

theorem cc_uniform_approximation (X : Type u) [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] (𝕜 : Type v) [RCLike 𝕜] (f : Czero X 𝕜)
    (ε : ℝ) (hε : 0 < ε) : ∃ g : Cc X 𝕜, ‖f - ccInclusion X 𝕜 g‖ ≤ ε := by
  have hK : IsCompact {x | ε ≤ ‖f x‖} :=
    (zeroAtInfinity_iff X 𝕜 f f.continuous).mp (zero_at_infty f) ε hε
  obtain ⟨φ, hφ, hφK, hφc, _⟩ :=
    D11.Ch18.compact_cutoff X {x | ε ≤ ‖f x‖} Set.univ hK isOpen_univ
      (Set.subset_univ _)
  let g : Cc X 𝕜 :=
    ⟨⟨fun x => φ x • f x, φ.continuous.smul f.continuous⟩,
      φ.hasCompactSupport.smul_right⟩
  refine ⟨g, (czero_norm_le_iff X 𝕜 _ ε hε.le).mpr ?_⟩
  intro x
  change ‖f x - φ x • f x‖ ≤ ε
  by_cases hx : ε ≤ ‖f x‖
  · rw [hφK x hx, one_smul, sub_self, norm_zero]
    exact hε.le
  · have hxlt : ‖f x‖ < ε := lt_of_not_ge hx
    have hφabs : ‖(1 : ℝ) - φ x‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hφ x).2)]
      exact sub_le_self _ (hφ x).1
    calc
      ‖f x - φ x • f x‖ = ‖((1 : ℝ) - φ x) • f x‖ := by rw [sub_smul, one_smul]
      _ = ‖(1 : ℝ) - φ x‖ * ‖f x‖ := norm_smul _ _
      _ ≤ 1 * ‖f x‖ := mul_le_mul_of_nonneg_right hφabs (norm_nonneg _)
      _ ≤ ε := by simpa only [one_mul] using hxlt.le

theorem cc_denseRange (X : Type u) [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] (𝕜 : Type v) [RCLike 𝕜] : DenseRange (ccInclusion X 𝕜) := by
  apply Metric.denseRange_iff.mpr
  intro f ε hε
  obtain ⟨g, hg⟩ := cc_uniform_approximation X 𝕜 f (ε / 2) (half_pos hε)
  exact ⟨g, (show dist f (ccInclusion X 𝕜 g) ≤ ε / 2 by
    simpa only [dist_eq_norm] using hg).trans_lt (half_lt_self hε)⟩

end D11.Ch19
