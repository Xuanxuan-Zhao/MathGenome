import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.SmoothPartitionOfUnity
import Mathlib.Geometry.Manifold.PartitionOfUnity

open Set TopologicalSpace Function
open scoped Manifold ContDiff

namespace ExpandedFA.Distributions

/-- A compactly supported smooth function on an open domain extends by zero
to an ambient test function. -/
noncomputable def extendSmoothTest {d : ℕ} (Ω : Opens (Domain d))
    (f : C^∞⟮𝓘(ℝ, Domain d), Ω; 𝓘(ℝ), ℝ⟯) (hf : HasCompactSupport f) : Tests ℝ Ω where
  toFun := (Subtype.val : Ω → Domain d).extend f 0
  contDiff' := contMDiff_iff_contDiff.mp (ContMDiff.extend_zero hf f.contMDiff)
  hasCompactSupport' := hf.extend_zero continuous_subtype_val
  tsupport_subset' := (hf.tsupport_extend_zero_subset continuous_subtype_val).trans
    (Subtype.coe_image_subset _ _)

@[simp] theorem extendSmoothTest_apply {d : ℕ} (Ω : Opens (Domain d))
    (f : C^∞⟮𝓘(ℝ, Domain d), Ω; 𝓘(ℝ), ℝ⟯) (hf : HasCompactSupport f) (x : Ω) :
    extendSmoothTest Ω f hf x = f x := by
  exact Subtype.val_injective.extend_apply _ _ _

theorem extendSmoothTest_tsupport_subset {d : ℕ} (Ω : Opens (Domain d))
    (f : C^∞⟮𝓘(ℝ, Domain d), Ω; 𝓘(ℝ), ℝ⟯) (hf : HasCompactSupport f) :
    tsupport (extendSmoothTest Ω f hf) ⊆ Subtype.val '' tsupport f :=
  hf.tsupport_extend_zero_subset continuous_subtype_val

/-- Paper.tex, smooth partitions of unity: arbitrary covers are permitted,
while the subordinate compactly supported partition is countable. -/
theorem smooth_partition_of_unity :
    Specs.ExpandedFA.Distributions.SmoothPartitionOfUnity.partitionUnityType := by
  classical
  intro d Ω ι U hU hcover
  let : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  have hchoose (x : Ω) : ∃ i, (x : Domain d) ∈ U i :=
    mem_iUnion.mp (hcover x.property)
  choose ind hind using hchoose
  let V : Ω → Set Ω := fun x => (Subtype.val : Ω → Domain d) ⁻¹' U (ind x)
  have hV (x : Ω) : V x ∈ nhds x :=
    (hU (ind x)).preimage continuous_subtype_val |>.mem_nhds (hind x)
  obtain ⟨κ, b, hb⟩ := SmoothBumpCovering.exists_isSubordinate
    (𝓘(ℝ, Domain d)) (M := Ω) isClosed_univ (fun x _ => hV x)
  let : Encodable κ := b.locallyFinite.encodable (fun i => (b i).nonempty_support)
  let ρ := b.toSmoothPartitionOfUnity
  have hρ (k : κ) : HasCompactSupport (ρ k) :=
    (b k).hasCompactSupport.mono (b.support_toSmoothPartitionOfUnity_subset k)
  let φ : κ → Tests ℝ Ω := fun k => extendSmoothTest Ω (ρ k) (hρ k)
  have hφ (k : κ) : tsupport (φ k) ⊆ Subtype.val '' tsupport (ρ k) :=
    extendSmoothTest_tsupport_subset Ω (ρ k) (hρ k)
  refine ⟨κ, inferInstance, φ, ?_, ?_, ?_, ?_⟩
  · intro k x
    by_cases hx : x ∈ Ω
    · change 0 ≤ extendSmoothTest Ω (ρ k) (hρ k) (⟨x, hx⟩ : Ω)
      rw [extendSmoothTest_apply]
      exact ρ.nonneg k ⟨x, hx⟩
    · rw [(φ k).zero_on_compl hx]
      exact le_rfl
  · refine ρ.locallyFinite.closure.subset fun k x hx => ?_
    obtain ⟨y, hy, heq⟩ := hφ k hx
    have : y = x := Subtype.val_injective heq
    simpa only [this, tsupport] using hy
  · intro x hx
    calc
      (∑ᶠ k, φ k x) = ∑ᶠ k, ρ k (⟨x, hx⟩ : Ω) := by
        congr 1
        funext k
        exact extendSmoothTest_apply Ω (ρ k) (hρ k) ⟨x, hx⟩
      _ = 1 := ρ.sum_eq_one (mem_univ _)
  · intro k
    refine ⟨ind (b.c k), ?_⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hφ k hx
    exact hb.toSmoothPartitionOfUnity k hy

end ExpandedFA.Distributions
