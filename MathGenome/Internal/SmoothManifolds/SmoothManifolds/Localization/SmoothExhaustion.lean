import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Localization.SmoothExhaustion
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Localization.Partitions

/-! M01.07(b): the sum of cutoff complements is locally finite. Its first
N terms equal one outside the Nth compact set, bounding every sublevel. -/
namespace SmoothManifolds
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]

/-- A smooth nonnegative exhaustion, including boundary and empty manifolds. -/
theorem exists_smooth_exhaustion (S : SmoothManifold n a M) :
    ∃ ρ : M → ℝ, ScalarSmooth S.smoothStructure.val ρ ∧
      (∀ x, 0 ≤ ρ x) ∧ ∀ c : ℝ, IsCompact {x | ρ x ≤ c} := by
  classical
  let : T2Space M := S.topologicalManifold.hausdorff
  obtain ⟨K, hK, hnest, hcover⟩ := TopologicalManifold.exists_compact_exhaustion S.topologicalManifold
  have hmono : Monotone K := monotone_nat_of_le_succ
    (fun j => (hnest j).trans interior_subset)
  have hcut (j : ℕ) : ∃ χ : M → ℝ, IsCutoff S (K j) (interior (K (j + 1))) χ :=
    exists_smooth_cutoff S (K j) (interior (K (j + 1)))
      (hK j).isClosed isOpen_interior (hnest j)
  choose χ hχ using hcut
  let f : ℕ → M → ℝ := fun j x => 1 - χ j x
  have hsmooth (j : ℕ) : ScalarSmooth S.smoothStructure.val (f j) := by
    intro x
    exact ScalarContDiffAt.add
      (ScalarContDiffAt.const _ _ 1 x) (ScalarContDiffAt.neg ((hχ j).1 x))
  have hnonneg (j : ℕ) (x : M) : 0 ≤ f j x := sub_nonneg.mpr ((hχ j).2.1 x).2
  have hsupp (j : ℕ) : sectionSupport (f j) ⊆ (K j)ᶜ := by
    obtain ⟨V, hV, hKV, hχV⟩ := (hχ j).2.2.1
    have hsub : sectionSupport (f j) ⊆ Vᶜ := by
      apply closure_minimal _ hV.isClosed_compl
      intro x hx hxV
      exact hx (by change 1 - χ j x = 0; rw [hχV hxV]; ring)
    exact hsub.trans (compl_subset_compl.mpr hKV)
  have hlf : LocallyFinite (fun j => sectionSupport (f j)) := by
    intro x
    have hx : x ∈ ⋃ (j : ℕ) (_ : 1 ≤ j), interior (K j) := by rw [hcover]; trivial
    obtain ⟨N, hxN⟩ := mem_iUnion.mp hx
    obtain ⟨_, hxN⟩ := mem_iUnion.mp hxN
    refine ⟨interior (K N), isOpen_interior.mem_nhds hxN,
      (Set.finite_lt_nat N).subset ?_⟩
    rintro j ⟨y, hy, hyN⟩
    by_contra hj
    exact hsupp j hy (hmono (Nat.le_of_not_gt hj) (interior_subset hyN))
  let ρ : M → ℝ := fun x => ∑ᶠ j, f j x
  have hρ : ScalarSmooth S.smoothStructure.val ρ := scalarContDiff_finsum hsmooth hlf
  have hρcont : Continuous ρ := continuous_iff_continuousAt.mpr
    (fun x => (scalarContDiffAt_iff _ _ _ x).mp (hρ x) |>.1)
  refine ⟨ρ, hρ, fun x => finsum_nonneg (fun j => hnonneg j x), ?_⟩
  intro c
  obtain ⟨N, hNc⟩ := exists_nat_gt c
  apply (hK N).of_isClosed_subset (isClosed_le hρcont continuous_const)
  intro x hx
  by_contra hxK
  have hfirst (j : ℕ) (hj : j ∈ Finset.range N) : f j x = 1 := by
    have hxχ : χ j x = 0 := by
      apply Function.notMem_support.mp
      intro hxχ
      exact hxK (hmono (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
        (interior_subset ((hχ j).2.2.2 (subset_closure hxχ))))
    simp [f, hxχ]
  have hfinite : (Function.support (fun j => f j x)).Finite :=
    (hlf.point_finite x).subset (fun _ hj => subset_closure hj)
  have hbound : (N : ℝ) ≤ ρ x := by
    let t := Finset.range N ∪ hfinite.toFinset
    have heq : ρ x = ∑ j ∈ t, f j x := by
      apply finsum_eq_sum_of_support_subset
      intro j hj
      exact Finset.mem_union_right _ (hfinite.mem_toFinset.mpr hj)
    rw [heq]
    calc
      (N : ℝ) = ∑ j ∈ Finset.range N, f j x := by
        rw [Finset.sum_congr rfl hfirst]
        simp
      _ ≤ ∑ j ∈ t, f j x := Finset.sum_le_sum_of_subset_of_nonneg
        Finset.subset_union_left (fun j _ _ => hnonneg j x)
  exact (not_lt_of_ge (hbound.trans hx)) hNc

end SmoothManifolds
