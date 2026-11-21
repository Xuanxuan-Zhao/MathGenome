import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Localization.Extension
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Localization.Partitions

namespace SmoothManifolds
open Set Filter
open scoped Topology
universe u
variable {n k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]

/-- A finite vector is smooth exactly when each scalar coordinate is smooth.
The finite intersection of ambient neighborhoods also handles the zero vector space. -/
theorem manifoldContDiffToEuclideanAt_iff_coordinates (r : ℕ∞)
    (B : Set (ModelChart n a M)) (f : M → Euclidean k) (x : M) :
    ManifoldContDiffToEuclideanAt r B f x ↔
      ∀ j, ScalarContDiffAt r B (fun y => f y j) x := by
  constructor
  · rintro ⟨hc, he⟩ j
    apply (scalarContDiffAt_iff r B _ x).mpr
    refine ⟨(continuous_apply j).continuousAt.comp hc, ?_⟩
    intro e heB hxe
    obtain ⟨V, hV, hxV, F, hF, heq⟩ := he e heB hxe
    exact ⟨V, hV, hxV, fun z => F z j, (contDiffOn_pi.mp hF) j,
      heq.mono (fun _ h => congrFun h j)⟩
  · intro h
    have hj := fun j => (scalarContDiffAt_iff r B _ x).mp (h j)
    refine ⟨continuousAt_pi.mpr (fun j => (hj j).1), ?_⟩
    intro e heB hxe
    choose V hV hxV F hF heq using (fun j => (hj j).2 e heB hxe)
    refine ⟨⋂ j, V j, isOpen_iInter_of_finite hV, mem_iInter.mpr hxV,
      fun z j => F j z, contDiffOn_pi.mpr (fun j => (hF j).mono (iInter_subset V j)), ?_⟩
    exact (Filter.eventually_all.mpr heq).mono (fun _ h => funext h)

/-- Multiplying a local smooth function by a smooth weight with closed support
inside its domain gives a globally smooth function, with no bounds on the local function. -/
theorem scalarContDiff_mul_of_support_subset {r : ℕ∞}
    {B : Set (ModelChart n a M)} {w g : M → ℝ} {V : Set M}
    (hw : ScalarContDiff r B w) (hg : ∀ x ∈ V, ScalarContDiffAt r B g x)
    (hsupp : sectionSupport w ⊆ V) :
    ScalarContDiff r B (fun x => w x * g x) := by
  intro x
  by_cases hx : x ∈ sectionSupport w
  · exact ScalarContDiffAt.mul (hw x) (hg x (hsupp hx))
  · apply ScalarContDiffAt.congr (ScalarContDiffAt.const r B 0 x)
    filter_upwards [isClosed_closure.compl_mem_nhds hx] with y hy
    have hz : w y = 0 := Function.notMem_support.mp (fun h => hy (subset_closure h))
    simp [hz]

/-- The extension theorem for closed subsets, including noncompact subsets,
boundary manifolds, dimension zero, and empty domains. -/
theorem exists_supported_smooth_extension (S : SmoothManifold n a M) (A U : Set M)
    (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U)
    (f : A → Euclidean k) (hf : LocallySmoothOnSubset S.smoothStructure.val A f) :
    ∃ F : M → Euclidean k,
      (∀ x, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val F x) ∧
      (∀ x : A, F x.val = f x) ∧ sectionSupport F ⊆ U := by
  classical
  choose V hV hxV g hg heq using hf
  let W : Option A → Set M
    | none => Aᶜ
    | some x => V x ∩ U
  have hW : ∀ i, IsOpen (W i) := by
    intro i
    cases i with
    | none => exact hA.isOpen_compl
    | some x => exact (hV x).inter hU
  have hcover : ∀ y : M, ∃ i, y ∈ W i := by
    intro y
    by_cases hy : y ∈ A
    · exact ⟨some ⟨y, hy⟩, hxV ⟨y, hy⟩, hAU hy⟩
    · exact ⟨none, hy⟩
  obtain ⟨ρ, hρ, hsub⟩ := exists_smooth_partition S W hW hcover
  obtain ⟨hsm, hpos, hlf, hsum⟩ := hρ
  let G : Option A → M → Euclidean k
    | none => fun _ => 0
    | some x => g x
  let F : M → Euclidean k := fun y j => ∑ᶠ i, ρ i y * G i y j
  have hterm (i : Option A) (j : Fin k) :
      ScalarSmooth S.smoothStructure.val (fun y => ρ i y * G i y j) := by
    apply scalarContDiff_mul_of_support_subset (hsm i) (V := W i)
    · intro y hy
      cases i with
      | none => exact ScalarContDiffAt.const _ _ 0 y
      | some x =>
        exact (manifoldContDiffToEuclideanAt_iff_coordinates _ _ _ y).mp (hg x y hy.1) j
    · exact hsub i
  have htermsupp (j : Fin k) (i : Option A) :
      sectionSupport (fun y => ρ i y * G i y j) ⊆ sectionSupport (ρ i) := by
    apply closure_mono
    intro y hy
    exact left_ne_zero_of_mul hy
  refine ⟨F, ?_, ?_, ?_⟩
  · intro y
    apply (manifoldContDiffToEuclideanAt_iff_coordinates _ _ F y).mpr
    intro j
    exact scalarContDiff_finsum (fun i => hterm i j) (hlf.subset (htermsupp j)) y
  · intro x
    funext j
    have hval (i : Option A) : ρ i x.val * G i x.val j = ρ i x.val * f x j := by
      by_cases hz : ρ i x.val = 0
      · simp [hz]
      · have hxi := hsub i (subset_closure hz)
        cases i with
        | none => exact False.elim (hxi x.property)
        | some z => rw [show G (some z) x.val = f x from heq z x hxi.1]
    change (∑ᶠ i, ρ i x.val * G i x.val j) = f x j
    simp_rw [hval]
    rw [← finsum_mul, hsum x.val, one_mul]
  · let C : Set M := ⋃ x : A, sectionSupport (ρ (some x))
    have hCclosed : IsClosed C :=
      (hlf.comp_injective (Option.some_injective A)).isClosed_iUnion (fun _ => isClosed_closure)
    have hCU : C ⊆ U := by
      intro y hy
      obtain ⟨x, hx⟩ := mem_iUnion.mp hy
      exact (hsub (some x) hx).2
    apply Subset.trans (closure_minimal (t := C) ?_ hCclosed) hCU
    intro y hy
    by_contra hyC
    apply hy
    funext j
    change (∑ᶠ i, ρ i y * G i y j) = 0
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    cases i with
    | none => simp [G]
    | some x =>
      have hz : ρ (some x) y = 0 := Function.notMem_support.mp (fun h =>
        hyC (mem_iUnion.mpr ⟨x, subset_closure h⟩))
      simp [hz]

end SmoothManifolds
