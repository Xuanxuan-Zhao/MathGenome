import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.RelativeEuclideanApproximation
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Localization.Partitions
import Mathlib.Tactic.NormNum

namespace SmoothManifolds
open Set Filter
open scoped Topology
universe u

variable {n q : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]

/-- Coordinatewise scalar smoothness is equivalent to the shared vector test.
The intersection of the finitely many extension domains is still open.
This proof also covers the empty coordinate set. -/
theorem manifoldContDiffToEuclideanAt_iff_coordinates
    (r : ℕ∞) (B : Set (ModelChart n a M)) (f : M → Euclidean q) (x : M) :
    ManifoldContDiffToEuclideanAt r B f x ↔
      ∀ j : Fin q, ScalarContDiffAt r B (fun y => f y j) x := by
  classical
  constructor
  · rintro ⟨hc, he⟩ j
    apply (scalarContDiffAt_iff r B _ x).mpr
    refine ⟨(continuous_apply j).continuousAt.comp hc, ?_⟩
    intro e heB hxe
    obtain ⟨U, hU, hxU, F, hF, heq⟩ := he e heB hxe
    exact ⟨U, hU, hxU, fun z => F z j, (contDiffOn_pi.mp hF) j,
      heq.mono (fun _ h => congrFun h j)⟩
  · intro h
    have hc (j : Fin q) := (scalarContDiffAt_iff r B _ x).mp (h j)
    refine ⟨continuousAt_pi.mpr (fun j => (hc j).1), ?_⟩
    intro e heB hxe
    choose U hU hxU F hF heq using (fun j => (hc j).2 e heB hxe)
    refine ⟨⋂ j, U j, isOpen_iInter_of_finite hU, mem_iInter.mpr hxU,
      fun z j => F j z, contDiffOn_pi.mpr (fun j => (hF j).mono (iInter_subset U j)), ?_⟩
    have hh : ∀ᶠ y in 𝓝 x, ∀ j, F j (e y).val = f y j :=
      eventually_all.mpr heq
    exact hh.mono (fun _ hy => funext hy)

/-- Smooth scalar weights may multiply maps smooth only on an open set
containing the closed support of the weight. -/
theorem scalarContDiff_weighted_local {r : ℕ∞} {B : Set (ModelChart n a M)}
    {ρ f : M → ℝ} {U : Set M} (_hU : IsOpen U)
    (hρ : ScalarContDiff r B ρ) (hsupp : sectionSupport ρ ⊆ U)
    (hf : ∀ x ∈ U, ScalarContDiffAt r B f x) :
    ScalarContDiff r B (fun x => ρ x * f x) := by
  intro x
  by_cases hx : x ∈ U
  · exact ScalarContDiffAt.mul (hρ x) (hf x hx)
  · have hxs : x ∉ sectionSupport ρ := fun h => hx (hsupp h)
    apply ScalarContDiffAt.congr (ScalarContDiffAt.const r B 0 x)
    filter_upwards [isClosed_closure.compl_mem_nhds hxs] with y hy
    have hz : ρ y = 0 := by
      by_contra hz
      exact hy (subset_closure hz)
    simp [hz]

/-- A local smooth approximation with the relative equality, before averaging.
Only the restricted data on the closed set are extended. -/
theorem exists_local_relative_approximation
    (S : SmoothManifold n a M) (A : Set M) (F : M → Euclidean q) (ε : M → ℝ)
    (hA : IsClosed A) (hF : Continuous F) (hε : Continuous ε)
    (hpos : ∀ x, 0 < ε x)
    (hlocal : LocallySmoothOnSubset S.smoothStructure.val A (fun x => F x.val))
    (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ f : M → Euclidean q,
      (∀ y ∈ U, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val f y) ∧
      (∀ y ∈ U, y ∈ A → f y = F y) ∧
      ∀ y ∈ U, ‖WithLp.toLp 2 (f y - F y)‖ < ε y / 2 := by
  classical
  have shrink (U : Set M) (hU : IsOpen U) (hxU : x ∈ U)
      (f : M → Euclidean q) (hf : ContinuousAt f x) (hfx : f x = F x) :
      ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
        ∀ y ∈ V, ‖WithLp.toLp 2 (f y - F y)‖ < ε y / 2 := by
    have hcont : ContinuousAt (fun y => ‖WithLp.toLp 2 (f y - F y)‖) x :=
      ((PiLp.continuous_toLp 2 (fun _ : Fin q => ℝ)).continuousAt.comp
        (hf.sub hF.continuousAt)).norm
    have herr : ∀ᶠ y in 𝓝 x, ‖WithLp.toLp 2 (f y - F y)‖ < ε y / 2 := by
      apply hcont.eventually_lt (hε.continuousAt.div_const 2)
      simpa [hfx] using (div_pos (hpos x) (by norm_num : (0 : ℝ) < 2))
    obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds hxU) herr)
    exact ⟨V, hV, hxV, fun y hy => (hVsub hy).1, fun y hy => (hVsub hy).2⟩
  by_cases hx : x ∈ A
  · obtain ⟨U, hU, hxU, f, hf, heq⟩ := hlocal ⟨x, hx⟩
    have hfx : f x = F x := heq ⟨x, hx⟩ hxU
    obtain ⟨V, hV, hxV, hVU, herr⟩ := shrink U hU hxU f (hf x hxU).1 hfx
    exact ⟨V, hV, hxV, f, fun y hy => hf y (hVU hy),
      fun y hy hyA => heq ⟨y, hyA⟩ (hVU hy), herr⟩
  · obtain ⟨V, hV, hxV, hVA, herr⟩ := shrink Aᶜ hA.isOpen_compl hx
      (fun _ => F x) continuousAt_const rfl
    refine ⟨V, hV, hxV, fun _ => F x, ?_, ?_, herr⟩
    · intro y _
      exact (manifoldContDiffToEuclideanAt_iff_coordinates _ _ _ _).mpr
        (fun j => ScalarContDiffAt.const _ _ (F x j) y)
    · intro y hy hyA
      exact (hVA hy hyA).elim

/-- Relative approximation, obtained by a locally finite convex average of
smooth local representatives. The quantitative bound uses the Euclidean norm. -/
theorem exists_relative_euclidean_approximation
    (S : SmoothManifold n a M) (A : Set M) (F : M → Euclidean q) (ε : M → ℝ)
    (hA : IsClosed A) (hF : Continuous F) (hε : Continuous ε)
    (hpos : ∀ x, 0 < ε x)
    (hlocal : LocallySmoothOnSubset S.smoothStructure.val A (fun x => F x.val)) :
    ∃ G : M → Euclidean q,
      (∀ x, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val G x) ∧
      EqOn G F A ∧ ∀ x, ‖WithLp.toLp 2 (G x - F x)‖ < ε x := by
  classical
  choose U hU hxU f hf heq herr using
    exists_local_relative_approximation S A F ε hA hF hε hpos hlocal
  obtain ⟨ρ, hρ, hsub⟩ := exists_smooth_partition S U hU (fun x => ⟨x, hxU x⟩)
  obtain ⟨hρsmooth, hρpos, hρlf, hρsum⟩ := hρ
  let G : M → Euclidean q := fun x j => ∑ᶠ i, ρ i x * f i x j
  have hGsmooth : ∀ x, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val G x := by
    intro x
    apply (manifoldContDiffToEuclideanAt_iff_coordinates _ _ _ _).mpr
    intro j
    apply scalarContDiff_finsum (f := fun i x => ρ i x * f i x j) _ _ x
    · intro i
      apply scalarContDiff_weighted_local (hU i) (hρsmooth i) (hsub i)
      intro y hy
      exact (manifoldContDiffToEuclideanAt_iff_coordinates _ _ _ _).mp (hf i y hy) j
    · apply hρlf.subset
      intro i
      apply closure_mono
      intro y hy
      exact left_ne_zero_of_mul hy
  have hfin (x : M) : (Function.support (fun i => ρ i x)).Finite :=
    (hρlf.point_finite x).subset (fun i hi => subset_closure hi)
  have hGsum (x : M) :
      G x = ∑ i ∈ (hfin x).toFinset, ρ i x • f i x := by
    funext j
    change (∑ᶠ i, ρ i x * f i x j) = _
    have hs : Function.support (fun i => ρ i x * f i x j) ⊆ (hfin x).toFinset := by
      intro i hi
      exact (hfin x).mem_toFinset.mpr (left_ne_zero_of_mul hi)
    rw [finsum_eq_sum_of_support_subset _ hs]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hsum (x : M) : ∑ i ∈ (hfin x).toFinset, ρ i x = 1 := by
    rw [← finsum_eq_sum _ (hfin x)]
    exact hρsum x
  have hactive (x i : M) (hi : i ∈ (hfin x).toFinset) : x ∈ U i :=
    hsub i (subset_closure ((hfin x).mem_toFinset.mp hi))
  refine ⟨G, hGsmooth, ?_, ?_⟩
  · intro x hx
    rw [hGsum]
    calc
      (∑ i ∈ (hfin x).toFinset, ρ i x • f i x) =
          ∑ i ∈ (hfin x).toFinset, ρ i x • F x := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [heq i x (hactive x i hi) hx]
      _ = F x := by rw [← Finset.sum_smul, hsum, one_smul]
  · intro x
    have hdiff : G x - F x =
        ∑ i ∈ (hfin x).toFinset, ρ i x • (f i x - F x) := by
      simp_rw [smul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul, hGsum]
    calc
      ‖WithLp.toLp 2 (G x - F x)‖ =
          ‖∑ i ∈ (hfin x).toFinset, ρ i x • WithLp.toLp 2 (f i x - F x)‖ := by
        rw [hdiff, WithLp.toLp_sum]
        simp only [WithLp.toLp_smul]
      _ ≤ ∑ i ∈ (hfin x).toFinset, ‖ρ i x • WithLp.toLp 2 (f i x - F x)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i ∈ (hfin x).toFinset, ρ i x * (ε x / 2) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρpos i x)]
        exact mul_le_mul_of_nonneg_left (herr i x (hactive x i hi)).le (hρpos i x)
      _ = ε x / 2 := by rw [← Finset.sum_mul, hsum, one_mul]
      _ < ε x := half_lt_self (hpos x)

/-- The Euclidean-target clause of relative Whitney approximation, with a
continuous homotopy fixed pointwise on the prescribed closed set. -/
theorem relative_euclidean_approximation :
    Specs.SmoothManifolds.Ch04.RelativeEuclideanApproximation.relative_euclidean_approximationType := by
  intro n q a M _ S A F ε hA hF hε hpos hlocal
  obtain ⟨G, hG, hEq, herr⟩ :=
    exists_relative_euclidean_approximation S A F ε hA hF hε hpos hlocal
  have hGc : Continuous G := continuous_iff_continuousAt.mpr (fun x => (hG x).1)
  let H : Icc (0 : ℝ) 1 × M → Euclidean q :=
    fun z => (1 - z.1.val) • F z.2 + z.1.val • G z.2
  refine ⟨G, hG, hEq, herr, H, ?_, ?_, ?_, ?_⟩
  · exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (hF.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul (hGc.comp continuous_snd))
  · intro x
    simp [H]
  · intro x
    simp [H]
  · intro t x hx
    simp [H, hEq hx, ← add_smul]

end SmoothManifolds
