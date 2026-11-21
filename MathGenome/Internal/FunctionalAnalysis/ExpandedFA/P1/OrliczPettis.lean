import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.OrliczPettis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.NoCzeroWuc
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12ConvexClosure
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C15UnconditionalCriteria
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Filter Topology
open scoped BigOperators
noncomputable section
universe u v
namespace ExpandedFA.P1.OrliczPettis
open Spec NoCzeroWuc.Spec EquivalentBases.Spec

variable {𝕜 : Type u} [RCLike 𝕜]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The scalar subseries criterion gives absolute scalar summability. -/
theorem weakSubseries_wuc {x : ℕ → E} (h : EveryWeakSubseries (𝕜 := 𝕜) x) :
    WeaklyUnconditionallyCauchy (𝕜 := 𝕜) x := by
  intro f
  have hs : C15UnconditionalCriteria.EverySubseriesConverges (fun n => f (x n)) := by
    intro A
    obtain ⟨u, hu⟩ := h A
    exact ⟨f u, (C01Banach.hasSequentialSum_iff _ _ _).mpr (hu f)⟩
  exact summable_norm_iff.mpr
    ((C15Unconditional.unconditionallyConvergent_iff_summable _).mp
      ((C15UnconditionalCriteria.unconditionallyConvergent_iff_everySubseriesConverges _).mpr hs))

/-- Scalar tests characterize convergence for the canonical weak topology. -/
theorem weak_tendsto_of_scalar {α : Type*} {l : Filter α} {z : α → E} {u : E}
    (h : ∀ f : E →L[𝕜] 𝕜, Tendsto (fun i => f (z i)) l (𝓝 (f u))) :
    Tendsto z l
      (@nhds E (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜)
        (topDualPairing 𝕜 E)) u) := by
  rw [dualPairTopology_evaluation 𝕜 E, nhds_iInf]
  apply tendsto_iInf.mpr
  intro f
  rw [nhds_induced, tendsto_comap_iff]
  exact h f

/-- Absolute scalar summability permits disjoint finite blocks in any order. -/
theorem scalar_hasSum_blocks {a : ℕ → 𝕜}
    (F : ℕ → Finset ℕ) (hF : Pairwise (fun i j => Disjoint (F i) (F j)))
    {b : 𝕜} (hb : HasSum (({n | ∃ k, n ∈ F k} : Set ℕ).indicator a) b) :
    HasSum (fun k => ∑ n ∈ F k, a n) b := by
  classical
  let g : (Σ k, {n // n ∈ F k}) → ℕ := fun p => p.2.val
  have hg : Function.Injective g := by
    rintro ⟨i, n, hn⟩ ⟨j, m, hm⟩ heq
    have hnm : n = m := heq
    subst m
    have hij : i = j := by
      by_contra hij
      exact Finset.disjoint_left.mp (hF hij) hn hm
    subst j
    rfl
  have hs : HasSum (fun p : Σ k, {n // n ∈ F k} => a p.2.val) b := by
    have hh := (hg.hasSum_iff (f := ({n | ∃ k, n ∈ F k} : Set ℕ).indicator a)
      (fun n hn => by
        apply Set.indicator_of_notMem
        rintro ⟨k, hk⟩
        exact hn ⟨⟨k, ⟨n, hk⟩⟩, rfl⟩)).mpr hb
    convert hh using 1
    funext p
    exact (Set.indicator_of_mem (show p.2.val ∈ ({n | ∃ k, n ∈ F k} : Set ℕ)
      from ⟨p.1, p.2.property⟩) a).symm
  exact hs.sigma (fun k => (F k).hasSum a)

/-- The subseries on the union of disjoint blocks supplies their weak sum. -/
theorem weak_sum_disjoint_blocks {x : ℕ → E}
    (h : EveryWeakSubseries (𝕜 := 𝕜) x) (F : ℕ → Finset ℕ)
    (hF : Pairwise (fun i j => Disjoint (F i) (F j))) :
    ∃ u : E, ∀ f : E →L[𝕜] 𝕜,
      HasSum (fun k => f (∑ n ∈ F k, x n)) (f u) := by
  classical
  let A : Set ℕ := {n | ∃ k, n ∈ F k}
  obtain ⟨u, hu⟩ := h A
  refine ⟨u, fun f => ?_⟩
  have ha : Summable (fun n => f (x n)) := (weakSubseries_wuc h f).of_norm
  have hb : HasSum (A.indicator (fun n => f (x n))) (f u) :=
    ((ha.indicator A).hasSum_iff_tendsto_nat).mpr (hu f)
  simpa only [map_sum] using scalar_hasSum_blocks F hF hb

/-- A basic sequence with a weakly summable unit-coefficient series must be
norm null: its weak sum lies in the closed span and has all coordinates one. -/
theorem basic_weak_sum_norm_null [CompleteSpace E] {y : ℕ → E}
    (hy : IsBasicSequence (𝕜 := 𝕜) y) {u : E}
    (hu : ∀ f : E →L[𝕜] 𝕜, HasSum (fun n => f (y n)) (f u)) :
    Tendsto y atTop (𝓝 0) := by
  classical
  let S := closedSpan (𝕜 := 𝕜) y
  have hweak : Tendsto (fun N => ∑ n ∈ Finset.range N, y n) atTop
      (@nhds E (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜)
        (topDualPairing 𝕜 E)) u) := by
    apply weak_tendsto_of_scalar
    intro f
    simpa only [map_sum] using (hu f).tendsto_sum_nat
  have huS : u ∈ S := by
    have hclosed := C12ConvexClosure.isWeaklyClosed_of_isClosed_submodule 𝕜 E S
      (Submodule.isClosed_topologicalClosure _)
    exact @IsClosed.mem_of_tendsto E
      (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
      ℕ u S (fun N => ∑ n ∈ Finset.range N, y n) atTop inferInstance hclosed hweak
      (Eventually.of_forall (fun N => Submodule.sum_mem S
        (fun n _ => (spanVector (𝕜 := 𝕜) y n).property)))
  let z : S := ⟨u, huS⟩
  obtain ⟨b, hbe, hba, _⟩ := C15CoordinateContinuity.raw_native_basis hy
  have he (i : ℕ) : b i = spanVector y i := congrFun hbe i
  have hcoord (i : ℕ) : b.coord i z = 1 := by
    obtain ⟨f, hf, _⟩ := C05NormExtension.norm_preserving_extension 𝕜 E S (b.coord i)
    have hfy (j : ℕ) : f (y j) = if i = j then 1 else 0 := by
      rw [← show (spanVector (𝕜 := 𝕜) y j : E) = y j from rfl, hf, ← he]
      by_cases hij : i = j <;> simpa [Pi.single_apply, hij] using b.ortho i j
    have ht : Tendsto (fun N => ∑ n ∈ Finset.range N, f (y n)) atTop (𝓝 1) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop i] with N hN
      simp [hfy, hN]
    have hfu : f u = 1 := tendsto_nhds_unique (hu f).tendsto_sum_nat ht
    rw [← hf z]
    exact hfu
  have hnorm : Tendsto (fun N => ∑ n ∈ Finset.range N, y n) atTop (𝓝 u) := by
    have hz := C15Basis.rawCoordinates_tendsto hy z
    have heq : C15Basis.Spec.orderedPartialSum (spanVector (𝕜 := 𝕜) y)
        (C15Basis.Spec.rawCoordinates hy z) =
        (fun N => ∑ n ∈ Finset.range N, spanVector (𝕜 := 𝕜) y n) := by
      funext N
      simp only [C15Basis.Spec.orderedPartialSum, ← hba, hcoord, one_smul]
    change Tendsto (C15Basis.Spec.orderedPartialSum _
      (C15Basis.Spec.rawCoordinates hy z)) atTop (𝓝 z) at hz
    rw [heq] at hz
    simpa only [Function.comp_def, map_sum, Submodule.subtypeL_apply, spanVector, z] using
      (S.subtypeL.continuous.tendsto z).comp hz
  have hd := (hnorm.comp (tendsto_add_atTop_nat 1)).sub hnorm
  simpa only [Function.comp_def, Finset.sum_range_succ, add_sub_cancel_left, sub_self] using hd

/-- Orlicz–Pettis for real and complex Banach spaces, including the zero space. -/
theorem orlicz_pettis : Spec.OrliczPettis.{u,v} := by
  intro 𝕜 E _ _ _ _ x hx
  by_contra hn
  obtain ⟨ε, hε, F, hF, hlo⟩ := NoCzeroWuc.exists_nonvanishing_blocks hn
  let z : ℕ → E := fun k => ∑ n ∈ F k, x n
  have hw : WeaklyUnconditionallyCauchy (𝕜 := 𝕜) z :=
    NoCzeroWuc.wuc_disjoint_blocks (weakSubseries_wuc hx) F hF
  have hnz : ¬Tendsto z atTop (𝓝 0) := by
    intro hz
    have hh : ε ≤ 0 := by simpa using ge_of_tendsto hz.norm (Eventually.of_forall hlo)
    exact (not_le_of_gt hε) hh
  obtain ⟨φ, hφ, hb⟩ := BasicSelection.weakly_null_basic_subsequence z
    (NoCzeroWuc.wuc_weakly_null hw) hnz
  obtain ⟨u, hu⟩ := weak_sum_disjoint_blocks hx (F ∘ φ)
    (fun i j hij => hF (hφ.injective.ne hij))
  have hz0 := basic_weak_sum_norm_null hb hu
  have hh : ε ≤ 0 := by
    simpa using ge_of_tendsto hz0.norm (Eventually.of_forall (fun n => hlo (φ n)))
  exact (not_le_of_gt hε) hh

end ExpandedFA.P1.OrliczPettis
