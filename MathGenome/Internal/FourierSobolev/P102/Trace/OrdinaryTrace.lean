import MathGenome.Internal.FourierSobolev.Specs.P102.Trace.OrdinaryTrace
import MathGenome.Internal.FourierSobolev.P102.Trace.FlatZeroTrace
import MathGenome.Internal.FourierSobolev.P102.Trace.FlatExactTrace
import MathGenome.Internal.FourierSobolev.P102.Trace.FlatTraceLift
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.HalfSpaceExtension
import MathGenome.Internal.FourierSobolev.P102.U4.MeyersSerrin
import MathGenome.Internal.FourierSobolev.P102.U4.BiLipschitzPullback
import MathGenome.Internal.FourierSobolev.P102.Sobolev.LipschitzGeometry
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach

import MathGenome.Internal.FourierSobolev.P102.Trace.OrdinaryTraceMap
/-!
The complete ordinary trace theorem. The analytic helpers are assembled
using the established trace-map results, including smooth compatibility,
cutoff compatibility, uniqueness, and the dimension-one endpoint formula.
-/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Pointwise ContDiff

namespace P102.Trace.Ordinary
open P102.U4 P102.U4.GraphPieces P102.Sobolev.Geometry
open P102.Sobolev.Extension

variable {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space (m + 1))} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An ambient test supported in Ω vanishes at every physical boundary point. -/
theorem test_zero_on_frontier (φ : TestSpace 𝕜 Ω)
    {x : Space (m + 1)} (hx : x ∈ frontier (Ω : Set (Space (m + 1)))) :
    φ x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hs
  have hxΩ := φ.tsupport_subset hs
  exact hx.2 (by rwa [Ω.isOpen.interior_eq])

/-- Smooth compatibility already forces zero trace for every compact interior
test, in every dimension and without a Lipschitz hypothesis. -/
theorem trace_test_eq_zero
    (T : Sobolev 𝕜 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (φ : TestSpace 𝕜 Ω) (u : Sobolev 𝕜 Ω 1 p)
    (hu : sobolevUnderlying u = testToDomainLp Ω p φ) : T u = 0 := by
  apply Lp.ext
  have hrep : (sobolevUnderlying u : Space (m + 1) → 𝕜) =ᵐ[
      volume.restrict (Ω : Set (Space (m + 1)))] φ := by
    rw [hu]
    exact testToDomainLp_ae Ω p φ
  have ht := hT u φ φ.contDiff hrep
  have hf : (φ : Space (m + 1) → 𝕜) =ᵐ[boundaryMeasure Ω] 0 := by
    filter_upwards [ae_restrict_mem measurableSet_frontier] with x hx
    exact test_zero_on_frontier φ hx
  exact (ht.trans hf).trans (Lp.coeFn_zero _ _ _).symm

/-- One kernel inclusion holds on any open set, using the genuine norm
closure of smooth compactly supported functions. -/
theorem sobolevZero_le_trace_ker
    (T : Sobolev 𝕜 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T) :
    sobolevZeroSubmodule 𝕜 Ω 1 p ≤ T.ker := by
  apply (smoothSobolevSubmodule 𝕜 Ω 1 p).topologicalClosure_minimal
  · intro u hu
    change ∃ φ, testToDomainLp Ω p φ = sobolevUnderlying u at hu
    obtain ⟨φ, hφ⟩ := hu
    exact trace_test_eq_zero T hT φ u hφ.symm
  · exact isClosed_singleton.preimage T.continuous

/-- W₀ membership gives the actual whole-space zero extension. The proof
uses the existing isometry; it does not build in weak-derivative identities
as an extra hypothesis. -/
theorem hasZeroExtension_of_mem_sobolevZero (u : Sobolev 𝕜 Ω 1 p)
    (hu : u ∈ sobolevZeroSubmodule 𝕜 Ω 1 p) : HasZeroExtension u := by
  exact ⟨sobolevZeroExtensionLI Ω 1 p ⟨u, hu⟩, rfl⟩

/-- Physical-coordinate mollification of a compact interior Sobolev class.
The output is an actual ambient smooth test whose topological support lies
in Ω. No smoothness of a preceding bi-Lipschitz change of coordinates is
used or inferred. This works at every integer order on an arbitrary open. -/
theorem exists_interior_test_approximation {d k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (u : Sobolev 𝕜 Ω k p) (hu : HasCompactSupportIn (sobolevUnderlying u))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (φ : TestSpace 𝕜 Ω) (v : Sobolev 𝕜 Ω k p),
      sobolevUnderlying v = testToDomainLp Ω p φ ∧ ‖v - u‖ < ε := by
  obtain ⟨K, hK, hvan⟩ := hu
  obtain ⟨w, hw, _, _⟩ := zeroExtension_compact Ω k p hp u ⟨K, hK, hvan⟩
  have hwhole : ∀ᵐ x ∂volume, x ∉ (K : Set (Space d)) →
      sobolevUnderlying w x = 0 := by
    rw [hw]
    have hvan' := (ae_restrict_iff' Ω.isOpen.measurableSet).mp hvan
    filter_upwards [lpZeroExtension_ae Ω p (sobolevUnderlying u), hvan']
      with x hx hv hxK
    rw [hx]
    by_cases hxΩ : x ∈ Ω
    · rw [Set.indicator_of_mem hxΩ]
      exact hv hxΩ hxK
    · exact Set.indicator_of_notMem hxΩ _
  obtain ⟨δ, hδ, _, hδΩ⟩ := exists_supportRadius K hK (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨φ, z, hz, herr, hs⟩ :=
    exists_mollified_approximation hp w K hwhole hδ hε
  let ψ : TestSpace 𝕜 Ω := ⟨φ, φ.contDiff, φ.hasCompactSupport, hs.trans hδΩ⟩
  have hback : sobolevRestrict Ω w = u := by
    apply sobolevUnderlying_injective Ω k p
    change domainLpRestrict Ω (sobolevUnderlying w) = _
    rw [hw, domainLpRestrict_zeroExtension]
  refine ⟨ψ, sobolevRestrict Ω z, ?_, ?_⟩
  · apply Lp.ext
    have hz0 := hz (zeroSobolevIndex d k)
    simp only [zeroSobolevIndex, multiPartial, Multiset.sort_zero, partialWord] at hz0
    exact ((P102.U4.domainLpRestrict_ae Ω (sobolevUnderlying z)).trans
      (ae_restrict_of_ae hz0)).trans (testToDomainLp_ae Ω p ψ).symm
  · calc
      ‖sobolevRestrict Ω z - u‖ = ‖sobolevRestrict Ω (z - w)‖ := by
        rw [← hback]
        exact congrArg norm ((sobolevRestrictCLM Ω).map_sub z w).symm
      _ ≤ ‖z - w‖ := sobolevRestrict_norm_le Ω _
      _ < ε := herr

/-- Compact interior support suffices for W₀ membership, by the physical
smooth approximation just constructed. -/
theorem mem_sobolevZero_of_compactSupport {d k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (u : Sobolev 𝕜 Ω k p) (hu : HasCompactSupportIn (sobolevUnderlying u)) :
    u ∈ sobolevZeroSubmodule 𝕜 Ω k p := by
  change u ∈ closure (smoothSobolevSubmodule 𝕜 Ω k p : Set (Sobolev 𝕜 Ω k p))
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨φ, v, hv, herr⟩ := exists_interior_test_approximation hp u hu hε
  refine ⟨v, ?_, ?_⟩
  · change ∃ φ, testToDomainLp Ω p φ = sobolevUnderlying v
    exact ⟨φ, hv.symm⟩
  · simpa only [dist_eq_norm', norm_sub_rev] using herr

/-- This closes the physical smoothing step for a convergent sequence of
compact interior Sobolev pieces. Each approximating piece may have been
obtained by a merely bi-Lipschitz pushforward. -/
theorem mem_sobolevZero_of_compactSupport_limit {d k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {u : Sobolev 𝕜 Ω k p} (v : ℕ → Sobolev 𝕜 Ω k p)
    (hv : ∀ n, HasCompactSupportIn (sobolevUnderlying (v n)))
    (ht : Tendsto v atTop (𝓝 u)) : u ∈ sobolevZeroSubmodule 𝕜 Ω k p := by
  apply (smoothSobolevSubmodule 𝕜 Ω k p).isClosed_topologicalClosure.mem_of_tendsto ht
  exact Filter.Eventually.of_forall fun n => mem_sobolevZero_of_compactSupport hp (v n) (hv n)

/-- Smooth compact interpolation of arbitrary data on a finite set. It is
used for the endpoint case, where the boundary has only finitely many atoms. -/
theorem exists_test_interpolating_finite {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {s : Set (Space d)} (hs : s.Finite) (g : Space d → 𝕜) :
    ∃ φ : WholeTests d 𝕜, ∀ x ∈ s, φ x = g x := by
  classical
  let : Fintype s := hs.fintype
  have hb (y : s) : ∃ b : Space d → ℝ,
      tsupport b ⊆ (s \ {y.val})ᶜ ∧ HasCompactSupport b ∧
      ContDiff ℝ (⊤ : ℕ∞) b ∧ Set.range b ⊆ Icc 0 1 ∧ b y = 1 := by
    apply exists_contDiff_tsupport_subset
    exact (hs.sdiff (t := {y.val})).isClosed.isOpen_compl.mem_nhds (by simp)
  choose b hb hc hd hr hv using hb
  let ψ (y : s) : WholeTests d 𝕜 :=
    ⟨fun x => b y x • g y, (hd y).smul contDiff_const, (hc y).smul_right, subset_univ _⟩
  refine ⟨∑ y : s, ψ y, ?_⟩
  intro x hx
  have heval : (∑ y : s, ψ y) x = ∑ y : s, b y x • g y := by
    simp [ψ]
  rw [heval, Finset.sum_eq_single (⟨x, hx⟩ : s)]
  · rw [hv]
    exact one_smul ℝ _
  · intro y _ hy
    have hxy : x ≠ y.val := by
      intro h
      apply hy
      exact Subtype.ext h.symm
    have hzero : b y x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      exact hb y hmem ⟨hx, by simpa using hxy⟩
    rw [hzero, zero_smul]
  · simp

/-- If the physical frontier is finite, smooth compatibility by itself gives
surjectivity: interpolate the finitely many boundary values by an ambient
smooth compact function, then restrict its Sobolev class to Ω. -/
theorem trace_surjective_of_finite_frontier
    (hfinite : (frontier (Ω : Set (Space (m + 1)))).Finite)
    (T : Sobolev 𝕜 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T) :
    Function.Surjective T := by
  intro g
  obtain ⟨φ, hφ⟩ := exists_test_interpolating_finite hfinite g
  obtain ⟨w, hw⟩ := wholeSpace_smoothTests 1 p φ
  refine ⟨sobolevRestrict Ω w, ?_⟩
  apply Lp.ext
  have hw0 := hw (zeroSobolevIndex (m + 1) 1)
  simp only [zeroSobolevIndex, multiPartial, Multiset.sort_zero, partialWord] at hw0
  have hrep : (sobolevUnderlying (sobolevRestrict Ω w) : Space (m + 1) → 𝕜) =ᵐ[
      volume.restrict (Ω : Set (Space (m + 1)))] φ :=
    (P102.U4.domainLpRestrict_ae Ω (sobolevUnderlying w)).trans (ae_restrict_of_ae hw0)
  have ht := hT _ φ φ.contDiff hrep
  apply ht.trans
  filter_upwards [ae_restrict_mem measurableSet_frontier] with x hx
  exact hφ x hx

/-- The one-dimensional quantitative surjectivity clause is completely
derived from the full frozen premises. The remaining higher-dimensional
local lifting argument is not assumed here. All four parameters have their
original universal types and their contract order. -/
theorem endpoint_surjectivity_oneDimension_conditional
    (_hCutoff : Expected.CutoffCompatibility)
    (hEndpoint : Expected.EndpointIdentification)
    (hTrace : Expected.TraceExists)
    (hUnique : Expected.TraceUniqueness) :
    ∀ (e : Ambient 0 ≃ₗᵢ[ℝ] Space 1) (Ω : Opens (Space 1)),
      IsLipschitzOpen (geometricOpen e Ω : Set (Ambient 0)) →
      ∀ (𝕜 : Type) [RCLike 𝕜],
      ∃ C : ℝ, 0 ≤ C ∧
        (∃ T : Sobolev 𝕜 Ω 1 1 →L[𝕜] BoundaryLp 𝕜 Ω 1, IsTrace T) ∧
        ∀ T : Sobolev 𝕜 Ω 1 1 →L[𝕜] BoundaryLp 𝕜 Ω 1, IsTrace T →
        ∀ g : BoundaryLp 𝕜 Ω 1,
          ∃ u : Sobolev 𝕜 Ω 1 1, T u = g ∧ ‖u‖ ≤ C * ‖g‖ := by
  intro e Ω hΩ 𝕜 _
  obtain ⟨_, _, T, hT, _, _⟩ := hTrace 0 e Ω hΩ 𝕜 1 (by simp)
  obtain ⟨_, n, a, b, _, _, _, _, hfront, _⟩ :=
    hEndpoint e Ω hΩ 𝕜 1 (by simp) T hT
  have hfinite : (frontier (Ω : Set (Space 1))).Finite := by
    rw [hfront]
    exact Set.finite_iUnion fun _ => by simp
  obtain ⟨C, hC, hpre⟩ :=
    T.exists_preimage_norm_le (trace_surjective_of_finite_frontier hfinite T hT)
  refine ⟨C, hC.le, ⟨T, hT⟩, ?_⟩
  intro S hS g
  have hST := hUnique 0 e Ω hΩ 𝕜 1 (by simp) S T hS hT
  rw [hST]
  exact hpre g

/-- The bulk extension recalled by the source follows from the stronger
fixed-formula upstream statement. This lemma does not assume that statement
has already been proved in this conditional draft. -/
theorem bulkExtension_of_extension
    (hE : P102.Sobolev.Extension.Expected.Extension) : Expected.BulkExtension := by
  intro m e Ω hΩ 𝕜 _ p _ _
  obtain ⟨D, K, C, B, _, h⟩ := hE m e Ω hΩ
  obtain ⟨E, _, hrest, hsupp, _⟩ := h 𝕜 p
  exact ⟨K, E, hrest, hsupp⟩

set_option maxHeartbeats 1200000 in
/-- The full cutoff premise supplies a bounded linear localization, not just
an unrelated choice of a Sobolev product for each input. Boundedness follows
from the closed graph theorem and the continuous injection into Lp. -/
theorem exists_sobolevCutoffCLM
    (hCutoff : Expected.CutoffCompatibility)
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m))) (hp : p ≠ ⊤)
    (T : Sobolev 𝕜 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (χ : Space (m + 1) → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ M : Sobolev 𝕜 Ω 1 p →L[𝕜] Sobolev 𝕜 Ω 1 p,
      (∀ u, sobolevUnderlying (M u) =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))]
        (fun x => χ x • sobolevUnderlying u x)) ∧
      ∀ u, (T (M u) : Space (m + 1) → 𝕜) =ᵐ[boundaryMeasure Ω]
        (fun x => χ x • T u x) := by
  classical
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hχ.continuous
  let B : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hb : ∀ᵐ x ∂volume.restrict (Ω : Set (Space (m + 1))), ‖χ x‖ ≤ B :=
    Filter.Eventually.of_forall fun x => (hC x).trans (le_max_left _ _)
  let A := realMultiplier (𝕜 := 𝕜) Ω p χ B hχ.continuous.aestronglyMeasurable hb
  let J := sobolevUnderlyingCLM (𝕜 := 𝕜) Ω 1 p
  have hinj : Function.Injective J := sobolevUnderlying_injective Ω 1 p
  have hex (u : Sobolev 𝕜 Ω 1 p) : ∃ v : Sobolev 𝕜 Ω 1 p, J v = A (J u) := by
    obtain ⟨v, hv⟩ := (hCutoff m e Ω hΩ 𝕜 p hp T hT χ hχ hc u).1
    refine ⟨v, Lp.ext (hv.trans ?_)⟩
    exact (realMultiplier_ae Ω p χ B hχ.continuous.aestronglyMeasurable hb (J u)).symm
  choose v hv using hex
  let L : Sobolev 𝕜 Ω 1 p →ₗ[𝕜] Sobolev 𝕜 Ω 1 p :=
    { toFun := v
      map_add' := fun u w => by
        apply hinj
        rw [map_add, hv, hv, hv, map_add, map_add]
      map_smul' := fun c u => by
        apply hinj
        rw [map_smul, hv, hv, map_smul, map_smul]
        rfl }
  have hgraph (us : ℕ → Sobolev 𝕜 Ω 1 p) (x y : Sobolev 𝕜 Ω 1 p)
      (hx : Tendsto us atTop (𝓝 x)) (hy : Tendsto (L ∘ us) atTop (𝓝 y)) : y = L x := by
    apply hinj
    change J y = J (v x)
    rw [hv]
    have hleft := (J.continuous.tendsto y).comp hy
    have hright := ((A.comp J).continuous.tendsto x).comp hx
    have heq : (J ∘ L ∘ us) = (A.comp J) ∘ us := by
      funext n
      exact hv (us n)
    rw [heq] at hleft
    exact tendsto_nhds_unique hleft hright
  let M := ContinuousLinearMap.ofSeqClosedGraph hgraph
  have hrep (u : Sobolev 𝕜 Ω 1 p) :
      sobolevUnderlying (M u) =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))]
        (fun x => χ x • sobolevUnderlying u x) := by
    change J (v u) =ᵐ[_] _
    rw [hv]
    exact realMultiplier_ae Ω p χ B hχ.continuous.aestronglyMeasurable hb (J u)
  exact ⟨M, hrep, fun u => (hCutoff m e Ω hΩ 𝕜 p hp T hT χ hχ hc u).2 _ (hrep u)⟩

/-- Finite localization reconstructs the original Sobolev class, including
its weak derivatives, because the zeroth-coordinate map is injective. -/
theorem sum_localized_eq {ι : Type*} [Fintype ι]
    (χ : ι → Space (m + 1) → ℝ)
    (hχ : ∀ x ∈ (Ω : Set (Space (m + 1))), ∑ i, χ i x = 1)
    (u : Sobolev 𝕜 Ω 1 p) (v : ι → Sobolev 𝕜 Ω 1 p)
    (hv : ∀ i, sobolevUnderlying (v i) =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))]
      (fun x => χ i x • sobolevUnderlying u x)) : ∑ i, v i = u := by
  apply sobolevUnderlying_injective Ω 1 p
  change (sobolevUnderlyingCLM Ω 1 p) (∑ i, v i) = _
  rw [map_sum]
  apply Lp.ext
  have hall := ae_all_iff.mpr hv
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => sobolevUnderlying (v i)),
    hall, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hvs hxΩ
  change (∑ i, sobolevUnderlying (v i)) x = _ at hx ⊢
  rw [hx]
  simp only [Finset.sum_apply]
  simp_rw [hvs]
  rw [← Finset.sum_smul, hχ x hxΩ, one_smul]

/-- The a.e. cutoff identity preserves zero trace for the same canonical
operator. No representative is evaluated on an exceptional boundary set. -/
theorem localized_trace_eq_zero
    (T : Sobolev 𝕜 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p)
    (u v : Sobolev 𝕜 Ω 1 p) (χ : Space (m + 1) → ℝ)
    (hv : (T v : Space (m + 1) → 𝕜) =ᵐ[boundaryMeasure Ω]
      (fun x => χ x • T u x)) (hu : T u = 0) : T v = 0 := by
  apply Lp.ext
  rw [hu] at hv
  filter_upwards [hv, Lp.coeFn_zero 𝕜 p (boundaryMeasure Ω)] with x hx hz
  simpa only [hz, Pi.zero_apply, smul_zero] using hx

/-- Interior partition pieces lie in the actual smooth-test closure, using
physical mollification, even if their input is not smooth. -/
theorem localized_mem_sobolevZero (hp : p ≠ ⊤)
    (χ : Space (m + 1) → ℝ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (Ω : Set (Space (m + 1))))
    (u v : Sobolev 𝕜 Ω 1 p)
    (hv : sobolevUnderlying v =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))]
      (fun x => χ x • sobolevUnderlying u x)) :
    v ∈ sobolevZeroSubmodule 𝕜 Ω 1 p := by
  apply mem_sobolevZero_of_compactSupport hp v
  refine ⟨⟨tsupport χ, hc⟩, hs, ?_⟩
  filter_upwards [hv] with x hx hxs
  rw [hx, image_eq_zero_of_notMem_tsupport hxs, zero_smul]

/-- Transfer the geometric finite partition into the physical Euclidean
space. Compact supports stay inside full charts; the interior piece stays
compactly inside Ω. This includes m=0 and disconnected or empty opens. -/
theorem exists_physical_partition
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m))) :
    ∃ (n : ℕ) (C : Fin n → BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
      (χ : Fin (n + 1) → Space (m + 1) → ℝ),
      (∀ i, ContDiff ℝ ∞ (χ i) ∧ HasCompactSupport (χ i) ∧ ∀ x, 0 ≤ χ i x) ∧
      (∀ x ∈ closure (Ω : Set (Space (m + 1))), ∑ i, χ i x = 1) ∧
      tsupport (χ 0) ⊆ (Ω : Set (Space (m + 1))) ∧
      ∀ i, tsupport (χ i.succ) ⊆ e ''
        chartImage (C i).frame (C i).graphFunction (C i).center (C i).radius (C i).height := by
  obtain ⟨n, C, r, a, hsmall, _, V, χ, _, hV, hχ, hsum, hinter, _, hboundary⟩ :=
    finite_localization m (geometricOpen e Ω : Set (Ambient m)) hΩ
  let ψ (i : Fin (n + 1)) : Space (m + 1) → ℝ := χ i ∘ e.symm
  have hsupport (i : Fin (n + 1)) :
      tsupport (ψ i) ⊆ e.symm ⁻¹' tsupport (χ i) :=
    tsupport_comp_subset_preimage (χ i) e.symm.continuous
  refine ⟨n, C, ψ, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(hχ i).1.comp e.symm.contDiff,
      (hχ i).2.1.comp_homeomorph e.symm.toHomeomorph, fun x => (hχ i).2.2 _⟩
  · intro x hx
    apply hsum
    apply hV
    have heq : (geometricOpen e Ω : Set (Ambient m)) =
        e.toHomeomorph.symm '' (Ω : Set (Space (m + 1))) := by
      ext z
      constructor
      · intro hz
        exact ⟨e z, hz, e.symm_apply_apply z⟩
      · rintro ⟨y, hy, rfl⟩
        change e (e.symm y) ∈ (Ω : Set (Space (m + 1)))
        rwa [e.apply_symm_apply]
    rw [heq, ← e.toHomeomorph.symm.image_closure]
    exact mem_image_of_mem _ hx
  · intro x hx
    have he := hinter (hsupport 0 hx)
    change e (e.symm x) ∈ (Ω : Set (Space (m + 1))) at he
    rwa [e.apply_symm_apply] at he
  · intro i x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    exact chartImage_mono (C i).frame (C i).graphFunction (C i).center
      (hsmall i).2.1.le (hsmall i).2.2.2.le (hboundary i (hsupport i.succ hx))

/-- A finite family of bounded linear physical localizations, with exact
reconstruction, preservation of the same trace kernel, and an interior
piece already in W₀. No chart trace-identification theorem is assumed. -/
theorem exists_sobolev_localization
    (hCutoff : Expected.CutoffCompatibility)
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m))) (hp : p ≠ ⊤)
    (T : Sobolev 𝕜 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T) :
    ∃ (n : ℕ) (C : Fin n → BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
      (χ : Fin (n + 1) → Space (m + 1) → ℝ)
      (M : Fin (n + 1) → Sobolev 𝕜 Ω 1 p →L[𝕜] Sobolev 𝕜 Ω 1 p),
      (∀ i, ContDiff ℝ ∞ (χ i) ∧ HasCompactSupport (χ i)) ∧
      tsupport (χ 0) ⊆ (Ω : Set (Space (m + 1))) ∧
      (∀ i, tsupport (χ i.succ) ⊆ e ''
        chartImage (C i).frame (C i).graphFunction (C i).center (C i).radius (C i).height) ∧
      (∀ i u, sobolevUnderlying (M i u) =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))]
        (fun x => χ i x • sobolevUnderlying u x)) ∧
      (∀ i u, (T (M i u) : Space (m + 1) → 𝕜) =ᵐ[boundaryMeasure Ω]
        (fun x => χ i x • T u x)) ∧
      (∀ u, ∑ i, M i u = u) ∧
      (∀ i u, T u = 0 → T (M i u) = 0) ∧
      ∀ u, M 0 u ∈ sobolevZeroSubmodule 𝕜 Ω 1 p := by
  classical
  obtain ⟨n, C, χ, hχ, hsum, hinter, hboundary⟩ := exists_physical_partition e hΩ
  have hM (i : Fin (n + 1)) :=
    exists_sobolevCutoffCLM hCutoff e hΩ hp T hT (χ i) (hχ i).1 (hχ i).2.1
  choose M hrep htrace using hM
  refine ⟨n, C, χ, M, fun i => ⟨(hχ i).1, (hχ i).2.1⟩,
    hinter, hboundary, hrep, htrace, ?_, ?_, ?_⟩
  · intro u
    exact sum_localized_eq χ (fun x hx => hsum x (subset_closure hx)) u _ (fun i => hrep i u)
  · intro i u hu
    exact localized_trace_eq_zero T u (M i u) (χ i) (htrace i u) hu
  · intro u
    exact localized_mem_sobolevZero hp (χ 0) (hχ 0).2.1 hinter u (M 0 u) (hrep 0 u)

/-- Essential compact support is transported by an actual bi-Lipschitz
chart. The inverse is only required to be continuous on its own open set. -/
theorem bilipschitz_pullback_compactSupport {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {U V : Opens (Space d)} {L M : ℝ≥0} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (g : BiLipschitzChart U V L M) (u : DomainLp 𝕜 U p)
    (hu : HasCompactSupportIn u) : HasCompactSupportIn (g.lpPullback 𝕜 p u) := by
  obtain ⟨K, hK, hvan⟩ := hu
  have hcompact : IsCompact (g.invFun '' (K : Set (Space d))) :=
    K.isCompact.image_of_continuousOn (g.inv_lipschitz.continuousOn.mono hK)
  refine ⟨⟨g.invFun '' (K : Set (Space d)), hcompact⟩, ?_, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    exact g.inv_mapsTo (hK hx)
  · filter_upwards [g.lpPullback_ae 𝕜 p u, g.ae_comp hvan,
      ae_restrict_mem V.isOpen.measurableSet] with x hx hv hxV hnot
    rw [hx]
    apply hv
    intro hxK
    exact hnot ⟨g.toFun x, hxK, g.left_inv x hxV⟩

/-- Compactly supported pullbacks can be approximated by genuine smooth
tests in the target coordinates. Smoothness of the chart is unnecessary. -/
theorem bilipschitz_pullback_mem_sobolevZero_of_compactSupport
    {d : ℕ} (hd : 0 < d) {𝕜 : Type} [RCLike 𝕜]
    {U V : Opens (Space d)} {L M : ℝ≥0} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (g : BiLipschitzChart U V L M) (u : Sobolev 𝕜 U 1 p)
    (hu : HasCompactSupportIn (sobolevUnderlying u)) :
    g.sobolevPullback meyersSerrin_smoothDensity hd 𝕜 p u ∈
      sobolevZeroSubmodule 𝕜 V 1 p := by
  apply mem_sobolevZero_of_compactSupport hp
  rw [g.sobolevPullback_underlying]
  exact bilipschitz_pullback_compactSupport g _ hu

/-- W₀ is invariant under bi-Lipschitz changes of coordinates. This passes
to the closure through a bounded Sobolev map, after physically smoothing
each transformed compact test, rather than declaring the transform smooth. -/
theorem bilipschitz_pullback_mem_sobolevZero
    {d : ℕ} (hd : 0 < d) {𝕜 : Type} [RCLike 𝕜]
    {U V : Opens (Space d)} {L M : ℝ≥0} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (g : BiLipschitzChart U V L M) (u : Sobolev 𝕜 U 1 p)
    (hu : u ∈ sobolevZeroSubmodule 𝕜 U 1 p) :
    g.sobolevPullback meyersSerrin_smoothDensity hd 𝕜 p u ∈
      sobolevZeroSubmodule 𝕜 V 1 p := by
  let A := g.sobolevPullback meyersSerrin_smoothDensity hd 𝕜 p
  have hle : smoothSobolevSubmodule 𝕜 U 1 p ≤
      (sobolevZeroSubmodule 𝕜 V 1 p).comap A.toLinearMap := by
    intro v hv
    obtain ⟨φ, hφ⟩ := hv
    change testToDomainLp U p φ = sobolevUnderlying v at hφ
    apply bilipschitz_pullback_mem_sobolevZero_of_compactSupport hd hp g v
    refine ⟨⟨tsupport φ, φ.hasCompactSupport⟩, φ.tsupport_subset, ?_⟩
    have hrep := testToDomainLp_ae U p φ
    rw [hφ] at hrep
    filter_upwards [hrep] with x hx hxs
    rw [hx]
    exact image_eq_zero_of_notMem_tsupport hxs
  have hclosed : IsClosed ((sobolevZeroSubmodule 𝕜 V 1 p).comap A.toLinearMap :
      Set (Sobolev 𝕜 U 1 p)) :=
    (smoothSobolevSubmodule 𝕜 V 1 p).isClosed_topologicalClosure.preimage A.continuous
  exact (smoothSobolevSubmodule 𝕜 U 1 p).topologicalClosure_minimal hle hclosed hu

/-- A zero-extended class retains its actual compact essential support,
including outside the original open set. -/
theorem lpZeroExtension_zero_off_compact {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {U : Opens (Space d)} {p : ℝ≥0∞} (u : DomainLp 𝕜 U p)
    (K : Compacts (Space d))
    (hu : ∀ᵐ x ∂volume.restrict (U : Set (Space d)), x ∉ K → u x = 0) :
    ∀ᵐ x ∂volume, x ∉ K → lpZeroExtension U p u x = 0 := by
  have hvan := (ae_restrict_iff' U.isOpen.measurableSet).mp hu
  filter_upwards [lpZeroExtension_ae U p u, hvan] with x hx hv hxK
  rw [hx]
  by_cases hxU : x ∈ U
  · rw [indicator_of_mem hxU]
    exact hv hxU hxK
  · exact indicator_of_notMem hxU _

/-- Zero extension from a smaller open and restriction to a larger open
preserves W₀. This is the gluing operation at artificial chart boundaries. -/
theorem zeroExtension_restrict_mem_sobolevZero {d k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {U V : Opens (Space d)} (hUV : U ≤ V)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (u : SobolevZero 𝕜 U k p) :
    sobolevRestrict V (sobolevZeroExtensionLI U k p u) ∈
      sobolevZeroSubmodule 𝕜 V k p := by
  classical
  obtain ⟨φ, v, hv, ht, _⟩ := smoothDensity_on_sobolevZero u
  have hrep (n : ℕ) : sobolevUnderlying (v n) =ᵐ[volume.restrict (U : Set (Space d))] φ n := by
    have h := hv n (zeroSobolevIndex d k)
    simpa only [sobolevUnderlying, zeroSobolevIndex, multiPartial, Multiset.sort_zero, partialWord] using h
  have hvU (n : ℕ) : HasCompactSupportIn (sobolevUnderlying (v n)) := by
    refine ⟨⟨tsupport (φ n), (φ n).hasCompactSupport⟩, (φ n).tsupport_subset, ?_⟩
    filter_upwards [hrep n] with x hx hxs
    exact hx.trans (image_eq_zero_of_notMem_tsupport hxs)
  let v₀ (n : ℕ) : SobolevZero 𝕜 U k p :=
    ⟨v n, mem_sobolevZero_of_compactSupport hp (v n) (hvU n)⟩
  have ht₀ : Tendsto v₀ atTop (𝓝 u) := by
    apply tendsto_subtype_rng.mpr
    exact ht
  let w (n : ℕ) := sobolevRestrict V (sobolevZeroExtensionLI U k p (v₀ n))
  apply mem_sobolevZero_of_compactSupport_limit hp w
  · intro n
    obtain ⟨K, hK, hvan⟩ := hvU n
    refine ⟨K, hK.trans hUV, ?_⟩
    have hw := lpZeroExtension_zero_off_compact (sobolevUnderlying (v n)) K hvan
    have hwr := P102.U4.domainLpRestrict_ae V
      (sobolevUnderlying (sobolevZeroExtensionLI U k p (v₀ n)))
    filter_upwards [hwr, ae_restrict_of_ae hw] with x hx hz hxK
    exact hx.trans (hz hxK)
  · exact ((sobolevRestrictCLM (𝕜 := 𝕜) V).continuous.comp
      (sobolevZeroExtensionLI U k p).continuous).tendsto u |>.comp ht₀

/-- Cutting off an actual whole-space zero extension gives an actual zero
extension of the localized input. No derivative formula is postulated. -/
theorem hasZeroExtension_localized
    (χ : Space (m + 1) → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (u v : Sobolev 𝕜 Ω 1 p)
    (hv : sobolevUnderlying v =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))]
      (fun x => χ x • sobolevUnderlying u x)) (hu : HasZeroExtension u) :
    HasZeroExtension v := by
  obtain ⟨w, hw⟩ := hu
  let a : WholeTests (m + 1) 𝕜 := TestFunction.postcompCLM RCLike.ofRealCLM
    ⟨χ, hχ, hc, subset_univ _⟩
  obtain ⟨z, hz⟩ := sobolev_testMul 1 p w a
  refine ⟨z, ?_⟩
  apply Lp.ext
  simp only [Opens.coe_top, Measure.restrict_univ]
  have hzrep := testMulLp_ae a (sobolevUnderlying w)
  rw [← hz] at hzrep
  have hwrep := lpZeroExtension_ae Ω p (sobolevUnderlying u)
  rw [← hw] at hwrep
  have hvrep := indicator_ae_eq Ω hv
  filter_upwards [hzrep, hwrep, lpZeroExtension_ae Ω p (sobolevUnderlying v), hvrep]
    with x hx hxw hxv hxprod
  rw [hx, hxw, hxv, hxprod]
  change (χ x : 𝕜) * (Ω : Set (Space (m + 1))).indicator (sobolevUnderlying u) x = _
  by_cases hxΩ : x ∈ Ω
  · simp only [indicator_of_mem hxΩ, RCLike.real_smul_eq_coe_mul]
  · simp only [indicator_of_notMem hxΩ, mul_zero]

/-- Pairing a zero extension restricted to another open with a target test
is the original-domain pairing with that same ambient test function. -/
theorem lpTestPairing_zeroExtension_restrict {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U V : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : DomainLp 𝕜 U p) (φ : TestSpace 𝕜 V) :
    lpTestPairing V p φ (domainLpRestrict V (lpZeroExtension U p f)) =
      ∫ x in U, f x * φ x := by
  rw [P102.U4.lpTestPairing_restrict, lpTestPairing_eq_integral]
  simp only [Opens.coe_top, Measure.restrict_univ, zeroExtension,
    TestFunction.monoCLM_apply, le_refl, le_top, and_self, ite_true]
  change (∫ x, lpZeroExtension U p f x * φ x) = _
  exact integral_lpZeroExtension_mul U p f φ

/-- Extend by zero across an artificial edge, relatively to a target open.
The two domains only need to agree on the target side of a neighborhood of
the compact support. The support may meet their genuine boundary. Thus this
does not assume a zero trace, W₀ membership, or a global zero extension.
Every weak derivative is transferred and the full Sobolev norm decreases. -/
theorem transfer_across_artificial_boundary {d k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {U V W : Opens (Space d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (K : Compacts (Space d)) (hKW : (K : Set (Space d)) ⊆ W)
    (hVU : (V : Set (Space d)) ∩ (W : Set (Space d)) ⊆ U)
    (u : Sobolev 𝕜 U k p)
    (hu : ∀ᵐ x ∂volume.restrict (U : Set (Space d)),
      x ∉ K → sobolevUnderlying u x = 0) :
    ∃ v : Sobolev 𝕜 V k p,
      (∀ α, sobolevDerivative v α =
        domainLpRestrict V (lpZeroExtension U p (sobolevDerivative u α))) ∧
      ‖v‖ ≤ ‖u‖ := by
  obtain ⟨χ, _, N, hKN, _, hχ⟩ := cutoff d W K hKW
  let χk : TestSpace 𝕜 W := TestFunction.postcompCLM RCLike.ofRealCLM χ
  let F : SobolevTuple 𝕜 V k p := WithLp.toLp 1
    (fun α => domainLpRestrict V (lpZeroExtension U p (sobolevDerivative u α)))
  have hF : F ∈ sobolevSubmodule 𝕜 V k p := by
    apply (mem_sobolevSubmodule_iff V k p F).mpr
    intro α φ
    let ψ : TestSpace 𝕜 U := ⟨fun x => χk x * φ x,
      χk.contDiff.mul φ.contDiff, χk.hasCompactSupport.mul_right, by
        intro x hx
        exact hVU ⟨φ.tsupport_subset (tsupport_mul_subset_right hx),
          χk.tsupport_subset (tsupport_mul_subset_left hx)⟩⟩
    have hψ (x : Space d) (hx : x ∈ N) : ψ x = φ x := by
      change (RCLike.ofReal (χ x)) * φ x = φ x
      simp only [hχ x hx, RCLike.ofReal_one, one_mul]
    have hder (x : Space d) (hx : x ∈ K) :
        testPartialWord U (α.val.sort (· ≤ ·)) ψ x =
          testPartialWord V (α.val.sort (· ≤ ·)) φ x := by
      rw [testPartialWord_coe, testPartialWord_coe]
      have he : (ψ : Space d → 𝕜) =ᶠ[𝓝 x] φ := by
        filter_upwards [N.isOpen.mem_nhds (hKN hx)] with y hy
        exact hψ y hy
      exact (partialWord_eventuallyEq he _).eq_of_nhds
    have hleft : (∫ x in U, sobolevDerivative u α x * φ x) =
        ∫ x in U, sobolevDerivative u α x * ψ x := by
      apply integral_congr_ae
      filter_upwards [sobolevDerivative_zero_off_compact U k p u K hu α] with x hx
      by_cases hxK : x ∈ K
      · rw [hψ x (hKN hxK)]
      · simp only [hx hxK, zero_mul]
    have hright : (∫ x in U, sobolevUnderlying u x *
        testPartialWord V (α.val.sort (· ≤ ·)) φ x) =
        ∫ x in U, sobolevUnderlying u x *
          testPartialWord U (α.val.sort (· ≤ ·)) ψ x := by
      apply integral_congr_ae
      filter_upwards [hu] with x hx
      by_cases hxK : x ∈ K
      · rw [hder x hxK]
      · simp only [hx hxK, zero_mul]
    change lpTestPairing V p φ
        (domainLpRestrict V (lpZeroExtension U p (sobolevDerivative u α))) =
      (-1 : 𝕜) ^ α.val.card * lpTestPairing V p
        (testPartialWord V (α.val.sort (· ≤ ·)) φ)
        (domainLpRestrict V (lpZeroExtension U p (sobolevUnderlying u)))
    rw [lpTestPairing_zeroExtension_restrict, lpTestPairing_zeroExtension_restrict,
      hleft, hright]
    have he := (mem_sobolevSubmodule_iff U k p u.val).mp u.property α ψ
    simpa only [lpTestPairing_eq_integral, sobolevDerivative, sobolevUnderlying] using he
  refine ⟨⟨F, hF⟩, fun _ => rfl, ?_⟩
  rw [sobolev_norm V k p, sobolev_norm U k p]
  apply Finset.sum_le_sum
  intro α _
  change ‖domainLpRestrict V (lpZeroExtension U p (sobolevDerivative u α))‖ ≤ _
  exact (P102.U4.domainLpRestrict_norm_le V _).trans_eq (lpZeroExtension_norm U p _)


/-- The flat density result in the ordinary Sobolev closure model. This
also works in dimension one: the underlying translation and mollification
lemma has no lower bound on the tangential dimension. -/
theorem mem_sobolevZero_halfSpace_of_zeroExtension {m : ℕ}
    {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (u : HalfSobolev m 𝕜 p) (hu : FlatZeroTraceExpected.HasFlatZeroExtension u) :
    u ∈ sobolevZeroSubmodule 𝕜 (halfSpace m) 1 p := by
  obtain ⟨w, hw⟩ := hu
  have hback : sobolevRestrict (halfSpace m) w = u := by
    apply sobolevUnderlying_injective (halfSpace m) 1 p
    change domainLpRestrict (halfSpace m) (sobolevUnderlying w) = _
    rw [hw]
    exact domainLpRestrict_zeroExtension (halfSpace m) (sobolevUnderlying u)
  have hwneg : ∀ᵐ x ∂volume, x (Fin.last m) < 0 → sobolevUnderlying w x = 0 := by
    have h := flatZeroExtension_ae (sobolevUnderlying u)
    change (FlatZeroTraceExpected.flatZeroExtension (sobolevUnderlying u) : Space (m + 1) → 𝕜) =ᵐ[volume] _ at h
    rw [← hw] at h
    filter_upwards [h] with x hx hxneg
    rw [hx]
    apply indicator_of_notMem
    change ¬0 < x (Fin.last m)
    exact not_lt.mpr hxneg.le
  change u ∈ closure (smoothSobolevSubmodule 𝕜 (halfSpace m) 1 p :
    Set (HalfSobolev m 𝕜 p))
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨φ, v, hv, herror⟩ := halfSpace_approximation_of_wholeSpace hp w hwneg hε
  refine ⟨sobolevRestrict (halfSpace m) v, ?_, ?_⟩
  · change ∃ φ, testToDomainLp (halfSpace m) p φ = _
    refine ⟨φ, ?_⟩
    apply Lp.ext
    have hv0 := hv (zeroSobolevIndex (m + 1) 1)
    simp only [zeroSobolevIndex, multiPartial, Multiset.sort_zero, partialWord] at hv0
    have hv0' : (sobolevUnderlying v : Space (m + 1) → 𝕜) =ᵐ[volume] φ := hv0
    filter_upwards [testToDomainLp_ae (halfSpace m) p φ,
      P102.U4.domainLpRestrict_ae (halfSpace m) (sobolevUnderlying v),
      ae_restrict_of_ae hv0'] with x hx hy hz
    exact hx.trans (hz.symm.trans hy.symm)
  · rw [← hback, dist_eq_norm']
    have heq := (sobolevRestrictCLM (𝕜 := 𝕜) (m := 1) (p := p) (halfSpace m)).map_sub v w
    change ‖(sobolevRestrictCLM (halfSpace m)) v - (sobolevRestrictCLM (halfSpace m)) w‖ < ε
    rw [← heq]
    exact (sobolevRestrict_norm_le (halfSpace m) (v - w)).trans_lt herror

theorem flatZeroExtension_iff_mem_sobolevZero {m : ℕ}
    {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (u : HalfSobolev m 𝕜 p) :
    FlatZeroTraceExpected.HasFlatZeroExtension u ↔
      u ∈ sobolevZeroSubmodule 𝕜 (halfSpace m) 1 p := by
  constructor
  · exact mem_sobolevZero_halfSpace_of_zeroExtension hp u
  · intro hu
    exact ⟨sobolevZeroExtensionLI (halfSpace m) 1 p ⟨u, hu⟩, rfl⟩

lemma boundaryLp_zero_at {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space 1)}
    {p : ℝ≥0∞} (hcount : boundaryMeasure Ω =
      Measure.count.restrict (frontier (Ω : Set (Space 1))))
    {g : BoundaryLp 𝕜 Ω p} (hg : g = 0) {x : Space 1}
    (hx : x ∈ frontier (Ω : Set (Space 1))) : g x = 0 := by
  have h := (Lp.coeFn_zero 𝕜 p (boundaryMeasure Ω))
  have hc := h.filter_mono (ae_mono hcount.symm.le)
  have ha := Measure.ae_count_iff.mp ((ae_restrict_iff' measurableSet_frontier).mp hc)
  rw [hg]
  exact ha x hx

lemma endpoint_trace_eq_zero_iff {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space 1)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (T : Sobolev 𝕜 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p)
    (hcount : boundaryMeasure Ω = Measure.count.restrict (frontier (Ω : Set (Space 1))))
    {n : ℕ} {a b : Fin n → ℝ}
    (hfront : frontier (Ω : Set (Space 1)) = ⋃ i, {linePoint (a i), linePoint (b i)})
    (hval : ∀ (u : Sobolev 𝕜 Ω 1 p) (f : ℝ → 𝕜),
      IsEndpointRepresentative a b u f → ∀ i,
        T u (linePoint (a i)) = f (a i) ∧ T u (linePoint (b i)) = f (b i))
    (u : Sobolev 𝕜 Ω 1 p) (f : ℝ → 𝕜) (hf : IsEndpointRepresentative a b u f) :
    T u = 0 ↔ ∀ i, f (a i) = 0 ∧ f (b i) = 0 := by
  constructor
  · intro hu i
    have ha : linePoint (a i) ∈ frontier (Ω : Set (Space 1)) := by
      rw [hfront]
      exact mem_iUnion.mpr ⟨i, by simp⟩
    have hb : linePoint (b i) ∈ frontier (Ω : Set (Space 1)) := by
      rw [hfront]
      exact mem_iUnion.mpr ⟨i, by simp⟩
    exact ⟨(hval u f hf i).1.symm.trans (boundaryLp_zero_at hcount hu ha),
      (hval u f hf i).2.symm.trans (boundaryLp_zero_at hcount hu hb)⟩
  · intro hz
    apply Lp.ext
    apply Filter.EventuallyEq.trans _ (Lp.coeFn_zero 𝕜 p (boundaryMeasure Ω)).symm
    filter_upwards [ae_restrict_mem measurableSet_frontier] with x hx
    rw [hfront] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rcases hi with rfl | hi
    · exact (hval u f hf i).1.trans (hz i).1
    · have he : x = linePoint (b i) := by simpa using hi
      rw [he]
      exact (hval u f hf i).2.trans (hz i).2
lemma interval_endpoint_not_other {n : ℕ} {a b : Fin n → ℝ}
    (hab : ∀ i, a i < b i) (hinj : Function.Injective (Sum.elim a b))
    (hdis : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    {i j : Fin n} (hij : i ≠ j) :
    a i ∉ Icc (a j) (b j) ∧ b i ∉ Icc (a j) (b j) := by
  have haa : a i ≠ a j := fun h => hij (Sum.inl.inj (hinj h))
  have habj : a i ≠ b j := fun h => Sum.inl_ne_inr (hinj (show Sum.elim a b (Sum.inl i) = Sum.elim a b (Sum.inr j) from h))
  have hba : b i ≠ a j := fun h => Sum.inr_ne_inl (hinj (show Sum.elim a b (Sum.inr i) = Sum.elim a b (Sum.inl j) from h))
  have hbb : b i ≠ b j := fun h => hij (Sum.inr.inj (hinj h))
  have hd := Ioo_disjoint_Ioo.mp (hdis hij)
  constructor
  · rintro ⟨hja, hjb⟩
    have hja' : a j < a i := lt_of_le_of_ne hja haa.symm
    have hjb' : a i < b j := lt_of_le_of_ne hjb habj
    rw [max_eq_left hja'.le] at hd
    exact (lt_min (hab i) hjb').not_ge hd
  · rintro ⟨hja, hjb⟩
    have hja' : a j < b i := lt_of_le_of_ne hja hba.symm
    have hjb' : b i < b j := lt_of_le_of_ne hjb hbb
    rw [min_eq_left hjb'.le] at hd
    exact (max_lt (hab i) hja').not_ge hd

lemma exists_endpoint_exterior_intervals {n : ℕ} {a b : Fin n → ℝ}
    (hab : ∀ i, a i < b i) (hinj : Function.Injective (Sum.elim a b))
    (hdis : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (i : Fin n) : ∃ δ > 0,
      (∀ t ∈ Ioo (a i - δ) (a i), t ∉ ⋃ j, Ioo (a j) (b j)) ∧
      (∀ t ∈ Ioo (b i) (b i + δ), t ∉ ⋃ j, Ioo (a j) (b j)) := by
  classical
  let S : Set ℝ := ⋃ j : {j : Fin n // j ≠ i}, Icc (a j) (b j)
  have hclosed : IsClosed S := isClosed_iUnion_of_finite fun _ => isClosed_Icc
  have hai : a i ∈ Sᶜ := by
    simp only [S, mem_compl_iff, mem_iUnion, not_exists]
    intro j
    exact (interval_endpoint_not_other hab hinj hdis j.property.symm).1
  have hbi : b i ∈ Sᶜ := by
    simp only [S, mem_compl_iff, mem_iUnion, not_exists]
    intro j
    exact (interval_endpoint_not_other hab hinj hdis j.property.symm).2
  obtain ⟨δa, hδa, hsa⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hai)
  obtain ⟨δb, hδb, hsb⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hbi)
  refine ⟨min δa δb, lt_min hδa hδb, ?_, ?_⟩
  · intro t ht hmem
    obtain ⟨j, hj⟩ := mem_iUnion.mp hmem
    by_cases hji : j = i
    · subst j; exact (not_lt_of_ge ht.2.le) hj.1
    · have htball : t ∈ Metric.ball (a i) δa := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [min_le_left δa δb, ht.1, ht.2]
      exact hsa htball (mem_iUnion.mpr ⟨⟨j, hji⟩, ⟨hj.1.le, hj.2.le⟩⟩)
  · intro t ht hmem
    obtain ⟨j, hj⟩ := mem_iUnion.mp hmem
    by_cases hji : j = i
    · subst j; exact (not_lt_of_ge ht.1.le) hj.2
    · have htball : t ∈ Metric.ball (b i) δb := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [min_le_right δa δb, ht.1, ht.2]
      exact hsb htball (mem_iUnion.mpr ⟨⟨j, hji⟩, ⟨hj.1.le, hj.2.le⟩⟩)
lemma linePoint_injective : Function.Injective linePoint := by
  intro s t h
  exact congrArg (fun z : Space 1 => z.ofLp 0) h

lemma linePoint_preimage_intervals {n : ℕ} {a b : Fin n → ℝ}
    {Ω : Opens (Space 1)}
    (hΩ : (Ω : Set (Space 1)) = ⋃ i, linePoint '' Ioo (a i) (b i)) :
    linePoint ⁻¹' (Ω : Set (Space 1)) = ⋃ i, Ioo (a i) (b i) := by
  rw [hΩ, preimage_iUnion]
  simp only [linePoint_injective.preimage_image]

lemma acl_line_one_eq (t : ℝ) : ACL.line (0 : Fin 1) 0 t = linePoint t := by
  apply WithLp.ofLp_injective 2
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  rfl

lemma ae_linePoint {P : Space 1 → Prop} (hP : ∀ᵐ x ∂volume, P x) :
    ∀ᵐ t ∂volume, P (linePoint t) := by
  have h := ACL.ae_on_fibers (Ω := (⊤ : Opens (Space 1))) (0 : Fin 1)
    (by simpa only [Opens.coe_top, Measure.restrict_univ] using hP)
  letI : IsEmpty {j : Fin 1 // j ≠ (0 : Fin 1)} :=
    ⟨fun j => j.property (Subsingleton.elim _ _)⟩
  simpa only [Measure.volume_pi_eq_dirac (0 : ACL.Transverse (0 : Fin 1)),
    ae_dirac_eq, Filter.eventually_pure, ACL.fiber, Opens.coe_top,
    preimage_univ, Measure.restrict_univ, acl_line_one_eq] using h

lemma zeroExtension_exists_continuous_line_representative {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space 1)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 Ω 1 p) (hu : HasZeroExtension u) :
    ∃ g : ℝ → 𝕜, Continuous g ∧
      (∀ᵐ t ∂volume, g t =
        (Ω : Set (Space 1)).indicator (sobolevUnderlying u) (linePoint t)) := by
  obtain ⟨w, hw⟩ := hu
  obtain ⟨k, hwk, hk, _⟩ :=
    (acl_dimensionOne 𝕜 (⊤ : Opens (Space 1))
      (sobolevUnderlying w) (firstWeakDerivative w 0)
      (domainLp_locallyIntegrable ⊤ p _) (domainLp_locallyIntegrable ⊤ p _)).mp
        (sobolev_derivative_distribution ⊤ 1 p w (firstSobolevIndex 0))
  have hwk' : (sobolevUnderlying w : Space 1 → 𝕜) =ᵐ[volume] k := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using hwk
  have hke : k =ᵐ[volume] (Ω : Set (Space 1)).indicator (sobolevUnderlying u) := by
    rw [hw] at hwk'
    exact hwk'.symm.trans (lpZeroExtension_ae Ω p _)
  refine ⟨fun t => k (linePoint t), ?_, ae_linePoint hke⟩
  apply continuousOn_univ.mp
  apply ExpandedFA.Sobolev.Lines.LocallyAbsolutelyContinuousOn.continuousOn _ isOpen_univ
  simpa only [ACL.fiber, Opens.coe_top, preimage_univ, acl_line_one_eq] using hk
lemma zeroExtension_implies_zero_endpoint_values {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space 1)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {n : ℕ} {a b : Fin n → ℝ}
    (hab : ∀ i, a i < b i) (hinj : Function.Injective (Sum.elim a b))
    (hdis : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (hΩ : (Ω : Set (Space 1)) = ⋃ i, linePoint '' Ioo (a i) (b i))
    (u : Sobolev 𝕜 Ω 1 p) (f : ℝ → 𝕜) (hf : IsEndpointRepresentative a b u f)
    (hu : HasZeroExtension u) : ∀ i, f (a i) = 0 ∧ f (b i) = 0 := by
  obtain ⟨g, hg, hge⟩ := zeroExtension_exists_continuous_line_representative u hu
  have hpre := linePoint_preimage_intervals hΩ
  have hgf : g =ᵐ[volume.restrict (linePoint ⁻¹' (Ω : Set (Space 1)))] f := by
    filter_upwards [ae_restrict_of_ae hge, hf.1,
      ae_restrict_mem (Ω.isOpen.preimage (by
        change Continuous (fun t : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => t))
        fun_prop)).measurableSet] with t ht hft htΩ
    exact (ht.trans (indicator_of_mem (show linePoint t ∈ (Ω : Set (Space 1)) from htΩ) _)).trans hft
  intro i
  obtain ⟨δ, hδ, hexl, hexr⟩ := exists_endpoint_exterior_intervals hab hinj hdis i
  have hgl : g =ᵐ[volume.restrict (Ioo (a i - δ) (a i))] 0 := by
    filter_upwards [ae_restrict_of_ae hge, ae_restrict_mem measurableSet_Ioo] with t ht hti
    rw [ht]
    apply indicator_of_notMem
    change t ∉ linePoint ⁻¹' (Ω : Set (Space 1))
    rw [hpre]
    exact hexl t hti
  have hgr : g =ᵐ[volume.restrict (Ioo (b i) (b i + δ))] 0 := by
    filter_upwards [ae_restrict_of_ae hge, ae_restrict_mem measurableSet_Ioo] with t ht hti
    rw [ht]
    apply indicator_of_notMem
    change t ∉ linePoint ⁻¹' (Ω : Set (Space 1))
    rw [hpre]
    exact hexr t hti
  have hga : g (a i) = 0 := by
    have he := (Measure.eqOn_open_of_ae_eq hgl isOpen_Ioo hg.continuousOn
      continuous_const.continuousOn).closure hg continuous_const
    apply he
    rw [closure_Ioo (by linarith : a i - δ ≠ a i)]
    exact ⟨by linarith, le_rfl⟩
  have hgb : g (b i) = 0 := by
    have he := (Measure.eqOn_open_of_ae_eq hgr isOpen_Ioo hg.continuousOn
      continuous_const.continuousOn).closure hg continuous_const
    apply he
    rw [closure_Ioo (by linarith : b i ≠ b i + δ)]
    exact ⟨le_rfl, by linarith⟩
  have hfi : ContinuousOn f (Icc (a i) (b i)) := by
    simpa only [uIcc_of_le (hab i).le] using (hf.2.1 i).continuousOn
  have hgi : g =ᵐ[volume.restrict (Ioo (a i) (b i))] f := by
    apply ae_restrict_of_ae_restrict_of_subset _ hgf
    rw [hpre]
    exact subset_iUnion (fun j => Ioo (a j) (b j)) i
  have he := (Measure.eqOn_open_of_ae_eq hgi isOpen_Ioo hg.continuousOn
    (hfi.mono Ioo_subset_Icc_self)).of_subset_closure hg.continuousOn hfi
      Ioo_subset_Icc_self (by rw [closure_Ioo (hab i).ne])
  exact ⟨(he ⟨le_rfl, (hab i).le⟩).symm.trans hga,
    (he ⟨(hab i).le, le_rfl⟩).symm.trans hgb⟩

/-- In physical dimension one, actual whole-space zero extendibility
forces zero trace. The proof uses whole-space ACL continuity through each
endpoint and the genuine exterior gaps between the finitely many components. -/
theorem zeroExtension_implies_trace_zero_oneDimension_conditional
    (_hCutoff : Expected.CutoffCompatibility)
    (hEndpoint : Expected.EndpointIdentification)
    (_hTrace : Expected.TraceExists)
    (_hUnique : Expected.TraceUniqueness) :
    ∀ (e : Ambient 0 ≃ₗᵢ[ℝ] Space 1) (Ω : Opens (Space 1)),
      IsLipschitzOpen (geometricOpen e Ω : Set (Ambient 0)) →
      ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ →
      ∀ T : Sobolev 𝕜 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p, IsTrace T →
      ∀ u : Sobolev 𝕜 Ω 1 p, HasZeroExtension u → T u = 0 := by
  intro e Ω hΩ 𝕜 _ p _ hp T hT u hu
  obtain ⟨hcount, n, a, b, hab, hinj, hdis, hopen, hfront, _, hrep, hval⟩ :=
    hEndpoint e Ω hΩ 𝕜 p hp T hT
  obtain ⟨f, hf⟩ := hrep u
  apply (endpoint_trace_eq_zero_iff T hcount hfront hval u f hf).mpr
  exact zeroExtension_implies_zero_endpoint_values hab hinj hdis hopen u f hf hu

def physicalChartOpen (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m))) : Opens (Space (m + 1)) :=
  Ω ⊓ ⟨e '' chartImage C.frame C.graphFunction C.center C.radius C.height,
    e.toHomeomorph.isOpenMap _ (chartImage_open C.frame C.graph_lipschitz)⟩

def flatChartOpen (q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (c : Space m) (r a : ℝ) : Opens (Space (m + 1)) :=
  ⟨q '' upperCylinder c r a, q.toHomeomorph.isOpenMap _
    ((isOpen_ball.preimage (horizontal_lipschitz m).continuous).inter
      (isOpen_Ioo.preimage (vertical_lipschitz m).continuous))⟩

def physicalChartMap (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m))) :
    BiLipschitzChart (physicalChartOpen e Ω C)
      (flatChartOpen q C.center C.radius C.height)
      (shearConstant C.constant) (shearConstant C.constant) where
  toFun x := e (C.frame (shear C.graphFunction (q.symm x)))
  invFun y := q (unshear C.graphFunction (C.frame.symm (e.symm y)))
  mapsTo := by
    intro x hx
    have hflat : q.symm x ∈ upperCylinder C.center C.radius C.height := by
      obtain ⟨z,hz,hzx⟩ := hx
      simpa only [← hzx, LinearIsometryEquiv.symm_apply_apply] using hz
    have hs : C.frame (shear C.graphFunction (q.symm x)) ∈
        (geometricOpen e Ω : Set (Ambient m)) ∩
          chartImage C.frame C.graphFunction C.center C.radius C.height := by
      rw [C.side]
      exact ⟨shear C.graphFunction (q.symm x), ⟨q.symm x,hflat,rfl⟩,rfl⟩
    exact ⟨hs.1, ⟨C.frame (shear C.graphFunction (q.symm x)),hs.2,rfl⟩⟩
  inv_mapsTo := by
    intro y hy
    have hs : e.symm y ∈ (geometricOpen e Ω : Set (Ambient m)) ∩
        chartImage C.frame C.graphFunction C.center C.radius C.height := by
      refine ⟨?_, ?_⟩
      · change e (e.symm y) ∈ Ω
        simpa using hy.1
      · obtain ⟨z,hz,hzy⟩ := hy.2
        simpa only [← hzy, LinearIsometryEquiv.symm_apply_apply] using hz
    rw [C.side] at hs
    obtain ⟨z,⟨w,hw,rfl⟩,hz⟩ := hs
    refine ⟨w,hw,?_⟩
    simp only [← hz, AffineIsometryEquiv.symm_apply_apply, unshear_shear]
  left_inv := by
    intro x hx
    simp only [LinearIsometryEquiv.symm_apply_apply, AffineIsometryEquiv.symm_apply_apply,
      unshear_shear, LinearIsometryEquiv.apply_symm_apply]
  right_inv := by
    intro y hy
    simp only [LinearIsometryEquiv.symm_apply_apply, shear_unshear,
      AffineIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  lipschitz := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hx' : q.symm x ∈ strip (ball C.center C.radius) := by
      obtain ⟨z,hz,rfl⟩ := hx
      simpa only [LinearIsometryEquiv.symm_apply_apply, strip, mem_ofPred_eq] using hz.1
    have hy' : q.symm y ∈ strip (ball C.center C.radius) := by
      obtain ⟨z,hz,rfl⟩ := hy
      simpa only [LinearIsometryEquiv.symm_apply_apply, strip, mem_ofPred_eq] using hz.1
    simpa only [e.isometry.dist_eq, C.frame.isometry.dist_eq, q.symm.isometry.dist_eq] using
      (shear_lipschitzOn C.graph_lipschitz).dist_le_mul (q.symm x) hx' (q.symm y) hy'
  inv_lipschitz := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hstrip : ∀ z ∈ physicalChartOpen e Ω C,
        C.frame.symm (e.symm z) ∈ strip (ball C.center C.radius) := by
      intro z hz
      obtain ⟨u,⟨v,⟨w,hw,rfl⟩,rfl⟩,rfl⟩ := hz.2
      simpa only [LinearIsometryEquiv.symm_apply_apply, AffineIsometryEquiv.symm_apply_apply, strip, mem_ofPred_eq, shear, WithLp.ofLp_toLp]
        using hw.1
    simpa only [q.isometry.dist_eq, C.frame.symm.isometry.dist_eq, e.symm.isometry.dist_eq] using
      (unshear_lipschitzOn C.graph_lipschitz).dist_le_mul
        (C.frame.symm (e.symm x)) (hstrip x hx) (C.frame.symm (e.symm y)) (hstrip y hy)


theorem physical_boundary_in_chart
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m))) :
    frontier (Ω : Set (Space (m + 1))) ∩
      e '' chartImage C.frame C.graphFunction C.center C.radius C.height =
      (fun x => e (C.frame (graph C.graphFunction x))) '' ball C.center C.radius := by
  have hgeo : e '' (geometricOpen e Ω : Set (Ambient m)) = (Ω : Set (Space (m + 1))) :=
    e.surjective.image_preimage _
  have hfront : frontier (Ω : Set (Space (m + 1))) =
      e '' frontier (geometricOpen e Ω : Set (Ambient m)) := by
    have hm := (e.toHomeomorph.image_frontier (geometricOpen e Ω : Set (Ambient m))).symm
    change frontier (e '' (geometricOpen e Ω : Set (Ambient m))) =
      e '' frontier (geometricOpen e Ω : Set (Ambient m)) at hm
    rwa [hgeo] at hm
  rw [hfront, ← Set.image_inter e.injective, C.boundary]
  simp only [← Set.image_comp, Function.comp_def]

@[simp] theorem physicalChartMap_boundary
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m))) (x : Space m) :
    (physicalChartMap e q Ω C).toFun (q (WithLp.toLp 2 (x, (0 : ℝ)))) =
      e (C.frame (graph C.graphFunction x)) := by
  simp only [physicalChartMap, LinearIsometryEquiv.symm_apply_apply, shear,
    WithLp.ofLp_toLp, add_zero, graph]

@[simp] theorem physicalChartMap_inverse_boundary
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m))) (x : Space m) :
    (physicalChartMap e q Ω C).invFun (e (C.frame (graph C.graphFunction x))) =
      q (WithLp.toLp 2 (x, (0 : ℝ))) := by
  simp only [physicalChartMap, LinearIsometryEquiv.symm_apply_apply,
    AffineIsometryEquiv.symm_apply_apply, unshear, graph, WithLp.ofLp_toLp, sub_self]


/-- The full physical chart, before intersection with the domain. -/
def fullPhysicalChartOpen (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    {G : Set (Ambient m)} (C : BoundaryChart G) : Opens (Space (m + 1)) :=
  ⟨e '' chartImage C.frame C.graphFunction C.center C.radius C.height,
    e.toHomeomorph.isOpenMap _ (chartImage_open C.frame C.graph_lipschitz)⟩

/-- The full symmetric flat cylinder. -/
def fullFlatChartOpen (q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (c : Space m) (r a : ℝ) : Opens (Space (m + 1)) :=
  ⟨q '' cylinder c r a, q.toHomeomorph.isOpenMap _ (cylinder_open c r a)⟩

def fullChartMap (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    {G : Set (Ambient m)} (C : BoundaryChart G) :
    BiLipschitzChart (fullPhysicalChartOpen e C)
      (fullFlatChartOpen q C.center C.radius C.height)
      (shearConstant C.constant) (shearConstant C.constant) where
  toFun x := e (C.frame (shear C.graphFunction (q.symm x)))
  invFun y := q (unshear C.graphFunction (C.frame.symm (e.symm y)))
  mapsTo := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := hx
    exact ⟨C.frame (shear C.graphFunction z),
      ⟨shear C.graphFunction z, ⟨z,hz,rfl⟩,rfl⟩, by simp⟩
  inv_mapsTo := by
    intro y hy
    obtain ⟨u,⟨v,⟨w,hw,rfl⟩,rfl⟩,rfl⟩ := hy
    exact ⟨w,hw,by simp⟩
  left_inv := by
    intro x hx
    simp only [LinearIsometryEquiv.symm_apply_apply, AffineIsometryEquiv.symm_apply_apply,
      unshear_shear, LinearIsometryEquiv.apply_symm_apply]
  right_inv := by
    intro y hy
    simp only [LinearIsometryEquiv.symm_apply_apply, shear_unshear,
      AffineIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  lipschitz := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hx' : q.symm x ∈ strip (ball C.center C.radius) := by
      obtain ⟨z,hz,rfl⟩ := hx
      simpa only [LinearIsometryEquiv.symm_apply_apply, strip, mem_ofPred_eq] using hz.1
    have hy' : q.symm y ∈ strip (ball C.center C.radius) := by
      obtain ⟨z,hz,rfl⟩ := hy
      simpa only [LinearIsometryEquiv.symm_apply_apply, strip, mem_ofPred_eq] using hz.1
    simpa only [e.isometry.dist_eq, C.frame.isometry.dist_eq, q.symm.isometry.dist_eq] using
      (shear_lipschitzOn C.graph_lipschitz).dist_le_mul (q.symm x) hx' (q.symm y) hy'
  inv_lipschitz := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hstrip : ∀ z ∈ fullPhysicalChartOpen e C,
        C.frame.symm (e.symm z) ∈ strip (ball C.center C.radius) := by
      intro z hz
      obtain ⟨u,⟨v,⟨w,hw,rfl⟩,rfl⟩,rfl⟩ := hz
      simpa only [LinearIsometryEquiv.symm_apply_apply, AffineIsometryEquiv.symm_apply_apply,
        strip, mem_ofPred_eq, shear, WithLp.ofLp_toLp] using hw.1
    simpa only [q.isometry.dist_eq, C.frame.symm.isometry.dist_eq, e.symm.isometry.dist_eq] using
      (unshear_lipschitzOn C.graph_lipschitz).dist_le_mul
        (C.frame.symm (e.symm x)) (hstrip x hx) (C.frame.symm (e.symm y)) (hstrip y hy)

/-- Pull the ambient compact support through the full chart, including
height zero. This compact set stays strictly inside the full flat cylinder. -/
def fullChartPullbackCompact
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    {G : Set (Ambient m)} (C : BoundaryChart G)
    (K : Compacts (Space (m + 1))) (hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C) :
    Compacts (Space (m + 1)) :=
  ⟨(fullChartMap e q C).invFun '' (K : Set (Space (m + 1))),
    K.isCompact.image_of_continuousOn ((fullChartMap e q C).inv_lipschitz.continuousOn.mono hK)⟩

theorem fullChartPullbackCompact_subset
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    {G : Set (Ambient m)} (C : BoundaryChart G)
    (K : Compacts (Space (m + 1))) (hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C) :
    (fullChartPullbackCompact e q C K hK : Set (Space (m + 1))) ⊆
      fullFlatChartOpen q C.center C.radius C.height := by
  rintro x ⟨y,hy,rfl⟩
  exact (fullChartMap e q C).inv_mapsTo (hK hy)



theorem physicalChart_pullback_zero_off_compact
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 (physicalChartOpen e Ω C) p)
    (K : Compacts (Space (m + 1))) (hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C)
    (hu : ∀ᵐ x ∂volume.restrict (physicalChartOpen e Ω C : Set (Space (m + 1))),
      x ∉ K → u x = 0) :
    ∀ᵐ x ∂volume.restrict (flatChartOpen q C.center C.radius C.height : Set (Space (m + 1))),
      x ∉ fullChartPullbackCompact e q C K hK →
        (physicalChartMap e q Ω C).lpPullback 𝕜 p u x = 0 := by
  let g := physicalChartMap e q Ω C
  filter_upwards [g.lpPullback_ae 𝕜 p u, g.ae_comp hu,
      ae_restrict_mem (flatChartOpen q C.center C.radius C.height).isOpen.measurableSet]
      with x hx hv hxV hnot
  rw [hx]
  apply hv
  intro hxK
  exact hnot ⟨g.toFun x, hxK, g.left_inv x hxV⟩

/-- The upper side of the flat chart in the same arbitrary isometric
coordinates. For canonical q this is the standard half-space. -/
def flatPositiveOpen (q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) : Opens (Space (m + 1)) :=
  ⟨q '' {z : Ambient m | 0 < z.ofLp.2}, q.toHomeomorph.isOpenMap _
    (isOpen_lt continuous_const (vertical_lipschitz m).continuous)⟩

theorem flatPositive_inter_full_subset_flat
    (q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (c : Space m) (r a : ℝ) :
    (flatPositiveOpen q : Set (Space (m + 1))) ∩ fullFlatChartOpen q c r a ⊆
      flatChartOpen q c r a := by
  rintro x ⟨⟨y,hy,rfl⟩,⟨z,hz,hzq⟩⟩
  have hzy : z = y := q.injective hzq
  subst z
  exact ⟨y,⟨hz.1,hy,hz.2.2⟩,rfl⟩

theorem flatChartOpen_le_flatPositive
    (q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (c : Space m) (r a : ℝ) :
    flatChartOpen q c r a ≤ flatPositiveOpen q := by
  rintro x ⟨z,hz,rfl⟩
  exact ⟨z,hz.2.1,rfl⟩

def sobolevSupportedSubmodule {d k : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (U : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (K : Set (Space d)) : Submodule 𝕜 (Sobolev 𝕜 U k p) where
  carrier := {u | ∀ᵐ x ∂volume.restrict (U : Set (Space d)),
    x ∉ K → sobolevUnderlying u x = 0}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero 𝕜 p (volume.restrict (U : Set (Space d)))] with x hx _
    exact hx
  add_mem' := by
    intro u v hu hv
    filter_upwards [hu, hv, Lp.coeFn_add (sobolevUnderlying u) (sobolevUnderlying v)]
      with x hux hvx hsum hxK
    change (sobolevUnderlying u + sobolevUnderlying v) x = 0
    rw [hsum, Pi.add_apply, hux hxK, hvx hxK, add_zero]
  smul_mem' := by
    intro c u hu
    filter_upwards [hu, Lp.coeFn_smul c (sobolevUnderlying u)] with x hux hsmul hxK
    change (c • sobolevUnderlying u) x = 0
    rw [hsmul, Pi.smul_apply, hux hxK, smul_zero]

def transferSupportedCLM {d k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U V : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (K : Set (Space d))
    (hTransfer : ∀ u : Sobolev 𝕜 U k p,
      (∀ᵐ x ∂volume.restrict (U : Set (Space d)), x ∉ K → sobolevUnderlying u x = 0) →
      ∃ v : Sobolev 𝕜 V k p,
        (∀ α, sobolevDerivative v α =
          domainLpRestrict V (lpZeroExtension U p (sobolevDerivative u α))) ∧
        ‖v‖ ≤ ‖u‖) :
    sobolevSupportedSubmodule (k := k) 𝕜 U p K →L[𝕜] Sobolev 𝕜 V k p := by
  classical
  let f (u : sobolevSupportedSubmodule (k := k) 𝕜 U p K) :=
    (hTransfer u.val u.property).choose
  have hf (u : sobolevSupportedSubmodule (k := k) 𝕜 U p K) :
      (∀ α, sobolevDerivative (f u) α =
        domainLpRestrict V (lpZeroExtension U p (sobolevDerivative u.val α))) ∧
        ‖f u‖ ≤ ‖u.val‖ := (hTransfer u.val u.property).choose_spec
  let L : sobolevSupportedSubmodule (k := k) 𝕜 U p K →ₗ[𝕜] Sobolev 𝕜 V k p :=
    { toFun := f
      map_add' := by
        intro u v
        apply Subtype.ext
        apply PiLp.ext
        intro α
        change sobolevDerivative (f (u + v)) α =
          sobolevDerivative (f u) α + sobolevDerivative (f v) α
        rw [(hf (u + v)).1 α, (hf u).1 α, (hf v).1 α]
        change (domainLpRestrictCLM V) ((lpZeroExtensionLI U p)
          (sobolevDerivative u.val α + sobolevDerivative v.val α)) = _
        rw [map_add, map_add]
        rfl
      map_smul' := by
        intro c u
        apply Subtype.ext
        apply PiLp.ext
        intro α
        change sobolevDerivative (f (c • u)) α = c • sobolevDerivative (f u) α
        rw [(hf (c • u)).1 α, (hf u).1 α]
        change (domainLpRestrictCLM V) ((lpZeroExtensionLI U p)
          (c • sobolevDerivative u.val α)) = _
        rw [map_smul, map_smul]
        rfl }
  exact L.mkContinuous 1 (by
    intro u
    change ‖f u‖ ≤ 1 * ‖u.val‖
    simpa only [one_mul] using (hf u).2)


def flatCoordinates (m : ℕ) : Ambient m ≃ₗᵢ[ℝ] Space (m + 1) where
  toFun z := WithLp.toLp 2 (Fin.snoc z.ofLp.1 z.ofLp.2)
  invFun x := WithLp.toLp 2 (WithLp.toLp 2 (fun i => x i.castSucc), x (Fin.last m))
  left_inv := by
    intro z
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · apply PiLp.ext
      intro i
      simp
    · simp
  right_inv := by
    intro x
    apply PiLp.ext
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp
  map_add' := by
    intro x y
    apply PiLp.ext
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' := by
    intro c x
    apply PiLp.ext
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  norm_map' := by
    intro z
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq]
    rw [Fin.sum_univ_castSucc]
    rw [WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq]
    change (∑ i : Fin m, ‖Fin.snoc (α := fun _ => ℝ) z.ofLp.1.ofLp z.ofLp.2 i.castSucc‖ ^ 2) +
      ‖Fin.snoc (α := fun _ => ℝ) z.ofLp.1.ofLp z.ofLp.2 (Fin.last m)‖ ^ 2 = _
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rfl
@[simp] theorem flatCoordinates_last (m : ℕ) (z : Ambient m) :
    flatCoordinates m z (Fin.last m) = z.ofLp.2 := by
  simp [flatCoordinates]

@[simp] theorem flatCoordinates_symm_height (m : ℕ) (x : Space (m + 1)) :
    ((flatCoordinates m).symm x).ofLp.2 = x (Fin.last m) := rfl

theorem flatPositiveOpen_flatCoordinates (m : ℕ) :
    flatPositiveOpen (flatCoordinates m) = halfSpace m := by
  apply Opens.ext
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    change 0 < flatCoordinates m z (Fin.last m)
    rwa [flatCoordinates_last]
  · intro hx
    refine ⟨(flatCoordinates m).symm x, ?_, (flatCoordinates m).apply_symm_apply x⟩
    exact hx

@[simp] theorem fullChartMap_left_inv_global
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    {G : Set (Ambient m)} (C : BoundaryChart G) (x : Space (m + 1)) :
    (fullChartMap e q C).invFun ((fullChartMap e q C).toFun x) = x := by
  simp only [fullChartMap, LinearIsometryEquiv.symm_apply_apply,
    AffineIsometryEquiv.symm_apply_apply, unshear_shear, LinearIsometryEquiv.apply_symm_apply]

@[simp] theorem fullChartMap_right_inv_global
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    {G : Set (Ambient m)} (C : BoundaryChart G) (x : Space (m + 1)) :
    (fullChartMap e q C).toFun ((fullChartMap e q C).invFun x) = x := by
  simp only [fullChartMap, LinearIsometryEquiv.symm_apply_apply, shear_unshear,
    AffineIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]

theorem fullChartMap_tsupport_comp_subset
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    {G : Set (Ambient m)} (C : BoundaryChart G)
    {E : Type*} [Zero E] (φ : Space (m + 1) → E)
    (K : Compacts (Space (m + 1))) (hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C)
    (hφ : tsupport φ ⊆ (K : Set (Space (m + 1)))) :
    tsupport (φ ∘ (fullChartMap e q C).toFun) ⊆
      (fullChartPullbackCompact e q C K hK : Set (Space (m + 1))) := by
  apply closure_minimal _ (fullChartPullbackCompact e q C K hK).isCompact.isClosed
  intro x hx
  exact ⟨(fullChartMap e q C).toFun x, hφ (subset_tsupport φ hx),
    fullChartMap_left_inv_global e q C x⟩

theorem fullChartMap_continuous_comp
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    {G : Set (Ambient m)} (C : BoundaryChart G)
    {E : Type*} [Zero E] [TopologicalSpace E] (φ : Space (m + 1) → E)
    (hc : Continuous φ)
    (K : Compacts (Space (m + 1))) (hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C)
    (hφ : tsupport φ ⊆ (K : Set (Space (m + 1)))) :
    Continuous (φ ∘ (fullChartMap e q C).toFun) := by
  apply continuous_of_tsupport
  intro x hx
  have hxV := fullChartPullbackCompact_subset e q C K hK
    (fullChartMap_tsupport_comp_subset e q C φ K hK hφ hx)
  exact hc.continuousAt.comp
    ((fullChartMap e q C).lipschitz.continuousOn.continuousAt
      ((fullFlatChartOpen q C.center C.radius C.height).isOpen.mem_nhds hxV))

theorem fullChartMap_hasCompactSupport_comp
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    {G : Set (Ambient m)} (C : BoundaryChart G)
    {E : Type*} [Zero E] (φ : Space (m + 1) → E)
    (K : Compacts (Space (m + 1))) (hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C)
    (hφ : tsupport φ ⊆ (K : Set (Space (m + 1)))) :
    HasCompactSupport (φ ∘ (fullChartMap e q C).toFun) := by
  exact (fullChartPullbackCompact e q C K hK).isCompact.of_isClosed_subset
    (isClosed_tsupport _) (fullChartMap_tsupport_comp_subset e q C φ K hK hφ)

def chartBoundaryParam (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m))) : Space m → Space (m + 1) :=
  fun x => e (C.frame (graph C.graphFunction x))

theorem chartBoundaryParam_mem_frontier
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    {x : Space m} (hx : x ∈ ball C.center C.radius) :
    chartBoundaryParam e Ω C x ∈ frontier (Ω : Set (Space (m + 1))) := by
  have hp : chartBoundaryParam e Ω C x ∈
      (fun y => e (C.frame (graph C.graphFunction y))) '' ball C.center C.radius :=
    ⟨x,hx,rfl⟩
  rw [← physical_boundary_in_chart] at hp
  exact hp.1

theorem chartBoundaryParam_lipschitz
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m))) :
    LipschitzOnWith (graphConstant C.constant) (chartBoundaryParam e Ω C)
      (ball C.center C.radius) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  simpa only [chartBoundaryParam, e.isometry.dist_eq, C.frame.isometry.dist_eq] using
    (graph_geometry m (ball C.center C.radius) C.graphFunction C.constant C.graph_lipschitz).1.dist_le_mul x hx y hy

theorem chartBoundaryParam_preimage_volume_le
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (E : Set (Space (m + 1))) :
    volume (ball C.center C.radius ∩ (chartBoundaryParam e Ω C) ⁻¹' E) ≤
      boundaryMeasure Ω E := by
  let S := ball C.center C.radius ∩ (chartBoundaryParam e Ω C) ⁻¹' E
  have himg : chartBoundaryParam e Ω C '' S =
      e '' (C.frame '' (graph C.graphFunction '' S)) := by
    change (e ∘ C.frame ∘ graph C.graphFunction) '' S = _
    rw [Set.image_comp, Set.image_comp]
  calc
    volume S ≤ (μHE[m] : Measure (Ambient m)) (graph C.graphFunction '' S) :=
      ((graph_geometry m (ball C.center C.radius) C.graphFunction C.constant
        C.graph_lipschitz).2.2 S inter_subset_left).1
    _ = (μHE[m] : Measure (Space (m + 1))) (chartBoundaryParam e Ω C '' S) := by
      rw [himg, e.isometry.euclideanHausdorffMeasure_image,
        C.frame.isometry.euclideanHausdorffMeasure_image]
    _ ≤ boundaryMeasure Ω E := by
      rw [boundaryMeasure, Measure.restrict_apply' measurableSet_frontier]
      apply measure_mono
      rintro y ⟨x,⟨hx,hxE⟩,rfl⟩
      exact ⟨hxE,chartBoundaryParam_mem_frontier e Ω C hx⟩

theorem chartBoundaryParam_map_volume_le
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m))) :
    Measure.map (chartBoundaryParam e Ω C)
      (volume.restrict (ball C.center C.radius)) ≤ boundaryMeasure Ω := by
  apply Measure.le_iff.mpr
  intro E hE
  rw [Measure.map_apply_of_aemeasurable
    ((chartBoundaryParam_lipschitz e Ω C).continuousOn.aemeasurable measurableSet_ball) hE,
    Measure.restrict_apply' measurableSet_ball]
  · simpa only [inter_comm] using chartBoundaryParam_preimage_volume_le e Ω C E

open P102.Trace.CoordinateBridge
private def modelEvenReflection (m : ℕ) (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :=
  (ExpandedFA.Sobolev.HalfSpace.halfSpace_extension 𝕜 (m + 1) (Fin.last m) p).choose

def halfEvenReflection (m : ℕ) (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    HalfSobolev m 𝕜 p →L[𝕜] Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p :=
  ((sobolevEquiv (𝕜 := 𝕜) (⊤ : Opens (Space (m + 1))) p).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((modelEvenReflection m 𝕜 p).comp
      (halfEquiv (𝕜 := 𝕜) m p).toContinuousLinearEquiv.toContinuousLinearMap)

private theorem halfEvenReflection_coordinates (m : ℕ) (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : HalfSobolev m 𝕜 p) :
    sobolevEquiv (⊤ : Opens (Space (m + 1))) p (halfEvenReflection m 𝕜 p u) =
      modelEvenReflection m 𝕜 p (halfEquiv m p u) := by
  change sobolevEquiv (⊤ : Opens (Space (m + 1))) p
    ((sobolevEquiv (⊤ : Opens (Space (m + 1))) p).symm
      (modelEvenReflection m 𝕜 p (halfEquiv m p u))) = _
  exact (sobolevEquiv (⊤ : Opens (Space (m + 1))) p).apply_symm_apply _

theorem halfEvenReflection_norm (m : ℕ) (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : HalfSobolev m 𝕜 p) :
    ‖halfEvenReflection m 𝕜 p u‖ =
      ExpandedFA.Sobolev.HalfSpace.reflectionFactor p * ‖u‖ := by
  have h := (ExpandedFA.Sobolev.HalfSpace.halfSpace_extension
    𝕜 (m + 1) (Fin.last m) p).choose_spec.2.2.2.1 (halfEquiv m p u)
  change ‖modelEvenReflection m 𝕜 p (halfEquiv m p u)‖ = _ at h
  rw [← halfEvenReflection_coordinates m 𝕜 p u] at h
  have hn := (sobolevEquiv (𝕜 := 𝕜) (⊤ : Opens (Space (m + 1))) p).norm_map
    (halfEvenReflection m 𝕜 p u)
  have hu := (halfEquiv (𝕜 := 𝕜) m p).norm_map u
  exact hn.symm.trans (h.trans (congrArg
    (fun a : ℝ => ExpandedFA.Sobolev.HalfSpace.reflectionFactor p * a) hu))

/-- Even reflection written directly on the original Euclidean representative. -/
def euclideanEvenValue {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f : Space (m + 1) → 𝕜) (x : Space (m + 1)) : 𝕜 :=
  ExpandedFA.Sobolev.HalfSpace.reflection (Fin.last m) false
    (f ∘ (ACL.coordinates (m + 1)).symm) (ACL.coordinates (m + 1) x)

theorem halfEvenReflection_underlying (m : ℕ) (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : HalfSobolev m 𝕜 p) :
    sobolevUnderlying (halfEvenReflection m 𝕜 p u) =ᵐ[volume]
      euclideanEvenValue (sobolevUnderlying u) := by
  have hb := sobolevEquiv_underlying_reverse
    (⊤ : Opens (Space (m + 1))) p (halfEvenReflection m 𝕜 p u)
  simp only [Opens.coe_top, Measure.restrict_univ,
    halfEvenReflection_coordinates] at hb
  have hm := (ExpandedFA.Sobolev.HalfSpace.halfSpace_extension
    𝕜 (m + 1) (Fin.last m) p).choose_spec.1 (halfEquiv m p u)
  change (modelEvenReflection m 𝕜 p (halfEquiv m p u)).val
    (ExpandedFA.Sobolev.zeroIndex (m + 1) 1) =ᵐ[volume]
      ExpandedFA.Sobolev.HalfSpace.reflection (Fin.last m) false
        ((halfEquiv m p u).val (ExpandedFA.Sobolev.zeroIndex (m + 1) 1)) at hm
  have hu := lpCoordinates_coe (halfSpace m) p (sobolevUnderlying u)
  have hr := ExpandedFA.Sobolev.HalfSpace.reflection_congr (Fin.last m) false hu
  have hid : (halfEquiv m p u).val (ExpandedFA.Sobolev.zeroIndex (m + 1) 1) =
      lpCoordinates (halfSpace m) p (sobolevUnderlying u) :=
    sobolevEquiv_underlying (halfSpace m) p u
  rw [hid] at hm
  have hfull := hm.trans hr
  exact hb.symm.trans ((coordinates_measurePreserving (d := m + 1)).quasiMeasurePreserving.ae_eq_comp hfull)

theorem halfEvenReflection_restrict (m : ℕ) (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : HalfSobolev m 𝕜 p) :
    sobolevUnderlying (halfEvenReflection m 𝕜 p u) =ᵐ[
      volume.restrict (halfSpace m : Set (Space (m + 1)))] sobolevUnderlying u := by
  have h : sobolevUnderlying (halfEvenReflection m 𝕜 p u) =ᵐ[
      volume.restrict (halfSpace m : Set (Space (m + 1)))]
      euclideanEvenValue (sobolevUnderlying u) :=
    (halfEvenReflection_underlying m 𝕜 p u).filter_mono
      (ae_mono Measure.restrict_le_self)
  filter_upwards [h, ae_restrict_mem (halfSpace m).isOpen.measurableSet] with x hx hxH
  rw [hx]
  unfold euclideanEvenValue
  rw [ExpandedFA.Sobolev.HalfSpace.reflection_of_pos]
  · simp only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply]
  · exact hxH


/-- Physical reflection across the coordinate face. -/
def euclideanReflectionPoint {m : ℕ} (x : Space (m + 1)) : Space (m + 1) :=
  (ACL.coordinates (m + 1)).symm
    (ExpandedFA.Sobolev.HalfSpace.reflect (Fin.last m) (ACL.coordinates (m + 1) x))

theorem euclideanEvenValue_eq {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f : Space (m + 1) → 𝕜) (x : Space (m + 1)) :
    euclideanEvenValue f x =
      (halfSpace m : Set (Space (m + 1))).indicator f x +
      (halfSpace m : Set (Space (m + 1))).indicator f (euclideanReflectionPoint x) := by
  rfl

theorem euclideanReflectionPoint_involutive {m : ℕ} :
    Function.Involutive (@euclideanReflectionPoint m) := by
  intro x
  simp only [euclideanReflectionPoint, ContinuousLinearEquiv.apply_symm_apply,
    ExpandedFA.Sobolev.HalfSpace.reflect_reflect, ContinuousLinearEquiv.symm_apply_apply]

theorem euclideanReflectionPoint_continuous {m : ℕ} :
    Continuous (@euclideanReflectionPoint m) := by
  apply (ACL.coordinates (m + 1)).symm.continuous.comp
  change Continuous ((ExpandedFA.Sobolev.HalfSpace.reflect (Fin.last m)) ∘
    (ACL.coordinates (m + 1)))
  refine Continuous.comp ?_ (ACL.coordinates (m + 1)).continuous
  apply continuous_pi
  intro j
  dsimp [ExpandedFA.Sobolev.HalfSpace.reflect]
  split_ifs
  · exact (continuous_apply j).neg
  · exact continuous_apply j

theorem euclideanReflectionPoint_measurePreserving {m : ℕ} :
    MeasurePreserving (@euclideanReflectionPoint m) volume volume := by
  exact ((PiLp.volume_preserving_toLp (Fin (m + 1))).comp
    (ExpandedFA.Sobolev.HalfSpace.reflect_measurePreserving (Fin.last m))).comp
      (coordinates_measurePreserving (d := m + 1))

def euclideanReflectedCompact {m : ℕ} (K : Compacts (Space (m + 1))) :
    Compacts (Space (m + 1)) :=
  ⟨(K : Set (Space (m + 1))) ∪ euclideanReflectionPoint '' (K : Set (Space (m + 1))),
    K.isCompact.union (K.isCompact.image euclideanReflectionPoint_continuous)⟩

theorem halfEvenReflection_zero_off_compact {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : HalfSobolev m 𝕜 p)
    (K : Compacts (Space (m + 1)))
    (hu : ∀ᵐ x ∂volume.restrict (halfSpace m : Set (Space (m + 1))),
      x ∉ K → sobolevUnderlying u x = 0) :
    ∀ᵐ x ∂volume, x ∉ euclideanReflectedCompact K →
      sobolevUnderlying (halfEvenReflection m 𝕜 p u) x = 0 := by
  have hz : ∀ᵐ x ∂volume, x ∉ K →
      (halfSpace m : Set (Space (m + 1))).indicator (sobolevUnderlying u) x = 0 := by
    filter_upwards [(ae_restrict_iff' (halfSpace m).isOpen.measurableSet).mp hu]
      with x hx hxK
    by_cases hxH : x ∈ (halfSpace m : Set (Space (m + 1)))
    · rw [indicator_of_mem hxH]
      exact hx hxH hxK
    · exact indicator_of_notMem hxH _
  have hzR := euclideanReflectionPoint_measurePreserving.quasiMeasurePreserving.ae hz
  filter_upwards [halfEvenReflection_underlying m 𝕜 p u, hz, hzR]
    with x hx hxK hxR hxout
  have hxout' : x ∉ (K : Set (Space (m + 1))) ∪
      euclideanReflectionPoint '' (K : Set (Space (m + 1))) := hxout
  have hxnot : x ∉ (K : Set (Space (m + 1))) :=
    fun hxK => hxout' (Or.inl hxK)
  have hxRnot : euclideanReflectionPoint x ∉ (K : Set (Space (m + 1))) := by
    intro hmem
    apply hxout'
    exact Or.inr ⟨euclideanReflectionPoint x, hmem,
      euclideanReflectionPoint_involutive x⟩
  rw [hx, euclideanEvenValue_eq, hxK hxnot, hxR hxRnot, add_zero]

/-- The artificial-edge transfer is one bounded linear map on the actual
subspace of inputs with fixed essential support. -/
def artificialBoundaryTransferCLM {d k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U V W : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (K : Compacts (Space d)) (hKW : (K : Set (Space d)) ⊆ W)
    (hVU : (V : Set (Space d)) ∩ (W : Set (Space d)) ⊆ U) :
    sobolevSupportedSubmodule (k := k) 𝕜 U p K →L[𝕜] Sobolev 𝕜 V k p :=
  transferSupportedCLM U V p K
    (fun u hu => transfer_across_artificial_boundary K hKW hVU u hu)

theorem artificialBoundaryTransferCLM_derivative {d k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U V W : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (K : Compacts (Space d)) (hKW : (K : Set (Space d)) ⊆ W)
    (hVU : (V : Set (Space d)) ∩ (W : Set (Space d)) ⊆ U)
    (u : sobolevSupportedSubmodule (k := k) 𝕜 U p K) (α : SobolevIndex d k) :
    sobolevDerivative (artificialBoundaryTransferCLM U V W p K hKW hVU u) α =
      domainLpRestrict V (lpZeroExtension U p (sobolevDerivative u.val α)) :=
  (transfer_across_artificial_boundary K hKW hVU u.val u.property).choose_spec.1 α

/-- Essential support is retained when transferring across artificial edges. -/
theorem artificialBoundaryTransferCLM_zero_off_compact {d k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U V W : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (K : Compacts (Space d)) (hKW : (K : Set (Space d)) ⊆ W)
    (hVU : (V : Set (Space d)) ∩ (W : Set (Space d)) ⊆ U)
    (u : sobolevSupportedSubmodule (k := k) 𝕜 U p K) :
    ∀ᵐ x ∂volume.restrict (V : Set (Space d)), x ∉ K →
      sobolevUnderlying (artificialBoundaryTransferCLM U V W p K hKW hVU u) x = 0 := by
  have he := artificialBoundaryTransferCLM_derivative U V W p K hKW hVU u
    (zeroSobolevIndex d k)
  change sobolevUnderlying (artificialBoundaryTransferCLM U V W p K hKW hVU u) =
    domainLpRestrict V (lpZeroExtension U p (sobolevUnderlying u.val)) at he
  rw [he]
  filter_upwards [P102.U4.domainLpRestrict_ae V (lpZeroExtension U p (sobolevUnderlying u.val)),
    ae_restrict_of_ae (lpZeroExtension_zero_off_compact (sobolevUnderlying u.val) K u.property)]
    with x hx hz hxK
  exact hx.trans (hz hxK)


/-- Restriction of supported classes preserves their essential compact support. -/
def physicalSupportedRestrictionCLM
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (K : Compacts (Space (m + 1))) :
    sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K →L[𝕜]
      Sobolev 𝕜 (physicalChartOpen e Ω C) 1 p :=
  artificialBoundaryTransferCLM Ω (physicalChartOpen e Ω C) ⊤ p K
    (subset_univ _) (fun _ hx => hx.1.1)

/-- Flatten a physically supported class on the actual upper cylinder. -/
def flattenCylinderSupportedCLM
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (K : Compacts (Space (m + 1))) :
    sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K →L[𝕜]
      Sobolev 𝕜 (flatChartOpen q C.center C.radius C.height) 1 p :=
  ((physicalChartMap e q Ω C).sobolevPullback meyersSerrin_smoothDensity
    (Nat.succ_pos m) 𝕜 p).comp (physicalSupportedRestrictionCLM e Ω C p K)

theorem flattenCylinderSupportedCLM_underlying
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (K : Compacts (Space (m + 1)))
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K) :
    sobolevUnderlying (flattenCylinderSupportedCLM e q Ω C p K u) =
      (physicalChartMap e q Ω C).lpPullback 𝕜 p
        (domainLpRestrict (physicalChartOpen e Ω C)
          (lpZeroExtension Ω p (sobolevUnderlying u.val))) := by
  rw [flattenCylinderSupportedCLM, ContinuousLinearMap.comp_apply,
    (physicalChartMap e q Ω C).sobolevPullback_underlying]
  congr 1
  exact artificialBoundaryTransferCLM_derivative Ω (physicalChartOpen e Ω C) ⊤ p K
    (subset_univ _) (fun _ hx => hx.1.1) u (zeroSobolevIndex (m + 1) 1)

theorem flattenCylinderSupportedCLM_zero_off_compact
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (K : Compacts (Space (m + 1))) (hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C)
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K) :
    ∀ᵐ x ∂volume.restrict (flatChartOpen q C.center C.radius C.height : Set (Space (m + 1))),
      x ∉ fullChartPullbackCompact e q C K hK →
        sobolevUnderlying (flattenCylinderSupportedCLM e q Ω C p K u) x = 0 := by
  change ∀ᵐ x ∂volume.restrict (flatChartOpen q C.center C.radius C.height : Set (Space (m + 1))),
    x ∉ fullChartPullbackCompact e q C K hK →
      sobolevUnderlying ((physicalChartMap e q Ω C).sobolevPullback meyersSerrin_smoothDensity
        (Nat.succ_pos m) 𝕜 p (physicalSupportedRestrictionCLM e Ω C p K u)) x = 0
  rw [(physicalChartMap e q Ω C).sobolevPullback_underlying]
  exact physicalChart_pullback_zero_off_compact e q Ω C
    (sobolevUnderlying (physicalSupportedRestrictionCLM e Ω C p K u)) K hK
    (artificialBoundaryTransferCLM_zero_off_compact Ω (physicalChartOpen e Ω C) ⊤ p K
      (subset_univ _) (fun _ hx => hx.1.1) u)

/-- Flatten and glue across the artificial sides and top of the chart.
Only the genuine boundary remains in the target half-space. -/
def flattenSupportedCLM
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (K : Compacts (Space (m + 1))) (hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C) :
    sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K →L[𝕜] Sobolev 𝕜 (flatPositiveOpen q) 1 p :=
  (artificialBoundaryTransferCLM (flatChartOpen q C.center C.radius C.height)
    (flatPositiveOpen q) (fullFlatChartOpen q C.center C.radius C.height) p
    (fullChartPullbackCompact e q C K hK) (fullChartPullbackCompact_subset e q C K hK)
    (flatPositive_inter_full_subset_flat q C.center C.radius C.height)).comp
      ((flattenCylinderSupportedCLM e q Ω C p K).codRestrict
        (sobolevSupportedSubmodule (k := 1) 𝕜 (flatChartOpen q C.center C.radius C.height) p
          (fullChartPullbackCompact e q C K hK))
        (flattenCylinderSupportedCLM_zero_off_compact e q Ω C p K hK))

theorem flattenSupportedCLM_derivative
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (K : Compacts (Space (m + 1))) (hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C)
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K) (α : SobolevIndex (m + 1) 1) :
    sobolevDerivative (flattenSupportedCLM e q Ω C p K hK u) α =
      domainLpRestrict (flatPositiveOpen q)
        (lpZeroExtension (flatChartOpen q C.center C.radius C.height) p
          (sobolevDerivative (flattenCylinderSupportedCLM e q Ω C p K u) α)) := by
  exact artificialBoundaryTransferCLM_derivative
    (flatChartOpen q C.center C.radius C.height) (flatPositiveOpen q)
    (fullFlatChartOpen q C.center C.radius C.height) p
    (fullChartPullbackCompact e q C K hK) (fullChartPullbackCompact_subset e q C K hK)
    (flatPositive_inter_full_subset_flat q C.center C.radius C.height) _ α

theorem flattenSupportedCLM_underlying
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (K : Compacts (Space (m + 1))) (hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C)
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K) :
    sobolevUnderlying (flattenSupportedCLM e q Ω C p K hK u) =
      domainLpRestrict (flatPositiveOpen q)
        (lpZeroExtension (flatChartOpen q C.center C.radius C.height) p
          ((physicalChartMap e q Ω C).lpPullback 𝕜 p
            (domainLpRestrict (physicalChartOpen e Ω C)
              (lpZeroExtension Ω p (sobolevUnderlying u.val))))) := by
  change sobolevDerivative (flattenSupportedCLM e q Ω C p K hK u)
    (zeroSobolevIndex (m + 1) 1) = _
  rw [flattenSupportedCLM_derivative]
  change domainLpRestrict (flatPositiveOpen q)
    (lpZeroExtension (flatChartOpen q C.center C.radius C.height) p
      (sobolevUnderlying (flattenCylinderSupportedCLM e q Ω C p K u))) = _
  rw [flattenCylinderSupportedCLM_underlying]

@[simp] theorem euclideanReflectionPoint_flatCoordinates {m : ℕ} (z : Ambient m) :
    euclideanReflectionPoint (flatCoordinates m z) =
      flatCoordinates m (WithLp.toLp 2 (z.ofLp.1, -z.ofLp.2)) := by
  apply PiLp.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [euclideanReflectionPoint, ExpandedFA.Sobolev.HalfSpace.reflect, ACL.coordinates,
      flatCoordinates]
  · simp [euclideanReflectionPoint, ExpandedFA.Sobolev.HalfSpace.reflect, ACL.coordinates,
      flatCoordinates]

theorem euclideanReflectionPoint_mapsTo_fullFlatChart {m : ℕ}
    (c : Space m) (r a : ℝ) :
    MapsTo (@euclideanReflectionPoint m)
      (fullFlatChartOpen (flatCoordinates m) c r a)
      (fullFlatChartOpen (flatCoordinates m) c r a) := by
  rintro x ⟨z, hz, rfl⟩
  rw [euclideanReflectionPoint_flatCoordinates]
  refine ⟨WithLp.toLp 2 (z.ofLp.1, -z.ofLp.2), ⟨hz.1, ?_⟩, rfl⟩
  change -a < -z.ofLp.2 ∧ -z.ofLp.2 < a
  have h1 : -a < z.ofLp.2 := hz.2.1
  have h2 : z.ofLp.2 < a := hz.2.2
  constructor <;> linarith only [h1, h2]

theorem euclideanReflectedCompact_subset_fullFlatChart {m : ℕ}
    (c : Space m) (r a : ℝ) (K : Compacts (Space (m + 1)))
    (hK : (K : Set (Space (m + 1))) ⊆ fullFlatChartOpen (flatCoordinates m) c r a) :
    (euclideanReflectedCompact K : Set (Space (m + 1))) ⊆
      fullFlatChartOpen (flatCoordinates m) c r a := by
  intro x hx
  rcases hx with hx | ⟨y, hy, rfl⟩
  · exact hK hx
  · exact euclideanReflectionPoint_mapsTo_fullFlatChart c r a (hK hy)

/-- A closed-interval AC representative with zero endpoints extends to a
whole-line AC function by zero, with exactly the zero-extended derivative. -/
lemma interval_zero_extension_ac {𝕜 : Type} [RCLike 𝕜] {f h : ℝ → 𝕜} {a b : ℝ}
    (hab : a < b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt f (h t) t)
    (hi : LocallyIntegrable h volume) (ha : f a = 0) (hb : f b = 0) :
    ACL.LocallyAC ((Ioo a b).indicator f) univ ∧
      (∀ᵐ t ∂volume, HasDerivAt ((Ioo a b).indicator f)
        ((Ioo a b).indicator h t) t) := by
  let k := (Ioo a b).indicator h
  have hki : LocallyIntegrable k volume := hi.indicator measurableSet_Ioo
  have hint (s t : ℝ) : IntervalIntegrable k volume s t :=
    (hki.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  let g : ℝ → 𝕜 := fun t => ∫ s in a..t, k s
  have hga (s t : ℝ) : AbsolutelyContinuousOnInterval g s t :=
    ExpandedFA.Sobolev.OneDimensional.integral_primitive_absolutelyContinuous hint s t a
  have hmid (t : ℝ) (ht : t ∈ Icc a b) : g t = f t := by
    have hsub : uIcc a t ⊆ uIcc a b := by
      rw [uIcc_of_le ht.1, uIcc_of_le hab.le]
      exact Icc_subset_Icc le_rfl ht.2
    have hdk : ∀ᵐ s ∂volume, s ∈ uIcc a t → HasDerivAt f (k s) s := by
      filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp hd,
        volume.ae_ne a, volume.ae_ne b] with s hs hsa hsb hst
      have hsab : s ∈ Icc a b := by
        simpa only [uIcc_of_le hab.le] using hsub hst
      have hsi : s ∈ Ioo a b :=
        ⟨lt_of_le_of_ne hsab.1 hsa.symm, lt_of_le_of_ne hsab.2 hsb⟩
      simpa only [k, indicator_of_mem hsi] using hs hsi
    have he := ExpandedFA.Sobolev.OneDimensional.integral_eq_sub_of_absolutelyContinuous_of_ae_hasDerivAt
      (hf.mono hsub) hki hdk
    change (∫ s in a..t, k s) = f t
    simpa only [ha, sub_zero] using he
  have hleft (t : ℝ) (ht : t ≤ a) : g t = 0 := by
    change (∫ s in a..t, k s) = 0
    rw [intervalIntegral.integral_symm, neg_eq_zero]
    rw [intervalIntegral.integral_of_le ht]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact indicator_of_notMem (fun hsi => (not_lt_of_ge hs.2) hsi.1) h
  have hright (t : ℝ) (ht : b ≤ t) : g t = 0 := by
    have hz : (∫ s in b..t, k s) = 0 := by
      rw [intervalIntegral.integral_of_le ht]
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact indicator_of_notMem (fun hsi => (not_lt_of_ge hs.1.le) hsi.2) h
    have he := intervalIntegral.integral_add_adjacent_intervals (hint a b) (hint b t)
    change g b + (∫ s in b..t, k s) = g t at he
    rw [hmid b ⟨hab.le, le_rfl⟩, hb, hz, zero_add] at he
    exact he.symm
  have hgeq : g = (Ioo a b).indicator f := by
    funext t
    by_cases hta : t ≤ a
    · rw [hleft t hta]
      exact (indicator_of_notMem (fun hti => (not_lt_of_ge hta) hti.1) f).symm
    · by_cases hbt : b ≤ t
      · rw [hright t hbt]
        exact (indicator_of_notMem (fun hti => (not_lt_of_ge hbt) hti.2) f).symm
      · have hti : t ∈ Ioo a b := ⟨not_le.mp hta, not_le.mp hbt⟩
        rw [hmid t ⟨hti.1.le, hti.2.le⟩, indicator_of_mem hti]
  constructor
  · intro s t _
    rw [← hgeq]
    exact hga s t
  · rw [← hgeq]
    exact (_root_.LocallyIntegrable.ae_hasDerivAt_integral hki).mono fun t ht => ht a

lemma linePoint_coordinate (x : Space 1) : linePoint (x.ofLp 0) = x := by
  apply WithLp.ofLp_injective 2
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  rfl

lemma linePoint_measurePreserving : MeasurePreserving linePoint volume volume := by
  exact (PiLp.volume_preserving_toLp (Fin 1)).comp
    (MeasurePreserving.symm (MeasurableEquiv.funUnique (Fin 1) ℝ)
      (volume_preserving_funUnique (Fin 1) ℝ))

lemma lineCoordinate_measurePreserving :
    MeasurePreserving (fun x : Space 1 => x.ofLp 0) volume volume := by
  exact (volume_preserving_funUnique (Fin 1) ℝ).comp
    (PiLp.volume_preserving_ofLp (Fin 1))

lemma ae_space_one_of_ae_linePoint {P : Space 1 → Prop}
    (h : ∀ᵐ t ∂volume, P (linePoint t)) : ∀ᵐ x ∂volume, P x := by
  have hh := lineCoordinate_measurePreserving.quasiMeasurePreserving.ae h
  simpa only [linePoint_coordinate] using hh

lemma ac_finset_sum {ι E : Type*} [SeminormedAddCommGroup E]
    (s : Finset ι) (f : ι → ℝ → E) {a b : ℝ}
    (hf : ∀ i ∈ s, AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun t => ∑ i ∈ s, f i t) a b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, AbsolutelyContinuousOnInterval, dist_self, Finset.sum_const_zero]
      exact tendsto_const_nhds
  | @insert i s his ih =>
      have hfi := hf i (Finset.mem_insert_self i s)
      have hfs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      apply (hfi.add hfs).congr
      intro t _
      simp only [Finset.sum_insert his, Pi.add_apply]

lemma locallyAC_finset_sum {ι : Type*} {𝕜 : Type} [RCLike 𝕜]
    (s : Finset ι) (f : ι → ℝ → 𝕜) (hf : ∀ i ∈ s, ACL.LocallyAC (f i) univ) :
    ACL.LocallyAC (fun t => ∑ i ∈ s, f i t) univ := by
  intro a b _
  exact ac_finset_sum s f (fun i hi => hf i hi a b (subset_univ _))

lemma sum_indicator_intervals {n : ℕ} {a b : Fin n → ℝ}
    (hdis : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) (t : ℝ) :
    ∑ i, (Ioo (a i) (b i)).indicator f t =
      (⋃ i, Ioo (a i) (b i)).indicator f t := by
  classical
  symm
  simpa only [Finset.mem_univ, iUnion_true] using
    (Finset.indicator_biUnion_apply Finset.univ (fun i => Ioo (a i) (b i))
      (fun i _ j _ hij => hdis hij) t :
      (⋃ i ∈ (Finset.univ : Finset (Fin n)), Ioo (a i) (b i)).indicator f t = _)

lemma zeroExtension_of_zero_endpoint_values {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space 1)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {n : ℕ} {a b : Fin n → ℝ}
    (hab : ∀ i, a i < b i)
    (hdis : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (hΩ : (Ω : Set (Space 1)) = ⋃ i, linePoint '' Ioo (a i) (b i))
    (u : Sobolev 𝕜 Ω 1 p) (f : ℝ → 𝕜) (hf : IsEndpointRepresentative a b u f)
    (hz : ∀ i, f (a i) = 0 ∧ f (b i) = 0) : HasZeroExtension u := by
  classical
  let U0 := lpZeroExtension Ω p (sobolevUnderlying u)
  let U1 := lpZeroExtension Ω p (firstWeakDerivative u 0)
  let G : ℝ → 𝕜 := fun t => U1 (linePoint t)
  let F : ℝ → 𝕜 := fun t => ∑ i, (Ioo (a i) (b i)).indicator f t
  have hpre := linePoint_preimage_intervals hΩ
  have hGi : LocallyIntegrable G volume := by
    have hm : MemLp G p volume := by
      have hmU1 : MemLp (U1 : Space 1 → 𝕜) p volume := by
        simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp U1
      exact hmU1.comp_measurePreserving linePoint_measurePreserving
    exact hm.locallyIntegrable (Fact.out : 1 ≤ p)
  have hU1 : ∀ᵐ t ∂volume, U1 (linePoint t) =
      (Ω : Set (Space 1)).indicator (firstWeakDerivative u 0) (linePoint t) :=
    ae_linePoint (lpZeroExtension_ae Ω p _)
  have hd (i : Fin n) : ∀ᵐ t ∂volume.restrict (Ioo (a i) (b i)),
      HasDerivAt f (G t) t := by
    have hsub : Ioo (a i) (b i) ⊆ linePoint ⁻¹' (Ω : Set (Space 1)) := by
      rw [hpre]
      exact subset_iUnion (fun j => Ioo (a j) (b j)) i
    filter_upwards [ae_restrict_of_ae hU1,
      ae_restrict_of_ae_restrict_of_subset hsub hf.2.2,
      ae_restrict_mem measurableSet_Ioo] with t ht hdt hti
    have htiΩ : linePoint t ∈ (Ω : Set (Space 1)) := hsub hti
    dsimp only [G]
    rw [ht, indicator_of_mem htiΩ]
    exact hdt
  have hAC (i : Fin n) := interval_zero_extension_ac (hab i) (hf.2.1 i) (hd i)
    hGi (hz i).1 (hz i).2
  have hFac : ACL.LocallyAC F univ :=
    locallyAC_finset_sum Finset.univ _ (fun i _ => (hAC i).1)
  have hFder : ∀ᵐ t ∂volume, HasDerivAt F (G t) t := by
    have hh := ae_all_iff.mpr (fun i => (hAC i).2)
    filter_upwards [hh, hU1] with t ht hU1t
    have he : ∑ i, (Ioo (a i) (b i)).indicator G t = G t := by
      rw [sum_indicator_intervals hdis, ← hpre]
      by_cases hti : t ∈ linePoint ⁻¹' (Ω : Set (Space 1))
      · exact indicator_of_mem hti G
      · rw [indicator_of_notMem hti]
        change 0 = U1 (linePoint t)
        rw [hU1t]
        exact (indicator_of_notMem (show linePoint t ∉ (Ω : Set (Space 1)) from hti) _).symm
    rw [← he]
    exact HasDerivAt.fun_sum fun i _ => ht i
  have hFrep : ∀ᵐ t ∂volume, U0 (linePoint t) = F t := by
    have hA : MeasurableSet (linePoint ⁻¹' (Ω : Set (Space 1))) :=
      Ω.isOpen.measurableSet.preimage linePoint_measurePreserving.measurable
    have hfi := (ae_eq_restrict_iff_indicator_ae_eq hA).mp hf.1
    filter_upwards [ae_linePoint (lpZeroExtension_ae Ω p (sobolevUnderlying u)), hfi]
      with t ht hft
    rw [ht]
    dsimp only [F]
    rw [sum_indicator_intervals hdis, ← hpre, ← hft]
    by_cases htΩ : linePoint t ∈ (Ω : Set (Space 1))
    · rw [indicator_of_mem htΩ, indicator_of_mem (show t ∈ linePoint ⁻¹' (Ω : Set (Space 1)) from htΩ)]
    · rw [indicator_of_notMem htΩ,
        indicator_of_notMem (show t ∉ linePoint ⁻¹' (Ω : Set (Space 1)) from htΩ)]
  have hweak : distributionPartial {(0 : Fin 1)}
      (regularDistribution (⊤ : Opens (Space 1)) U0) =
      regularDistribution (⊤ : Opens (Space 1)) U1 := by
    apply (acl_dimensionOne 𝕜 (⊤ : Opens (Space 1)) U0 U1
      (domainLp_locallyIntegrable ⊤ p _) (domainLp_locallyIntegrable ⊤ p _)).mpr
    refine ⟨fun x => F (x.ofLp 0), ?_, ?_, ?_⟩
    · simp only [Opens.coe_top, Measure.restrict_univ]
      apply ae_space_one_of_ae_linePoint
      exact hFrep
    · simpa only [ACL.fiber, Opens.coe_top, preimage_univ, acl_line_one_eq, linePoint] using hFac
    · simpa only [ACL.fiber, Opens.coe_top, preimage_univ, Measure.restrict_univ,
        acl_line_one_eq, linePoint, G] using hFder
  have hderivs : HasSobolevDerivatives (⊤ : Opens (Space 1)) 1 p U0 := by
    intro α hα
    by_cases hzα : α = 0
    · subst α
      exact ⟨U0, derivative_zero 1 𝕜 ⊤ _⟩
    · have hc : α.card = 1 := by
        have hn := Multiset.card_eq_zero.not.mpr hzα
        omega
      obtain ⟨j, rfl⟩ := Multiset.card_eq_one.mp hc
      have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      exact ⟨U1, hweak⟩
  obtain ⟨w, hw⟩ := (Set.ext_iff.mp (sobolev_range (⊤ : Opens (Space 1)) 1 p) U0).mpr hderivs
  exact ⟨w, hw⟩
/-- The entire zero-extension criterion in physical dimension one, with the
same canonical trace and all four frozen hypotheses explicitly retained. -/
theorem zero_extension_criterion_oneDimension_conditional
    (_hCutoff : Expected.CutoffCompatibility)
    (hEndpoint : Expected.EndpointIdentification)
    (_hTrace : Expected.TraceExists)
    (_hUnique : Expected.TraceUniqueness) :
    ∀ (e : Ambient 0 ≃ₗᵢ[ℝ] Space 1) (Ω : Opens (Space 1)),
      IsLipschitzOpen (geometricOpen e Ω : Set (Ambient 0)) →
      ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ →
      ∀ T : Sobolev 𝕜 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p, IsTrace T →
      ∀ u : Sobolev 𝕜 Ω 1 p, T u = 0 ↔ HasZeroExtension u := by
  intro e Ω hΩ 𝕜 _ p _ hp T hT u
  obtain ⟨hcount, n, a, b, hab, hinj, hdis, hopen, hfront, _, hrep, hval⟩ :=
    hEndpoint e Ω hΩ 𝕜 p hp T hT
  obtain ⟨f, hf⟩ := hrep u
  constructor
  · intro hu
    have hz := (endpoint_trace_eq_zero_iff T hcount hfront hval u f hf).mp hu
    exact zeroExtension_of_zero_endpoint_values hab hdis hopen u f hf hz
  · intro hu
    apply (endpoint_trace_eq_zero_iff T hcount hfront hval u f hf).mpr
    exact zeroExtension_implies_zero_endpoint_values hab hinj hdis hopen u f hf hu


theorem physicalSupportedRestrictionCLM_underlying_ae
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (K : Compacts (Space (m + 1)))
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K) :
    sobolevUnderlying (physicalSupportedRestrictionCLM e Ω C p K u) =ᵐ[
      volume.restrict (physicalChartOpen e Ω C : Set (Space (m + 1)))] sobolevUnderlying u.val := by
  have he := artificialBoundaryTransferCLM_derivative Ω (physicalChartOpen e Ω C) ⊤ p K
    (subset_univ _) (fun _ hx => hx.1.1) u (zeroSobolevIndex (m + 1) 1)
  change sobolevUnderlying (physicalSupportedRestrictionCLM e Ω C p K u) =
    domainLpRestrict (physicalChartOpen e Ω C) (lpZeroExtension Ω p (sobolevUnderlying u.val)) at he
  rw [he]
  filter_upwards [P102.U4.domainLpRestrict_ae (physicalChartOpen e Ω C)
      (lpZeroExtension Ω p (sobolevUnderlying u.val)),
    ae_restrict_of_ae (lpZeroExtension_ae Ω p (sobolevUnderlying u.val)),
    ae_restrict_mem (physicalChartOpen e Ω C).isOpen.measurableSet] with x hx hz hxU
  rw [hx,hz,indicator_of_mem hxU.1]

theorem flattenCylinderSupportedCLM_underlying_ae
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (K : Compacts (Space (m + 1)))
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K) :
    sobolevUnderlying (flattenCylinderSupportedCLM e q Ω C p K u) =ᵐ[
      volume.restrict (flatChartOpen q C.center C.radius C.height : Set (Space (m + 1)))]
      (fun x => sobolevUnderlying u.val ((physicalChartMap e q Ω C).toFun x)) := by
  change sobolevUnderlying ((physicalChartMap e q Ω C).sobolevPullback meyersSerrin_smoothDensity
    (Nat.succ_pos m) 𝕜 p (physicalSupportedRestrictionCLM e Ω C p K u)) =ᵐ[_] _
  rw [(physicalChartMap e q Ω C).sobolevPullback_underlying]
  exact ((physicalChartMap e q Ω C).lpPullback_ae 𝕜 p _).trans
    ((physicalChartMap e q Ω C).ae_comp (physicalSupportedRestrictionCLM_underlying_ae e Ω C p K u))

theorem flattenSupportedCLM_underlying_ae
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (K : Compacts (Space (m + 1))) (hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C)
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K) :
    sobolevUnderlying (flattenSupportedCLM e q Ω C p K hK u) =ᵐ[
      volume.restrict (flatPositiveOpen q : Set (Space (m + 1)))]
      (flatChartOpen q C.center C.radius C.height : Set (Space (m + 1))).indicator
        (fun x => sobolevUnderlying u.val ((physicalChartMap e q Ω C).toFun x)) := by
  have he := flattenSupportedCLM_derivative e q Ω C p K hK u (zeroSobolevIndex (m + 1) 1)
  change sobolevUnderlying (flattenSupportedCLM e q Ω C p K hK u) =
    domainLpRestrict (flatPositiveOpen q)
      (lpZeroExtension (flatChartOpen q C.center C.radius C.height) p
        (sobolevUnderlying (flattenCylinderSupportedCLM e q Ω C p K u))) at he
  rw [he]
  have hrep := (ae_restrict_iff' (flatChartOpen q C.center C.radius C.height).isOpen.measurableSet).mp
    (flattenCylinderSupportedCLM_underlying_ae e q Ω C p K u)
  filter_upwards [P102.U4.domainLpRestrict_ae (flatPositiveOpen q)
      (lpZeroExtension (flatChartOpen q C.center C.radius C.height) p
        (sobolevUnderlying (flattenCylinderSupportedCLM e q Ω C p K u))),
    ae_restrict_of_ae (lpZeroExtension_ae (flatChartOpen q C.center C.radius C.height) p
      (sobolevUnderlying (flattenCylinderSupportedCLM e q Ω C p K u))),
    ae_restrict_of_ae hrep] with x hx hz hr
  rw [hx,hz]
  by_cases hxU : x ∈ flatChartOpen q C.center C.radius C.height
  · rw [indicator_of_mem hxU,indicator_of_mem hxU]
    exact hr hxU
  · rw [indicator_of_notMem hxU,indicator_of_notMem hxU]


theorem flattenSupportedCLM_represents
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (K : Compacts (Space (m + 1))) (hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C)
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K)
    (f : Space (m + 1) → 𝕜) (hf : tsupport f ⊆ (K : Set (Space (m + 1))))
    (hu : sobolevUnderlying u.val =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] f) :
    sobolevUnderlying (flattenSupportedCLM e q Ω C p K hK u) =ᵐ[
      volume.restrict (flatPositiveOpen q : Set (Space (m + 1)))]
      (f ∘ (fullChartMap e q C).toFun) := by
  have hphysical : sobolevUnderlying u.val =ᵐ[
      volume.restrict (physicalChartOpen e Ω C : Set (Space (m + 1)))] f :=
    hu.filter_mono (ae_mono (volume.restrict_mono_set (fun _ hx => hx.1)))
  have hflat := (ae_restrict_iff'
    (flatChartOpen q C.center C.radius C.height).isOpen.measurableSet).mp
      ((physicalChartMap e q Ω C).ae_comp hphysical)
  filter_upwards [flattenSupportedCLM_underlying_ae e q Ω C p K hK u,
      ae_restrict_of_ae hflat, ae_restrict_mem (flatPositiveOpen q).isOpen.measurableSet]
      with x hx hr hxP
  rw [hx]
  by_cases hxF : x ∈ flatChartOpen q C.center C.radius C.height
  · rw [indicator_of_mem hxF]
    exact hr hxF
  · rw [indicator_of_notMem hxF]
    symm
    apply image_eq_zero_of_notMem_tsupport
    intro hxS
    have hxQ := fullChartMap_tsupport_comp_subset e q C f K hK hf hxS
    have hxW := fullChartPullbackCompact_subset e q C K hK hxQ
    exact hxF (flatPositive_inter_full_subset_flat q C.center C.radius C.height ⟨hxP,hxW⟩)

theorem flattenSupportedCLM_continuous_representation
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (K : Compacts (Space (m + 1))) (hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C)
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K)
    (f : Space (m + 1) → 𝕜) (hc : Continuous f)
    (hf : tsupport f ⊆ (K : Set (Space (m + 1))))
    (hu : sobolevUnderlying u.val =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] f) :
    Continuous (f ∘ (fullChartMap e q C).toFun) ∧
    HasCompactSupport (f ∘ (fullChartMap e q C).toFun) ∧
    sobolevUnderlying (flattenSupportedCLM e q Ω C p K hK u) =ᵐ[
      volume.restrict (flatPositiveOpen q : Set (Space (m + 1)))]
      (f ∘ (fullChartMap e q C).toFun) :=
  ⟨fullChartMap_continuous_comp e q C f hc K hK hf,
    fullChartMap_hasCompactSupport_comp e q C f K hK hf,
    flattenSupportedCLM_represents e q Ω C p K hK u f hf hu⟩


section BoundaryData

def chartBaseOpen {G : Set (Ambient m)} (C : BoundaryChart G) : Opens (Space m) :=
  ⟨ball C.center C.radius,isOpen_ball⟩

theorem chartBoundaryParam_aemeasurable
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m))) :
    AEMeasurable (chartBoundaryParam e Ω C)
      (volume.restrict (chartBaseOpen C : Set (Space m))) :=
  (chartBoundaryParam_lipschitz e Ω C).continuousOn.aemeasurable measurableSet_ball

theorem chartBoundaryParam_ae_comp
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    {P : Space (m + 1) → Prop} (hP : ∀ᵐ x ∂boundaryMeasure Ω, P x) :
    ∀ᵐ x ∂volume.restrict (chartBaseOpen C : Set (Space m)), P (chartBoundaryParam e Ω C x) :=
  ae_of_ae_map (chartBoundaryParam_aemeasurable e Ω C)
    ((Measure.absolutelyContinuous_of_le (chartBoundaryParam_map_volume_le e Ω C)).ae_le hP)

theorem chartBoundaryParam_memLp_comp
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} {f : Space (m + 1) → E}
    (hf : MemLp f p (boundaryMeasure Ω)) :
    MemLp (f ∘ chartBoundaryParam e Ω C) p
      (volume.restrict (chartBaseOpen C : Set (Space m))) :=
  (hf.mono_measure (chartBoundaryParam_map_volume_le e Ω C)).comp_of_map
    (chartBoundaryParam_aemeasurable e Ω C)

theorem chartBoundaryParam_eLpNorm_comp_le
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} {f : Space (m + 1) → E}
    (hf : MemLp f p (boundaryMeasure Ω)) :
    eLpNorm (f ∘ chartBoundaryParam e Ω C) p
      (volume.restrict (chartBaseOpen C : Set (Space m))) ≤ eLpNorm f p (boundaryMeasure Ω) := by
  have hm := hf.mono_measure (chartBoundaryParam_map_volume_le e Ω C)
  change eLpNorm (f ∘ chartBoundaryParam e Ω C) p
    (volume.restrict (ball C.center C.radius)) ≤ _
  rw [← eLpNorm_map_measure hm.aestronglyMeasurable (chartBoundaryParam_aemeasurable e Ω C)]
  exact eLpNorm_mono_measure f (chartBoundaryParam_map_volume_le e Ω C)

variable (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]

def chartBoundaryLpPullbackLinear : BoundaryLp 𝕜 Ω p →ₗ[𝕜] DomainLp 𝕜 (chartBaseOpen C) p where
  toFun u := (chartBoundaryParam_memLp_comp e Ω C (Lp.memLp u)).toLp (u ∘ chartBoundaryParam e Ω C)
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(chartBoundaryParam_memLp_comp e Ω C (Lp.memLp (u + v))).coeFn_toLp,
      (chartBoundaryParam_memLp_comp e Ω C (Lp.memLp u)).coeFn_toLp,
      (chartBoundaryParam_memLp_comp e Ω C (Lp.memLp v)).coeFn_toLp,
      Lp.coeFn_add ((chartBoundaryParam_memLp_comp e Ω C (Lp.memLp u)).toLp (u ∘ chartBoundaryParam e Ω C))
        ((chartBoundaryParam_memLp_comp e Ω C (Lp.memLp v)).toLp (v ∘ chartBoundaryParam e Ω C)),
      chartBoundaryParam_ae_comp e Ω C (Lp.coeFn_add u v)] with x huv hu hv hadd hsource
    simpa only [Function.comp_apply, huv, hadd, Pi.add_apply, hu, hv] using hsource
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [(chartBoundaryParam_memLp_comp e Ω C (Lp.memLp (c • u))).coeFn_toLp,
      (chartBoundaryParam_memLp_comp e Ω C (Lp.memLp u)).coeFn_toLp,
      Lp.coeFn_smul c ((chartBoundaryParam_memLp_comp e Ω C (Lp.memLp u)).toLp (u ∘ chartBoundaryParam e Ω C)),
      chartBoundaryParam_ae_comp e Ω C (Lp.coeFn_smul c u)] with x hcu hu hsmul hsource
    simpa only [Function.comp_apply, hcu, RingHom.id_apply, hsmul, Pi.smul_apply, hu] using hsource

theorem chartBoundaryLpPullbackLinear_norm_le (u : BoundaryLp 𝕜 Ω p) :
    ‖chartBoundaryLpPullbackLinear e Ω C 𝕜 p u‖ ≤ ‖u‖ := by
  change ‖(chartBoundaryParam_memLp_comp e Ω C (Lp.memLp u)).toLp (u ∘ chartBoundaryParam e Ω C)‖ ≤ _
  rw [Lp.norm_toLp]
  exact ENNReal.toReal_mono (by finiteness)
    (chartBoundaryParam_eLpNorm_comp_le e Ω C (Lp.memLp u))

/-- Pull physical boundary data to the chart base, with norm at most one. -/
def chartBoundaryLpPullback : BoundaryLp 𝕜 Ω p →L[𝕜] DomainLp 𝕜 (chartBaseOpen C) p :=
  (chartBoundaryLpPullbackLinear e Ω C 𝕜 p).mkContinuous 1
    (fun u => by simpa only [one_mul] using chartBoundaryLpPullbackLinear_norm_le e Ω C 𝕜 p u)

theorem chartBoundaryLpPullback_ae (u : BoundaryLp 𝕜 Ω p) :
    chartBoundaryLpPullback e Ω C 𝕜 p u =ᵐ[volume.restrict (chartBaseOpen C : Set (Space m))]
      (u ∘ chartBoundaryParam e Ω C) :=
  (chartBoundaryParam_memLp_comp e Ω C (Lp.memLp u)).coeFn_toLp

theorem chartBoundaryLpPullback_norm_le : ‖chartBoundaryLpPullback e Ω C 𝕜 p‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The same boundary pullback, extended by zero to the entire chart base. -/
def chartBoundaryLpPullbackFull : BoundaryLp 𝕜 Ω p →L[𝕜] DomainLp 𝕜 (⊤ : Opens (Space m)) p :=
  (lpZeroExtensionLI (chartBaseOpen C) p).toContinuousLinearMap.comp (chartBoundaryLpPullback e Ω C 𝕜 p)

theorem chartBoundaryLpPullbackFull_ae (u : BoundaryLp 𝕜 Ω p) :
    chartBoundaryLpPullbackFull e Ω C 𝕜 p u =ᵐ[volume]
      (chartBaseOpen C : Set (Space m)).indicator (u ∘ chartBoundaryParam e Ω C) := by
  have hlocal := (ae_restrict_iff' (chartBaseOpen C).isOpen.measurableSet).mp
    (chartBoundaryLpPullback_ae e Ω C 𝕜 p u)
  filter_upwards [lpZeroExtension_ae (chartBaseOpen C) p (chartBoundaryLpPullback e Ω C 𝕜 p u),
    hlocal] with x hx hl
  change lpZeroExtension (chartBaseOpen C) p (chartBoundaryLpPullback e Ω C 𝕜 p u) x = _
  rw [hx]
  by_cases hxB : x ∈ chartBaseOpen C
  · rw [indicator_of_mem hxB,indicator_of_mem hxB]
    exact hl hxB
  · rw [indicator_of_notMem hxB,indicator_of_notMem hxB]

theorem chartBoundaryLpPullbackFull_norm_le : ‖chartBoundaryLpPullbackFull e Ω C 𝕜 p‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖lpZeroExtension (chartBaseOpen C) p (chartBoundaryLpPullback e Ω C 𝕜 p u)‖ ≤ _
  rw [lpZeroExtension_norm]
  change ‖chartBoundaryLpPullbackLinear e Ω C 𝕜 p u‖ ≤ 1 * ‖u‖
  simpa only [one_mul] using chartBoundaryLpPullbackLinear_norm_le e Ω C 𝕜 p u

end BoundaryData


section LocalBulk

variable (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
  (Ω : Opens (Space (m + 1)))
  (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
  (p : ℝ≥0∞) [Fact (1 ≤ p)]
  (K : Compacts (Space (m + 1))) (hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C)

def flattenHalfSupportedCLM :
    sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K →L[𝕜] HalfSobolev m 𝕜 p :=
  (artificialBoundaryTransferCLM (flatChartOpen (flatCoordinates m) C.center C.radius C.height)
    (halfSpace m) (fullFlatChartOpen (flatCoordinates m) C.center C.radius C.height) p
    (fullChartPullbackCompact e (flatCoordinates m) C K hK)
    (fullChartPullbackCompact_subset e (flatCoordinates m) C K hK)
    (by rw [← flatPositiveOpen_flatCoordinates m]
        exact flatPositive_inter_full_subset_flat (flatCoordinates m) C.center C.radius C.height)).comp
    ((flattenCylinderSupportedCLM e (flatCoordinates m) Ω C p K).codRestrict
      (sobolevSupportedSubmodule (k := 1) 𝕜
        (flatChartOpen (flatCoordinates m) C.center C.radius C.height) p
        (fullChartPullbackCompact e (flatCoordinates m) C K hK))
      (flattenCylinderSupportedCLM_zero_off_compact e (flatCoordinates m) Ω C p K hK))

theorem flattenHalfSupportedCLM_zero_off_compact
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K) :
    ∀ᵐ x ∂volume.restrict (halfSpace m : Set (Space (m + 1))),
      x ∉ fullChartPullbackCompact e (flatCoordinates m) C K hK →
        sobolevUnderlying (flattenHalfSupportedCLM e Ω C p K hK u) x = 0 := by
  exact artificialBoundaryTransferCLM_zero_off_compact
    (flatChartOpen (flatCoordinates m) C.center C.radius C.height)
    (halfSpace m) (fullFlatChartOpen (flatCoordinates m) C.center C.radius C.height) p
    (fullChartPullbackCompact e (flatCoordinates m) C K hK)
    (fullChartPullbackCompact_subset e (flatCoordinates m) C K hK)
    (by rw [← flatPositiveOpen_flatCoordinates m]
        exact flatPositive_inter_full_subset_flat (flatCoordinates m) C.center C.radius C.height)
    _

def reflectSupportedCLM :
    sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K →L[𝕜]
      Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p :=
  (halfEvenReflection m 𝕜 p).comp (flattenHalfSupportedCLM e Ω C p K hK)

theorem reflectSupportedCLM_zero_off_compact
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K) :
    ∀ᵐ x ∂volume,
      x ∉ euclideanReflectedCompact (fullChartPullbackCompact e (flatCoordinates m) C K hK) →
        sobolevUnderlying (reflectSupportedCLM e Ω C p K hK u) x = 0 :=
  halfEvenReflection_zero_off_compact _ _
    (flattenHalfSupportedCLM_zero_off_compact e Ω C p K hK u)

def restrictedFlatEvenCLM :
    sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K →L[𝕜]
      Sobolev 𝕜 (fullFlatChartOpen (flatCoordinates m) C.center C.radius C.height) 1 p :=
  (sobolevRestrictCLM _).comp (reflectSupportedCLM e Ω C p K hK)

theorem restrictedFlatEvenCLM_zero_off_compact
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K) :
    ∀ᵐ x ∂volume.restrict (fullFlatChartOpen (flatCoordinates m) C.center C.radius C.height : Set (Space (m + 1))),
      x ∉ euclideanReflectedCompact (fullChartPullbackCompact e (flatCoordinates m) C K hK) →
        sobolevUnderlying (restrictedFlatEvenCLM e Ω C p K hK u) x = 0 := by
  filter_upwards [P102.U4.domainLpRestrict_ae
      (fullFlatChartOpen (flatCoordinates m) C.center C.radius C.height)
      (sobolevUnderlying (reflectSupportedCLM e Ω C p K hK u)),
    ae_restrict_of_ae (reflectSupportedCLM_zero_off_compact e Ω C p K hK u)]
    with x hx hz hxK
  exact hx.trans (hz hxK)

def localBulkSupport : Compacts (Space (m + 1)) :=
  ⟨(fullChartMap e (flatCoordinates m) C).toFun ''
      (euclideanReflectedCompact (fullChartPullbackCompact e (flatCoordinates m) C K hK) : Set (Space (m + 1))),
    (euclideanReflectedCompact (fullChartPullbackCompact e (flatCoordinates m) C K hK)).isCompact.image_of_continuousOn
      ((fullChartMap e (flatCoordinates m) C).lipschitz.continuousOn.mono
        (euclideanReflectedCompact_subset_fullFlatChart C.center C.radius C.height _
          (fullChartPullbackCompact_subset e (flatCoordinates m) C K hK)))⟩

theorem localBulkSupport_subset :
    (localBulkSupport e Ω C K hK : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C := by
  rintro x ⟨y, hy, rfl⟩
  exact (fullChartMap e (flatCoordinates m) C).mapsTo
    (euclideanReflectedCompact_subset_fullFlatChart C.center C.radius C.height _
      (fullChartPullbackCompact_subset e (flatCoordinates m) C K hK) hy)

def returnPhysicalSupportedCLM :
    sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K →L[𝕜]
      Sobolev 𝕜 (fullPhysicalChartOpen e C) 1 p :=
  ((fullChartMap e (flatCoordinates m) C).symm.sobolevPullback
    meyersSerrin_smoothDensity (Nat.succ_pos m) 𝕜 p).comp
      (restrictedFlatEvenCLM e Ω C p K hK)

theorem returnPhysicalSupportedCLM_zero_off_compact
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K) :
    ∀ᵐ x ∂volume.restrict (fullPhysicalChartOpen e C : Set (Space (m + 1))),
      x ∉ localBulkSupport e Ω C K hK →
        sobolevUnderlying (returnPhysicalSupportedCLM e Ω C p K hK u) x = 0 := by
  let g := fullChartMap e (flatCoordinates m) C
  change ∀ᵐ x ∂volume.restrict (fullPhysicalChartOpen e C : Set (Space (m + 1))),
    x ∉ localBulkSupport e Ω C K hK →
      sobolevUnderlying (g.symm.sobolevPullback meyersSerrin_smoothDensity
        (Nat.succ_pos m) 𝕜 p (restrictedFlatEvenCLM e Ω C p K hK u)) x = 0
  rw [g.symm.sobolevPullback_underlying]
  filter_upwards [g.symm.lpPullback_ae 𝕜 p
      (sobolevUnderlying (restrictedFlatEvenCLM e Ω C p K hK u)),
    g.symm.ae_comp (restrictedFlatEvenCLM_zero_off_compact e Ω C p K hK u),
    ae_restrict_mem (fullPhysicalChartOpen e C).isOpen.measurableSet]
    with x hx hz hxV hxK
  rw [hx]
  apply hz
  intro hy
  exact hxK ⟨g.invFun x, hy, g.right_inv x hxV⟩

def localBulkExtensionCLM :
    sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K →L[𝕜]
      Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p :=
  (artificialBoundaryTransferCLM (fullPhysicalChartOpen e C) ⊤ (fullPhysicalChartOpen e C)
    p (localBulkSupport e Ω C K hK) (localBulkSupport_subset e Ω C K hK)
    (fun _ hx => hx.2)).comp
    ((returnPhysicalSupportedCLM e Ω C p K hK).codRestrict
      (sobolevSupportedSubmodule (k := 1) 𝕜 (fullPhysicalChartOpen e C) p (localBulkSupport e Ω C K hK))
      (returnPhysicalSupportedCLM_zero_off_compact e Ω C p K hK))

theorem localBulkExtensionCLM_zero_off_compact
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K) :
    ∀ᵐ x ∂volume,
      x ∉ localBulkSupport e Ω C K hK →
        sobolevUnderlying (localBulkExtensionCLM e Ω C p K hK u) x = 0 := by
  simpa only [localBulkExtensionCLM, ContinuousLinearMap.comp_apply,
    Opens.coe_top, Measure.restrict_univ] using
    artificialBoundaryTransferCLM_zero_off_compact
      (fullPhysicalChartOpen e C) ⊤ (fullPhysicalChartOpen e C)
      p (localBulkSupport e Ω C K hK) (localBulkSupport_subset e Ω C K hK)
      (fun _ hx => hx.2) _


theorem artificialBoundaryTransferCLM_underlying_ae {d k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U V W : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (K : Compacts (Space d)) (hKW : (K : Set (Space d)) ⊆ W)
    (hVU : (V : Set (Space d)) ∩ (W : Set (Space d)) ⊆ U)
    (u : sobolevSupportedSubmodule (k := k) 𝕜 U p K) :
    sobolevUnderlying (artificialBoundaryTransferCLM U V W p K hKW hVU u) =ᵐ[
      volume.restrict (V : Set (Space d))] (U : Set (Space d)).indicator (sobolevUnderlying u.val) := by
  change sobolevDerivative (artificialBoundaryTransferCLM U V W p K hKW hVU u)
    (zeroSobolevIndex d k) =ᵐ[_] _
  rw [artificialBoundaryTransferCLM_derivative]
  exact (P102.U4.domainLpRestrict_ae V _).trans (ae_restrict_of_ae (lpZeroExtension_ae U p _))

theorem flattenHalfSupportedCLM_underlying_ae
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K) :
    sobolevUnderlying (flattenHalfSupportedCLM e Ω C p K hK u) =ᵐ[
      volume.restrict (halfSpace m : Set (Space (m + 1)))]
      (flatChartOpen (flatCoordinates m) C.center C.radius C.height : Set (Space (m + 1))).indicator
        (sobolevUnderlying (flattenCylinderSupportedCLM e (flatCoordinates m) Ω C p K u)) := by
  exact artificialBoundaryTransferCLM_underlying_ae
    (flatChartOpen (flatCoordinates m) C.center C.radius C.height)
    (halfSpace m) (fullFlatChartOpen (flatCoordinates m) C.center C.radius C.height) p
    (fullChartPullbackCompact e (flatCoordinates m) C K hK)
    (fullChartPullbackCompact_subset e (flatCoordinates m) C K hK)
    (by rw [← flatPositiveOpen_flatCoordinates m]
        exact flatPositive_inter_full_subset_flat (flatCoordinates m) C.center C.radius C.height)
    _

theorem restrictedFlatEvenCLM_agrees_positive
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K) :
    ∀ᵐ x ∂volume.restrict
      (fullFlatChartOpen (flatCoordinates m) C.center C.radius C.height : Set (Space (m + 1))),
      x ∈ flatChartOpen (flatCoordinates m) C.center C.radius C.height →
        sobolevUnderlying (restrictedFlatEvenCLM e Ω C p K hK u) x =
          sobolevUnderlying (flattenCylinderSupportedCLM e (flatCoordinates m) Ω C p K u) x := by
  have hhalf := (ae_restrict_iff' (halfSpace m).isOpen.measurableSet).mp
    (halfEvenReflection_restrict m 𝕜 p (flattenHalfSupportedCLM e Ω C p K hK u))
  have hflat := (ae_restrict_iff' (halfSpace m).isOpen.measurableSet).mp
    (flattenHalfSupportedCLM_underlying_ae e Ω C p K hK u)
  filter_upwards [P102.U4.domainLpRestrict_ae
      (fullFlatChartOpen (flatCoordinates m) C.center C.radius C.height)
      (sobolevUnderlying (reflectSupportedCLM e Ω C p K hK u)),
    ae_restrict_of_ae hhalf, ae_restrict_of_ae hflat] with x hx hh hf hxFlat
  have hxH : x ∈ halfSpace m := by
    rw [← flatPositiveOpen_flatCoordinates m]
    exact flatChartOpen_le_flatPositive (flatCoordinates m) C.center C.radius C.height hxFlat
  exact hx.trans ((hh hxH).trans ((hf hxH).trans (indicator_of_mem hxFlat _)))

theorem returnPhysicalSupportedCLM_agrees
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K) :
    sobolevUnderlying (returnPhysicalSupportedCLM e Ω C p K hK u) =ᵐ[
      volume.restrict (physicalChartOpen e Ω C : Set (Space (m + 1)))] sobolevUnderlying u.val := by
  let g := fullChartMap e (flatCoordinates m) C
  let gP := physicalChartMap e (flatCoordinates m) Ω C
  have hinc : (physicalChartOpen e Ω C : Set (Space (m + 1))) ⊆
      fullPhysicalChartOpen e C := fun _ hx => hx.2
  have hreturn := g.symm.lpPullback_ae 𝕜 p
    (sobolevUnderlying (restrictedFlatEvenCLM e Ω C p K hK u))
  have hmid := g.symm.ae_comp (restrictedFlatEvenCLM_agrees_positive e Ω C p K hK u)
  have hflat : sobolevUnderlying (flattenCylinderSupportedCLM e (flatCoordinates m) Ω C p K u) =ᵐ[
      volume.restrict (flatChartOpen (flatCoordinates m) C.center C.radius C.height : Set (Space (m + 1)))]
      fun x => sobolevUnderlying (physicalSupportedRestrictionCLM e Ω C p K u) (gP.toFun x) := by
    change sobolevUnderlying (gP.sobolevPullback meyersSerrin_smoothDensity
      (Nat.succ_pos m) 𝕜 p (physicalSupportedRestrictionCLM e Ω C p K u)) =ᵐ[_] _
    rw [gP.sobolevPullback_underlying]
    exact gP.lpPullback_ae 𝕜 p _
  have hflatback := gP.symm.ae_comp hflat
  have hstart := artificialBoundaryTransferCLM_underlying_ae Ω (physicalChartOpen e Ω C) ⊤ p K
    (subset_univ _) (fun _ hx => hx.1.1) u
  filter_upwards [hreturn.filter_mono (ae_mono (volume.restrict_mono_set hinc)),
    hmid.filter_mono (ae_mono (volume.restrict_mono_set hinc)), hflatback, hstart,
    ae_restrict_mem (physicalChartOpen e Ω C).isOpen.measurableSet]
    with x hr hm hf hs hxP
  change sobolevUnderlying (g.symm.sobolevPullback meyersSerrin_smoothDensity
    (Nat.succ_pos m) 𝕜 p (restrictedFlatEvenCLM e Ω C p K hK u)) x = _
  rw [g.symm.sobolevPullback_underlying]
  change g.symm.lpPullback 𝕜 p _ x = _ at hr ⊢
  simp only [Function.comp_apply] at hr
  have hf' := hf.trans (congrArg
    (fun y => sobolevUnderlying (physicalSupportedRestrictionCLM e Ω C p K u) y)
    (gP.right_inv x hxP))
  exact hr.trans ((hm (gP.inv_mapsTo hxP)).trans
    (hf'.trans (hs.trans (indicator_of_mem hxP.1 _))))


theorem localBulkExtensionCLM_underlying_ae
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K) :
    sobolevUnderlying (localBulkExtensionCLM e Ω C p K hK u) =ᵐ[volume]
      (fullPhysicalChartOpen e C : Set (Space (m + 1))).indicator
        (sobolevUnderlying (returnPhysicalSupportedCLM e Ω C p K hK u)) := by
  let v : sobolevSupportedSubmodule (k := 1) 𝕜 (fullPhysicalChartOpen e C) p
      (localBulkSupport e Ω C K hK) :=
    ⟨returnPhysicalSupportedCLM e Ω C p K hK u,
      returnPhysicalSupportedCLM_zero_off_compact e Ω C p K hK u⟩
  have h := artificialBoundaryTransferCLM_underlying_ae
    (fullPhysicalChartOpen e C) ⊤ (fullPhysicalChartOpen e C)
    p (localBulkSupport e Ω C K hK) (localBulkSupport_subset e Ω C K hK)
    (fun _ hx => hx.2) v
  change sobolevUnderlying (localBulkExtensionCLM e Ω C p K hK u) =ᵐ[
    volume.restrict (↑(⊤ : Opens (Space (m + 1))) : Set (Space (m + 1)))]
      (fullPhysicalChartOpen e C : Set (Space (m + 1))).indicator
        (sobolevUnderlying (returnPhysicalSupportedCLM e Ω C p K hK u)) at h
  simpa only [Opens.coe_top, Measure.restrict_univ] using h

theorem localBulkExtensionCLM_agrees
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K) :
    sobolevUnderlying (localBulkExtensionCLM e Ω C p K hK u) =ᵐ[
      volume.restrict (Ω : Set (Space (m + 1)))] sobolevUnderlying u.val := by
  have hr := (ae_restrict_iff' (physicalChartOpen e Ω C).isOpen.measurableSet).mp
    (returnPhysicalSupportedCLM_agrees e Ω C p K hK u)
  filter_upwards [ae_restrict_of_ae (localBulkExtensionCLM_underlying_ae e Ω C p K hK u),
    ae_restrict_of_ae hr, u.property, ae_restrict_mem Ω.isOpen.measurableSet]
    with x he hr hu hxΩ
  rw [he]
  by_cases hxF : x ∈ fullPhysicalChartOpen e C
  · rw [indicator_of_mem hxF]
    exact hr ⟨hxΩ, hxF⟩
  · rw [indicator_of_notMem hxF]
    exact (hu (fun hxK => hxF (hK hxK))).symm

include e C hK in
theorem localBulkExtension_exists :
    ∃ (Kout : Compacts (Space (m + 1)))
      (E : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K →L[𝕜]
        Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p),
      (∀ u, sobolevUnderlying (E u) =ᵐ[
        volume.restrict (Ω : Set (Space (m + 1)))] sobolevUnderlying u.val) ∧
      (∀ u, ∀ᵐ x ∂volume, x ∉ Kout → sobolevUnderlying (E u) x = 0) :=
  ⟨localBulkSupport e Ω C K hK, localBulkExtensionCLM e Ω C p K hK,
    localBulkExtensionCLM_agrees e Ω C p K hK,
    localBulkExtensionCLM_zero_off_compact e Ω C p K hK⟩

end LocalBulk

set_option maxHeartbeats 1800000 in
/-- Glue actual supported boundary extensions and the interior zero extension.
The hypothesis here is a local theorem interface, not an assumed global
extension certificate. -/
theorem bulkExtension_of_supported_chart_extensions
    (hCutoff : Expected.CutoffCompatibility) (hTrace : Expected.TraceExists)
    (hLocal : ∀ (m : ℕ) (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
      (Ω : Opens (Space (m + 1)))
      (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
      (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ →
      ∀ (K : Compacts (Space (m + 1))),
        (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C →
      ∃ (Kout : Compacts (Space (m + 1)))
        (E : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K →L[𝕜]
          Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p),
        (∀ u, sobolevUnderlying (E u) =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))]
          sobolevUnderlying u.val) ∧
        ∀ u, ∀ᵐ x ∂volume, x ∉ Kout → sobolevUnderlying (E u) x = 0) :
    Expected.BulkExtension := by
  classical
  intro m e Ω hΩ 𝕜 _ p _ hp
  obtain ⟨_, _, T, hT, _, _⟩ := hTrace m e Ω hΩ 𝕜 p hp
  obtain ⟨n, C, χ, M, hχ, hinter, hboundary, hrep, _, hsum, _, hzero⟩ :=
    exists_sobolev_localization hCutoff e hΩ hp T hT
  let K (i : Fin (n + 1)) : Compacts (Space (m + 1)) :=
    ⟨tsupport (χ i), (hχ i).2⟩
  have hsupp (i : Fin (n + 1)) (u : Sobolev 𝕜 Ω 1 p) :
      M i u ∈ sobolevSupportedSubmodule (k := 1) 𝕜 Ω p (K i) := by
    filter_upwards [hrep i u] with x hx hxK
    rw [hx, image_eq_zero_of_notMem_tsupport hxK, zero_smul]
  let N (i : Fin (n + 1)) : Sobolev 𝕜 Ω 1 p →L[𝕜]
      sobolevSupportedSubmodule (k := 1) 𝕜 Ω p (K i) :=
    (M i).codRestrict _ (hsupp i)
  have hlocal (i : Fin n) := hLocal m e Ω (C i) 𝕜 p hp (K i.succ) (hboundary i)
  choose Kout E hright hsupport using hlocal
  let E₀ : Sobolev 𝕜 Ω 1 p →L[𝕜] Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p :=
    (sobolevZeroExtensionLI Ω 1 p).toContinuousLinearMap.comp
      ((M 0).codRestrict (sobolevZeroSubmodule 𝕜 Ω 1 p) hzero)
  let F : Sobolev 𝕜 Ω 1 p →L[𝕜] Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p :=
    E₀ + ∑ i, (E i).comp (N i.succ)
  let Kall : Compacts (Space (m + 1)) :=
    ⟨(K 0 : Set (Space (m + 1))) ∪ ⋃ i, (Kout i : Set (Space (m + 1))),
      (K 0).isCompact.union (isCompact_iUnion fun i => (Kout i).isCompact)⟩
  have hrest₀ (u : Sobolev 𝕜 Ω 1 p) : sobolevRestrict Ω (E₀ u) = M 0 u := by
    apply sobolevUnderlying_injective Ω 1 p
    change domainLpRestrict Ω (lpZeroExtension Ω p (sobolevUnderlying (M 0 u))) = _
    exact domainLpRestrict_zeroExtension Ω _
  have hrest (i : Fin n) (u : Sobolev 𝕜 Ω 1 p) :
      sobolevRestrict Ω (E i (N i.succ u)) = M i.succ u := by
    apply sobolevUnderlying_injective Ω 1 p
    apply Lp.ext
    exact (P102.U4.domainLpRestrict_ae Ω _).trans (hright i (N i.succ u))
  refine ⟨Kall, F, ?_, ?_⟩
  · intro u
    have he : sobolevRestrict Ω (F u) = u := by
      simp only [F, add_apply, sum_apply, ContinuousLinearMap.comp_apply]
      change (sobolevRestrictCLM Ω) (E₀ u + ∑ i, E i (N i.succ u)) = u
      rw [map_add, map_sum]
      change sobolevRestrict Ω (E₀ u) + ∑ i, sobolevRestrict Ω (E i (N i.succ u)) = u
      rw [hrest₀]
      simp_rw [hrest]
      have hsum' := hsum u
      rw [Fin.sum_univ_succ] at hsum'
      exact hsum'
    have h := P102.U4.domainLpRestrict_ae Ω (sobolevUnderlying (F u))
    change sobolevUnderlying (sobolevRestrict Ω (F u)) =ᵐ[_] _ at h
    rw [he] at h
    exact h.symm
  · intro u
    have hzero₀ : ∀ᵐ x ∂volume, x ∉ K 0 → sobolevUnderlying (E₀ u) x = 0 :=
      lpZeroExtension_zero_off_compact (sobolevUnderlying (M 0 u)) (K 0) (hsupp 0 u)
    have hzeros := ae_all_iff.mpr (fun i => hsupport i (N i.succ u))
    have hadd := Lp.coeFn_add (sobolevUnderlying (E₀ u))
      (∑ i, sobolevUnderlying (E i (N i.succ u)))
    have hsumae := Lp.coeFn_finsetSum Finset.univ
      (fun i => sobolevUnderlying (E i (N i.succ u)))
    simp only [Opens.coe_top, Measure.restrict_univ] at hadd hsumae
    filter_upwards [hzero₀, hzeros, hadd, hsumae] with x hx₀ hxs ha hs hxout
    have hxK : x ∉ K 0 := fun hx => hxout (Or.inl hx)
    have hxouts (i : Fin n) : x ∉ Kout i := fun hx =>
      hxout (Or.inr (mem_iUnion.mpr ⟨i, hx⟩))
    have heval : sobolevUnderlying (F u) =
        sobolevUnderlying (E₀ u) + ∑ i, sobolevUnderlying (E i (N i.succ u)) := by
      change (sobolevUnderlyingCLM ⊤ 1 p) (F u) = _
      simp only [F, add_apply, sum_apply,
        ContinuousLinearMap.comp_apply, map_add, map_sum]
      rfl
    rw [heval]
    change (sobolevUnderlying (E₀ u) + ∑ i, sobolevUnderlying (E i (N i.succ u))) x = 0
    rw [ha]
    simp only [Pi.add_apply]
    rw [hs, hx₀ hxK]
    simp only [Finset.sum_apply]
    simp_rw [fun i => hxs i (hxouts i)]
    simp

/-- Restriction of whole-space smooth approximants gives genuine ambient
smooth density once the bulk extension has been constructed. -/
theorem ambient_smooth_density_of_bulkExtension (hBulk : Expected.BulkExtension) :
    P102.Sobolev.Extension.Expected.Density := by
  intro m e Ω hΩ 𝕜 _ p _ hp u
  obtain ⟨K, E, hrest, _⟩ := hBulk m e Ω hΩ 𝕜 p hp
  obtain ⟨φ, v, hrep, ht, _⟩ := wholeSpace_density 1 p hp (E u)
  have hback : sobolevRestrict Ω (E u) = u := by
    apply sobolevUnderlying_injective Ω 1 p
    apply Lp.ext
    exact (P102.U4.domainLpRestrict_ae Ω _).trans (hrest u)
  refine ⟨φ, fun n => sobolevRestrict Ω (v n), ?_, ?_⟩
  · intro n α
    exact (P102.U4.domainLpRestrict_ae Ω (sobolevDerivative (v n) α)).trans
      (ae_restrict_of_ae (hrep n α))
  · rw [← hback]
    exact ((sobolevRestrictCLM (𝕜 := 𝕜) Ω).continuous.tendsto (E u)).comp ht

lemma restrict_mem_sobolevZero_of_supported_left_interval {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space 1)} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {a c b : ℝ} (hcb : c < b)
    (hΩ : linePoint '' Ioo a b ⊆ (Ω : Set (Space 1)))
    (w : Sobolev 𝕜 (⊤ : Opens (Space 1)) 1 p)
    (hw : ∀ᵐ x ∂volume, x.ofLp 0 ∉ Icc a c → sobolevUnderlying w x = 0) :
    sobolevRestrict Ω w ∈ sobolevZeroSubmodule 𝕜 Ω 1 p := by
  have hline : Continuous linePoint := by
    change Continuous (fun t : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => t))
    fun_prop
  have hl0 : linePoint 0 = 0 := rfl
  have ht : Tendsto (fun δ : ℝ => sobolevRestrict Ω (translateWholeSobolev (linePoint δ) w))
      (𝓝[>] 0) (𝓝 (sobolevRestrict Ω w)) := by
    have hc := ((sobolevRestrictCLM (𝕜 := 𝕜) Ω).continuous.comp
      ((continuous_translateWholeSobolev hp w).comp hline)).tendsto 0
    change Tendsto (fun δ : ℝ => sobolevRestrict Ω (translateWholeSobolev (linePoint δ) w))
      (𝓝 0) (𝓝 (sobolevRestrict Ω (translateWholeSobolev (linePoint 0) w))) at hc
    rw [hl0, translateWholeSobolev_zero] at hc
    exact hc.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  apply (smoothSobolevSubmodule 𝕜 Ω 1 p).isClosed_topologicalClosure.mem_of_tendsto ht
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < b - c :=
    (eventually_lt_nhds (sub_pos.mpr hcb)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with δ hδ hδsmall
  change 0 < δ at hδ
  let K : Compacts (Space 1) :=
    ⟨linePoint '' Icc (a + δ) (c + δ), isCompact_Icc.image hline⟩
  apply mem_sobolevZero_of_compactSupport hp
  refine ⟨K, ?_, ?_⟩
  · rintro x ⟨t, ht, rfl⟩
    apply hΩ
    exact ⟨t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
  · have hwa := (measurePreserving_sub_right volume (linePoint δ)).quasiMeasurePreserving.ae hw
    have hrep := P102.U4.domainLpRestrict_ae Ω
      (sobolevUnderlying (translateWholeSobolev (linePoint δ) w))
    filter_upwards [hrep, ae_restrict_of_ae hwa,
      ae_restrict_of_ae (translateWholeLp_ae (linePoint δ) (sobolevUnderlying w))]
      with x hx hvan htr hxK
    change domainLpRestrict Ω (sobolevUnderlying (translateWholeSobolev (linePoint δ) w)) x = 0
    rw [hx]
    change translateWholeLp (linePoint δ) (sobolevUnderlying w) x = 0
    rw [htr]
    apply hvan
    intro hxsub
    apply hxK
    refine ⟨x.ofLp 0, ?_, ?_⟩
    · change x.ofLp 0 - δ ∈ Icc a c at hxsub
      exact ⟨by linarith [hxsub.1], by linarith [hxsub.2]⟩
    · apply WithLp.ofLp_injective 2
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rfl

lemma restrict_mem_sobolevZero_of_supported_right_interval {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space 1)} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {a c b : ℝ} (hac : a < c)
    (hΩ : linePoint '' Ioo a b ⊆ (Ω : Set (Space 1)))
    (w : Sobolev 𝕜 (⊤ : Opens (Space 1)) 1 p)
    (hw : ∀ᵐ x ∂volume, x.ofLp 0 ∉ Icc c b → sobolevUnderlying w x = 0) :
    sobolevRestrict Ω w ∈ sobolevZeroSubmodule 𝕜 Ω 1 p := by
  have hline : Continuous (fun δ : ℝ => linePoint (-δ)) := by
    change Continuous (fun t : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => -t))
    fun_prop
  have hl0 : linePoint (-(0 : ℝ)) = 0 := by rw [neg_zero]; rfl
  have ht : Tendsto (fun δ : ℝ => sobolevRestrict Ω (translateWholeSobolev (linePoint (-δ)) w))
      (𝓝[>] 0) (𝓝 (sobolevRestrict Ω w)) := by
    have hc := ((sobolevRestrictCLM (𝕜 := 𝕜) Ω).continuous.comp
      ((continuous_translateWholeSobolev hp w).comp hline)).tendsto 0
    change Tendsto (fun δ : ℝ => sobolevRestrict Ω (translateWholeSobolev (linePoint (-δ)) w))
      (𝓝 0) (𝓝 (sobolevRestrict Ω (translateWholeSobolev (linePoint (-0)) w))) at hc
    rw [hl0, translateWholeSobolev_zero] at hc
    exact hc.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  apply (smoothSobolevSubmodule 𝕜 Ω 1 p).isClosed_topologicalClosure.mem_of_tendsto ht
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < c - a :=
    (eventually_lt_nhds (sub_pos.mpr hac)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with δ hδ hδsmall
  change 0 < δ at hδ
  let K : Compacts (Space 1) :=
    ⟨linePoint '' Icc (c - δ) (b - δ), isCompact_Icc.image (by
      change Continuous (fun t : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => t)); fun_prop)⟩
  apply mem_sobolevZero_of_compactSupport hp
  refine ⟨K, ?_, ?_⟩
  · rintro x ⟨t, ht, rfl⟩
    apply hΩ
    exact ⟨t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
  · have hwa := (measurePreserving_sub_right volume (linePoint (-δ))).quasiMeasurePreserving.ae hw
    have hrep := P102.U4.domainLpRestrict_ae Ω
      (sobolevUnderlying (translateWholeSobolev (linePoint (-δ)) w))
    filter_upwards [hrep, ae_restrict_of_ae hwa,
      ae_restrict_of_ae (translateWholeLp_ae (linePoint (-δ)) (sobolevUnderlying w))]
      with x hx hvan htr hxK
    change domainLpRestrict Ω (sobolevUnderlying (translateWholeSobolev (linePoint (-δ)) w)) x = 0
    rw [hx]
    change translateWholeLp (linePoint (-δ)) (sobolevUnderlying w) x = 0
    rw [htr]
    apply hvan
    intro hxsub
    apply hxK
    refine ⟨x.ofLp 0, ?_, ?_⟩
    · change x.ofLp 0 - -δ ∈ Icc c b at hxsub
      exact ⟨by linarith [hxsub.1], by linarith [hxsub.2]⟩
    · apply WithLp.ofLp_injective 2
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rfl
/-- A whole-space Sobolev class supported on a closed component interval
restricts to W₀ on any open containing that interval's interior. Splitting
at the midpoint and translating the two halves inward supplies compact
interior approximants; physical smoothing is delegated to the proved lemma. -/
lemma restrict_mem_sobolevZero_of_supported_interval {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space 1)} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {a b : ℝ} (hab : a < b)
    (hΩ : linePoint '' Ioo a b ⊆ (Ω : Set (Space 1)))
    (w : Sobolev 𝕜 (⊤ : Opens (Space 1)) 1 p)
    (hw : ∀ᵐ x ∂volume, x.ofLp 0 ∉ Icc a b → sobolevUnderlying w x = 0) :
    sobolevRestrict Ω w ∈ sobolevZeroSubmodule 𝕜 Ω 1 p := by
  let l := (2 * a + b) / 3
  let r := (a + 2 * b) / 3
  have hal : a < l := by dsimp [l]; linarith
  have hlr : l < r := by dsimp [l, r]; linarith
  have hrb : r < b := by dsimp [r]; linarith
  have hline : Continuous linePoint := by
    change Continuous (fun t : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => t)); fun_prop
  have hcoord (x : Space 1) : linePoint (x.ofLp 0) = x := by
    apply WithLp.ofLp_injective 2
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl
  let K : Compacts (Space 1) := ⟨linePoint '' Icc a l, isCompact_Icc.image hline⟩
  let V : Opens (Space 1) := ⟨{x | x.ofLp 0 < r}, by
    exact isOpen_lt (by fun_prop) continuous_const⟩
  have hKV : (K : Set (Space 1)) ⊆ V := by
    rintro x ⟨t, ht, rfl⟩
    exact lt_of_le_of_lt ht.2 hlr
  obtain ⟨χ, _, N, hKN, _, hχone⟩ := cutoff 1 V K hKV
  let χw : WholeTests 1 ℝ := ⟨χ, χ.contDiff, χ.hasCompactSupport, subset_univ _⟩
  let χk : WholeTests 1 𝕜 := TestFunction.postcompCLM RCLike.ofRealCLM χw
  obtain ⟨wL, hwL⟩ := sobolev_testMul 1 p w χk
  have hLrep : (sobolevUnderlying wL : Space 1 → 𝕜) =ᵐ[volume]
      (fun x => χk x * sobolevUnderlying w x) := by
    rw [hwL]
    exact testMulLp_ae χk (sobolevUnderlying w)
  have hL : sobolevRestrict Ω wL ∈ sobolevZeroSubmodule 𝕜 Ω 1 p := by
    apply restrict_mem_sobolevZero_of_supported_left_interval hp hrb hΩ
    filter_upwards [hw, hLrep] with x hx hrep hnot
    rw [hrep]
    by_cases hxa : x.ofLp 0 < a
    · rw [hx (fun hxi => (not_lt_of_ge hxi.1) hxa), mul_zero]
    · have hxr : r < x.ofLp 0 := by
        by_contra h
        exact hnot ⟨not_lt.mp hxa, not_lt.mp h⟩
      have hzero : χ x = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hxs
        exact (not_lt_of_ge hxr.le) (χ.tsupport_subset hxs)
      change (χ x : 𝕜) * sobolevUnderlying w x = 0
      rw [hzero, RCLike.ofReal_zero, zero_mul]
  have hsub : sobolevUnderlying (w - wL) = sobolevUnderlying w - sobolevUnderlying wL :=
    (sobolevUnderlyingCLM (⊤ : Opens (Space 1)) 1 p).map_sub w wL
  have hRrep : (sobolevUnderlying (w - wL) : Space 1 → 𝕜) =ᵐ[volume]
      (fun x => sobolevUnderlying w x - χk x * sobolevUnderlying w x) := by
    rw [hsub]
    have he := Lp.coeFn_sub (sobolevUnderlying w) (sobolevUnderlying wL)
    simp only [Opens.coe_top, Measure.restrict_univ] at he
    filter_upwards [he, hLrep] with x hx hxl
    rw [hx, Pi.sub_apply, hxl]
  have hR : sobolevRestrict Ω (w - wL) ∈ sobolevZeroSubmodule 𝕜 Ω 1 p := by
    apply restrict_mem_sobolevZero_of_supported_right_interval hp hal hΩ
    filter_upwards [hw, hRrep] with x hx hrep hnot
    rw [hrep]
    by_cases hxb : b < x.ofLp 0
    · rw [hx (fun hxi => (not_lt_of_ge hxi.2) hxb), mul_zero, sub_self]
    · have hxl : x.ofLp 0 < l := by
        by_contra h
        exact hnot ⟨not_lt.mp h, not_lt.mp hxb⟩
      by_cases hxa : x.ofLp 0 < a
      · rw [hx (fun hxi => (not_lt_of_ge hxi.1) hxa), mul_zero, sub_self]
      · have hxK : x ∈ K := ⟨x.ofLp 0, ⟨not_lt.mp hxa, hxl.le⟩, hcoord x⟩
        have hone : χ x = 1 := hχone x (hKN hxK)
        change sobolevUnderlying w x - (χ x : 𝕜) * sobolevUnderlying w x = 0
        rw [hone, RCLike.ofReal_one, one_mul, sub_self]
  have he : sobolevRestrict Ω wL + sobolevRestrict Ω (w - wL) = sobolevRestrict Ω w := by
    change (sobolevRestrictCLM Ω) wL + (sobolevRestrictCLM Ω) (w - wL) =
      (sobolevRestrictCLM Ω) w
    rw [← map_add]
    congr 1
    abel
  rw [← he]
  exact (sobolevZeroSubmodule 𝕜 Ω 1 p).add_mem hL hR
lemma closed_component_intervals_disjoint {n : ℕ} {a b : Fin n → ℝ}
    (hab : ∀ i, a i < b i) (hinj : Function.Injective (Sum.elim a b))
    (hdis : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))) :
    Pairwise (fun i j => Disjoint (Icc (a i) (b i)) (Icc (a j) (b j))) := by
  intro i j hij
  have hd := Ioo_disjoint_Ioo.mp (hdis hij)
  have hba : b i ≠ a j := fun h => Sum.inr_ne_inl
    (hinj (show Sum.elim a b (Sum.inr i) = Sum.elim a b (Sum.inl j) from h))
  have hab' : b j ≠ a i := fun h => Sum.inr_ne_inl
    (hinj (show Sum.elim a b (Sum.inr j) = Sum.elim a b (Sum.inl i) from h))
  have hord : b i < a j ∨ b j < a i := by
    rcases le_total (a i) (a j) with h | h
    · rw [max_eq_right h] at hd
      rcases min_le_iff.mp hd with hi | hj
      · exact Or.inl (lt_of_le_of_ne hi hba)
      · exact False.elim ((hab j).not_ge hj)
    · rw [max_eq_left h] at hd
      rcases min_le_iff.mp hd with hi | hj
      · exact False.elim ((hab i).not_ge hi)
      · exact Or.inr (lt_of_le_of_ne hj hab')
  apply Set.disjoint_left.mpr
  intro t ht hj
  rcases hord with hord | hord
  · linarith [ht.2, hj.1]
  · linarith [hj.2, ht.1]

/-- On a finite union of disjoint intervals with distinct endpoints, a genuine
whole-space zero extension gives membership of the original smooth-test
closure. Each compact component is isolated by a smooth cutoff, then the
proved inward-translation argument supplies actual interior approximants. -/
lemma mem_sobolevZero_of_zeroExtension_finite_intervals {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space 1)} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {n : ℕ} {a b : Fin n → ℝ}
    (hab : ∀ i, a i < b i) (hinj : Function.Injective (Sum.elim a b))
    (hdis : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (hΩ : (Ω : Set (Space 1)) = ⋃ i, linePoint '' Ioo (a i) (b i))
    (u : Sobolev 𝕜 Ω 1 p) (hu : HasZeroExtension u) :
    u ∈ sobolevZeroSubmodule 𝕜 Ω 1 p := by
  classical
  obtain ⟨w, hw⟩ := hu
  have hline : Continuous linePoint := by
    change Continuous (fun t : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => t)); fun_prop
  have hcoord (x : Space 1) : linePoint (x.ofLp 0) = x := by
    apply WithLp.ofLp_injective 2
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl
  let I (i : Fin n) : Set (Space 1) := linePoint '' Icc (a i) (b i)
  let K (i : Fin n) : Compacts (Space 1) := ⟨I i, isCompact_Icc.image hline⟩
  have hclosed (i : Fin n) : IsClosed (I i) := (K i).isCompact.isClosed
  let V (i : Fin n) : Opens (Space 1) :=
    ⟨(⋃ j : {j : Fin n // j ≠ i}, I j)ᶜ,
      (isClosed_iUnion_of_finite (fun j : {j : Fin n // j ≠ i} => hclosed j)).isOpen_compl⟩
  have hKV (i : Fin n) : (K i : Set (Space 1)) ⊆ V i := by
    rintro x ⟨t, ht, rfl⟩ hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    obtain ⟨s, hs, hst⟩ := hj
    have hst' : s = t := linePoint_injective hst
    subst s
    exact Set.disjoint_left.mp (closed_component_intervals_disjoint hab hinj hdis j.property.symm) ht hs
  choose χ hχbound N hKN hNV hχone using (fun i => cutoff 1 (V i) (K i) (hKV i))
  let χw (i : Fin n) : WholeTests 1 ℝ :=
    ⟨χ i, (χ i).contDiff, (χ i).hasCompactSupport, subset_univ _⟩
  let χk (i : Fin n) : WholeTests 1 𝕜 := TestFunction.postcompCLM RCLike.ofRealCLM (χw i)
  choose wi hwi using (fun i => sobolev_testMul 1 p w (χk i))
  have hrep (i : Fin n) : (sobolevUnderlying (wi i) : Space 1 → 𝕜) =ᵐ[volume]
      (fun x => χ i x • sobolevUnderlying w x) := by
    rw [hwi i]
    exact (testMulLp_ae (χk i) (sobolevUnderlying w)).mono fun x hx => by
      change testMulLp (χk i) (sobolevUnderlying w) x =
        (χ i x : 𝕜) * sobolevUnderlying w x at hx
      simpa only [RCLike.real_smul_eq_coe_mul] using hx
  have hwrep : (sobolevUnderlying w : Space 1 → 𝕜) =ᵐ[volume]
      (Ω : Set (Space 1)).indicator (sobolevUnderlying u) := by
    rw [hw]
    exact lpZeroExtension_ae Ω p _
  have hχzero (i j : Fin n) (hji : j ≠ i) {x : Space 1} (hx : x ∈ I j) : χ i x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hxs
    have hxV := (χ i).tsupport_subset hxs
    exact hxV (mem_iUnion.mpr ⟨⟨j, hji⟩, hx⟩)
  have hmem (i : Fin n) : sobolevRestrict Ω (wi i) ∈ sobolevZeroSubmodule 𝕜 Ω 1 p := by
    apply restrict_mem_sobolevZero_of_supported_interval hp (hab i)
      (by rw [hΩ]; exact subset_iUnion (fun j => linePoint '' Ioo (a j) (b j)) i)
    filter_upwards [hrep i, hwrep] with x hx hxw hnot
    rw [hx]
    by_cases hxΩ : x ∈ (Ω : Set (Space 1))
    · rw [hΩ] at hxΩ
      obtain ⟨j, t, ht, rfl⟩ := mem_iUnion.mp hxΩ
      by_cases hji : j = i
      · subst j
        exact False.elim (hnot ⟨ht.1.le, ht.2.le⟩)
      · rw [hχzero i j hji ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩, zero_smul]
    · rw [hxw, indicator_of_notMem hxΩ, smul_zero]
  have hsumχ (x : Space 1) (hx : x ∈ (Ω : Set (Space 1))) : ∑ i, χ i x = 1 := by
    rw [hΩ] at hx
    obtain ⟨j, t, ht, rfl⟩ := mem_iUnion.mp hx
    rw [Finset.sum_eq_single j]
    · exact hχone j _ (hKN j ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩)
    · intro i _ hij
      exact hχzero i j hij.symm ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
    · simp
  have hsum : ∑ i, wi i = w := by
    apply sobolevUnderlying_injective (⊤ : Opens (Space 1)) 1 p
    change (sobolevUnderlyingCLM ⊤ 1 p) (∑ i, wi i) = _
    rw [map_sum]
    apply Lp.ext
    simp only [Opens.coe_top, Measure.restrict_univ]
    have hall := ae_all_iff.mpr hrep
    have he := Lp.coeFn_finsetSum Finset.univ (fun i => sobolevUnderlying (wi i))
    simp only [Opens.coe_top, Measure.restrict_univ] at he
    filter_upwards [he, hall, hwrep] with x hx hxi hxw
    change (∑ i, sobolevUnderlying (wi i)) x = _ at hx ⊢
    rw [hx]
    simp only [Finset.sum_apply]
    simp_rw [hxi]
    rw [← Finset.sum_smul]
    by_cases hxΩ : x ∈ (Ω : Set (Space 1))
    · rw [hsumχ x hxΩ, one_smul]
    · rw [hxw, indicator_of_notMem hxΩ, smul_zero]
  have hrest : sobolevRestrict Ω w = u := by
    apply sobolevUnderlying_injective Ω 1 p
    change domainLpRestrict Ω (sobolevUnderlying w) = _
    rw [hw, domainLpRestrict_zeroExtension]
  rw [← hrest, ← hsum]
  change (sobolevRestrictCLM Ω) (∑ i, wi i) ∈ _
  rw [map_sum]
  exact (sobolevZeroSubmodule 𝕜 Ω 1 p).sum_mem (fun i _ => hmem i)
/-- The genuine smooth-test kernel characterization in physical dimension
one, for all finite unions of component intervals and finite p≥1. -/
theorem kernel_oneDimension_conditional
    (hCutoff : Expected.CutoffCompatibility)
    (hEndpoint : Expected.EndpointIdentification)
    (hTrace : Expected.TraceExists)
    (hUnique : Expected.TraceUniqueness) :
    ∀ (e : Ambient 0 ≃ₗᵢ[ℝ] Space 1) (Ω : Opens (Space 1)),
      IsLipschitzOpen (geometricOpen e Ω : Set (Ambient 0)) →
      ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ →
      ∀ T : Sobolev 𝕜 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p, IsTrace T →
        T.ker = sobolevZeroSubmodule 𝕜 Ω 1 p := by
  intro e Ω hΩ 𝕜 _ p _ hp T hT
  obtain ⟨_, n, a, b, hab, hinj, hdis, hopen, _⟩ :=
    hEndpoint e Ω hΩ 𝕜 p hp T hT
  apply le_antisymm
  · intro u hu
    have he := (zero_extension_criterion_oneDimension_conditional
      hCutoff hEndpoint hTrace hUnique e Ω hΩ 𝕜 p hp T hT u).mp hu
    exact mem_sobolevZero_of_zeroExtension_finite_intervals hp hab hinj hdis hopen u he
  · exact sobolevZero_le_trace_ker T hT

section FlatBoundary

/-- The canonical omitted-last coordinate base, with its product volume. -/
def boundaryBaseCoordinates (m : ℕ) : Space m ≃ᵐ P102.Trace.Boundary m :=
  (MeasurableEquiv.toLp 2 (Fin m → ℝ)).symm.trans (P102.Trace.boundaryCoordinates m)

theorem boundaryBaseCoordinates_measurePreserving (m : ℕ) :
    MeasurePreserving (boundaryBaseCoordinates m) volume volume :=
  (P102.Trace.boundaryCoordinates_measurePreserving m).comp (PiLp.volume_preserving_ofLp (Fin m))

theorem boundaryBaseCoordinates_symm_measurePreserving (m : ℕ) :
    MeasurePreserving (boundaryBaseCoordinates m).symm volume volume :=
  (boundaryBaseCoordinates_measurePreserving m).symm (boundaryBaseCoordinates m)

@[simp] theorem point_boundaryBaseCoordinates (m : ℕ) (x : Space m) (t : ℝ) :
    P102.Trace.point m (boundaryBaseCoordinates m x) t =
      flatCoordinates m (WithLp.toLp 2 (x,t)) := by
  apply PiLp.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [P102.Trace.point, ACL.line, ExpandedFA.Sobolev.Lines.coordinateLine, flatCoordinates]
  · simp [P102.Trace.point, ACL.line, ExpandedFA.Sobolev.Lines.coordinateLine,
      flatCoordinates, boundaryBaseCoordinates, P102.Trace.boundaryCoordinates,
      MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
      finSuccAboveEquiv_symm_apply_last]

variable (m : ℕ) (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]


theorem boundaryBaseCoordinates_measurePreserving_top (m : ℕ) :
    MeasurePreserving (boundaryBaseCoordinates m)
      (volume.restrict ((⊤ : Opens (Space m)) : Set (Space m))) volume := by
  simpa only [Opens.coe_top, Measure.restrict_univ] using boundaryBaseCoordinates_measurePreserving m

theorem boundaryBaseCoordinates_symm_measurePreserving_top (m : ℕ) :
    MeasurePreserving (boundaryBaseCoordinates m).symm volume
      (volume.restrict ((⊤ : Opens (Space m)) : Set (Space m))) := by
  simpa only [Opens.coe_top, Measure.restrict_univ] using boundaryBaseCoordinates_symm_measurePreserving m

/-- The flat-boundary Lp class in the Euclidean coordinates of the chart base. -/
def flatBoundaryToBaseLI : P102.Trace.BoundaryLp m 𝕜 p →ₗᵢ[𝕜]
    DomainLp 𝕜 (⊤ : Opens (Space m)) p :=
  Lp.compMeasurePreservingₗᵢ 𝕜 (boundaryBaseCoordinates m)
    (boundaryBaseCoordinates_measurePreserving_top m)

theorem flatBoundaryToBaseLI_ae (u : P102.Trace.BoundaryLp m 𝕜 p) :
    flatBoundaryToBaseLI m 𝕜 p u =ᵐ[volume] (u ∘ boundaryBaseCoordinates m) := by
  change Lp.compMeasurePreserving (boundaryBaseCoordinates m)
    (boundaryBaseCoordinates_measurePreserving_top m) u =ᵐ[volume] _
  have h := Lp.coeFn_compMeasurePreserving u (boundaryBaseCoordinates_measurePreserving_top m)
  simpa only [Opens.coe_top, Measure.restrict_univ] using h

/-- The inverse reindexing, also an isometry. -/
def baseToFlatBoundaryLI : DomainLp 𝕜 (⊤ : Opens (Space m)) p →ₗᵢ[𝕜]
    P102.Trace.BoundaryLp m 𝕜 p :=
  Lp.compMeasurePreservingₗᵢ 𝕜 (boundaryBaseCoordinates m).symm
    (boundaryBaseCoordinates_symm_measurePreserving_top m)

theorem baseToFlatBoundaryLI_ae (u : DomainLp 𝕜 (⊤ : Opens (Space m)) p) :
    baseToFlatBoundaryLI m 𝕜 p u =ᵐ[volume] (u ∘ (boundaryBaseCoordinates m).symm) :=
  Lp.coeFn_compMeasurePreserving u (boundaryBaseCoordinates_symm_measurePreserving_top m)


@[simp] theorem baseToFlatBoundaryLI_flatBoundaryToBaseLI (u : P102.Trace.BoundaryLp m 𝕜 p) :
    baseToFlatBoundaryLI m 𝕜 p (flatBoundaryToBaseLI m 𝕜 p u) = u := by
  change Lp.compMeasurePreserving (boundaryBaseCoordinates m).symm
    (boundaryBaseCoordinates_symm_measurePreserving_top m)
      (Lp.compMeasurePreserving (boundaryBaseCoordinates m)
        (boundaryBaseCoordinates_measurePreserving_top m) u) = u
  rw [← Lp.compMeasurePreserving_comp_apply]
  have he : (boundaryBaseCoordinates m) ∘ (boundaryBaseCoordinates m).symm = id := by
    funext x
    exact (boundaryBaseCoordinates m).apply_symm_apply x
  simp only [he, Lp.compMeasurePreserving_id_apply]

@[simp] theorem flatBoundaryToBaseLI_baseToFlatBoundaryLI
    (u : DomainLp 𝕜 (⊤ : Opens (Space m)) p) :
    flatBoundaryToBaseLI m 𝕜 p (baseToFlatBoundaryLI m 𝕜 p u) = u := by
  change Lp.compMeasurePreserving (boundaryBaseCoordinates m)
    (boundaryBaseCoordinates_measurePreserving_top m)
      (Lp.compMeasurePreserving (boundaryBaseCoordinates m).symm
        (boundaryBaseCoordinates_symm_measurePreserving_top m) u) = u
  rw [← Lp.compMeasurePreserving_comp_apply]
  have he : (boundaryBaseCoordinates m).symm ∘ (boundaryBaseCoordinates m) = id := by
    funext x
    exact (boundaryBaseCoordinates m).symm_apply_apply x
  simp only [he, Lp.compMeasurePreserving_id_apply]

/-- The flat boundary and the Euclidean chart base carry identical Lp geometry. -/
def flatBoundaryBaseLE : P102.Trace.BoundaryLp m 𝕜 p ≃ₗᵢ[𝕜]
    DomainLp 𝕜 (⊤ : Opens (Space m)) p where
  toLinearEquiv :=
    { toFun := flatBoundaryToBaseLI m 𝕜 p
      invFun := baseToFlatBoundaryLI m 𝕜 p
      left_inv := baseToFlatBoundaryLI_flatBoundaryToBaseLI m 𝕜 p
      right_inv := flatBoundaryToBaseLI_baseToFlatBoundaryLI m 𝕜 p
      map_add' := (flatBoundaryToBaseLI m 𝕜 p).map_add
      map_smul' := (flatBoundaryToBaseLI m 𝕜 p).map_smul }
  norm_map' := (flatBoundaryToBaseLI m 𝕜 p).norm_map

end FlatBoundary

/-- The recalled bulk extension, now constructed from actual chart maps,
reflection and gluing. All four frozen premises retain their full types. -/
theorem bulk_extension_conditional
    (hCutoff : Expected.CutoffCompatibility)
    (_hEndpoint : Expected.EndpointIdentification)
    (hTrace : Expected.TraceExists)
    (_hUnique : Expected.TraceUniqueness) : Expected.BulkExtension := by
  apply bulkExtension_of_supported_chart_extensions hCutoff hTrace
  intro m e Ω C 𝕜 _ p _ _ K hK
  exact localBulkExtension_exists (𝕜 := 𝕜) e Ω C p K hK

/-- Ambient smooth restrictions are dense in the full Sobolev norm, using
the actual constructed bulk extension rather than a provisional certificate. -/
theorem ambient_smooth_density_conditional
    (hCutoff : Expected.CutoffCompatibility)
    (hEndpoint : Expected.EndpointIdentification)
    (hTrace : Expected.TraceExists)
    (hUnique : Expected.TraceUniqueness) : P102.Sobolev.Extension.Expected.Density :=
  ambient_smooth_density_of_bulkExtension
    (bulk_extension_conditional hCutoff hEndpoint hTrace hUnique)


theorem flattenHalfSupportedCLM_represents
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (K : Compacts (Space (m + 1))) (hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C)
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K)
    (f : Space (m + 1) → 𝕜) (hf : tsupport f ⊆ (K : Set (Space (m + 1))))
    (hu : sobolevUnderlying u.val =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] f) :
    sobolevUnderlying (flattenHalfSupportedCLM e Ω C p K hK u) =ᵐ[
      volume.restrict (halfSpace m : Set (Space (m + 1)))]
      (f ∘ (fullChartMap e (flatCoordinates m) C).toFun) := by
  have hphysical : sobolevUnderlying u.val =ᵐ[
      volume.restrict (physicalChartOpen e Ω C : Set (Space (m + 1)))] f :=
    hu.filter_mono (ae_mono (volume.restrict_mono_set (fun _ hx => hx.1)))
  have hflat := (ae_restrict_iff'
    (flatChartOpen (flatCoordinates m) C.center C.radius C.height).isOpen.measurableSet).mp
      ((flattenCylinderSupportedCLM_underlying_ae e (flatCoordinates m) Ω C p K u).trans
        ((physicalChartMap e (flatCoordinates m) Ω C).ae_comp hphysical))
  filter_upwards [flattenHalfSupportedCLM_underlying_ae e Ω C p K hK u,
      ae_restrict_of_ae hflat, ae_restrict_mem (halfSpace m).isOpen.measurableSet]
      with x hx hr hxH
  rw [hx]
  by_cases hxF : x ∈ flatChartOpen (flatCoordinates m) C.center C.radius C.height
  · rw [indicator_of_mem hxF]
    exact hr hxF
  · rw [indicator_of_notMem hxF]
    symm
    apply image_eq_zero_of_notMem_tsupport
    intro hxS
    have hxQ := fullChartMap_tsupport_comp_subset e (flatCoordinates m) C f K hK hf hxS
    have hxW := fullChartPullbackCompact_subset e (flatCoordinates m) C K hK hxQ
    have hxP : x ∈ flatPositiveOpen (flatCoordinates m) := by
      rwa [flatPositiveOpen_flatCoordinates]
    exact hxF (flatPositive_inter_full_subset_flat (flatCoordinates m) C.center C.radius C.height ⟨hxP,hxW⟩)


theorem chartBoundaryParam_notMem_full_of_notMem_base
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    {x : Space m} (hx : x ∉ chartBaseOpen C) :
    chartBoundaryParam e Ω C x ∉ fullPhysicalChartOpen e C := by
  rintro ⟨z,⟨s,⟨w,hw,rfl⟩,rfl⟩,he⟩
  have hEq := C.frame.injective (e.injective he)
  have hhor := congrArg (fun v : Ambient m => v.ofLp.1) hEq
  simp only [shear, graph, WithLp.ofLp_toLp] at hhor
  exact hx (hhor ▸ hw.1)

theorem chartBoundaryParam_zero_off_base
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (K : Compacts (Space (m + 1))) (hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C)
    (f : Space (m + 1) → 𝕜) (hf : tsupport f ⊆ (K : Set (Space (m + 1))))
    {x : Space m} (hx : x ∉ chartBaseOpen C) : f (chartBoundaryParam e Ω C x) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hs
  exact chartBoundaryParam_notMem_full_of_notMem_base e Ω C hx (hK (hf hs))

theorem flattenHalf_trace_of_smooth_supported
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (K : Compacts (Space (m + 1))) (hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C)
    (T : Sobolev 𝕜 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (Tflat : HalfSobolev m 𝕜 p →L[𝕜] P102.Trace.BoundaryLp m 𝕜 p)
    (hflat : ∀ (v : HalfSobolev m 𝕜 p) (F : Space (m + 1) → 𝕜),
      ContinuousOn F {x | 0 ≤ x (Fin.last m)} →
      sobolevUnderlying v =ᵐ[volume.restrict (halfSpace m : Set (Space (m + 1)))] F →
      (fun z => Tflat v z) =ᵐ[volume] (fun z => F (point m z 0)))
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K)
    (f : Space (m + 1) → 𝕜) (hc : ContDiff ℝ ∞ f)
    (hf : tsupport f ⊆ (K : Set (Space (m + 1))))
    (hu : sobolevUnderlying u.val =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] f) :
    flatBoundaryToBaseLI m 𝕜 p (Tflat (flattenHalfSupportedCLM e Ω C p K hK u)) =
      chartBoundaryLpPullbackFull e Ω C 𝕜 p (T u.val) := by
  let F := f ∘ (fullChartMap e (flatCoordinates m) C).toFun
  have hFc : Continuous F := fullChartMap_continuous_comp e (flatCoordinates m) C f hc.continuous K hK hf
  have hFr := flattenHalfSupportedCLM_represents e Ω C p K hK u f hf hu
  have hTf := hflat (flattenHalfSupportedCLM e Ω C p K hK u) F hFc.continuousOn hFr
  have hTfbase := (boundaryBaseCoordinates_measurePreserving m).quasiMeasurePreserving.ae hTf
  have hTp := (ae_restrict_iff' (chartBaseOpen C).isOpen.measurableSet).mp
    (chartBoundaryParam_ae_comp e Ω C (hT u.val f hc hu))
  apply Lp.ext
  simp only [Opens.coe_top, Measure.restrict_univ]
  filter_upwards [flatBoundaryToBaseLI_ae m 𝕜 p (Tflat (flattenHalfSupportedCLM e Ω C p K hK u)),
    hTfbase, chartBoundaryLpPullbackFull_ae e Ω C 𝕜 p (T u.val), hTp] with x hLI hTF hPB hTP
  rw [hLI, Function.comp_apply, hTF, hPB]
  have heval : F (point m (boundaryBaseCoordinates m x) 0) = f (chartBoundaryParam e Ω C x) := by
    simp only [F, Function.comp_apply, point_boundaryBaseCoordinates, fullChartMap,
      LinearIsometryEquiv.symm_apply_apply, shear, WithLp.ofLp_toLp, add_zero,
      chartBoundaryParam, graph]
  rw [heval]
  by_cases hxB : x ∈ chartBaseOpen C
  · rw [indicator_of_mem hxB]
    exact (hTP hxB).symm
  · rw [indicator_of_notMem hxB]
    exact chartBoundaryParam_zero_off_base e Ω C K hK f hf hxB


/-- Codomain restriction records the essential compact support produced by
an actual smooth physical cutoff. -/
def cutoffSupportedCLM
    (Ω : Opens (Space (m + 1))) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (K : Compacts (Space (m + 1))) (χ : Space (m + 1) → ℝ)
    (hχK : tsupport χ ⊆ (K : Set (Space (m + 1))))
    (M : Sobolev 𝕜 Ω 1 p →L[𝕜] Sobolev 𝕜 Ω 1 p)
    (hM : ∀ u, sobolevUnderlying (M u) =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))]
      (fun x => χ x • sobolevUnderlying u x)) :
    Sobolev 𝕜 Ω 1 p →L[𝕜] sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K :=
  M.codRestrict _ (fun u => by
    filter_upwards [hM u] with x hx hxK
    rw [hx, image_eq_zero_of_notMem_tsupport (fun hxχ => hxK (hχK hxχ)), zero_smul])

/-- The flat trace of a localized physical Sobolev class is the pullback
of its same physical trace. Density is an explicit full upstream statement. -/
theorem local_trace_identification_of_density
    (hDensity : P102.Sobolev.Extension.Expected.Density)
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1)))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (K : Compacts (Space (m + 1))) (hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C)
    (χ : Space (m + 1) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχK : tsupport χ ⊆ (K : Set (Space (m + 1))))
    (M : Sobolev 𝕜 Ω 1 p →L[𝕜] Sobolev 𝕜 Ω 1 p)
    (hM : ∀ u, sobolevUnderlying (M u) =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))]
      (fun x => χ x • sobolevUnderlying u x))
    (T : Sobolev 𝕜 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (Tflat : HalfSobolev m 𝕜 p →L[𝕜] P102.Trace.BoundaryLp m 𝕜 p)
    (hflat : ∀ (v : HalfSobolev m 𝕜 p) (F : Space (m + 1) → 𝕜),
      ContinuousOn F {x | 0 ≤ x (Fin.last m)} →
      sobolevUnderlying v =ᵐ[volume.restrict (halfSpace m : Set (Space (m + 1)))] F →
      (fun z => Tflat v z) =ᵐ[volume] (fun z => F (point m z 0))) :
    (((flatBoundaryToBaseLI m 𝕜 p).toContinuousLinearMap.comp Tflat).comp
      ((flattenHalfSupportedCLM e Ω C p K hK).comp
        (cutoffSupportedCLM Ω p K χ hχK M hM))) =
      (chartBoundaryLpPullbackFull e Ω C 𝕜 p).comp (T.comp M) := by
  let N := cutoffSupportedCLM Ω p K χ hχK M hM
  let A := ((flatBoundaryToBaseLI m 𝕜 p).toContinuousLinearMap.comp Tflat).comp
    ((flattenHalfSupportedCLM e Ω C p K hK).comp N)
  let B := (chartBoundaryLpPullbackFull e Ω C 𝕜 p).comp (T.comp M)
  change A = B
  apply ContinuousLinearMap.ext
  intro u
  obtain ⟨φ,v,hv,ht⟩ := hDensity m e Ω hΩ 𝕜 p hp u
  have heq (n : ℕ) : A (v n) = B (v n) := by
    change flatBoundaryToBaseLI m 𝕜 p
      (Tflat (flattenHalfSupportedCLM e Ω C p K hK (N (v n)))) =
      chartBoundaryLpPullbackFull e Ω C 𝕜 p (T (M (v n)))
    have hφ : sobolevUnderlying (v n) =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] φ n := by
      have hz := hv n (zeroSobolevIndex (m + 1) 1)
      change (sobolevUnderlying (v n) : Space (m + 1) → 𝕜) =ᵐ[_] multiPartial (φ n) 0 at hz
      simpa only [multiPartial, Multiset.sort_zero, partialWord] using hz
    apply flattenHalf_trace_of_smooth_supported e Ω C p K hK T hT Tflat hflat (N (v n))
      (fun x => χ x • φ n x) (hχ.smul (φ n).contDiff)
      ((tsupport_smul_subset_left χ (φ n)).trans hχK)
    change sobolevUnderlying (M (v n)) =ᵐ[_] _
    filter_upwards [hM (v n), hφ] with x hx hy
    rw [hx,hy]
  have hAlim := (A.continuous.tendsto u).comp ht
  have hBlim := (B.continuous.tendsto u).comp ht
  have heqfun : A ∘ v = B ∘ v := funext heq
  rw [heqfun] at hAlim
  exact tendsto_nhds_unique hAlim hBlim

section FlattenZeroExtension

theorem flatChartOpen_subset_fullFlatChart
    (q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (c : Space m) (r a : ℝ) (ha : 0 < a) :
    (flatChartOpen q c r a : Set (Space (m + 1))) ⊆ fullFlatChartOpen q c r a := by
  rintro x ⟨z, hz, rfl⟩
  exact ⟨z, ⟨hz.1, lt_trans (neg_lt_zero.mpr ha) hz.2.1, hz.2.2⟩, rfl⟩

theorem fullChart_indicator_side
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (f : Space (m + 1) → 𝕜) :
    (fullFlatChartOpen q C.center C.radius C.height : Set (Space (m + 1))).indicator
      (fun x => (Ω : Set (Space (m + 1))).indicator f ((fullChartMap e q C).toFun x)) =
      (flatChartOpen q C.center C.radius C.height : Set (Space (m + 1))).indicator
        (f ∘ (fullChartMap e q C).toFun) := by
  funext x
  let g := fullChartMap e q C
  let gP := physicalChartMap e q Ω C
  by_cases hxF : x ∈ flatChartOpen q C.center C.radius C.height
  · have hxB := flatChartOpen_subset_fullFlatChart q C.center C.radius C.height C.height_pos hxF
    have hxΩ : g.toFun x ∈ Ω := (gP.mapsTo hxF).1
    rw [indicator_of_mem hxB, indicator_of_mem hxF]
    exact indicator_of_mem hxΩ f
  · by_cases hxB : x ∈ fullFlatChartOpen q C.center C.radius C.height
    · have hxΩ : g.toFun x ∉ Ω := by
        intro hΩ
        have hxP : g.toFun x ∈ physicalChartOpen e Ω C := ⟨hΩ, g.mapsTo hxB⟩
        have hinv := gP.inv_mapsTo hxP
        have heq : gP.invFun (g.toFun x) = x := fullChartMap_left_inv_global e q C x
        exact hxF (heq ▸ hinv)
      rw [indicator_of_mem hxB, indicator_of_notMem hxF]
      exact indicator_of_notMem hxΩ f
    · simp only [indicator_of_notMem hxB, indicator_of_notMem hxF]

variable (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
  (Ω : Opens (Space (m + 1)))
  (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
  (p : ℝ≥0∞) [Fact (1 ≤ p)]
  (K : Compacts (Space (m + 1))) (hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C)

theorem flattenHalfSupportedCLM_hasFlatZeroExtension
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K)
    (hu : HasZeroExtension u.val) :
    HasFlatZeroExtension (flattenHalfSupportedCLM e Ω C p K hK u) := by
  obtain ⟨w, hw⟩ := hu
  let q := flatCoordinates m
  let g := fullChartMap e q C
  let A := fullPhysicalChartOpen e C
  let B := fullFlatChartOpen q C.center C.radius C.height
  let F := flatChartOpen q C.center C.radius C.height
  let Kflat := fullChartPullbackCompact e q C K hK
  let wA := sobolevRestrict A w
  let v := g.sobolevPullback meyersSerrin_smoothDensity (Nat.succ_pos m) 𝕜 p wA
  have hwraw : sobolevUnderlying w =ᵐ[volume]
      (Ω : Set (Space (m + 1))).indicator (sobolevUnderlying u.val) := by
    rw [hw]
    exact lpZeroExtension_ae Ω p _
  have hvraw : sobolevUnderlying v =ᵐ[volume.restrict (B : Set (Space (m + 1)))]
      (fun x => (Ω : Set (Space (m + 1))).indicator (sobolevUnderlying u.val) (g.toFun x)) := by
    change sobolevUnderlying (g.sobolevPullback meyersSerrin_smoothDensity
      (Nat.succ_pos m) 𝕜 p wA) =ᵐ[_] _
    rw [g.sobolevPullback_underlying]
    filter_upwards [g.lpPullback_ae 𝕜 p (sobolevUnderlying wA),
      g.ae_comp (P102.U4.domainLpRestrict_ae A (sobolevUnderlying w)),
      g.ae_comp (ae_restrict_of_ae hwraw)] with x hx ha hw
    exact hx.trans (ha.trans hw)
  have hwvan : ∀ᵐ x ∂volume, x ∉ K → sobolevUnderlying w x = 0 := by
    rw [hw]
    exact lpZeroExtension_zero_off_compact (sobolevUnderlying u.val) K u.property
  have hvvan : ∀ᵐ x ∂volume.restrict (B : Set (Space (m + 1))),
      x ∉ Kflat → sobolevUnderlying v x = 0 := by
    have hvw : sobolevUnderlying v =ᵐ[volume.restrict (B : Set (Space (m + 1)))]
        (sobolevUnderlying w ∘ g.toFun) := by
      change sobolevUnderlying (g.sobolevPullback meyersSerrin_smoothDensity
        (Nat.succ_pos m) 𝕜 p wA) =ᵐ[_] _
      rw [g.sobolevPullback_underlying]
      exact (g.lpPullback_ae 𝕜 p _).trans (g.ae_comp (P102.U4.domainLpRestrict_ae A (sobolevUnderlying w)))
    filter_upwards [hvw, g.ae_comp (ae_restrict_of_ae hwvan),
      ae_restrict_mem B.isOpen.measurableSet] with x hx hz hxB hxK
    rw [hx]
    apply hz
    intro hxmem
    exact hxK ⟨g.toFun x, hxmem, g.left_inv x hxB⟩
  let vS : sobolevSupportedSubmodule (k := 1) 𝕜 B p Kflat := ⟨v, hvvan⟩
  let z := artificialBoundaryTransferCLM B ⊤ B p Kflat
    (fullChartPullbackCompact_subset e q C K hK) (fun _ hx => hx.2) vS
  have hzraw : sobolevUnderlying z =ᵐ[volume]
      (B : Set (Space (m + 1))).indicator (sobolevUnderlying v) := by
    have hz := artificialBoundaryTransferCLM_underlying_ae B ⊤ B p Kflat
      (fullChartPullbackCompact_subset e q C K hK) (fun _ hx => hx.2) vS
    simpa only [Opens.coe_top, Measure.restrict_univ] using hz
  have hvind := (ae_eq_restrict_iff_indicator_ae_eq B.isOpen.measurableSet).mp hvraw
  have hzF : sobolevUnderlying z =ᵐ[volume]
      (F : Set (Space (m + 1))).indicator (sobolevUnderlying u.val ∘ g.toFun) := by
    exact (hzraw.trans hvind).trans (Filter.Eventually.of_forall
      (fun x => congrFun (fullChart_indicator_side e q Ω C (sobolevUnderlying u.val)) x))
  have hh := (ae_eq_restrict_iff_indicator_ae_eq
      (halfSpace m).isOpen.measurableSet).mp
    (flattenHalfSupportedCLM_underlying_ae e Ω C p K hK u)
  have hc := (ae_eq_restrict_iff_indicator_ae_eq F.isOpen.measurableSet).mp
    (flattenCylinderSupportedCLM_underlying_ae e q Ω C p K u)
  have hFleH : (F : Set (Space (m + 1))) ⊆ halfSpace m := by
    rw [← flatPositiveOpen_flatCoordinates m]
    exact flatChartOpen_le_flatPositive q C.center C.radius C.height
  have hnest (f : Space (m + 1) → 𝕜) :
      (halfSpace m : Set (Space (m + 1))).indicator ((F : Set (Space (m + 1))).indicator f) =
        (F : Set (Space (m + 1))).indicator f := by
    funext x
    by_cases hxF : x ∈ F
    · simp only [indicator_of_mem hxF, indicator_of_mem (hFleH hxF)]
    · by_cases hxH : x ∈ halfSpace m <;> simp [hxF, hxH]
  have hhalfraw : (halfSpace m : Set (Space (m + 1))).indicator
      (sobolevUnderlying (flattenHalfSupportedCLM e Ω C p K hK u)) =ᵐ[volume]
      (F : Set (Space (m + 1))).indicator (sobolevUnderlying u.val ∘ g.toFun) := by
    rw [hnest] at hh
    exact hh.trans hc
  refine ⟨z, Lp.ext ?_⟩
  simpa only [Opens.coe_top, Measure.restrict_univ] using
    hzF.trans ((flatZeroExtension_ae (sobolevUnderlying
      (flattenHalfSupportedCLM e Ω C p K hK u))).trans hhalfraw).symm

theorem flattenHalfSupportedCLM_zeroFlatTrace_of_zeroExtension
    (hm : 1 ≤ m) (hp : p ≠ ⊤)
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K)
    (hu : HasZeroExtension u.val) :
    HasZeroFlatTrace (flattenHalfSupportedCLM e Ω C p K hK u) :=
  flat_zero_extension_implies_zero_trace m hm 𝕜 p hp _
    (flattenHalfSupportedCLM_hasFlatZeroExtension e Ω C p K hK u hu)

theorem flattenHalfSupportedCLM_mem_sobolevZero_of_zeroExtension
    (hp : p ≠ ⊤) (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K)
    (hu : HasZeroExtension u.val) :
    flattenHalfSupportedCLM e Ω C p K hK u ∈ sobolevZeroSubmodule 𝕜 (halfSpace m) 1 p :=
  (flatZeroExtension_iff_mem_sobolevZero hp _).mp
    (flattenHalfSupportedCLM_hasFlatZeroExtension e Ω C p K hK u hu)

end FlattenZeroExtension

set_option maxHeartbeats 1200000 in
/-- An actual compact smooth coefficient acts continuously on whole-space
Sobolev classes, derived from product existence and the closed graph theorem. -/
theorem exists_wholeSobolevCutoffCLM {d k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (χ : Space d → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ M : Sobolev 𝕜 (⊤ : Opens (Space d)) k p →L[𝕜]
        Sobolev 𝕜 (⊤ : Opens (Space d)) k p,
      ∀ u, sobolevUnderlying (M u) =ᵐ[volume]
        (fun x => χ x • sobolevUnderlying u x) := by
  classical
  let Ω : Opens (Space d) := ⊤
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hχ.continuous
  let B : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hb : ∀ᵐ x ∂volume.restrict (Ω : Set (Space d)), ‖χ x‖ ≤ B :=
    Filter.Eventually.of_forall fun x => (hC x).trans (le_max_left _ _)
  let A := realMultiplier (𝕜 := 𝕜) Ω p χ B hχ.continuous.aestronglyMeasurable hb
  let J := sobolevUnderlyingCLM (𝕜 := 𝕜) Ω k p
  have hinj : Function.Injective J := sobolevUnderlying_injective Ω k p
  let χw : WholeTests d ℝ := ⟨χ, hχ, hc, subset_univ _⟩
  let χk : WholeTests d 𝕜 := TestFunction.postcompCLM RCLike.ofRealCLM χw
  have hex (u : Sobolev 𝕜 Ω k p) : ∃ v : Sobolev 𝕜 Ω k p, J v = A (J u) := by
    obtain ⟨v, hv⟩ := sobolev_testMul k p u χk
    refine ⟨v, ?_⟩
    apply Lp.ext
    have hrep := testMulLp_ae χk (sobolevUnderlying u)
    rw [← hv] at hrep
    have hA := realMultiplier_ae Ω p χ B hχ.continuous.aestronglyMeasurable hb (J u)
    simp only [Ω, Opens.coe_top, Measure.restrict_univ] at hA ⊢
    filter_upwards [hrep, hA] with x hx hax
    change sobolevUnderlying v x = _
    rw [hx, hax]
    exact (RCLike.real_smul_eq_coe_mul (χ x) (sobolevUnderlying u x)).symm
  choose v hv using hex
  let L : Sobolev 𝕜 Ω k p →ₗ[𝕜] Sobolev 𝕜 Ω k p :=
    { toFun := v
      map_add' := fun u w => by
        apply hinj
        rw [map_add, hv, hv, hv, map_add, map_add]
      map_smul' := fun c u => by
        apply hinj
        rw [map_smul, hv, hv, map_smul, map_smul]
        rfl }
  have hgraph (us : ℕ → Sobolev 𝕜 Ω k p) (x y : Sobolev 𝕜 Ω k p)
      (hx : Tendsto us atTop (𝓝 x)) (hy : Tendsto (L ∘ us) atTop (𝓝 y)) : y = L x := by
    apply hinj
    change J y = J (v x)
    rw [hv]
    have hleft := (J.continuous.tendsto y).comp hy
    have hright := ((A.comp J).continuous.tendsto x).comp hx
    have heq : (J ∘ L ∘ us) = (A.comp J) ∘ us := by
      funext n
      exact hv (us n)
    rw [heq] at hleft
    exact tendsto_nhds_unique hleft hright
  let M := ContinuousLinearMap.ofSeqClosedGraph hgraph
  refine ⟨M, ?_⟩
  intro u
  change J (v u) =ᵐ[volume] _
  rw [hv]
  change A (J u) =ᵐ[volume] (fun x => χ x • J u x)
  simpa only [A, Ω, Opens.coe_top, Measure.restrict_univ] using
    realMultiplier_ae Ω p χ B hχ.continuous.aestronglyMeasurable hb (J u)

section Unflatten
variable {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
  (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
  (Ω : Opens (Space (m + 1)))
  (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
  (p : ℝ≥0∞) [Fact (1 ≤ p)]
  (J : Compacts (Space (m + 1)))
  (hJ : (J : Set (Space (m + 1))) ⊆ fullFlatChartOpen q C.center C.radius C.height)

/-- Physical image of a compact set staying strictly inside the full flat chart. -/
def chartPushforwardCompact : Compacts (Space (m + 1)) :=
  ⟨(fullChartMap e q C).toFun '' (J : Set (Space (m + 1))),
    J.isCompact.image_of_continuousOn ((fullChartMap e q C).lipschitz.continuousOn.mono hJ)⟩

theorem chartPushforwardCompact_subset :
    (chartPushforwardCompact e q Ω C J hJ : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C := by
  rintro x ⟨y, hy, rfl⟩
  exact (fullChartMap e q C).mapsTo (hJ hy)

def restrictWholeSupportedCLM :
    sobolevSupportedSubmodule (k := 1) 𝕜 (⊤ : Opens (Space (m + 1))) p J →L[𝕜]
      Sobolev 𝕜 (fullFlatChartOpen q C.center C.radius C.height) 1 p :=
  (sobolevRestrictCLM (𝕜 := 𝕜) (m := 1) (p := p) _).comp
    (sobolevSupportedSubmodule (k := 1) 𝕜 ⊤ p (J : Set (Space (m + 1)))).subtypeL

def unflattenPhysicalSupportedCLM :
    sobolevSupportedSubmodule (k := 1) 𝕜 (⊤ : Opens (Space (m + 1))) p J →L[𝕜]
      Sobolev 𝕜 (fullPhysicalChartOpen e C) 1 p :=
  ((fullChartMap e q C).symm.sobolevPullback meyersSerrin_smoothDensity
    (Nat.succ_pos m) 𝕜 p).comp (restrictWholeSupportedCLM e q Ω C p J)

theorem unflattenPhysicalSupportedCLM_zero_off_compact
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 (⊤ : Opens (Space (m + 1))) p J) :
    ∀ᵐ x ∂volume.restrict (fullPhysicalChartOpen e C : Set (Space (m + 1))),
      x ∉ chartPushforwardCompact e q Ω C J hJ →
        sobolevUnderlying (unflattenPhysicalSupportedCLM e q Ω C p J u) x = 0 := by
  let g := fullChartMap e q C
  change ∀ᵐ x ∂volume.restrict (fullPhysicalChartOpen e C : Set (Space (m + 1))),
    x ∉ chartPushforwardCompact e q Ω C J hJ →
      sobolevUnderlying (g.symm.sobolevPullback meyersSerrin_smoothDensity
        (Nat.succ_pos m) 𝕜 p (sobolevRestrict (fullFlatChartOpen q C.center C.radius C.height) u.val)) x = 0
  rw [g.symm.sobolevPullback_underlying]
  have hz : ∀ᵐ x ∂volume.restrict (fullFlatChartOpen q C.center C.radius C.height : Set (Space (m + 1))),
      x ∉ J → sobolevUnderlying (sobolevRestrict (fullFlatChartOpen q C.center C.radius C.height) u.val) x = 0 := by
    have hu : ∀ᵐ x ∂volume, x ∉ J → sobolevUnderlying u.val x = 0 := by
      have hh := u.property
      change ∀ᵐ x ∂volume.restrict ((⊤ : Opens (Space (m + 1))) : Set (Space (m + 1))),
        x ∉ J → sobolevUnderlying u.val x = 0 at hh
      simpa only [Opens.coe_top, Measure.restrict_univ] using hh
    filter_upwards [P102.U4.domainLpRestrict_ae (fullFlatChartOpen q C.center C.radius C.height)
        (sobolevUnderlying u.val), ae_restrict_of_ae hu] with x hx hxu hxJ
    exact hx.trans (hxu hxJ)
  filter_upwards [g.symm.lpPullback_ae 𝕜 p _, g.symm.ae_comp hz,
    ae_restrict_mem (fullPhysicalChartOpen e C).isOpen.measurableSet]
    with x hx hz hxV hxK
  rw [hx]
  apply hz
  intro hy
  exact hxK ⟨g.invFun x, hy, g.right_inv x hxV⟩

/-- Return any compactly supported whole-space chart function to Ω,
continuously and with the actual chart formula. -/
def unflattenSupportedCLM :
    sobolevSupportedSubmodule (k := 1) 𝕜 (⊤ : Opens (Space (m + 1))) p J →L[𝕜]
      Sobolev 𝕜 Ω 1 p :=
  (artificialBoundaryTransferCLM (fullPhysicalChartOpen e C) Ω (fullPhysicalChartOpen e C)
    p (chartPushforwardCompact e q Ω C J hJ) (chartPushforwardCompact_subset e q Ω C J hJ)
    (fun _ hx => hx.2)).comp
    ((unflattenPhysicalSupportedCLM e q Ω C p J).codRestrict
      (sobolevSupportedSubmodule (k := 1) 𝕜 (fullPhysicalChartOpen e C) p
        (chartPushforwardCompact e q Ω C J hJ))
      (unflattenPhysicalSupportedCLM_zero_off_compact e q Ω C p J hJ))

theorem unflattenPhysicalSupportedCLM_underlying_ae
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 (⊤ : Opens (Space (m + 1))) p J) :
    sobolevUnderlying (unflattenPhysicalSupportedCLM e q Ω C p J u) =ᵐ[
      volume.restrict (fullPhysicalChartOpen e C : Set (Space (m + 1)))]
      (fun x => sobolevUnderlying u.val ((fullChartMap e q C).invFun x)) := by
  let g := fullChartMap e q C
  change sobolevUnderlying (g.symm.sobolevPullback meyersSerrin_smoothDensity
    (Nat.succ_pos m) 𝕜 p (sobolevRestrict (fullFlatChartOpen q C.center C.radius C.height) u.val)) =ᵐ[_] _
  rw [g.symm.sobolevPullback_underlying]
  exact (g.symm.lpPullback_ae 𝕜 p _).trans
    (g.symm.ae_comp (P102.U4.domainLpRestrict_ae (fullFlatChartOpen q C.center C.radius C.height)
      (sobolevUnderlying u.val)))

theorem unflattenSupportedCLM_underlying_ae
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 (⊤ : Opens (Space (m + 1))) p J) :
    sobolevUnderlying (unflattenSupportedCLM e q Ω C p J hJ u) =ᵐ[
      volume.restrict (Ω : Set (Space (m + 1)))]
      (fullPhysicalChartOpen e C : Set (Space (m + 1))).indicator
        (fun x => sobolevUnderlying u.val ((fullChartMap e q C).invFun x)) := by
  let v : sobolevSupportedSubmodule (k := 1) 𝕜 (fullPhysicalChartOpen e C) p
      (chartPushforwardCompact e q Ω C J hJ) :=
    ⟨unflattenPhysicalSupportedCLM e q Ω C p J u,
      unflattenPhysicalSupportedCLM_zero_off_compact e q Ω C p J hJ u⟩
  have ht := artificialBoundaryTransferCLM_underlying_ae
    (fullPhysicalChartOpen e C) Ω (fullPhysicalChartOpen e C) p
    (chartPushforwardCompact e q Ω C J hJ) (chartPushforwardCompact_subset e q Ω C J hJ)
    (fun _ hx => hx.2) v
  have hi := indicator_ae_eq (fullPhysicalChartOpen e C)
    (unflattenPhysicalSupportedCLM_underlying_ae e q Ω C p J u)
  exact ht.trans (ae_restrict_of_ae hi)

theorem unflattenSupportedCLM_hasCompactSupportIn
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 (⊤ : Opens (Space (m + 1))) p J)
    (L : Compacts (Space (m + 1)))
    (hL : (L : Set (Space (m + 1))) ⊆ flatChartOpen q C.center C.radius C.height)
    (hu : ∀ᵐ x ∂volume, x ∉ L → sobolevUnderlying u.val x = 0) :
    HasCompactSupportIn (sobolevUnderlying (unflattenSupportedCLM e q Ω C p J hJ u)) := by
  let g := fullChartMap e q C
  have hLF : (L : Set (Space (m + 1))) ⊆ fullFlatChartOpen q C.center C.radius C.height := by
    rintro x hx
    obtain ⟨z, hz, rfl⟩ := hL hx
    exact ⟨z, ⟨hz.1, ⟨by linarith [hz.2.1, C.height_pos], hz.2.2⟩⟩, rfl⟩
  let Lp : Compacts (Space (m + 1)) :=
    ⟨g.toFun '' (L : Set (Space (m + 1))),
      L.isCompact.image_of_continuousOn (g.lipschitz.continuousOn.mono hLF)⟩
  refine ⟨Lp, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    exact ((physicalChartMap e q Ω C).mapsTo (hL hy)).1
  · have hvan := (ae_restrict_iff' (fullPhysicalChartOpen e C).isOpen.measurableSet).mp
      (g.symm.ae_comp (ae_restrict_of_ae hu))
    filter_upwards [unflattenSupportedCLM_underlying_ae e q Ω C p J hJ u,
      ae_restrict_of_ae hvan] with x hx hz hxL
    rw [hx]
    by_cases hxF : x ∈ fullPhysicalChartOpen e C
    · rw [indicator_of_mem hxF]
      apply hz hxF
      intro hy
      exact hxL ⟨g.invFun x, hy, g.right_inv x hxF⟩
    · exact indicator_of_notMem hxF _

end Unflatten


theorem chartBoundaryParam_image_measure_le
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (S : Set (Space m)) (hS : S ⊆ ball C.center C.radius) :
    (μHE[m] : Measure (Space (m + 1))) (chartBoundaryParam e Ω C '' S) ≤
      (graphConstant C.constant : ℝ≥0∞) ^ m * volume S := by
  have himg : chartBoundaryParam e Ω C '' S =
      e '' (C.frame '' (graph C.graphFunction '' S)) := by
    change (e ∘ C.frame ∘ graph C.graphFunction) '' S = _
    rw [Set.image_comp, Set.image_comp]
  rw [himg, e.isometry.euclideanHausdorffMeasure_image,
    C.frame.isometry.euclideanHausdorffMeasure_image]
  exact ((graph_geometry m (ball C.center C.radius) C.graphFunction C.constant
    C.graph_lipschitz).2.2 S hS).2

/-- Reverse measure comparison on the actual physical boundary patch. -/
theorem chartBoundaryParam_reverse_measure_le
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (E : Set (Space (m + 1))) :
    boundaryMeasure Ω (E ∩ (fullPhysicalChartOpen e C : Set (Space (m + 1)))) ≤
      (graphConstant C.constant : ℝ≥0∞) ^ m *
        volume (ball C.center C.radius ∩ chartBoundaryParam e Ω C ⁻¹' E) := by
  rw [boundaryMeasure, Measure.restrict_apply' measurableSet_frontier]
  have hset : (E ∩ (fullPhysicalChartOpen e C : Set (Space (m + 1)))) ∩
        frontier (Ω : Set (Space (m + 1))) =
      chartBoundaryParam e Ω C '' (ball C.center C.radius ∩ chartBoundaryParam e Ω C ⁻¹' E) := by
    ext x
    constructor
    · rintro ⟨⟨hxE, hxF⟩, hxf⟩
      have hi : x ∈ (fun y => e (C.frame (graph C.graphFunction y))) ''
          ball C.center C.radius := by
        rw [← physical_boundary_in_chart]
        exact ⟨hxf, hxF⟩
      obtain ⟨y, hy, rfl⟩ := hi
      exact ⟨y, ⟨hy, hxE⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hyE⟩, rfl⟩
      have hi : chartBoundaryParam e Ω C y ∈
          frontier (Ω : Set (Space (m + 1))) ∩
            (fullPhysicalChartOpen e C : Set (Space (m + 1))) := by
        change chartBoundaryParam e Ω C y ∈ frontier (Ω : Set (Space (m + 1))) ∩
          e '' chartImage C.frame C.graphFunction C.center C.radius C.height
        rw [physical_boundary_in_chart]
        exact ⟨y, hy, rfl⟩
      exact ⟨⟨hyE, hi.2⟩, hi.1⟩
  rw [hset]
  exact chartBoundaryParam_image_measure_le e Ω C _ inter_subset_left

/-- A vanishing chart-base pullback detects every boundary class supported
on that physical patch. The reverse Hausdorff comparison is essential. -/
theorem chartBoundaryLpPullbackFull_eq_zero_iff_of_supported
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (g : BoundaryLp 𝕜 Ω p)
    (hg : ∀ᵐ x ∂boundaryMeasure Ω, x ∉ fullPhysicalChartOpen e C → g x = 0) :
    chartBoundaryLpPullbackFull e Ω C 𝕜 p g = 0 ↔ g = 0 := by
  constructor
  · intro hzero
    have hlocal : chartBoundaryLpPullback e Ω C 𝕜 p g = 0 := by
      apply (lpZeroExtensionLI (chartBaseOpen C) p).injective
      change chartBoundaryLpPullbackFull e Ω C 𝕜 p g = _
      simpa only [map_zero] using hzero
    have hrep := chartBoundaryLpPullback_ae e Ω C 𝕜 p g
    rw [hlocal] at hrep
    have hz : (g ∘ chartBoundaryParam e Ω C) =ᵐ[
        volume.restrict (chartBaseOpen C : Set (Space m))] 0 :=
      hrep.symm.trans (Lp.coeFn_zero 𝕜 p _)
    have hbase : volume (ball C.center C.radius ∩
        chartBoundaryParam e Ω C ⁻¹' {x | g x ≠ 0}) = 0 := by
      have h := (ae_iff.mp hz)
      simp only [Pi.zero_apply] at h
      change (volume.restrict (ball C.center C.radius)) {a | ¬(g ∘ chartBoundaryParam e Ω C) a = 0} = 0 at h
      rw [Measure.restrict_apply' measurableSet_ball] at h
      simpa only [Set.preimage_ofPred_eq, Function.comp_apply, Pi.zero_apply, inter_comm] using h
    have hpatch : boundaryMeasure Ω ({x | g x ≠ 0} ∩
        (fullPhysicalChartOpen e C : Set (Space (m + 1)))) = 0 := by
      simpa only [hbase, mul_zero, nonpos_iff_eq_zero] using
        (chartBoundaryParam_reverse_measure_le e Ω C {x | g x ≠ 0})
    have hon : ∀ᵐ x ∂(boundaryMeasure Ω).restrict
        (fullPhysicalChartOpen e C : Set (Space (m + 1))), g x = 0 := by
      apply ae_iff.mpr
      rw [Measure.restrict_apply' (fullPhysicalChartOpen e C).isOpen.measurableSet]
      exact hpatch
    have hon' := (ae_restrict_iff' (fullPhysicalChartOpen e C).isOpen.measurableSet).mp hon
    apply Lp.ext
    apply Filter.EventuallyEq.trans _ (Lp.coeFn_zero 𝕜 p _).symm
    filter_upwards [hon', hg] with x hx hy
    by_cases hxF : x ∈ fullPhysicalChartOpen e C
    · exact hx hxF
    · exact hy hxF
  · intro h
    rw [h, map_zero]

/-- Restrict an actual whole-space cutoff map to its fixed support subspace. -/
def wholeCutoffSupportedCLM {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (χ : Space d → ℝ) (J : Compacts (Space d)) (hχJ : tsupport χ ⊆ (J : Set (Space d)))
    (M : Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p →L[𝕜] Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p)
    (hM : ∀ u, sobolevUnderlying (M u) =ᵐ[volume] (fun x => χ x • sobolevUnderlying u x)) :
    Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p →L[𝕜]
      sobolevSupportedSubmodule (k := 1) 𝕜 (⊤ : Opens (Space d)) p J :=
  M.codRestrict _ (by
    intro u
    change ∀ᵐ x ∂volume.restrict ((⊤ : Opens (Space d)) : Set (Space d)),
      x ∉ J → sobolevUnderlying (M u) x = 0
    simp only [Opens.coe_top, Measure.restrict_univ]
    filter_upwards [hM u] with x hx hxJ
    rw [hx, image_eq_zero_of_notMem_tsupport (fun hxs => hxJ (hχJ hxs)), zero_smul])

section CutoffUnflatten
variable {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
  (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
  (Ω : Opens (Space (m + 1)))
  (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
  (p : ℝ≥0∞) [Fact (1 ≤ p)]
  (χ : Space (m + 1) → ℝ) (hc : HasCompactSupport χ)
  (hχ : tsupport χ ⊆ fullFlatChartOpen (flatCoordinates m) C.center C.radius C.height)
  (M : Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p →L[𝕜]
    Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p)
  (hM : ∀ u, sobolevUnderlying (M u) =ᵐ[volume] (fun x => χ x • sobolevUnderlying u x))

def cutoffUnflattenCLM :
    Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p →L[𝕜] Sobolev 𝕜 Ω 1 p :=
  (unflattenSupportedCLM e (flatCoordinates m) Ω C p ⟨tsupport χ, hc⟩ hχ).comp
    (wholeCutoffSupportedCLM χ ⟨tsupport χ, hc⟩ (Subset.rfl) M hM)

theorem cutoffUnflattenCLM_mem_sobolevZero (hp : p ≠ ⊤)
    (w : Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p)
    (hw : ∀ᵐ x ∂volume, x (Fin.last m) < 0 → sobolevUnderlying w x = 0) :
    cutoffUnflattenCLM e Ω C p χ hc hχ M hM w ∈ sobolevZeroSubmodule 𝕜 Ω 1 p := by
  let A := cutoffUnflattenCLM e Ω C p χ hc hχ M hM
  have hclosed : IsClosed {v | A v ∈ sobolevZeroSubmodule 𝕜 Ω 1 p} :=
    (smoothSobolevSubmodule 𝕜 Ω 1 p).isClosed_topologicalClosure.preimage A.continuous
  apply hclosed.closure_subset
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨φ, z, hz, herr⟩ := halfSpace_approximation_of_wholeSpace hp w hw hε
  refine ⟨z, ?_, ?_⟩
  · apply mem_sobolevZero_of_compactSupport hp
    let L : Compacts (Space (m + 1)) :=
      ⟨tsupport χ ∩ tsupport φ, hc.inter_right (isClosed_tsupport φ)⟩
    apply unflattenSupportedCLM_hasCompactSupportIn e (flatCoordinates m) Ω C p
      ⟨tsupport χ, hc⟩ hχ (wholeCutoffSupportedCLM χ ⟨tsupport χ, hc⟩ (Subset.rfl) M hM z) L
    · intro x hx
      have hxH : x ∈ flatPositiveOpen (flatCoordinates m) := by
        rw [flatPositiveOpen_flatCoordinates]
        exact φ.tsupport_subset hx.2
      exact flatPositive_inter_full_subset_flat (flatCoordinates m) C.center C.radius C.height
        ⟨hxH, hχ hx.1⟩
    · have hz0 := hz (zeroSobolevIndex (m + 1) 1)
      simp only [zeroSobolevIndex, multiPartial, Multiset.sort_zero, partialWord] at hz0
      change (sobolevUnderlying z : Space (m + 1) → 𝕜) =ᵐ[volume] φ at hz0
      filter_upwards [hM z, hz0] with x hx hzx hxL
      change sobolevUnderlying (M z) x = 0
      rw [hx]
      by_cases hxχ : x ∈ tsupport χ
      · have hxφ : x ∉ tsupport φ := fun h => hxL ⟨hxχ, h⟩
        rw [hzx, image_eq_zero_of_notMem_tsupport hxφ, smul_zero]
      · rw [image_eq_zero_of_notMem_tsupport hxχ, zero_smul]
  · simpa only [dist_eq_norm', norm_sub_rev] using herr

end CutoffUnflatten

section FlatCutoffTrace

/-- The zero-height face point in the canonical Euclidean chart. -/
def flatFace (m : ℕ) (x : Space m) : Space (m + 1) :=
  flatCoordinates m (WithLp.toLp 2 (x, (0 : ℝ)))

theorem flatFace_continuous (m : ℕ) : Continuous (flatFace m) := by
  exact (flatCoordinates m).continuous.comp
    ((WithLp.homeomorphProd 2 (Space m) ℝ).symm.continuous.comp
      (continuous_id.prodMk continuous_const))

variable {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (ψ : Space (m + 1) → ℝ) (hψ : Continuous ψ)
    (B : ℝ≥0) (hB : ∀ x, ‖ψ x‖ ≤ B)

def flatFaceMultiplier : DomainLp 𝕜 (⊤ : Opens (Space m)) p →L[𝕜]
    DomainLp 𝕜 (⊤ : Opens (Space m)) p :=
  realMultiplier ⊤ p (ψ ∘ flatFace m) B
    (hψ.comp (flatFace_continuous m)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => hB (flatFace m x))

theorem flatFaceMultiplier_ae (u : DomainLp 𝕜 (⊤ : Opens (Space m)) p) :
    flatFaceMultiplier p ψ hψ B hB u =ᵐ[volume]
      (fun x => ψ (flatFace m x) • u x) := by
  have h := realMultiplier_ae (𝕜 := 𝕜) ⊤ p (ψ ∘ flatFace m) B
    (hψ.comp (flatFace_continuous m)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => hB (flatFace m x)) u
  change realMultiplier ⊤ p (ψ ∘ flatFace m) B
    (hψ.comp (flatFace_continuous m)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => hB (flatFace m x)) u =ᵐ[volume] _
  simpa only [Opens.coe_top, Measure.restrict_univ, Function.comp_apply] using h

set_option maxHeartbeats 1200000 in
/-- The same flat trace commutes with multiplication of a whole-space
extension by an actual smooth cutoff. -/
theorem flat_trace_whole_cutoff_commutes
    (hp : p ≠ ⊤) (hψsmooth : ContDiff ℝ ∞ ψ)
    (M : Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p →L[𝕜]
      Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p)
    (hM : ∀ u, sobolevUnderlying (M u) =ᵐ[volume]
      (fun x => ψ x • sobolevUnderlying u x))
    (Tflat : HalfSobolev m 𝕜 p →L[𝕜] P102.Trace.BoundaryLp m 𝕜 p)
    (hflat : ∀ (v : HalfSobolev m 𝕜 p) (F : Space (m + 1) → 𝕜),
      ContinuousOn F {x | 0 ≤ x (Fin.last m)} →
      sobolevUnderlying v =ᵐ[volume.restrict (halfSpace m : Set (Space (m + 1)))] F →
      (fun z => Tflat v z) =ᵐ[volume] (fun z => F (point m z 0))) :
    (((flatBoundaryToBaseLI m 𝕜 p).toContinuousLinearMap.comp Tflat).comp
      ((sobolevRestrictCLM (𝕜 := 𝕜) (m := 1) (p := p) (halfSpace m)).comp M)) =
      (flatFaceMultiplier p ψ hψ B hB).comp
        (((flatBoundaryToBaseLI m 𝕜 p).toContinuousLinearMap.comp Tflat).comp
          (sobolevRestrictCLM (𝕜 := 𝕜) (m := 1) (p := p) (halfSpace m))) := by
  let R := sobolevRestrictCLM (𝕜 := 𝕜) (m := 1) (p := p) (halfSpace m)
  let A := ((flatBoundaryToBaseLI m 𝕜 p).toContinuousLinearMap.comp Tflat).comp (R.comp M)
  let D := ((flatBoundaryToBaseLI m 𝕜 p).toContinuousLinearMap.comp Tflat).comp R
  let E := (flatFaceMultiplier p ψ hψ B hB).comp D
  change A = E
  apply ContinuousLinearMap.ext
  intro u
  obtain ⟨φ,v,hv,ht,_⟩ := wholeSpace_density 1 p hp u
  have heq (n : ℕ) : A (v n) = E (v n) := by
    have hφ : sobolevUnderlying (v n) =ᵐ[volume] φ n := by
      have hz := hv n (zeroSobolevIndex (m + 1) 1)
      change (sobolevUnderlying (v n) : Space (m + 1) → 𝕜) =ᵐ[_] multiPartial (φ n) 0 at hz
      simpa only [multiPartial, Multiset.sort_zero, partialWord] using hz
    have hvr : sobolevUnderlying (R (v n)) =ᵐ[
        volume.restrict (halfSpace m : Set (Space (m + 1)))] φ n :=
      (P102.U4.domainLpRestrict_ae (halfSpace m) _).trans (ae_restrict_of_ae hφ)
    have hMr : sobolevUnderlying (R (M (v n))) =ᵐ[
        volume.restrict (halfSpace m : Set (Space (m + 1)))] (fun x => ψ x • φ n x) := by
      filter_upwards [P102.U4.domainLpRestrict_ae (halfSpace m) (sobolevUnderlying (M (v n))),
        ae_restrict_of_ae (hM (v n)), ae_restrict_of_ae hφ] with x hx hy hz
      change domainLpRestrict (halfSpace m) (sobolevUnderlying (M (v n))) x = _
      rw [hx,hy,hz]
    have hTv := (boundaryBaseCoordinates_measurePreserving m).quasiMeasurePreserving.ae
      (hflat (R (v n)) (φ n) (φ n).continuous.continuousOn hvr)
    have hTM := (boundaryBaseCoordinates_measurePreserving m).quasiMeasurePreserving.ae
      (hflat (R (M (v n))) (fun x => ψ x • φ n x)
        ((hψsmooth.smul (φ n).contDiff).continuous.continuousOn) hMr)
    apply Lp.ext
    simp only [Opens.coe_top, Measure.restrict_univ]
    filter_upwards [flatBoundaryToBaseLI_ae m 𝕜 p (Tflat (R (M (v n)))), hTM,
      flatFaceMultiplier_ae p ψ hψ B hB (D (v n)),
      flatBoundaryToBaseLI_ae m 𝕜 p (Tflat (R (v n))), hTv] with x hLI hTM hmul hLIv hTv
    change flatBoundaryToBaseLI m 𝕜 p (Tflat (R (M (v n)))) x =
      flatFaceMultiplier p ψ hψ B hB (D (v n)) x
    rw [hmul]
    change flatBoundaryToBaseLI m 𝕜 p (Tflat (R (M (v n)))) x =
      ψ (flatFace m x) • flatBoundaryToBaseLI m 𝕜 p (Tflat (R (v n))) x
    rw [hLI, Function.comp_apply, hTM, hLIv, Function.comp_apply, hTv]
    simp only [point_boundaryBaseCoordinates, flatFace]
  have hAlim := (A.continuous.tendsto u).comp ht
  have hElim := (E.continuous.tendsto u).comp ht
  have heqfun : A ∘ v = E ∘ v := funext heq
  rw [heqfun] at hAlim
  exact tendsto_nhds_unique hAlim hElim

end FlatCutoffTrace


section Recovery
variable {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
  (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
  (Ω : Opens (Space (m + 1)))
  (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
  (p : ℝ≥0∞) [Fact (1 ≤ p)]
  (K : Compacts (Space (m + 1)))
  (hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C)

theorem unflattenSupportedCLM_recovers_flattenHalf
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K)
    (J : Compacts (Space (m + 1)))
    (hJ : (J : Set (Space (m + 1))) ⊆ fullFlatChartOpen (flatCoordinates m) C.center C.radius C.height)
    (z : sobolevSupportedSubmodule (k := 1) 𝕜 (⊤ : Opens (Space (m + 1))) p J)
    (hz : sobolevUnderlying z.val = lpZeroExtension (halfSpace m) p
      (sobolevUnderlying (flattenHalfSupportedCLM e Ω C p K hK u))) :
    unflattenSupportedCLM e (flatCoordinates m) Ω C p J hJ z = u.val := by
  let q := flatCoordinates m
  let g := fullChartMap e q C
  let gP := physicalChartMap e q Ω C
  have hinc : (flatChartOpen q C.center C.radius C.height : Set (Space (m + 1))) ⊆ halfSpace m := by
    intro x hx
    rw [← flatPositiveOpen_flatCoordinates m]
    exact flatChartOpen_le_flatPositive q C.center C.radius C.height hx
  have hzrep : (sobolevUnderlying z.val : Space (m + 1) → 𝕜) =ᵐ[volume]
      (halfSpace m : Set (Space (m + 1))).indicator
        (sobolevUnderlying (flattenHalfSupportedCLM e Ω C p K hK u)) := by
    rw [hz]
    exact lpZeroExtension_ae (halfSpace m) p _
  have hzu : (sobolevUnderlying z.val : Space (m + 1) → 𝕜) =ᵐ[
      volume.restrict (flatChartOpen q C.center C.radius C.height : Set (Space (m + 1)))]
      (fun x => sobolevUnderlying u.val (gP.toFun x)) := by
    filter_upwards [ae_restrict_of_ae hzrep,
      (flattenHalfSupportedCLM_underlying_ae e Ω C p K hK u).filter_mono
        (ae_mono (volume.restrict_mono_set hinc)),
      flattenCylinderSupportedCLM_underlying_ae e q Ω C p K u,
      ae_restrict_mem (flatChartOpen q C.center C.radius C.height).isOpen.measurableSet]
      with x hx hh hf hxF
    rw [hx, indicator_of_mem (hinc hxF), hh, indicator_of_mem hxF, hf]
  have hphys : (fun x => sobolevUnderlying z.val (g.invFun x)) =ᵐ[
      volume.restrict (physicalChartOpen e Ω C : Set (Space (m + 1)))] sobolevUnderlying u.val := by
    filter_upwards [gP.symm.ae_comp hzu,
      ae_restrict_mem (physicalChartOpen e Ω C).isOpen.measurableSet] with x hx hxP
    exact hx.trans (congrArg (fun y => sobolevUnderlying u.val y) (gP.right_inv x hxP))
  apply sobolevUnderlying_injective Ω 1 p
  apply Lp.ext
  have hpglob := (ae_restrict_iff' (physicalChartOpen e Ω C).isOpen.measurableSet).mp hphys
  filter_upwards [unflattenSupportedCLM_underlying_ae e q Ω C p J hJ z,
    ae_restrict_of_ae hpglob, u.property, ae_restrict_mem Ω.isOpen.measurableSet]
    with x hx hp hu hxΩ
  rw [hx]
  by_cases hxF : x ∈ fullPhysicalChartOpen e C
  · rw [indicator_of_mem hxF]
    exact hp ⟨hxΩ, hxF⟩
  · rw [indicator_of_notMem hxF]
    exact (hu (fun hxK => hxF (hK hxK))).symm

/-- Reverse local kernel transfer. Flat W₀ membership produces physical
compact interior approximants, including after a merely bi-Lipschitz chart.
The final smoothing is in the physical ambient coordinates. -/
theorem mem_sobolevZero_of_flattenHalf_mem_sobolevZero
    (hp : p ≠ ⊤)
    (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K)
    (hu : flattenHalfSupportedCLM e Ω C p K hK u ∈
      sobolevZeroSubmodule 𝕜 (halfSpace m) 1 p) :
    u.val ∈ sobolevZeroSubmodule 𝕜 Ω 1 p := by
  let v : SobolevZero 𝕜 (halfSpace m) 1 p := ⟨flattenHalfSupportedCLM e Ω C p K hK u, hu⟩
  let w := sobolevZeroExtensionLI (halfSpace m) 1 p v
  let Kf := fullChartPullbackCompact e (flatCoordinates m) C K hK
  obtain ⟨χ, _, N, hKfN, _, hχone⟩ := cutoff (m + 1)
    (fullFlatChartOpen (flatCoordinates m) C.center C.radius C.height) Kf
    (fullChartPullbackCompact_subset e (flatCoordinates m) C K hK)
  obtain ⟨M, hM⟩ := exists_wholeSobolevCutoffCLM (k := 1) (𝕜 := 𝕜) p
    (χ : Space (m + 1) → ℝ) χ.contDiff χ.hasCompactSupport
  have hwK : ∀ᵐ x ∂volume, x ∉ Kf → sobolevUnderlying w x = 0 :=
    lpZeroExtension_zero_off_compact
      (sobolevUnderlying (flattenHalfSupportedCLM e Ω C p K hK u)) Kf
      (flattenHalfSupportedCLM_zero_off_compact e Ω C p K hK u)
  have hMw : M w = w := by
    apply sobolevUnderlying_injective (⊤ : Opens (Space (m + 1))) 1 p
    apply Lp.ext
    simp only [Opens.coe_top, Measure.restrict_univ]
    filter_upwards [hM w, hwK] with x hx hz
    rw [hx]
    by_cases hxK : x ∈ Kf
    · rw [hχone x (hKfN hxK), one_smul]
    · rw [hz hxK, smul_zero]
  have hwneg : ∀ᵐ x ∂volume, x (Fin.last m) < 0 → sobolevUnderlying w x = 0 := by
    have he := lpZeroExtension_ae (halfSpace m) p
      (sobolevUnderlying (flattenHalfSupportedCLM e Ω C p K hK u))
    filter_upwards [he] with x hx hxneg
    change lpZeroExtension (halfSpace m) p
      (sobolevUnderlying (flattenHalfSupportedCLM e Ω C p K hK u)) x = 0
    rw [hx]
    apply indicator_of_notMem
    change ¬0 < x (Fin.last m)
    exact not_lt.mpr hxneg.le
  have hm := cutoffUnflattenCLM_mem_sobolevZero e Ω C p χ χ.hasCompactSupport
    χ.tsupport_subset M hM hp w hwneg
  have hrec : cutoffUnflattenCLM e Ω C p χ χ.hasCompactSupport χ.tsupport_subset M hM w = u.val := by
    apply unflattenSupportedCLM_recovers_flattenHalf e Ω C p K hK u
      ⟨tsupport χ, χ.hasCompactSupport⟩ χ.tsupport_subset
      (wholeCutoffSupportedCLM χ ⟨tsupport χ, χ.hasCompactSupport⟩ (Subset.rfl) M hM w)
    change sobolevUnderlying (M w) = _
    rw [hMw]
    rfl
  rwa [hrec] at hm

end Recovery

section GlobalKernel
variable
  (hBack : ∀ (m : ℕ) (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ →
    ∀ (K : Compacts (Space (m + 1)))
      (hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C)
      (u : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K),
      flattenHalfSupportedCLM e Ω C p K hK u ∈ sobolevZeroSubmodule 𝕜 (halfSpace m) 1 p →
        u.val ∈ sobolevZeroSubmodule 𝕜 Ω 1 p)

include hBack

set_option maxHeartbeats 2000000 in
/-- Global kernel assembly from the actual localized flat closure assertion. -/
theorem kernel_of_supported_flat_closure
    (hCutoff : Expected.CutoffCompatibility)
    (hEndpoint : Expected.EndpointIdentification)
    (hTrace : Expected.TraceExists)
    (hUnique : Expected.TraceUniqueness) : Expected.Kernel := by
  classical
  intro m e Ω hΩ 𝕜 _ p _ hp T hT
  by_cases hm : 1 ≤ m
  · obtain ⟨_, _, Tf, _, hSlices, hCompat⟩ := flat_trace_exists m hm 𝕜 p hp
    obtain ⟨n, C, χ, M, hχ, hinter, hboundary, hrep, _, hsum, hz, hzero⟩ :=
      exists_sobolev_localization hCutoff e hΩ hp T hT
    apply le_antisymm
    · intro u hu
      have hmem (i : Fin n) : M i.succ u ∈ sobolevZeroSubmodule 𝕜 Ω 1 p := by
        let K : Compacts (Space (m + 1)) := ⟨tsupport (χ i.succ), (hχ i.succ).2⟩
        have hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e (C i) := hboundary i
        let N := cutoffSupportedCLM Ω p K (χ i.succ) (subset_refl _) (M i.succ) (hrep i.succ)
        let v := flattenHalfSupportedCLM e Ω (C i) p K hK (N u)
        have he := congrArg (fun A : Sobolev 𝕜 Ω 1 p →L[𝕜]
            DomainLp 𝕜 (⊤ : Opens (Space m)) p => A u)
          (local_trace_identification_of_density
            (ambient_smooth_density_conditional hCutoff hEndpoint hTrace hUnique)
            e Ω hΩ (C i) p hp K hK (χ i.succ) (hχ i.succ).1 (subset_refl _)
            (M i.succ) (hrep i.succ) T hT Tf hCompat)
        change flatBoundaryToBaseLI m 𝕜 p (Tf v) =
          chartBoundaryLpPullbackFull e Ω (C i) 𝕜 p (T (M i.succ u)) at he
        rw [hz i.succ u hu, map_zero] at he
        have hTv : Tf v = 0 := (flatBoundaryToBaseLI m 𝕜 p).injective
          (he.trans (map_zero (flatBoundaryToBaseLI m 𝕜 p)).symm)
        obtain ⟨F, _, _, _, _, _, _, _, hB⟩ := hSlices v
        have hZero : HasZeroFlatTrace v := by
          change HasVerticalBoundaryValues v 0
          rwa [hTv] at hB
        have hW0 : v ∈ sobolevZeroSubmodule 𝕜 (halfSpace m) 1 p :=
          (flatZeroExtension_iff_mem_sobolevZero hp v).mp
            ((flat_zero_trace_iff_extension m hm 𝕜 p hp v).mp hZero)
        exact hBack m e Ω (C i) 𝕜 p hp K hK (N u) hW0
      have he := hsum u
      rw [Fin.sum_univ_succ] at he
      rw [← he]
      exact (sobolevZeroSubmodule 𝕜 Ω 1 p).add_mem (hzero u)
        ((sobolevZeroSubmodule 𝕜 Ω 1 p).sum_mem (fun i _ => hmem i))
    · exact sobolevZero_le_trace_ker T hT
  · have hm0 : m = 0 := by omega
    subst m
    exact kernel_oneDimension_conditional hCutoff hEndpoint hTrace hUnique e Ω hΩ 𝕜 p hp T hT

set_option maxHeartbeats 1600000 in
/-- A physical zero extension localizes, flattens on both sides, and belongs
to the actual test closure. This uses the flat closure assertion in every dimension. -/
theorem mem_sobolevZero_of_hasZeroExtension_of_supported_flat_closure
    (hCutoff : Expected.CutoffCompatibility)
    (hEndpoint : Expected.EndpointIdentification)
    (hTrace : Expected.TraceExists)
    (hUnique : Expected.TraceUniqueness)
    (m : ℕ) (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (u : Sobolev 𝕜 Ω 1 p) (hu : HasZeroExtension u) :
    u ∈ sobolevZeroSubmodule 𝕜 Ω 1 p := by
  classical
  obtain ⟨_, _, T, hT, _, _⟩ := hTrace m e Ω hΩ 𝕜 p hp
  obtain ⟨n, C, χ, M, hχ, hinter, hboundary, hrep, _, hsum, _, hzero⟩ :=
    exists_sobolev_localization hCutoff e hΩ hp T hT
  have hmem (i : Fin n) : M i.succ u ∈ sobolevZeroSubmodule 𝕜 Ω 1 p := by
    let K : Compacts (Space (m + 1)) := ⟨tsupport (χ i.succ), (hχ i.succ).2⟩
    have hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e (C i) := hboundary i
    let N := cutoffSupportedCLM Ω p K (χ i.succ) (subset_refl _) (M i.succ) (hrep i.succ)
    have hEx : HasZeroExtension (N u).val :=
      hasZeroExtension_localized (χ i.succ) (hχ i.succ).1 (hχ i.succ).2 u (M i.succ u)
        (hrep i.succ u) hu
    exact hBack m e Ω (C i) 𝕜 p hp K hK (N u)
      (flattenHalfSupportedCLM_mem_sobolevZero_of_zeroExtension e Ω (C i) p K hK hp (N u) hEx)
  have he := hsum u
  rw [Fin.sum_univ_succ] at he
  rw [← he]
  exact (sobolevZeroSubmodule 𝕜 Ω 1 p).add_mem (hzero u)
    ((sobolevZeroSubmodule 𝕜 Ω 1 p).sum_mem (fun i _ => hmem i))

/-- Both sides of the zero-extension criterion, after local closure transfer. -/
theorem zero_extension_criterion_of_supported_flat_closure
    (hCutoff : Expected.CutoffCompatibility)
    (hEndpoint : Expected.EndpointIdentification)
    (hTrace : Expected.TraceExists)
    (hUnique : Expected.TraceUniqueness) : Expected.ZeroExtensionCriterion := by
  intro m e Ω hΩ 𝕜 _ p _ hp T hT u
  constructor
  · intro hu
    apply hasZeroExtension_of_mem_sobolevZero u
    rw [← kernel_of_supported_flat_closure hBack hCutoff hEndpoint hTrace hUnique
      m e Ω hΩ 𝕜 p hp T hT]
    exact hu
  · intro hu
    exact sobolevZero_le_trace_ker T hT
      (mem_sobolevZero_of_hasZeroExtension_of_supported_flat_closure hBack
        hCutoff hEndpoint hTrace hUnique m e Ω hΩ 𝕜 p hp u hu)

end GlobalKernel

/-- The full all-dimensional kernel theorem, with precisely the four
ordered frozen trace-map premises. -/
theorem kernel_conditional
    (hCutoff : Expected.CutoffCompatibility)
    (hEndpoint : Expected.EndpointIdentification)
    (hTrace : Expected.TraceExists)
    (hUnique : Expected.TraceUniqueness) : Expected.Kernel := by
  apply kernel_of_supported_flat_closure ?_ hCutoff hEndpoint hTrace hUnique
  intro m e Ω C 𝕜 _ p _ hp K hK u hu
  exact mem_sobolevZero_of_flattenHalf_mem_sobolevZero e Ω C p K hK hp u hu

/-- The full physical zero-extension criterion, using the actual norm
closure of compact interior tests and the actual whole-space extension. -/
theorem zero_extension_criterion_conditional
    (hCutoff : Expected.CutoffCompatibility)
    (hEndpoint : Expected.EndpointIdentification)
    (hTrace : Expected.TraceExists)
    (hUnique : Expected.TraceUniqueness) : Expected.ZeroExtensionCriterion := by
  apply zero_extension_criterion_of_supported_flat_closure ?_ hCutoff hEndpoint hTrace hUnique
  intro m e Ω C 𝕜 _ p _ hp K hK u hu
  exact mem_sobolevZero_of_flattenHalf_mem_sobolevZero e Ω C p K hK hp u hu


/-- The flat cutoff does not alter data supported on the original physical
compact set when it equals one on its full inverse image. -/
theorem flatFaceMultiplier_fixes_supported_pullback
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (K : Compacts (Space (m + 1))) (hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C)
    (g : BoundaryLp 𝕜 Ω p)
    (hg : ∀ᵐ y ∂boundaryMeasure Ω, y ∉ K → g y = 0)
    (ψ : Space (m + 1) → ℝ) (hψ : Continuous ψ)
    (B : ℝ≥0) (hB : ∀ x, ‖ψ x‖ ≤ B)
    (hψone : ∀ y ∈ fullChartPullbackCompact e (flatCoordinates m) C K hK, ψ y = 1) :
    flatFaceMultiplier p ψ hψ B hB (chartBoundaryLpPullbackFull e Ω C 𝕜 p g) =
      chartBoundaryLpPullbackFull e Ω C 𝕜 p g := by
  have hgs := (ae_restrict_iff' (chartBaseOpen C).isOpen.measurableSet).mp
    (chartBoundaryParam_ae_comp e Ω C hg)
  apply Lp.ext
  simp only [Opens.coe_top, Measure.restrict_univ]
  filter_upwards [flatFaceMultiplier_ae p ψ hψ B hB (chartBoundaryLpPullbackFull e Ω C 𝕜 p g),
    chartBoundaryLpPullbackFull_ae e Ω C 𝕜 p g, hgs] with x hmul hPB hgs
  rw [hmul,hPB]
  by_cases hxB : x ∈ chartBaseOpen C
  · rw [indicator_of_mem hxB]
    by_cases hxK : chartBoundaryParam e Ω C x ∈ K
    · have hxQ : flatFace m x ∈ fullChartPullbackCompact e (flatCoordinates m) C K hK := by
        refine ⟨chartBoundaryParam e Ω C x,hxK,?_⟩
        simp only [fullChartMap, chartBoundaryParam, LinearIsometryEquiv.symm_apply_apply,
          AffineIsometryEquiv.symm_apply_apply, unshear, graph, WithLp.ofLp_toLp, sub_self, flatFace]
      rw [hψone _ hxQ, one_smul]
    · have hzero := hgs hxB hxK
      simp only [Function.comp_apply, hzero, smul_zero]
  · rw [indicator_of_notMem hxB]
    exact smul_zero _

/-- The returned physical class retains a compact support in the full
physical patch, including at the genuine boundary. -/
theorem unflattenSupportedCLM_zero_off_compact
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (J : Compacts (Space (m + 1)))
    (hJ : (J : Set (Space (m + 1))) ⊆ fullFlatChartOpen q C.center C.radius C.height)
    (w : sobolevSupportedSubmodule (k := 1) 𝕜 (⊤ : Opens (Space (m + 1))) p J) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (Space (m + 1))),
      x ∉ chartPushforwardCompact e q Ω C J hJ →
        sobolevUnderlying (unflattenSupportedCLM e q Ω C p J hJ w) x = 0 :=
  artificialBoundaryTransferCLM_zero_off_compact
    (fullPhysicalChartOpen e C) Ω (fullPhysicalChartOpen e C) p
    (chartPushforwardCompact e q Ω C J hJ) (chartPushforwardCompact_subset e q Ω C J hJ)
    (fun _ hx => hx.2) _


/-- Flattening the genuine unflattened class recovers the original
whole-space function on the upper half-space. -/
theorem flattenHalf_unflatten_recovery
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (J : Compacts (Space (m + 1)))
    (hJ : (J : Set (Space (m + 1))) ⊆ fullFlatChartOpen (flatCoordinates m) C.center C.radius C.height)
    (w : sobolevSupportedSubmodule (k := 1) 𝕜 (⊤ : Opens (Space (m + 1))) p J)
    (K : Compacts (Space (m + 1))) (hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C)
    (v : sobolevSupportedSubmodule (k := 1) 𝕜 Ω p K)
    (hv : v.val = unflattenSupportedCLM e (flatCoordinates m) Ω C p J hJ w) :
    flattenHalfSupportedCLM e Ω C p K hK v = sobolevRestrict (halfSpace m) w.val := by
  let g := physicalChartMap e (flatCoordinates m) Ω C
  have hu : sobolevUnderlying v.val =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))]
      (fullPhysicalChartOpen e C : Set (Space (m + 1))).indicator
        (fun x => sobolevUnderlying w.val ((fullChartMap e (flatCoordinates m) C).invFun x)) := by
    rw [hv]
    exact unflattenSupportedCLM_underlying_ae e (flatCoordinates m) Ω C p J hJ w
  have huP : sobolevUnderlying v.val =ᵐ[volume.restrict (physicalChartOpen e Ω C : Set (Space (m + 1)))]
      (fullPhysicalChartOpen e C : Set (Space (m + 1))).indicator
        (fun x => sobolevUnderlying w.val ((fullChartMap e (flatCoordinates m) C).invFun x)) :=
    hu.filter_mono (ae_mono (volume.restrict_mono_set (fun _ hx => hx.1)))
  have hcyl : sobolevUnderlying (flattenCylinderSupportedCLM e (flatCoordinates m) Ω C p K v) =ᵐ[
      volume.restrict (flatChartOpen (flatCoordinates m) C.center C.radius C.height : Set (Space (m + 1)))]
        sobolevUnderlying w.val := by
    filter_upwards [flattenCylinderSupportedCLM_underlying_ae e (flatCoordinates m) Ω C p K v,
      g.ae_comp huP, ae_restrict_mem (flatChartOpen (flatCoordinates m) C.center C.radius C.height).isOpen.measurableSet]
      with x hx hy hxU
    have hmem : g.toFun x ∈ fullPhysicalChartOpen e C := (g.mapsTo hxU).2
    rw [hx,hy,indicator_of_mem hmem]
    change sobolevUnderlying w.val
      ((fullChartMap e (flatCoordinates m) C).invFun ((fullChartMap e (flatCoordinates m) C).toFun x)) = _
    rw [fullChartMap_left_inv_global]
  have hcyla := (ae_restrict_iff'
    (flatChartOpen (flatCoordinates m) C.center C.radius C.height).isOpen.measurableSet).mp hcyl
  have hw : ∀ᵐ x ∂volume, x ∉ J → sobolevUnderlying w.val x = 0 := by
    have h := w.property
    change ∀ᵐ x ∂volume.restrict ((⊤ : Opens (Space (m + 1))) : Set (Space (m + 1))),
      x ∉ J → sobolevUnderlying w.val x = 0 at h
    simpa only [Opens.coe_top, Measure.restrict_univ] using h
  apply sobolevUnderlying_injective (halfSpace m) 1 p
  apply Lp.ext
  filter_upwards [flattenHalfSupportedCLM_underlying_ae e Ω C p K hK v,
    P102.U4.domainLpRestrict_ae (halfSpace m) (sobolevUnderlying w.val),
    ae_restrict_of_ae hcyla, ae_restrict_of_ae hw,
    ae_restrict_mem (halfSpace m).isOpen.measurableSet] with x hx hy hc hw hxH
  change sobolevUnderlying (flattenHalfSupportedCLM e Ω C p K hK v) x =
    domainLpRestrict (halfSpace m) (sobolevUnderlying w.val) x
  rw [hx,hy]
  by_cases hxU : x ∈ flatChartOpen (flatCoordinates m) C.center C.radius C.height
  · rw [indicator_of_mem hxU]
    exact hc hxU
  · rw [indicator_of_notMem hxU]
    symm
    apply hw
    intro hxJ
    have hxF := hJ hxJ
    have hxP : x ∈ flatPositiveOpen (flatCoordinates m) := by
      rwa [flatPositiveOpen_flatCoordinates]
    exact hxU (flatPositive_inter_full_subset_flat (flatCoordinates m) C.center C.radius C.height ⟨hxP,hxF⟩)


set_option maxHeartbeats 1600000 in
/-- Every boundary datum supported on a compact subset of one physical
chart has a preimage under the same ordinary trace. The flat lifting
surjectivity and smooth density are explicit established interfaces. -/
theorem local_endpoint_lift_of_flat_surjective
    (hCutoff : Expected.CutoffCompatibility)
    (hDensity : P102.Sobolev.Extension.Expected.Density)
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1)))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (T : Sobolev 𝕜 Ω 1 1 →L[𝕜] BoundaryLp 𝕜 Ω 1) (hT : IsTrace T)
    (Tflat : HalfSobolev m 𝕜 1 →L[𝕜] P102.Trace.BoundaryLp m 𝕜 1)
    (hflat : ∀ (v : HalfSobolev m 𝕜 1) (F : Space (m + 1) → 𝕜),
      ContinuousOn F {x | 0 ≤ x (Fin.last m)} →
      sobolevUnderlying v =ᵐ[volume.restrict (halfSpace m : Set (Space (m + 1)))] F →
      (fun z => Tflat v z) =ᵐ[volume] (fun z => F (point m z 0)))
    (hsurj : Function.Surjective Tflat)
    (K : Compacts (Space (m + 1))) (hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C)
    (g : BoundaryLp 𝕜 Ω 1)
    (hg : ∀ᵐ y ∂boundaryMeasure Ω, y ∉ K → g y = 0) :
    ∃ v : Sobolev 𝕜 Ω 1 1, T v = g := by
  classical
  let Q := fullChartPullbackCompact e (flatCoordinates m) C K hK
  obtain ⟨ψ,hψbound,V,hQV,_,hψone⟩ := cutoff (m + 1)
    (fullFlatChartOpen (flatCoordinates m) C.center C.radius C.height) Q
    (fullChartPullbackCompact_subset e (flatCoordinates m) C K hK)
  let J : Compacts (Space (m + 1)) := ⟨tsupport ψ,ψ.hasCompactSupport⟩
  have hJ : (J : Set (Space (m + 1))) ⊆
      fullFlatChartOpen (flatCoordinates m) C.center C.radius C.height := ψ.tsupport_subset
  have hψB : ∀ x, ‖ψ x‖ ≤ (1 : ℝ≥0) := by
    intro x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hψbound x).1, NNReal.coe_one] using (hψbound x).2
  have hψQ : ∀ y ∈ Q, ψ y = 1 := fun y hy => hψone y (hQV hy)
  obtain ⟨Mψ,hMψ⟩ := exists_wholeSobolevCutoffCLM (k := 1) (𝕜 := 𝕜)
    1 ψ ψ.contDiff ψ.hasCompactSupport
  let gbase := chartBoundaryLpPullbackFull e Ω C 𝕜 1 g
  let gflat := baseToFlatBoundaryLI m 𝕜 1 gbase
  obtain ⟨u,hu⟩ := hsurj gflat
  let w := halfEvenReflection m 𝕜 1 u
  have hRw : sobolevRestrict (halfSpace m) w = u := by
    apply sobolevUnderlying_injective (halfSpace m) 1 1
    apply Lp.ext
    exact (P102.U4.domainLpRestrict_ae (halfSpace m) (sobolevUnderlying w)).trans
      (halfEvenReflection_restrict m 𝕜 1 u)
  let z := wholeCutoffSupportedCLM (ψ : Space (m + 1) → ℝ) J (Subset.rfl) Mψ hMψ w
  let v := unflattenSupportedCLM e (flatCoordinates m) Ω C 1 J hJ z
  let P := chartPushforwardCompact e (flatCoordinates m) Ω C J hJ
  have hP : (P : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C :=
    chartPushforwardCompact_subset e (flatCoordinates m) Ω C J hJ
  have hvP : ∀ᵐ x ∂volume.restrict (Ω : Set (Space (m + 1))),
      x ∉ P → sobolevUnderlying v x = 0 :=
    unflattenSupportedCLM_zero_off_compact e (flatCoordinates m) Ω C 1 J hJ z
  let PK : Compacts (Space (m + 1)) := ⟨(P : Set (Space (m + 1))) ∪ (K : Set (Space (m + 1))),P.isCompact.union K.isCompact⟩
  have hPK : (PK : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C :=
    union_subset hP hK
  obtain ⟨ρ,_,N,hPKN,_,hρone⟩ := cutoff (m + 1) (fullPhysicalChartOpen e C) PK hPK
  let Kρ : Compacts (Space (m + 1)) := ⟨tsupport ρ,ρ.hasCompactSupport⟩
  have hKρ : (Kρ : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C := ρ.tsupport_subset
  obtain ⟨Mρ,hMρ,hTρ⟩ := exists_sobolevCutoffCLM hCutoff e hΩ (by simp)
    T hT ρ ρ.contDiff ρ.hasCompactSupport
  have hMv : Mρ v = v := by
    apply sobolevUnderlying_injective Ω 1 1
    apply Lp.ext
    filter_upwards [hMρ v,hvP] with x hx hxP
    rw [hx]
    by_cases hxp : x ∈ P
    · rw [hρone x (hPKN (Or.inl hxp)),one_smul]
    · rw [hxP hxp,smul_zero]
  let vρ := cutoffSupportedCLM Ω 1 Kρ ρ (Subset.rfl) Mρ hMρ v
  have hvρ : vρ.val = unflattenSupportedCLM e (flatCoordinates m) Ω C 1 J hJ z := hMv
  have hrecovery := flattenHalf_unflatten_recovery e Ω C 1 J hJ z Kρ hKρ vρ hvρ
  have hident := congrArg (fun A : Sobolev 𝕜 Ω 1 1 →L[𝕜] DomainLp 𝕜 (⊤ : Opens (Space m)) 1 => A v)
    (local_trace_identification_of_density hDensity e Ω hΩ C 1 (by simp) Kρ hKρ
      ρ ρ.contDiff (Subset.rfl) Mρ hMρ T hT Tflat hflat)
  change flatBoundaryToBaseLI m 𝕜 1 (Tflat (flattenHalfSupportedCLM e Ω C 1 Kρ hKρ vρ)) =
    chartBoundaryLpPullbackFull e Ω C 𝕜 1 (T (Mρ v)) at hident
  rw [hrecovery,hMv] at hident
  have hcut := congrArg (fun A : Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 1 →L[𝕜]
      DomainLp 𝕜 (⊤ : Opens (Space m)) 1 => A w)
    (flat_trace_whole_cutoff_commutes 1 ψ ψ.continuous 1 hψB (by simp)
      ψ.contDiff Mψ hMψ Tflat hflat)
  change flatBoundaryToBaseLI m 𝕜 1 (Tflat (sobolevRestrict (halfSpace m) (Mψ w))) =
    flatFaceMultiplier 1 ψ ψ.continuous 1 hψB
      (flatBoundaryToBaseLI m 𝕜 1 (Tflat (sobolevRestrict (halfSpace m) w))) at hcut
  rw [hRw,hu] at hcut
  simp only [gflat, flatBoundaryToBaseLI_baseToFlatBoundaryLI] at hcut
  have hfix := flatFaceMultiplier_fixes_supported_pullback e Ω C 1 K hK g hg ψ ψ.continuous 1 hψB hψQ
  have hPB : chartBoundaryLpPullbackFull e Ω C 𝕜 1 (T v) = chartBoundaryLpPullbackFull e Ω C 𝕜 1 g :=
    hident.symm.trans (hcut.trans hfix)
  have htrace := hTρ v
  rw [hMv] at htrace
  have hdiff : ∀ᵐ x ∂boundaryMeasure Ω,
      x ∉ fullPhysicalChartOpen e C → (T v - g) x = 0 := by
    filter_upwards [htrace,hg,Lp.coeFn_sub (T v) g] with x hx hgx hsub hxout
    have hρzero : ρ x = 0 := image_eq_zero_of_notMem_tsupport (fun hxs => hxout (ρ.tsupport_subset hxs))
    have hgzero : g x = 0 := hgx (fun hxK => hxout (hK hxK))
    rw [hsub,Pi.sub_apply,hx,hρzero,zero_smul,hgzero,sub_self]
  have hdiffzero : T v - g = 0 :=
    (chartBoundaryLpPullbackFull_eq_zero_iff_of_supported e Ω C 1 (T v - g) hdiff).mp (by
      rw [map_sub,hPB,sub_self])
  exact ⟨v,sub_eq_zero.mp hdiffzero⟩

theorem boundaryCutoff_memLp {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space (m + 1))}
    (χ : Space (m + 1) → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (g : BoundaryLp 𝕜 Ω 1) :
    MemLp (fun x => χ x • g x) 1 (boundaryMeasure Ω) := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hχ
  have htop : MemLp χ ∞ (boundaryMeasure Ω) :=
    memLp_top_of_bound hχ.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  exact htop.smul (Lp.memLp g)

set_option maxHeartbeats 1600000 in
theorem endpointSurjectivity_of_supported_chart_lifts
    (hCutoff : Expected.CutoffCompatibility)
    (hEndpoint : Expected.EndpointIdentification)
    (hTrace : Expected.TraceExists)
    (hUnique : Expected.TraceUniqueness)
    (hLocal : ∀ (m : ℕ), 1 ≤ m →
      ∀ (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1))),
      IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)) →
      ∀ (𝕜 : Type) [RCLike 𝕜]
        (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
        (K : Compacts (Space (m + 1))),
      (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C →
      ∀ (T : Sobolev 𝕜 Ω 1 1 →L[𝕜] BoundaryLp 𝕜 Ω 1), IsTrace T →
      ∀ g : BoundaryLp 𝕜 Ω 1,
      (∀ᵐ x ∂boundaryMeasure Ω, x ∉ K → g x = 0) →
        ∃ u : Sobolev 𝕜 Ω 1 1, T u = g) :
    Expected.EndpointSurjectivity := by
  classical
  intro m
  by_cases hm0 : m = 0
  · subst m
    exact endpoint_surjectivity_oneDimension_conditional hCutoff hEndpoint hTrace hUnique
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  intro e Ω hΩ 𝕜 _
  obtain ⟨_, _, T, hT, _, _⟩ := hTrace m e Ω hΩ 𝕜 1 (by simp)
  obtain ⟨n, C, χ, hχ, hsum, hinter, hboundary⟩ := exists_physical_partition e hΩ
  have hsurj : Function.Surjective T := by
    intro g
    let K (i : Fin n) : Compacts (Space (m + 1)) :=
      ⟨tsupport (χ i.succ), (hχ i.succ).2.1⟩
    have hmem (i : Fin n) :
        MemLp (fun x => χ i.succ x • g x) 1 (boundaryMeasure Ω) :=
      boundaryCutoff_memLp (χ i.succ) (hχ i.succ).1.continuous (hχ i.succ).2.1 g
    let parts (i : Fin n) : BoundaryLp 𝕜 Ω 1 :=
      (hmem i).toLp (fun x => χ i.succ x • g x)
    have hparts (i : Fin n) :
        (parts i : Space (m + 1) → 𝕜) =ᵐ[boundaryMeasure Ω]
          (fun x => χ i.succ x • g x) := (hmem i).coeFn_toLp
    have hsupport (i : Fin n) :
        ∀ᵐ x ∂boundaryMeasure Ω, x ∉ K i → parts i x = 0 := by
      filter_upwards [hparts i] with x hx hxK
      rw [hx, image_eq_zero_of_notMem_tsupport hxK, zero_smul]
    have hlift (i : Fin n) : ∃ u : Sobolev 𝕜 Ω 1 1, T u = parts i :=
      hLocal m hm e Ω hΩ 𝕜 (C i) (K i) (hboundary i) T hT (parts i) (hsupport i)
    choose lifts hlifts using hlift
    have hpartsSum : ∑ i, parts i = g := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_finsetSum Finset.univ parts, ae_all_iff.mpr hparts,
        ae_restrict_mem measurableSet_frontier] with x hx hpx hxFront
      rw [hx]
      simp only [Finset.sum_apply]
      simp_rw [hpx]
      rw [← Finset.sum_smul]
      have hzero : χ 0 x = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hxS
        exact hxFront.2 (by rw [Ω.isOpen.interior_eq]; exact hinter hxS)
      have hsum' := hsum x (frontier_subset_closure hxFront)
      rw [Fin.sum_univ_succ, hzero, zero_add] at hsum'
      rw [hsum', one_smul]
    refine ⟨∑ i, lifts i, ?_⟩
    rw [map_sum]
    simp_rw [hlifts]
    exact hpartsSum
  obtain ⟨B, hB, hpre⟩ := T.exists_preimage_norm_le hsurj
  refine ⟨B, hB.le, ⟨T, hT⟩, ?_⟩
  intro S hS g
  have hST := hUnique m e Ω hΩ 𝕜 1 (by simp) S T hS hT
  rw [hST]
  exact hpre g

/-- Quantitative surjectivity of the same physical trace at p=1, under
exactly the four ordered frozen trace-map premises. -/
theorem endpoint_surjectivity_conditional
    (hCutoff : Expected.CutoffCompatibility)
    (hEndpoint : Expected.EndpointIdentification)
    (hTrace : Expected.TraceExists)
    (hUnique : Expected.TraceUniqueness) : Expected.EndpointSurjectivity := by
  apply endpointSurjectivity_of_supported_chart_lifts hCutoff hEndpoint hTrace hUnique
  intro m hm e Ω hΩ 𝕜 _ C K hK T hT g hg
  obtain ⟨_, _, Tf, _, hSlices, hCompat⟩ := flat_trace_exists m hm 𝕜 1 (by simp)
  have hIsFlat : P102.Trace.IsFlatTrace Tf := by
    intro u
    obtain ⟨F, hF, hF0, _⟩ := hSlices u
    exact ⟨F, hF, hF0⟩
  obtain ⟨_, _, hLift⟩ := flat_trace_lift.2 m hm
  have hsurj : Function.Surjective Tf := by
    intro f
    obtain ⟨u, hu, _⟩ := (hLift 𝕜).2 Tf hIsFlat f
    exact ⟨u, hu⟩
  exact local_endpoint_lift_of_flat_surjective hCutoff
    (ambient_smooth_density_conditional hCutoff hEndpoint hTrace hUnique)
    e Ω hΩ C T hT Tf hCompat hsurj K hK g hg

/-- The full original ordinary-trace proposition, derived conditionally
from exactly the ordered frozen premises. This helper is distinct from the
original target, whose closed wrapper belongs to the owner after closure. -/
theorem ordinary_trace_conditional
    (hCutoff : Expected.CutoffCompatibility)
    (hEndpoint : Expected.EndpointIdentification)
    (hTrace : Expected.TraceExists)
    (hUnique : Expected.TraceUniqueness) : Expected.OrdinaryTrace :=
  ⟨hTrace, kernel_conditional hCutoff hEndpoint hTrace hUnique,
    zero_extension_criterion_conditional hCutoff hEndpoint hTrace hUnique,
    endpoint_surjectivity_conditional hCutoff hEndpoint hTrace hUnique,
    hEndpoint, bulk_extension_conditional hCutoff hEndpoint hTrace hUnique⟩

end P102.Trace.Ordinary

/-- Ordinary trace, its kernel and zero-extension criterion, the endpoint
lifting theorem, and bounded linear bulk extension on bounded Lipschitz opens. -/
theorem P102.Trace.Ordinary.ordinary_trace : P102.Trace.Ordinary.Expected.OrdinaryTrace :=
  P102.Trace.Ordinary.ordinary_trace_conditional
    P102.Trace.Ordinary.cutoff_compatibility
    P102.Trace.Ordinary.endpoint_identification
    P102.Trace.Ordinary.trace_exists
    P102.Trace.Ordinary.trace_uniqueness
