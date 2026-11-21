import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.AscoliConverseClassical
import MathGenome.Internal.PointSetTopology.D10Topology.Ch13.AscoliSufficiency
import MathGenome.Internal.PointSetTopology.D10Topology.Ch13.EvaluationParameter
import MathGenome.Internal.PointSetTopology.D10Topology.Ch13.FunctorialMaps
import MathGenome.Internal.PointSetTopology.D10Topology.Ch13.TopologyComparison
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.RealAndEuclideanCompactness

/-! Ascoli necessity and its compact-domain and real-vector corollaries.
Joint evaluation and the compact tube lemma give one neighborhood that works
for every member of a compact family. Evaluation images give the pointwise
compactness. The uniform-topology results then use the established equality
with compact-open on compact domains; no completeness of the target is used. -/
noncomputable section
open Set Filter
open scoped Topology
universe u v
namespace D10Topology.Ch13

variable {X : Type u} {Y : Type v}

/-- A compact compact-open family on an LCH domain is equicontinuous. -/
theorem compact_family_equicontinuous [TopologicalSpace X] [MetricSpace Y]
    (hX : Ch11.LCH X) (H : Set (ContinuousMaps X Y))
    (hH : @IsCompact _ compactOpenContinuousTopology H) : Equicontinuous H := by
  rw [compactOpenContinuousTopology_eq_mathlib] at hH
  have heval := joint_evaluation_continuous (Y := Y) hX
  rw [compactOpenContinuousTopology_eq_mathlib] at heval
  intro x ε hε
  have hd : Continuous (fun p : X × ContinuousMaps X Y => dist (p.2 p.1) (p.2 x)) :=
    (heval.comp continuous_swap).dist ((continuous_eval_const x).comp continuous_snd)
  have hopen : IsOpen {p : X × ContinuousMaps X Y | dist (p.2 p.1) (p.2 x) < ε} :=
    isOpen_lt hd continuous_const
  have hU : ∀ᶠ y in 𝓝 x, ∀ f ∈ H, dist (f y) (f x) < ε :=
    hH.eventually_forall_of_forall_eventually (fun f _ =>
      hopen.mem_nhds (by simpa using hε))
  exact ⟨_, hU, fun _ hy _ hf => hy _ hf⟩

/-- No local compactness is needed for the pointwise condition. -/
theorem compact_family_pointwiseRelativelyCompact [TopologicalSpace X] [MetricSpace Y]
    (H : Set (ContinuousMaps X Y))
    (hH : @IsCompact _ compactOpenContinuousTopology H) :
    PointwiseRelativelyCompact H := by
  rw [compactOpenContinuousTopology_eq_mathlib] at hH
  intro x
  exact (hH.image (continuous_eval_const x)).closure

theorem ascoli_converse [TopologicalSpace X] [MetricSpace Y]
    (hX : Ch11.LCH X) (A : Set (ContinuousMaps X Y))
    (hA : @IsCompact _ compactOpenContinuousTopology
      (@closure _ compactOpenContinuousTopology A)) :
    Equicontinuous A ∧ PointwiseRelativelyCompact A := by
  letI : TopologicalSpace (ContinuousMaps X Y) := compactOpenContinuousTopology
  have he := compact_family_equicontinuous hX _ hA
  have hp := compact_family_pointwiseRelativelyCompact _ hA
  constructor
  · intro x ε hε
    obtain ⟨U, hU, hh⟩ := he x ε hε
    exact ⟨U, hU, fun y hy f hf => hh y hy f (subset_closure hf)⟩
  · intro x
    exact (hp x).of_isClosed_subset isClosed_closure
      (closure_mono (image_mono subset_closure))

theorem compactDomain_ascoli_iff [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MetricSpace Y] (A : Set (ContinuousMaps X Y)) :
    @IsCompact _ uniformContinuousTopology (@closure _ uniformContinuousTopology A) ↔
      Equicontinuous A ∧ PointwiseRelativelyCompact A := by
  rw [← compactDomain_continuousTopologies_eq.2]
  constructor
  · exact ascoli_converse
      ⟨Ch11.locallyCompact_of_mathlib_locallyCompactSpace X inferInstance, inferInstance⟩ A
  · rintro ⟨he, hp⟩
    exact ascoli_sufficiency A he hp

theorem compactMetric_ascoli_iff [MetricSpace X] [CompactSpace X] [MetricSpace Y]
    (A : Set (ContinuousMaps X Y)) :
    @IsCompact _ uniformContinuousTopology (@closure _ uniformContinuousTopology A) ↔
      Equicontinuous A ∧ PointwiseRelativelyCompact A := compactDomain_ascoli_iff A

theorem euclidean_pointwiseRelativelyCompact_iff_bounded [TopologicalSpace X] (m : ℕ)
    (A : Set (ContinuousMaps X (EuclideanSpace ℝ (Fin m)))) :
    PointwiseRelativelyCompact A ↔
      ∀ x : X, ∃ R : ℝ, ∀ f ∈ A, ‖f x‖ ≤ R := by
  constructor
  · intro h x
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp (h x).isBounded
    exact ⟨R, fun f hf => hR _ (subset_closure (mem_image_of_mem _ hf))⟩
  · intro h x
    obtain ⟨R, hR⟩ := h x
    apply (isBounded_iff_forall_norm_le.mpr ?_).isCompact_closure
    exact ⟨R, by rintro _ ⟨f, hf, rfl⟩; exact hR f hf⟩

theorem classical_ascoli_iff [TopologicalSpace X] [CompactSpace X] [T2Space X] (m : ℕ)
    (A : Set (ContinuousMaps X (EuclideanSpace ℝ (Fin m)))) :
    @IsCompact _ uniformContinuousTopology (@closure _ uniformContinuousTopology A) ↔
      Equicontinuous A ∧ (∀ x : X, ∃ R : ℝ, ∀ f ∈ A, ‖f x‖ ≤ R) := by
  rw [compactDomain_ascoli_iff, euclidean_pointwiseRelativelyCompact_iff_bounded]

theorem classical_compact_iff_closed [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (m : ℕ) (A : Set (ContinuousMaps X (EuclideanSpace ℝ (Fin m))))
    (he : Equicontinuous A) (hp : ∀ x : X, ∃ R : ℝ, ∀ f ∈ A, ‖f x‖ ≤ R) :
    @IsCompact _ uniformContinuousTopology A ↔ @IsClosed _ uniformContinuousTopology A := by
  have ht := compactDomain_continuousTopologies_eq (X := X)
    (Y := EuclideanSpace ℝ (Fin m)) |>.2
  rw [← ht, compactOpenContinuousTopology_eq_mathlib]
  have hc := (classical_ascoli_iff m A).mpr ⟨he, hp⟩
  rw [← ht, compactOpenContinuousTopology_eq_mathlib] at hc
  exact ⟨fun h => h.isClosed, fun h => h.closure_eq ▸ hc⟩

/-- A common finite Lipschitz constant supplies the common neighborhoods. -/
theorem common_lipschitz_equicontinuous [MetricSpace X] [MetricSpace Y]
    (A : Set (ContinuousMaps X Y)) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ f ∈ A, ∀ x y, dist (f x) (f y) ≤ L * dist x y) :
    Equicontinuous A := by
  intro x ε hε
  have hLp : 0 < L + 1 := by linarith
  refine ⟨Metric.ball x (ε / (L + 1)), Metric.ball_mem_nhds x (div_pos hε hLp), ?_⟩
  intro y hy f hf
  have hy' : dist y x < ε / (L + 1) := hy
  calc
    dist (f y) (f x) ≤ L * dist y x := hLip f hf y x
    _ ≤ (L + 1) * dist y x := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    _ < ε := by simpa only [mul_comm] using (lt_div_iff₀ hLp).mp hy'

theorem interval_lipschitz_compact_closure (a b : ℝ) (m : ℕ)
    (A : Set (ContinuousMaps (Icc a b) (EuclideanSpace ℝ (Fin m))))
    (R L : ℝ) (hL : 0 ≤ L) (hBound : ∀ f ∈ A, ∀ x, ‖f x‖ ≤ R)
    (hLip : ∀ f ∈ A, ∀ x y, dist (f x) (f y) ≤ L * dist x y) :
    @IsCompact _ uniformContinuousTopology (@closure _ uniformContinuousTopology A) := by
  exact (classical_ascoli_iff m A).mpr
    ⟨common_lipschitz_equicontinuous A L hL hLip,
      fun x => ⟨R, fun f hf => hBound f hf x⟩⟩

end D10Topology.Ch13
