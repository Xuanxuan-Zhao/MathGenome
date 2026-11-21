import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch16.Complete
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch16.Equicontinuity
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Bolzano
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.MetricCompactness
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.AscoliSubsequence
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Constructions
import Mathlib.Tactic.Linarith

namespace SingleVariableAnalysis
open scoped Topology
open Filter

/-- Countable-coordinate compactness supplies the diagonal extraction.
Only the scalar value bounds are used here, without equicontinuity. -/
theorem ascoli_countable_extraction :
    Specs.SingleVariableAnalysis.Ch16.AscoliSubsequence.countableExtraction := by
  intro E _ _ K F D hD hb
  classical
  let : Countable D := hD.to_subtype
  obtain ⟨M, hM, hbound⟩ := hb
  let B := Metric.closedBall (0 : E) M
  let : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 M)
  let u : ℕ → (D → B) := fun n x => ⟨F n x.val, by
    change dist (F n x.val) 0 ≤ M
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      hbound (F n) ⟨n, rfl⟩ x.val⟩
  obtain ⟨L, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq u
  refine ⟨φ, hφ, fun x => (L x).val, fun x => ?_⟩
  exact (continuous_subtype_val.tendsto (L x)).comp ((tendsto_pi_nhds.mp hlim) x)

/-- A common modulus and Cauchy values on a dense set imply uniform Cauchyness.
Compactness selects finitely many centers from that same dense set. -/
theorem ascoli_uniformCauchy_from_dense :
    Specs.SingleVariableAnalysis.Ch16.AscoliSubsequence.uniformCauchyFromDense := by
  intro E _ K _ F D hD heq hc ε hε
  classical
  obtain ⟨δ, hδ, hmod⟩ := heq (ε / 3) (by linarith)
  have hcover : Set.univ ⊆ ⋃ y : D, Metric.ball y.val δ := by
    intro x _
    obtain ⟨y, hxy, hy⟩ := Metric.dense_iff.mp hD x δ hδ
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, by simpa only [Metric.mem_ball, dist_comm] using hxy⟩
  obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (Set.univ : Set K)).elim_finite_subcover
    (fun y : D => Metric.ball y.val δ) (fun _ => Metric.isOpen_ball) hcover
  have hcenters : ∀ y : D, ∃ N : ℕ,
      ∀ n ≥ N, ∀ m ≥ N, ‖F n y.val - F m y.val‖ < ε / 3 := by
    intro y
    simpa only [dist_eq_norm] using Metric.cauchySeq_iff.mp (hc y.val y.property)
      (ε / 3) (by linarith)
  choose N hN using hcenters
  refine ⟨t.sup N, ?_⟩
  intro m hm n hn x
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  have hNy : N y ≤ t.sup N := Finset.le_sup hy
  have hmid := hN y n (hNy.trans hn) m (hNy.trans hm)
  have hleft := hmod x y.val hxy (F n) ⟨n, rfl⟩
  have hright := hmod y.val x (by simpa only [Metric.mem_ball, dist_comm] using hxy) (F m) ⟨m, rfl⟩
  calc
    ‖F n x - F m x‖ ≤ ‖F n x - F n y.val‖ +
        ‖F n y.val - F m y.val‖ + ‖F m y.val - F m x‖ := by
      simpa only [dist_eq_norm] using
        dist_triangle4 (F n x) (F n y.val) (F m y.val) (F m x)
    _ < ε := by linarith

/-- The diagonal subsequence is uniformly Cauchy; completeness is not used yet. -/
theorem ascoli_subsequence_uniformCauchy {E : Type} [NormedAddCommGroup E]
    [ProperSpace E] (K : Set ℝ) [CompactSpace K] (F : ℕ → C(K, E))
    (hb : UniformlyBoundedFamily K (Set.range F))
    (heq : PointwiseEquicontinuousFamily K (Set.range F)) :
    ∃ D : Set K, D.Countable ∧ Dense D ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∃ L : D → E, ∀ x : D,
        Tendsto (fun n => F (φ n) x.val) atTop (𝓝 (L x))) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
        ∀ m ≥ N, ∀ n ≥ N, ∀ x : K, ‖F (φ n) x - F (φ m) x‖ < ε) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense K
  obtain ⟨φ, hφ, L, hL⟩ := ascoli_countable_extraction K F D hDc hb
  refine ⟨D, hDc, hDd, φ, hφ, ⟨L, hL⟩, ?_⟩
  have hU := compact_uniformEquicontinuity K
    (isCompact_iff_compactSpace.mpr inferInstance) (Set.range F) heq
  apply ascoli_uniformCauchy_from_dense K (fun n => F (φ n)) D hDd
  · intro ε hε
    obtain ⟨δ, hδ, hmod⟩ := hU ε hε
    refine ⟨δ, hδ, ?_⟩
    rintro x y hxy f ⟨n, rfl⟩
    exact hmod x y hxy (F (φ n)) ⟨φ n, rfl⟩
  · intro x hx
    exact (hL ⟨x, hx⟩).cauchySeq

/-- Real Arzelà–Ascoli, with the dense-set and Cauchy witnesses retained. -/
theorem real_ascoli_subsequence :
    Specs.SingleVariableAnalysis.Ch16.AscoliSubsequence.realAscoliSubsequence := by
  intro K _ F hb heq
  obtain ⟨D, hDc, hDd, φ, hφ, hL, hC⟩ :=
    ascoli_subsequence_uniformCauchy K F hb heq
  obtain ⟨f, hf⟩ := realSupSpace_complete K (fun n => F (φ n)) (by
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    exact ⟨N, fun m hm n hn =>
      ((F (φ n) - F (φ m)).norm_lt_iff hε).mpr (hN m hm n hn)⟩)
  refine ⟨D, hDc, hDd, φ, hφ, hL, ?_, f, ?_, hf⟩
  · simpa only [Real.norm_eq_abs] using hC
  · exact (realSupSpace_norm_converges_iff_uniform K (fun n => F (φ n)) f).mp hf

/-- Complex Arzelà–Ascoli uses the same metric argument and complex completeness. -/
theorem complex_ascoli_subsequence :
    Specs.SingleVariableAnalysis.Ch16.AscoliSubsequence.complexAscoliSubsequence := by
  intro K _ F hb heq
  obtain ⟨D, hDc, hDd, φ, hφ, hL, hC⟩ :=
    ascoli_subsequence_uniformCauchy K F hb heq
  obtain ⟨f, hf⟩ := complexSupSpace_complete K (fun n => F (φ n)) (by
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    exact ⟨N, fun m hm n hn =>
      ((F (φ n) - F (φ m)).norm_lt_iff hε).mpr (hN m hm n hn)⟩)
  exact ⟨D, hDc, hDd, φ, hφ, hL, hC, f,
    (complexSupSpace_norm_converges_iff_uniform K (fun n => F (φ n)) f).mp hf, hf⟩

end SingleVariableAnalysis
