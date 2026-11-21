import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.BaireOneContinuity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07Baire
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic.Linarith

/-!
# Continuity points of a Baire first-class function

Theorem `fa2:p1:baire-one` (paper.tex:6572–6577).
For each positive ε, the closed sets on which a tail stays within ε/4 of
its first term cover the space. Their interiors have dense union by Baire.
Continuity of that first term gives neighborhoods on which the limit has
diameter less than ε. Intersecting these open dense sets for ε = 1/(n+1)
gives continuity points. The full continuity set is Gδ by the general
metric-codomain theorem.
-/

open Set Filter TopologicalSpace
open scoped Topology

universe u

namespace ExpandedFA.Supplements.BaireOneContinuity

variable {X : Type u} [MetricSpace X]

/-- Points admitting an open neighborhood on which the image has diameter < ε. -/
private def smallOscillation (f : X → ℝ) (ε : ℝ) : Set X :=
  {x | ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∀ y ∈ U, ∀ z ∈ U, dist (f y) (f z) < ε}

private theorem isOpen_smallOscillation (f : X → ℝ) (ε : ℝ) :
    IsOpen (smallOscillation f ε) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨U, hU, hx, hdiam⟩
  exact mem_of_superset (hU.mem_nhds hx) (fun y hy => ⟨U, hU, hy, hdiam⟩)

/-- The closed tail-Cauchy cover makes every positive small-oscillation set dense. -/
private theorem dense_smallOscillation [BaireSpace X]
    (fseq : ℕ → X → ℝ) (f : X → ℝ)
    (hc : ∀ n, Continuous (fseq n))
    (hlim : ∀ x, Tendsto (fun n => fseq n x) atTop (𝓝 (f x)))
    {ε : ℝ} (hε : 0 < ε) : Dense (smallOscillation f ε) := by
  let E : ℕ → Set X := fun N =>
    {x | ∀ n, N ≤ n → dist (fseq n x) (fseq N x) ≤ ε / 4}
  have hclosed : ∀ N, IsClosed (E N) := by
    intro N
    simp only [E, ofPred_forall]
    exact isClosed_iInter fun n => isClosed_iInter fun _ =>
      isClosed_le ((hc n).dist (hc N)) continuous_const
  have hcover : (⋃ N, E N) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp (hlim x).cauchySeq
      (ε / 4) (by linarith)
    exact mem_iUnion.mpr ⟨N, fun n hn => (hN n hn).le⟩
  have hbound (N : ℕ) (y : X) (hy : y ∈ E N) :
      dist (f y) (fseq N y) ≤ ε / 4 := by
    apply le_of_tendsto ((hlim y).dist tendsto_const_nhds)
    exact eventually_atTop.mpr ⟨N, fun n hn => hy n hn⟩
  apply (dense_iUnion_interior_of_closed hclosed hcover).mono
  intro x hx
  obtain ⟨N, hx⟩ := mem_iUnion.mp hx
  let V := interior (E N) ∩ (fseq N) ⁻¹' Metric.ball (fseq N x) (ε / 8)
  have hV : IsOpen V := isOpen_interior.inter (Metric.isOpen_ball.preimage (hc N))
  have hxV : x ∈ V := ⟨hx, by simpa using (show (0 : ℝ) < ε / 8 by linarith)⟩
  refine ⟨V, hV, hxV, ?_⟩
  intro y hy z hz
  have hybound := hbound N y (interior_subset hy.1)
  have hzbound := hbound N z (interior_subset hz.1)
  have hydist : dist (fseq N y) (fseq N x) < ε / 8 := hy.2
  have hzdist : dist (fseq N z) (fseq N x) < ε / 8 := hz.2
  have hmiddle := dist_triangle (fseq N y) (fseq N x) (fseq N z)
  have htotal := dist_triangle4 (f y) (fseq N y) (fseq N z) (f z)
  rw [dist_comm (fseq N x) (fseq N z)] at hmiddle
  rw [dist_comm (fseq N z) (f z)] at htotal
  linarith

/-- Membership in every small-oscillation set forces continuity. -/
private theorem continuousAt_of_smallOscillation (f : X → ℝ) {x : X}
    (hx : x ∈ ⋂ n : ℕ, smallOscillation f (1 / (n + 1 : ℝ))) :
    ContinuousAt f x := by
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  obtain ⟨U, hU, hxU, hdiam⟩ := mem_iInter.mp hx n
  exact mem_of_superset (hU.mem_nhds hxU) fun y hy => (hdiam y hy x hxU).trans hn

/-- The full continuity set of the pointwise limit is dense and Gδ. -/
theorem continuityPoints_dense_isGDelta [CompleteSpace X]
    (fseq : ℕ → X → ℝ) (f : X → ℝ)
    (hc : ∀ n, Continuous (fseq n))
    (hlim : ∀ x, Tendsto (fun n => fseq n x) atTop (𝓝 (f x))) :
    Dense {x | ContinuousAt f x} ∧ IsGδ {x | ContinuousAt f x} := by
  let : BaireSpace X := ExpandedFA.P1.C07Baire.baireSpace_of_completeMetric X
  refine ⟨?_, IsGδ.setOfPred_continuousAt f⟩
  have hd : Dense (⋂ n : ℕ, smallOscillation f (1 / (n + 1 : ℝ))) :=
    dense_iInter_of_isOpen_nat (fun _ => isOpen_smallOscillation f _)
      (fun n => dense_smallOscillation fseq f hc hlim (by positivity))
  exact hd.mono fun _ hx => continuousAt_of_smallOscillation f hx

end ExpandedFA.Supplements.BaireOneContinuity
