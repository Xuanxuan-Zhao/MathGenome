import MathGenome.Internal.MultivariableAnalysis.D04CornerCompletion.VertexCurveDerivative
import MathGenome.Internal.MultivariableAnalysis.Specs.D04CornerCompletion.NoVertexChart
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
open Set Filter Topology
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open scoped ContDiff

namespace D04CornerCompletion

/-- A coordinate direction parallel to the bounding hyperplane gives a two-sided
line in either model space. No centering assumption is needed for this fact. -/
private theorem model_line_direction {n : ℕ} (hn : 2 ≤ n) (half : Bool)
    (u : E n) (hu : u ∈ parameterSpace n half) :
    ∃ w : E n, w ≠ 0 ∧ ∀ t : ℝ, u + t • w ∈ parameterSpace n half := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 2 := ⟨n - 2, by omega⟩
  let w : E (d + 2) := WithLp.toLp 2 (Pi.single (0 : Fin (d + 2)) (1 : ℝ))
  have hw0 : w (0 : Fin (d + 2)) = 1 := by simp [w]
  have hwlast : w (Fin.last (d + 1)) = 0 := by
    have hne : Fin.last (d + 1) ≠ (0 : Fin (d + 2)) := by
      intro h
      have := congrArg Fin.val h
      simp at this
    simp [w, hne]
  refine ⟨w, ?_, ?_⟩
  · intro h
    have := congrArg (fun x : E (d + 2) => x (0 : Fin (d + 2))) h
    simp [hw0] at this
  · intro t
    cases half with
    | false => simp [parameterSpace]
    | true =>
      have hu' : 0 ≤ u (Fin.last (d + 1)) := hu
      change 0 ≤ (u + t • w) (Fin.last (d + 1))
      simpa [hwlast] using hu'

/-- The local extension along a two-sided parameter line would have both zero
velocity at the box vertex and nonzero velocity by its injective derivative. -/
theorem no_centered_vertex_chart
    {n : ℕ} (hn : 2 ≤ n) (a b : E n)
    (hab : ∀ i : Fin n, a i < b i) (v : E n)
    (hv : IsBoxVertex a b v) :
    ¬ ∃ (c : EmbeddedChart (1 : ℕ∞ω) n n (box a b)) (u : E n),
      CenteredAt c u ∧ c.toFun u = v := by
  rintro ⟨c, u, hcenter, hcv⟩
  obtain ⟨O, hO, hsource⟩ := c.source_open
  have hu : u ∈ c.source := hcenter.1
  have huO : u ∈ O := (hsource ▸ hu).2
  have huP : u ∈ parameterSpace n c.half := (hsource ▸ hu).1
  obtain ⟨w, hw, hmodel⟩ := model_line_direction hn c.half u huP
  obtain ⟨W, g, hW, huW, heq, hg, hrank⟩ := c.regular u hu
  have hline : HasDerivAt (fun t : ℝ => u + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add u
  have htend : Tendsto (fun t : ℝ => u + t • w) (𝓝 0) (𝓝 u) := by
    simpa using hline.continuousAt.tendsto
  have hlocal : ∀ᶠ t in 𝓝 (0 : ℝ), u + t • w ∈ c.source ∩ W := by
    filter_upwards [htend.eventually (hO.mem_nhds huO),
      htend.eventually (hW.mem_nhds huW)] with t htO htW
    refine ⟨?_, htW⟩
    rw [hsource]
    exact ⟨hmodel t, htO⟩
  have hdiff : DifferentiableAt ℝ g u :=
    hg.differentiableOn_one.differentiableAt (hW.mem_nhds huW)
  have hcurve : HasDerivAt (fun t : ℝ => g (u + t • w))
      ((fderiv ℝ g u) w) 0 := by
    exact hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hg0 : g (u + (0 : ℝ) • w) = v := by
    simpa using (heq ⟨hu, huW⟩).trans hcv
  have hbox : ∀ᶠ t in 𝓝 (0 : ℝ), g (u + t • w) ∈ box a b := by
    filter_upwards [hlocal] with t ht
    rw [heq ht]
    exact (c.map_source ht.1).1
  have hzero := vertex_curve_derivative_zero hn a b hab v hv
    (fun t : ℝ => g (u + t • w)) ((fderiv ℝ g u) w) hcurve hg0 hbox
  exact hw ((hrank u huW) (by simpa using hzero))

end D04CornerCompletion
