import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.Morera
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.TrianglePrimitiveCriterion
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.DiskPrimitives
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.DiskCauchyDerivatives
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.ContinuousExceptionalPoint

/-! Morera's theorem and continuous gluing across one point (D12.04.08).
On each disk, the triangle criterion constructs a genuine primitive F with
F' = f. Holomorphy of F' follows from the upstream all-derivatives theorem.
The exceptional-point triangle lemma then gives the corollary. -/

noncomputable section
open Set Metric Filter
open scoped Topology

namespace D12Complex.Morera

theorem morera : Specs.D12Complex.Ch04.Morera.morera_type := by
  intro Ω f hΩ hf htri
  refine ⟨hΩ, ?_⟩
  intro z hz
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hΩ z hz
  have hlocal : ZeroTriangleIntegrals (ball z r) f :=
    fun a b c hT => htri a b c (hT.trans hsub)
  obtain ⟨hF, hd⟩ := convex_triangle_primitive_criterion (ball z r) z f
    isOpen_ball (mem_ball_self hr) (convex_ball z r) (hf.mono hsub) hlocal
  have hF' : HolomorphicOn (ball z r) (deriv (radialPrimitive f z)) := by
    simpa only [iteratedDeriv_one] using
      (DiskCauchyDerivatives.holomorphicOn_iteratedDeriv (ball z r)
        (radialPrimitive f z) hF 1).1
  apply (hF'.2 z (mem_ball_self hr)).congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with w hw
  exact (hd w hw).deriv.symm

theorem continuous_point_gluing :
    Specs.D12Complex.Ch04.Morera.continuous_point_gluing_type := by
  intro Ω p f hΩ hf hd
  apply morera Ω f hΩ hf
  intro a b c hT
  have h := ContinuousExceptionalPoint.goursat_triangle a b c p Ω f hΩ hf hd hT
  change WeakGoursat.triangleBoundaryIntegral a b c f = 0 at h
  simpa only [WeakGoursat.triangleBoundaryIntegral,
    DiskPrimitives.goursat_segmentPath_eq, D12Complex.triangleBoundaryIntegral,
    segmentIntegral] using h

end D12Complex.Morera
