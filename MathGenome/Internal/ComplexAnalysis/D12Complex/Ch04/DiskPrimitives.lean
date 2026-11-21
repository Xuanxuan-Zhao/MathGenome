import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.DiskPrimitives
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.WeakGoursat
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.TrianglePrimitiveCriterion
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PrimitivePeriodCriterion

/-! The disk primitive theorem, paper.tex:875–903. Weak Goursat gives
zero triangle integrals; the continuous triangle criterion constructs the
radial primitive. The rectifiable endpoint theorem then annihilates every
closed rectifiable integral, including non-AC parametrizations. -/

noncomputable section
open Set Metric

namespace D12Complex.DiskPrimitives

/-- The two upstream segment parametrizations are the same directed path. -/
theorem goursat_segmentPath_eq (a b : ℂ) :
    WeakGoursat.segmentPath a b = D12Complex.segmentPath a b := by
  apply Subtype.ext
  have hfun : (fun t : ℝ => a + t • (b - a)) = AffineMap.lineMap a b := by
    funext t
    simp [AffineMap.lineMap_apply_module', add_comm]
  simp only [WeakGoursat.segmentPath, D12Complex.segmentPath, hfun]

/-- Goursat in the canonical triangle-integral interface. -/
theorem holomorphic_zeroTriangleIntegrals {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn Ω f) : ZeroTriangleIntegrals Ω f := by
  intro a b c hT
  have h := WeakGoursat.goursat_triangle a b c Ω f hf hT
  change WeakGoursat.triangleBoundaryIntegral a b c f = 0 at h
  simpa only [WeakGoursat.triangleBoundaryIntegral, goursat_segmentPath_eq,
    D12Complex.triangleBoundaryIntegral, segmentIntegral] using h

/-- The construction works on every open convex set containing its basepoint. -/
theorem convex_radialPrimitive {Ω : Set ℂ} {a : ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn Ω f) (ha : a ∈ Ω) (hconv : Convex ℝ Ω) :
    HolomorphicOn Ω (radialPrimitive f a) ∧
      ∀ z ∈ Ω, HasDerivAt (radialPrimitive f a) (f z) z := by
  exact convex_triangle_primitive_criterion Ω a f hf.1 ha hconv
    (fun z hz => (hf.2 z hz).continuousAt.continuousWithinAt)
    (holomorphic_zeroTriangleIntegrals hf)

theorem disk_radialPrimitive :
    Specs.D12Complex.Ch04.DiskPrimitives.disk_radialPrimitive_type := by
  intro a r f hr hf
  exact convex_radialPrimitive hf (mem_ball_self hr) (convex_ball a r)

theorem disk_exists_primitive :
    Specs.D12Complex.Ch04.DiskPrimitives.disk_exists_primitive_type := by
  intro a r f hr hf
  obtain ⟨hF, hd⟩ := disk_radialPrimitive a r f hr hf
  exact ⟨radialPrimitive f a, hF, fun z hz => (hd z hz).deriv⟩

theorem disk_closed_rectifiable_integral :
    Specs.D12Complex.Ch04.DiskPrimitives.disk_closed_rectifiable_integral_type := by
  intro a r f hr hf γ hγ htrace hclosed
  obtain ⟨F, hF⟩ := disk_exists_primitive a r f hr hf
  rw [Primitives.rectifiable_endpoint (ball a r) f F
    (fun z hz => (hf.2 z hz).continuousAt.continuousWithinAt) hF γ hγ htrace,
    hclosed, sub_self]

theorem entire_radialPrimitive :
    Specs.D12Complex.Ch04.DiskPrimitives.entire_radialPrimitive_type := by
  intro a f hf
  obtain ⟨hF, hd⟩ := convex_radialPrimitive hf (mem_univ a) convex_univ
  exact ⟨hF, fun z => hd z (mem_univ z)⟩

theorem entire_exists_primitive :
    Specs.D12Complex.Ch04.DiskPrimitives.entire_exists_primitive_type := by
  intro f hf
  obtain ⟨hF, hd⟩ := entire_radialPrimitive 0 f hf
  exact ⟨radialPrimitive f 0, hF, fun z _ => (hd z).deriv⟩

theorem entire_closed_rectifiable_integral :
    Specs.D12Complex.Ch04.DiskPrimitives.entire_closed_rectifiable_integral_type := by
  intro f hf γ hγ hclosed
  obtain ⟨F, hF⟩ := entire_exists_primitive f hf
  rw [Primitives.rectifiable_endpoint univ f F
    (fun z hz => (hf.2 z hz).continuousAt.continuousWithinAt) hF γ hγ (subset_univ _),
    hclosed, sub_self]

end D12Complex.DiskPrimitives
