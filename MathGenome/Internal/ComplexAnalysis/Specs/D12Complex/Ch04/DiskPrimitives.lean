import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PrimitivePeriodCriterion
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.TrianglePrimitiveCriterion
import Mathlib.Analysis.Normed.Module.Convex

/-! Independent statements for the primitive and closed-path part of
paper.tex:875–903 (D12.04.02). Holomorphy is pointwise complex
differentiability. The rectifiable integral is the canonical Stieltjes
integral, with no absolute continuity assumption on the parametrization.
The unbounded disk is represented by the whole plane. -/

noncomputable section
open Set Metric

namespace Specs.D12Complex.Ch04.DiskPrimitives
open _root_.D12Complex

def disk_radialPrimitive_type : Prop :=
  ∀ (a : ℂ) (r : ℝ) (f : ℂ → ℂ), 0 < r → HolomorphicOn (ball a r) f →
    HolomorphicOn (ball a r) (radialPrimitive f a) ∧
      ∀ z ∈ ball a r, HasDerivAt (radialPrimitive f a) (f z) z

def disk_exists_primitive_type : Prop :=
  ∀ (a : ℂ) (r : ℝ) (f : ℂ → ℂ), 0 < r → HolomorphicOn (ball a r) f →
    ∃ F, Ch03.PrimitivePeriodCriterion.IsPrimitive_value (ball a r) f F

def disk_closed_rectifiable_integral_type : Prop :=
  ∀ (a : ℂ) (r : ℝ) (f : ℂ → ℂ), 0 < r → HolomorphicOn (ball a r) f →
    ∀ γ : ComplexPath, Stieltjes.Rectifiable γ → γ.trace ⊆ ball a r →
      γ.IsClosed → Stieltjes.contourIntegral γ f = 0

def entire_radialPrimitive_type : Prop :=
  ∀ (a : ℂ) (f : ℂ → ℂ), HolomorphicOn univ f →
    HolomorphicOn univ (radialPrimitive f a) ∧
      ∀ z : ℂ, HasDerivAt (radialPrimitive f a) (f z) z

def entire_exists_primitive_type : Prop :=
  ∀ f : ℂ → ℂ, HolomorphicOn univ f →
    ∃ F, Ch03.PrimitivePeriodCriterion.IsPrimitive_value univ f F

def entire_closed_rectifiable_integral_type : Prop :=
  ∀ f : ℂ → ℂ, HolomorphicOn univ f →
    ∀ γ : ComplexPath, Stieltjes.Rectifiable γ → γ.IsClosed →
      Stieltjes.contourIntegral γ f = 0

end Specs.D12Complex.Ch04.DiskPrimitives
