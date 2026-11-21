import MathGenome.Internal.LinearPDE.P201Specs.Common.SpatialInterfaces
import MathGenome.Internal.FourierSobolev.P102.Trace.GraphFractionalTransport

/-! Physical trace spaces for paper.tex, C02. The full bulk H¹ norm is
`P201Specs.H`; the positive-dimensional boundary norm is precisely the
MathGenome intrinsic sum norm. In dimension one only counting L² is used.
No existence, lifting, or kernel certificate is assumed in these definitions. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
open Set TopologicalSpace MeasureTheory MeasureTheory.Measure
open scoped ENNReal ContDiff
namespace P201Specs
namespace Trace
open P102.Trace.MeasuredFractional

/-- The exact-trace specialization s = 1 - 1/p at p = 2. -/
abbrev halfOrder : ℝ := 1 - 1 / (2 : ℝ≥0∞).toReal

@[simp] theorem halfOrder_eq : halfOrder = (1 / 2 : ℝ) := by norm_num [halfOrder]

variable {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)

theorem boundaryFinite (hΩ : IsBoundedLipschitzOpen Ω) : IsFiniteMeasure (boundaryMeasure Ω) :=
  ⟨P102.Trace.Ordinary.boundaryMeasure_univ_lt_top (graphFrame m) Ω hΩ⟩

abbrev BoundaryL2 := P102.Trace.Ordinary.BoundaryLp ℝ Ω 2

abbrev PairL2 := MeasureTheory.Lp ℝ 2
  (metricPairMeasure m (boundaryMeasure Ω) halfOrder 2)

abbrev GraphAmbient := WithLp 1 (BoundaryL2 Ω × PairL2 Ω)

/-- A graph over the actual surface L² quotient, with the weighted increment
as its second coordinate. The product has the sum norm. -/
def fractionalGraph (hΩ : IsBoundedLipschitzOpen Ω) : Submodule ℝ (GraphAmbient Ω) where
  carrier := {z | (z.ofLp.2 : Space (m + 1) × Space (m + 1) → ℝ) =ᵐ[
    metricPairMeasure m (boundaryMeasure Ω) halfOrder 2]
    metricIncrement (z.ofLp.1 : Space (m + 1) → ℝ)}
  zero_mem' := by
    haveI := boundaryFinite Ω hΩ
    change ((0 : PairL2 Ω) : P201Specs.Space (m + 1) × P201Specs.Space (m + 1) → ℝ) =ᵐ[_]
      metricIncrement ((0 : BoundaryL2 Ω) : P201Specs.Space (m + 1) → ℝ)
    apply Filter.EventuallyEq.trans (Lp.coeFn_zero _ _ _)
    have hz := (Lp.coeFn_zero ℝ 2 (boundaryMeasure Ω))
    have hh : metricIncrement (0 : Space (m + 1) → ℝ) =ᵐ[
        metricPairMeasure m (boundaryMeasure Ω) halfOrder 2]
        metricIncrement ((0 : BoundaryL2 Ω) : Space (m + 1) → ℝ) := by
      apply (metricPairMeasure_absolutelyContinuous (m := m) (s := halfOrder) (p := 2)).ae_le
      filter_upwards [quasiMeasurePreserving_fst.ae hz,
        quasiMeasurePreserving_snd.ae hz] with z hz1 hz2
      simp only [metricIncrement, hz1, hz2, Pi.zero_apply]
    have he : metricIncrement (0 : P201Specs.Space (m + 1) → ℝ) = 0 := by
      funext z; simp [metricIncrement]
    rwa [he] at hh
  add_mem' := by
    haveI := boundaryFinite Ω hΩ
    intro u v hu hv
    change (u.ofLp.2 : _ → ℝ) =ᵐ[_] metricIncrement (u.ofLp.1 : _ → ℝ) at hu
    change (v.ofLp.2 : _ → ℝ) =ᵐ[_] metricIncrement (v.ofLp.1 : _ → ℝ) at hv
    have hh := Lp.coeFn_add u.ofLp.1 v.ofLp.1
    have hp : metricIncrement ((u.ofLp.1 + v.ofLp.1 : BoundaryL2 Ω) : Space (m + 1) → ℝ) =ᵐ[
        metricPairMeasure m (boundaryMeasure Ω) halfOrder 2]
        metricIncrement (u.ofLp.1 : Space (m + 1) → ℝ) +
          metricIncrement (v.ofLp.1 : Space (m + 1) → ℝ) := by
      apply (metricPairMeasure_absolutelyContinuous (m := m) (s := halfOrder) (p := 2)).ae_le
      filter_upwards [quasiMeasurePreserving_fst.ae hh,
        quasiMeasurePreserving_snd.ae hh] with z hz1 hz2
      simp only [metricIncrement, hz1, hz2, Pi.add_apply]
      ring
    exact (Lp.coeFn_add u.ofLp.2 v.ofLp.2).trans ((hu.add hv).trans hp.symm)
  smul_mem' := by
    haveI := boundaryFinite Ω hΩ
    intro c u hu
    change (u.ofLp.2 : _ → ℝ) =ᵐ[_] metricIncrement (u.ofLp.1 : _ → ℝ) at hu
    have hh := Lp.coeFn_smul c u.ofLp.1
    have hp : metricIncrement ((c • u.ofLp.1 : BoundaryL2 Ω) : Space (m + 1) → ℝ) =ᵐ[
        metricPairMeasure m (boundaryMeasure Ω) halfOrder 2]
        c • metricIncrement (u.ofLp.1 : Space (m + 1) → ℝ) := by
      apply (metricPairMeasure_absolutelyContinuous (m := m) (s := halfOrder) (p := 2)).ae_le
      filter_upwards [quasiMeasurePreserving_fst.ae hh,
        quasiMeasurePreserving_snd.ae hh] with z hz1 hz2
      simp only [metricIncrement, hz1, hz2, Pi.smul_apply, smul_sub]
    exact (Lp.coeFn_smul c u.ofLp.2).trans ((hu.const_smul c).trans hp.symm)

/-- Boundary dimension zero is counting L². Positive boundary dimensions
use the physical fractional graph. This covers every ambient n ≥ 1. -/
abbrev Space : {m : ℕ} → (Ω : Domain (m + 1)) → IsBoundedLipschitzOpen Ω → Type
  | 0, Ω, _ => BoundaryL2 Ω
  | _ + 1, Ω, hΩ => ↥(fractionalGraph Ω hΩ)

instance spaceNormedAddCommGroup : NormedAddCommGroup (Space Ω hΩ) := by
  cases m <;> unfold Space <;> infer_instance
instance spaceNormedSpace : NormedSpace ℝ (Space Ω hΩ) := by
  cases m <;> unfold Space <;> infer_instance

/-- The physical L² class, without changing boundary or measure. -/
def inclusion : Space Ω hΩ →L[ℝ] BoundaryL2 Ω := by
  cases m with
  | zero => exact ContinuousLinearMap.id ℝ _
  | succ m =>
    exact (WithLp.fstL 1 ℝ (BoundaryL2 Ω) (PairL2 Ω)).comp
      (fractionalGraph Ω hΩ).subtypeL

end Trace

/-- The same trace space, including its specified norm. -/
abbrev Hhalf {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω) :=
  Trace.Space Ω hΩ

/-- Real continuous dual of this very trace space, as in the C02 dualities. -/
abbrev HminusHalf {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω) :=
  Hhalf Ω hΩ →L[ℝ] ℝ

abbrev HhalfExportType := {m : ℕ} → (Ω : Domain (m + 1)) →
  IsBoundedLipschitzOpen Ω → Type
abbrev HminusHalfExportType := HhalfExportType

namespace Trace
open P102.Trace.MeasuredFractional
/-- The full physical fractional space and its exact sum norm, with s=1/2,
p=2, boundary dimension m+1 and ambient dimension m+2. -/
def PhysicalSpaceStatement : Prop :=
  ∀ (m : ℕ) (Ω : Domain ((m + 1) + 1)) (hΩ : IsBoundedLipschitzOpen Ω),
    (∀ u : Hhalf Ω hΩ, ‖u‖ = ‖inclusion Ω hΩ u‖ +
      (metricSeminorm (m + 1) (boundaryMeasure Ω) (1 / 2) 2
        (inclusion Ω hΩ u : P201Specs.Space ((m + 1) + 1) → ℝ)).toReal) ∧
    ∀ g : BoundaryL2 Ω,
      (∃ u : Hhalf Ω hΩ, inclusion Ω hΩ u = g) ↔
        metricSeminorm (m + 1) (boundaryMeasure Ω) (1 / 2) 2
          (g : P201Specs.Space ((m + 1) + 1) → ℝ) < ⊤

/-- In dimension one there is no fractional seminorm: the norm and measure
are exactly endpoint counting L², with no renormalization. -/
def EndpointSpaceStatement : Prop :=
  ∀ (Ω : Domain 1) (hΩ : IsBoundedLipschitzOpen Ω),
    boundaryMeasure Ω = Measure.count.restrict (frontier (Ω : Set (P201Specs.Space 1))) ∧
    (∀ u : Hhalf Ω hΩ, ‖u‖ = ‖inclusion Ω hΩ u‖) ∧
    Function.Bijective (inclusion Ω hΩ)

/-- Smooth restrictions are tested on actual boundary a.e. classes. -/
def AgreesWithSmooth {m : ℕ} {Ω : Domain (m + 1)} {hΩ : IsBoundedLipschitzOpen Ω}
    (T : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ) : Prop :=
  ∀ (u : H ℝ Ω 1) (f : P201Specs.Space (m + 1) → ℝ), ContDiff ℝ ∞ f →
    hUnderlying Ω 1 u =ᵐ[domainMeasure Ω] f →
      (inclusion Ω hΩ (T u) : P201Specs.Space (m + 1) → ℝ) =ᵐ[boundaryMeasure Ω] f

/-- Bounded, onto trace and bounded linear section, with the actual closure kernel. -/
def ExactStatement : Prop :=
  ∀ (m : ℕ) (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω),
    ∃ (T : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ)
      (L : Hhalf Ω hΩ →L[ℝ] H ℝ Ω 1),
      AgreesWithSmooth T ∧ Function.Surjective T ∧
      (∀ g, T (L g) = g) ∧ T.ker = hZeroSubmodule ℝ Ω

/-- The explicitly stated one-dimensional affine lifting, with a single
bounded linear operator for all endpoint data. The formula specifies the
bulk class on each component, so it is independent of L² representatives. -/
def EndpointAffineStatement : Prop :=
  ∀ (Ω : Domain 1) (hΩ : IsBoundedLipschitzOpen Ω),
    ∃ (n : ℕ) (a b : Fin n → ℝ)
      (T : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ)
      (L : Hhalf Ω hΩ →L[ℝ] H ℝ Ω 1),
      (∀ i, a i < b i) ∧ Function.Injective (Sum.elim a b) ∧
      Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) ∧
      (Ω : Set (P201Specs.Space 1)) =
        ⋃ i, P102.Trace.Ordinary.linePoint '' Ioo (a i) (b i) ∧
      frontier (Ω : Set (P201Specs.Space 1)) =
        ⋃ i, {P102.Trace.Ordinary.linePoint (a i), P102.Trace.Ordinary.linePoint (b i)} ∧
      AgreesWithSmooth T ∧ (∀ g, T (L g) = g) ∧
      T.ker = hZeroSubmodule ℝ Ω ∧
      ∀ (g : Hhalf Ω hΩ) (i : Fin n),
        ∀ᵐ t ∂volume.restrict (Ioo (a i) (b i)),
          hUnderlying Ω 1 (L g) (P102.Trace.Ordinary.linePoint t) =
            ((b i - t) / (b i - a i)) *
              inclusion Ω hΩ g (P102.Trace.Ordinary.linePoint (a i)) +
            ((t - a i) / (b i - a i)) *
              inclusion Ω hΩ g (P102.Trace.Ordinary.linePoint (b i))

/-- Full C02 obligation, retaining the specified affine section. -/
def FullStatement : Prop :=
  PhysicalSpaceStatement ∧ EndpointSpaceStatement ∧ ExactStatement ∧ EndpointAffineStatement

end Trace
end P201Specs
