import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinSymmetricOperator
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.DistributionPrimitive
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.MultiplicityModel
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Canonical shared data for the spectral-kernel portion of
`fa2:p4:krein-kernel`, paper.tex:21266–21324. Migrated from the parent handoff,
preserving declaration names and values. These statements do not assert the
later mollifier limit or the final representation of F, allocated separately.
All kernels take values in the same ℓ² as the upstream multiplicity model.
The real spectral parameter has no boundedness assumption. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace Topology

namespace ExpandedFA.PartIV.KreinSpectralKernel

abbrev FiberSpace := VonNeumann.MultiplicityModel.Spec.SequenceSpace
abbrev coordinateFiber := VonNeumann.MultiplicityModel.Spec.fiber
abbrev LineTest := DistributionPrimitive.LineTests ℂ (⊤ : TopologicalSpace.Opens ℝ)

/-- The selected, normalized real solution, with its original zero parameter. -/
def solution (p : Bool) (ξ t : ℝ) : ℝ :=
  if p then KreinSolutions.Specs.CValue ξ t else KreinSolutions.Specs.SValue ξ t

/-- Finite intervals always carry restricted Lebesgue measure. -/
def intervalMeasure (R : ℝ) : Measure ℝ := volume.restrict (Icc (-R) R)

/-- A finite-control-measure spectral representation of an unbounded operator.
The range condition identifies the actual direct integral. The graph condition
specifies both the full domain and the action, not merely an intertwining on
some core. Zero spaces and the zero measure are allowed. -/
structure RealSpectralModel {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (S : Unbounded.Operator ℂ H H) where
  μ : Measure ℝ
  finite : IsFiniteMeasure μ
  multiplicity : ℝ → ℕ∞
  measurable_multiplicity : Measurable multiplicity
  positive_multiplicity : ∀ᵐ ξ ∂μ, 0 < multiplicity ξ
  U : H →ₗᵢ[ℂ] Lp FiberSpace 2 μ
  range_eq : Set.range U = {f | ∀ᵐ ξ ∂μ, f ξ ∈ coordinateFiber (multiplicity ξ)}
  graph_iff : ∀ x y : H,
    (∃ hx : x ∈ S.domain, S ⟨x, hx⟩ = y) ↔
      (U y : ℝ → FiberSpace) =ᵐ[μ] fun ξ => (ξ : ℂ) • U x ξ

/-- The distributional equation uses scalar-linear testing, with two
derivatives and therefore a positive sign. Local L² is imposed separately. -/
def WeakEquation (ξ : ℝ) (h : ℝ → FiberSpace) : Prop :=
  ∀ φ : LineTest,
    (∫ t : ℝ, deriv (deriv (fun t => φ t)) t • h t) =
      (ξ : ℂ) • ∫ t : ℝ, φ t • h t

/-- A single globally chosen kernel, rather than unrelated representatives
for each test or each interval. The nested a.e. assertions remove one scalar
null set for all local bounds, parity, fiber membership, and all tests. -/
structure KernelData {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {p : Bool} {F : ℝ → ℝ}
    (G : KreinSymmetricOperator.Spec.GramData p F H)
    {S : Unbounded.Operator ℂ H H} (M : RealSpectralModel S) where
  h : ℝ → ℝ → FiberSpace
  measurable : AEStronglyMeasurable (Function.uncurry h) (M.μ.prod volume)
  local_square : ∀ R : ℝ, 0 < R →
    MemLp (Function.uncurry h) 2 (M.μ.prod (intervalMeasure R))
  fiber_properties : ∀ᵐ ξ ∂M.μ,
    (∀ n : ℕ, MemLp (h ξ) 2 (intervalMeasure (n + 1))) ∧
    (∀ᵐ t ∂volume, h ξ t ∈ coordinateFiber (M.multiplicity ξ)) ∧
    (∀ᵐ t ∂volume, h ξ (-t) = KreinSymmetricOperator.Spec.paritySign p • h ξ t) ∧
    WeakEquation ξ (h ξ)
  represents : ∀ R : ℝ, 0 < R → ∀ f : Lp ℂ 2 (intervalMeasure R),
    (M.U (∫ t, f t • G.vectors t ∂intervalMeasure R) : ℝ → FiberSpace) =ᵐ[M.μ]
      fun ξ => ∫ t, f t • h ξ t ∂intervalMeasure R
  energy : ∀ R : ℝ, 0 < R →
    (∫⁻ ξ, ∫⁻ t, ‖h ξ t‖ₑ ^ 2 ∂intervalMeasure R ∂M.μ) =
      ENNReal.ofReal (∫ t, ‖G.vectors t‖ ^ 2 ∂intervalMeasure R)

/-- The scalar measure determined by the fiber amplitude, without an arbitrary
normalization or an assumed finite total mass. -/
def amplitudeMeasure (μ : Measure ℝ) (c : ℝ → FiberSpace) : Measure ℝ :=
  μ.withDensity (fun ξ => ‖c ξ‖ₑ ^ 2)

/-- All the amplitude conclusions refer to the same kernel, control measure,
and Gram synthesis map. In the odd case only local finiteness is asserted. -/
structure AmplitudeData {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {p : Bool} {F : ℝ → ℝ}
    {G : KreinSymmetricOperator.Spec.GramData p F H}
    {S : Unbounded.Operator ℂ H H} {M : RealSpectralModel S} (K : KernelData G M) where
  c : ℝ → FiberSpace
  measurable : AEStronglyMeasurable c M.μ
  fiber : ∀ᵐ ξ ∂M.μ, c ξ ∈ coordinateFiber (M.multiplicity ξ)
  factorization : ∀ᵐ ξ ∂M.μ,
    (K.h ξ) =ᵐ[volume] fun t => (solution p ξ t : ℂ) • c ξ
  locally_finite : IsLocallyFiniteMeasure (amplitudeMeasure M.μ c)
  local_energy : ∀ R : ℝ, 0 < R →
    (∫⁻ ξ, ∫⁻ t, ENNReal.ofReal (|solution p ξ t| ^ 2)
      ∂intervalMeasure R ∂amplitudeMeasure M.μ c) < ∞
  gram_identity : ∀ f g : KreinSymmetricOperator.Spec.SmoothTest p,
    Integrable (fun ξ =>
      star (∫ t : ℝ, f.val t * (solution p ξ t : ℂ)) *
        (∫ t : ℝ, g.val t * (solution p ξ t : ℂ))) (amplitudeMeasure M.μ c) ∧
    ⟪KreinSymmetricOperator.Spec.testIntegral G.vectors f.val,
      KreinSymmetricOperator.Spec.testIntegral G.vectors g.val⟫_ℂ =
      ∫ ξ, star (∫ t : ℝ, f.val t * (solution p ξ t : ℂ)) *
        (∫ t : ℝ, g.val t * (solution p ξ t : ℂ)) ∂amplitudeMeasure M.μ c

namespace Spec

/-- Remaining spectral-model obligation, separated from the kernel analysis. -/
def RealModelExistence : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (S : Unbounded.Operator ℂ H H),
    Unbounded.SymmetryAndDeficienciesSpec.selfAdjointValue S →
      Nonempty (RealSpectralModel S)

end Spec
end ExpandedFA.PartIV.KreinSpectralKernel

namespace ExpandedFA.PartIV.KreinRealSpectralModel.Spec
open ExpandedFA.Unbounded ExpandedFA.PartIV.KreinSpectralKernel

/-- The zero space is included, with the zero real control measure. -/
def ZeroModel : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Subsingleton H] (S : Operator ℂ H H),
    ∃ M : RealSpectralModel S, M.μ = 0

/-- The Cayley transform, including its full inverse graph, without a spectral
boundedness or nonzero-space hypothesis. -/
def CayleyExistence : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Operator ℂ H H), SymmetryAndDeficienciesSpec.selfAdjointValue S →
    ∃ V : H ≃ₗᵢ[ℂ] H,
      (∀ x : S.domain, V (S x + Complex.I • (x : H)) = S x - Complex.I • (x : H)) ∧
      (∀ x : H, V x = x → x = 0) ∧
      (∀ x y : H, (∃ hx : x ∈ S.domain, S ⟨x, hx⟩ = y) ↔
        V (y + Complex.I • x) = y - Complex.I • x)

end ExpandedFA.PartIV.KreinRealSpectralModel.Spec
