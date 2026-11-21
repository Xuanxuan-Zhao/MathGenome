import MathGenome.Internal.LinearPDE.P201Specs.Common.SpatialInterfaces
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.SolutionDiffeomorphism

/-! Independent specifications for the flow assertions in paper.tex,
Theorem thm:pde-transport-flow (3643ff), and its proof. Transport formulas,
Jacobian formulas, and transverse data are allocated to other goals.

C¹ on a closed slab is expressed intrinsically by `ContDiffOn`. Derivatives
of solution curves are within derivatives on the closed interval. No extension
or existence of solutions is part of the hypotheses. Ambient representatives
of fields and curves carry no conditions outside their specified domains.
-/
noncomputable section
open Set
open scoped ContDiff NNReal
namespace P201Specs
namespace Hyperbolic

/-- A local C¹ time-dependent field on its original open time-state domain. -/
structure LocalField (n : ℕ) where
  domain : Set (ℝ × Space n)
  isOpen_domain : IsOpen domain
  velocity : ℝ × Space n → Space n
  regular : ContDiffOn ℝ 1 velocity domain

/-- An unused real parameter permits direct use of D13's joint flow theorem.
The domain is the preimage of the original domain, with no enlargement. -/
def LocalField.equation {n : ℕ} (b : LocalField n) :
    D13Unified.ParameterODE (Space n) ℝ where
  domain := Prod.fst ⁻¹' b.domain
  isOpen_domain := b.isOpen_domain.preimage continuous_fst
  field := fun q => b.velocity q.val.1
  continuous_field := b.regular.continuousOn.domRestrict.comp
    ((continuous_fst.comp continuous_subtype_val).subtype_mk (fun q => q.property))

def localFlow {n : ℕ} (b : LocalField n) (t s : ℝ) (y : Space n) : Space n :=
  D13Unified.Ch06.C1Dependence.solution b.equation (t, ((s, y), 0))

def localFlowDomain {n : ℕ} (b : LocalField n) : Set (ℝ × (ℝ × Space n)) :=
  {q | (q.1, ((q.2.1, q.2.2), (0 : ℝ))) ∈
    Specs.D13Unified.Ch04.MaximalSolutionMap.parameterSolutionDomainValue b.equation}

def survivalDomain {n : ℕ} (b : LocalField n) (s t : ℝ) : Set (Space n) :=
  {y | (t, s, y) ∈ localFlowDomain b}

/-- Maximality is tested against all classical solutions in the original domain. -/
def IsLocalSolution {n : ℕ} (b : LocalField n) (I : D13Unified.OpenTimeInterval)
    (x : ℝ → Space n) : Prop :=
  ContDiffOn ℝ 1 x I.carrier ∧
  (∀ t ∈ I.carrier, (t, x t) ∈ b.domain) ∧
  ∀ t ∈ I.carrier, HasDerivAt x (b.velocity (t, x t)) t

structure LocalFlowProperties {n : ℕ} (b : LocalField n) : Prop where
  open_domain : IsOpen (localFlowDomain b)
  regular : ContDiffOn ℝ 1 (fun q : ℝ × (ℝ × Space n) =>
    localFlow b q.1 q.2.1 q.2.2) (localFlowDomain b)
  initial : ∀ s y, (s, y) ∈ b.domain →
    (s, s, y) ∈ localFlowDomain b ∧ localFlow b s s y = y
  equation : ∀ t s y, (t, s, y) ∈ localFlowDomain b →
    (t, localFlow b t s y) ∈ b.domain ∧
    HasDerivAt (fun r => localFlow b r s y)
      (b.velocity (t, localFlow b t s y)) t
  maximal : ∀ s y, (s, y) ∈ b.domain →
    ∀ (I : D13Unified.OpenTimeInterval) (x : ℝ → Space n),
      IsLocalSolution b I x → s ∈ I.carrier → x s = y →
      (∀ t ∈ I.carrier, (t, s, y) ∈ localFlowDomain b) ∧
      EqOn (fun t => localFlow b t s y) x I.carrier
  composition : ∀ r s y, (r, s, y) ∈ localFlowDomain b →
    ∀ t, ((t, r, localFlow b r s y) ∈ localFlowDomain b ↔
      (t, s, y) ∈ localFlowDomain b) ∧
      ((t, s, y) ∈ localFlowDomain b →
        localFlow b t r (localFlow b r s y) = localFlow b t s y)
  diffeomorphism : ∀ s t,
    IsOpen (survivalDomain b s t) ∧ IsOpen (survivalDomain b t s) ∧
    (localFlow b t s) '' survivalDomain b s t = survivalDomain b t s ∧
    ∃ e : OpenPartialHomeomorph (Space n) (Space n),
      e.source = survivalDomain b s t ∧ e.target = survivalDomain b t s ∧
      (e : Space n → Space n) = localFlow b t s ∧
      (e.symm : Space n → Space n) = localFlow b s t ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target

def localFlowStatement : Prop :=
  ∀ n, 1 ≤ n → ∀ b : LocalField n, LocalFlowProperties b

/-- These are exactly coefficient hypotheses, with explicit uniform bounds.
`spatial_bound` refers to the derivative of the spatial slice, including at
the time endpoints; it is not a bound on the full time-state derivative. -/
structure SlabField (n : ℕ) (T : ℝ) where
  velocity : ℝ × Space n → Space n
  regular : ContDiffOn ℝ 1 velocity (Icc 0 T ×ˢ univ)
  bound : ℝ≥0
  velocity_bound : ∀ t ∈ Icc 0 T, ∀ y, ‖velocity (t, y)‖ ≤ bound
  spatialBound : ℝ≥0
  spatial_bound : ∀ t ∈ Icc 0 T, ∀ y,
    ‖fderiv ℝ (fun x => velocity (t, x)) y‖ ≤ spatialBound

/-- The actual uniform velocity norm on the slab. Its defining set is
nonempty when `0 ≤ T`, and `velocity_bound` supplies boundedness above. -/
def slabVelocityNorm {n : ℕ} {T : ℝ} (b : SlabField n T) : ℝ :=
  sSup ((fun q : ℝ × Space n => ‖b.velocity q‖) '' (Icc 0 T ×ˢ univ))

/-- A solution on the slab, with the appropriate one-sided endpoint equations. -/
def IsSlabSolution {n : ℕ} {T : ℝ} (b : SlabField n T)
    (x : ℝ → Space n) : Prop :=
  ContinuousOn x (Icc 0 T) ∧ ∀ t ∈ Icc 0 T,
    HasDerivWithinAt x (b.velocity (t, x t)) (Icc 0 T) t

structure SlabFlowProperties {n : ℕ} {T : ℝ} (b : SlabField n T)
    (X : ℝ → ℝ → Space n → Space n) : Prop where
  regular : ContDiffOn ℝ 1 (fun q : ℝ × (ℝ × Space n) => X q.1 q.2.1 q.2.2)
    (Icc 0 T ×ˢ (Icc 0 T ×ˢ univ))
  initial : ∀ s ∈ Icc 0 T, ∀ y, X s s y = y
  solution : ∀ s ∈ Icc 0 T, ∀ y, IsSlabSolution b (fun t => X t s y)
  unique : ∀ s ∈ Icc 0 T, ∀ y (x : ℝ → Space n), IsSlabSolution b x →
    x s = y → EqOn x (fun t => X t s y) (Icc 0 T)
  composition : ∀ t ∈ Icc 0 T, ∀ r ∈ Icc 0 T, ∀ s ∈ Icc 0 T, ∀ y,
    X t r (X r s y) = X t s y
  displacement : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, ∀ y,
    ‖X t s y - y‖ ≤ slabVelocityNorm b * |t - s|
  diffeomorphism : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T,
    ∃ e : Space n ≃ₜ Space n,
      (e : Space n → Space n) = X t s ∧
      (e.symm : Space n → Space n) = X s t ∧
      ContDiff ℝ 1 e ∧ ContDiff ℝ 1 e.symm

def slabFlowStatement : Prop :=
  ∀ n, 1 ≤ n → ∀ T : ℝ, 0 ≤ T → ∀ b : SlabField n T,
    ∃ X, SlabFlowProperties b X

/-- Extension is a proof obligation, not a hypothesis of `slabFlowStatement`.
Uniform bounds need not be sharp off the slab. The exact slab bound remains
available for the flow displacement estimate. -/
def slabExtensionStatement : Prop :=
  ∀ n, 1 ≤ n → ∀ T : ℝ, 0 ≤ T → ∀ b : SlabField n T,
    ∃ v : ℝ × Space n → Space n,
      ContDiff ℝ 1 v ∧ EqOn v b.velocity (Icc 0 T ×ˢ univ) ∧
      (∃ M : ℝ≥0, ∀ q, ‖v q‖ ≤ M)

def slabFlowFromExtensionStatement : Prop :=
  slabExtensionStatement → slabFlowStatement

end Hyperbolic
end P201Specs
