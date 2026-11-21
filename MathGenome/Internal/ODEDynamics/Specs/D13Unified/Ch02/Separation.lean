import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.SolutionConcepts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Order.IntermediateValue

/-! Independent specification of paper.tex, Theorem d13:02:separable.
Ambient representatives are used only on the specified open intervals.
No differentiability or local Lipschitz hypothesis is imposed on `g`.
-/

noncomputable section
open Set MeasureTheory

namespace D13Unified.Separation

/-- The original continuous coefficients, domains, and initial data. -/
structure Data where
  I : OpenTimeInterval
  J : OpenTimeInterval
  a : ℝ → ℝ
  g : ℝ → ℝ
  continuous_a : ContinuousOn a I.carrier
  continuous_g : ContinuousOn g J.carrier
  nonzero_g : ∀ u ∈ J.carrier, g u ≠ 0
  s : ℝ
  ξ : ℝ
  mem_s : s ∈ I.carrier
  mem_ξ : ξ ∈ J.carrier

/-- The field on exactly the original rectangle. -/
def Data.ode (d : Data) : ODE ℝ where
  domain := d.I.carrier ×ˢ d.J.carrier
  isOpen_domain := d.I.isOpen.prod d.J.isOpen
  field := fun p => d.a p.val.1 * d.g p.val.2
  continuous_field :=
    (d.continuous_a.comp_continuous (continuous_fst.comp continuous_subtype_val) fun p => p.property.1).mul
      (d.continuous_g.comp_continuous (continuous_snd.comp continuous_subtype_val) fun p => p.property.2)

def primitive (d : Data) (u : ℝ) : ℝ := ∫ v in d.ξ..u, (d.g v)⁻¹

def timePrimitive (d : Data) (t : ℝ) : ℝ := ∫ r in d.s..t, d.a r

/-- The actual image, with no unstated endpoint convention. -/
def image (d : Data) : Set ℝ := primitive d '' d.J.carrier

/-- The inverse is used only on `image d`. -/
def inverse (d : Data) : ℝ → ℝ := Function.invFunOn (primitive d) d.J.carrier

def admissibleTimes (d : Data) : Set ℝ :=
  d.I.carrier ∩ timePrimitive d ⁻¹' image d

def branch (d : Data) : Set ℝ := connectedComponentIn (admissibleTimes d) d.s

def formula (d : Data) (t : ℝ) : ℝ := inverse d (timePrimitive d t)

end D13Unified.Separation

namespace Specs.D13Unified.Ch02.Separation
open _root_.D13Unified _root_.D13Unified.Separation

/-- C¹ monotone primitive and C¹ inverse on its actual open image. -/
def primitiveExpected : Prop := ∀ d : Data,
  ContDiffOn ℝ 1 (primitive d) d.J.carrier ∧
  (∀ u ∈ d.J.carrier, HasDerivAt (primitive d) (d.g u)⁻¹ u) ∧
  (StrictMonoOn (primitive d) d.J.carrier ∨ StrictAntiOn (primitive d) d.J.carrier) ∧
  IsOpen (image d) ∧
  MapsTo (inverse d) (image d) d.J.carrier ∧
  LeftInvOn (inverse d) (primitive d) d.J.carrier ∧
  RightInvOn (inverse d) (primitive d) (image d) ∧
  ContDiffOn ℝ 1 (inverse d) (image d) ∧
  (∀ z ∈ image d, HasDerivAt (inverse d) (d.g (inverse d z)) z)

/-- The inverse formula supplies the maximal branch on the stated connected
component. Every classical IVP on any open subinterval of the original rectangle
is its restriction. Maximality uses the shared domain-aware solution predicate. -/
def branchExpected : Prop := ∀ d : Data,
  ∃ x : Solution d.ode,
    x.interval.carrier = branch d ∧
    EqOn x.representative (formula d) x.interval.carrier ∧
    d.s ∈ x.interval.carrier ∧ x.representative d.s = d.ξ ∧
    (∀ y : Solution d.ode, d.s ∈ y.interval.carrier → y.representative d.s = d.ξ →
      Ch01.SolutionConcepts.extensionValue y x) ∧
    Ch01.SolutionConcepts.maximalValue x

/-- Division discards no zero of the original coefficient. The equilibrium
claim is about the original field on any actual open domain containing its graph;
continuity of an ambient extension of `g` away from that graph is unnecessary. -/
def equilibriumExpected : Prop := ∀ (d : Data) (c : ℝ), d.g c = 0 →
  c ∉ d.J.carrier ∧
  ∀ (F : ODE ℝ),
    (∀ t ∈ d.I.carrier, (t, c) ∈ F.domain) →
    (∀ t ∈ d.I.carrier, F.eval t c = d.a t * d.g c) →
    Ch01.SolutionConcepts.classicalIVPOnValue F d.I (fun _ => c) d.s c

end Specs.D13Unified.Ch02.Separation
