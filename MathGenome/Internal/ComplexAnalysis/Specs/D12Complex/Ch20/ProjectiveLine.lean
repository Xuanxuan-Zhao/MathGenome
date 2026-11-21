import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.Surfaces
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.SphereHolomorphic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Constructions

/-! The literal scalar-orbit quotient, with its quotient topology. The theorem
contract below requires the full surface structure and the two prescribed charts,
as well as the homeomorphic and biholomorphic identification with the sphere. -/
noncomputable section
open Set
namespace D12Complex.ProjectiveLine

/-- Nonzero homogeneous coordinate vectors. -/
abbrev HomogeneousVector := {v : ℂ × ℂ // v ≠ 0}

/-- The quotient (ℂ² \ {0}) / ℂ*. -/
def ComplexProjectiveLine := Projectivization ℂ (ℂ × ℂ)

instance : TopologicalSpace ComplexProjectiveLine :=
  inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid ℂ (ℂ × ℂ))))

/-- The orbit projection; the source has the subspace topology. -/
def projection (v : HomogeneousVector) : ComplexProjectiveLine :=
  Projectivization.mk ℂ v.val v.property

/-- The section z ↦ [1:z]. -/
def finiteParam (z : ℂ) : ComplexProjectiveLine :=
  projection ⟨(1, z), by simp⟩

/-- The section w ↦ [w:1], including infinity at w=0. -/
def reciprocalParam (w : ℂ) : ComplexProjectiveLine :=
  projection ⟨(w, 1), by simp⟩

end D12Complex.ProjectiveLine

namespace Specs.D12Complex.Ch20.ProjectiveLine
open _root_.D12Complex _root_.D12Complex.ProjectiveLine _root_.D12Complex.Surfaces

def HomogeneousVector_type := Type
def HomogeneousVector_value : HomogeneousVector_type := {v : ℂ × ℂ // v ≠ 0}
def ComplexProjectiveLine_type := Type
def ComplexProjectiveLine_value : ComplexProjectiveLine_type := Projectivization ℂ (ℂ × ℂ)
def projection_type := HomogeneousVector → ComplexProjectiveLine
def projection_value : projection_type := fun v => Projectivization.mk ℂ v.val v.property
def finiteParam_type := ℂ → ComplexProjectiveLine
def finiteParam_value : finiteParam_type := fun z => projection ⟨(1, z), by simp⟩
def reciprocalParam_type := ℂ → ComplexProjectiveLine
def reciprocalParam_value : reciprocalParam_type := fun w => projection ⟨(w, 1), by simp⟩

def projection_quotient_type : Prop := Topology.IsQuotientMap projection

/-- All topological and complex-analytic conclusions of d12:20-02. Equality of
the partial equivalences specifies maps, inverses, sources and targets. The last
four assertions are the coordinate expressions of the identification and its
inverse in matching finite and reciprocal charts. -/
def projective_line_type : Prop :=
  Topology.IsQuotientMap projection ∧ CompactSpace ComplexProjectiveLine ∧
  ∃ (e : ComplexProjectiveLine ≃ₜ RiemannSphere)
    (S : RiemannSurface ComplexProjectiveLine)
    (c₀ c₁ : ComplexChart ComplexProjectiveLine),
    (∀ v : HomogeneousVector, e (projection v) =
      if v.val.1 = 0 then sphereInfty else sphereFinite (v.val.2 / v.val.1)) ∧
    (∀ z : ℂ, e (finiteParam z) = sphereFinite z) ∧
    (∀ w : ℂ, e (reciprocalParam w) = infinityParametrization w) ∧
    (∀ z : ℂ, c₀.val (finiteParam z) = z ∧ c₀.val.symm z = finiteParam z) ∧
    (∀ w : ℂ, c₁.val (reciprocalParam w) = w ∧ c₁.val.symm w = reciprocalParam w) ∧
    projection ⁻¹' c₀.val.source = {v | v.val.1 ≠ 0} ∧
    projection ⁻¹' c₁.val.source = {v | v.val.2 ≠ 0} ∧
    S.atlas = {c₀, c₁} ∧
    c₀.val.toPartialEquiv = e.toEquiv.toPartialEquiv.trans finiteChart ∧
    c₁.val.toPartialEquiv = e.toEquiv.toPartialEquiv.trans infinityChart ∧
    BiholomorphicPair ({0}ᶜ : Set ℂ) ({0}ᶜ : Set ℂ)
      (fun z => c₁.val (c₀.val.symm z)) (fun w => c₀.val (c₁.val.symm w)) ∧
    (∀ z : ℂ, z ≠ 0 → c₁.val (c₀.val.symm z) = z⁻¹) ∧
    HolomorphicOn univ (fun z => finiteCoordinate (e (c₀.val.symm z))) ∧
    HolomorphicOn univ (fun w => infinityCoordinate (e (c₁.val.symm w))) ∧
    HolomorphicOn univ (fun z => c₀.val (e.symm (sphereFinite z))) ∧
    HolomorphicOn univ (fun w => c₁.val (e.symm (infinityParametrization w)))

end Specs.D12Complex.Ch20.ProjectiveLine
