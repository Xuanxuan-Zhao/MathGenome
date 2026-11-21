import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.ProjectiveLine
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.MapsMultiplicity
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! The literal affine power curve, and the explicit compactification in
paper.tex:3720–3734. The compactification is constructed on the quotient
projective line. Its dense open affine inclusion, complex charts, and extended
projection are conclusions, rather than assumed completion certificates. -/

noncomputable section
open Set

namespace D12Complex.PowerCurve

/-- Coordinates are `(z,w)`, with the original equation `w^n = z`. -/
abbrev AffineCurve (n : ℕ) := {p : ℂ × ℂ // p.2 ^ n = p.1}

/-- The global parameter is the actual polynomial graph. -/
def parameter (n : ℕ) (t : ℂ) : AffineCurve n := ⟨(t ^ n, t), rfl⟩

/-- The inverse parameter is the second ambient coordinate. -/
def coordinate (n : ℕ) (p : AffineCurve n) : ℂ := p.val.2

/-- Inclusion into the literal scalar-orbit quotient, using `[1:w]`. -/
def inclusion (n : ℕ) (p : AffineCurve n) :
    ProjectiveLine.ComplexProjectiveLine := ProjectiveLine.finiteParam p.val.2

end D12Complex.PowerCurve

namespace Specs.D12Complex.Ch21.PowerCurve
open _root_.D12Complex _root_.D12Complex.PowerCurve
open _root_.D12Complex.ProjectiveLine _root_.D12Complex.Surfaces

def AffineCurve_type := ℕ → Type
def AffineCurve_value : AffineCurve_type := fun n => {p : ℂ × ℂ // p.2 ^ n = p.1}
def parameter_type := (n : ℕ) → ℂ → AffineCurve n
def parameter_value : parameter_type := fun n t => ⟨(t ^ n, t), rfl⟩
def coordinate_type := (n : ℕ) → AffineCurve n → ℂ
def coordinate_value : coordinate_type := fun _ p => p.val.2
def inclusion_type := (n : ℕ) → AffineCurve n → ComplexProjectiveLine
def inclusion_value : inclusion_type := fun _ p => finiteParam p.val.2

/-- A genuine global complex coordinate on the smooth embedded affine curve.
The derivative of the polynomial parametrization has second component one,
so it is nonzero even at `t=0`. -/
def affine_parameter_type : Prop :=
  ∀ n : ℕ, ∃ (e : ℂ ≃ₜ AffineCurve n)
    (S : RiemannSurface (AffineCurve n)) (c : ComplexChart (AffineCurve n)),
    (∀ t, e t = parameter n t) ∧
    (∀ p, e.symm p = coordinate n p) ∧
    c.val.source = univ ∧ c.val.target = univ ∧
    (∀ p, c.val p = coordinate n p) ∧
    (∀ t, c.val.symm t = parameter n t) ∧ S.atlas = {c} ∧
    ScalarHolomorphic S (fun p => p.val.1) ∧ ScalarHolomorphic S (coordinate n) ∧
    (∀ t : ℂ, HasDerivAt (fun u => (parameter n u).val)
      ((n : ℂ) * t ^ (n - 1), 1) t) ∧
    (∀ t : ℂ, ((n : ℂ) * t ^ (n - 1), (1 : ℂ)) ≠ 0)

/-- The completion is the actual compact projective line with its standard
finite and reciprocal charts. The affine inclusion is open, dense, and locally
biholomorphic, and adds exactly the point `[0:1]`. The chart formulas identify
the original projection `z=w^n`, including `1/z=s^n` at infinity. Multiplicity
uses the canonical chart-independent surface predicate. -/
def compact_completion_type : Prop :=
  ∀ n : ℕ, 0 < n →
    ∃ (S₀ : RiemannSurface (AffineCurve n)) (c : ComplexChart (AffineCurve n))
      (S : RiemannSurface ComplexProjectiveLine)
      (c₀ c₁ : ComplexChart ComplexProjectiveLine)
      (e : ComplexProjectiveLine ≃ₜ RiemannSphere)
      (π : ComplexProjectiveLine → ComplexProjectiveLine),
      CompactSpace ComplexProjectiveLine ∧
      S₀.atlas = {c} ∧ c.val.source = univ ∧ c.val.target = univ ∧
      (∀ p, c.val p = coordinate n p) ∧
      (∀ t, c.val.symm t = parameter n t) ∧
      S.atlas = {c₀, c₁} ∧
      c₀.val.toPartialEquiv = e.toEquiv.toPartialEquiv.trans finiteChart ∧
      c₁.val.toPartialEquiv = e.toEquiv.toPartialEquiv.trans infinityChart ∧
      (∀ t, e (finiteParam t) = sphereFinite t) ∧
      (∀ s, e (reciprocalParam s) = infinityParametrization s) ∧
      (∀ t, c₀.val (finiteParam t) = t ∧ c₀.val.symm t = finiteParam t) ∧
      (∀ s, c₁.val (reciprocalParam s) = s ∧ c₁.val.symm s = reciprocalParam s) ∧
      Topology.IsOpenEmbedding (inclusion n) ∧ DenseRange (inclusion n) ∧
      Set.range (inclusion n) = {reciprocalParam 0}ᶜ ∧
      HolomorphicMap S₀ S (inclusion n) ∧
      (∀ p, LocallyBiholomorphicAt S₀ S (inclusion n) p) ∧
      HolomorphicMap S S π ∧
      (∀ p : AffineCurve n, π (inclusion n p) = finiteParam p.val.1) ∧
      (∀ t : ℂ, π (finiteParam t) = finiteParam (t ^ n)) ∧
      (∀ s : ℂ, π (reciprocalParam s) = reciprocalParam (s ^ n)) ∧
      HasMultiplicity S S π (finiteParam 0) n ∧
      HasMultiplicity S S π (reciprocalParam 0) n ∧
      (n = 1 → LocallyBiholomorphicAt S S π (finiteParam 0) ∧
        LocallyBiholomorphicAt S S π (reciprocalParam 0))

end Specs.D12Complex.Ch21.PowerCurve
