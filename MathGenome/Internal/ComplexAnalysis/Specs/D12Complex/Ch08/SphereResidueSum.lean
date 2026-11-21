import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.InfinityResidue

/-! The global residue theorem, paper.tex:2002–2018.
A total finite-chart coefficient represents f(z) dz. At a regular finite
point its actual values are holomorphic; values at poles are arbitrary fillers.
At infinity only the punctured germ of -f(1/w)w⁻² matters. Meromorphy below
is local holomorphy or a pole of finite positive order, with no assumed
finiteness of the pole set, residue identity, or rational representation. -/
noncomputable section
open Set
open scoped BigOperators

namespace D12Complex.SphereResidueSum

/-- A holomorphic coefficient on a full neighborhood of a finite point. -/
def RegularAt (f : ℂ → ℂ) (a : ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ HolomorphicOn (Metric.ball a r) f

/-- Meromorphy in the two source charts of the differential f(z) dz.
The second chart uses the differential transition rule, including its Jacobian. -/
def MeromorphicDifferential (f : ℂ → ℂ) : Prop :=
  (∀ a : ℂ, RegularAt f a ∨ PoleAt f a) ∧
  (RemovableSingularityAt (InfinityResidue.pullbackCoefficient f) 0 ∨
    PoleAt (InfinityResidue.pullbackCoefficient f) 0)

/-- Actual poles of the differential, including a possible pole at infinity. -/
def poleSet (f : ℂ → ℂ) : Set RiemannSphere :=
  sphereFinite '' {a | PoleAt f a} ∪
    {p | p = sphereInfty ∧ PoleAt (InfinityResidue.pullbackCoefficient f) 0}

/-- The finite and infinite residues are computed from their differential coefficients. -/
def residueOnSphere (f : ℂ → ℂ) (p : RiemannSphere) : ℂ :=
  OnePoint.elim p (InfinityResidue.residueAtInfinity f) (Residue.residue f)

end D12Complex.SphereResidueSum

namespace Specs.D12Complex.Ch08.SphereResidueSum
open _root_.D12Complex _root_.D12Complex.SphereResidueSum

def RegularAt_type := (ℂ → ℂ) → ℂ → Prop
def RegularAt_value : RegularAt_type :=
  fun f a => ∃ r : ℝ, 0 < r ∧ HolomorphicOn (Metric.ball a r) f

def MeromorphicDifferential_type := (ℂ → ℂ) → Prop
def MeromorphicDifferential_value : MeromorphicDifferential_type :=
  fun f => (∀ a : ℂ, RegularAt f a ∨ PoleAt f a) ∧
    (RemovableSingularityAt (InfinityResidue.pullbackCoefficient f) 0 ∨
      PoleAt (InfinityResidue.pullbackCoefficient f) 0)

def poleSet_type := (ℂ → ℂ) → Set RiemannSphere
def poleSet_value : poleSet_type := fun f =>
  sphereFinite '' {a | PoleAt f a} ∪
    {p | p = sphereInfty ∧ PoleAt (InfinityResidue.pullbackCoefficient f) 0}

def residueOnSphere_type := (ℂ → ℂ) → RiemannSphere → ℂ
def residueOnSphere_value : residueOnSphere_type := fun f p =>
  OnePoint.elim p (InfinityResidue.residueAtInfinity f) (Residue.residue f)

def poles_finite_type : Prop :=
  ∀ f : ℂ → ℂ, MeromorphicDifferential f → (poleSet f).Finite

def residue_zero_off_poles_type : Prop :=
  ∀ f : ℂ → ℂ, MeromorphicDifferential f →
    ∀ p : RiemannSphere, p ∉ poleSet f → residueOnSphere f p = 0

/-- A finite sum over precisely all the poles, with no multiplicity weights:
a residue already accounts for the full local principal part. -/
def total_residue_zero_type : Prop :=
  ∀ f : ℂ → ℂ, MeromorphicDifferential f →
    ∃ s : Finset RiemannSphere,
      (∀ p, p ∈ s ↔ p ∈ poleSet f) ∧ ∑ p ∈ s, residueOnSphere f p = 0

/-- The same identity with the infinity term displayed separately, including
when infinity is regular and its residue is zero. -/
def finite_residue_sum_type : Prop :=
  ∀ f : ℂ → ℂ, MeromorphicDifferential f →
    ∃ s : Finset ℂ, (∀ a, a ∈ s ↔ PoleAt f a) ∧
      (∑ a ∈ s, Residue.residue f a) + InfinityResidue.residueAtInfinity f = 0

end Specs.D12Complex.Ch08.SphereResidueSum
