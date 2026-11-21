import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.ResidueCycle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Independent specification of the finite identity in paper.tex:2147–2162.
There is no restriction on the type or order of the isolated singularities.
The deletion radii are indexed by the distinct real singularity coordinates.
-/
noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace D12Complex.IndentedHalfDisk.Definitions

/-- Distinct real coordinates of the real members of the finite excluded set. -/
def realSingularities (A : Finset ℂ) : Finset ℝ :=
  (A.filter (fun a => a.im = 0)).image Complex.re

/-- The retained real diameter, with independently chosen open intervals deleted. -/
def deletedDiameter (s : Finset ℝ) (r : ℝ) (ε : s → ℝ) : Set ℝ :=
  Icc (-r) r \ ⋃ a : s, Ioo (a.val - ε a) (a.val + ε a)

/-- The raw counterclockwise upper-arc integrand, including its velocity. -/
def arcIntegrand (f : ℂ → ℂ) (a : ℂ) (r : ℝ) (t : ℝ) : ℂ :=
  f (circleMap a r t) * (circleMap 0 r t * Complex.I)

/-- The oriented sum of the retained diameter, outer arc and clockwise dents. -/
def boundaryIntegral (A : Finset ℂ) (f : ℂ → ℂ) (r : ℝ)
    (ε : realSingularities A → ℝ) : ℂ :=
  (∫ x in deletedDiameter (realSingularities A) r ε, f (x : ℂ)) +
    (∫ t in (0 : ℝ)..Real.pi, arcIntegrand f 0 r t) -
    ∑ a : realSingularities A,
      ∫ t in (0 : ℝ)..Real.pi, arcIntegrand f (a.val : ℂ) (ε a) t

/-- The actual intended trace, including all retained diameter points and all arcs. -/
def boundaryTrace (A : Finset ℂ) (r : ℝ) (ε : realSingularities A → ℝ) : Set ℂ :=
  Complex.ofReal '' deletedDiameter (realSingularities A) r ε ∪
    circleMap 0 r '' Icc 0 Real.pi ∪
    ⋃ a : realSingularities A, circleMap (a.val : ℂ) (ε a) '' Icc 0 Real.pi

end D12Complex.IndentedHalfDisk.Definitions

namespace Specs.D12Complex.Ch08.IndentedHalfDisk
open _root_.D12Complex _root_.D12Complex.IndentedHalfDisk.Definitions

/-- Full finite residue equation, integrability and a genuine canonical cycle.
The trace equality rules out leaving pole-containing diameter paths in the support.
The negative small-arc sign records their clockwise traversal. -/
def finite_indented_half_disk_type : Prop :=
  ∀ (A : Finset ℂ) (f : ℂ → ℂ) (r : ℝ),
    HolomorphicOn (Set.univ \ (A : Set ℂ)) f →
    0 < r → (∀ a ∈ A, ‖a‖ < r) →
    ∃ η : ℝ, 0 < η ∧ ∀ ε : realSingularities A → ℝ,
      (∀ a, 0 < ε a ∧ ε a < η) →
      IntegrableOn (fun x : ℝ => f (x : ℂ))
        (deletedDiameter (realSingularities A) r ε) ∧
      IntervalIntegrable (arcIntegrand f 0 r) volume 0 Real.pi ∧
      (∀ a : realSingularities A,
        IntervalIntegrable (arcIntegrand f (a.val : ℂ) (ε a)) volume 0 Real.pi) ∧
      (∃ Γ : IntegralCycle,
        Γ.trace = boundaryTrace A r ε ∧ Disjoint Γ.trace (A : Set ℂ) ∧
        (∀ a ∈ A, Γ.index a = if 0 < a.im then 1 else 0) ∧
        Γ.integral f = boundaryIntegral A f r ε) ∧
      boundaryIntegral A f r ε = (2 * Real.pi * Complex.I : ℂ) *
        ∑ a ∈ A.filter (fun a => 0 < a.im), Residue.residue f a


/-- The integrability part can be checked independently of the contour construction. -/
def integrability_for_small_radii_type : Prop :=
  ∀ (A : Finset ℂ) (f : ℂ → ℂ),
    HolomorphicOn (Set.univ \ (A : Set ℂ)) f →
    ∀ (r : ℝ), 0 < r → (∀ a ∈ A, ‖a‖ < r) →
    ∃ η : ℝ, 0 < η ∧ ∀ ε : realSingularities A → ℝ,
      (∀ a, 0 < ε a ∧ ε a < η) →
      IntegrableOn (fun x : ℝ => f (x : ℂ))
        (deletedDiameter (realSingularities A) r ε) ∧
      IntervalIntegrable (arcIntegrand f 0 r) volume 0 Real.pi ∧
      ∀ a : realSingularities A,
        IntervalIntegrable (arcIntegrand f (a.val : ℂ) (ε a)) volume 0 Real.pi

/-- Fully proved boundary case with no real excluded points. -/
def no_real_singularities_identity_type : Prop :=
  ∀ (A : Finset ℂ) (f : ℂ → ℂ),
    HolomorphicOn (Set.univ \ (A : Set ℂ)) f →
    ∀ (r : ℝ), 0 < r → (∀ a ∈ A, ‖a‖ < r) →
    (∀ a ∈ A, a.im ≠ 0) →
    (∫ x in Icc (-r) r, f (x : ℂ)) +
      (∫ t in (0 : ℝ)..Real.pi, arcIntegrand f 0 r t) =
      (2 * Real.pi * Complex.I : ℂ) *
        ∑ a ∈ A.filter (fun a => 0 < a.im), Residue.residue f a

/-- The full avoiding cycle witness in the case with no real excluded point.
The radius function has empty domain, so no smallness hypothesis is needed. -/
def no_real_singularities_cycle_type : Prop :=
  ∀ (A : Finset ℂ) (f : ℂ → ℂ),
    HolomorphicOn (Set.univ \ (A : Set ℂ)) f →
    ∀ (r : ℝ), 0 < r → (∀ a ∈ A, ‖a‖ < r) →
    (∀ a ∈ A, a.im ≠ 0) →
    ∀ ε : realSingularities A → ℝ,
      ∃ Γ : IntegralCycle,
        Γ.trace = boundaryTrace A r ε ∧ Disjoint Γ.trace (A : Set ℂ) ∧
        (∀ a ∈ A, Γ.index a = if 0 < a.im then 1 else 0) ∧
        Γ.integral f = boundaryIntegral A f r ε

end Specs.D12Complex.Ch08.IndentedHalfDisk
