import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.FirstIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.LinearAlgebra.Determinant

/-! Independent scope of paper.tex, Proposition d13:11:hamiltonian.
Coordinates 0,…,m-1 are q, and m,…,2m-1 are p. Ambient representatives
are used only on the given open domain. There is no completeness assumption.
The case m = 0 is included. -/
noncomputable section
open Set MeasureTheory

namespace Specs.D13Unified.Ch11.Hamiltonian
open _root_.D13Unified _root_.D13Unified.Ch06.StateDerivative
open Ch01.AutonomousParameters Ch01.SolutionConcepts Ch11.Flow

abbrev Phase (m : ℕ) := Fin (m + m) → ℝ

/-- The canonical Hamiltonian field (H_p,-H_q), in standard coordinates. -/
def vectorField {m : ℕ} (H : Phase m → ℝ) (x : Phase m) : Phase m :=
  Fin.addCases
    (fun i : Fin m => (fderiv ℝ H x) (Pi.single (Fin.natAdd m i) 1))
    (fun i : Fin m => -(fderiv ℝ H x) (Pi.single (Fin.castAdd m i) 1))

lemma vectorField_contDiffOn {m : ℕ} {Ω : Set (Phase m)} (hΩ : IsOpen Ω)
    {H : Phase m → ℝ} (hH : ContDiffOn ℝ 2 H Ω) :
    ContDiffOn ℝ 1 (vectorField H) Ω := by
  have hd : ContDiffOn ℝ 1 (fderiv ℝ H) Ω := hH.fderiv_of_isOpen hΩ (by norm_num)
  apply contDiffOn_pi.mpr
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [vectorField, Fin.addCases_left] using hd.clm_apply contDiffOn_const
  · simpa only [vectorField, Fin.addCases_right] using (hd.clm_apply (contDiffOn_const (c := Pi.single (Fin.castAdd m j) 1))).neg

/-- The original equation, with exactly Ω as its state domain. Continuity is
derived from C² regularity of H, rather than supplied as a new hypothesis. -/
def equation {m : ℕ} (Ω : Set (Phase m)) (hΩ : IsOpen Ω)
    (H : Phase m → ℝ) (hH : ContDiffOn ℝ 2 H Ω) : AutonomousODE (Phase m) where
  domain := Ω
  isOpen_domain := hΩ
  field := fun x => vectorField H x.val
  continuous_field := (vectorField_contDiffOn hΩ hH).continuousOn.domRestrict

/-- Constancy at any two times of every classical solution; in particular this
covers every maximal solution object. -/
def Energy : Prop :=
  ∀ (m : ℕ) (Ω : Set (Phase m)) (hΩ : IsOpen Ω) (H : Phase m → ℝ)
    (hH : ContDiffOn ℝ 2 H Ω),
    ∀ (I : OpenTimeInterval) (x : ℝ → Phase m),
      classicalSolutionOnValue (autonomousToODEValue (equation Ω hΩ H hH)) I x →
      ∀ s ∈ I.carrier, ∀ t ∈ I.carrier, H (x t) = H (x s)

/-- The actual local time diffeomorphism, with its actual reverse-time codomain,
including the exact (positive, rather than absolute) Jacobian determinant. -/
def TimeMaps : Prop :=
  ∀ (m : ℕ) (Ω : Set (Phase m)) (hΩ : IsOpen Ω) (H : Phase m → ℝ)
    (hH : ContDiffOn ℝ 2 H Ω) (t : ℝ),
    let F := equation Ω hΩ H hH
    IsOpen (timeDomainValue F t) ∧ IsOpen (timeDomainValue F (-t)) ∧
    (flow F t) '' timeDomainValue F t = timeDomainValue F (-t) ∧
    (∃ e : OpenPartialHomeomorph (Phase m) (Phase m),
      e.source = timeDomainValue F t ∧ e.target = timeDomainValue F (-t) ∧
      (e : Phase m → Phase m) = flow F t ∧
      (e.symm : Phase m → Phase m) = flow F (-t) ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target) ∧
    ∀ x ∈ timeDomainValue F t, (fderiv ℝ (flow F t) x).det = 1

/-- Lebesgue measurable subsets of the survival domain, measured in the ambient
codomain after mapping. NullMeasurableSet includes the Lebesgue completion,
so this also covers subsets of Borel null sets. Infinite measure is allowed. -/
def Volume : Prop :=
  ∀ (m : ℕ) (Ω : Set (Phase m)) (hΩ : IsOpen Ω) (H : Phase m → ℝ)
    (hH : ContDiffOn ℝ 2 H Ω) (t : ℝ),
    let F := equation Ω hΩ H hH
    ∀ A : Set (Phase m), A ⊆ timeDomainValue F t → NullMeasurableSet A volume →
      NullMeasurableSet ((flow F t) '' A) volume ∧
      volume ((flow F t) '' A) = volume A

end Specs.D13Unified.Ch11.Hamiltonian
