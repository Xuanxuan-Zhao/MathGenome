import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Orbits

/-! The near-period return branch from paper.tex, d13:14:return-map.
The affine chart of the section is v ↦ p+v, v ∈ ker ℓ. An arbitrary open
section piece S containing zero can be prescribed. The theorem is stronger
than the periodic-orbit specialization: it only needs an actual return at T
and transversality, so in particular applies at the least positive period of
every nonconstant periodic orbit. First-positive-return exclusion is the
separate ReturnMap obligation. -/
noncomputable section
open Set
open scoped ContDiff

namespace Specs.D13Unified.Ch14.ReturnBranch
open _root_.D13Unified _root_.D13Unified.Ch06.StateDerivative
open Ch01.AutonomousParameters
universe u

/-- A return time is unique in one common open time interval about T.
Both the section source and target lie in the prescribed local section S.
The partial homeomorphism and its inverse are Cᵏ on their actual open domains.
All flow evaluations in the uniqueness assertion are admissible. -/
def LocalReturnBranch {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (F : AutonomousODE E) (p : E) (T : ℝ) : Prop :=
    ∀ ℓ : E →L[ℝ] ℝ, ℓ (autonomousEvalValue F p) ≠ 0 →
    ∀ S : Set ℓ.ker, IsOpen S → (0 : ℓ.ker) ∈ S →
    ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
    ∃ τ : ℓ.ker → ℝ, ∃ P : OpenPartialHomeomorph ℓ.ker ℓ.ker,
      (0 : ℓ.ker) ∈ P.source ∧ (0 : ℓ.ker) ∈ P.target ∧
      P.source ⊆ S ∧ P.target ⊆ S ∧
      (∀ v ∈ P.source, p + (v : E) ∈ F.domain) ∧
      (∀ v ∈ P.target, p + (v : E) ∈ F.domain) ∧
      τ 0 = T ∧ P 0 = 0 ∧
      ContDiffOn ℝ k τ P.source ∧ ContDiffOn ℝ k P P.source ∧
      ContDiffOn ℝ k P.symm P.target ∧
      (∀ v ∈ P.source, τ v ∈ Ioo (T-δ) (T+δ)) ∧
      (∀ v ∈ P.source, ∀ t ∈ Ioo (T-δ) (T+δ),
        (t, p + (v : E)) ∈ flowDomain F) ∧
      (∀ v ∈ P.source, flow F (τ v) (p + (v : E)) = p + (P v : E)) ∧
      (∀ v ∈ P.source, ∀ t ∈ Ioo (T-δ) (T+δ),
        ℓ (flow F t (p + (v : E)) - p) = 0 ↔ t = τ v) ∧
      (∀ v : ℓ.ker,
        (fderiv ℝ τ 0) v = -ℓ ((fderiv ℝ (flow F T) p) (v : E)) /
          ℓ (autonomousEvalValue F p)) ∧
      (∀ v : ℓ.ker,
        ((fderiv ℝ (P : ℓ.ker → ℓ.ker) 0) v : E) =
          (fderiv ℝ (flow F T) p) (v : E) -
            (ℓ ((fderiv ℝ (flow F T) p) (v : E)) /
              ℓ (autonomousEvalValue F p)) • autonomousEvalValue F p)


/-- Strong form: any actual transverse return suffices; positivity, leastness
and nonconstancy are not needed for the near-time branch. -/
def ReturnBranchExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ), 1 ≤ k → ∀ (F : AutonomousODE E),
    ContDiffOn ℝ k (autonomousEvalValue F) F.domain →
    ∀ p ∈ F.domain, ∀ T : ℝ, T ∈ (flowInterval F p).carrier → flow F T p = p →
      LocalReturnBranch k F p T

/-- The original periodic-orbit specialization. Completeness, a period and
leastness use exactly the components of Chapter 11's `HasLeastPeriod`, with
the chosen least period named T. -/
def PeriodicReturnBranchExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ), 1 ≤ k → ∀ (F : AutonomousODE E),
    ContDiffOn ℝ k (autonomousEvalValue F) F.domain →
    ∀ p ∈ F.domain, ∀ T : ℝ, 0 < T →
      _root_.D13Unified.Ch11.Orbits.IsComplete F p →
      Function.Periodic (fun t => flow F t p) T →
      (∀ R : ℝ, 0 < R → Function.Periodic (fun t => flow F t p) R → T ≤ R) →
      ¬ _root_.D13Unified.Ch11.Orbits.IsConstant F p → LocalReturnBranch k F p T

end Specs.D13Unified.Ch14.ReturnBranch
