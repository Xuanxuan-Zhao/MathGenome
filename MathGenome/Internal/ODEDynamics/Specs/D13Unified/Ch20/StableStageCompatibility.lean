import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Flow
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.CountableImmersedAtlas

/-! Independent statement of the stage geometry in paper.tex, Remark
`d13:20:local-global`. All times refer to the original canonical maximal flow.
The open set V is allowed to be empty. Nonemptiness is needed only when
packaging the data for the nonempty-union atlas interface. -/
noncomputable section
open Set Function
open scoped ContDiff
namespace D13Unified.Ch20.StableStageCompatibility
open Ch06.StateDerivative Specs.D13Unified.Ch11.Flow
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual backward survival domain in parameter coordinates. -/
def stageDomain (F : AutonomousODE E) (G : S → E) (V : Set S) (m : ℕ) : Set S :=
  V ∩ G ⁻¹' timeDomainValue F (-(m : ℝ))

/-- The parametrization at the m-th backward stage, meaningful on stageDomain. -/
def stageMap (F : AutonomousODE E) (G : S → E) (m : ℕ) (ξ : S) : E :=
  flow F (-(m : ℝ)) (G ξ)

/-- The prescribed forward formula, extended as a total function off its source. -/
def transition (F : AutonomousODE E) (G : S → E) (P : E → S)
    (m n : ℕ) (ξ : S) : S := P (flow F (n : ℝ) (stageMap F G m ξ))

/-- Original assumptions: a split smooth parametrization and a forward invariant
open portion, with complete forward trajectories but no backward completeness. -/
structure Hypotheses (F : AutonomousODE E) (k : ℕ∞)
    (G : S → E) (P : E → S) (V : Set S) : Prop where
  one_le : 1 ≤ k
  field_regular : ContDiffOn ℝ (k : ℕ∞ω) (Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue F) F.domain
  graph_regular : ContDiff ℝ (k : ℕ∞ω) G
  projection_regular : ContDiff ℝ (k : ℕ∞ω) P
  left_inverse : LeftInverse P G
  graph_differential : ∀ ξ, Injective (fderiv ℝ G ξ)
  open_portion : IsOpen V
  admissible : ∀ ξ ∈ V, G ξ ∈ F.domain
  forward_exists : ∀ ξ ∈ V, ∀ t : ℝ, 0 ≤ t → G ξ ∈ timeDomainValue F t
  forward_invariant : ∀ ξ ∈ V, ∀ t : ℝ, 0 ≤ t → flow F t (G ξ) ∈ G '' V

/-- All stage geometry, including full-rank open coordinate inclusions.
Neither an open overlap nor a stage atlas is an input. -/
structure CompatibleStages (F : AutonomousODE E) (k : ℕ∞)
    (G : S → E) (P : E → S) (V : Set S) where
  open_domain : ∀ m, IsOpen (stageDomain F G V m)
  regular : ∀ m, ContDiffOn ℝ (k : ℕ∞ω) (stageMap F G m) (stageDomain F G V m)
  injective : ∀ m, InjOn (stageMap F G m) (stageDomain F G V m)
  differential : ∀ m ξ, ξ ∈ stageDomain F G V m → Injective (fderiv ℝ (stageMap F G m) ξ)
  change : ∀ m n : ℕ, m ≤ n → OpenPartialHomeomorph S S
  change_source : ∀ m n h, (change m n h).source = stageDomain F G V m
  change_target : ∀ m n h, (change m n h).target ⊆ stageDomain F G V n
  change_regular : ∀ m n h, ContDiffOn ℝ (k : ℕ∞ω) (change m n h) (change m n h).source
  change_symm_regular : ∀ m n h,
    ContDiffOn ℝ (k : ℕ∞ω) (change m n h).symm (change m n h).target
  change_formula : ∀ m n h ξ, ξ ∈ stageDomain F G V m →
    change m n h ξ = transition F G P m n ξ
  change_symm_formula : ∀ m n h η, η ∈ (change m n h).target →
    (change m n h).symm η = P (flow F ((m : ℝ) - n) (G η))
  change_differential : ∀ m n h ξ, ξ ∈ stageDomain F G V m →
    Bijective (fderiv ℝ (change m n h) ξ)
  forward_domain : ∀ (m n : ℕ) (_h : m ≤ n) (ξ : S), ξ ∈ stageDomain F G V m →
    stageMap F G m ξ ∈ timeDomainValue F (n : ℝ)
  backward_domain : ∀ m n h η, η ∈ (change m n h).target →
    G η ∈ timeDomainValue F ((m : ℝ) - n)
  forward_graph : ∀ m n h ξ, ξ ∈ stageDomain F G V m →
    G (change m n h ξ) = flow F (n : ℝ) (stageMap F G m ξ)
  intertwine : ∀ m n h ξ, ξ ∈ stageDomain F G V m →
    stageMap F G n (change m n h ξ) = stageMap F G m ξ

end D13Unified.Ch20.StableStageCompatibility

namespace Specs.D13Unified.Ch20.StableStageCompatibility
open _root_.D13Unified _root_.D13Unified.Ch20.StableStageCompatibility

def compatibilityExpected : Prop :=
  ∀ (S E : Type*) [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E) (k : ℕ∞) (G : S → E) (P : E → S) (V : Set S),
    Hypotheses F k G P V → Nonempty (CompatibleStages F k G P V)

/-- Package directly for the upstream generic atlas theorem. The main geometry
above has no nonemptiness hypothesis; this output uses the atlas interface's
necessary nonemptiness of the union. -/
def atlasPackageExpected : Prop :=
  ∀ (S E : Type*) [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E) (k : ℕ∞) (G : S → E) (P : E → S) (V : Set S),
    Hypotheses F k G P V → V.Nonempty →
    ∃ D : Ch20.CountableImmersedAtlas.Data S E k,
      D.U = stageDomain F G V ∧ D.f = stageMap F G

end Specs.D13Unified.Ch20.StableStageCompatibility
