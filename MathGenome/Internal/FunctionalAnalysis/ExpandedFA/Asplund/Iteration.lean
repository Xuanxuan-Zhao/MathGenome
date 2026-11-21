import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Asplund.Iteration
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06Conjugates
import Mathlib.Tactic.Ring

/-! The arithmetic/infimal-convolution iteration on a real normed space,
possibly incomplete. See `fa2:p1:asplund-convex-iteration`.

Definitions accept real-valued functions directly, so no certificates of
convexity, continuity, or attainment are hidden in their construction.
`InitialData` records the original assumptions. Under those assumptions,
`iteration_infima` verifies the genuine infimum at every stage.
Conjugation is the accepted continuous-dual conjugation in `EReal`. -/
namespace ExpandedFA.Asplund.Iteration

/-- The two finite convex initial functions, nonnegative and ordered,
with both values zero at the origin. -/
def InitialData : Spec.InitialDataType := Spec.InitialDataValue

noncomputable def arithmeticMean : Spec.MeanType :=
  fun _ _ _ φ ψ x => (φ x + ψ x) / 2

/-- One half of the infimum of the unscaled sum. Under nonnegativity it
is a genuine finite infimum; no minimizing splitting is required. -/
noncomputable def infimalMean : Spec.MeanType :=
  fun _ _ _ φ ψ x => sInf (Set.range fun y => φ (x + y) + ψ (x - y)) / 2

/-- Simultaneous recursion: both new functions use the previous pair. -/
noncomputable def iteratePair : Spec.IteratePairType := fun E _ _ φ ψ =>
  Nat.rec (φ, ψ) (fun _ p =>
    (arithmeticMean E p.1 p.2, infimalMean E p.1 p.2))

noncomputable def phi : Spec.SequenceType :=
  fun E _ _ φ ψ n => (iteratePair E φ ψ n).1

noncomputable def psi : Spec.SequenceType :=
  fun E _ _ φ ψ n => (iteratePair E φ ψ n).2

/-- Include a finite real function in the established half-extended primal
space, without altering its domain. -/
def finiteExtension : Spec.FiniteExtensionType := fun _ q x => (q x : WithTop ℝ)

/-- The canonical continuous real dual and full extended-real supremum.
In particular this applies to `phi E φ₀ ψ₀ n` and `psi E φ₀ ψ₀ n`. -/
noncomputable def conjugate : Spec.ConjugateType := fun E _ _ q f =>
  P1.C06Conjugates.convexConjugate E (finiteExtension E q) f

@[simp] theorem phi_zero (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ₀ ψ₀ : E → ℝ) (x : E) : phi E φ₀ ψ₀ 0 x = φ₀ x := rfl

@[simp] theorem psi_zero (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ₀ ψ₀ : E → ℝ) (x : E) : psi E φ₀ ψ₀ 0 x = ψ₀ x := rfl

theorem phi_succ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ₀ ψ₀ : E → ℝ) (n : ℕ) (x : E) :
    phi E φ₀ ψ₀ (n + 1) x = (phi E φ₀ ψ₀ n x + psi E φ₀ ψ₀ n x) / 2 := rfl

theorem psi_succ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ₀ ψ₀ : E → ℝ) (n : ℕ) (x : E) :
    psi E φ₀ ψ₀ (n + 1) x =
      sInf (Set.range fun y => phi E φ₀ ψ₀ n (x + y) + psi E φ₀ ψ₀ n (x - y)) / 2 := rfl

theorem iteration_equations : Spec.IterationEquations := by
  intro E _ _ φ₀ ψ₀
  exact ⟨phi_zero E φ₀ ψ₀, psi_zero E φ₀ ψ₀,
    phi_succ E φ₀ ψ₀, psi_succ E φ₀ ψ₀⟩

/-- Zero is a lower bound for the splitting sums. -/
theorem splitting_bddBelow {E : Type*} [NormedAddCommGroup E]
    (φ ψ : E → ℝ) (hφ : ∀ x, 0 ≤ φ x) (hψ : ∀ x, 0 ≤ ψ x) (x : E) :
    BddBelow (Set.range fun y => φ (x + y) + ψ (x - y)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact add_nonneg (hφ _) (hψ _)

theorem infimalMean_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ ψ : E → ℝ) (hφ : ∀ x, 0 ≤ φ x) (hψ : ∀ x, 0 ≤ ψ x) (x : E) :
    0 ≤ infimalMean E φ ψ x := by
  apply div_nonneg _ (by norm_num)
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨y, rfl⟩
  exact add_nonneg (hφ _) (hψ _)

theorem infimalMean_isGLB : Spec.InfimalMeanIsGLB := by
  intro E _ _ φ ψ hφ hψ x
  have heq : 2 * infimalMean E φ ψ x =
      sInf (Set.range fun y => φ (x + y) + ψ (x - y)) := by
    dsimp [infimalMean]
    ring
  change IsGLB (Set.range fun y => φ (x + y) + ψ (x - y))
    (2 * infimalMean E φ ψ x)
  rw [heq]
  exact isGLB_csInf (Set.range_nonempty _) (splitting_bddBelow φ ψ hφ hψ x)

/-- The only induction needed to justify the real infimum: nonnegative
functions produce nonnegative functions at the next stage. -/
theorem iterates_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ₀ ψ₀ : E → ℝ) (hφ : ∀ x, 0 ≤ φ₀ x) (hψ : ∀ x, 0 ≤ ψ₀ x) :
    ∀ n, (∀ x, 0 ≤ phi E φ₀ ψ₀ n x) ∧ (∀ x, 0 ≤ psi E φ₀ ψ₀ n x) := by
  intro n
  induction n with
  | zero => exact ⟨hφ, hψ⟩
  | succ n ih =>
    constructor
    · intro x
      rw [phi_succ]
      exact div_nonneg (add_nonneg (ih.1 x) (ih.2 x)) (by norm_num)
    · exact infimalMean_nonneg _ _ ih.1 ih.2

theorem iteration_infima : Spec.IterationInfima := by
  intro E _ _ φ₀ ψ₀ h n
  have hφ : ∀ x, 0 ≤ φ₀ x := fun x => (h.2.2.1 x).trans (h.2.2.2.1 x)
  have hn := iterates_nonneg φ₀ ψ₀ hφ h.2.2.1 n
  refine ⟨hn.1, hn.2, ?_⟩
  intro x
  exact infimalMean_isGLB E _ _ hn.1 hn.2 x

theorem finiteExtension_proper : Spec.FiniteExtensionProper := by
  intro E _ q
  constructor
  · ext x
    simp [P1.ExtendedConvexFunctions.Spec.finiteDomainValue, Spec.finiteExtensionValue]
  · exact ⟨Classical.arbitrary E, WithTop.coe_ne_top⟩

theorem conjugate_formula : Spec.ConjugateFormula := by
  intro E _ _ q f
  apply iSup_congr
  intro x
  exact (EReal.coe_sub (f x) (q x)).symm

theorem conjugate_ne_bot : Spec.ConjugateNeverBottom := by
  intro E _ _ q f
  exact P1.C06Conjugates.convexConjugate_ne_bot E (finiteExtension E q)
    (finiteExtension_proper E q).2 f

end ExpandedFA.Asplund.Iteration
