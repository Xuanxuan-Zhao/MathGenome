import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Dual
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! Independent specification of paper.tex:3540–3557 and the notation at 3561.
The scalar field here is real, as required by this particular paragraph.
`convexHull` means the ordinary finite convex hull, without closure.
No completeness, separability, or nontriviality hypothesis is imposed. -/

universe u
namespace ExpandedFA.P1.JamesBlockObjects.Spec

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Norm boundedness of a sequence in the continuous linear dual. -/
def BoundedSequence (f : ℕ → E →L[ℝ] ℝ) : Prop := ∃ C : ℝ, ∀ n, ‖f n‖ ≤ C

def LType := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
  (ℕ → E →L[ℝ] ℝ) → Set (E →L[ℝ] ℝ)

def LValue : LType.{u} := fun f =>
  {w | ∀ x, w x ≤ Filter.limsup (fun n => f n x) Filter.atTop}

def VType := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
  (ℕ → E →L[ℝ] ℝ) → Set (ℕ → E →L[ℝ] ℝ)

def VValue : VType.{u} := fun f =>
  {g | ∀ n, g n ∈ convexHull ℝ (f '' Set.Ici n)}

def NormOnType := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
  Set E → (E →L[ℝ] ℝ) → ℝ

noncomputable def NormOnValue : NormOnType.{u} := fun A h => sSup ((fun x => |h x|) '' A)

def LNonempty : Prop := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f : ℕ → E →L[ℝ] ℝ), BoundedSequence f → (LValue f).Nonempty

def LBounds : Prop := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f : ℕ → E →L[ℝ] ℝ), BoundedSequence f → ∀ w ∈ LValue f, ∀ x,
  Filter.liminf (fun n => f n x) Filter.atTop ≤ w x ∧
  w x ≤ Filter.limsup (fun n => f n x) Filter.atTop

def VTransitive : Prop := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f g : ℕ → E →L[ℝ] ℝ), g ∈ VValue f → VValue g ⊆ VValue f

def LMonotone : Prop := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f g : ℕ → E →L[ℝ] ℝ), BoundedSequence f → g ∈ VValue f → LValue g ⊆ LValue f

def SubsequenceMemV : Prop := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f : ℕ → E →L[ℝ] ℝ) (φ : ℕ → ℕ), StrictMono φ → (f ∘ φ) ∈ VValue f

/-- The supremum is finite and has its usual least-upper-bound meaning on the
specified nonempty bounded sets. This also guards against vacuous real sSup use. -/
def NormOnIsLUB : Prop := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (A : Set E), A.Nonempty → Bornology.IsBounded A → ∀ h : E →L[ℝ] ℝ,
  IsLUB ((fun x => |h x|) '' A) (NormOnValue A h)

end ExpandedFA.P1.JamesBlockObjects.Spec
