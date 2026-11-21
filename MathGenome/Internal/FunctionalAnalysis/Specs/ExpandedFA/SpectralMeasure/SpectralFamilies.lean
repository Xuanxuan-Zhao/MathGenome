import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.NormalSpectralTests
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Spectral families in `fa2:p2:spectral-corollaries` (paper.tex 12578–12607).
The PVM lives on the actual complex spectrum. For self-adjoint A this spectrum
is real; taking the real part below therefore gives precisely (-∞,t].
All statements include the zero Hilbert space. -/
noncomputable section
open scoped InnerProductSpace
open Set Filter
namespace ExpandedFA.SpectralMeasure.SpectralFamilies.Spec
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The closed, right-continuous spectral cut. -/
def cut (A : H →L[ℂ] H) (t : ℝ) : Set (spectrum ℂ A) :=
  {z | (z : ℂ).re ≤ t}

def family {A : H →L[ℂ] H} (E : ProjectionValuedMeasure (spectrum ℂ A) H)
    (t : ℝ) : H →L[ℂ] H := E (cut A t)

/-- Increasing means inclusion of the closed ranges of the orthogonal
projections. Right continuity and both limits are strong, not norm, limits. -/
def FamilyProperties : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H), IsSelfAdjoint A →
    ∀ E : ProjectionValuedMeasure (spectrum ℂ A) H, NormalPVM.Spec.Resolves A E →
      (∀ t, IsSelfAdjoint (family E t) ∧ family E t * family E t = family E t) ∧
      (∀ s t, s ≤ t → LinearMap.range (family E s).toLinearMap ≤
        LinearMap.range (family E t).toLinearMap) ∧
      (∀ t x, Tendsto (fun r => family E r x) (nhdsWithin t (Ici t))
        (nhds (family E t x))) ∧
      (∀ x, Tendsto (fun t => family E t x) atBot (nhds 0)) ∧
      (∀ x, Tendsto (fun t => family E t x) atTop (nhds x))

/-- A finite tagged subdivision. Repeated vertices are harmless and allowed;
`n = 0` is possible exactly on a singleton interval. -/
structure TaggedPartition (m M : ℝ) where
  n : ℕ
  point : Fin (n + 1) → ℝ
  mono : Monotone point
  first : point 0 = m
  last : point (Fin.last n) = M
  tag : Fin n → ℝ
  tag_mem : ∀ i, point i.castSucc ≤ tag i ∧ tag i ≤ point i.succ

namespace TaggedPartition
variable {m M : ℝ}

def mesh (P : TaggedPartition m M) : ℝ :=
  ((Finset.univ.sup (fun i : Fin P.n => (P.point i.succ - P.point i.castSucc).toNNReal) : NNReal) : ℝ)

def lowerTag (P : TaggedPartition m M) : ℝ :=
  if h : 0 < P.n then P.tag ⟨0, h⟩ else m

/-- The explicit lower atom is the meaning of `m-0`. The remaining
increments use (pᵢ,pᵢ₊₁]. The atom takes the first cell's tag, so the
first tagged cell is [m,p₁], with the other cells half open. For n=0 the
singleton sum is m times its atom. -/
def operatorSum (P : TaggedPartition m M) {A : H →L[ℂ] H}
    (E : ProjectionValuedMeasure (spectrum ℂ A) H) : H →L[ℂ] H :=
  (P.lowerTag : ℂ) • family E m + ∑ i : Fin P.n,
    (P.tag i : ℂ) • (family E (P.point i.succ) - family E (P.point i.castSucc))

/-- Ordinary tagged Stieltjes sums, with the lower endpoint atom retained.
This is defined for any complex distribution function, not through A. -/
def scalarSum (P : TaggedPartition m M) (F : ℝ → ℂ) (lowerAtom : ℂ) : ℂ :=
  (P.lowerTag : ℂ) * lowerAtom + ∑ i : Fin P.n,
    (P.tag i : ℂ) * (F (P.point i.succ) - F (P.point i.castSucc))

end TaggedPartition

/-- The ordinary epsilon/mesh definition of the scalar Riemann--Stieltjes
integral ∫_{m-0}^M t dF(t), including a separately specified lower atom.
No measure integral or operator identity is assumed by this definition. -/
def HasStieltjesIntegral (m M : ℝ) (F : ℝ → ℂ) (lowerAtom value : ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ P : TaggedPartition m M,
    P.mesh < δ → ‖P.scalarSum F lowerAtom - value‖ < ε

/-- Exact mesh error for every tagged subdivision; its epsilon form records
operator norm convergence. The scalar conclusion is the ordinary Stieltjes
integral of each coefficient distribution, retaining the atom at m. -/
def StieltjesApproximation : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H), IsSelfAdjoint A →
    ∀ E : ProjectionValuedMeasure (spectrum ℂ A) H, NormalPVM.Spec.Resolves A E →
    ∀ m M : ℝ, (∀ z ∈ spectrum ℂ A, m ≤ z.re ∧ z.re ≤ M) →
      (∀ P : TaggedPartition m M, ‖P.operatorSum E - A‖ ≤ P.mesh) ∧
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ P : TaggedPartition m M,
        P.mesh < δ → ‖P.operatorSum E - A‖ < ε) ∧
      (∀ x y : H,
        HasStieltjesIntegral m M (fun t => ⟪x, family E t y⟫_ℂ)
          ⟪x, E {z | (z : ℂ) = (m : ℂ)} y⟫_ℂ ⟪x, A y⟫_ℂ) ∧
      (m = M → A = (m : ℂ) • (1 : H →L[ℂ] H))

end ExpandedFA.SpectralMeasure.SpectralFamilies.Spec
