import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.Definitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.OperatorDomains
import Mathlib.Analysis.InnerProductSpace.Dual

/-! Independent specifications for paper.tex:7633–7643, 8062–8067,
8939–8956, with the canonical exact-domain operators of Part III.
All order pairings use the continuous real-linear dual. No completeness,
reflexivity, nontriviality, closedness, or density is implicit in these definitions.
The Hilbert transport below uses real Riesz, rather than a new pairing. -/
namespace ExpandedFA.Monotone.Spec
universe u

def MapGraphType :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X], 
    (X → X →L[ℝ] ℝ) → Set (X × (X →L[ℝ] ℝ))

def MapGraphValue : MapGraphType.{u} :=
  fun _ _ _ A => {p | p.2 = A p.1}

def MonotoneType :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X], 
    Set (X × (X →L[ℝ] ℝ)) → Prop

def MonotoneValue : MonotoneType.{u} :=
  fun X _ _ A => ∀ ⦃x y : X⦄ ⦃f g : X →L[ℝ] ℝ⦄, (x, f) ∈ A → (y, g) ∈ A → 0 ≤ (f - g) (x - y)

def MaximalMonotoneType :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X], 
    Set (X × (X →L[ℝ] ℝ)) → Prop

def MaximalMonotoneValue : MaximalMonotoneType.{u} :=
  fun X _ _ A => MonotoneValue X A ∧ ∀ B, MonotoneValue X B → A ⊆ B → B = A

def MonotoneOnType :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X], 
    (X → X →L[ℝ] ℝ) → Set X → Prop

def MonotoneOnValue : MonotoneOnType.{u} :=
  fun _ _ _ A D => ∀ x ∈ D, ∀ y ∈ D, 0 ≤ (A x - A y) (x - y)

def MonotoneMapType :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X], 
    (X → X →L[ℝ] ℝ) → Prop

def MonotoneMapValue : MonotoneMapType.{u} :=
  fun _ _ _ A => ∀ x y, 0 ≤ (A x - A y) (x - y)

def StrictMonotoneMapType :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X], 
    (X → X →L[ℝ] ℝ) → Prop

def StrictMonotoneMapValue : StrictMonotoneMapType.{u} :=
  fun _ _ _ A => ∀ x y, x ≠ y → 0 < (A x - A y) (x - y)

def BoundedOnBoundedSetsType :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X], 
    (X → X →L[ℝ] ℝ) → Prop

def BoundedOnBoundedSetsValue : BoundedOnBoundedSetsType.{u} :=
  fun X _ _ A => ∀ D : Set X, Bornology.IsBounded D → Bornology.IsBounded (A '' D)

def HemicontinuousType :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X], 
    (X → X →L[ℝ] ℝ) → Prop

def HemicontinuousValue : HemicontinuousType.{u} :=
  fun X _ _ A => ∀ x y z : X, Continuous (fun t : ℝ => A (x + t • y) z)

def CoerciveType :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X], 
    (X → X →L[ℝ] ℝ) → Prop

def CoerciveValue : CoerciveType.{u} :=
  fun X _ _ A => Filter.Tendsto (fun x => A x x / ‖x‖) (Filter.comap (fun x : X => ‖x‖) Filter.atTop) Filter.atTop

def LinearGraphType :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X], 
    ExpandedFA.Unbounded.Operator ℝ X (X →L[ℝ] ℝ) → Set (X × (X →L[ℝ] ℝ))

def LinearGraphValue : LinearGraphType.{u} :=
  fun _ _ _ A => (A.graph : Set _)

def LinearMonotoneType :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X], 
    ExpandedFA.Unbounded.Operator ℝ X (X →L[ℝ] ℝ) → Prop

def LinearMonotoneValue : LinearMonotoneType.{u} :=
  fun X _ _ A => MonotoneValue X (LinearGraphValue X A)

def LinearMaximalMonotoneType :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X], 
    ExpandedFA.Unbounded.Operator ℝ X (X →L[ℝ] ℝ) → Prop

def LinearMaximalMonotoneValue : LinearMaximalMonotoneType.{u} :=
  fun X _ _ A => MaximalMonotoneValue X (LinearGraphValue X A)

/-- Transport a Hilbert graph by the real Riesz embedding in its second coordinate.
It is defined already on pre-Hilbert spaces; the inverse identification below
uses completeness precisely where Riesz surjectivity is needed. -/
def HilbertGraphType :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    Set (H × H) → Set (H × (H →L[ℝ] ℝ))
def HilbertGraphValue : HilbertGraphType.{u} :=
  fun H _ _ A => (fun p : H × H => (p.1, InnerProductSpace.toDualMap ℝ H p.2)) '' A

/-- No larger graph is allowed, including nonlinear and multivalued extensions. -/
def MaximalityLaw : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : Set (X × (X →L[ℝ] ℝ))),
    MaximalMonotoneValue X A ↔ MonotoneValue X A ∧
      ∀ x f, (∀ y g, (y, g) ∈ A → 0 ≤ (f - g) (x - y)) → (x, f) ∈ A

def MapGraphLaw : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : X → X →L[ℝ] ℝ),
    MonotoneValue X (MapGraphValue X A) ↔ MonotoneMapValue X A

def MonotoneOnLaw : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : X → X →L[ℝ] ℝ) (D : Set X),
    MonotoneOnValue X A D ↔ MonotoneValue X {p | p.1 ∈ D ∧ p.2 = A p.1}

def StrictMonotonicityLaw : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : X → X →L[ℝ] ℝ), StrictMonotoneMapValue X A → MonotoneMapValue X A

def LinearGraphLaw : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : ExpandedFA.Unbounded.Operator ℝ X (X →L[ℝ] ℝ)) (x : X) (f : X →L[ℝ] ℝ),
    (x, f) ∈ LinearGraphValue X A ↔ ∃ hx : x ∈ A.domain, A ⟨x, hx⟩ = f

def LinearMonotonicityLaw : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : ExpandedFA.Unbounded.Operator ℝ X (X →L[ℝ] ℝ)),
    LinearMonotoneValue X A ↔ ∀ x y : A.domain, 0 ≤ (A x - A y) ((x : X) - y)

def LinearPositivityLaw : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : ExpandedFA.Unbounded.Operator ℝ X (X →L[ℝ] ℝ)),
    LinearMonotoneValue X A ↔ ∀ x : A.domain, 0 ≤ A x (x : X)

/-- A threshold formulation of the exact quotient limit, not a quadratic
lower bound or a norm-only growth condition. Valid also on the zero space. -/
def CoercivityLaw : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : X → X →L[ℝ] ℝ),
    CoerciveValue X A ↔ ∀ M : ℝ, ∃ R : ℝ, ∀ x : X, R ≤ ‖x‖ → M ≤ A x x / ‖x‖

def HilbertMonotonicityLaw : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (A : Set (H × H)),
    MonotoneValue H (HilbertGraphValue H A) ↔
      ∀ ⦃x y a b : H⦄, (x, a) ∈ A → (y, b) ∈ A → 0 ≤ inner ℝ (a - b) (x - y)

def HilbertRieszLaw : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : Set (H × H)) (x : H) (f : H →L[ℝ] ℝ),
    (x, f) ∈ HilbertGraphValue H A ↔ (x, (InnerProductSpace.toDual ℝ H).symm f) ∈ A

def SubgradientGraphType :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X],
    ExpandedFA.P1.ExtendedConvexFunctions.ExtendedFunction X → Set (X × (X →L[ℝ] ℝ))
def SubgradientGraphValue : SubgradientGraphType.{u} :=
  fun X _ _ φ => {p | p.2 ∈ ExpandedFA.BanachConvex.Spec.SubdifferentialValue X φ p.1}

/-- The same maximality criterion in Hilbert coordinates. Riesz surjectivity
ensures that all dual-valued possible extensions are tested. -/
def HilbertMaximalityLaw : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : Set (H × H)),
    MaximalMonotoneValue H (HilbertGraphValue H A) ↔
      (∀ ⦃x y a b : H⦄, (x, a) ∈ A → (y, b) ∈ A →
        0 ≤ inner ℝ (a - b) (x - y)) ∧
      ∀ x a, (∀ y b, (y, b) ∈ A → 0 ≤ inner ℝ (a - b) (x - y)) → (x, a) ∈ A

end ExpandedFA.Monotone.Spec
