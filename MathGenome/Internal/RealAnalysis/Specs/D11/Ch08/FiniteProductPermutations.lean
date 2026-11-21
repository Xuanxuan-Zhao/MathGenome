import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-! Independent statements for paper.tex:2753–2788. A bracketing is a
nonempty binary tree; its leaves index arbitrary measurable factor spaces.
`Tuple` uses actual binary products and `tupleMeasure` uses actual binary
product measures, rather than defining the latter by transport from a pi type.
All leaves of a tree, including the one-leaf tree, are retained.

The reindexing equivalence is quantified over all bijections of leaf sets.
Order-preserving bijections give parenthesization changes; arbitrary ones also
give permutations. The recursive integrals are successive integrals all the
way down to individual factors. `ScalarSections` records absolute integrability
and measurability at every stage, with a.e. qualifications at section steps.
-/

open Set MeasureTheory
open scoped ENNReal

universe u v
noncomputable section
namespace Specs.D11.Ch08.FiniteProductPermutations

inductive Bracketing where
  | atom
  | pair (left right : Bracketing)

@[reducible] def Leaves : Bracketing → Type
  | .atom => PUnit
  | .pair l r => Leaves l ⊕ Leaves r

instance leavesFintype : (t : Bracketing) → Fintype (Leaves t)
  | .atom => inferInstanceAs (Fintype PUnit)
  | .pair l r => by
      letI := leavesFintype l
      letI := leavesFintype r
      exact inferInstanceAs (Fintype (Leaves l ⊕ Leaves r))

@[reducible] def Tuple : (t : Bracketing) → (Leaves t → Type u) → Type u
  | .atom, X => X PUnit.unit
  | .pair l r, X => Tuple l (fun i => X (.inl i)) × Tuple r (fun i => X (.inr i))

@[instance_reducible] def tupleSpace : (t : Bracketing) → (X : Leaves t → Type u) →
    (∀ i, MeasurableSpace (X i)) → MeasurableSpace (Tuple t X)
  | .atom, _, m => m PUnit.unit
  | .pair l r, X, m => by
      letI := tupleSpace l (fun i => X (.inl i)) (fun i => m (.inl i))
      letI := tupleSpace r (fun i => X (.inr i)) (fun i => m (.inr i))
      exact inferInstanceAs (MeasurableSpace
        (Tuple l (fun i => X (.inl i)) × Tuple r (fun i => X (.inr i))))

instance tupleMeasurableSpace (t : Bracketing) (X : Leaves t → Type u)
    [m : ∀ i, MeasurableSpace (X i)] : MeasurableSpace (Tuple t X) := tupleSpace t X m

def flatten : (t : Bracketing) → (X : Leaves t → Type u) →
    [∀ i, MeasurableSpace (X i)] → Tuple t X ≃ᵐ (∀ i, X i)
  | .atom, X, _ => (MeasurableEquiv.piUnique X).symm
  | .pair l r, X, m => by
      letI : ∀ i, MeasurableSpace (X (.inl i)) := fun i => m (.inl i)
      letI : ∀ i, MeasurableSpace (X (.inr i)) := fun i => m (.inr i)
      exact ((flatten l (fun i => X (.inl i))).prodCongr
        (flatten r (fun i => X (.inr i)))).trans
          (MeasurableEquiv.sumPiEquivProdPi X).symm

def tupleMeasure : (t : Bracketing) → {X : Leaves t → Type u} →
    [∀ i, MeasurableSpace (X i)] → (∀ i, Measure (X i)) → Measure (Tuple t X)
  | .atom, _, _, μ => μ PUnit.unit
  | .pair l r, X, m, μ => by
      letI : ∀ i, MeasurableSpace (X (.inl i)) := fun i => m (.inl i)
      letI : ∀ i, MeasurableSpace (X (.inr i)) := fun i => m (.inr i)
      exact (tupleMeasure l (fun i => μ (.inl i))).prod (tupleMeasure r (fun i => μ (.inr i)))

/-- The canonical tuple identification, in the direction from reindexed leaves
to the original leaf labels. Its inverse gives the map in the other direction. -/
def rebracket (s t : Bracketing) (e : Leaves s ≃ Leaves t)
    (X : Leaves t → Type u) [∀ i, MeasurableSpace (X i)] :
    Tuple s (fun i => X (e i)) ≃ᵐ Tuple t X := by
  letI : ∀ i, MeasurableSpace (X (e i)) := fun i => inferInstance
  exact ((flatten s (fun i => X (e i))).trans (MeasurableEquiv.piCongrLeft X e)).trans
    (flatten t X).symm

/-- An actual parenthesization with `n + 1` leaves. -/
def rightBracketing : ℕ → Bracketing
  | 0 => .atom
  | n + 1 => .pair .atom (rightBracketing n)

/-- The left-to-right numbering of these leaves, including the one-factor case. -/
def rightLeafOrder : (n : ℕ) → Leaves (rightBracketing n) ≃ Fin (n + 1)
  | 0 => Equiv.ofUnique PUnit (Fin 1)
  | n + 1 =>
      ((Equiv.ofUnique PUnit (Fin 1)).sumCongr (rightLeafOrder n)).trans
        (finSumFinEquiv.trans (finCongr (by omega)))

/-- Read a parenthesized tuple in any specified coordinate order. -/
def coordinates {ι : Type} (t : Bracketing) (e : Leaves t ≃ ι)
    (X : ι → Type u) [∀ i, MeasurableSpace (X i)] :
    Tuple t (fun i => X (e i)) ≃ᵐ (∀ i, X i) :=
  (flatten t (fun i => X (e i))).trans (MeasurableEquiv.piCongrLeft X e)

def iteratedLIntegral : (t : Bracketing) → {X : Leaves t → Type u} →
    [∀ i, MeasurableSpace (X i)] → (∀ i, Measure (X i)) →
    (Tuple t X → ℝ≥0∞) → ℝ≥0∞
  | .atom, _, _, μ, f => ∫⁻ x, f x ∂μ PUnit.unit
  | .pair l r, X, m, μ, f => by
      letI : ∀ i, MeasurableSpace (X (.inl i)) := fun i => m (.inl i)
      letI : ∀ i, MeasurableSpace (X (.inr i)) := fun i => m (.inr i)
      exact iteratedLIntegral l (fun i => μ (.inl i))
        (fun x => iteratedLIntegral r (fun i => μ (.inr i)) (fun y => f (x, y)))

/-- Native scalar integrals are zero on nonintegrable sections. The theorem
below supplies actual measurability and absolute existence at all valid stages. -/
def iteratedIntegral {𝕜 : Type} [RCLike 𝕜] :
    (t : Bracketing) → {X : Leaves t → Type u} → [∀ i, MeasurableSpace (X i)] →
    (∀ i, Measure (X i)) → (Tuple t X → 𝕜) → 𝕜
  | .atom, _, _, μ, f => ∫ x, f x ∂μ PUnit.unit
  | .pair l r, X, m, μ, f => by
      letI : ∀ i, MeasurableSpace (X (.inl i)) := fun i => m (.inl i)
      letI : ∀ i, MeasurableSpace (X (.inr i)) := fun i => m (.inr i)
      exact iteratedIntegral l (fun i => μ (.inl i))
        (fun x => iteratedIntegral r (fun i => μ (.inr i)) (fun y => f (x, y)))

def ScalarSections {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜] :
    (t : Bracketing) → {X : Leaves t → Type u} → [∀ i, MeasurableSpace (X i)] →
    (∀ i, Measure (X i)) → (Tuple t X → 𝕜) → Prop
  | .atom, _, _, μ, f => Measurable f ∧ Integrable f (μ PUnit.unit)
  | .pair l r, X, m, μ, f => by
      letI : ∀ i, MeasurableSpace (X (.inl i)) := fun i => m (.inl i)
      letI : ∀ i, MeasurableSpace (X (.inr i)) := fun i => m (.inr i)
      exact (Measurable f ∧ Integrable f (tupleMeasure (.pair l r) μ)) ∧
      (∀ᵐ x ∂tupleMeasure l (fun i => μ (.inl i)),
        ScalarSections r (fun i => μ (.inr i)) (fun y => f (x, y))) ∧
      ScalarSections l (fun i => μ (.inl i))
        (fun x => iteratedIntegral r (fun i => μ (.inr i)) (fun y => f (x, y)))

/-- In the nonnegative case the successive sections and integral maps are
measurable at every parameter, without any exceptional-set convention. -/
def NonnegativeSections :
    (t : Bracketing) → {X : Leaves t → Type u} → [∀ i, MeasurableSpace (X i)] →
    (∀ i, Measure (X i)) → (Tuple t X → ℝ≥0∞) → Prop
  | .atom, _, _, _, f => Measurable f
  | .pair l r, X, m, μ, f => by
      letI : ∀ i, MeasurableSpace (X (.inl i)) := fun i => m (.inl i)
      letI : ∀ i, MeasurableSpace (X (.inr i)) := fun i => m (.inr i)
      exact Measurable f ∧
        (∀ x, NonnegativeSections r (fun i => μ (.inr i)) (fun y => f (x, y))) ∧
        NonnegativeSections l (fun i => μ (.inl i))
          (fun x => iteratedLIntegral r (fun i => μ (.inr i)) (fun y => f (x, y)))

def rectangle_sigma : Prop :=
  ∀ {ι : Type} [Finite ι] (X : ι → Type u) [∀ i, MeasurableSpace (X i)],
    MeasurableSpace.generateFrom
      (Set.pi Set.univ '' Set.pi Set.univ (fun i => {A : Set (X i) | MeasurableSet A})) =
        (inferInstance : MeasurableSpace (∀ i, X i))

def rectangle_measure : Prop :=
  ∀ {ι : Type} [Fintype ι] {X : ι → Type u} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)],
    SigmaFinite (Measure.pi μ) ∧
    (∀ (A : ∀ i, Set (X i)), (∀ i, MeasurableSet (A i)) →
      Measure.pi μ (Set.pi Set.univ A) = ∏ i, μ i (A i)) ∧
    ∀ η : Measure (∀ i, X i),
      (∀ (A : ∀ i, Set (X i)), (∀ i, MeasurableSet (A i)) →
        η (Set.pi Set.univ A) = ∏ i, μ i (A i)) → η = Measure.pi μ

def tuple_rectangle_sigma : Prop :=
  ∀ (t : Bracketing) (X : Leaves t → Type u) [∀ i, MeasurableSpace (X i)],
    MeasurableSpace.generateFrom
      ((fun A : Set (∀ i, X i) => (flatten t X) ⁻¹' A) ''
        (Set.pi Set.univ '' Set.pi Set.univ (fun i => {A : Set (X i) | MeasurableSet A}))) =
          (inferInstance : MeasurableSpace (Tuple t X))

def flatten_preserving : Prop :=
  ∀ (t : Bracketing) {X : Leaves t → Type u} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)],
    MeasurePreserving (flatten t X) (tupleMeasure t μ) (Measure.pi μ)

def tuple_rectangle_measure : Prop :=
  ∀ (t : Bracketing) {X : Leaves t → Type u} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (A : ∀ i, Set (X i)), (∀ i, MeasurableSet (A i)) →
    tupleMeasure t μ ((flatten t X) ⁻¹' Set.pi Set.univ A) = ∏ i, μ i (A i)

def rebracket_preserving : Prop :=
  ∀ (s t : Bracketing) (e : Leaves s ≃ Leaves t)
    {X : Leaves t → Type u} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)],
    MeasurePreserving (rebracket s t e X)
      (tupleMeasure s (fun i => μ (e i))) (tupleMeasure t μ)

def rebracket_coordinates : Prop :=
  ∀ (s t : Bracketing) (e : Leaves s ≃ Leaves t)
    (X : Leaves t → Type u) [∀ i, MeasurableSpace (X i)]
    (x : Tuple s (fun i => X (e i))) (i : Leaves s),
    flatten t X (rebracket s t e X x) (e i) =
      flatten s (fun j => X (e j)) x i

def positive_arity : Prop :=
  ∀ n : ℕ, ∃ t : Bracketing, Nonempty (Leaves t ≃ Fin (n + 1))

/-- In particular this gives every permutation of `Fin n`, for all `n ≥ 1`.
The reverse map reorders a tuple as `x ↦ (i ↦ x (e i))`. -/
def permutation_preserving : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (X : κ → Type u) [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)],
    MeasurePreserving (MeasurableEquiv.piCongrLeft X e)
      (Measure.pi (fun i => μ (e i))) (Measure.pi μ)

def one_factor : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X),
    rebracket .atom .atom (Equiv.refl _) (fun _ => X) = MeasurableEquiv.refl X ∧
    tupleMeasure .atom (fun _ => μ) = μ ∧
    (∀ f : X → ℝ≥0∞, iteratedLIntegral .atom (fun _ => μ) f = ∫⁻ x, f x ∂μ) ∧
    ∀ {𝕜 : Type} [RCLike 𝕜] (f : X → 𝕜),
      iteratedIntegral .atom (fun _ => μ) f = ∫ x, f x ∂μ

def tonelli_tree : Prop :=
  ∀ (t : Bracketing) {X : Leaves t → Type u} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (f : Tuple t X → ℝ≥0∞), Measurable f →
    (∫⁻ x, f x ∂tupleMeasure t μ) = iteratedLIntegral t μ f

def fubini_tree : Prop :=
  ∀ (t : Bracketing) {X : Leaves t → Type u} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : Tuple t X → 𝕜), Measurable f → Integrable f (tupleMeasure t μ) →
    ScalarSections t μ f ∧ (∫ x, f x ∂tupleMeasure t μ) = iteratedIntegral t μ f

/-- Every numbering of the leaves gives an integration order. In particular
`rightLeafOrder (n-1)` composed with any permutation gives every order for n≥1.
The source's supremum-defined integral is used on the left. -/
def tonelli_all_orders : Prop :=
  ∀ {n : ℕ} (t : Bracketing) (e : Leaves t ≃ Fin n)
    {X : Fin n → Type u} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (f : (∀ i, X i) → ℝ≥0∞), Measurable f →
    NonnegativeSections t (fun i => μ (e i)) (f ∘ coordinates t e X) ∧
    Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value (Measure.pi μ) f =
      iteratedLIntegral t (fun i => μ (e i)) (f ∘ coordinates t e X)

/-- Absolute integrability is the shared source predicate, on the original
sigma-algebra. `ScalarSections` explicitly retains actual measurability as well
as native absolute integrability; the shared scalar bridge identifies these
with source integrability at each successive stage. -/
def fubini_all_orders : Prop :=
  ∀ {n : ℕ} (t : Bracketing) (e : Leaves t ≃ Fin n)
    {X : Fin n → Type u} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : (∀ i, X i) → 𝕜)
    (hf : Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value (Measure.pi μ) f),
    ScalarSections t (fun i => μ (e i)) (f ∘ coordinates t e X) ∧
    Specs.D11.Ch06.ScalarIntegral.scalarIntegral_value (Measure.pi μ) f hf =
      iteratedIntegral t (fun i => μ (e i)) (f ∘ coordinates t e X)

end Specs.D11.Ch08.FiniteProductPermutations
