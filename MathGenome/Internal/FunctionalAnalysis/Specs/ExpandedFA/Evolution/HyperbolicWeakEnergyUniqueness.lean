import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Evolution.HyperbolicWeakEnergyExistence

/-!
Independent statements for the weak uniqueness and restarting paragraphs of
`fa2:p3:hyperbolic-triple`, paper.tex:15324–15370.

The weak solution is the accepted upstream graph, with the original V and H
norms, actual vector distributional derivatives, and weak representatives at
every time. In particular, neither an energy identity nor strong state
continuity is a hypothesis. The fixed-data singleton case is included.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
universe u v

namespace ExpandedFA.Evolution.HyperbolicWeakEnergyUniquenessSpec
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec

section Spaces
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Uniqueness of the two weak representatives, including the endpoints.
The acceleration is only a Bochner representative and is unique a.e. -/
def WeakUniqueness : Prop := ∀ (j : HilbertTriple V H) (T : ℝ), 0 ≤ T →
  ∀ (a : ℝ → Form V) (α C : ℝ), FormHypotheses j T a α C →
  ∀ (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z w : WeakEnergySolution j T a u₀ v₀ f),
    (∀ t ∈ Set.Icc 0 T,
      z.displacement t = w.displacement t ∧ z.velocity t = w.velocity t) ∧
    z.acceleration =ᵐ[timeMeasureValue T] w.acceleration

/-- Strong continuity of every weak solution, with no strong-energy-identity
assumption and no separability or compact-embedding assumption. -/
def StrongStateContinuity : Prop := ∀ (j : HilbertTriple V H) (T : ℝ), 0 ≤ T →
  ∀ (a : ℝ → Form V) (α C : ℝ), FormHypotheses j T a α C →
  ∀ (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z : WeakEnergySolution j T a u₀ v₀ f),
    ContinuousOn z.displacement (Set.Icc 0 T) ∧
    ContinuousOn z.velocity (Set.Icc 0 T)

/-- Supporting primitive identities for the already prescribed weak
representatives. These give the Banach-valued absolute continuity used in
the integrated test; they do not assert strong continuity in V × H. -/
def PrimitiveRepresentatives : Prop := ∀ (j : HilbertTriple V H) (T : ℝ), 0 < T →
  ∀ (a : ℝ → Form V) (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z : WeakEnergySolution j T a u₀ v₀ f),
    ContinuousOn (fun t => j.embedding (z.displacement t)) (Set.Icc 0 T) ∧
    ContinuousOn (fun t => pivotValue j (z.velocity t)) (Set.Icc 0 T) ∧
    (∀ s t : Set.Icc 0 T,
      j.embedding (z.displacement t) - j.embedding (z.displacement s) =
        ∫ r in s.val..t.val, z.velocity r) ∧
    (∀ s t : Set.Icc 0 T,
      pivotValue j (z.velocity t) - pivotValue j (z.velocity s) =
        ∫ r in s.val..t.val, z.acceleration r)

/-- Equality a.e. suffices for equality of the weak state representatives.
This step uses positive length, while the next statement handles T = 0. -/
def StateEqualityOfAE : Prop := ∀ (j : HilbertTriple V H) (T : ℝ), 0 < T →
  ∀ (a : ℝ → Form V) (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z w : WeakEnergySolution j T a u₀ v₀ f),
    z.displacement =ᵐ[timeMeasureValue T] w.displacement →
    z.velocity =ᵐ[timeMeasureValue T] w.velocity →
    ∀ t ∈ Set.Icc 0 T,
      z.displacement t = w.displacement t ∧ z.velocity t = w.velocity t

def ZeroTimeUniqueness : Prop := ∀ (j : HilbertTriple V H)
  (a : ℝ → Form V) (u₀ : V) (v₀ : H) (f : timeLpValue H 2 0)
  (z w : WeakEnergySolution j 0 a u₀ v₀ f),
  (∀ t ∈ Set.Icc (0 : ℝ) 0,
    z.displacement t = w.displacement t ∧ z.velocity t = w.velocity t) ∧
  z.acceleration =ᵐ[timeMeasureValue 0] w.acceleration

/-- A rigorous integration-by-parts identity for w(t) = ∫_t^T u(r) dr.
This identity uses only the two distributional derivative graphs. -/
def IntegratedPairing : Prop := ∀ (j : HilbertTriple V H) (T : ℝ), 0 < T →
  ∀ (a : ℝ → Form V) (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z : WeakEnergySolution j T a u₀ v₀ f),
    let U : ℝ → V := fun t => ∫ r in 0..t, z.displacement r
    let w : ℝ → V := fun t => U T - U t
    IntervalIntegrable (fun t => z.acceleration t (w t) -
      inner ℝ (z.velocity t) (j.embedding (z.displacement t))) volume 0 T ∧
    (∫ t in 0..T, z.acceleration t (w t) -
      inner ℝ (z.velocity t) (j.embedding (z.displacement t))) =
      -(pivotValue j v₀ (U T))

end Spaces

def WeakUniquenessExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    WeakUniqueness (V := V) (H := H)

def StrongStateContinuityExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    StrongStateContinuity (V := V) (H := H)

def PrimitiveRepresentativesExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    PrimitiveRepresentatives (V := V) (H := H)

def StateEqualityOfAEExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    StateEqualityOfAE (V := V) (H := H)

def ZeroTimeUniquenessExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    ZeroTimeUniqueness (V := V) (H := H)

def IntegratedPairingExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    IntegratedPairing (V := V) (H := H)

end ExpandedFA.Evolution.HyperbolicWeakEnergyUniquenessSpec
