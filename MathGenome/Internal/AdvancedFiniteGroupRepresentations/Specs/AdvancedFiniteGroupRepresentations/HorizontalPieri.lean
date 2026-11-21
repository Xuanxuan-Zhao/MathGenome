import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.CharacteristicMultiplication
import Mathlib.RepresentationTheory.Induced

/-! FR-C07, horizontal part, source lines 1117–1150. Diagrams are the
canonical diagrams of the upstream partitions. The strip condition below
literally means containment and at most one added cell in any column.
The total degree of an extension supplies its required number of cells.
All degrees and alphabet sizes, including zero, are allowed. -/
noncomputable section
open scoped BigOperators DirectSum
namespace Specs.AdvancedFiniteGroupRepresentations

def HorizontalStrip {n m : ℕ} (lam : Partition n) (mu : Partition m) : Prop :=
  cells lam ⊆ cells mu ∧
    Set.InjOn Prod.snd (↑(cells mu \ cells lam) : Set (ℕ × ℕ))

def horizontalExtensions {n : ℕ} (lam : Partition n) (k : ℕ) : Finset (Partition (n+k)) := by
  classical
  exact Finset.univ.filter (HorizontalStrip lam)

/-- The Schur function in the actual upstream graded ring. -/
def schurFunction {n : ℕ} (lam : Partition n) : StableSymmetricRing :=
  DirectSum.of (fun n => stableDegree n) n (stableSchur lam)

/-- The row Schur function. Its specialization to the source's literal
complete homogeneous polynomial is a separate obligation below. -/
def completeFunction (k : ℕ) : StableSymmetricRing :=
  schurFunction (Nat.Partition.indiscrete k)

/-- The actual external tensor product with the trivial complex line. -/
def horizontalPieriInput {n : ℕ} {lam : Partition n}
    (rho : Representation ℂ (SymmetricGroup n) (SpechtModule lam)) (k : ℕ) :
    Representation ℂ (SymmetricGroup n × SymmetricGroup k)
      (TensorProduct ℂ (SpechtModule lam) ℂ) :=
  Representation.tprod (rho.comp (MonoidHom.fst (SymmetricGroup n) (SymmetricGroup k)))
    (Representation.trivial ℂ (SymmetricGroup n × SymmetricGroup k) ℂ)

/-- There is one copy of each allowed shape, with no multiplicity index. -/
def horizontalPieriSum {n : ℕ} (lam : Partition n) (k : ℕ)
    (sigma : (mu : Partition (n+k)) →
      Representation ℂ (SymmetricGroup (n+k)) (SpechtModule mu)) :
    Representation ℂ (SymmetricGroup (n+k))
      (⨁ mu : {mu : Partition (n+k) // HorizontalStrip lam mu}, SpechtModule mu.val) :=
  Representation.directSum (fun mu => sigma mu.val)

def horizontalPieriInputType := ∀ {n : ℕ} {lam : Partition n},
  Representation ℂ (SymmetricGroup n) (SpechtModule lam) → (k : ℕ) →
    Representation ℂ (SymmetricGroup n × SymmetricGroup k)
      (TensorProduct ℂ (SpechtModule lam) ℂ)

def horizontalPieriSumType := ∀ {n : ℕ} (lam : Partition n) (k : ℕ),
  ((mu : Partition (n+k)) → Representation ℂ (SymmetricGroup (n+k)) (SpechtModule mu)) →
    Representation ℂ (SymmetricGroup (n+k))
      (⨁ mu : {mu : Partition (n+k) // HorizontalStrip lam mu}, SpechtModule mu.val)

def HorizontalStripType := {n m : ℕ} → Partition n → Partition m → Prop

def horizontalExtensionsType := {n : ℕ} → (lam : Partition n) →
  (k : ℕ) → Finset (Partition (n+k))
def schurFunctionType := {n : ℕ} → Partition n → StableSymmetricRing
def completeFunctionType := ℕ → StableSymmetricRing

def horizontalStrip_interlacingType : Prop := ∀ {n m} (lam : Partition n) (mu : Partition m),
  HorizontalStrip lam mu ↔
    (∀ i, rowLength lam i ≤ rowLength mu i) ∧
      ∀ i, rowLength mu (i+1) ≤ rowLength lam i

def horizontalStrip_cardType : Prop := ∀ {n k} (lam : Partition n) (mu : Partition (n+k)),
  HorizontalStrip lam mu → (cells mu \ cells lam).card = k

def horizontalStrip_zeroType : Prop := ∀ {n} (lam mu : Partition n),
  HorizontalStrip lam mu ↔ lam = mu

def horizontalStrip_emptyType : Prop := ∀ {k} (mu : Partition k),
  HorizontalStrip emptyPartition mu ↔ mu = Nat.Partition.indiscrete k

def completeFunction_specializationType : Prop := ∀ k r,
  stableSpecialization r (completeFunction k) = h r (k : ℤ)

def schurFunction_specializationType : Prop := ∀ {n} (lam : Partition n) r,
  stableSpecialization r (schurFunction lam) = schurPolynomial lam r

def schurFunction_specialization_zeroType : Prop := ∀ {n r} (lam : Partition n),
  r < length lam → stableSpecialization r (schurFunction lam) = 0

/-- No cutoff on the summation shapes: tall shapes give the stipulated zero. -/
def horizontal_pieri_finiteType : Prop := ∀ {n} (lam : Partition n) (k r : ℕ),
  schurPolynomial lam r * h r (k : ℤ) =
    ∑ mu ∈ horizontalExtensions lam k, schurPolynomial mu r

def horizontal_pieri_stableType : Prop := ∀ {n} (lam : Partition n) (k : ℕ),
  schurFunction lam * completeFunction k =
    ∑ mu ∈ horizontalExtensions lam k, schurFunction mu

/-- The induced class function is exactly the sum of the allowed Specht
characters. This is also an explicit multiplicity-one assertion. -/
def horizontal_pieri_characterType : Prop := ∀ {n} (lam : Partition n) (k : ℕ)
    (rho : Representation ℂ (SymmetricGroup n) (SpechtModule lam))
    (sigma : (mu : Partition (n+k)) →
      Representation ℂ (SymmetricGroup (n+k)) (SpechtModule mu)),
  InheritedSpechtAction lam rho → (∀ mu, InheritedSpechtAction mu (sigma mu)) →
    inducedExternal (representationClassFunction rho)
      (representationClassFunction (Representation.trivial ℂ (SymmetricGroup k) ℂ)) =
        ∑ mu ∈ horizontalExtensions lam k, representationClassFunction (sigma mu)

/-- The representation conclusion, using actual induction and the actual
external tensor product. It includes k=0 and the empty partition. -/
def horizontal_pieri_moduleType : Prop := ∀ {n} (lam : Partition n) (k : ℕ)
    (rho : Representation ℂ (SymmetricGroup n) (SpechtModule lam))
    (sigma : (mu : Partition (n+k)) →
      Representation ℂ (SymmetricGroup (n+k)) (SpechtModule mu)),
  InheritedSpechtAction lam rho → (∀ mu, InheritedSpechtAction mu (sigma mu)) →
    Nonempty ((Representation.ind (A := TensorProduct ℂ (SpechtModule lam) ℂ)
      (blockEmbedding n k) (horizontalPieriInput rho k)).Equiv
      (horizontalPieriSum lam k sigma))

-- Conditional assembly lemmas are recorded as implications, not used as
-- substitutes for the unconditional four Pieri targets above.
def horizontal_pieri_stable_of_finiteType : Prop :=
  horizontal_pieri_finiteType → horizontal_pieri_stableType

def horizontal_pieri_finite_of_stableType : Prop :=
  horizontal_pieri_stableType → horizontal_pieri_finiteType

def horizontal_pieri_character_of_stableType : Prop :=
  horizontal_pieri_stableType → horizontal_pieri_characterType

end Specs.AdvancedFiniteGroupRepresentations
