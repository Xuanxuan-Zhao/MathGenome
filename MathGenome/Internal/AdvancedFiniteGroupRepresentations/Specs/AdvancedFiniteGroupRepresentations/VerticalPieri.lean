import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.HorizontalPieri

/-! FR-C07, vertical Pieri rule (source lines 1117–1160).
The strip consists of exactly k new cells, with at most one per row.
The degree fixes its cardinality; no positivity restrictions are imposed. -/
noncomputable section
open scoped BigOperators DirectSum
namespace Specs.AdvancedFiniteGroupRepresentations

def VerticalStrip {n m : ℕ} (lam : Partition n) (mu : Partition m) : Prop :=
  cells lam ⊆ cells mu ∧
    Set.InjOn Prod.fst (↑(cells mu \ cells lam) : Set (ℕ × ℕ))

def verticalExtensions {n : ℕ} (lam : Partition n) (k : ℕ) : Finset (Partition (n+k)) := by
  classical
  exact Finset.univ.filter (VerticalStrip lam)

/-- A column Schur function; the literal elementary polynomial is identified below. -/
def elementaryFunction (k : ℕ) : StableSymmetricRing :=
  schurFunction (transpose (Nat.Partition.indiscrete k))

/-- The complex sign line with its actual permutation action. -/
def signLine (k : ℕ) : Representation ℂ (SymmetricGroup k) ℂ where
  toFun g := permutationSign g • LinearMap.id
  map_one' := by
    ext z
    simp [permutationSign]
  map_mul' g h := by
    ext z
    simp [permutationSign, mul_smul, mul_comm]

def verticalPieriInput {n : ℕ} {lam : Partition n}
    (rho : Representation ℂ (SymmetricGroup n) (SpechtModule lam)) (k : ℕ) :
    Representation ℂ (SymmetricGroup n × SymmetricGroup k)
      (TensorProduct ℂ (SpechtModule lam) ℂ) :=
  Representation.tprod (rho.comp (MonoidHom.fst (SymmetricGroup n) (SymmetricGroup k)))
    ((signLine k).comp (MonoidHom.snd (SymmetricGroup n) (SymmetricGroup k)))

def verticalPieriSum {n : ℕ} (lam : Partition n) (k : ℕ)
    (sigma : (mu : Partition (n+k)) →
      Representation ℂ (SymmetricGroup (n+k)) (SpechtModule mu)) :
    Representation ℂ (SymmetricGroup (n+k))
      (⨁ mu : {mu : Partition (n+k) // VerticalStrip lam mu}, SpechtModule mu.val) :=
  Representation.directSum (fun mu => sigma mu.val)

def VerticalStripType := {n m : ℕ} → Partition n → Partition m → Prop
def verticalExtensionsType := {n : ℕ} → (lam : Partition n) →
  (k : ℕ) → Finset (Partition (n+k))
def elementaryFunctionType := ℕ → StableSymmetricRing
def signLineType := (k : ℕ) → Representation ℂ (SymmetricGroup k) ℂ

def verticalPieriInputType := ∀ {n : ℕ} {lam : Partition n},
  Representation ℂ (SymmetricGroup n) (SpechtModule lam) → (k : ℕ) →
    Representation ℂ (SymmetricGroup n × SymmetricGroup k)
      (TensorProduct ℂ (SpechtModule lam) ℂ)
def verticalPieriSumType := ∀ {n : ℕ} (lam : Partition n) (k : ℕ),
  ((mu : Partition (n+k)) → Representation ℂ (SymmetricGroup (n+k)) (SpechtModule mu)) →
    Representation ℂ (SymmetricGroup (n+k))
      (⨁ mu : {mu : Partition (n+k) // VerticalStrip lam mu}, SpechtModule mu.val)

def verticalStrip_rowsType : Prop := ∀ {n m} (lam : Partition n) (mu : Partition m),
  VerticalStrip lam mu ↔
    ∀ i, rowLength lam i ≤ rowLength mu i ∧ rowLength mu i ≤ rowLength lam i + 1

def verticalStrip_cardType : Prop := ∀ {n k} (lam : Partition n) (mu : Partition (n+k)),
  VerticalStrip lam mu → (cells mu \ cells lam).card = k

def verticalStrip_zeroType : Prop := ∀ {n} (lam mu : Partition n),
  VerticalStrip lam mu ↔ lam = mu

def verticalStrip_emptyType : Prop := ∀ {k} (mu : Partition k),
  VerticalStrip emptyPartition mu ↔ mu = transpose (Nat.Partition.indiscrete k)

def elementaryFunction_specializationType : Prop := ∀ k r,
  stableSpecialization r (elementaryFunction k) = e r (k : ℤ)

def vertical_pieri_finiteType : Prop := ∀ {n} (lam : Partition n) (k r : ℕ),
  schurPolynomial lam r * e r (k : ℤ) =
    ∑ mu ∈ verticalExtensions lam k, schurPolynomial mu r

def vertical_pieri_stableType : Prop := ∀ {n} (lam : Partition n) (k : ℕ),
  schurFunction lam * elementaryFunction k =
    ∑ mu ∈ verticalExtensions lam k, schurFunction mu

def vertical_pieri_characterType : Prop := ∀ {n} (lam : Partition n) (k : ℕ)
    (rho : Representation ℂ (SymmetricGroup n) (SpechtModule lam))
    (sigma : (mu : Partition (n+k)) →
      Representation ℂ (SymmetricGroup (n+k)) (SpechtModule mu)),
  InheritedSpechtAction lam rho → (∀ mu, InheritedSpechtAction mu (sigma mu)) →
    inducedExternal (representationClassFunction rho) (representationClassFunction (signLine k)) =
      ∑ mu ∈ verticalExtensions lam k, representationClassFunction (sigma mu)

def vertical_pieri_moduleType : Prop := ∀ {n} (lam : Partition n) (k : ℕ)
    (rho : Representation ℂ (SymmetricGroup n) (SpechtModule lam))
    (sigma : (mu : Partition (n+k)) →
      Representation ℂ (SymmetricGroup (n+k)) (SpechtModule mu)),
  InheritedSpechtAction lam rho → (∀ mu, InheritedSpechtAction mu (sigma mu)) →
    Nonempty ((Representation.ind (A := TensorProduct ℂ (SpechtModule lam) ℂ)
      (blockEmbedding n k) (verticalPieriInput rho k)).Equiv
      (verticalPieriSum lam k sigma))

end Specs.AdvancedFiniteGroupRepresentations
