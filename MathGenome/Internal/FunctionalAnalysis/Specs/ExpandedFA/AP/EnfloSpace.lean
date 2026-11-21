import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.AP.BalancedIncidenceSets
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.BanachSums
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01ExamplesComplete
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Independent construction for paper.tex:12789–12825.
Natural block index `m` denotes the source's positive index `m+1`. The compact
space is literally the finite disjoint union of the indicated cubes, with the
discrete topology. The summands are continuous real functions with their sup
norm, and `Y` is exactly the canonical general Banach sum at exponent two.
No inner product on the summands is used or postulated. Reflexivity and the
coordinate-functionals argument belong to the separately allocated goals. -/

noncomputable section
open scoped ENNReal BigOperators

namespace ExpandedFA.AP.EnfloSpace.Spec
open ExpandedFA.AP

/-- Precisely the simultaneous data supplied by the balanced incidence theorem.
The natural indices in these fields retain that theorem's convention. -/
structure IncidenceData where
  offset : ℕ
  sets : ∀ m, Fin (Incidence.rowCount offset (m + 1)) →
    Finset (Incidence.Symbol offset m)
  dimension_ge_two : ∀ m, 1 ≤ m → 2 ≤ Incidence.dimension offset m
  properties : ∀ m, 1 ≤ m → Incidence.FamilyProperties
    (Incidence.rowCount offset m) (Incidence.levelSize offset m)
    (Incidence.levelSize offset (m + 1)) (Incidence.rowCount offset (m + 1))
    (Incidence.dimension offset (m + 1)) (sets m)
  reciprocal_summable : Summable (fun m : ℕ =>
    1 / (Incidence.dimension offset (m + 1) : ℝ))

abbrev n (D : IncidenceData) (m : ℕ) := Incidence.dimension D.offset (m + 1)
abbrev t (D : IncidenceData) (m : ℕ) := Incidence.levelSize D.offset (m + 1)
abbrev k (D : IncidenceData) (m : ℕ) := Incidence.rowCount D.offset (m + 1)
abbrev Row (D : IncidenceData) (m : ℕ) := Fin (k D m)
abbrev Symbol (D : IncidenceData) (m : ℕ) := Incidence.Symbol D.offset (m + 1)

/-- Next-block row `j` is incident with precisely this set of current symbols. -/
def incident (D : IncidenceData) (m : ℕ) (j : Row D (m + 1)) :
    Finset (Symbol D m) := D.sets (m + 1) j

/-- A tagged disjoint union of `k_m` copies of the finite cube. -/
def K (D : IncidenceData) (m : ℕ) := Row D m × Walsh.Cube (n D m)

instance (D : IncidenceData) (m : ℕ) : Fintype (K D m) :=
  inferInstanceAs (Fintype (Row D m × Walsh.Cube (n D m)))
instance (D : IncidenceData) (m : ℕ) : TopologicalSpace (K D m) := ⊥
instance (D : IncidenceData) (m : ℕ) : DiscreteTopology (K D m) := ⟨rfl⟩

abbrev Summand (D : IncidenceData) (m : ℕ) := C(K D m, ℝ)

abbrev Y (D : IncidenceData) :=
  ExpandedFA.Supplements.BanachSumDefinitions.Spec.Space (Summand D) 2

/-- The elementary cardinal identity only constructs a labelling; it is not
an assumed orthogonality or norm statement. -/
private theorem upper_card (D : IncidenceData) (m : ℕ) :
    (Walsh.level (n D m) (n D m + 1)).card = t D m := by
  simp only [Walsh.level, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  change (2 * n D m).choose (n D m + 1) = (2 * n D m).choose (n D m - 1)
  have hn : 2 ≤ n D m := D.dimension_ge_two (m + 1) (by omega)
  exact Nat.choose_symm_of_eq_add (by omega)

/-- Each position in a current row gets a distinct upper-level character. -/
def upperLabels (D : IncidenceData) (m : ℕ) :
    Fin (t D m) ≃ ↥(Walsh.level (n D m) (n D m + 1)) :=
  Fintype.equivOfCardEq (by simpa only [Fintype.card_fin, Fintype.card_coe] using
    (upper_card D m).symm)

/-- Every next-block row gets its own bijection from the incident set to
its lower Walsh level, as permitted by the source. -/
def lowerLabels (D : IncidenceData) (m : ℕ) (j : Row D (m + 1)) :
    ↥(incident D m j) ≃ ↥(Walsh.level (n D (m + 1)) (n D (m + 1) - 1)) :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_coe (incident D m j),
      Fintype.card_coe (Walsh.level (n D (m + 1)) (n D (m + 1) - 1))]
    calc
      (incident D m j).card = t D (m + 1) := (D.properties (m + 1) (by omega)).1 j
      _ = (Walsh.level (n D (m + 1)) (n D (m + 1) - 1)).card := by
        simp only [Walsh.level, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
        rfl)

/-- The generator's own block; it vanishes off its own row. -/
def ownBlock (D : IncidenceData) (m : ℕ) (e : Symbol D m) : Summand D m :=
  ⟨fun p => if p.1 = e.1 then
    Walsh.character (n D m) (upperLabels D m e.2).val p.2 else 0,
    continuous_of_discreteTopology⟩

/-- The next block, with the independently assigned lower character in
every incident row and zero in every nonincident row. -/
def nextBlock (D : IncidenceData) (m : ℕ) (e : Symbol D m) : Summand D (m + 1) :=
  ⟨fun p => if h : e ∈ incident D m p.1 then
    Walsh.character (n D (m + 1)) (lowerLabels D m p.1 ⟨e, h⟩).val p.2 else 0,
    continuous_of_discreteTopology⟩

/-- Two coordinate inclusions in the canonical Banach sum give an actual
square-summable vector, without needing any estimate on its sup norms. -/
def generator (D : IncidenceData) (m : ℕ) (e : Symbol D m) : Y D :=
  lp.single 2 m (ownBlock D m e) + lp.single 2 (m + 1) (nextBlock D m e)

abbrev AllSymbols (D : IncidenceData) := Σ m : ℕ, Symbol D m

def generators (D : IncidenceData) : Set (Y D) :=
  Set.range (fun e : AllSymbols D => generator D e.1 e.2)

/-- The source's closed real linear span in the stated ambient norm. -/
def closedSpan (D : IncidenceData) : Submodule ℝ (Y D) :=
  (Submodule.span ℝ (generators D)).topologicalClosure

abbrev X (D : IncidenceData) : Type := closedSpan D

def generatorX (D : IncidenceData) (m : ℕ) (e : Symbol D m) : X D :=
  ⟨generator D m e,
    (Submodule.span ℝ (generators D)).le_topologicalClosure
      (Submodule.subset_span ⟨⟨m, e⟩, rfl⟩)⟩

/-! Definition contracts. Canonical objects above are shared with later goals;
implementation names are aliases with these exact values. -/
def IncidenceDataType := Type
def IncidenceDataValue : IncidenceDataType := IncidenceData

def nType := IncidenceData → ℕ → ℕ
def tType := IncidenceData → ℕ → ℕ
def kType := IncidenceData → ℕ → ℕ
def RowType := IncidenceData → ℕ → Type
def SymbolType := IncidenceData → ℕ → Type
def AllSymbolsType := IncidenceData → Type

def incidentType := ∀ D m, Row D (m + 1) → Finset (Symbol D m)
def KType := IncidenceData → ℕ → Type
def SummandType := IncidenceData → ℕ → Type
def YType := IncidenceData → Type
def upperLabelsType := ∀ D m,
  Fin (t D m) ≃ ↥(Walsh.level (n D m) (n D m + 1))
def lowerLabelsType := ∀ D m (j : Row D (m + 1)),
  ↥(incident D m j) ≃ ↥(Walsh.level (n D (m + 1)) (n D (m + 1) - 1))
def ownBlockType := ∀ D m, Symbol D m → Summand D m
def nextBlockType := ∀ D m, Symbol D m → Summand D (m + 1)
def generatorType := ∀ D m, Symbol D m → Y D
def generatorsType := ∀ D, Set (Y D)
def closedSpanType := ∀ D, Submodule ℝ (Y D)
def XType := IncidenceData → Type
def generatorXType := ∀ D m, Symbol D m → X D

/-! Full proposition types: no certificates are assumed. -/
def DataExists : Prop := Nonempty IncidenceData

def SummandFiniteDimensional : Prop := ∀ D m, FiniteDimensional ℝ (Summand D m)
def SummandComplete : Prop := ∀ D m, CompleteSpace (Summand D m)
def SummandSupNorm : Prop := ∀ D m (f : Summand D m), ‖f‖ = ⨆ p : K D m, |f p|

def AmbientComplete : Prop := ∀ D, CompleteSpace (Y D)
def AmbientSquareNorm : Prop := ∀ D (y : Y D),
  ‖y‖ ^ 2 = ⨆ A : Finset ℕ, ∑ i ∈ A, ‖y i‖ ^ 2

def GeneratorOwn : Prop := ∀ D m (e : Symbol D m) (r : Row D m) (a : Walsh.Cube (n D m)),
  generator D m e m (r, a) =
    if r = e.1 then Walsh.character (n D m) (upperLabels D m e.2).val a else 0

def GeneratorNext : Prop := ∀ D m (e : Symbol D m) (r : Row D (m + 1))
    (a : Walsh.Cube (n D (m + 1))),
  generator D m e (m + 1) (r, a) =
    if h : e ∈ incident D m r then
      Walsh.character (n D (m + 1)) (lowerLabels D m r ⟨e, h⟩).val a else 0

def GeneratorOther : Prop := ∀ D m (e : Symbol D m) j,
  j ≠ m → j ≠ m + 1 → generator D m e j = 0

def GeneratorsCountable : Prop := ∀ D, (generators D).Countable

def ClosedSpanClosed : Prop := ∀ D, IsClosed (closedSpan D : Set (Y D))
def XComplete : Prop := ∀ D, CompleteSpace (X D)
def XBanach : Prop := ∀ D, ExpandedFA.P1.C01Banach.Spec.IsBanachSpaceValue (X D)
def XSeparable : Prop := ∀ D, TopologicalSpace.SeparableSpace (X D)

/-- The construction is nonvacuous, with exactly the preceding definitions. -/
def SpaceExists : Prop := ∃ D : IncidenceData,
  CompleteSpace (Y D) ∧ CompleteSpace (X D) ∧ TopologicalSpace.SeparableSpace (X D)

end ExpandedFA.AP.EnfloSpace.Spec
