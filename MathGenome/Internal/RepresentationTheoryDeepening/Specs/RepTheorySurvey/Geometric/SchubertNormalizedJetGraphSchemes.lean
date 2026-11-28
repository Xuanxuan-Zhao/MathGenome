import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.LatticeModels
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

namespace RepTheorySurvey.Geometric.SchubertNormalizedJetGraphSpecs

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open LinearAlgebraicGroups (Points SchemeOver testSpec)
open LinearAlgebraicGroups.Specs.GrassmannianCharts
open LatticeModelSpecs
open scoped Matrix

noncomputable section

/-- The ordinary Grassmannian containing the reduced minimal stability scheme. -/
abbrev WindowGrassmannian {b : ℤ} {m : ℕ} (d : WindowDimension 2 b m) : SchemeOver ℂ :=
  (grassmannianCharts (windowBasis 2 b m) (windowDimension_le d)).scheme

def stableInclusion {b : ℤ} {m : ℕ} (d : WindowDimension 2 b m) :
    windowStableScheme 2 b m d ⟶ WindowGrassmannian d :=
  reducedClosureInclusion _ {p | StablePlane (windowBasis 2 b m)
    (windowDimension_le d) (windowOperator 2 b m) p}

/-- A row normalized at `i` gives a graph over the other jet coordinate. -/
def jetPivot {b : ℤ} {m : ℕ} {d : WindowDimension 2 b m}
    (hd : d.val = m) (i : Fin 2) : Pivot (Fin 2 × Fin m) d.val :=
  ⟨Finset.univ.map ⟨fun k : Fin m ↦ (i.rev, k), fun _ _ h ↦ congrArg Prod.snd h⟩, by
    simp [hd]⟩

def jetPivotChart {b : ℤ} {m : ℕ} {d : WindowDimension 2 b m}
    (hd : d.val = m) (i : Fin 2) :
    chartScheme (k := ℂ) (jetPivot hd i) ⟶ WindowGrassmannian d :=
  (grassmannianCharts (windowBasis 2 b m) (windowDimension_le d)).chart (jetPivot hd i)

def stablePivotOpen {b : ℤ} {m : ℕ} {d : WindowDimension 2 b m}
    (hd : d.val = m) (i : Fin 2) : (windowStableScheme 2 b m d).left.Opens := by
  letI : IsOpenImmersion (jetPivotChart hd i).left :=
    (grassmannianCharts (windowBasis 2 b m) (windowDimension_le d)).openChart (jetPivot hd i)
  exact (stableInclusion d).left ⁻¹ᵁ (jetPivotChart hd i).left.opensRange

def normalizedJetOpen {b : ℤ} {m : ℕ} {d : WindowDimension 2 b m}
    (hd : d.val = m) : (windowStableScheme 2 b m d).left.Opens :=
  stablePivotOpen hd 0 ⊔ stablePivotOpen hd 1

def normalizedJetScheme {b : ℤ} {m : ℕ} {d : WindowDimension 2 b m}
    (hd : d.val = m) : SchemeOver ℂ :=
  Over.mk ((normalizedJetOpen hd).ι ≫ (windowStableScheme 2 b m d).hom)

def normalizedJetInclusion {b : ℤ} {m : ℕ} {d : WindowDimension 2 b m}
    (hd : d.val = m) : normalizedJetScheme hd ⟶ windowStableScheme 2 b m d :=
  Over.homMk (normalizedJetOpen hd).ι rfl

abbrev NormalizedJetPoints {b : ℤ} {m : ℕ} {d : WindowDimension 2 b m}
    (hd : d.val = m) := Points (normalizedJetScheme hd) complexAlgebra

instance normalizedJetTopology {b : ℤ} {m : ℕ} {d : WindowDimension 2 b m}
    (hd : d.val = m) : TopologicalSpace (NormalizedJetPoints hd) :=
  TopologicalSpace.induced
    (fun p : NormalizedJetPoints hd ↦ p ≫ normalizedJetInclusion hd ≫ stableInclusion d)
    (grassmannianAnalyticTopology (windowBasis 2 b m) (windowDimension_le d))

def normalizedJetSubspace {b : ℤ} {m : ℕ} {d : WindowDimension 2 b m} {hd : d.val = m}
    (p : NormalizedJetPoints hd) : Submodule ℂ (Window 2 b m) :=
  grassmannianSubspace (windowBasis 2 b m) (windowDimension_le d)
    (p ≫ normalizedJetInclusion hd ≫ stableInclusion d)

abbrev AffineCoordinateRing (n : ℕ) := MvPolynomial (Fin n) ℂ

abbrev Affine (n : ℕ) : SchemeOver ℂ :=
  (testSpec ℂ).obj (op (CommAlgCat.of ℂ (AffineCoordinateRing n)))

def affinePoint {n : ℕ} (z : Fin n → ℂ) : Points (Affine n) complexAlgebra :=
  (testSpec ℂ).map (CommAlgCat.ofHom (MvPolynomial.aeval z)).op

def affineHead {m : ℕ} (hm : 0 < m) : Affine m ⟶ Affine 1 :=
  (testSpec ℂ).map (CommAlgCat.ofHom (MvPolynomial.aeval (R := ℂ)
    (fun _ : Fin 1 ↦ (MvPolynomial.X ⟨0, hm⟩ : AffineCoordinateRing m)))).op

/-- The nonpivot block of the universal graph, given by multiplication by `-z`.
The other block is the identity, as in `LatticeModelSpecs.graphMatrix`. -/
def polynomialGraph {b : ℤ} {m : ℕ} {d : WindowDimension 2 b m}
    (hd : d.val = m) (i : Fin 2) :
    Matrix (Outside (jetPivot hd i)) (Inside (jetPivot hd i)) (AffineCoordinateRing m) :=
  Matrix.of fun r c ↦
    if c.val.2.val ≤ r.val.2.val then
      -MvPolynomial.X ⟨r.val.2.val - c.val.2.val, by
        exact lt_of_le_of_lt (Nat.sub_le _ _) r.val.2.isLt⟩
    else 0

def polynomialGraphMap {b : ℤ} {m : ℕ} {d : WindowDimension 2 b m}
    (hd : d.val = m) (i : Fin 2) : Affine m ⟶ chartScheme (k := ℂ) (jetPivot hd i) :=
  (testSpec ℂ).map (CommAlgCat.ofHom
    (MvPolynomial.aeval (R := ℂ) (fun rc ↦ polynomialGraph hd i rc.1 rc.2))).op

private theorem other_ne (i : Fin 2) : i.rev ≠ i := by
  fin_cases i <;> decide

/-- Recover the normalized row from the negated zeroth column of its graph. -/
def zerothColumnCoefficients {b : ℤ} {m : ℕ} {d : WindowDimension 2 b m}
    (hd : d.val = m) (hm : 0 < m) (i : Fin 2)
    (A : Matrix (Outside (jetPivot hd i)) (Inside (jetPivot hd i)) ℂ) : Fin m → ℂ :=
  fun k ↦ -A
    ⟨(i, k), by
      intro h
      obtain ⟨_, _, h⟩ := Finset.mem_map.mp h
      exact other_ne i (congrArg Prod.fst h)⟩
    ⟨(i.rev, ⟨0, hm⟩), Finset.mem_map.mpr ⟨⟨0, hm⟩, Finset.mem_univ _, rfl⟩⟩

theorem projectiveLineDimension : 1 ≤ Module.finrank ℂ (Fin 2 → ℂ) := by simp

abbrev ProjectiveLine : SchemeOver ℂ :=
  (grassmannianCharts (Pi.basisFun ℂ (Fin 2)) projectiveLineDimension).scheme

def linePivot (i : Fin 2) : Pivot (Fin 2) 1 := ⟨{i}, by simp⟩

/-- The open chart of lines with normalized `i`-th coordinate. -/
def lineChart (i : Fin 2) : Affine 1 ⟶ ProjectiveLine :=
  (testSpec ℂ).map (CommAlgCat.ofHom (MvPolynomial.aeval (R := ℂ)
    (fun _ : Outside (linePivot i) × Inside (linePivot i) ↦
      (MvPolynomial.X 0 : AffineCoordinateRing 1)))).op ≫
    (grassmannianCharts (Pi.basisFun ℂ (Fin 2)) projectiveLineDimension).chart (linePivot i)

def normalizedLine (i : Fin 2) (x : ℂ) : Submodule ℂ (Fin 2 → ℂ) :=
  Submodule.span ℂ {fun j : Fin 2 ↦ if j = i then 1 else x}

def headVariable {m : ℕ} (hm : 0 < m) : AffineCoordinateRing m :=
  MvPolynomial.X ⟨0, hm⟩

abbrev OverlapRing {m : ℕ} (hm : 0 < m) := Localization.Away (headVariable hm)

abbrev Overlap {m : ℕ} (hm : 0 < m) : SchemeOver ℂ :=
  (testSpec ℂ).obj (op (CommAlgCat.of ℂ (OverlapRing hm)))

def overlapInclusion {m : ℕ} (hm : 0 < m) : Overlap hm ⟶ Affine m :=
  (testSpec ℂ).map (CommAlgCat.ofHom
    (IsScalarTower.toAlgHom ℂ (AffineCoordinateRing m) (OverlapRing hm))).op

/-- The reciprocal of the universal truncated series on the principal open
of its constant coefficient, represented by a finite geometric sum. -/
def inverseJetPolynomial {m : ℕ} (hm : 0 < m) : Polynomial (OverlapRing hm) :=
  let u : OverlapRing hm := IsLocalization.Away.invSelf (headVariable hm)
  let p := ∑ k ∈ (Finset.univ : Finset (Fin m)).filter (fun k ↦ k.val ≠ 0),
    Polynomial.monomial k.val (algebraMap (AffineCoordinateRing m) (OverlapRing hm)
      (MvPolynomial.X k))
  Polynomial.C u * ∑ k ∈ Finset.range m, (-(Polynomial.C u * p)) ^ k

def overlapInversion {m : ℕ} (hm : 0 < m) : Overlap hm ⟶ Affine m :=
  (testSpec ℂ).map (CommAlgCat.ofHom (MvPolynomial.aeval (R := ℂ)
    (fun k : Fin m ↦ (inverseJetPolynomial hm).coeff k.val))).op

/-- Algebraic and analytic chart data on the actual open of the reduced stability scheme. -/
structure NormalizedJetGraphCharts {b : ℤ} {m : ℕ} {d : WindowDimension 2 b m}
    (hd : d.val = m) (hm : 0 < m) where
  chart : Fin 2 → (Affine m ⟶ normalizedJetScheme hd)
  projection : normalizedJetScheme hd ⟶ ProjectiveLine
  chart_open : ∀ i, IsOpenImmersion (chart i).left
  chart_range : ∀ i,
    Set.range ((chart i ≫ normalizedJetInclusion hd).left) = (stablePivotOpen hd i : Set _)
  chart_cover : ∀ p : (normalizedJetScheme hd).left, ∃ i, p ∈ Set.range (chart i).left
  polynomial_graph : ∀ i,
    chart i ≫ normalizedJetInclusion hd ≫ stableInclusion d =
      polynomialGraphMap hd i ≫ jetPivotChart hd i
  kernel : ∀ i (z : Fin m → ℂ) (x : Window 2 b m),
    x ∈ normalizedJetSubspace (affinePoint z ≫ chart i) ↔
      windowJets 2 b m x i +
        (jetCoefficients m).symm z * windowJets 2 b m x i.rev = 0
  line_chart_open : ∀ i, IsOpenImmersion (lineChart i).left
  line_chart_cover : ∀ p : ProjectiveLine.left, ∃ i, p ∈ Set.range (lineChart i).left
  line_chart_point : ∀ i (x : Fin 1 → ℂ),
    grassmannianSubspace (Pi.basisFun ℂ (Fin 2)) projectiveLineDimension
      (affinePoint x ≫ lineChart i) = normalizedLine i (x 0)
  projection_pullback : ∀ i, IsPullback (chart i) (affineHead hm) projection (lineChart i)
  inversion_pullback : ∀ i, IsPullback (overlapInclusion hm) (overlapInversion hm)
    (chart i) (chart i.rev)
  inversion_on_points : ∀ i (z w : Fin m → ℂ),
    affinePoint z ≫ chart i = affinePoint w ≫ chart i.rev ↔
      ∃ v : (JetRing m)ˣ, (jetCoefficients m).symm z = v.val ∧
        (jetCoefficients m).symm w = (v⁻¹).val
  smooth : SmoothOfRelativeDimension m (normalizedJetScheme hd).hom
  analytic_open : ∀ i, Topology.IsOpenEmbedding
    (fun z : Fin m → ℂ ↦ (affinePoint z ≫ chart i : NormalizedJetPoints hd))
  recover_coefficients : ∀ i (z : Fin m → ℂ),
    zerothColumnCoefficients hd hm i ((polynomialGraph hd i).map (MvPolynomial.aeval z)) = z

def NormalizedJetGraphSchemeCharts : Prop :=
  ∀ (b : ℤ) (m : ℕ) (d : WindowDimension 2 b m) (hd : d.val = m) (hm : 0 < m),
    Nonempty (NormalizedJetGraphCharts hd hm)

end

end RepTheorySurvey.Geometric.SchubertNormalizedJetGraphSpecs
