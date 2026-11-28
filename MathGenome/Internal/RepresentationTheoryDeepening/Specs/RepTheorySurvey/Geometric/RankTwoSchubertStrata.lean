import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.BoundedLattices
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SchubertAnalyticFlagTransport
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SchubertNormalizedJetGraphSchemes

namespace RepTheorySurvey.Geometric.RankTwoSchubertStrataSpecs

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LinearAlgebraicGroups (Points SchemeOver testSpec)
open LinearAlgebraicGroups.Specs.GrassmannianCharts
open LatticeModelSpecs BoundedLatticeSpecs
open scoped Matrix MatrixGroups Matrix.Norms.Elementwise

noncomputable section

/-- The lower and upper scalar lattices for the rank-two interval `[b,a]`. -/
def Between (a b : ℤ) (L : GL2Lattice) : Prop :=
  (scalarLattice 2 a).val ≤ L.val ∧ L.val ≤ (scalarLattice 2 b).val

def difference (ab : DominantPair) : ℕ := (ab.val.1 - ab.val.2).toNat

def Occupied (ab : DominantPair) (N : ℕ) (d : WindowDimension 2 (-(N : ℤ)) (2 * N)) :
    Prop :=
  (d.val : ℤ) = 2 * (N : ℤ) - (ab.val.1 + ab.val.2)

def diagonalBounded (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) :
    BoundedLattice 2 N :=
  ⟨diagonalLattice (pairCoweight ab),
    gl2Orbit_bounded ab hN (MulAction.mem_orbit_self _)⟩

/-- The dimension index of the orbit in the symmetric window. -/
def occupiedDimension (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) :
    WindowDimension 2 (-(N : ℤ)) (2 * N) := by
  refine ⟨(2 * (N : ℤ) - (ab.val.1 + ab.val.2)).toNat, ?_⟩
  have ha₀ : -(N : ℤ) ≤ ab.val.1 := by simpa [pairCoweight] using (hN 0).1
  have hb₀ : -(N : ℤ) ≤ ab.val.2 := by simpa [pairCoweight] using (hN 1).1
  change _ < Module.finrank ℂ (BoundedWindow 2 N) + 1
  rw [Module.finrank_eq_card_basis (windowBasis 2 (-(N : ℤ)) (2 * N)),
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  omega

theorem occupiedDimension_occupied (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) :
    Occupied ab N (occupiedDimension ab N hN) := by
  have ha : ab.val.1 ≤ (N : ℤ) := by simpa [pairCoweight] using (hN 0).2
  have hb : ab.val.2 ≤ (N : ℤ) := by simpa [pairCoweight] using (hN 1).2
  change ((2 * (N : ℤ) - (ab.val.1 + ab.val.2)).toNat : ℤ) = _
  exact Int.toNat_of_nonneg (by omega)

/-- The set of orbit labels in the dominance interval of `(a,b)`. -/
def Below (cd ab : DominantPair) : Prop :=
  ∃ j : ℕ, 2 * (j : ℤ) ≤ ab.val.1 - ab.val.2 ∧
    cd.val.1 = ab.val.1 - (j : ℤ) ∧ cd.val.2 = ab.val.2 + (j : ℤ)

/-- Lattice description of the set underlying a reduced Schubert closure. -/
def closureLattices (ab : DominantPair) : Set GL2Lattice :=
  {L | ∃ cd : DominantPair, Below cd ab ∧ L ∈ gl2Orbit cd}

def SmithClassification : Prop :=
  (∀ L : GL2Lattice, ∃! ab : DominantPair, L ∈ gl2Orbit ab) ∧
  ∀ (ab : DominantPair) (L : GL2Lattice), L ∈ gl2Orbit ab →
    (∀ c : ℤ, (scalarLattice 2 c).val ≤ L.val ↔ ab.val.1 ≤ c) ∧
    (∀ c : ℤ, L.val ≤ (scalarLattice 2 c).val ↔ c ≤ ab.val.2) ∧
    ∀ (c : ℤ) (m : ℕ), c ≤ ab.val.2 → ab.val.1 ≤ c + (m : ℤ) →
      (Module.finrank ℂ (latticeSubspace c m L) : ℤ) =
        2 * (c + (m : ℤ)) - (ab.val.1 + ab.val.2)

abbrev occupiedSchubert (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) :=
  schubertScheme ab N hN (occupiedDimension ab N hN)

abbrev BoundedGrassmannian := SchubertAnalyticFlagTransportSpecs.BoundedGrassmannian

def schubertToGrassmannian (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (d : WindowDimension 2 (-(N : ℤ)) (2 * N)) :
    schubertScheme ab N hN d ⟶ BoundedGrassmannian N d :=
  reducedClosureInclusion _ (schubertOrbitPoints ab N hN d)

def schubertLatticeSet (ab : DominantPair) (N : ℕ) : Set (BoundedLattice 2 N) :=
  {L | L.val ∈ closureLattices ab}

def boundedOrbit (ab : DominantPair) (N : ℕ) : Set (BoundedLattice 2 N) :=
  {L | L.val ∈ gl2Orbit ab}

def BoundedSchubertComparison : Prop :=
  ∀ (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N),
    Occupied ab N (occupiedDimension ab N hN) ∧
    (∀ d, (schubertOrbitPoints ab N hN d).Nonempty ↔ Occupied ab N d) ∧
    (∀ L : GL2Lattice, L ∈ closureLattices ab →
      ∃ B : BoundedLattice 2 N, B.val = L) ∧
    (∀ L : BoundedLattice 2 N,
      L ∈ schubertLatticeSet ab N ↔
        Between ab.val.1 ab.val.2 L.val ∧ Occupied ab N (boundedPoint L).1) ∧
    IsClosed {L : BoundedLattice 2 N | Between ab.val.1 ab.val.2 L.val} ∧
    closure (boundedOrbit ab N) = schubertLatticeSet ab N ∧
    ∀ (d : WindowDimension 2 (-(N : ℤ)) (2 * N)) (p : WindowPoints 2 (-(N : ℤ)) (2 * N) d),
      pointLocation p ∈ closure (pointLocation '' schubertOrbitPoints ab N hN d) ↔
        ∃ L ∈ schubertLatticeSet ab N,
          grassmannianSubspace (windowBasis 2 (-(N : ℤ)) (2 * N)) (windowDimension_le d) p =
            boundedSubspace L

/-- Comparison with the reduced stability scheme in the smallest scalar interval.
The dimension equation is the occupation condition in that interval. -/
def MinimalWindowComparison : Prop :=
  ∀ (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N),
    ∃ d : WindowDimension 2 ab.val.2 (difference ab), d.val = difference ab ∧
      ∃ e : windowStableScheme 2 ab.val.2 (difference ab) d ≅ occupiedSchubert ab N hN,
        ∀ (L : WindowLattice 2 ab.val.2 (difference ab))
          (q : Points (windowStableScheme 2 ab.val.2 (difference ab) d) complexAlgebra),
          windowSchemeSubspace q = latticeSubspace ab.val.2 (difference ab) L.val →
          grassmannianSubspace (windowBasis 2 (-(N : ℤ)) (2 * N))
            (windowDimension_le (occupiedDimension ab N hN))
            (q ≫ e.hom ≫ schubertToGrassmannian ab N hN (occupiedDimension ab N hN)) =
              latticeSubspace (-(N : ℤ)) (2 * N) L.val

def BoundedSchubertInvariance : Prop :=
  ∀ (ab : DominantPair) (N M : ℕ) (hN : OrbitBound ab N) (hM : OrbitBound ab M)
    (hNM : N ≤ M),
    (∃ e : schubertLatticeSet ab N ≃ₜ schubertLatticeSet ab M,
      ∀ L, (e L).val = boundedInclusion hNM L.val) ∧
    ∃ (e : occupiedSchubert ab N hN ≅ occupiedSchubert ab M hM)
      (j : windowStableScheme 2 (-(N : ℤ)) (2 * N) (occupiedDimension ab N hN) ⟶
        windowStableScheme 2 (-(M : ℤ)) (2 * M) (occupiedDimension ab M hM))
      (iN : occupiedSchubert ab N hN ⟶
        windowStableScheme 2 (-(N : ℤ)) (2 * N) (occupiedDimension ab N hN))
      (iM : occupiedSchubert ab M hM ⟶
        windowStableScheme 2 (-(M : ℤ)) (2 * M) (occupiedDimension ab M hM)),
      IsClosedImmersion j.left ∧ IsClosedImmersion iN.left ∧ IsClosedImmersion iM.left ∧
      iN ≫ windowSchemeInGrassmannian 2 (-(N : ℤ)) (2 * N) _ =
        schubertToGrassmannian ab N hN _ ∧
      iM ≫ windowSchemeInGrassmannian 2 (-(M : ℤ)) (2 * M) _ =
        schubertToGrassmannian ab M hM _ ∧
      e.hom ≫ iM = iN ≫ j ∧
      ∀ (L : BoundedLattice 2 N)
        (q : Points (windowStableScheme 2 (-(N : ℤ)) (2 * N) (occupiedDimension ab N hN))
          complexAlgebra),
        windowSchemeSubspace q = boundedSubspace L →
        windowSchemeSubspace (q ≫ j) = boundedSubspace (boundedInclusion hNM L)

def adjacentPair (ab : DominantPair) (h : 2 ≤ difference ab) : DominantPair :=
  ⟨(ab.val.1 - 1, ab.val.2 + 1), by
    have hs := ab.property
    change ab.val.2 ≤ ab.val.1 at hs
    dsimp [difference] at h
    dsimp
    omega⟩

def adjacentColumn (ab : DominantPair) (s : ℂ) : Fin 2 → Coordinates 2 :=
  ![![monomial (ab.val.1 - 1), s • monomial ab.val.2],
    ![0, monomial (ab.val.2 + 1)]]

/-- A single ordinary Grassmannian graph chart with polynomial entries contains the
adjacent specialization, including its value at zero. -/
def AdjacentSpecialization : Prop :=
  ∀ (ab : DominantPair) (h : 2 ≤ difference ab) (N : ℕ) (hN : OrbitBound ab N),
    let d := occupiedDimension ab N hN
    let b := windowBasis 2 (-(N : ℤ)) (2 * N)
    ∃ (I : Pivot (Fin 2 × Fin (2 * N)) d.val)
      (A : Matrix (Outside I) (Inside I) (Polynomial ℂ)) (L : ℂ → BoundedLattice 2 N),
      (∀ s, (L s).val.val = Submodule.span O (Set.range (adjacentColumn ab s))) ∧
      (∀ s, grassmannianSubspace b (windowDimension_le d)
          (grassmannianChartPoint b (windowDimension_le d) I (A.map (Polynomial.eval s))) =
        boundedSubspace (L s)) ∧
      (∀ s, s ≠ 0 → (L s).val ∈ gl2Orbit ab) ∧
      (L 0).val = diagonalLattice (pairCoweight (adjacentPair ab h))

abbrev Row (m : ℕ) := Fin 2 → JetRing m

def IsPrimitive {m : ℕ} (row : Row m) : Prop := ∃ i, IsUnit (row i)

abbrev PrimitiveRow (m : ℕ) := {row : Row m // IsPrimitive row}

def primitiveRowRel (m : ℕ) : Setoid (PrimitiveRow m) where
  r v w := ∃ u : (JetRing m)ˣ, ∀ i, w.val i = u.val * v.val i
  iseqv := by
    constructor
    · intro v
      exact ⟨1, fun i ↦ by simp⟩
    · rintro v w ⟨u, hu⟩
      exact ⟨u⁻¹, fun i ↦ by simp [hu i, ← mul_assoc]⟩
    · rintro v w x ⟨u, hu⟩ ⟨v', hv⟩
      exact ⟨v' * u, fun i ↦ by simp [hu i, hv i, mul_assoc]⟩

def rowMap {m : ℕ} (row : Row m) : (Fin 2 → O) →ₗ[O] JetRing m :=
  ∑ i : Fin 2, row i •
    ((Ideal.Quotient.mkₐ O (jetIdeal m)).toLinearMap.comp (LinearMap.proj i))

/-- The kernel transported from the normalized lattice `O²` to `t^b O²`. -/
def shiftedKernel {m : ℕ} (b : ℤ) (row : Row m) : Submodule O (Coordinates 2) :=
  (rowMap row).ker.map (shiftedInclusion 2 b)

def PrimitiveRowClassification : Prop :=
  ∀ (ab : DominantPair), 0 < difference ab →
    (∀ v : PrimitiveRow (difference ab), Function.Surjective (rowMap v.val)) ∧
    ∃ e : Quotient (primitiveRowRel (difference ab)) ≃ gl2Orbit ab,
      ∀ v : PrimitiveRow (difference ab),
        (e (Quotient.mk _ v)).val.val = shiftedKernel ab.val.2 v.val

/-- The orbit open is the complement of the next Schubert closure, when there is one. -/
def orbitOpen (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) :
    (occupiedSchubert ab N hN).left.Opens := by
  classical
  let d := occupiedDimension ab N hN
  let X := (occupiedSchubert ab N hN).left
  by_cases h : 2 ≤ difference ab
  · have hN' : OrbitBound (adjacentPair ab h) N := by
      have h0 := hN (0 : Fin 2)
      have h1 := hN (1 : Fin 2)
      simp [pairCoweight] at h0 h1
      have hab := ab.property
      change ab.val.2 ≤ ab.val.1 at hab
      dsimp [difference] at h
      intro i
      fin_cases i <;> simp [pairCoweight, adjacentPair] <;> omega
    let Z : Set (BoundedGrassmannian N d).left :=
      closure (pointLocation '' schubertOrbitPoints (adjacentPair ab h) N hN' d)
    exact ⟨(schubertToGrassmannian ab N hN d).left ⁻¹' Zᶜ,
      isClosed_closure.isOpen_compl.preimage (schubertToGrassmannian ab N hN d).left.continuous⟩
  · exact ⊤

def orbitScheme (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) : SchemeOver ℂ :=
  Over.mk ((orbitOpen ab N hN).ι ≫ (occupiedSchubert ab N hN).hom)

def orbitToSchubert (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) :
    orbitScheme ab N hN ⟶ occupiedSchubert ab N hN :=
  Over.homMk (orbitOpen ab N hN).ι rfl

def orbitToGrassmannian (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) :
    orbitScheme ab N hN ⟶ BoundedGrassmannian N (occupiedDimension ab N hN) :=
  orbitToSchubert ab N hN ≫ schubertToGrassmannian ab N hN _

abbrev OrbitPoints (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) :=
  Points (orbitScheme ab N hN) complexAlgebra

def orbitPointSubspace {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    (p : OrbitPoints ab N hN) : Submodule ℂ (BoundedWindow 2 N) :=
  grassmannianSubspace (windowBasis 2 (-(N : ℤ)) (2 * N))
    (windowDimension_le (occupiedDimension ab N hN)) (p ≫ orbitToGrassmannian ab N hN)

instance orbitPointsTopology (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) :
    TopologicalSpace (OrbitPoints ab N hN) :=
  SchubertAnalyticFlagTransportSpecs.pointTopology (orbitToGrassmannian ab N hN)

def OrbitPointComparison : Prop :=
  ∀ (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N),
    ∃ e : OrbitPoints ab N hN ≃ₜ boundedOrbit ab N,
      ∀ p, orbitPointSubspace p = boundedSubspace (e p).val

abbrev OccupiedSchubertPoints (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) :=
  Points (occupiedSchubert ab N hN) complexAlgebra

def schubertPointSubspace {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    (p : OccupiedSchubertPoints ab N hN) : Submodule ℂ (BoundedWindow 2 N) :=
  grassmannianSubspace (windowBasis 2 (-(N : ℤ)) (2 * N))
    (windowDimension_le (occupiedDimension ab N hN)) (p ≫ schubertToGrassmannian ab N hN _)

instance occupiedSchubertPointsTopology (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) :
    TopologicalSpace (OccupiedSchubertPoints ab N hN) :=
  SchubertAnalyticFlagTransportSpecs.pointTopology (schubertToGrassmannian ab N hN _)

/-- The actual complex points of the closed scheme inherit the analytic topology
of the lattice model. Orbit strata enter it through their own closed Schubert schemes. -/
def SchubertStratification : Prop :=
  ∀ (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N),
    ∃ E : OccupiedSchubertPoints ab N hN ≃ₜ schubertLatticeSet ab N,
      (∀ p, schubertPointSubspace p = boundedSubspace (E p).val) ∧
      ∀ (cd : DominantPair) (hN' : OrbitBound cd N), Below cd ab →
        ∃ (hd : occupiedDimension cd N hN' = occupiedDimension ab N hN)
          (j : occupiedSchubert cd N hN' ⟶ occupiedSchubert ab N hN),
          IsClosedImmersion j.left ∧
          j ≫ schubertToGrassmannian ab N hN _ =
            schubertToGrassmannian cd N hN' _ ≫ eqToHom (congrArg (BoundedGrassmannian N) hd) ∧
          Topology.IsEmbedding (fun q : OrbitPoints cd N hN' ↦
            (q ≫ orbitToSchubert cd N hN' ≫ j : OccupiedSchubertPoints ab N hN)) ∧
          Set.range (fun q : OrbitPoints cd N hN' ↦ E (q ≫ orbitToSchubert cd N hN' ≫ j)) =
            {L | L.val ∈ boundedOrbit cd N}

abbrev Affine := SchubertNormalizedJetGraphSpecs.Affine

abbrev affinePoint {n : ℕ} := @SchubertNormalizedJetGraphSpecs.affinePoint n

abbrev affineHead {n : ℕ} := @SchubertNormalizedJetGraphSpecs.affineHead n

theorem projectiveLineDimension : 1 ≤ Module.finrank ℂ (Fin 2 → ℂ) :=
  SchubertNormalizedJetGraphSpecs.projectiveLineDimension

abbrev ProjectiveLine := SchubertNormalizedJetGraphSpecs.ProjectiveLine

def normalizedRow {m : ℕ} (i : Fin 2) (z : JetRing m) : Row m :=
  fun j ↦ if j = i then 1 else z

abbrev chartLine := SchubertNormalizedJetGraphSpecs.normalizedLine

def chartKernel {m : ℕ} (b : ℤ) (i : Fin 2) (z : Fin m → ℂ) : Submodule O (Coordinates 2) :=
  shiftedKernel b (normalizedRow i ((jetCoefficients m).symm z))

/-- The two normalized row charts are algebraic products over the two standard opens
of the projective line. The projection takes the line of constant coefficients. -/
def PrimitiveRowCharts : Prop :=
  ∀ (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) (hm : 0 < difference ab),
    let m := difference ab
    let Y := orbitScheme ab N hN
    SmoothOfRelativeDimension m Y.hom ∧
    ∃ (π : Y ⟶ ProjectiveLine) (c : Fin 2 → (Affine m ⟶ Y))
      (u : Fin 2 → (Affine 1 ⟶ ProjectiveLine)),
      (∀ i, IsOpenImmersion (c i).left ∧ IsOpenImmersion (u i).left ∧
        IsPullback (c i) (affineHead hm) π (u i)) ∧
      (∀ y : Y.left, ∃ i, y ∈ Set.range (c i).left) ∧
      (∀ y : ProjectiveLine.left, ∃ i, y ∈ Set.range (u i).left) ∧
      (∀ i (x : Fin 1 → ℂ),
        grassmannianSubspace (Pi.basisFun ℂ (Fin 2)) projectiveLineDimension
          (affinePoint x ≫ u i) = chartLine i (x 0)) ∧
      (∀ i (z : Fin m → ℂ),
        ∃ L : BoundedLattice 2 N, L.val.val = chartKernel ab.val.2 i z ∧
          orbitPointSubspace (hN := hN) (affinePoint z ≫ c i) = boundedSubspace L) ∧
      (∀ i, Topology.IsOpenEmbedding
        (fun z : Fin m → ℂ ↦ (affinePoint z ≫ c i : OrbitPoints ab N hN))) ∧
      ∀ z w : Fin m → ℂ, affinePoint z ≫ c 0 = affinePoint w ≫ c 1 ↔
        ∃ v : (JetRing m)ˣ, (jetCoefficients m).symm z = v.val ∧
          (jetCoefficients m).symm w = (v⁻¹).val

def EqualPairOrbit : Prop :=
  ∀ (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N), ab.val.1 = ab.val.2 →
    closureLattices ab = {scalarLattice 2 ab.val.1} ∧
      gl2Orbit ab = {scalarLattice 2 ab.val.1} ∧
      Nonempty (orbitScheme ab N hN ≅ (testSpec ℂ).obj (Opposite.op complexAlgebra))

def stageImage (a : ℤ) (m : ℕ) (S : Set GL2Lattice) : Set (WindowStage 2 a m) :=
  windowStagePoint a m '' S

/-- Restriction of the finite jet action, including its effect on windows and its
agreement with reduction of positive loops. -/
def JetActionOn (a : ℤ) (m n : ℕ) (hn : 1 ≤ n) (hmn : m ≤ n) (S : Set GL2Lattice) :
    Prop :=
  ∃ ρ : MulAction (GLJets 2 n hn) (stageImage a m S),
    (∀ g : GLJets 2 n hn, ∀ p : stageImage a m S,
      windowStageSubspace (ρ.smul g p).val =
        (windowStageSubspace p.val).map (windowJetLinear a hmn g.val)) ∧
    (∀ (g : GL (Fin 2) O) (L : GL2Lattice) (hL : L ∈ S),
      (ρ.smul (reduceGL 2 n hn g) ⟨windowStagePoint a m L, ⟨L, hL, rfl⟩⟩).val =
        windowStagePoint a m (positiveGLMap 2 g • L)) ∧
    Continuous (fun x : GLJets 2 n hn × stageImage a m S ↦ ρ.smul x.1 x.2) ∧
    ∀ (d : WindowDimension 2 a m) (I : Pivot (WindowIndex 2 m) d.val)
      (g : GLJets 2 n hn) (A : Matrix (Outside I) (Inside I) ℂ),
      let B := jetMatrixCoefficients g.val
      ∃ (J : Pivot (WindowIndex 2 m) d.val)
        (U : Set (JetMatrixCoefficients 2 n × Matrix (Outside I) (Inside I) ℂ))
        (F : JetMatrixCoefficients 2 n × Matrix (Outside I) (Inside I) ℂ →
          Matrix (Outside J) (Inside J) ℂ),
        (B, A) ∈ U ∧ IsOpen U ∧ AnalyticOnNhd ℂ F U ∧
        ∀ (g' : GLJets 2 n hn) (C : Matrix (Outside I) (Inside I) ℂ)
          (p : stageImage a m S), (jetMatrixCoefficients g'.val, C) ∈ U →
          windowStageSubspace p.val =
            grassmannianSubspace (windowBasis 2 a m) (windowDimension_le d)
              (grassmannianChartPoint (windowBasis 2 a m) (windowDimension_le d) I C) →
          windowStageSubspace (ρ.smul g' p).val =
            grassmannianSubspace (windowBasis 2 a m) (windowDimension_le d)
              (grassmannianChartPoint (windowBasis 2 a m) (windowDimension_le d) J
                (F (jetMatrixCoefficients g'.val, C)))

def SchubertJetActions : Prop :=
  ∀ (ab : DominantPair) (a : ℤ) (m n : ℕ) (hn : 1 ≤ n) (hmn : m ≤ n),
    a ≤ ab.val.2 → ab.val.1 ≤ a + (m : ℤ) →
    JetActionOn a m n hn hmn (gl2Orbit ab) ∧
    JetActionOn a m n hn hmn (closureLattices ab)

end

end RepTheorySurvey.Geometric.RankTwoSchubertStrataSpecs
