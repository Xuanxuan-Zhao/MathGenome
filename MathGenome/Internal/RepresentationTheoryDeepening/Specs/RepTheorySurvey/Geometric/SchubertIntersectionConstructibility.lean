import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.RankTwoSchubertStrata
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.MiddleExtension

noncomputable section

open CategoryTheory Topology

namespace RepTheorySurvey.Geometric.SchubertIntersectionConstructibilitySpecs

open Analytic Analytic.IntersectionComplex
open LatticeModelSpecs RankTwoSchubertStrataSpecs

/-- The complex points of the occupied reduced Schubert scheme with their analytic topology. -/
abbrev SchubertSpace (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) : TopCat.{0} :=
  TopCat.of (OccupiedSchubertPoints ab N hN)

abbrev OrbitIndex (ab : DominantPair) := Fin (difference ab / 2 + 1)

/-- The orbit at depth (j) has dominant label ((a-j,b+j)). -/
def orbitLabel (ab : DominantPair) (j : OrbitIndex ab) : DominantPair :=
  ⟨(ab.val.1 - (j.val : ℤ), ab.val.2 + (j.val : ℤ)), by
    have h := j.isLt
    have hab := ab.property
    change ab.val.2 ≤ ab.val.1 at hab
    change ab.val.2 + (j.val : ℤ) ≤ ab.val.1 - (j.val : ℤ)
    unfold difference at h
    omega⟩

def orbitDimension (ab : DominantPair) (k : ℕ) : ℕ :=
  difference ab - 2 * k

/-- Orbit membership on the scheme's actual complex points, read in the bounded lattice model. -/
def orbitPoints (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) (j : OrbitIndex ab) :
    Set (SchubertSpace ab N hN) :=
  {p | ∃ L : BoundedLattice 2 N,
    L.val ∈ gl2Orbit (orbitLabel ab j) ∧ schubertPointSubspace p = boundedSubspace L}

/-- The initial union of the orbits through depth (k), from largest dimension down. -/
def stagePoints (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) (k : ℕ) :
    Set (SchubertSpace ab N hN) :=
  {p | ∃ j : OrbitIndex ab, j.val ≤ k ∧ p ∈ orbitPoints ab N hN j}

/-- An open stage and its stratification agree with the indicated orbits in the actual
Schubert space. -/
def RealizesOrbitStage {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    {Y : TopCat.{0}} (f : Y ⟶ SchubertSpace ab N hN) (k : ℕ)
    (P : Stratification Y) : Prop :=
  IsOpenEmbedding f ∧ Set.range f = stagePoints ab N hN k ∧
    ∃ e : P.Index ≃ {j : OrbitIndex ab // j.val ≤ k},
      ∀ i : P.Index,
        Set.range (P.stratum i).inclusion = f ⁻¹' orbitPoints ab N hN (e i).val ∧
        (P.stratum i).complexDimension = orbitDimension ab (e i).val.val

/-- The dimension filtration realizes the successive open orbit unions. At an attachment the
actual untruncated direct image is bounded constructible, including on the new closed stratum.
The normalized truncated complex is middle perverse at every stage and strict on each new
stratum. -/
inductive IsNormalizedOrbitIC (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) :
    {Y : TopCat.{0}} → {s : ℕ} → (Y ⟶ SchubertSpace ab N hN) → ℕ →
      Stratification Y → DimensionFiltration Y s → Prop
  | top {Y : TopCat.{0}} (f : Y ⟶ SchubertSpace ab N hN) (P : Stratification Y)
      (stage : RealizesOrbitStage f 0 P)
      (perverse : IsMiddlePerverse P (shiftedConstant Y (difference ab)).obj) :
      IsNormalizedOrbitIC ab N hN f 0 P (.top Y (difference ab))
  | attach {U Y : TopCat.{0}} {d k : ℕ} {D : DimensionFiltration U d}
      (f : Y ⟶ SchubertSpace ab N hN) (P : Stratification Y) (Q : Stratification U)
      (j : U ⟶ Y) (hj : IsOpenEmbedding j) (hs : orbitDimension ab (k + 1) < d)
      (previous : IsNormalizedOrbitIC ab N hN (j ≫ f) k Q D)
      (stage : RealizesOrbitStage f (k + 1) P)
      (strata : AttachmentStratification j (orbitDimension ab (k + 1)) Q P)
      (boundaryConstructible : IsConstructibleOnBoundary j ((derivedDirectImage j).obj (complex D)))
      (directImageConstructible : IsConstructible P ((derivedDirectImage j).obj (complex D)).obj)
      (perverse : IsMiddlePerverse P ((attachment j hj (orbitDimension ab (k + 1))).obj (complex D)).obj)
      (strict : IsStrictExtension hj (orbitDimension ab (k + 1))
        ((attachment j hj (orbitDimension ab (k + 1))).obj (complex D))) :
      IsNormalizedOrbitIC ab N hN f (k + 1) P (.attach D j hj hs)

/-- Every dominant pair admits the normalized bounded constructible middle intersection complex
on its actual reduced Schubert variety in every sufficiently large window. -/
def SchubertIntersectionConstructibility : Prop :=
  ∀ (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N),
    ∃ (P : Stratification (SchubertSpace ab N hN))
      (D : DimensionFiltration (SchubertSpace ab N hN) (orbitDimension ab (difference ab / 2))),
      IsNormalizedOrbitIC ab N hN (𝟙 (SchubertSpace ab N hN)) (difference ab / 2) P D

end RepTheorySurvey.Geometric.SchubertIntersectionConstructibilitySpecs
