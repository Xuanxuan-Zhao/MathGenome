import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.EquivariantIntersectionComplexes

namespace RepTheorySurvey.Geometric.CentralSchubertComparisonSpecs

open CategoryTheory
open LinearAlgebraicGroups (Points)
open LatticeModelSpecs BoundedLatticeSpecs RankTwoSchubertStrataSpecs
open SchubertIntersectionConstructibilitySpecs EquivariantIntersectionComplexesSpecs
open scoped MatrixGroups

noncomputable section

set_option autoImplicit false

/-- Multiply a rank-two lattice by the scalar `t^a`. -/
def translate (a : ℤ) (L : GL2Lattice) : GL2Lattice :=
  mapLattice (diagonalEquiv (fun _ : Fin 2 ↦ a)) L

/-- Add the same integer to both entries of a dominant pair. -/
def shiftPair (a : ℤ) (ab : DominantPair) : DominantPair :=
  ⟨(ab.val.1 + a, ab.val.2 + a), by
    have hab : ab.val.2 ≤ ab.val.1 := ab.property
    exact add_le_add_left hab a⟩

/-- The scalar translation on the minimal stable windows, before comparison
with the occupied reduced Schubert schemes. -/
structure ShiftedMinimalWindow (a : ℤ) (ab : DominantPair) : Prop where
  mapsWindow (L : WindowLattice 2 ab.val.2 (difference ab)) :
    Between (ab.val.2 + a + (difference ab : ℤ)) (ab.val.2 + a) (translate a L.val)
  schemeComparison (d : WindowDimension 2 ab.val.2 (difference ab)) :
    ∃ d' : WindowDimension 2 (ab.val.2 + a) (difference ab), d'.val = d.val ∧
      ∃ e : windowStableScheme 2 ab.val.2 (difference ab) d ≅
          windowStableScheme 2 (ab.val.2 + a) (difference ab) d',
        ∀ (q : Points (windowStableScheme 2 ab.val.2 (difference ab) d) complexAlgebra)
          (L : WindowLattice 2 ab.val.2 (difference ab)),
          windowSchemeSubspace q = latticeSubspace ab.val.2 (difference ab) L.val →
          windowSchemeSubspace (q ≫ e.hom) =
            latticeSubspace (ab.val.2 + a) (difference ab) (translate a L.val)

/-- Continuity tested on maps into two bounded stages whose lattice values are
related by scalar translation. -/
def ContinuousBoundedTranslation (a : ℤ) : Prop :=
  ∀ (N M : ℕ) {V : Type} [TopologicalSpace V]
    (e : V → BoundedLattice 2 N) (u : V → BoundedLattice 2 M),
    Continuous e → (∀ x, (u x).val = translate a (e x).val) → Continuous u

/-- The lattice and bounded continuity facts used to pass from the translated
minimal window to the actual stratified Schubert spaces. -/
structure ScalarTranslationProperties (a : ℤ) : Prop where
  leftInverse : Function.LeftInverse (translate (-a)) (translate a)
  rightInverse : Function.RightInverse (translate (-a)) (translate a)
  orbitImage (ab : DominantPair) :
    translate a '' gl2Orbit ab = gl2Orbit (shiftPair a ab)
  closureImage (ab : DominantPair) :
    translate a '' closureLattices ab = closureLattices (shiftPair a ab)
  commutesWithPositiveLoop (g : GL (Fin 2) O) (L : GL2Lattice) :
    translate a (positiveGLMap 2 g • L) = positiveGLMap 2 g • translate a L
  continuousForward : ContinuousBoundedTranslation a
  continuousInverse : ContinuousBoundedTranslation (-a)

/-- The scheme isomorphism induces the analytic isomorphism on the same complex points,
with the scalar formulas and the actual orbit strata and actions. -/
structure SchubertTranslationData (a : ℤ) (ab : DominantPair) (N M : ℕ)
    (hN : OrbitBound ab N) (hM : OrbitBound (shiftPair a ab) M) where
  schemeIso : occupiedSchubert ab N hN ≅ occupiedSchubert (shiftPair a ab) M hM
  analyticIso : SchubertSpace ab N hN ≅ SchubertSpace (shiftPair a ab) M hM
  onPoints (p : SchubertSpace ab N hN) : analyticIso.hom p = p ≫ schemeIso.hom
  onInversePoints (p : SchubertSpace (shiftPair a ab) M hM) :
    analyticIso.inv p = p ≫ schemeIso.inv
  onLattices (p : SchubertSpace ab N hN) (L : BoundedLattice 2 N) :
    schubertPointSubspace p = boundedSubspace L →
    schubertPointSubspace (analyticIso.hom p) =
      latticeSubspace (-(M : ℤ)) (2 * M) (translate a L.val)
  onInverseLattices (p : SchubertSpace (shiftPair a ab) M hM) (L : BoundedLattice 2 M) :
    schubertPointSubspace p = boundedSubspace L →
    schubertPointSubspace (analyticIso.inv p) =
      latticeSubspace (-(N : ℤ)) (2 * N) (translate (-a) L.val)
  preservesStrata : ∃ e : OrbitIndex ab ≃ OrbitIndex (shiftPair a ab), ∀ j : OrbitIndex ab,
    (e j).val = j.val ∧
    analyticIso.hom ⁻¹' orbitPoints (shiftPair a ab) M hM (e j) = orbitPoints ab N hN j ∧
    orbitDimension (shiftPair a ab) (e j).val = orbitDimension ab j.val
  sameDepth (j : OrbitIndex ab) (j' : OrbitIndex (shiftPair a ab)) (h : j.val = j'.val) :
    analyticIso.hom ⁻¹' orbitPoints (shiftPair a ab) M hM j' = orbitPoints ab N hN j ∧
    orbitDimension (shiftPair a ab) j'.val = orbitDimension ab j.val
  intertwines (J : GL2JetParameters) (A : SchubertJetAction J ab N hN)
      (B : SchubertJetAction J (shiftPair a ab) M hM) :
    JetMapsCommute A.action B.action analyticIso.hom

namespace Expected

def SchubertTranslation : Prop :=
  ∀ (a : ℤ) (ab : DominantPair),
    ShiftedMinimalWindow a ab → ScalarTranslationProperties a →
    ∀ (N M : ℕ) (hN : OrbitBound ab N) (hM : OrbitBound (shiftPair a ab) M),
      Nonempty (SchubertTranslationData a ab N M hN hM)

end Expected

end

end RepTheorySurvey.Geometric.CentralSchubertComparisonSpecs
