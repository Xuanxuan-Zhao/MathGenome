import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.CellularDegrees
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.Degree
import Mathlib.Data.ZMod.Basic

/-!
Independent statements for the real projective portion of
`prop:p202-homology-computations`, paper.tex 1601–1607, 1639–1654.
The space is the actual antipodal quotient of the geometric unit sphere,
with its quotient topology, including dimension zero.
No cellular differential or homology computation is assumed in these definitions.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace P202Specs.RealProjectiveHomology
open P202.Cellular P202Specs.SpheresDisks P202Specs.SingularChains
open P202Specs.CellularChains P202Specs.CellularDegrees

/-- Negation on the actual unit sphere in R^(n+1). -/
def antipodal (n : ℕ) : sphere n ⟶ sphere n :=
  TopCat.ofHom {
    toFun := fun x => ⟨-x.val, by
      simpa only [Metric.mem_sphere, dist_zero_right, norm_neg] using x.property⟩
    continuous_toFun := (continuous_neg.comp continuous_subtype_val).subtype_mk _ }

/-- Each equivalence class consists of a unit vector and its negative. -/
def antipodalSetoid (m : ℕ) : Setoid (sphere m) where
  r x y := x.val = y.val ∨ x.val = -y.val
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      intro x y h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h, neg_neg])
    trans := by
      intro x y z h k
      rcases h with h | h <;> rcases k with k | k
      · exact Or.inl (h.trans k)
      · exact Or.inr (h.trans k)
      · exact Or.inr (by rw [h, k])
      · exact Or.inl (by rw [h, k, neg_neg]) }

abbrev Space (m : ℕ) := Quotient (antipodalSetoid m)
abbrev projective (m : ℕ) : TopCat := TopCat.of (Space m)

/-- The sphere-to-projective quotient, with the quotient topology on its target. -/
def quotientMap (m : ℕ) : sphere m ⟶ projective m :=
  TopCat.ofHom ⟨Quotient.mk (antipodalSetoid m), continuous_quot_mk⟩

/-- Coordinates of the standard upper hemisphere of the j-dimensional
coordinate subsphere. For j=0 this is the first coordinate unit vector. -/
def hemisphereVector (m j : ℕ) (x : Disk j) : EuclideanSpace ℝ (Fin (m+1)) :=
  WithLp.toLp 2 (fun k => if h : k.val < j then x.val ⟨k.val, h⟩
    else if k.val = j then Real.sqrt (1 - ‖x.val‖ ^ 2) else 0)

/-- A standard CW structure must have precisely one cell in degrees 0..m,
with the hemisphere characteristic maps. The norm-one representative is a
conclusion, not an assumed parametrization certificate. -/
def StandardCW (m : ℕ) (C : CWStructure (Space m)) : Prop :=
  letI : CWStructure (Space m) := C
  ∃ labels : ∀ j, Cell (Space m) j ≃ { i : Unit // j ≤ m },
    ∀ (j : ℕ) (c : Cell (Space m) j) (x : Disk j),
      ∃ y : sphere m, y.val = hemisphereVector m j x ∧
        characteristic (Space m) j c x = quotientMap m y

/-- The integer in the differential from degree j to degree j-1. -/
def incidence (j : ℕ) : ℤ := 1 + (-1 : ℤ) ^ j

/-- Simultaneous characteristic-compatible coordinates of the actual skeletal
relative groups. The equation covers j=1 (coincident endpoints), every higher
cell, and all absent cells above m. -/
def CellularCalculation (m : ℕ) (C : CWStructure (Space m)) : Prop :=
  letI : CWStructure (Space m) := C
  ∃ (g : ∀ j, ℤ ≃ₗ[ℤ]
      P202Specs.RelativeSingularChains.relativeHomology ℤ ℤ
        (referenceDiskPair.{0} j) (j : ℤ))
    (e : ∀ j, chainGroup (Space m) ℤ ℤ j ≃ₗ[ℤ] (Cell (Space m) j →₀ ℤ)),
    (∀ j, CharacteristicCoordinates (Space m) ℤ ℤ j (g j) (e j)) ∧
    ∀ (n : ℕ) (c : Cell (Space m) (n+1)) (d : Cell (Space m) n) (a : ℤ),
      e n (differential (Space m) ℤ ℤ n
        (cellClass (Space m) ℤ ℤ (n+1) c (g (n+1) a))) d = incidence (n+1) * a

/-- The complete integral homology answer, with all degrees, the top cell,
the interior odd degrees, and dimension zero explicitly covered. -/
def HomologyCalculation (m : ℕ) : Prop :=
  ∀ j : ℕ,
    ((j = 0 ∨ (j = m ∧ Odd m)) →
      Nonempty (homology ℤ ℤ (projective m) (j : ℤ) ≃ₗ[ℤ] ℤ)) ∧
    ((0 < j ∧ j < m ∧ Odd j) →
      Nonempty (homology ℤ ℤ (projective m) (j : ℤ) ≃ₗ[ℤ] ZMod 2)) ∧
    ((¬ (j = 0 ∨ (j = m ∧ Odd m)) ∧ ¬ (0 < j ∧ j < m ∧ Odd j)) →
      IsZero (homology ℤ ℤ (projective m) (j : ℤ)))

namespace Expected

/-- The sign used for the attaching sphere of the j-cell, j=n+1. -/
def antipodalDegree : Prop :=
  ∀ n : ℕ, P202Specs.Degree.degree n (antipodal n) = (-1 : ℤ) ^ (n+1)

def cellularModel : Prop :=
  ∀ m : ℕ, ∃ C : CWStructure (Space m), StandardCW m C ∧ CellularCalculation m C

def integralHomology : Prop := ∀ m : ℕ, HomologyCalculation m

/-- The m=0 boundary case is the actual quotient, homeomorphic to a point. -/
def pointCase : Prop :=
  Nonempty (Space 0 ≃ₜ PUnit.{1}) ∧ HomologyCalculation 0

end Expected
end P202Specs.RealProjectiveHomology
