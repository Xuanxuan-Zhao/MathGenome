import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ExceptionalCoordinateE
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SerreFiniteType
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.VoganEquivalence

/-! The outer (E_6) portion of res:J08. Indices start at zero, so the branch is
index 2 and the short arm ends at index 5. -/

namespace Specs.LieAlgebrasAndRepresentations.ExceptionalOuterInvolutions

open _root_.LieAlgebrasAndRepresentations
open ExceptionalGF (QVec)
open Serre
open _root_.LieAlgebrasAndRepresentations.RealForms
open StableCartanVoganData (DiagramData Presents)
open VoganEquivalence (colorSign reflectedColors)
open CartanDecompositionSignature (complexFixed killingSignature)
open PolarRealStructures (involutionConjugation)

universe u

def e6Cartan : Matrix (Fin 6) (Fin 6) ℤ :=
  !![2,-1,0,0,0,0; -1,2,-1,0,0,0; 0,-1,2,-1,0,-1;
     0,0,-1,2,-1,0; 0,0,0,-1,2,0; 0,0,-1,0,0,2]

/-- The order of the existing coordinate basis is reordered into the chain
followed by the end of the short arm. -/
def coordinateIndex : Fin 6 ≃ Fin 6 :=
  { toFun := fun i => ![0,2,3,4,5,1] i
    invFun := fun i => ![0,5,1,2,3,4] i
    left_inv := by decide
    right_inv := by decide }

def diagramInvolution : Fin 6 ≃ Fin 6 :=
  { toFun := fun i => ![4,3,2,1,0,5] i
    invFun := fun i => ![4,3,2,1,0,5] i
    left_inv := by decide
    right_inv := by decide }

/-- Coordinates in the simple basis in the numbering of res:J08. -/
def simpleCoefficients (x : QVec 8) : QVec 6 :=
  let c₁ := -2 * x 5
  let c₅ := x 4 + c₁ / 2
  let c₄ := x 3 + c₅ + c₁ / 2
  let c₃ := x 2 + c₄ + c₁ / 2
  let c₆ := (x 0 + x 1 + c₃) / 2
  let c₂ := x 1 + c₃ + c₁ / 2 - c₆
  ![c₁,c₂,c₃,c₄,c₅,c₆]

def e6Coefficients : Finset (QVec 6) :=
  ExceptionalE.e6List.image simpleCoefficients

def fixedRoots : Finset (QVec 6) :=
  e6Coefficients.filter fun c => ∀ i, c (diagramInvolution i) = c i

/-- Fixed roots whose coefficient at vertex 3 is an even integer. -/
def evenFixedRoots : Finset (QVec 6) :=
  fixedRoots.filter fun c => (c 2).den = 1 ∧ (c 2).num % 2 = 0

def rootCountsType : Prop :=
  e6Coefficients.card = 72 ∧ fixedRoots.card = 24 ∧ evenFixedRoots.card = 8

/-- Coordinates of the restriction to the fixed Cartan in the folded basis. -/
def foldRoot (c : QVec 6) : QVec 4 := ![c 0 + c 4,c 1 + c 3,c 2,c 5]

/-- The projected roots for the involution with vertex 3 black. -/
def blackRoots : Finset (QVec 4) :=
  ((e6Coefficients \ fixedRoots) ∪ evenFixedRoots).image foldRoot

def positiveBlackRoots : Finset (QVec 4) :=
  blackRoots.filter fun c => (∀ i, 0 ≤ c i) ∧ c ≠ 0

def simpleBlackRoots : Finset (QVec 4) :=
  positiveBlackRoots.filter fun c =>
    ∀ d ∈ positiveBlackRoots, c - d ∉ positiveBlackRoots

def blackSimpleRootsType : Prop :=
  blackRoots.card = 32 ∧ simpleBlackRoots =
    {![0,1,0,0], ![1,0,0,0], ![0,1,1,0], ![0,0,0,1]}

/-- The (F_4) matrix in the order short, short, long, long. -/
def f4Cartan : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2,-1,0,0; -1,2,-2,0; 0,-1,2,-1; 0,0,-1,2]

/-- The (C_4) matrix in the order short, short, short, long. -/
def c4Cartan : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2,-1,0,0; -1,2,-1,0; 0,-1,2,-2; 0,0,-1,2]

abbrev Coloring := ZMod 2 × ZMod 2

def vertexColor (b : Coloring) (i : Fin 6) : ZMod 2 :=
  if i = 2 then b.1 else if i = 5 then b.2 else 0

def reflectColoring (i : Fin 6) (b : Coloring) : Coloring :=
  (reflectedColors e6Cartan i (vertexColor b) 2,
    reflectedColors e6Cartan i (vertexColor b) 5)

/-- The elementary fixed-vertex moves of res:J06. -/
def ColorMove (b c : Coloring) : Prop :=
  c = reflectColoring 2 b ∨ c = reflectColoring 5 b

def colorOrbitsType : Prop :=
  ∀ b c : Coloring, Relation.EqvGen ColorMove b c ↔ (b = 0 ↔ c = 0)

noncomputable section

def foldGenerators (x : Fin 6 → Algebra e6Cartan) : Fin 4 → Algebra e6Cartan :=
  ![x 0 + x 4, x 1 + x 3, x 2, x 5]

def foldedSerreType : Prop :=
  RelationsHold f4Cartan (foldGenerators (e e6Cartan))
    (foldGenerators (f e6Cartan)) (foldGenerators (h e6Cartan))

/-- The third short root is the restriction of either \(\alpha_2+\alpha_3\)
or \(\alpha_4+\alpha_3\). Take differences in these two interchanged lines. -/
def blackE : Fin 4 → Algebra e6Cartan :=
  ![e e6Cartan 1 + e e6Cartan 3, e e6Cartan 0 + e e6Cartan 4,
    ⁅e e6Cartan 1,e e6Cartan 2⁆ - ⁅e e6Cartan 3,e e6Cartan 2⁆, e e6Cartan 5]

def blackF : Fin 4 → Algebra e6Cartan :=
  ![f e6Cartan 1 + f e6Cartan 3, f e6Cartan 0 + f e6Cartan 4,
    ⁅f e6Cartan 2,f e6Cartan 1⁆ - ⁅f e6Cartan 2,f e6Cartan 3⁆, f e6Cartan 5]

def blackH : Fin 4 → Algebra e6Cartan :=
  ![h e6Cartan 1 + h e6Cartan 3, h e6Cartan 0 + h e6Cartan 4,
    h e6Cartan 1 + h e6Cartan 3 + (2 : ℂ) • h e6Cartan 2, h e6Cartan 5]

def blackFoldedSerreType : Prop := RelationsHold c4Cartan blackE blackF blackH

section Realizations

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

/-- The specified normalized action on the entire simple presentation. -/
def HasColor (E F H : Fin 6 → L) (b : Coloring) (a : L ≃ₗ⁅ℂ⁆ L) : Prop :=
  ∀ i, a (E i) = colorSign (vertexColor b i) • E (diagramInvolution i) ∧
    a (F i) = colorSign (vertexColor b i) • F (diagramInvolution i) ∧
    a (H i) = H (diagramInvolution i)

def realizeOuterType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (ω : Conjugation L)
    (E F H : Fin 6 → L), Presents e6Cartan E F H →
    (∀ i, ω.map (E i) = -F i ∧ ω.map (F i) = -E i ∧ ω.map (H i) = -H i) →
    ∀ b : Coloring, ∃ a : L ≃ₗ⁅ℂ⁆ L,
      HasColor E F H b a ∧ Intertwines ω ω a ∧ Function.Involutive a

/-- Classification of the normalized outer data in a compatible compact
presentation of the complex algebra of type (E_6). -/
def outerClassificationType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (ω : Conjugation L), PolarRealStructures.IsCompact ω →
    ∀ (E F H : Fin 6 → L), Presents e6Cartan E F H →
    (∀ i, ω.map (E i) = -F i ∧ ω.map (F i) = -E i ∧ ω.map (H i) = -H i) →
    (∀ (b c : Coloring) (a a' : L ≃ₗ⁅ℂ⁆ L), HasColor E F H b a → HasColor E F H c a' →
      ∀ (ha : Intertwines ω ω a) (hia : Function.Involutive a)
        (hb : Intertwines ω ω a') (hib : Function.Involutive a'),
      Nonempty ((involutionConjugation ω a ha hia).fixed ≃ₗ⁅ℝ⁆
        (involutionConjugation ω a' hb hib).fixed) ↔ (b = 0 ↔ c = 0)) ∧
    (∀ (b : Coloring) (a : L ≃ₗ⁅ℂ⁆ L), HasColor E F H b a →
      ∀ (ha : Intertwines ω ω a) (hia : Function.Involutive a),
      let K := complexFixed a
      let S := (involutionConjugation ω a ha hia).fixed
      if b = 0 then
        Nonempty (Algebra f4Cartan ≃ₗ⁅ℂ⁆ K) ∧
          Module.finrank ℂ K = 52 ∧ killingSignature S = -26
      else
        Nonempty (Algebra c4Cartan ≃ₗ⁅ℂ⁆ K) ∧
          Module.finrank ℂ K = 36 ∧ killingSignature S = 6)

end Realizations

end
end Specs.LieAlgebrasAndRepresentations.ExceptionalOuterInvolutions
