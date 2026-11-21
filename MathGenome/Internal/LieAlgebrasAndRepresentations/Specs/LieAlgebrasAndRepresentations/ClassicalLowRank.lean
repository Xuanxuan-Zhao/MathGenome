import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalRootsA
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalRootsB
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalRootsC
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalRootsD
import Mathlib.Algebra.Lie.Prod

/-! The low-rank part of LA-D08 (notes/005, lines 1949–1955 and 1979–1983).
The integer coordinate vectors are viewed with their ordinary Euclidean dot
product, equivalently after embedding each coordinate into the reals. -/

namespace Specs.LieAlgebrasAndRepresentations.ClassicalLowRank

def axis {n : ℕ} (i : Fin n) : Fin n → ℤ := fun j => if j = i then 1 else 0

def signed {n : ℕ} (i : Fin n) (negative : Bool) : Fin n → ℤ :=
  if negative then -axis i else axis i

def aRoot {n : ℕ} (ij : {p : Fin n × Fin n // p.1 ≠ p.2}) : Fin n → ℤ :=
  axis ij.val.1 - axis ij.val.2

def dRoot {n : ℕ} (p : {p : Fin n × Fin n // p.1 < p.2} × Bool × Bool) :
    Fin n → ℤ := signed p.1.val.1 p.2.1 + signed p.1.val.2 p.2.2

def bRoot {n : ℕ} (p : (Fin n × Bool) ⊕ ({p : Fin n × Fin n // p.1 < p.2} × Bool × Bool)) :
    Fin n → ℤ := p.elim (fun q => signed q.1 q.2) dRoot

def cRoot {n : ℕ} (p : (Fin n × Bool) ⊕ ({p : Fin n × Fin n // p.1 < p.2} × Bool × Bool)) :
    Fin n → ℤ := p.elim (fun q => 2 • signed q.1 q.2) dRoot

def aOneSumRoot (p : Bool × Bool) : Fin 4 → ℤ :=
  if p.1 then (if p.2 then ![0, 0, -1, 1] else ![0, 0, 1, -1])
  else (if p.2 then ![-1, 1, 0, 0] else ![1, -1, 0, 0])

def dot {n : ℕ} (x y : Fin n → ℤ) : ℤ := ∑ i, x i * y i

/-- A bijection between the full coordinate root sets represented by two
injective enumerations. Proportional Gram matrices give a similarity of the
real root spans: a linear combination has squared norm zero on one side
exactly when the matching combination does on the other. The Gram ratio
also cancels in every ordered pairing with a coroot. -/
def CoordinateIdentification {n m : ℕ} (R : Set (Fin n → ℤ)) (S : Set (Fin m → ℤ))
    (r s : ℕ) : Prop :=
  0 < r ∧ 0 < s ∧
  ∃ (k : ℕ) (x : Fin k → Fin n → ℤ) (y : Fin k → Fin m → ℤ),
    Function.Injective x ∧ Function.Injective y ∧
    Set.range x = R ∧ Set.range y = S ∧
    ∀ i j, (r : ℤ) * dot (x i) (x j) = (s : ℤ) * dot (y i) (y j)

def b1_a1_coordinates_type : Prop :=
  CoordinateIdentification (Set.range (@bRoot 1)) (Set.range (@aRoot 2)) 2 1

def c1_a1_coordinates_type : Prop :=
  CoordinateIdentification (Set.range (@cRoot 1)) (Set.range (@aRoot 2)) 1 2

/-- The rank-two similarity scales squared lengths by two. -/
def b2_c2_coordinates_type : Prop :=
  CoordinateIdentification (Set.range (@bRoot 2)) (Set.range (@cRoot 2)) 2 1

def d2_a1_sum_coordinates_type : Prop :=
  CoordinateIdentification (Set.range (@dRoot 2)) (Set.range aOneSumRoot) 1 1

def d3_a3_coordinates_type : Prop :=
  CoordinateIdentification (Set.range (@dRoot 3)) (Set.range (@aRoot 4)) 1 1

def b1_a1_type : Prop :=
  Nonempty (ClassicalRootsB.algebra 1 ≃ₗ⁅ℂ⁆ ClassicalRootsA.sl 1)

def c1_a1_type : Prop :=
  Nonempty (ClassicalRootsC.sp 1 ≃ₗ⁅ℂ⁆ ClassicalRootsA.sl 1)

def b2_c2_type : Prop :=
  Nonempty (ClassicalRootsB.algebra 2 ≃ₗ⁅ℂ⁆ ClassicalRootsC.sp 2)

def d2_a1_sum_type : Prop :=
  Nonempty (ClassicalRootsD.algebra 2 ≃ₗ⁅ℂ⁆ (ClassicalRootsA.sl 1 × ClassicalRootsA.sl 1))

def d3_a3_type : Prop :=
  Nonempty (ClassicalRootsD.algebra 3 ≃ₗ⁅ℂ⁆ ClassicalRootsA.sl 3)

def d1_not_semisimple_type : Prop := ClassicalRootsD.d1_not_semisimple_type

end Specs.LieAlgebrasAndRepresentations.ClassicalLowRank
