import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RealRootSpace
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RootWeightLattices
import Mathlib.LinearAlgebra.Basis.Defs

/-! Chapter 7, opening conventions (source lines 3107–3121).
All constructions below permit an empty index type. They are defined for arbitrary
families of forms and Cartan elements, so in particular apply to the fixed simple
roots and normalized simple coroots of a complex semisimple Lie algebra.

The real-to-complex comparison uses a real simple-root basis `b` and the complex
simple-coroot basis `c` of the Cartan. It constructs extension of real weights by
the formula χ(c i) = ⟪x, (b i)∨⟫, rather than assuming a lattice identification.

-/
noncomputable section
namespace Specs.LieAlgebrasAndRepresentations.HighestWeightData
open _root_.LieAlgebrasAndRepresentations Module
universe u v w
variable {H : Type u} [AddCommGroup H] [Module ℂ H] {ι : Type v}

/-- Q₊ = ∑ ℕ αᵢ, including the empty sum. -/
def positiveRootCone_value (α : ι → Module.Dual ℂ H) : Submodule ℕ (Module.Dual ℂ H) :=
  Submodule.span ℕ (Set.range α)

/-- Q = ∑ ℤ αᵢ. -/
def integralRootLattice_value (α : ι → Module.Dual ℂ H) : Submodule ℤ (Module.Dual ℂ H) :=
  Submodule.span ℤ (Set.range α)

/-- P consists of complex linear forms integral on every simple coroot. -/
def integralWeights_value (h : ι → H) : Submodule ℤ (Module.Dual ℂ H) where
  carrier := {χ | ∀ i, ∃ z : ℤ, χ (h i) = (z : ℂ)}
  zero_mem' := fun _ => ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy i
    obtain ⟨a, ha⟩ := hx i
    obtain ⟨b, hb⟩ := hy i
    exact ⟨a + b, by simp [ha, hb]⟩
  smul_mem' := by
    intro z x hx i
    obtain ⟨a, ha⟩ := hx i
    exact ⟨z * a, by simp [ha, zsmul_eq_mul]⟩

/-- P₊: nonnegative integral evaluations. This avoids ordering ℂ. -/
def dominantWeights_value (h : ι → H) : Submodule ℕ (Module.Dual ℂ H) where
  carrier := {χ | ∀ i, ∃ n : ℕ, χ (h i) = (n : ℂ)}
  zero_mem' := fun _ => ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy i
    obtain ⟨a, ha⟩ := hx i
    obtain ⟨b, hb⟩ := hy i
    exact ⟨a + b, by simp [ha, hb]⟩
  smul_mem' := by
    intro n x hx i
    obtain ⟨a, ha⟩ := hx i
    exact ⟨n * a, by simp [ha, nsmul_eq_mul]⟩

/-- μ ≤ χ iff χ − μ ∈ Q₊. -/
def weightLE_value (α : ι → Module.Dual ℂ H) (μ χ : Module.Dual ℂ H) : Prop :=
  χ - μ ∈ positiveRootCone_value α

variable {L : Type w} [LieRing L] [LieAlgebra ℂ L]
variable (V : Type*) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]

/-- Ordinary simultaneous eigenspaces, with no finite-dimensionality restriction on V. -/
def weightSpace_value (H : LieSubalgebra ℂ L) (μ : Module.Dual ℂ H) : Submodule ℂ V :=
  (LieModule.weightSpace V (μ : H → ℂ)).toSubmodule

variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Complex extension of a real weight, characterized on simple coroots. -/
def realization_value (b : Basis ι ℝ E) (c : Basis ι ℂ H) :
    E →ₗ[ℝ] Module.Dual ℂ H where
  toFun x := c.constr ℂ (fun i => (inner ℝ x (coroot (b i)) : ℂ))
  map_add' x y := by
    apply c.ext
    intro i
    simp [inner_add_left]
  map_smul' r x := by
    apply c.ext
    intro i
    simp [real_inner_smul_left]


-- Independent types of the public constructions.
def positiveRootCone_type := ∀ {H : Type u} [AddCommGroup H] [Module ℂ H]
  {ι : Type v}, (ι → Module.Dual ℂ H) → Submodule ℕ (Module.Dual ℂ H)

def integralRootLattice_type := ∀ {H : Type u} [AddCommGroup H] [Module ℂ H]
  {ι : Type v}, (ι → Module.Dual ℂ H) → Submodule ℤ (Module.Dual ℂ H)

def integralWeights_type := ∀ {H : Type u} [AddCommGroup H] [Module ℂ H]
  {ι : Type v}, (ι → H) → Submodule ℤ (Module.Dual ℂ H)

def dominantWeights_type := ∀ {H : Type u} [AddCommGroup H] [Module ℂ H]
  {ι : Type v}, (ι → H) → Submodule ℕ (Module.Dual ℂ H)

def weightLE_type := ∀ {H : Type u} [AddCommGroup H] [Module ℂ H]
  {ι : Type v}, (ι → Module.Dual ℂ H) → Module.Dual ℂ H → Module.Dual ℂ H → Prop

def weightSpace_type := ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L]
  (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
  (H : LieSubalgebra ℂ L), Module.Dual ℂ H → Submodule ℂ V

def realization_type := ∀ {H : Type u} [AddCommGroup H] [Module ℂ H] {ι : Type v}
  {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  Basis ι ℝ E → Basis ι ℂ H → E →ₗ[ℝ] Module.Dual ℂ H

def mem_weightSpace_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L]
  (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
  (H : LieSubalgebra ℂ L) (μ : Module.Dual ℂ H) (v : V),
  v ∈ weightSpace_value V H μ ↔ ∀ h : H, ⁅(h : L), v⁆ = μ h • v

def root_action_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L]
  (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
  (H : LieSubalgebra ℂ L) (α μ : Module.Dual ℂ H) (x : L) (v : V),
  x ∈ RootDecomposition.rootSpace_value H α →
  v ∈ weightSpace_value V H μ →
  ⁅x, v⁆ ∈ weightSpace_value V H (μ + α)

def dominant_iff_type : Prop :=
  ∀ {H : Type u} [AddCommGroup H] [Module ℂ H] {ι : Type v}
  (h : ι → H) (χ : Module.Dual ℂ H),
  χ ∈ dominantWeights_value h ↔ χ ∈ integralWeights_value h ∧ ∀ i, 0 ≤ (χ (h i)).re


def mem_integralWeights_type : Prop :=
  ∀ {H : Type u} [AddCommGroup H] [Module ℂ H] {ι : Type v},
∀ (h : ι → H) (χ : Module.Dual ℂ H),
χ ∈ integralWeights_value h ↔ ∀ i, ∃ z : ℤ, χ (h i) = (z : ℂ)

def mem_dominantWeights_type : Prop :=
  ∀ {H : Type u} [AddCommGroup H] [Module ℂ H] {ι : Type v},
∀ (h : ι → H) (χ : Module.Dual ℂ H),
χ ∈ dominantWeights_value h ↔ ∀ i, ∃ n : ℕ, χ (h i) = (n : ℂ)

def mem_positiveRootCone_iff_type : Prop :=
  ∀ {H : Type u} [AddCommGroup H] [Module ℂ H] {ι : Type v},
∀ [Fintype ι]
    (α : ι → Module.Dual ℂ H) (χ : Module.Dual ℂ H),
χ ∈ positiveRootCone_value α ↔ ∃ n : ι → ℕ, ∑ i, n i • α i = χ

def weightLE_antisymm_type : Prop :=
  ∀ {H : Type u} [AddCommGroup H] [Module ℂ H] {ι : Type v},
∀ (a : Basis ι ℂ (Module.Dual ℂ H))
    {χ μ : Module.Dual ℂ H} (h₁ : weightLE_value a χ μ) (h₂ : weightLE_value a μ χ),
χ = μ

def weightLE_refl_type : Prop :=
  ∀ {H : Type u} [AddCommGroup H] [Module ℂ H] {ι : Type v},
∀ (α : ι → Module.Dual ℂ H) (χ : Module.Dual ℂ H),
weightLE_value α χ χ

def weightLE_trans_type : Prop :=
  ∀ {H : Type u} [AddCommGroup H] [Module ℂ H] {ι : Type v},
∀ (α : ι → Module.Dual ℂ H) {χ μ ν : Module.Dual ℂ H}
    (h₁ : weightLE_value α χ μ) (h₂ : weightLE_value α μ ν),
weightLE_value α χ ν

def realization_apply_coroot_type : Prop :=
  ∀ {H : Type u} [AddCommGroup H] [Module ℂ H] {ι : Type v},
∀ {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
∀ (b : Basis ι ℝ E) (c : Basis ι ℂ H)
    (x : E) (i : ι),
realization_value b c x (c i) = (inner ℝ x (coroot (b i)) : ℂ)

def realization_unique_type : Prop :=
  ∀ {H : Type u} [AddCommGroup H] [Module ℂ H] {ι : Type v},
∀ {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
∀ (b : Basis ι ℝ E) (c : Basis ι ℂ H)
    (x : E) (χ : Module.Dual ℂ H)
    (hχ : ∀ i, χ (c i) = (inner ℝ x (coroot (b i)) : ℂ)),
χ = realization_value b c x

def realization_integral_iff_type : Prop :=
  ∀ {H : Type u} [AddCommGroup H] [Module ℂ H] {ι : Type v},
∀ {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
∀ (b : Basis ι ℝ E) (c : Basis ι ℂ H) (x : E),
realization_value b c x ∈ integralWeights_value c ↔ x ∈ weightLattice b

def realization_injective_type : Prop :=
  ∀ {H : Type u} [AddCommGroup H] [Module ℂ H] {ι : Type v},
∀ {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
∀ [Finite ι] [DecidableEq ι]
    (b : Basis ι ℝ E) (c : Basis ι ℂ H),
Function.Injective (realization_value b c)

def integralWeights_realization_type : Prop :=
  ∀ {H : Type u} [AddCommGroup H] [Module ℂ H] {ι : Type v},
∀ {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
∀ [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) (c : Basis ι ℂ H) (χ : Module.Dual ℂ H)
    (hχ : χ ∈ integralWeights_value c),
∃ x ∈ weightLattice b, realization_value b c x = χ

def realization_weightLattice_type : Prop :=
  ∀ {H : Type u} [AddCommGroup H] [Module ℂ H] {ι : Type v},
∀ {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
∀ [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) (c : Basis ι ℂ H),
(weightLattice b).map ((realization_value b c).restrictScalars ℤ) = integralWeights_value c

def realization_rootLattice_type : Prop :=
  ∀ {H : Type u} [AddCommGroup H] [Module ℂ H] {ι : Type v},
∀ {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
∀ (b : Basis ι ℝ E) (c : Basis ι ℂ H)
    (α : ι → Module.Dual ℂ H)
    (hα : ∀ i j, α i (c j) = (inner ℝ (b i) (coroot (b j)) : ℂ)),
(rootLattice b).map ((realization_value b c).restrictScalars ℤ) = integralRootLattice_value α

def realization_positiveRootCone_type : Prop :=
  ∀ {H : Type u} [AddCommGroup H] [Module ℂ H] {ι : Type v},
∀ {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
∀ (b : Basis ι ℝ E) (c : Basis ι ℂ H)
    (α : ι → Module.Dual ℂ H)
    (hα : ∀ i j, α i (c j) = (inner ℝ (b i) (coroot (b j)) : ℂ)),
(Submodule.span ℕ (Set.range b)).map ((realization_value b c).restrictScalars ℕ) =
      positiveRootCone_value α

def realization_dominant_iff_type : Prop :=
  ∀ {H : Type u} [AddCommGroup H] [Module ℂ H] {ι : Type v},
∀ {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
∀ [Finite ι] [DecidableEq ι]
    (R : Set E) (v : E) (b : Basis ι ℝ E) (hb : IsSimpleBasis R v b)
    (c : Basis ι ℂ H) (x : E),
realization_value b c x ∈ dominantWeights_value c ↔
      x ∈ weightLattice b ∧ x ∈ closedSimpleChamber R v

def realization_dominant_image_type : Prop :=
  ∀ {H : Type u} [AddCommGroup H] [Module ℂ H] {ι : Type v},
∀ {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
∀ [Fintype ι] [DecidableEq ι]
    (R : Set E) (v : E) (b : Basis ι ℝ E) (hb : IsSimpleBasis R v b)
    (c : Basis ι ℂ H),
realization_value b c '' {x | x ∈ weightLattice b ∧ x ∈ closedSimpleChamber R v} =
      (dominantWeights_value c : Set (Module.Dual ℂ H))

def positiveRootCone_empty_type : Prop :=
  ∀ {H : Type u} [AddCommGroup H] [Module ℂ H] {ι : Type v},
∀ [IsEmpty ι] (α : ι → Module.Dual ℂ H),
positiveRootCone_value α = ⊥

def integralWeights_empty_type : Prop :=
  ∀ {H : Type u} [AddCommGroup H] [Module ℂ H] {ι : Type v},
∀ [IsEmpty ι] (h : ι → H),
integralWeights_value h = ⊤

def dominantWeights_empty_type : Prop :=
  ∀ {H : Type u} [AddCommGroup H] [Module ℂ H] {ι : Type v},
∀ [IsEmpty ι] (h : ι → H),
dominantWeights_value h = ⊤

def weightLE_empty_type : Prop :=
  ∀ {H : Type u} [AddCommGroup H] [Module ℂ H] {ι : Type v},
∀ [IsEmpty ι] (α : ι → Module.Dual ℂ H)
    (μ χ : Module.Dual ℂ H),
weightLE_value α μ χ ↔ μ = χ

end Specs.LieAlgebrasAndRepresentations.HighestWeightData

namespace Specs.LieAlgebrasAndRepresentations.HighestWeightData

open _root_.LieAlgebrasAndRepresentations Module
open RealRootSpace RootDecomposition RootForm

universe u v

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
variable {H : LieSubalgebra ℂ L}

/-- The comparison for the simple roots of the given positive system, in any
enumeration. The complex roots are the extensions of the real simple roots,
and the Cartan elements are the Killing-normalized `h i` of the simple triples. -/
def CartanLatticeComparison (d : Realization H) : Prop :=
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  ∀ (v : E H), RootRegular (realRoots H) v →
  ∀ {ι : Type v} (s : ι ≃ simpleRoots (realRoots H) v),
    let α : ι → Module.Dual ℂ H := fun i => d.j (s i : E H)
    let h : ι → H := fun i => coroot_value H (α i)
    ∃ (b : Basis ι ℝ (E H)) (c : Basis ι ℂ H) (a : Basis ι ℂ (Module.Dual ℂ H)),
      IsSimpleBasis (realRoots H) v b ∧
      (∀ i, b i = (s i : E H) ∧ a i = α i ∧ c i = h i ∧
        α i ∈ rootSet_value H ∧ rootRestriction H (α i) = b i) ∧
      (∀ x i, d.j x (h i) = (inner ℝ x (coroot (b i)) : ℂ)) ∧
      Function.Injective d.j ∧
      (rootLattice b).map (d.j.restrictScalars ℤ) = integralRootLattice_value α ∧
      (Submodule.span ℕ (Set.range b)).map (d.j.restrictScalars ℕ) = positiveRootCone_value α ∧
      (weightLattice b).map (d.j.restrictScalars ℤ) = integralWeights_value h ∧
      d.j '' {x | x ∈ weightLattice b ∧ x ∈ closedSimpleChamber (realRoots H) v} =
        (dominantWeights_value h : Set (Module.Dual ℂ H)) ∧
      (∀ χ ∈ integralWeights_value h, ∃ x ∈ weightLattice b, d.j x = χ ∧
        ∀ u : realCartan H, χ u = (x u : ℂ)) ∧
      (∀ μ χ, weightLE_value α μ χ → weightLE_value α χ μ → μ = χ) ∧
      (IsEmpty ι ↔ rootSet_value H = ∅) ∧
      (IsEmpty ι → integralRootLattice_value α = ⊥ ∧ positiveRootCone_value α = ⊥ ∧
        integralWeights_value h = ⊥ ∧ dominantWeights_value h = ⊥)

/-- The comparison holds for the actual realized root system of every
finite-dimensional complex semisimple Lie algebra with a chosen Cartan. -/
def cartan_lattice_comparison_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra],
      ∃ d : Realization H, CartanLatticeComparison.{u, v} d

def root_set_empty_of_subsingleton_cartan_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (H : LieSubalgebra ℂ L) [Subsingleton H],
    rootSet_value H = ∅

end Specs.LieAlgebrasAndRepresentations.HighestWeightData
