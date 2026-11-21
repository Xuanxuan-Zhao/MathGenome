import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.PolarsBipolar
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Independent statements for paper.tex §v01-10. The index types may be empty.
The tangent uses positive real times and sequences, as in the manuscript. -/
open Set Filter
open scoped Topology
noncomputable section
universe u v w
namespace VariationalNotes.ConvexGeometry.Specs

def contingentTangent {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (x : E) : Set E :=
  {v | ∃ (z : ℕ → E) (t : ℕ → ℝ),
    (∀ k, z k ∈ C) ∧ (∀ k, 0 < t k) ∧
    Tendsto t atTop (𝓝 0) ∧
    Tendsto (fun k => (t k)⁻¹ • (z k - x)) atTop (𝓝 v)}

def contingentTangentType : Type (u+1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E], Set E → E → Set E

def polyhedralSet {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {I : Type v} {J : Type w} (a : I → E) (b : I → ℝ) (e : J → E) (d : J → ℝ) : Set E :=
  {y | (∀ i, inner ℝ (a i) y ≤ b i) ∧ (∀ j, inner ℝ (e j) y = d j)}

def polyhedralSetType : Type (max u v w + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {I : Type v} {J : Type w}, (I → E) → (I → ℝ) → (J → E) → (J → ℝ) → Set E

def convex_normal_tangent_polar : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (x : E), Convex ℝ C → x ∈ C →
    normalCone C x = negativePolar (contingentTangent C x)

def polyhedral_tangent : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (a : I → E) (b : I → ℝ) (e : J → E) (d : J → ℝ) (x : E),
    x ∈ polyhedralSet a b e d →
    contingentTangent (polyhedralSet a b e d) x =
      {v | (∀ i, inner ℝ (a i) x = b i → inner ℝ (a i) v ≤ 0) ∧
        (∀ j, inner ℝ (e j) v = 0)}

/-- The vector normal is the inverse image of the canonical continuous-dual
normal under the Riesz linear isometry, not a separately chosen convention. -/
def polyhedral_normal : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (a : I → E) (b : I → ℝ) (e : J → E) (d : J → ℝ) (x : E),
    x ∈ polyhedralSet a b e d →
    (InnerProductSpace.toDual ℝ E) ⁻¹' normalCone (polyhedralSet a b e d) x =
      {z | ∃ (lam : {i // inner ℝ (a i) x = b i} → ℝ) (nu : J → ℝ),
        (∀ i, 0 ≤ lam i) ∧
        z = (∑ i, lam i • a i.val) + ∑ j, nu j • e j}

def polyhedral_normal_polar : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (a : I → E) (b : I → ℝ) (e : J → E) (d : J → ℝ) (x : E),
    x ∈ polyhedralSet a b e d →
    normalCone (polyhedralSet a b e d) x =
      negativePolar (contingentTangent (polyhedralSet a b e d) x)

/-- The same formula stated directly in the continuous dual. -/
def polyhedral_dual_normal : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (a : I → E) (b : I → ℝ) (e : J → E) (d : J → ℝ) (x : E),
    x ∈ polyhedralSet a b e d →
    normalCone (polyhedralSet a b e d) x =
      (InnerProductSpace.toDual ℝ E) ''
        {z | ∃ (lam : {i // inner ℝ (a i) x = b i} → ℝ) (nu : J → ℝ),
          (∀ i, 0 ≤ lam i) ∧
          z = (∑ i, lam i • a i.val) + ∑ j, nu j • e j}

end VariationalNotes.ConvexGeometry.Specs
