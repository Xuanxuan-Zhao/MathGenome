import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.Degree
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Quaternion

namespace LinearAlgebraicGroups.Arithmetic.LocalQuadraticSplitting

open _root_.Specs.RM03.CSA

universe u v w

/-- Every separable quadratic field splits a degree-two central simple algebra
over a nonarchimedean local field, including in characteristic two. -/
def QuadraticSplitting : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {A : Type v} [Ring A] [Algebra F A]
    {E : Type w} [Field E] [Algebra F E] [Algebra.IsSeparable F E],
    isCentralSimple F A → degree F A = 2 → Module.finrank F E = 2 →
      Nonempty (baseChange F E A ≃ₐ[E] Matrix (Fin 2) (Fin 2) E)

/-- Every separable quadratic field embeds in each local division algebra of degree two. -/
def QuadraticEmbedding : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {B : Type v} [DivisionRing B] [Algebra F B]
    {E : Type w} [Field E] [Algebra F E] [Algebra.IsSeparable F E],
    isCentralDivision F B → degree F B = 2 → Module.finrank F E = 2 →
      Nonempty (E →ₐ[F] B)

/-- A finite splitting field of a quaternion division algebra has even degree,
over any base field. In degree two it embeds into the division algebra. -/
def SplittingDegree : Prop :=
  ∀ {F : Type u} [Field F] {B : Type v} [DivisionRing B] [Algebra F B]
    {E : Type w} [Field E] [Algebra F E] [Module.Finite F E],
    isCentralDivision F B → degree F B = 2 → splits F E B →
      2 ∣ Module.finrank F E ∧ (Module.finrank F E = 2 → Nonempty (E →ₐ[F] B))

/-- Extending scalars by any odd finite degree preserves the division property. -/
def OddExtensionDivision : Prop :=
  ∀ {F : Type u} [Field F] {B : Type v} [DivisionRing B] [Algebra F B]
    {E : Type w} [Field E] [Algebra F E] [Module.Finite F E],
    isCentralDivision F B → degree F B = 2 → Odd (Module.finrank F E) →
      Nontrivial (baseChange F E B) ∧ ∀ x : baseChange F E B, x ≠ 0 → IsUnit x

/-- Every nonarchimedean local field admits a central division algebra of degree two. -/
def LocalDivisionExists : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F],
    ∃ (B : Type u) (_ : DivisionRing B) (_ : Algebra F B),
      isCentralDivision F B ∧ degree F B = 2

/-- Two central quaternion division algebras over the same nonarchimedean
local field are isomorphic over that field. -/
def LocalDivisionUnique : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {B : Type v} [DivisionRing B] [Algebra F B]
    {D : Type w} [DivisionRing D] [Algebra F D],
    isCentralDivision F B → degree F B = 2 →
    isCentralDivision F D → degree F D = 2 → Nonempty (B ≃ₐ[F] D)

/-- Complexification splits every real central simple algebra of degree two. -/
def ComplexSplitting : Prop :=
  ∀ {A : Type v} [Ring A] [Algebra ℝ A],
    isCentralSimple ℝ A → degree ℝ A = 2 →
      Nonempty (baseChange ℝ ℂ A ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)

/-- A real central quaternion division algebra is Hamilton's algebra, contains
a maximal complex subfield, and splits over the complex numbers. -/
def RealDivision : Prop :=
  ∀ {B : Type v} [DivisionRing B] [Algebra ℝ B],
    isCentralDivision ℝ B → degree ℝ B = 2 →
      Nonempty (B ≃ₐ[ℝ] Quaternion ℝ) ∧
      (∃ i : ℂ →ₐ[ℝ] B, Subalgebra.centralizer ℝ (Set.range i) = i.range) ∧
      Nonempty (baseChange ℝ ℂ B ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)

end LinearAlgebraicGroups.Arithmetic.LocalQuadraticSplitting
