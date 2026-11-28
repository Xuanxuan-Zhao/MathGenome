import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Affine.AffineSimpleTriples

/-! Proposition LO10 for the untwisted affine Lie algebra. -/

noncomputable section

universe u

namespace Specs.RepTheorySurvey.Affine.AffineTriangularDecomposition

open _root_.RepTheorySurvey.Affine
open _root_.LieAlgebrasAndRepresentations.HighestRoot (simpleRoots)
open _root_.Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSet_value rootSpace_value)
open _root_.Specs.LieAlgebrasAndRepresentations.VermaModules (Direction Regular)
open LoopAlgebra TriangularRootSpaces
open scoped Classical

variable {G : Type u} [LieRing G] [LieAlgebra ℂ G]

/-- The ordered triangular summands, adjoint weights, and simple triples of the loop model. -/
structure Conclusion [FiniteDimensional ℂ G] (B : InvariantForm G)
    (H : LieSubalgebra ℂ G) (φ : Direction H) : Prop where
  decomposition :
    IsCompl (affineNegative_value B H φ) (affineCartan_value B H ⊔ affinePositive_value B H φ)
  cartan_positive_disjoint :
    Disjoint (affineCartan_value B H) (affinePositive_value B H φ)
  cartan_abelian : ∀ x y : affineCartan_value B H,
    affineBracket_value B (x : AffineAlgebra B) (y : AffineAlgebra B) = 0
  positive_closed : ClosedUnderBracket B (affinePositive_value B H φ)
  negative_closed : ClosedUnderBracket B (affineNegative_value B H φ)
  cartan_weight_values :
    ∃ (ι : H →ₗ[ℂ] affineCartan_value B H) (k t : affineCartan_value B H),
      (∀ h : H, (ι h : AffineAlgebra B) = homogeneous_value B 0 (h : G)) ∧
        (k : AffineAlgebra B) = K_value B ∧ (t : AffineAlgebra B) = d_value B ∧
        (∀ h : H, delta_value B H (ι h) = 0) ∧
        delta_value B H k = 0 ∧ delta_value B H t = 1 ∧
        ∀ α : Module.Dual ℂ H,
          (∀ h : H, extendFiniteRoot_value B H α (ι h) = α h) ∧
          extendFiniteRoot_value B H α k = 0 ∧ extendFiniteRoot_value B H α t = 0
  adjoint_decomposition : DirectSum.IsInternal (affineWeightSpace_value B H)
  zero_weight : affineWeightSpace_value B H 0 = affineCartan_value B H
  nonzero_weights : ∀ χ : Module.Dual ℂ (affineCartan_value B H),
    (χ ≠ 0 ∧ affineWeightSpace_value B H χ ≠ ⊥) ↔
      (∃ (α : rootSet_value H) (m : ℤ),
        χ = extendFiniteRoot_value B H α.val + (m : ℂ) • delta_value B H) ∨
      (∃ m : ℤ, m ≠ 0 ∧ χ = (m : ℂ) • delta_value B H)
  real_root_spaces : ∀ (α : rootSet_value H) (m : ℤ),
    let χ := extendFiniteRoot_value B H α.val + (m : ℂ) • delta_value B H
    affineWeightSpace_value B H χ = (rootSpace_value H α.val).map (homogeneousLinear B m) ∧
      Module.finrank ℂ (affineWeightSpace_value B H χ) = 1
  imaginary_root_spaces : ∀ (m : ℤ), m ≠ 0 →
    let χ := (m : ℂ) • delta_value B H
    affineWeightSpace_value B H χ = H.toSubmodule.map (homogeneousLinear B m) ∧
      Module.finrank ℂ (affineWeightSpace_value B H χ) = Module.finrank ℂ H
  highest_root : ∃! θ, IsHighestFiniteRoot H φ θ
  triple_choices : ∀ θ : Module.Dual ℂ H, IsHighestFiniteRoot H φ θ →
    Nonempty (FiniteRootTriple H θ × (∀ i : simpleRoots H φ, FiniteRootTriple H i.val))
  /-- The index `none` is the affine triple formed from the highest finite root. -/
  simple_triples : ∀ (θ : Module.Dual ℂ H), IsHighestFiniteRoot H φ θ →
    ∀ (T : FiniteRootTriple H θ) (S : ∀ i : simpleRoots H φ, FiniteRootTriple H i.val),
      (∀ i : AffineSimpleIndex H φ,
        let α := affineSimpleRoot B H θ i
        let h := affineSimpleH B H θ i
        let e := affineSimpleE B T S i
        let f := affineSimpleF B T S i
        h ∈ affineCartan_value B H ∧ α ≠ 0 ∧
          e ∈ affineWeightSpace_value B H α ∧ f ∈ affineWeightSpace_value B H (-α) ∧
          h ≠ 0 ∧ affineBracket_value B e f = h ∧
          affineBracket_value B h e = (2 : ℂ) • e ∧
          affineBracket_value B h f = (-2 : ℂ) • f) ∧
      (∀ i j : AffineSimpleIndex H φ, i ≠ j →
        affineBracket_value B (affineSimpleE B T S i) (affineSimpleF B T S j) = 0) ∧
      affineLieSpan B (Set.range (affineSimpleE B T S)) = affinePositive_value B H φ ∧
      affineLieSpan B (Set.range (affineSimpleF B T S)) = affineNegative_value B H φ

def affineTriangularDecomposition_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [H.IsCartanSubalgebra] (φ : Direction H), B.IsNormalized H → Regular H φ → Conclusion B H φ

end Specs.RepTheorySurvey.Affine.AffineTriangularDecomposition
