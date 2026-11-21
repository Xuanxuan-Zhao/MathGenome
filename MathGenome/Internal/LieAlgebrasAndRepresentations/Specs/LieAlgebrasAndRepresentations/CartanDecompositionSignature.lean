import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.PolarRealStructures
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ReductiveDecomposition
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-! LA-J04, Lie volume, expanded lines 4747–4809. The polar bijection is
specified separately in PolarRealStructures. Here `a` is the complex-linear
extension of a compact-form involution and `ω` is its compact conjugation. -/

universe u

namespace Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature

open Complex
open LieAlgebrasAndRepresentations.RealForms
open PolarRealStructures (IsCompact involutionConjugation)
open ReductiveDecomposition (IsReductive_value)

section Objects
variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

/-- The complex fixed algebra of the extended involution. -/
def complexFixed (a : L ≃ₗ⁅ℂ⁆ L) : LieSubalgebra ℂ L where
  carrier := {x | a x = x}
  add_mem' {x y} hx hy := by
    change a x = x at hx
    change a y = y at hy
    change a (x + y) = x + y
    rw [map_add, hx, hy]
  zero_mem' := map_zero a
  smul_mem' c x hx := by
    change a x = x at hx
    change a (c • x) = c • x
    rw [map_smul, hx]
  lie_mem' {x y} hx hy := by
    change a x = x at hx
    change a y = y at hy
    change a ⁅x, y⁆ = ⁅x, y⁆
    rw [a.map_lie, hx, hy]

/-- The restriction of compact conjugation to the complex fixed algebra. -/
def fixedConjugation (ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L)
    (hcomm : Intertwines ω ω a) : Conjugation (complexFixed a) where
  map :=
    { toFun := fun x => ⟨ω.map (x : L), by
        change a (ω.map (x : L)) = ω.map (x : L)
        rw [← hcomm, show a (x : L) = (x : L) from x.property]⟩
      map_add' := fun x y => Subtype.ext (map_add ω.map (x : L) (y : L))
      map_smul' := fun r x => Subtype.ext (map_smul ω.map r (x : L))
      map_lie' := fun {x y} => Subtype.ext (ω.map.map_lie (x : L) (y : L)) }
  antilinear r x := Subtype.ext (ω.antilinear r (x : L))
  involutive x := Subtype.ext (ω.involutive (x : L))

/-- The real eigenspace of the extended involution inside the compact form,
represented as a real subspace of the ambient complex Lie algebra. -/
def compactEigenspace (ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L) (ε : ℂ) : Submodule ℝ L where
  carrier := {x | ω.map x = x ∧ a x = ε • x}
  add_mem' {x y} hx hy := by
    change ω.map x = x ∧ a x = ε • x at hx
    change ω.map y = y ∧ a y = ε • y at hy
    change ω.map (x + y) = x + y ∧ a (x + y) = ε • (x + y)
    rw [map_add, map_add, smul_add, hx.1, hy.1, hx.2, hy.2]
    exact ⟨rfl, rfl⟩
  zero_mem' := ⟨map_zero ω.map, by simp⟩
  smul_mem' r x hx := by
    change ω.map x = x ∧ a x = ε • x at hx
    refine ⟨by rw [map_smul, hx.1], ?_⟩
    change a ((r : ℂ) • x) = ε • ((r : ℂ) • x)
    rw [map_smul, hx.2, smul_comm]

def mulI : L →ₗ[ℝ] L :=
  (I • (LinearMap.id : L →ₗ[ℂ] L)).restrictScalars ℝ

/-- The compact +1 eigenspace as a subspace of the associated real form. -/
def compactPart (ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L)
    (hcomm : Intertwines ω ω a) (hinv : Function.Involutive a) :
    Submodule ℝ (involutionConjugation ω a hcomm hinv).fixed :=
  (compactEigenspace ω a 1).comap
    (involutionConjugation ω a hcomm hinv).fixed.toSubmodule.subtype

/-- The imaginary multiple of the compact −1 eigenspace inside the real form. -/
def noncompactPart (ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L)
    (hcomm : Intertwines ω ω a) (hinv : Function.Involutive a) :
    Submodule ℝ (involutionConjugation ω a hcomm hinv).fixed :=
  ((compactEigenspace ω a (-1)).map mulI).comap
    (involutionConjugation ω a hcomm hinv).fixed.toSubmodule.subtype

/-- The quadratic form of the intrinsic real Killing form. -/
noncomputable def killingQuadratic (A : Type u) [LieRing A] [LieAlgebra ℝ A] :
    QuadraticForm ℝ A :=
  (killingForm ℝ A).toQuadraticMap

noncomputable def killingSignature (A : Type u) [LieRing A] [LieAlgebra ℝ A] : ℤ :=
  (sigPos (killingQuadratic A) : ℤ) - (sigNeg (killingQuadratic A) : ℤ)

end Objects

def complexFixed_type :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L], (L ≃ₗ⁅ℂ⁆ L) → LieSubalgebra ℂ L

def fixedConjugation_type :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (ω : Conjugation L)
    (a : L ≃ₗ⁅ℂ⁆ L), Intertwines ω ω a → Conjugation (complexFixed a)

def compactEigenspace_type :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L],
    Conjugation L → (L ≃ₗ⁅ℂ⁆ L) → ℂ → Submodule ℝ L

def mulI_type :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L], L →ₗ[ℝ] L

def cartanPart_type :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (ω : Conjugation L)
    (a : L ≃ₗ⁅ℂ⁆ L) (hcomm : Intertwines ω ω a) (hinv : Function.Involutive a),
    Submodule ℝ (involutionConjugation ω a hcomm hinv).fixed

def killingQuadratic_type :=
  ∀ (A : Type u) [LieRing A] [LieAlgebra ℝ A], QuadraticForm ℝ A

def killingSignature_type :=
  ∀ (A : Type u) [LieRing A] [LieAlgebra ℝ A], ℤ

/-- The original real compact form is the direct sum of its two eigenspaces. -/
def compact_eigenspace_decomposition_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (ω : Conjugation L)
    (a : L ≃ₗ⁅ℂ⁆ L), Intertwines ω ω a → Function.Involutive a →
    Disjoint (compactEigenspace ω a 1) (compactEigenspace ω a (-1)) ∧
      compactEigenspace ω a 1 ⊔ compactEigenspace ω a (-1) = ω.fixed.toSubmodule

/-- The associated real form is the indicated embedded real direct sum. -/
def real_form_decomposition_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (ω : Conjugation L)
    (a : L ≃ₗ⁅ℂ⁆ L) (hcomm : Intertwines ω ω a) (hinv : Function.Involutive a),
    let σ := involutionConjugation ω a hcomm hinv
    IsRealForm σ.fixed ∧
      Disjoint (compactEigenspace ω a 1) ((compactEigenspace ω a (-1)).map mulI) ∧
      compactEigenspace ω a 1 ⊔ (compactEigenspace ω a (-1)).map mulI =
        σ.fixed.toSubmodule

/-- The positive-form argument applies to any finite-dimensional real Lie algebra
with such a form. -/
def reductive_of_positive_invariant_type : Prop :=
  ∀ (A : Type u) [LieRing A] [LieAlgebra ℝ A] [FiniteDimensional ℝ A]
    (B : LinearMap.BilinForm ℝ A), B.lieInvariant A →
    (∀ x : A, x ≠ 0 → 0 < B x x) → IsReductive_value ℝ A

def compact_fixed_reductive_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L) (hcomm : Intertwines ω ω a),
    IsCompact ω → IsReductive_value ℝ (fixedConjugation ω a hcomm).fixed

def complex_fixed_reductive_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L),
    Intertwines ω ω a → IsCompact ω → IsReductive_value ℂ (complexFixed a)

def cartan_killing_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L)
    (hcomm : Intertwines ω ω a) (hinv : Function.Involutive a), IsCompact ω →
    let S := (involutionConjugation ω a hcomm hinv).fixed
    let P := compactPart ω a hcomm hinv
    let N := noncompactPart ω a hcomm hinv
    (∀ x : P, (x : S) ≠ 0 → killingForm ℝ S x x < 0) ∧
    (∀ y : N, (y : S) ≠ 0 → 0 < killingForm ℝ S y y) ∧
    (∀ (x : P) (y : N), killingForm ℝ S x y = 0)

def killing_indices_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L)
    (hcomm : Intertwines ω ω a) (hinv : Function.Involutive a), IsCompact ω →
    let S := (involutionConjugation ω a hcomm hinv).fixed
    sigNeg (killingQuadratic S) = Module.finrank ℂ (complexFixed a) ∧
    sigPos (killingQuadratic S) + Module.finrank ℂ (complexFixed a) = Module.finrank ℂ L

def killing_signature_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L)
    (hcomm : Intertwines ω ω a) (hinv : Function.Involutive a), IsCompact ω →
    killingSignature (involutionConjugation ω a hcomm hinv).fixed =
      (Module.finrank ℂ L : ℤ) - 2 * (Module.finrank ℂ (complexFixed a) : ℤ)

/-- The conclusions for an involution given on the real compact form itself. -/
def compact_involution_geometry_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (ω : Conjugation L), IsCompact ω →
    ∀ (θ : ω.fixed ≃ₗ⁅ℝ⁆ ω.fixed), Function.Involutive θ →
    ∃ (a : L ≃ₗ⁅ℂ⁆ L) (hcomm : Intertwines ω ω a) (hinv : Function.Involutive a),
      let S := (involutionConjugation ω a hcomm hinv).fixed
      let Uplus := compactEigenspace ω a 1
      let Uminus := compactEigenspace ω a (-1)
      (∀ x : ω.fixed, a (x : L) = (θ x : L)) ∧ IsRealForm S ∧
        Disjoint Uplus (Uminus.map mulI) ∧ Uplus ⊔ Uminus.map mulI = S.toSubmodule ∧
        IsReductive_value ℂ (complexFixed a) ∧
        killingSignature S =
          (Module.finrank ℂ L : ℤ) - 2 * (Module.finrank ℂ (complexFixed a) : ℤ)

end Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature
