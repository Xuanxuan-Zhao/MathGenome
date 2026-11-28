import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! The coordinate Heisenberg algebra and the normalized cochain in Proposition LD01. -/

universe u v

namespace Specs.LieNotes.Heisenberg

/-- The ordered coordinates are those of x, y and z. The separate carrier
allows the Heisenberg bracket on this vector space. -/
@[ext] structure ModelValue (k : Type u) where
  coords : Fin 3 → k

variable (k : Type u) [Field k]

private def coordsEquiv : ModelValue k ≃ (Fin 3 → k) where
  toFun := ModelValue.coords
  invFun := ModelValue.mk

instance : AddCommGroup (ModelValue k) := (coordsEquiv k).addCommGroup

private def coordsAddEquiv : ModelValue k ≃+ (Fin 3 → k) where
  __ := coordsEquiv k
  map_add' _ _ := rfl

instance : Module k (ModelValue k) := (coordsAddEquiv k).module k

def coordinatesValue : ModelValue k ≃ₗ[k] (Fin 3 → k) := (coordsAddEquiv k).linearEquiv k

noncomputable def basisValue : Module.Basis (Fin 3) k (ModelValue k) :=
  Module.Basis.ofEquivFun (coordinatesValue k)

def xValue : ModelValue k := ⟨Pi.single 0 1⟩
def yValue : ModelValue k := ⟨Pi.single 1 1⟩
def zValue : ModelValue k := ⟨Pi.single 2 1⟩

def bracketValue (p q : ModelValue k) : ModelValue k :=
  (p.coords 0 * q.coords 1 - p.coords 1 * q.coords 0) • zValue k

private theorem bracket_coords (p q : ModelValue k) (i : Fin 3) :
    (bracketValue k p q).coords i =
      (p.coords 0 * q.coords 1 - p.coords 1 * q.coords 0) * (Pi.single 2 1 : Fin 3 → k) i :=
  rfl

@[simp] theorem coords_zero (i : Fin 3) : (0 : ModelValue k).coords i = 0 := rfl

@[simp] theorem coords_add (p q : ModelValue k) (i : Fin 3) :
    (p + q).coords i = p.coords i + q.coords i := rfl

@[simp] theorem coords_smul (r : k) (p : ModelValue k) (i : Fin 3) :
    (r • p).coords i = r * p.coords i := rfl

instance lieRingValue : LieRing (ModelValue k) where
  bracket := bracketValue k
  add_lie p q r := by
    apply ModelValue.ext
    funext i
    simp only [bracket_coords, coords_add]
    ring
  lie_add p q r := by
    apply ModelValue.ext
    funext i
    simp only [bracket_coords, coords_add]
    ring
  lie_self p := by
    change bracketValue k p p = 0
    simp [bracketValue, mul_comm]
  leibniz_lie p q r := by
    change bracketValue k p (bracketValue k q r) =
      bracketValue k (bracketValue k p q) r + bracketValue k q (bracketValue k p r)
    simp [bracketValue, zValue]

instance lieAlgebraValue : LieAlgebra k (ModelValue k) where
  lie_smul a p q := by
    apply ModelValue.ext
    funext i
    change (bracketValue k p (a • q)).coords i = (a • bracketValue k p q).coords i
    simp only [bracket_coords, coords_smul]
    ring

def centerLineValue : Submodule k (ModelValue k) := k ∙ zValue k

private theorem basis_coords (i j : Fin 3) :
    (basisValue k i).coords j = (Pi.single i 1 : Fin 3 → k) j := by
  rw [basisValue, Module.Basis.coe_ofEquivFun]
  rfl

private theorem basis_bracket_table :
    ⁅basisValue k 0, basisValue k 1⁆ = basisValue k 2 ∧
    ⁅basisValue k 0, basisValue k 2⁆ = 0 ∧
    ⁅basisValue k 1, basisValue k 2⁆ = 0 := by
  have hz : basisValue k 2 = zValue k := by
    apply ModelValue.ext
    funext i
    exact basis_coords k 2 i
  change bracketValue k (basisValue k 0) (basisValue k 1) = basisValue k 2 ∧
    bracketValue k (basisValue k 0) (basisValue k 2) = 0 ∧
    bracketValue k (basisValue k 1) (basisValue k 2) = 0
  simp [bracketValue, basis_coords, hz, zValue]

section Identification

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k} {L : Type v} [LieRing L] [LieAlgebra k L]

/-- The Lie equivalence given by sending the coordinate basis to a basis with
the Heisenberg bracket table. -/
noncomputable def basisLieEquivValue (b : Module.Basis (Fin 3) k L)
    (hxy : ⁅b 0, b 1⁆ = b 2) (hxz : ⁅b 0, b 2⁆ = 0) (hyz : ⁅b 1, b 2⁆ = 0) :
    ModelValue k ≃ₗ⁅k⁆ L := by
  let E := (basisValue k).equiv b (Equiv.refl _)
  have hE (i : Fin 3) : E (basisValue k i) = b i := by simp [E]
  let A := (LieAlgebra.ad k (ModelValue k)).toLinearMap.compr₂ E.toLinearMap
  let B := (LieAlgebra.ad k L).toLinearMap.compl₁₂ E.toLinearMap E.toLinearMap
  have H : A = B := by
    apply LinearMap.ext_basis (basisValue k) (basisValue k)
    intro i j
    change E ⁅basisValue k i, basisValue k j⁆ = ⁅E (basisValue k i), E (basisValue k j)⁆
    rw [hE, hE]
    obtain ⟨mxy, mxz, myz⟩ := basis_bracket_table k
    have myx := lie_skew (basisValue k 1) (basisValue k 0)
    have mzx := lie_skew (basisValue k 2) (basisValue k 0)
    have mzy := lie_skew (basisValue k 2) (basisValue k 1)
    have hyx := lie_skew (b 1) (b 0)
    have hzx := lie_skew (b 2) (b 0)
    have hzy := lie_skew (b 2) (b 1)
    fin_cases i <;> fin_cases j <;>
      simp [mxy, mxz, myz, ← myx, ← mzx, ← mzy, hxy, hxz, hyz, ← hyx, ← hzx, ← hzy, hE]
  refine { E with map_lie' := ?_ }
  intro p q
  exact DFunLike.congr_fun (DFunLike.congr_fun H p) q

end Identification

private def minor (i j : Fin 3) (p q : ModelValue k) : k :=
  p.coords i * q.coords j - p.coords j * q.coords i

private def phiFormula (a b c d e : k) (p q : ModelValue k) : ModelValue k :=
  minor k 0 2 p q • (a • xValue k + b • yValue k + c • zValue k) +
  minor k 1 2 p q • (d • xValue k - a • yValue k + e • zValue k)

private def phiBilinear (a b c d e : k) : ModelValue k →ₗ[k] ModelValue k →ₗ[k] ModelValue k :=
  LinearMap.mk₂ k (phiFormula k a b c d e)
    (fun p q r => by
      apply ModelValue.ext
      funext i
      simp only [phiFormula, minor, coords_add, coords_smul]
      ring)
    (fun s p q => by
      apply ModelValue.ext
      funext i
      simp only [phiFormula, minor, coords_add, coords_smul]
      ring)
    (fun p q r => by
      apply ModelValue.ext
      funext i
      simp only [phiFormula, minor, coords_add, coords_smul]
      ring)
    (fun s p q => by
      apply ModelValue.ext
      funext i
      simp only [phiFormula, minor, coords_add, coords_smul]
      ring)

private def asMultilinear
    (f : ModelValue k →ₗ[k] ModelValue k →ₗ[k] ModelValue k) :
    MultilinearMap k (fun _ : Fin 2 => ModelValue k) (ModelValue k) :=
  ((MultilinearMap.ofSubsingletonₗ k k (ModelValue k) (ModelValue k) (0 : Fin 1)).toLinearMap.comp
    f).uncurryLeft

/-- The only contributions to the normalized cochain are the xz and yz minors. -/
def phiValue (a b c d e : k) : ModelValue k [⋀^Fin 2]→ₗ[k] ModelValue k where
  toMultilinearMap := asMultilinear k (phiBilinear k a b c d e)
  map_eq_zero_of_eq' m i j h hij := by
    have h01 : m 0 = m 1 := by
      fin_cases i <;> fin_cases j <;> simp_all
    change phiFormula k a b c d e (m 0) (m 1) = 0
    simp [h01, phiFormula, minor, mul_comm]

theorem phiValue_apply (a b c d e : k) (p q : ModelValue k) :
    phiValue k a b c d e ![p, q] =
      (p.coords 0 * q.coords 2 - p.coords 2 * q.coords 0) •
        (a • xValue k + b • yValue k + c • zValue k) +
      (p.coords 1 * q.coords 2 - p.coords 2 * q.coords 1) •
        (d • xValue k - a • yValue k + e • zValue k) :=
  rfl

noncomputable def phiExteriorValue (a b c d e : k) : (⋀[k]^2 (ModelValue k)) →ₗ[k] ModelValue k :=
  exteriorPower.alternatingMapLinearEquiv (phiValue k a b c d e)

def ModelType := Type u → Type u
def modelValue (k : Type u) : Type u := ModelValue k
def coordinatesType := ∀ (k : Type u) [Field k], ModelValue k ≃ₗ[k] (Fin 3 → k)
def basisType := ∀ (k : Type u) [Field k], Module.Basis (Fin 3) k (ModelValue k)
def vectorType := ∀ (k : Type u) [Field k], ModelValue k
def lieRingType := ∀ (k : Type u) [Field k], LieRing (ModelValue k)
def lieAlgebraType := ∀ (k : Type u) [Field k], LieAlgebra k (ModelValue k)
def centerLineType := ∀ (k : Type u) [Field k], Submodule k (ModelValue k)
def phiType := ∀ (k : Type u) [Field k], k → k → k → k → k →
  ModelValue k [⋀^Fin 2]→ₗ[k] ModelValue k
def phiExteriorType := ∀ (k : Type u) [Field k], k → k → k → k → k →
  (⋀[k]^2 (ModelValue k)) →ₗ[k] ModelValue k

set_option linter.checkUnivs false in
def basisLieEquivType := ∀ {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L]
    (b : Module.Basis (Fin 3) k L),
  ⁅b 0, b 1⁆ = b 2 → ⁅b 0, b 2⁆ = 0 → ⁅b 1, b 2⁆ = 0 → ModelValue k ≃ₗ⁅k⁆ L

def dimensionType : Prop := ∀ (k : Type u) [Field k], Module.finrank k (ModelValue k) = 3

def basisVectorsType : Prop := ∀ (k : Type u) [Field k],
  basisValue k 0 = xValue k ∧ basisValue k 1 = yValue k ∧ basisValue k 2 = zValue k

def bracketFormulaType : Prop := ∀ (k : Type u) [Field k] (p q : ModelValue k),
  ⁅p, q⁆ = (p.coords 0 * q.coords 1 - p.coords 1 * q.coords 0) • zValue k

def bracketTableType : Prop := ∀ (k : Type u) [Field k],
  ⁅xValue k, yValue k⁆ = zValue k ∧ ∀ p : ModelValue k, ⁅p, zValue k⁆ = 0

def centerType : Prop := ∀ (k : Type u) [Field k],
  (LieAlgebra.center k (ModelValue k)).toSubmodule = centerLineValue k

def bracketImageType : Prop := ∀ (k : Type u) [Field k] (r : ModelValue k),
  (∃ p q : ModelValue k, ⁅p, q⁆ = r) ↔ r ∈ centerLineValue k

def basisLieEquivApplyType : Prop :=
  ∀ {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L]
    (b : Module.Basis (Fin 3) k L) (hxy : ⁅b 0, b 1⁆ = b 2)
    (hxz : ⁅b 0, b 2⁆ = 0) (hyz : ⁅b 1, b 2⁆ = 0) (i : Fin 3),
  basisLieEquivValue b hxy hxz hyz (basisValue k i) = b i

def phiPairsType : Prop := ∀ (k : Type u) [Field k] (a b c d e : k),
  phiValue k a b c d e ![xValue k, yValue k] = 0 ∧
  phiValue k a b c d e ![xValue k, zValue k] = a • xValue k + b • yValue k + c • zValue k ∧
  phiValue k a b c d e ![yValue k, zValue k] = d • xValue k - a • yValue k + e • zValue k

def phiExteriorApplyType : Prop := ∀ (k : Type u) [Field k] (a b c d e : k) (p q : ModelValue k),
  phiExteriorValue k a b c d e (exteriorPower.ιMulti k 2 ![p, q]) = phiValue k a b c d e ![p, q]

end Specs.LieNotes.Heisenberg
