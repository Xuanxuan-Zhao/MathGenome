import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Affine.LoopAlgebra
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.VermaModules

/-! The triangular summands and ordinary adjoint weights in the untwisted loop model. -/

noncomputable section

universe u

namespace Specs.RepTheorySurvey.Affine.TriangularRootSpaces

open _root_.RepTheorySurvey.Affine
open LoopAlgebra
open LieAlgebra
open _root_.Specs.LieAlgebrasAndRepresentations
open VermaModules (Direction Regular positive_value negative_value)
open RootDecomposition (rootSpace_value rootSet_value)

variable {G : Type u} [LieRing G] [LieAlgebra ℂ G]

/-- The homogeneous coefficients followed by the central and degree coordinates. -/
def coordinates (B : InvariantForm G) :
    AffineAlgebra B ≃ₗ[ℂ] ((ℤ →₀ G) × ℂ) × ℂ :=
  (affineCoordinates_value B).trans
    (((LieAlgebra.LoopAlgebra.toFinsupp ℂ ℤ G).prodCongr
      (LinearEquiv.refl ℂ ℂ)).prodCongr (LinearEquiv.refl ℂ ℂ))

def homogeneousLinear (B : InvariantForm G) (m : ℤ) : G →ₗ[ℂ] AffineAlgebra B :=
  (loopIncl_value B).comp (loopVector_value m)

def components (B : InvariantForm G) (P : ℤ → Submodule ℂ G)
    (C D : Submodule ℂ ℂ) : Submodule ℂ (AffineAlgebra B) where
  carrier := {x | (∀ m, (coordinates B x).1.1 m ∈ P m) ∧
    (coordinates B x).1.2 ∈ C ∧ (coordinates B x).2 ∈ D}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hx, hc, hd⟩ ⟨hy, hc', hd'⟩
    exact ⟨fun m => by simpa using (P m).add_mem (hx m) (hy m),
      by simpa using C.add_mem hc hc', by simpa using D.add_mem hd hd'⟩
  smul_mem' := by
    rintro a x ⟨hx, hc, hd⟩
    exact ⟨fun m => by simpa using (P m).smul_mem a (hx m),
      by simpa using C.smul_mem a hc, by simpa using D.smul_mem a hd⟩

def cartanDegrees (H : LieSubalgebra ℂ G) (m : ℤ) : Submodule ℂ G :=
  if m = 0 then H.toSubmodule else ⊥

def sideDegrees (N : LieSubalgebra ℂ G) (s : ℤ) (m : ℤ) : Submodule ℂ G :=
  if m = 0 then N.toSubmodule else if 0 < s * m then ⊤ else ⊥

def affineCartan_value (B : InvariantForm G) (H : LieSubalgebra ℂ G) :
    Submodule ℂ (AffineAlgebra B) :=
  components B (cartanDegrees H) ⊤ ⊤

def affinePositive_value (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    (φ : Direction H) : Submodule ℂ (AffineAlgebra B) :=
  components B (sideDegrees (positive_value H φ) 1) ⊥ ⊥

def affineNegative_value (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    (φ : Direction H) : Submodule ℂ (AffineAlgebra B) :=
  components B (sideDegrees (negative_value H φ) (-1)) ⊥ ⊥

def affineCartan_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G], (B : InvariantForm G) →
    LieSubalgebra ℂ G → Submodule ℂ (AffineAlgebra B)

def affinePositive_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G], (B : InvariantForm G) →
    (H : LieSubalgebra ℂ G) → Direction H → Submodule ℂ (AffineAlgebra B)

def affineNegative_type := affinePositive_type.{u}

def cartanProjection (B : InvariantForm G) (H : LieSubalgebra ℂ G) :
    affineCartan_value B H →ₗ[ℂ] H :=
  (((Finsupp.lapply 0).comp (LinearMap.fst ℂ (ℤ →₀ G) ℂ)).comp
    ((LinearMap.fst ℂ ((ℤ →₀ G) × ℂ) ℂ).comp
      ((coordinates B).toLinearMap.comp (affineCartan_value B H).subtype))).codRestrict
    H.toSubmodule (fun h => by simpa [cartanDegrees] using h.property.1 (0 : ℤ))

def delta_value (B : InvariantForm G) (H : LieSubalgebra ℂ G) :
    Module.Dual ℂ (affineCartan_value B H) :=
  (LinearMap.snd ℂ ((ℤ →₀ G) × ℂ) ℂ).comp
    ((coordinates B).toLinearMap.comp (affineCartan_value B H).subtype)

def extendFiniteRoot_value (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    (α : Module.Dual ℂ H) : Module.Dual ℂ (affineCartan_value B H) :=
  α.comp (cartanProjection B H)

def delta_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G)
    (H : LieSubalgebra ℂ G), Module.Dual ℂ (affineCartan_value B H)

def extendFiniteRoot_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G)
    (H : LieSubalgebra ℂ G), Module.Dual ℂ H → Module.Dual ℂ (affineCartan_value B H)

def IsAdjointWeightVector (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    (χ : Module.Dual ℂ (affineCartan_value B H)) (x : AffineAlgebra B) : Prop :=
  ∀ h : affineCartan_value B H, affineBracket_value B (h : AffineAlgebra B) x = χ h • x

private theorem affineBracket_add_right (B : InvariantForm G) (h x y : AffineAlgebra B) :
    affineBracket_value B h (x + y) = affineBracket_value B h x + affineBracket_value B h y := by
  let p : LoopCentral B × ℂ := h
  let q : LoopCentral B × ℂ := x
  let r : LoopCentral B × ℂ := y
  change (⁅p.1, q.1 + r.1⁆ + p.2 • degreeCentral_value B (q.1 + r.1) -
    (q.2 + r.2) • degreeCentral_value B p.1, (0 : ℂ)) =
    ((⁅p.1, q.1⁆ + p.2 • degreeCentral_value B q.1 - q.2 • degreeCentral_value B p.1) +
      (⁅p.1, r.1⁆ + p.2 • degreeCentral_value B r.1 - r.2 • degreeCentral_value B p.1),
      0 + 0)
  simp only [lie_add, map_add, smul_add, add_smul, add_zero]
  congr 1
  abel

private theorem affineBracket_smul_right (B : InvariantForm G) (h x : AffineAlgebra B) (a : ℂ) :
    affineBracket_value B h (a • x) = a • affineBracket_value B h x := by
  let p : LoopCentral B × ℂ := h
  let q : LoopCentral B × ℂ := x
  change (⁅p.1, a • q.1⁆ + p.2 • degreeCentral_value B (a • q.1) -
    (a * q.2) • degreeCentral_value B p.1, (0 : ℂ)) =
    (a • (⁅p.1, q.1⁆ + p.2 • degreeCentral_value B q.1 - q.2 • degreeCentral_value B p.1),
      a * 0)
  simp only [lie_smul, map_smul, smul_sub, smul_add, mul_zero, smul_smul, mul_comm]

/-- The ordinary simultaneous eigenspace for the specified affine bracket. -/
def affineWeightSpace_value (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    (χ : Module.Dual ℂ (affineCartan_value B H)) : Submodule ℂ (AffineAlgebra B) where
  carrier := {x | IsAdjointWeightVector B H χ x}
  zero_mem' := by
    intro h
    change affineBracket_value B (h : AffineAlgebra B) 0 = χ h • (0 : AffineAlgebra B)
    simpa only [zero_smul, smul_zero] using affineBracket_smul_right B h 0 0
  add_mem' := by
    intro x y hx hy h
    rw [affineBracket_add_right, hx h, hy h, smul_add]
  smul_mem' := by
    intro a x hx h
    rw [affineBracket_smul_right, hx h, smul_comm a (χ h)]

def affineWeightSpace_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G)
    (H : LieSubalgebra ℂ G), Module.Dual ℂ (affineCartan_value B H) → Submodule ℂ (AffineAlgebra B)

open scoped Classical in
def adjointWeightDecomposition_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G] [H.IsCartanSubalgebra],
    DirectSum.IsInternal (affineWeightSpace_value B H)

def triangularDecomposition_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G)
    [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G] (H : LieSubalgebra ℂ G)
    [H.IsCartanSubalgebra] (φ : Direction H), Regular H φ →
    IsCompl (affineNegative_value B H φ) (affineCartan_value B H ⊔ affinePositive_value B H φ) ∧
      Disjoint (affineCartan_value B H) (affinePositive_value B H φ)

def cartanAbelianBracket_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G] [H.IsCartanSubalgebra] (x y : affineCartan_value B H),
    affineBracket_value B (x : AffineAlgebra B) (y : AffineAlgebra B) = 0

def ClosedUnderBracket (B : InvariantForm G) (P : Submodule ℂ (AffineAlgebra B)) : Prop :=
  ∀ ⦃x y⦄, x ∈ P → y ∈ P → affineBracket_value B x y ∈ P

def sidesClosed_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G)
    (H : LieSubalgebra ℂ G) (φ : Direction H),
    ClosedUnderBracket B (affinePositive_value B H φ) ∧
      ClosedUnderBracket B (affineNegative_value B H φ)

def zeroWeightSpace_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G] [H.IsCartanSubalgebra] (x : AffineAlgebra B),
    IsAdjointWeightVector B H 0 x ↔ x ∈ affineCartan_value B H

def realWeightSpace_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G] [H.IsCartanSubalgebra] (α : rootSet_value H) (m : ℤ),
    (∀ x, IsAdjointWeightVector B H (extendFiniteRoot_value B H α.val +
      (m : ℂ) • delta_value B H) x ↔
      x ∈ (rootSpace_value H α.val).map (homogeneousLinear B m)) ∧
    Module.finrank ℂ ((rootSpace_value H α.val).map (homogeneousLinear B m)) = 1

def imaginaryWeightSpace_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G] [H.IsCartanSubalgebra] (m : ℤ), m ≠ 0 →
    (∀ x, IsAdjointWeightVector B H ((m : ℂ) • delta_value B H) x ↔
      x ∈ H.toSubmodule.map (homogeneousLinear B m)) ∧
    Module.finrank ℂ (H.toSubmodule.map (homogeneousLinear B m)) = Module.finrank ℂ H

def nonzeroWeights_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G] [H.IsCartanSubalgebra] (χ : Module.Dual ℂ (affineCartan_value B H)),
    (χ ≠ 0 ∧ ∃ x : AffineAlgebra B, x ≠ 0 ∧ IsAdjointWeightVector B H χ x) ↔
      (∃ (α : rootSet_value H) (m : ℤ),
        χ = extendFiniteRoot_value B H α.val + (m : ℂ) • delta_value B H) ∨
      (∃ m : ℤ, m ≠ 0 ∧ χ = (m : ℂ) • delta_value B H)

end Specs.RepTheorySurvey.Affine.TriangularRootSpaces
