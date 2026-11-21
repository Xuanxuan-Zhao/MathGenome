import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.HorseshoeCoding
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add

/-! Independent full scope of paper.tex, Theorem d13:17:affine-horseshoe.
All orbits use the actual domain of the local strip map at every integer time.
The derivative is that of the prescribed affine branch, including at its boundary.
-/
namespace Specs.D13Unified.Ch17.AffineHorseshoe
open Set
open ShiftSpaces HorseshoeCoding
noncomputable section

abbrev Plane := ℝ × ℝ

def horizontalStrip (r : ℝ) (a : Binary) : Set Plane :=
  if a = 0 then Icc 0 1 ×ˢ Icc 0 r else Icc 0 1 ×ˢ Icc (1-r) 1

abbrev verticalDomain (r : ℝ) : Set Plane := verticalStrip r 0 ∪ verticalStrip r 1
abbrev horizontalDomain (r : ℝ) : Set Plane := horizontalStrip r 0 ∪ horizontalStrip r 1

def unitSquare : Set Plane := Icc 0 1 ×ˢ Icc 0 1

def invariantSet (r : ℝ) : Set Plane := CantorGeometry.cantorSet r ×ˢ CantorGeometry.cantorSet r

/-- An orbit for the partial map, not an orbit for an extension across the gap. -/
def fullOrbitSet (r : ℝ) : Set Plane :=
  {p | ∃ z : ℤ → Plane, z 0 = p ∧ ∀ n : ℤ,
    z n ∈ unitSquare ∧ ∃ hd : z n ∈ verticalDomain r,
      stripMap r ⟨z n, hd⟩ = z (n+1)}

/-- diag(r⁻¹,r) as a continuous real linear map in the standard coordinates. -/
def diagonal (r : ℝ) : Plane →L[ℝ] Plane :=
  ((r⁻¹ : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (r • ContinuousLinearMap.snd ℝ ℝ ℝ)

def horizontalStripType := ℝ → Binary → Set Plane
abbrev verticalDomainType := ℝ → Set Plane
abbrev horizontalDomainType := ℝ → Set Plane
def unitSquareType := Set Plane
def invariantSetType := ℝ → Set Plane
def fullOrbitSetType := ℝ → Set Plane
def diagonalType := ℝ → Plane →L[ℝ] Plane

def strip_homeomorphStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 →
    ∃ h : verticalDomain r ≃ₜ horizontalDomain r,
      ∀ p, (h p).val = stripMap r p

def strip_imagesStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → ∀ a : Binary,
    affineBranch r a '' verticalStrip r a = horizontalStrip r a

def strips_disjointStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 →
    Disjoint (verticalStrip r 0) (verticalStrip r 1) ∧
    Disjoint (horizontalStrip r 0) (horizontalStrip r 1)

def maximal_full_orbitStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → fullOrbitSet r = invariantSet r

/-- The digit-series homeomorphism, with a genuine self-map on C_r × C_r
whose values are those of the local map. No value over the middle gap is used. -/
def restriction_conjugacyStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 →
    ∃ h : TwoSided ≃ₜ (CantorGeometry.cantorSet r × CantorGeometry.cantorSet r),
    ∃ F : (CantorGeometry.cantorSet r × CantorGeometry.cantorSet r) →
      (CantorGeometry.cantorSet r × CantorGeometry.cantorSet r),
      (∀ s, ((h s).1.val, (h s).2.val) = coding r s) ∧
      (∀ p : (CantorGeometry.cantorSet r × CantorGeometry.cantorSet r),
        ∃ hd : (p.1.val, p.2.val) ∈ verticalDomain r,
        stripMap r ⟨(p.1.val, p.2.val), hd⟩ = ((F p).1.val, (F p).2.val)) ∧
      Function.Semiconj h shift F

def branch_derivativeStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 → ∀ a : Binary, ∀ p : Plane,
    HasFDerivAt (affineBranch r a) (diagonal r) p

def expansion_contractionStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1/2 →
    1 < r⁻¹ ∧ 0 < r ∧ r < 1 ∧
    (∀ v : ℝ, diagonal r (v,0) = (r⁻¹*v,0) ∧
      ‖diagonal r (v,0)‖ = r⁻¹ * ‖(v, (0:ℝ))‖) ∧
    (∀ v : ℝ, diagonal r (0,v) = (0,r*v) ∧
      ‖diagonal r (0,v)‖ = r * ‖((0:ℝ),v)‖)

end
end Specs.D13Unified.Ch17.AffineHorseshoe
