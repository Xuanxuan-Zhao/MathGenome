import Mathlib.LinearAlgebra.Quotient.Basic

namespace RepTheorySurvey.Geometric.ConvolutionBundleBaseChangeSpecs

/-- The constant coefficient lies in (S) and the linear coefficient is taken modulo (S). -/
def quotientCoefficients {R A : Type*} [Ring R] [AddCommGroup A] [Module R A]
    (S : Submodule R A) :
    (S.prod (⊤ : Submodule R A)) →ₗ[R] S × (A ⧸ S) where
  toFun v := (⟨v.val.1, (Submodule.mem_prod.mp v.property).1⟩, S.mkQ v.val.2)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/-- Both incidence inclusions and the coefficient quotient commute with change of base
using the spans of the coefficient images. -/
def AffineBaseChange : Prop :=
  ∀ {R T A D : Type*} [CommRing R] [CommRing T]
    [AddCommGroup A] [AddCommGroup D] [Module R A] [Module T D]
    (a : R →+* T) (c : A →ₛₗ[a] D)
    (S : Submodule R A) (P : Submodule R (A × A)),
    (⊥ : Submodule R A).prod S ≤ P → P ≤ S.prod ⊤ →
    let S' := Submodule.span T (c '' (S : Set A))
    let P' := Submodule.span T (Prod.map c c '' (P : Set (A × A)))
    let B := (P.comap (S.prod ⊤).subtype).map (quotientCoefficients S)
    (⊥ : Submodule T D).prod S' ≤ P' ∧
    P' ≤ S'.prod ⊤ ∧
    (P'.comap (S'.prod ⊤).subtype).map (quotientCoefficients S') =
      Submodule.span T {z |
        ∃ (x : S) (y : A), (x, S.mkQ y) ∈ B ∧
          ∃ hx : c x.val ∈ S', z = (⟨c x.val, hx⟩, S'.mkQ (c y))}

end RepTheorySurvey.Geometric.ConvolutionBundleBaseChangeSpecs
