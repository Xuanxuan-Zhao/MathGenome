import MathGenome.Internal.Specs.D05.M15.TopPairing
import MathGenome.Internal.Specs.D05.M15.InteriorProduct.Higher
import MathGenome.Internal.Specs.D05.M07.Biddual

/-! Volume duality, paper.tex:3163–3172. All contractions are the existing
reversed-composition contraction. Primal contraction acts on the dual space
through the canonical evaluation map, not an arbitrarily chosen self-duality.
The maps are defined on the exterior algebra; their restrictions to complementary
homogeneous degrees, including degree zero, are specified below. A basis of
`Fin n` expresses the hypothesis `dim V = n`. No characteristic restriction is used.
-/
noncomputable section
namespace Specs.D05.M15.TopPairing.VolumeDuality
universe u v w

abbrev D_type := {K : Type u} → {V : Type v} → [Field K] →
  [AddCommGroup V] → [Module K V] →
  _root_.ExteriorAlgebra K (Module.Dual K V) →
  (_root_.ExteriorAlgebra K V →ₗ[K] _root_.ExteriorAlgebra K (Module.Dual K V))

def D_value : D_type := fun {K V} _ _ _ ωstar =>
  ((InteriorProduct.Higher.contraction_value K (Module.Dual K V)).flip ωstar).comp
    (_root_.ExteriorAlgebra.map (Module.Dual.eval K V)).toLinearMap

abbrev E_type := {K : Type u} → {V : Type v} → [Field K] →
  [AddCommGroup V] → [Module K V] → _root_.ExteriorAlgebra K V →
  (_root_.ExteriorAlgebra K (Module.Dual K V) →ₗ[K] _root_.ExteriorAlgebra K V)

def E_value : E_type := fun {K V} _ _ _ ω =>
  (InteriorProduct.Higher.contraction_value K V).flip ω

section
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

def D_degree : Prop := ∀ (p q n : ℕ) (h : p + q = n)
  (ωstar : ⋀[K]^n (Module.Dual K V)) (x : ⋀[K]^p V),
  D_value (ωstar : _root_.ExteriorAlgebra K (Module.Dual K V)) x ∈ ⋀[K]^q (Module.Dual K V)

def E_degree : Prop := ∀ (p q n : ℕ) (h : p + q = n)
  (ω : ⋀[K]^n V) (α : ⋀[K]^p (Module.Dual K V)),
  E_value (ω : _root_.ExteriorAlgebra K V) α ∈ ⋀[K]^q V

/-- Pairing characterizations of the actual contractions. -/
def D_pairing : Prop := ∀ (p q : ℕ) (ωstar : ⋀[K]^(p+q) (Module.Dual K V))
  (x : ⋀[K]^p V) (y : ⋀[K]^q V)
  (z : ⋀[K]^q (Module.Dual K V)),
  (z : _root_.ExteriorAlgebra K (Module.Dual K V)) = D_value ωstar x →
  exteriorPower.pairingDual K V q z y =
    exteriorPower.pairingDual K V (p+q) ωstar (exteriorPower.wedge K V p q x y)

def E_pairing : Prop := ∀ (p q : ℕ) (ω : ⋀[K]^(p+q) V)
  (α : ⋀[K]^p (Module.Dual K V)) (β : ⋀[K]^q (Module.Dual K V))
  (z : ⋀[K]^q V),
  (z : _root_.ExteriorAlgebra K V) = E_value ω α →
  exteriorPower.pairingDual K V q β z =
    exteriorPower.pairingDual K V (p+q)
      (exteriorPower.wedge K (Module.Dual K V) p q α β) ω

/-- The signs sort the increasing list I followed by its increasing complement. -/
def basis_D : Prop := ∀ {n : ℕ} (b : Module.Basis (Fin n) K V)
  (p q : ℕ) (h : p + q = n) (I : Set.powersetCard (Fin n) p),
  D_value (DeterminantLine.volume b.dualBasis) (ExteriorBasis.increasingWedge b p I) =
    Set.powersetCard.sign I •
      (ExteriorBasis.increasingWedge b.dualBasis q
        (Set.powersetCard.compl (by simpa [Nat.add_comm] using h) I) :
          _root_.ExteriorAlgebra K (Module.Dual K V))

def basis_E : Prop := ∀ {n : ℕ} (b : Module.Basis (Fin n) K V)
  (p q : ℕ) (h : p + q = n) (I : Set.powersetCard (Fin n) p),
  E_value (DeterminantLine.volume b) (ExteriorBasis.increasingWedge b.dualBasis p I) =
    Set.powersetCard.sign I •
      (ExteriorBasis.increasingWedge b q
        (Set.powersetCard.compl (by simpa [Nat.add_comm] using h) I) : _root_.ExteriorAlgebra K V)

/-- These statements quantify arbitrary normalized nonzero volume choices. -/
def signed_ED : Prop := ∀ {n : ℕ} (b : Module.Basis (Fin n) K V)
  (p q : ℕ) (h : p + q = n) (ω : ⋀[K]^n V)
  (ωstar : ⋀[K]^n (Module.Dual K V)),
  exteriorPower.pairingDual K V n ωstar ω = 1 → ∀ x : ⋀[K]^p V,
  E_value ω (D_value ωstar x) = (-1 : K)^(p*q) • (x : _root_.ExteriorAlgebra K V)

def signed_DE : Prop := ∀ {n : ℕ} (b : Module.Basis (Fin n) K V)
  (p q : ℕ) (h : p + q = n) (ω : ⋀[K]^n V)
  (ωstar : ⋀[K]^n (Module.Dual K V)),
  exteriorPower.pairingDual K V n ωstar ω = 1 → ∀ α : ⋀[K]^p (Module.Dual K V),
  D_value ωstar (E_value ω α) =
    (-1 : K)^(p*q) • (α : _root_.ExteriorAlgebra K (Module.Dual K V))

def degree_zero_D : Prop := ∀ ωstar : _root_.ExteriorAlgebra K (Module.Dual K V),
  D_value ωstar 1 = ωstar

def degree_zero_E : Prop := ∀ ω : _root_.ExteriorAlgebra K V, E_value ω 1 = ω

def identifications : Prop := ∀ {n : ℕ} (b : Module.Basis (Fin n) K V)
  (p q : ℕ) (h : p + q = n) (ω : ⋀[K]^n V)
  (ωstar : ⋀[K]^n (Module.Dual K V)),
  exteriorPower.pairingDual K V n ωstar ω = 1 →
  (∃ d : (⋀[K]^p V) ≃ₗ[K] (⋀[K]^q (Module.Dual K V)), ∀ x,
    (d x : _root_.ExteriorAlgebra K (Module.Dual K V)) = D_value ωstar x) ∧
  (∃ e : (⋀[K]^p (Module.Dual K V)) ≃ₗ[K] (⋀[K]^q V), ∀ α,
    (e α : _root_.ExteriorAlgebra K V) = E_value ω α)

/-- Dual top volumes are uniquely determined, including n = 0. -/
def dual_volume_exists : Prop := ∀ {n : ℕ} (b : Module.Basis (Fin n) K V)
  (ω : ⋀[K]^n V), ω ≠ 0 → ∃! ωstar : ⋀[K]^n (Module.Dual K V),
    exteriorPower.pairingDual K V n ωstar ω = 1

end

def naturality : Prop := ∀ {K : Type u} {V : Type v} {W : Type w} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {n : ℕ} (b : Module.Basis (Fin n) K V) (g : V ≃ₗ[K] W)
  (p q : ℕ) (h : p + q = n) (ω : ⋀[K]^n V)
  (ωstar : ⋀[K]^n (Module.Dual K V))
  (ηstar : ⋀[K]^n (Module.Dual K W)),
  exteriorPower.pairingDual K V n ωstar ω = 1 →
  exteriorPower.pairingDual K W n ηstar (exteriorPower.map n g.toLinearMap ω) = 1 →
  ∀ x : ⋀[K]^p V,
    D_value ηstar (exteriorPower.map p g.toLinearMap x) =
      _root_.ExteriorAlgebra.map g.symm.toLinearMap.dualMap (D_value ωstar x)

/-- Closed proposition types for the universally quantified theorem bindings. -/
def D_degree_statement : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
    D_degree (K := K) (V := V)

def E_degree_statement : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
    E_degree (K := K) (V := V)

def D_pairing_statement : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
    D_pairing (K := K) (V := V)

def E_pairing_statement : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
    E_pairing (K := K) (V := V)

def basis_D_statement : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
    basis_D (K := K) (V := V)

def basis_E_statement : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
    basis_E (K := K) (V := V)

def signed_ED_statement : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
    signed_ED (K := K) (V := V)

def signed_DE_statement : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
    signed_DE (K := K) (V := V)

def degree_zero_D_statement : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
    degree_zero_D (K := K) (V := V)

def degree_zero_E_statement : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
    degree_zero_E (K := K) (V := V)

def identifications_statement : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
    identifications (K := K) (V := V)

def dual_volume_exists_statement : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
    dual_volume_exists (K := K) (V := V)

end Specs.D05.M15.TopPairing.VolumeDuality
