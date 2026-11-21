import MathGenome.Internal.FourVolumeAlgebra.Specs.Shared.Lie.UniversalEnveloping
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-! Independent objects and full statements for HA-A06, source lines 3112–3183.
The tensor factor carries the left regular U-action. Indices in Lean start at
zero. In the bracket sum the original removed positions are `i.castSucc` and
`j.succ`, with `i ≤ j`; thus its sign is `(-1)^(i+j+1)`. The second removal is
made after the first, so the unused entries keep their original order.
No PBW, exactness, rank bound, or characteristic assumption occurs here. -/

namespace AdvancedHomologicalAlgebra.CE

open scoped TensorProduct
universe u v w
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]

abbrev U := Shared.Lie.U k g
abbrev W (n : ℕ) := ⋀[k]^n g
abbrev V (n : ℕ) := U k g ⊗[k] W k g n
abbrev wedge (n : ℕ) := exteriorPower.ιMulti k n (M := g)
abbrev BoundaryFamily := ∀ n : ℕ, V k g (n+1) →ₗ[U k g] V k g n

/-- The single-removal part of the printed boundary. -/
def actionSum (n : ℕ) (a : U k g) (x : Fin (n+1) → g) : V k g n :=
  ∑ i : Fin (n+1), (-1 : ℤ) ^ (i : ℕ) •
    ((a * Shared.Lie.inclusion k g (x i)) ⊗ₜ[k] wedge k g n (i.removeNth x))

/-- The bracket part is zero on degree one; the other cases enumerate
all pairs of original positions exactly once. -/
def bracketSum : ∀ n : ℕ, U k g → (Fin (n+1) → g) → V k g n
  | 0, _, _ => 0
  | n+1, a, x =>
    ∑ i : Fin (n+1), ∑ j ∈ Finset.Ici i, (-1 : ℤ) ^ ((i : ℕ) + (j : ℕ) + 1) •
      (a ⊗ₜ[k] wedge k g (n+1)
        (Fin.cons ⁅x i.castSucc, x j.succ⁆ (j.removeNth (i.castSucc.removeNth x))))

/-- This is a formula for actual U-linear maps on the original tensor
products, not an assumption that an unproved formula descends. -/
def HasBoundaryFormula (d : BoundaryFamily k g) : Prop :=
  ∀ n a x, d n (a ⊗ₜ[k] wedge k g (n+1) x) =
    actionSum k g n a x + bracketSum k g n a x

/-- Agreement on pure tensors with exterior generators determines the
boundary, even when a proof uses a separately constructed formula model. -/
theorem boundaryFormula_unique {d e : BoundaryFamily k g}
    (hd : HasBoundaryFormula k g d) (he : HasBoundaryFormula k g e) : d = e := by
  funext n
  suffices h : (d n).restrictScalars k = (e n).restrictScalars k from
    LinearMap.ext fun z => LinearMap.congr_fun h z
  apply TensorProduct.ext'
  intro a z
  let f := ((d n).restrictScalars k).comp (TensorProduct.mk k (U k g) (W k g (n+1)) a)
  let f' := ((e n).restrictScalars k).comp (TensorProduct.mk k (U k g) (W k g (n+1)) a)
  have h : f = f' := exteriorPower.linearMap_ext <| AlternatingMap.ext fun x => by
    change d n (a ⊗ₜ[k] wedge k g (n+1) x) = e n (a ⊗ₜ[k] wedge k g (n+1) x)
    rw [hd, he]
  exact LinearMap.congr_fun h z

/-- The augmentation of V₀, using Λ⁰g ≃ k. -/
noncomputable def augmentation : V k g 0 →ₗ[k] k :=
  TensorProduct.lift
    { toFun := fun a => (Shared.Lie.augmentation k g a) •
        (exteriorPower.zeroEquiv k g).toLinearMap
      map_add' := by intros; simp only [map_add, add_smul]
      map_smul' := by intros; simp only [map_smul, smul_assoc, RingHom.id_apply] }

/-- The full printed boundary as an alternating map, including repeated-input
vanishing without a characteristic restriction. -/
def HasAlternatingBoundary : Prop :=
  ∀ n a, ∃ b : g [⋀^Fin (n+1)]→ₗ[k] V k g n,
    ∀ x, b x = actionSum k g n a x + bracketSum k g n a x

/-- Square zero and the actual augmented U-action compatibility. -/
def IsAugmentedComplex (d : BoundaryFamily k g) : Prop :=
  (∀ n, (d n).comp (d (n+1)) = 0) ∧
  (∀ z : V k g 1, augmentation k g (d 0 z) = 0) ∧
  (∀ (a : U k g) (z : V k g 0),
    augmentation k g (a • z) = Shared.Lie.augmentation k g a * augmentation k g z)

/-- The boundary exported to downstream modules, together with its defining
formula and all augmented complex laws. -/
structure BoundaryData where
  differential : BoundaryFamily k g
  formula : HasBoundaryFormula k g differential
  augmented : IsAugmentedComplex k g differential

variable (M : Type w) [AddCommGroup M] [Module k M]
  [Module (U k g) M] [IsScalarTower k (U k g) M]

/-- No signed internal-Hom convention: the resolution cochain differential
is exactly precomposition, as in the source. -/
def homCoboundary (d : BoundaryFamily k g) (n : ℕ)
    (F : V k g n →ₗ[U k g] M) : V k g (n+1) →ₗ[U k g] M :=
  F.comp (d n)

/-- The action term of the displayed coboundary. -/
def cochainActionSum (n : ℕ) (f : W k g n →ₗ[k] M) (x : Fin (n+1) → g) : M :=
  ∑ i : Fin (n+1), (-1 : ℤ) ^ (i : ℕ) •
    (Shared.Lie.inclusion k g (x i) • f (wedge k g n (i.removeNth x)))

/-- The bracket term of the displayed coboundary. -/
def cochainBracketSum : ∀ n : ℕ, (W k g n →ₗ[k] M) → (Fin (n+1) → g) → M
  | 0, _, _ => 0
  | n+1, f, x =>
    ∑ i : Fin (n+1), ∑ j ∈ Finset.Ici i, (-1 : ℤ) ^ ((i : ℕ) + (j : ℕ) + 1) •
      f (wedge k g (n+1)
        (Fin.cons ⁅x i.castSucc, x j.succ⁆ (j.removeNth (i.castSucc.removeNth x))))

/-- The actual evaluation comparison and its transported differential for
the supplied exterior boundary. -/
structure CochainData (d : BoundaryFamily k g) where
  evaluation : ∀ n, (V k g n →ₗ[U k g] M) ≃ₗ[k] (W k g n →ₗ[k] M)
  differential : ∀ n, (W k g n →ₗ[k] M) →ₗ[k] (W k g (n+1) →ₗ[k] M)
  evaluate_tmul : ∀ n F z, evaluation n F z = F ((1 : U k g) ⊗ₜ[k] z)
  inverse_tmul : ∀ n f a z, (evaluation n).symm f (a ⊗ₜ[k] z) = a • f z
  compatible : ∀ n F, differential n (evaluation n F) =
    evaluation (n+1) (homCoboundary k g M d n F)
  squared : ∀ n, (differential (n+1)).comp (differential n) = 0
  formula : ∀ n f x, differential n f (wedge k g (n+1) x) =
    cochainActionSum k g M n f x + cochainBracketSum k g M n f x

end AdvancedHomologicalAlgebra.CE

namespace Specs.AdvancedHomologicalAlgebra.CE
open _root_.AdvancedHomologicalAlgebra.CE
open scoped TensorProduct
universe u v w w'

/-- A named, formula-checked operation on the original exterior tensors. -/
abbrev boundaryDataExpected :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    [Module.Free k g], BoundaryData k g

/-- A named differential and evaluation comparison for any genuine CE boundary. -/
abbrev cochainDataExpected :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (M : Type w) [AddCommGroup M] [Module k M] [Module (U k g) M]
    [IsScalarTower k (U k g) M] (D : BoundaryData k g),
    CochainData k g M D.differential

/-- Complete chain construction, including well-definedness in every
characteristic (the alternating map), square zero, and augmentation. -/
def complexExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    [Module.Free k g],
    HasAlternatingBoundary k g ∧
    ∃ d : BoundaryFamily k g, HasBoundaryFormula k g d ∧ IsAugmentedComplex k g d

/-- The degreewise comparison and its inverse. This is valid without
freeness of g; naturality is specified separately below. -/
def comparisonExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (M : Type w) [AddCommGroup M] [Module k M] [Module (U k g) M]
    [IsScalarTower k (U k g) M] (n : ℕ),
    ∃ e : (V k g n →ₗ[U k g] M) ≃ₗ[k] (W k g n →ₗ[k] M),
      (∀ F z, e F z = F ((1 : U k g) ⊗ₜ[k] z)) ∧
      (∀ f a z, e.symm f (a ⊗ₜ[k] z) = a • f z)

/-- Full cochain assertion for any boundary family satisfying the explicit
formula. This conditional statement does not supply the boundary's existence;
that is the separate `complexExpected` obligation. -/
def cochainExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (M : Type w) [AddCommGroup M] [Module k M] [Module (U k g) M]
    [IsScalarTower k (U k g) M] (d : BoundaryFamily k g),
    HasBoundaryFormula k g d → IsAugmentedComplex k g d →
    ∃ (e : ∀ n, (V k g n →ₗ[U k g] M) ≃ₗ[k] (W k g n →ₗ[k] M))
      (δ : ∀ n, (W k g n →ₗ[k] M) →ₗ[k] (W k g (n+1) →ₗ[k] M)),
      (∀ n F z, e n F z = F ((1 : U k g) ⊗ₜ[k] z)) ∧
      (∀ n f a z, (e n).symm f (a ⊗ₜ[k] z) = a • f z) ∧
      (∀ n F, δ n (e n F) = e (n+1) (homCoboundary k g M d n F)) ∧
      (∀ n, (δ (n+1)).comp (δ n) = 0) ∧
      (∀ n f x, δ n f (wedge k g (n+1) x) =
        cochainActionSum k g M n f x + cochainBracketSum k g M n f x)

/-- Evaluation determines the comparison, naturally in every actual
U-linear coefficient map; identities and composition are included. -/
def naturalityExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (M : Type w) [AddCommGroup M] [Module k M] [Module (U k g) M]
    [IsScalarTower k (U k g) M]
    (N : Type w') [AddCommGroup N] [Module k N] [Module (U k g) N]
    [IsScalarTower k (U k g) N] (n : ℕ)
    (eM : (V k g n →ₗ[U k g] M) ≃ₗ[k] (W k g n →ₗ[k] M))
    (eN : (V k g n →ₗ[U k g] N) ≃ₗ[k] (W k g n →ₗ[k] N)),
    (∀ F z, eM F z = F ((1 : U k g) ⊗ₜ[k] z)) →
    (∀ F z, eN F z = F ((1 : U k g) ⊗ₜ[k] z)) →
    ∀ (h : M →ₗ[U k g] N) (F : V k g n →ₗ[U k g] M),
      eN (h.comp F) = (h.restrictScalars k).comp (eM F)

/-- Useful independently checked progress on the multiplication part. -/
def actionAlternatingExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (n : ℕ) (a : U k g), ∃ b : g [⋀^Fin (n+1)]→ₗ[k] V k g n,
    ∀ x, b x = actionSum k g n a x

/-- Augmentation compatibility is a completed component, without any
assumed square-zero or existence certificate. -/
def augmentationExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (d : BoundaryFamily k g), HasBoundaryFormula k g d →
      (∀ z : V k g 1, augmentation k g (d 0 z) = 0) ∧
      (∀ (a : U k g) (z : V k g 0),
        augmentation k g (a • z) = Shared.Lie.augmentation k g a * augmentation k g z)

/-- Only the square V₂ → V₀. The all-degree square is still required by
`complexExpected`; this partial statement does not replace it. -/
def squareTwoExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (d : BoundaryFamily k g), HasBoundaryFormula k g d → (d 0).comp (d 1) = 0

end Specs.AdvancedHomologicalAlgebra.CE
