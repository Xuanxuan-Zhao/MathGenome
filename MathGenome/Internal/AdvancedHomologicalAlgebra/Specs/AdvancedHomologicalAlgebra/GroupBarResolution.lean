import Mathlib.RepresentationTheory.Homological.Resolution
import Mathlib.Algebra.Module.ULift

/-! Homogeneous bar resolution, HA-A02 (the resolution part).
The module in degree n has basis all (n+1)-tuples. The maps `s` and `sAug`
are only k-linear; no equivariance condition is imposed on them. -/
noncomputable section
open CategoryTheory
open scoped MonoidAlgebra

namespace GroupBar
universe u
variable (k G : Type u) [CommRing k] [Group G]

abbrev B (n : ℕ) : Rep k G := Rep.ofMulAction k G (Fin (n + 1) → G)
abbrev complex : ChainComplex (Rep k G) ℕ := Rep.standardComplex k G
abbrev boundary (n : ℕ) : B k G (n + 1) ⟶ B k G n :=
  (complex k G).d (n + 1) n
abbrev d (n : ℕ) : B k G (n + 1) →ₗ[k] B k G n :=
  (boundary k G n).hom.toLinearMap
abbrev augmentation : B k G 0 ⟶ Rep.trivial k G k := Rep.standardComplex.ε k G
abbrev ε : B k G 0 →ₗ[k] k := (augmentation k G).hom.toLinearMap

def s (n : ℕ) : B k G n →ₗ[k] B k G (n + 1) :=
  MonoidAlgebra.mapDomainLinearMap k k (fun c : Fin (n + 1) → G => Fin.cons (1 : G) c)

def sAug : k →ₗ[k] B k G 0 :=
  (LinearMap.id : k →ₗ[k] k).smulRight (MonoidAlgebra.single (fun _ : Fin 1 => (1 : G)) 1)

/-- The full resolution assertion, with explicit formulas and augmented contraction.
Exactness is stated on elements, so applies without any nontriviality assumption on k. -/
def Resolution : Prop :=
  (∀ (n : ℕ) (g : G) (c : Fin (n + 1) → G) (r : k),
    (B k G n).ρ g (MonoidAlgebra.single c r) =
      MonoidAlgebra.single (fun i => g * c i) r) ∧
  (∀ (n : ℕ) (c : Fin (n + 2) → G) (r : k),
    d k G n (MonoidAlgebra.single c r) =
      ∑ i : Fin (n + 2), MonoidAlgebra.single (c ∘ i.succAbove) (r * (-1 : k) ^ i.val)) ∧
  (∀ (c : Fin 1 → G) (r : k), ε k G (MonoidAlgebra.single c r) = r) ∧
  (∀ n, boundary k G (n + 1) ≫ boundary k G n = 0) ∧
  (boundary k G 0 ≫ augmentation k G = 0) ∧
  (∀ n, Module.Free k[G] (B k G n).ρ.asModule) ∧
  (∀ (n : ℕ) (c : Fin (n + 1) → G) (r : k),
    s k G n (MonoidAlgebra.single c r) = MonoidAlgebra.single (Fin.cons 1 c) r) ∧
  (∀ r : k, sAug k G r = MonoidAlgebra.single (fun _ : Fin 1 => (1 : G)) r) ∧
  (ε k G ∘ₗ sAug k G = LinearMap.id) ∧
  (d k G 0 ∘ₗ s k G 0 + sAug k G ∘ₗ ε k G = LinearMap.id) ∧
  (∀ n, d k G (n + 1) ∘ₗ s k G (n + 1) + s k G n ∘ₗ d k G n = LinearMap.id) ∧
  Function.Surjective (ε k G) ∧
  (∀ x : B k G 0, ε k G x = 0 ↔ ∃ y : B k G 1, d k G 0 y = x) ∧
  (∀ (n : ℕ) (x : B k G (n + 1)),
    d k G n x = 0 ↔ ∃ y : B k G (n + 2), d k G (n + 1) y = x)

/-- Closed expected type of the resolution theorem. -/
def resolutionType : Prop :=
  ∀ (k G : Type u) [CommRing k] [Group G], Resolution k G

end GroupBar

namespace GroupBar.Large
universe u v w
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

/-- The simplicial homogeneous tuples in the universe of the coefficient category. -/
def liftedCover : SimplicialObject (Action (Type (max v w)) G) where
  obj n := Action.ofMulAction G (ULift.{w} (Fin (n.unop.len + 1) → G))
  map f :=
    { hom := ↾fun x => ULift.up (x.down ∘ f.unop.toOrderHom)
      comm := fun _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev B (n : ℕ) : Rep.{max u v w} k G :=
  Rep.ofMulAction k G (ULift.{w} (Fin (n+1) → G))

abbrev single {n : ℕ} (c : Fin (n+1) → G) (r : k) : B.{u,v,w} k G n :=
  MonoidAlgebra.single (ULift.up c) r

/-- The lifted action is used only to present the original tuple basis in
the coefficient category. The base ring and the acting group are `k` and `G`. -/
abbrev complex : ChainComplex (Rep.{max u v w} k G) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex (Rep.{max u v w} k G)).obj
    (liftedCover.{v,w} G ⋙ Rep.linearization k G)

abbrev boundary (n : ℕ) : B.{u,v,w} k G (n+1) ⟶ B.{u,v,w} k G n :=
  (complex.{u,v,w} k G).d (n+1) n

abbrev d (n : ℕ) : B.{u,v,w} k G (n+1) →ₗ[k] B.{u,v,w} k G n :=
  (boundary k G n).hom.toLinearMap

abbrev trivial : Rep.{max u v w} k G := Rep.trivial k G (ULift.{max v w} k)

def ε : B.{u,v,w} k G 0 →ₗ[k] k :=
  (Finsupp.linearCombination _ fun _ ↦ (1 : k)) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

def augmentation : B.{u,v,w} k G 0 ⟶ trivial.{u,v,w} k G := Rep.ofHom
  ⟨(ULift.moduleEquiv : ULift.{max v w} k ≃ₗ[k] k).symm.toLinearMap.comp (ε k G),
    fun _ ↦ MonoidAlgebra.lhom_ext' fun _ => LinearMap.ext_ring (by simp [ε])⟩

def s (n : ℕ) : B.{u,v,w} k G n →ₗ[k] B.{u,v,w} k G (n+1) :=
  MonoidAlgebra.mapDomainLinearMap k k
    (fun c : ULift.{w} (Fin (n+1) → G) => ULift.up (Fin.cons (1 : G) c.down))

def sAug : k →ₗ[k] B.{u,v,w} k G 0 :=
  (LinearMap.id : k →ₗ[k] k).smulRight (single k G (fun _ : Fin 1 => 1) 1)

/-- Identify the lifted presentation with the original homogeneous basis. -/
def originalBasis (n : ℕ) : B.{u,v,w} k G n ≃ₗ[k] k[Fin (n+1) → G] :=
  MonoidAlgebra.mapDomainLinearEquiv k k (Equiv.ulift : ULift.{w} (Fin (n+1) → G) ≃ _)

def Resolution : Prop :=
  (∀ (n : ℕ) (c : Fin (n+1) → G) (r : k),
    originalBasis.{u,v,w} k G n (single k G c r) = MonoidAlgebra.single c r) ∧
  (∀ (n : ℕ) (g : G) (c : Fin (n+1) → G) (r : k),
    (B.{u,v,w} k G n).ρ g (single k G c r) = single k G (fun i => g * c i) r) ∧
  (∀ (n : ℕ) (c : Fin (n+2) → G) (r : k),
    d.{u,v,w} k G n (single k G c r) =
      ∑ i : Fin (n+2), single k G (c ∘ i.succAbove) (r * (-1 : k) ^ i.val)) ∧
  (∀ (c : Fin 1 → G) (r : k), ε.{u,v,w} k G (single k G c r) = r) ∧
  (∀ n, boundary.{u,v,w} k G (n+1) ≫ boundary k G n = 0) ∧
  (boundary.{u,v,w} k G 0 ≫ augmentation k G = 0) ∧
  (∀ n, Module.Free k[G] (B.{u,v,w} k G n).ρ.asModule) ∧
  (∀ (n : ℕ) (c : Fin (n+1) → G) (r : k),
    s.{u,v,w} k G n (single k G c r) = single k G (Fin.cons 1 c) r) ∧
  (∀ r : k, sAug.{u,v,w} k G r = single k G (fun _ : Fin 1 => 1) r) ∧
  (ε.{u,v,w} k G ∘ₗ sAug k G = LinearMap.id) ∧
  (d.{u,v,w} k G 0 ∘ₗ s k G 0 + sAug k G ∘ₗ ε k G = LinearMap.id) ∧
  (∀ n, d.{u,v,w} k G (n+1) ∘ₗ s k G (n+1) + s k G n ∘ₗ d k G n = LinearMap.id) ∧
  Function.Surjective (ε.{u,v,w} k G) ∧
  (∀ x : B.{u,v,w} k G 0, ε k G x = 0 ↔ ∃ y : B.{u,v,w} k G 1, d k G 0 y = x) ∧
  (∀ (n : ℕ) (x : B.{u,v,w} k G (n+1)),
    d k G n x = 0 ↔ ∃ y : B.{u,v,w} k G (n+2), d k G (n+1) y = x)

def resolutionType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G], Resolution.{u,v,w} k G

end GroupBar.Large
