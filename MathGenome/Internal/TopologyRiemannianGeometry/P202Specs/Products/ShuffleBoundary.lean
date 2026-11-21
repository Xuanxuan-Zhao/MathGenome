import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.ShuffleModel

/-! The boundary obligation for the prescribed finite signed shuffle.  These
propositions use only the accepted canonical objects, without a certificate
that the shuffle is already a chain map. -/
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace P202Specs.ShuffleBoundary
open P202Specs.SingularChains P202Specs.AlexanderWhitney P202Specs.ShuffleModel
universe u w

def chain_identity_type : Prop := ∀ (R : Type u) [CommRing R]
    (X Y : TopCat.{w}) (n : ℕ),
  (boundary R R (productSpace X Y) n).comp (shuffle R X Y (n+1)) =
    (shuffle R X Y n).comp (totalBoundary R X Y n)

/-- The source complex is exactly the accepted ordinary tensor complex. -/
def chain_map_realization_type : Prop := ∀ (R : Type u) [CommRing R]
    (X Y : TopCat.{w}),
  ∃ F : tensorComplex R X Y ⟶ complex R R (productSpace X Y),
    ∀ n, F.f n = ModuleCat.ofHom (shuffle R X Y n)

def sign_eq_inversions_type : Prop := ∀ {p q : ℕ} (s : LatticePath p q),
  s.sign = (-1 : ℤ) ^
    (Finset.univ.filter (fun ij : Fin (p+q) × Fin (p+q) =>
      ij.1 < ij.2 ∧ s.stepLabel ij.2 < s.stepLabel ij.1)).card

def sign_delete_type : Prop := ∀ {n : ℕ} (σ : Equiv.Perm (Fin (n+1)))
    (τ : Equiv.Perm (Fin n)) (i j : Fin (n+1)),
    σ i = j → (∀ a, σ (i.succAbove a) = j.succAbove (τ a)) →
    (Equiv.Perm.sign σ : ℤ) = (-1 : ℤ)^(i.val+j.val) * (Equiv.Perm.sign τ : ℤ)

def sign_delete_boundary_type : Prop := ∀ {n : ℕ} (σ : Equiv.Perm (Fin (n+1)))
    (τ : Equiv.Perm (Fin n)) (i j : Fin (n+1)),
    σ i = j → (∀ a, σ (i.succAbove a) = j.succAbove (τ a)) →
    (-1 : ℤ)^i.val * (Equiv.Perm.sign σ : ℤ) =
      (-1 : ℤ)^j.val * (Equiv.Perm.sign τ : ℤ)

def chain_identity_on_zero_left_type : Prop := ∀ (R : Type u) [CommRing R]
    (X Y : TopCat.{w}) (σ : Simplex X 0) (n : ℕ) (c : Chains R Y (n+1)),
    boundary R R (productSpace X Y) n
      (shuffle R X Y (n+1) (Pi.single (⟨(0,n+1), by omega⟩ : Diagonal (n+1))
        (Finsupp.single σ (1:R) ⊗ₜ[R] c))) =
    shuffle R X Y n (totalBoundary R X Y n
      (Pi.single (⟨(0,n+1), by omega⟩ : Diagonal (n+1))
        (Finsupp.single σ (1:R) ⊗ₜ[R] c)))

def chain_identity_on_zero_right_type : Prop := ∀ (R : Type u) [CommRing R]
    (X Y : TopCat.{w}) (τ : Simplex Y 0) (n : ℕ) (c : Chains R X (n+1)),
    boundary R R (productSpace X Y) n
      (shuffle R X Y (n+1) (Pi.single (⟨(n+1,0), by omega⟩ : Diagonal (n+1))
        (c ⊗ₜ[R] Finsupp.single τ (1:R)))) =
    shuffle R X Y n (totalBoundary R X Y n
      (Pi.single (⟨(n+1,0), by omega⟩ : Diagonal (n+1))
        (c ⊗ₜ[R] Finsupp.single τ (1:R))))

def chain_identity_degree_one_type : Prop := ∀ (R : Type u) [CommRing R]
    (X Y : TopCat.{w}),
    (boundary R R (productSpace X Y) 0).comp (shuffle R X Y 1) =
      (shuffle R X Y 0).comp (totalBoundary R X Y 0)

def ordinary_boundary_zero_type : Prop := ∀ (R : Type u) [CommRing R]
    (X Y : TopCat.{w}) (n : ℕ),
    (tensorComplex R X Y).d 0 n = 0 ∧ (complex R R (productSpace X Y)).d 0 n = 0

end P202Specs.ShuffleBoundary
