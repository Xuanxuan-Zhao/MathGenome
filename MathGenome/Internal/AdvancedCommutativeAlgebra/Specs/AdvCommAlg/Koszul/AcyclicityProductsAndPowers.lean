import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.Construction

/-! RK-15, products and powers (paper.tex:2561–2582).
Vanishing means that the canonical Koszul homology module is zero.
All modules and commutative rings, including the zero ring, are allowed.
The fixed-degree statements include both requested acyclicity conditions.
Exponents may differ at every position; exponent one leaves a position unchanged. -/
noncomputable section
universe u v
namespace Specs.AdvCommAlg.Koszul
open _root_.AdvCommAlg.Koszul

def homologyProduct : Prop := ∀ {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (pre post : List R) (a b : R) (n : ℕ),
  Subsingleton (homology M (pre ++ a :: post) (n+1)) →
  Subsingleton (homology M (pre ++ b :: post) (n+1)) →
  Subsingleton (homology M (pre ++ (a*b) :: post) (n+1))

def homologyPower : Prop := ∀ {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (pre post : List R) (a : R) (k : ℕ) (n : ℕ),
  0 < k → Subsingleton (homology M (pre ++ a :: post) (n+1)) →
  Subsingleton (homology M (pre ++ a^k :: post) (n+1))

def homologyPowers : Prop := ∀ {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (ks : List ℕ) (n : ℕ),
  x.length = ks.length → (∀ k ∈ ks, 0 < k) →
  Subsingleton (homology M x (n+1)) →
  Subsingleton (homology M (List.zipWith (fun a k => a^k) x ks) (n+1))

def degreeOneProduct : Prop := ∀ {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (pre post : List R) (a b : R),
  Subsingleton (homology M (pre ++ a :: post) 1) →
  Subsingleton (homology M (pre ++ b :: post) 1) →
  Subsingleton (homology M (pre ++ (a*b) :: post) 1)

def degreeOnePower : Prop := ∀ {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (pre post : List R) (a : R) (k : ℕ),
  0 < k → Subsingleton (homology M (pre ++ a :: post) 1) →
  Subsingleton (homology M (pre ++ a^k :: post) 1)

def degreeOnePowers : Prop := ∀ {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (ks : List ℕ),
  x.length = ks.length → (∀ k ∈ ks, 0 < k) →
  Subsingleton (homology M x 1) →
  Subsingleton (homology M (List.zipWith (fun a k => a^k) x ks) 1)

def positiveProduct : Prop := ∀ {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (pre post : List R) (a b : R),
  (∀ q : ℕ, 0 < q → Subsingleton (homology M (pre ++ a :: post) q)) →
  (∀ q : ℕ, 0 < q → Subsingleton (homology M (pre ++ b :: post) q)) →
  (∀ q : ℕ, 0 < q → Subsingleton (homology M (pre ++ (a*b) :: post) q))

def positivePower : Prop := ∀ {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (pre post : List R) (a : R) (k : ℕ),
  0 < k → (∀ q : ℕ, 0 < q → Subsingleton (homology M (pre ++ a :: post) q)) →
  (∀ q : ℕ, 0 < q → Subsingleton (homology M (pre ++ a^k :: post) q))

def positivePowers : Prop := ∀ {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (ks : List ℕ),
  x.length = ks.length → (∀ k ∈ ks, 0 < k) →
  (∀ q : ℕ, 0 < q → Subsingleton (homology M x q)) →
  (∀ q : ℕ, 0 < q → Subsingleton (homology M (List.zipWith (fun a k => a^k) x ks) q))

end Specs.AdvCommAlg.Koszul
