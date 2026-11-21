import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.ReducedNorm
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option linter.checkUnivs false

namespace Specs.RM03.CSA.NormOneGroup

open scoped TensorProduct

universe u v w z q
variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
  {R : Type w} [CommRing R] [Algebra k R] {ι : Type z} [Fintype ι]

/-- Evaluation of the reduced norm polynomial on a point with coefficients in a test algebra. -/
noncomputable def normAt (hA : isCentralSimple k A) (b : Module.Basis ι k A)
    (x : R ⊗[k] A) : R :=
  MvPolynomial.eval₂ (algebraMap k R) (fun i => (b.baseChange R).repr x i)
    (genericReducedNorm hA b)

/-- The equation defining the points of the norm-one group. -/
noncomputable def normOne (hA : isCentralSimple k A) (b : Module.Basis ι k A) :=
  {x : R ⊗[k] A // normAt hA b x = 1}

/-- The projective group functor has these points over a test algebra. -/
abbrev projectivePoints (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A]
    (R : Type w) [CommRing R] [Algebra k R] :=
  (R ⊗[k] A) ≃ₐ[R] (R ⊗[k] A)


open Algebra.TensorProduct CategoryTheory

variable {S : Type q} [CommRing S] [Algebra k S]
  {K : Type*} [Field K] [Algebra k K]

def NormAtType :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {R : Type w} [CommRing R] [Algebra k R] {ι : Type z} [Fintype ι],
    isCentralSimple k A → Module.Basis ι k A → (R ⊗[k] A) → R

def NormOneType :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {R : Type w} [CommRing R] [Algebra k R] {ι : Type z} [Fintype ι],
    isCentralSimple k A → Module.Basis ι k A → Type (max v w)

def ProjectivePointsType :=
  ∀ (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A]
    (R : Type w) [CommRing R] [Algebra k R], Type (max v w)

def NormBasisIndependent : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {R : Type w} [CommRing R] [Algebra k R] {ι : Type z} [Fintype ι]
    {κ : Type q} [Fintype κ] (hA : isCentralSimple k A)
    (b : Module.Basis ι k A) (c : Module.Basis κ k A) (x : R ⊗[k] A),
    normAt hA b x = normAt hA c x

def NormOneUnit : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {R : Type w} [CommRing R] [Algebra k R] {ι : Type z} [Fintype ι]
    (hA : isCentralSimple k A) (b : Module.Basis ι k A) (x : R ⊗[k] A),
    normAt hA b x = 1 → IsUnit x

/-- The scalar extension of the splitting, specified by its values on pure tensors. -/
def SplittingExtends : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {K : Type q} [Field K] [Algebra k K]
    {R : Type w} [CommRing R] [Algebra k R] [Algebra K R] [IsScalarTower k K R]
    {ι : Type z} [Fintype ι] (hA : isCentralSimple k A) (b : Module.Basis ι k A)
    (e : baseChange k K A ≃ₐ[K] Matrix (Fin (degree k A)) (Fin (degree k A)) K),
    ∃ d : R ⊗[k] A ≃ₐ[R] Matrix (Fin (degree k A)) (Fin (degree k A)) R,
      (∀ r a, d (r ⊗ₜ[k] a) = r • (e (1 ⊗ₜ[k] a)).map (algebraMap K R)) ∧
      ∀ x, normAt hA b x = (d x).det

/-- Restriction of scalars along the field extension, for describing a natural
identification of functors on the extension field's test algebras. -/
abbrev restrictTestAlgebra (k : Type u) [Field k] (K : Type q) [Field K] [Algebra k K]
    (R : CommAlgCat.{w} K) : CommAlgCat.{w} k :=
  letI : Algebra k R := ((algebraMap K R).comp (algebraMap k K)).toAlgebra
  CommAlgCat.of k R

instance restrictTestAlgebra_tower (R : CommAlgCat.{w} K) :
    IsScalarTower k K (restrictTestAlgebra k K R) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

def restrictTestMap {R S : CommAlgCat.{w} K} (f : R ⟶ S) :
    restrictTestAlgebra k K R ⟶ restrictTestAlgebra k K S :=
  letI : Algebra k R := (restrictTestAlgebra k K R).algebra
  letI : Algebra k S := (restrictTestAlgebra k K S).algebra
  letI : IsScalarTower k K R := restrictTestAlgebra_tower (k := k) R
  letI : IsScalarTower k K S := restrictTestAlgebra_tower (k := k) S
  CommAlgCat.ofHom (f.hom.restrictScalars k)

/-- The functor of points, with the inherited product and the natural
identification with the determinant-one matrices over a splitting field. -/
def NormOneFunctor : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {ι : Type z} [Fintype ι] (hA : isCentralSimple k A) (b : Module.Basis ι k A),
    ∃ (F : CommAlgCat.{w} k ⥤ GrpCat.{max v w})
      (point : ∀ R : CommAlgCat.{w} k, F.obj R ≃ normOne (R := R) hA b),
      (∀ R, (point R 1).1 = 1) ∧
      (∀ R (x y : F.obj R), (point R (x * y)).1 = (point R x).1 * (point R y).1) ∧
      (∀ {R S : CommAlgCat.{w} k} (f : R ⟶ S) (x : F.obj R),
        (point S (F.map f x)).1 =
          map f.hom (AlgHom.id k A) (point R x).1) ∧
      ∀ (K : Type q) [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
        (e : baseChange k K A ≃ₐ[K] Matrix (Fin (degree k A)) (Fin (degree k A)) K),
        ∃ (d : ∀ R : CommAlgCat.{w} K,
              (restrictTestAlgebra k K R ⊗[k] A) ≃ₐ[restrictTestAlgebra k K R]
                Matrix (Fin (degree k A)) (Fin (degree k A)) (restrictTestAlgebra k K R))
          (split : ∀ R : CommAlgCat.{w} K,
            F.obj (restrictTestAlgebra k K R) ≃*
              Matrix.SpecialLinearGroup (Fin (degree k A)) R),
          (∀ R (r : restrictTestAlgebra k K R) (a : A),
            d R (r ⊗ₜ[k] a) = r • (e (1 ⊗ₜ[k] a)).map
              (algebraMap K (restrictTestAlgebra k K R))) ∧
          (∀ R x, (split R x).1 = d R (point (restrictTestAlgebra k K R) x).1) ∧
          ∀ {R S : CommAlgCat.{w} K} (f : R ⟶ S)
            (x : F.obj (restrictTestAlgebra k K R)),
            split S (F.map (restrictTestMap (k := k) f) x) =
              Matrix.SpecialLinearGroup.map f.hom.toRingHom (split R x)

/-- The projective form is the automorphism functor, with scalar extension
specified by its intertwining property. -/
def ProjectiveFunctor : Prop :=
  ∀ (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A],
    ∃ (F : CommAlgCat.{w} k ⥤ GrpCat.{max v w})
      (point : ∀ R : CommAlgCat.{w} k, F.obj R ≃* projectivePoints k A R),
      ∀ {R S : CommAlgCat.{w} k} (f : R ⟶ S) (g : F.obj R) (x : R ⊗[k] A),
        point S (F.map f g) (map f.hom (AlgHom.id k A) x) =
          map f.hom (AlgHom.id k A) (point R g x)

def ProjectiveField : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {F : Type w} [Field F] [Algebra k F], isCentralSimple k A →
      let U := (Units.map (algebraMap F (F ⊗[k] A)).toMonoidHom).range
      ∃ (_ : U.Normal) (e : ((F ⊗[k] A)ˣ ⧸ U) ≃* projectivePoints k A F),
        ∀ (u : (F ⊗[k] A)ˣ) (x : F ⊗[k] A),
          e (QuotientGroup.mk u) x = (u : F ⊗[k] A) * x * ↑u⁻¹

/-- Splitting transports the projective functor to matrix algebra automorphisms,
with change of test algebra acting by entrywise change of matrix coefficients. -/
def ProjectiveSplit : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {K : Type q} [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (e : baseChange k K A ≃ₐ[K] Matrix (Fin (degree k A)) (Fin (degree k A)) K),
    ∃ (F : CommAlgCat.{w} k ⥤ GrpCat.{max v w})
      (point : ∀ R : CommAlgCat.{w} k, F.obj R ≃* projectivePoints k A R),
      (∀ {R S : CommAlgCat.{w} k} (f : R ⟶ S) (g : F.obj R) (x : R ⊗[k] A),
        point S (F.map f g) (map f.hom (AlgHom.id k A) x) =
          map f.hom (AlgHom.id k A) (point R g x)) ∧
      ∃ (d : ∀ R : CommAlgCat.{w} K,
            (restrictTestAlgebra k K R ⊗[k] A) ≃ₐ[restrictTestAlgebra k K R]
              Matrix (Fin (degree k A)) (Fin (degree k A)) (restrictTestAlgebra k K R))
        (split : ∀ R : CommAlgCat.{w} K,
          F.obj (restrictTestAlgebra k K R) ≃*
            (Matrix (Fin (degree k A)) (Fin (degree k A)) R ≃ₐ[R]
              Matrix (Fin (degree k A)) (Fin (degree k A)) R)),
        (∀ R (r : restrictTestAlgebra k K R) (a : A),
          d R (r ⊗ₜ[k] a) = r • (e (1 ⊗ₜ[k] a)).map
            (algebraMap K (restrictTestAlgebra k K R))) ∧
        (∀ R g x, split R g (d R x) = d R (point (restrictTestAlgebra k K R) g x)) ∧
        ∀ {R S : CommAlgCat.{w} K} (f : R ⟶ S)
          (g : F.obj (restrictTestAlgebra k K R)) (x : Matrix (Fin (degree k A)) (Fin (degree k A)) R),
          split S (F.map (restrictTestMap (k := k) f) g) (f.hom.toRingHom.mapMatrix x) =
            f.hom.toRingHom.mapMatrix (split R g x)

/-- A single matrix implements the descent on the split algebra and both groups. -/
def GroupDescent : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {K : Type q} [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {ι : Type z} [Fintype ι] (hA : isCentralSimple k A) (b : Module.Basis ι k A)
    (e : baseChange k K A ≃ₐ[K] Matrix (Fin (degree k A)) (Fin (degree k A)) K)
    (σ : K ≃ₐ[k] K),
    let τ := map σ.toAlgHom (AlgHom.id k A)
    let M := Matrix (Fin (degree k A)) (Fin (degree k A)) K
    ∃ u : Mˣ,
      let t := fun x : M => (u : M) * σ.mapMatrix x * (↑u⁻¹ : M)
      (∀ x, e (τ x) = t (e x)) ∧
      (∀ x, normAt hA b x = 1 → normAt hA b (τ x) = 1 ∧ (e x).det = 1 ∧
        (e (τ x)).det = 1) ∧
      ∀ g : projectivePoints k A K,
        ∃ d : M ≃ₐ[K] M, ∀ x, d (t (e x)) = t (e (g x))


/-- The same descent conjugation works after semilinear change of any test algebra. -/
def GroupDescentNatural : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {K : Type q} [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {R : Type w} [CommRing R] [Algebra k R] [Algebra K R] [IsScalarTower k K R]
    {S : Type*} [CommRing S] [Algebra k S] [Algebra K S] [IsScalarTower k K S]
    {ι : Type z} [Fintype ι] (hA : isCentralSimple k A) (b : Module.Basis ι k A)
    (e : baseChange k K A ≃ₐ[K] Matrix (Fin (degree k A)) (Fin (degree k A)) K)
    (σ : K ≃ₐ[k] K) (f : R →ₐ[k] S),
    (∀ c, f (algebraMap K R c) = algebraMap K S (σ c)) →
    let n := degree k A
    let τ := map f (AlgHom.id k A)
    ∃ (u : (Matrix (Fin n) (Fin n) K)ˣ)
      (dR : R ⊗[k] A ≃ₐ[R] Matrix (Fin n) (Fin n) R)
      (dS : S ⊗[k] A ≃ₐ[S] Matrix (Fin n) (Fin n) S),
      let U := Units.map (algebraMap K S).mapMatrix.toMonoidHom u
      let t := fun m : Matrix (Fin n) (Fin n) R =>
        (U : Matrix (Fin n) (Fin n) S) * f.toRingHom.mapMatrix m *
          (↑(U⁻¹) : Matrix (Fin n) (Fin n) S)
      (∀ x, e (map σ.toAlgHom (AlgHom.id k A) x) =
        (u : Matrix (Fin n) (Fin n) K) * σ.mapMatrix (e x) *
          (↑(u⁻¹) : Matrix (Fin n) (Fin n) K)) ∧
      (∀ r a, dR (r ⊗ₜ[k] a) = r • (e (1 ⊗ₜ[k] a)).map (algebraMap K R)) ∧
      (∀ s a, dS (s ⊗ₜ[k] a) = s • (e (1 ⊗ₜ[k] a)).map (algebraMap K S)) ∧
      (∀ x, normAt hA b x = 1 → dS (τ x) = t (dR x)) ∧
      ∀ g : projectivePoints k A R,
        ∃ g' : projectivePoints k A S,
          (∀ x, g' (τ x) = τ (g x)) ∧
          ∀ x, dS (g' (dS.symm (t (dR x)))) = t (dR (g x))

end Specs.RM03.CSA.NormOneGroup
