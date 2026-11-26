import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.HomogeneousQuotient
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.NonabelianCohomology
import Mathlib.LinearAlgebra.Matrix.Reindex
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.ProjectiveClassification

open AlgebraicGeometry CategoryTheory
open scoped MatrixGroups TensorProduct CategoryTheory.MonObj

namespace LinearAlgebraicGroups.Descent.MatrixAlgebraForms

universe u w
set_option maxHeartbeats 1000000

open Matrix RM03.Brauer
open RM03.Brauer.ProjectiveClassification (Mat Form Isomorphic SplitClasses Implements IsTransport)
open RM03.Brauer.SemilinearDescent (AlgebraAction)


variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- Coefficientwise Galois action on the abstract scalar quotient. -/
def projectiveAction (n : ℕ) : Gal(K/k) →* MulAut PGL(n, K) where
  toFun σ :=
    { toFun := ProjectiveClassification.projectiveAction k K n σ
      invFun := ProjectiveClassification.projectiveAction k K n σ⁻¹
      left_inv := fun p => by
        change (ProjGenLinGroup.map (σ⁻¹).toRingHom) (ProjGenLinGroup.map σ.toRingHom p) = _
        rw [← MonoidHom.comp_apply, ← ProjGenLinGroup.map_comp]
        have h : (σ⁻¹).toRingHom.comp σ.toRingHom = RingHom.id K :=
          RingHom.ext σ.symm_apply_apply
        rw [h, ProjGenLinGroup.map_id]
        rfl
      right_inv := fun p => by
        change (ProjGenLinGroup.map σ.toRingHom) (ProjGenLinGroup.map (σ⁻¹).toRingHom p) = _
        rw [← MonoidHom.comp_apply, ← ProjGenLinGroup.map_comp]
        have h : σ.toRingHom.comp (σ⁻¹).toRingHom = RingHom.id K :=
          RingHom.ext σ.apply_symm_apply
        rw [h, ProjGenLinGroup.map_id]
        rfl
      map_mul' := map_mul _ }
  map_one' := MulEquiv.ext fun p =>
    DFunLike.congr_fun ProjGenLinGroup.map_id p
  map_mul' σ τ := MulEquiv.ext fun p =>
    DFunLike.congr_fun (ProjGenLinGroup.map_comp τ.toRingHom σ.toRingHom) p

/-- The usual conjugation action on matrix-algebra automorphisms. -/
def ConjugationIdentification : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] {n : ℕ}, 0 < n →
    ∃ e : PGL(n, K) ≃* (Mat K n ≃ₐ[K] Mat K n),
      (∀ (G : GL (Fin n) K) (x : Mat K n),
        e (ProjGenLinGroup.mk G) x = (G : Mat K n) * x * (↑G⁻¹ : Mat K n)) ∧
      (∀ (σ : Gal(K/k)) (p : PGL(n, K)) (x : Mat K n),
        (e p x).map σ = e (projectiveAction n σ p) (x.map σ))

/-- A presentation of the projective linear group as the fppf quotient by scalar matrices. -/
structure ProjectivePresentation (k : Type u) [Field k] (n : ℕ) where
  linearGroup : Specs.GroupScheme k
  scalarGroup : Specs.ClosedSubgroup linearGroup
  linearPoints : (groupPointsFunctor k).obj linearGroup ≅
    Specs.StandardGroups.generalLinearPoints k (ULift.{u} (Fin n))
  scalarPoints : (groupPointsFunctor k).obj scalarGroup.group ≅
    Specs.StandardGroups.multiplicativePoints k
  scalarFormula : ∀ (R : TestAlgebra k) (a : Points scalarGroup.group.X R),
    linearPoints.hom.app R (a ≫ scalarGroup.inclusion.hom.hom) =
      GeneralLinearGroup.scalar (ULift.{u} (Fin n)) (scalarPoints.hom.app R a)
  projectiveGroup : Specs.AffineAlgebraicGroup k
  projection : linearGroup ⟶ projectiveGroup.val
  kernel : Specs.IsSchemeKernel projection scalarGroup
  presentation : Specs.QuotientEmbedding.Presentation scalarGroup
  comparison : presentation.scheme ≅ projectiveGroup.val.X
  projectionFormula : presentation.projection ≫ comparison.hom = projection.hom.hom

/-- Reindex the finite matrix by a type in the universe of the test algebras. -/
def liftMatrix {R : Type u} [CommRing R] {n : ℕ} :
    GL (Fin n) R ≃* GL (ULift.{u} (Fin n)) R :=
  Units.mapEquiv (Matrix.reindexRingEquiv R Equiv.ulift.symm).toMulEquiv

/-- The point identification is induced by the quotient map and is Galois equivariant. -/
def PointIdentification {n : ℕ} (P : ProjectivePresentation k n)
    (e : PGL(n, K) ≃* NonabelianCohomology.Points k K P.projectiveGroup.val.X) : Prop :=
  (∀ G : GL (Fin n) K, e (ProjGenLinGroup.mk G) =
    P.linearPoints.inv.app (CommAlgCat.of k K) (liftMatrix G) ≫ P.projection.hom.hom) ∧
  (∀ (σ : Gal(K/k)) (p : PGL(n, K)),
    e (projectiveAction n σ p) =
      NonabelianCohomology.pointAction k K P.projectiveGroup.val.X σ (e p))

def ProjectivePresentable : Prop :=
  ∀ (k : Type u) [Field k] {n : ℕ}, 0 < n → Nonempty (ProjectivePresentation k n)

def ProjectivePointComparison : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] {n : ℕ} (_hn : 0 < n)
    (P : ProjectivePresentation k n),
    ∃ e : PGL(n, K) ≃* NonabelianCohomology.Points k K P.projectiveGroup.val.X, PointIdentification P e

/-- F03 cohomology with the Krull topology and discrete coefficients. -/
abbrev GaloisH1 {M : Type u} [Group M] (ρ : Gal(K/k) →* MulAut M) :=
  @NonabelianCohomology.H1 _ M _ (krullTopology k K) _ ⊥ ρ

abbrev GaloisCocycle {M : Type u} [Group M] (ρ : Gal(K/k) →* MulAut M) :=
  @NonabelianCohomology.Cocycle _ M _ (krullTopology k K) _ ⊥ ρ

abbrev galoisClass {M : Type u} [Group M] {ρ : Gal(K/k) →* MulAut M}
    (a : GaloisCocycle ρ) : GaloisH1 ρ :=
  @NonabelianCohomology.classOf _ M _ (krullTopology k K) _ ⊥ ρ a

abbrev galoisBasepoint {M : Type u} [Group M] (ρ : Gal(K/k) →* MulAut M) : GaloisH1 ρ :=
  @NonabelianCohomology.basepoint _ M _ (krullTopology k K) _ ⊥ ρ

/-- The comparison of cocycles and pointed quotients respects any equivariant
identification of the abstract scalar quotient with a group of coefficients. -/
def CohomologyComparison : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]
    {n : ℕ} {M : Type u} [Group M] (ρ : Gal(K/k) →* MulAut M) (m : PGL(n, K) ≃* M),
    (∀ σ p, m (projectiveAction n σ p) = ρ σ (m p)) →
    ∃ (j : ProjectiveClassification.Cocycle k K n ≃ GaloisCocycle ρ)
      (e : ProjectiveClassification.H1 k K n ≃ GaloisH1 ρ),
      (∀ c σ, (j c).val σ = m (c.val σ)) ∧
      (∀ c d, ProjectiveClassification.Cohomologous k K n c d ↔
        @NonabelianCohomology.Cohomologous _ M _ (krullTopology k K) _ ⊥ ρ (j c) (j d)) ∧
      (∀ c, e (Quot.mk _ c) = galoisClass (j c)) ∧
      e (Quot.mk _ (ProjectiveClassification.trivial k K n)) = galoisBasepoint ρ

/-- Splitting here is over the given extension, and the degree is the original
algebra's degree over the base field. -/
def FormCriterion : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] {n : ℕ} (_hn : 0 < n)
    {A : Type w} [Ring A] [Algebra k A], _root_.Specs.RM03.CSA.isCentralSimple k A →
    (Nonempty ((K ⊗[k] A) ≃ₐ[K] Mat K n) ↔
      _root_.Specs.RM03.CSA.degree k A = n ∧ _root_.Specs.RM03.CSA.splits k K A)

/-- A cocycle descends the matrix multiplication to a central simple algebra.
The canonical splitting sends a pure tensor to the corresponding scalar multiple. -/
def EffectiveDescent : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {n : ℕ} (_hn : 0 < n) (c : ProjectiveClassification.Cocycle k K n),
    ∃ ρ : AlgebraAction k K (Mat K n), Implements ρ c ∧
      _root_.Specs.RM03.CSA.isCentralSimple k ρ.fixedSubalgebra ∧
      _root_.Specs.RM03.CSA.degree k ρ.fixedSubalgebra = n ∧
      ∃ s : (K ⊗[k] ρ.fixedSubalgebra) ≃ₐ[K] Mat K n, IsTransport ρ s ∧
        ∀ (a : K) (x : ρ.fixedSubalgebra), s (a ⊗ₜ[k] x) = a • (x : Mat K n)

/-- The pointed bijection sends a splitting to its transported action and
sends a cocycle back to the fixed algebra of the twisted action. -/
def Classifies {n : ℕ} (P : ProjectivePresentation k n) : Prop :=
  let ρ := NonabelianCohomology.pointAction k K P.projectiveGroup.val.X
    ∃ (m : PGL(n, K) ≃* NonabelianCohomology.Points k K P.projectiveGroup.val.X)
      (j : ProjectiveClassification.Cocycle k K n ≃ GaloisCocycle ρ)
      (e : SplitClasses k K n ≃ GaloisH1 ρ),
      PointIdentification P m ∧ (∀ c σ, (j c).val σ = m (c.val σ)) ∧
      (∀ (A : Form k K n) (s : (K ⊗[k] A.val) ≃ₐ[K] Mat K n),
        ∃ (τ : AlgebraAction k K (Mat K n)) (c : ProjectiveClassification.Cocycle k K n),
          IsTransport τ s ∧ Implements τ c ∧
          e (Quot.mk (Isomorphic k K n) A) = galoisClass (j c)) ∧
      (∀ (A : Form k K n) (s : (K ⊗[k] A.val) ≃ₐ[K] Mat K n)
          (τ : AlgebraAction k K (Mat K n)) (c : ProjectiveClassification.Cocycle k K n),
        IsTransport τ s → Implements τ c →
        e (Quot.mk (Isomorphic k K n) A) = galoisClass (j c)) ∧
      (∀ {B : Type w} [Ring B] [Algebra k B] (s : (K ⊗[k] B) ≃ₐ[K] Mat K n)
          (τ : AlgebraAction k K (Mat K n)) (c : ProjectiveClassification.Cocycle k K n),
        IsTransport τ s → Implements τ c →
        ∃ A : Form k K n, Nonempty (B ≃ₐ[k] (A.val : Type u)) ∧
          e (Quot.mk (Isomorphic k K n) A) = galoisClass (j c)) ∧
      (∀ (c : ProjectiveClassification.Cocycle k K n) (τ : AlgebraAction k K (Mat K n)), Implements τ c →
        ∃ A : Form k K n, Nonempty ((A.val : Type u) ≃ₐ[k] τ.fixedSubalgebra) ∧
          e.symm (galoisClass (j c)) = Quot.mk (Isomorphic k K n) A) ∧
      (∃ A : Form k K n, Nonempty ((A.val : Type u) ≃ₐ[k] Mat k n)) ∧
      (∀ A : Form k K n, Nonempty ((A.val : Type u) ≃ₐ[k] Mat k n) →
        e (Quot.mk (Isomorphic k K n) A) = galoisBasepoint ρ)

/-- The classification for any presentation of the scalar quotient. -/
def ClassificationOnPresentation : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {n : ℕ}, 0 < n → ∀ P : ProjectivePresentation k n, Classifies.{u,w} (K := K) P

/-- The fixed-degree classification over the specified finite Galois extension. -/
def Classification : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {n : ℕ}, 0 < n → ∃ P : ProjectivePresentation k n, Classifies.{u,w} (K := K) P

end LinearAlgebraicGroups.Descent.MatrixAlgebraForms
