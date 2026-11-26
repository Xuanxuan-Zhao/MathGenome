import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.UnitaryRankOne
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitTorusProduct
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitDerivedRoots
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitAmbientWords
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitPinnedModels
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AdjointBorelCohomology
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SpecialLinearDatum
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.StandardParabolicLevi
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CentralDerived
import Mathlib.Algebra.Group.Action.Hom
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.RingTheory.TensorProduct.Pi

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits
open Module
open scoped BigOperators CategoryTheory.MonObj TensorProduct

universe u v w

namespace LinearAlgebraicGroups.Specs.QuasiSplitOrbitLevis

noncomputable section


open LieAlgebrasAndRepresentations
open AbsoluteDynkinTypes (HasDynkinType PreservesCartan)

/-- The orbit of a simple vertex under the action on the chosen based datum. -/
def diagramOrbit {Γ : Type u} {I : Type v} [Group Γ]
    (ρ : Γ →* Equiv.Perm I) (i : I) : Set I :=
  Set.range (fun g => ρ g i)

/-- An orthogonal simple-root orbit, or exactly the two middle vertices in an
even type A diagram. The equality describes the complete orbit. -/
def OrbitShape {Γ : Type u} {I : Type v} [Group Γ]
    (A : Matrix I I ℤ) (ρ : Γ →* Equiv.Perm I) (i : I) : Prop :=
  (∀ x ∈ diagramOrbit ρ i, ∀ y ∈ diagramOrbit ρ i, x ≠ y →
      A x y = 0 ∧ A y x = 0) ∨
    ∃ (n : ℕ) (h : 0 < n) (e : I ≃ Fin (2 * n)),
      PreservesCartan A (CartanMatrix.A (2 * n)) e ∧
      e '' diagramOrbit ρ i =
        {⟨n - 1, by omega⟩, ⟨n, by omega⟩}

/-- Orbit classification for any action preserving the full Cartan matrix
of an irreducible finite Dynkin diagram. -/
def CartanOrbitShapes : Prop :=
  ∀ {Γ : Type u} {I : Type v} [Group Γ] (A : Matrix I I ℤ)
    (t : FiniteDynkinType), HasDynkinType A t →
    ∀ (ρ : Γ →* Equiv.Perm I), (∀ g, PreservesCartan A A (ρ g)) →
      ∀ i, OrbitShape A ρ i

open Pinning (SplitBorelPair AttachedDatum)
open CharacterDescent (Cocharacter)
open GeometricRadicals (IsSemisimple)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open AbsoluteDynkinTypes (ClassifiedDatum)
open RootData (integralCartan)

variable {k : Type u} [Field k] {P : SplitBorelPair k}

/-- Action on the simple vertices by restriction of an actual based datum
automorphism. -/
def simplePermutation (D : AttachedDatum P) :
    Aut D.toBased →* Equiv.Perm D.toBased.base.support where
  toFun a := a.asIso.hom.val.indexEquiv.subtypeEquiv (by
    intro i
    have h := a.asIso.hom.property
    constructor
    · intro hi
      have hm : a.asIso.hom.val.indexEquiv i ∈
          a.asIso.hom.val.indexEquiv '' (D.toBased.base.support : Set _) := ⟨i, hi, rfl⟩
      change a.asIso.hom.val.indexEquiv i ∈ (D.toBased.base.support : Set _)
      exact Eq.mp (congrArg (fun S : Set D.toBased.I => a.asIso.hom.val.indexEquiv i ∈ S) h) hm
    · intro hi
      have hm : a.asIso.hom.val.indexEquiv i ∈
          a.asIso.hom.val.indexEquiv '' (D.toBased.base.support : Set _) :=
        Eq.mpr (congrArg (fun S : Set D.toBased.I => a.asIso.hom.val.indexEquiv i ∈ S) h) hi
      obtain ⟨j, hj, hji⟩ := hm
      exact (a.asIso.hom.val.indexEquiv.injective hji) ▸ hj)
  map_one' := by ext; rfl
  map_mul' a b := by ext; rfl

/-- The result on the diagram of the attached datum of a split Borel pair. -/
def AttachedOrbitShapes : Prop :=
  ∀ {k : Type u} [Field k] {P : SplitBorelPair k} (D : AttachedDatum P),
    ClassifiedDatum D → ∀ {Γ : Type v} [Group Γ] (ω : Γ →* Aut D.toBased)
      (i : D.toBased.base.support),
      letI := D.comm
      OrbitShape (integralCartan D.datum.rootDatum D.base) ((simplePermutation D).comp ω) i

/-- For the actual split maximal torus of a simply connected semisimple
group, the simple coroots are an integral basis. -/
def AttachedCorootBasis : Prop :=
  ∀ {k : Type u} [Field k] (P : SplitBorelPair k) (D : AttachedDatum P),
    IsSemisimple P.G → GeometricallySimplyConnected P.G →
    letI := D.comm
    ∃ b : Basis D.base.support ℤ (Additive (Cocharacter P.T.group)),
      ∀ i, b i = D.datum.rootDatum.coroot i.val


/-- Integral points of the rational span of some basis vectors are in their
integral span. Coordinates use the full lattice basis, as for simple coroots. -/
def IntegralPointsOfBasisSpan : Prop :=
  ∀ {I : Type u} {Y : Type v} [AddCommGroup Y] (b : Module.Basis I ℤ Y)
    (s : Set I) (y : Y),
    (b.repr y).mapRange (Int.cast : ℤ → ℚ) Int.cast_zero ∈
      Submodule.span ℚ ((fun i => Finsupp.single i (1 : ℚ)) '' s) ↔
    y ∈ Submodule.span ℤ (b '' s)

/-- Splitting the scalar algebra of the quadratic unitary model, using the
two embeddings of the quadratic field in the chosen splitting field. -/
def QuadraticTensorSplitting : Prop :=
  ∀ (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E],
    ∃ e : E ⊗[F] E ≃ₐ[E] E × E, ∀ x y, e (x ⊗ₜ[F] y) =
      (x * y, x * UnitaryRankOne.quadraticConjugation F E y)


/-- The scalar involution on a test algebra tensored with the quadratic field. -/
def quadraticTensorInvolution (F E R : Type*) [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [CommRing R] [Algebra F R] :
    R ⊗[F] E ≃ₐ[R] R ⊗[F] E :=
  Algebra.TensorProduct.congr (.refl : R ≃ₐ[R] R)
    (UnitaryRankOne.quadraticConjugation F E)

/-- Over every algebra of the quadratic field the scalar algebra splits into
two factors, and the involution interchanges them. -/
def UnitaryScalarSplitting : Prop :=
  ∀ (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    (R : Type v) [CommRing R] [Algebra F R] [Algebra E R] [IsScalarTower F E R],
    ∃ e : R ⊗[F] E ≃ₐ[R] R × R,
      (∀ x y, e (x ⊗ₜ[F] y) =
        (x * algebraMap E R y, x * algebraMap E R (UnitaryRankOne.quadraticConjugation F E y))) ∧
      ∀ z, e (quadraticTensorInvolution F E R z) = (e z).swap

section UnitaryModel

open Matrix

variable {R : Type u} [CommRing R]

abbrev SL₃ (R : Type u) [CommRing R] := Matrix.SpecialLinearGroup (Fin 3) R

/-- Reversal of the two matrix indices after inverse transpose. This is
conjugation of the inverse transpose by the anti-diagonal Gram matrix. -/
def hyperbolicInverseTranspose (g : SL₃ R) : SL₃ R :=
  ⟨(g⁻¹).val.transpose.submatrix Fin.revPerm Fin.revPerm,
    by rw [Matrix.det_submatrix_equiv_self, Matrix.det_transpose, (g⁻¹).property]⟩

/-- The nontrivial descent operator for the anti-diagonal hermitian form. -/
def unitaryDescentOperator (σ : R ≃+* R) (g : SL₃ R) : SL₃ R :=
  hyperbolicInverseTranspose (Matrix.SpecialLinearGroup.map σ.toRingHom g)

/-- Over the quadratic field the fixed point equation is the Hermitian
isometry equation, with the determinant encoded in `SL₃`. -/
def UnitaryDescentFixedPoints : Prop :=
  ∀ {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    (σ : E ≃ₐ[F] E) (g : SL₃ E),
    unitaryDescentOperator σ.toRingEquiv g = g ↔
      UnitaryRankOne.PreservesForm σ 1 g.val

/-- The split hyperbolic unitary point functor projects isomorphically to
the first special-linear factor. The second factor is inverse transpose
with the order of the basis reversed. -/
def SplitUnitaryPoints : Prop :=
  ∀ (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    (R : Type v) [CommRing R] [Algebra F R] [Algebra E R] [IsScalarTower F E R]
    (e : R ⊗[F] E ≃ₐ[R] R × R),
    (∀ z, e (quadraticTensorInvolution F E R z) = (e z).swap) →
    ∃ U : Subgroup (SL₃ (R ⊗[F] E)),
      (∀ g, g ∈ U ↔
        unitaryDescentOperator (quadraticTensorInvolution F E R).toRingEquiv g = g) ∧
      ∃ f : U ≃* SL₃ R,
        (∀ g : U, f g = Matrix.SpecialLinearGroup.map
          ((RingHom.fst R R).comp e.toRingEquiv.toRingHom) g.val) ∧
        ∀ g : U, hyperbolicInverseTranspose (f g) = Matrix.SpecialLinearGroup.map
          ((RingHom.snd R R).comp e.toRingEquiv.toRingHom) g.val

/-- The adjacent coordinate coroot in the determinant-one diagonal torus. -/
def matrixSimpleCoroot (i : Fin 2) (t : Rˣ) : SL₃ R :=
  ⟨Matrix.diagonal (fun j => (SpecialLinearDatum.coordinatePairUnits i.castSucc i.succ t j : R)),
    by fin_cases i <;>
      simp [Matrix.det_diagonal, Fin.prod_univ_three, SpecialLinearDatum.coordinatePairUnits]⟩

/-- The based diagram action of the hyperbolic unitary descent on diagonal
cocharacters, with the scalar action displayed explicitly. -/
def UnitaryCorootInterchange : Prop :=
  ∀ {R : Type u} [CommRing R] (σ : R ≃+* R) (i : Fin 2) (t : Rˣ),
    unitaryDescentOperator σ (matrixSimpleCoroot i t) =
      matrixSimpleCoroot i.rev (Units.map σ.toRingHom.toMonoidHom t)

/-- The pinning in which the second simple transvection has its parameter
negated is permuted by the semilinear hyperbolic descent operator. -/
def UnitaryPinningInterchange : Prop :=
  ∀ {R : Type u} [CommRing R] (σ : R ≃+* R) (t : R),
    let x₁ := fun a => Matrix.SpecialLinearGroup.transvection
      (i := (0 : Fin 3)) (j := 1) (by decide) a
    let x₂ := fun a => Matrix.SpecialLinearGroup.transvection
      (i := (1 : Fin 3)) (j := 2) (by decide) (-a)
    unitaryDescentOperator σ (x₁ t) = x₂ (σ t) ∧
      unitaryDescentOperator σ (x₂ t) = x₁ (σ t)

end UnitaryModel

section RankOneWords

open UnitaryRankOne

/-- The split rank-one words in an ambient subgroup that contains the images
of the upper and lower unipotent subgroups. -/
def SplitWordsTransfer : Prop :=
  ∀ {E : Type u} [Field E] {A : Type v} [Group A] (H : Subgroup A)
    (f : Matrix.SpecialLinearGroup (Fin 2) E →* A),
    (∀ a, f (splitUpper a) ∈ H) → (∀ a, f (splitLower a) ∈ H) →
    (∀ g : Matrix.SpecialLinearGroup (Fin 2) E,
      (∃ t : Eˣ, g.val = Matrix.diagonal ![(t : E), (↑t⁻¹ : E)]) → f g ∈ H) ∧
    f (splitWord 1) ∈ H

/-- The unitary rank-one words in an ambient subgroup that contains the
images of the admissible radical matrices. This uses the matrices in
the actual unitary point subgroup. -/
def UnitaryWordsTransfer : Prop :=
  ∀ {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [Infinite F]
    {A : Type w} [Group A]
    (M : Subgroup (Matrix.SpecialLinearGroup (Fin 3) E)) (H : Subgroup A)
    (f : M →* A),
    let σ := quadraticConjugation F E
    (∀ g, g ∈ M ↔ PreservesForm σ 1 g.val) →
    (∀ g : M, g.val ∈ unitaryRadicalGenerators σ 1 → f g ∈ H) →
    (∀ g : M, (∃ d : Fin 3 → E, g.val.val = Matrix.diagonal d) → f g ∈ H) ∧
    ∃ g : M, g.val.val = unitaryWeyl E ∧ f g ∈ H

/-- The split rank-one word acts by reflection on the diagonal coroot. -/
def SplitWeylCorootAction : Prop :=
  ∀ {R : Type u} [CommRing R] (t : Rˣ),
    (splitWord 1 * (splitWord t * splitWord (-1)) * (splitWord (1 : Rˣ))⁻¹).val =
      Matrix.diagonal ![(↑t⁻¹ : R), (t : R)]

/-- The unitary Weyl word acts on the two split simple coroots by the
longest Weyl element of A₂. -/
def UnitaryWeylCorootAction : Prop :=
  ∀ {E : Type u} [Field E] (w : SL₃ E), w.val = unitaryWeyl E →
    ∀ (i : Fin 2) (t : Eˣ),
      w * matrixSimpleCoroot i t * w⁻¹ = matrixSimpleCoroot i.rev t⁻¹

end RankOneWords

section OrbitField

/-- The orbit field is fixed by the stabilizer of a chosen simple vertex.
For a two-element orbit this stabilizer is also the kernel of the action
on that orbit. -/
def orbitField {F K : Type u} [Field F] [Field K] [Algebra F K] {I : Type v}
    (ρ : Gal(K/F) →* Equiv.Perm I) (i : I) : IntermediateField F K :=
  letI := MulAction.compHom I ρ
  IntermediateField.fixedField (MulAction.stabilizer Gal(K/F) i)

/-- The orbit field has degree the size of the orbit. In the adjacent case
this is two, and separability comes from the given finite Galois layer. -/
def OrbitFieldDegree : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    {I : Type v} (ρ : Gal(K/F) →* Equiv.Perm I) (i : I),
    Module.finrank F (orbitField ρ i) = (diagramOrbit ρ i).ncard ∧
    Algebra.IsSeparable F (orbitField ρ i)

/-- A Galois element acts on the actual orbit, viewed as a subtype of the
simple vertices. -/
def orbitTranslate {Γ : Type u} {I : Type v} [Group Γ]
    (ρ : Γ →* Equiv.Perm I) (i : I) (g : Γ) (j : diagramOrbit ρ i) : diagramOrbit ρ i :=
  ⟨ρ g j.val, by
    obtain ⟨h, hh⟩ := j.property
    refine ⟨g * h, ?_⟩
    change ρ (g * h) i = ρ g j.val
    rw [map_mul]
    exact congrArg (ρ g) hh⟩

/-- The scalar extension of the orbit field splits as the product indexed
by the actual orbit, with the embeddings and semilinear action specified. -/
def OrbitScalarSplitting : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    {I : Type u} (ρ : Gal(K/F) →* Equiv.Perm I) (i : I),
    let L := orbitField ρ i
    let J := diagramOrbit ρ i
    ∃ (emb : J → (L →ₐ[F] K)) (e : K ⊗[F] L ≃ₐ[K] (J → K)),
      (∀ (g : Gal(K/F)) (y : L), emb ⟨ρ g i, ⟨g, rfl⟩⟩ y = g y.val) ∧
      (∀ (x : K) (y : L) (j : J), e (x ⊗ₜ[F] y) j = x * emb j y) ∧
      ∀ (g : Gal(K/F)) (z : K ⊗[F] L) (j : J),
        e (Algebra.TensorProduct.map g.toAlgHom (AlgHom.id F L) z) j =
          g (e z (orbitTranslate ρ i g⁻¹ j))

/-- The same orbit-indexed scalar splitting works over arbitrary algebras
of the splitting field, including algebras with nilpotents. -/
def OrbitScalarSplittingOverAlgebras : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    {I : Type u} (ρ : Gal(K/F) →* Equiv.Perm I) (i : I),
    let L := orbitField ρ i
    let J := diagramOrbit ρ i
    ∃ emb : J → (L →ₐ[F] K),
      (∀ (g : Gal(K/F)) (y : L), emb ⟨ρ g i, ⟨g, rfl⟩⟩ y = g y.val) ∧
      ∀ (R : Type v) [CommRing R] [Algebra F R] [Algebra K R] [IsScalarTower F K R],
        ∃ e : R ⊗[F] L ≃ₐ[R] (J → R),
          ∀ x y j, e (x ⊗ₜ[F] y) j = x * algebraMap K R (emb j y)

end OrbitField

section LatticeDecomposition

/-- A partition of the simple coroot basis gives an integral product
decomposition. Its map is addition of the actual included sublattices. -/
def BasisPartitionProduct : Prop :=
  ∀ {I : Type u} {J : Type v} [Fintype J] {Y : Type w} [AddCommGroup Y]
    (b : Basis I ℤ Y) (p : I → J),
    let L := fun j : J => Submodule.span ℤ (b '' {i | p i = j})
    ∃ e : (∀ j, L j) ≃ₗ[ℤ] Y,
      ∀ x, e x = ∑ j, (x j).val

end LatticeDecomposition

section InvariantFace

open Pinning (SplitBorelPair AttachedDatum)
open Specs.CharacterDescent (Cocharacter)
open StandardParabolicLevi (HasFace leviRoots)

/-- The covariant action on the cocharacter lattice of the split Borel pair. -/
noncomputable def cocharacterAction {k : Type u} [Field k] {P : SplitBorelPair k} (D : AttachedDatum P) :
    Aut D.toBased →* (D.toBased.Y ≃ₗ[ℤ] D.toBased.Y) where
  toFun a := a.asIso.hom.val.coweightEquiv.symm
  map_one' := by
    ext x
    let e := (1 : Aut D.toBased).asIso.hom.val.coweightEquiv
    change e.symm x = x
    apply e.injective
    rw [e.apply_symm_apply]
    rfl
  map_mul' a b := by
    ext x
    let e := (a * b).asIso.hom.val.coweightEquiv
    let f := a.asIso.hom.val.coweightEquiv
    let g := b.asIso.hom.val.coweightEquiv
    change e.symm x = f.symm (g.symm x)
    apply e.injective
    rw [e.apply_symm_apply]
    change x = g (f (f.symm (g.symm x)))
    rw [f.apply_symm_apply, g.apply_symm_apply]

/-- A stable face of the actual based root datum admits an integral cocharacter
fixed by the entire finite group acting on the datum. -/
def InvariantFaceCocharacter : Prop :=
  ∀ {k : Type u} [Field k] (P : SplitBorelPair k) (D : AttachedDatum P),
    ∀ {Γ : Type v} [Group Γ] [Finite Γ] (ω : Γ →* Aut D.toBased)
      (I : Set (AbstractPairing.Root P.T)),
      letI := D.comm
      I ⊆ D.base.support →
      (∀ (g : Γ) (i : AbstractPairing.Root P.T),
        (ω g).asIso.hom.val.indexEquiv i ∈ I ↔ i ∈ I) →
      ∃ c : Cocharacter P.T.group, HasFace D.base I c ∧
        ∀ g, cocharacterAction D (ω g) (Additive.ofMul c) = Additive.ofMul c

/-- The orbit of a simple vertex, regarded as a subset of all absolute roots. -/
def orbitRootSet {k : Type u} [Field k] {P : SplitBorelPair k} (D : AttachedDatum P)
    {Γ : Type v} [Group Γ] (ω : Γ →* Aut D.toBased) (i : D.toBased.base.support) :
    Set (AbstractPairing.Root P.T) :=
  Subtype.val '' diagramOrbit ((simplePermutation D).comp ω) i

def OrbitRootStability : Prop :=
  ∀ {k : Type u} [Field k] {P : SplitBorelPair k} (D : AttachedDatum P)
    {Γ : Type v} [Group Γ] (ω : Γ →* Aut D.toBased) (i : D.toBased.base.support),
    letI := D.comm
    let I := orbitRootSet D ω i
    I ⊆ D.base.support ∧ ∀ (g : Γ) (α : AbstractPairing.Root P.T),
      (ω g).asIso.hom.val.indexEquiv α ∈ I ↔ α ∈ I

/-- Covariance on the attached simple coroots agrees with the permutation
of simple vertices. -/
def AttachedCorootPermutation : Prop :=
  ∀ {k : Type u} [Field k] {P : SplitBorelPair k} (D : AttachedDatum P)
    (a : Aut D.toBased) (i : D.toBased.base.support),
    letI := D.comm
    cocharacterAction D a (D.datum.rootDatum.coroot i.val) =
      D.datum.rootDatum.coroot (simplePermutation D a i).val

end InvariantFace

section RationalFace

open LinearAlgebraicGroups.CocharacterDynamics (unitPoint)
open DiagonalizableGroups (groupAlgebra IntegerCharacters)
open GeometricRadicals (IsReductive IsSplitTorus baseChangedSubgroup)
open GeometricBorelConjugacy (IsKBorel)
open Pinning (SplitBorelPair AttachedDatum)
open RankOneFlag (IsGeometricallyMaximal)
open SchemeDerivedGroup (IsSubgroupOf)
open StandardParabolicLevi (HasFace)
open Unipotent (baseChangedAlgebraicGroup)

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

/-- A split pair obtained from the specified rational torus and positive Borel. -/
structure SplitPairOver (G : AffineAlgebraicGroup F) (T B : ClosedSubgroup G.val) where
  torusClosed : IsClosedImmersion ((groupBaseChange F K).map T.inclusion).hom.hom.left
  borelClosed : IsClosedImmersion ((groupBaseChange F K).map B.inclusion).hom.hom.left
  reductive : IsReductive (baseChangedAlgebraicGroup K G)
  split : IsSplitTorus ((groupBaseChange F K).obj T.group)
  maximal : IsGeometricallyMaximal (baseChangedSubgroup K T torusClosed)
  borel : IsKBorel (baseChangedSubgroup K B borelClosed)
  containsTorus : IsSubgroupOf (baseChangedSubgroup K T torusClosed)
    (baseChangedSubgroup K B borelClosed)

/-- The Borel pair over the specified splitting field. -/
def SplitPairOver.pair {G : AffineAlgebraicGroup F} {T B : ClosedSubgroup G.val}
    (S : SplitPairOver (K := K) G T B) : SplitBorelPair K where
  G := baseChangedAlgebraicGroup K G
  reductive := S.reductive
  T := baseChangedSubgroup K T S.torusClosed
  split := S.split
  maximal := S.maximal
  B := baseChangedSubgroup K B S.borelClosed
  borel := S.borel
  containsTorus := S.containsTorus

/-- The semilinear map on the underlying scheme of a group defined over F. -/
def fieldConjugation (σ : Gal(K/F)) (A : GroupScheme F) :
    pullback A.X.hom (fieldSpecMap F K) ⟶ pullback A.X.hom (fieldSpecMap F K) :=
  pullback.lift (pullback.fst A.X.hom (fieldSpecMap F K))
    (pullback.snd A.X.hom (fieldSpecMap F K) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) (by
      have h : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ fieldSpecMap F K =
          fieldSpecMap F K := by
        rw [← Spec.map_comp]
        congr 1
        ext x
        exact σ.commutes x
      rw [Category.assoc, h, pullback.condition])

/-- The identification of Gₘ under base change, with its canonical unit coordinate. -/
abbrev MultiplicativeComparison (F K : Type u) [Field F] [Field K] [Algebra F K] :=
  specGroup (groupAlgebra K IntegerCharacters) ≅
    (groupBaseChange F K).obj (specGroup (groupAlgebra F IntegerCharacters))

def PreservesUnits (e : MultiplicativeComparison F K) : Prop :=
  ∀ (R : TestAlgebra K) (t : Rˣ),
    baseChangePoint F K (specGroup (groupAlgebra F IntegerCharacters)).X R
      (unitPoint R t ≫ e.hom.hom.hom) = unitPoint ((restrictTestAlgebra F K).obj R) t

/-- Compatibility with coefficient Galois action on every actual cocharacter. -/
def IsActualDiagramAction {G : AffineAlgebraicGroup F} {T B : ClosedSubgroup G.val}
    {S : SplitPairOver (K := K) G T B} (D : AttachedDatum S.pair)
    (e : MultiplicativeComparison F K) (ω : Gal(K/F) →* Aut D.toBased) : Prop :=
  ∀ (σ : Gal(K/F)) (y : D.toBased.Y),
    let d := e.inv ≫ (cocharacterAction D (ω σ) y).toMul
    let c := e.inv ≫ y.toMul
    fieldConjugation σ⁻¹ (specGroup (groupAlgebra F IntegerCharacters)) ≫ d.hom.hom.left =
      c.hom.hom.left ≫ fieldConjugation σ⁻¹ T.group

/-- A finite Galois stable face of the actual split pair is cut out by a
ground-field cocharacter of the specified torus. -/
def RationalFaceCocharacter : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (G : AffineAlgebraicGroup F) (T B : ClosedSubgroup G.val) (S : SplitPairOver (K := K) G T B)
    (D : AttachedDatum S.pair) (e : MultiplicativeComparison F K) (ω : Gal(K/F) →* Aut D.toBased),
    PreservesUnits e → IsActualDiagramAction D e ω →
    ∀ I : Set (AbstractPairing.Root S.pair.T),
      letI := D.comm
      I ⊆ D.base.support →
      (∀ (g : Gal(K/F)) (i : AbstractPairing.Root S.pair.T),
        (ω g).asIso.hom.val.indexEquiv i ∈ I ↔ i ∈ I) →
      ∃ c : Cocharacter T.group, HasFace D.base I (e.hom ≫ (groupBaseChange F K).map c)

end RationalFace

section SplitLevi

open Pinning (SplitBorelPair AttachedDatum)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition)
open Specs.CharacterDescent (Cocharacter)
open CharacterPairing (absoluteRoots pairing)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.GeometricRadicals (IsReductive)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.SchemeDerivedGroup (IsDerivedSubgroup)
open Specs.BorelProper (IsParabolic)
open StandardParabolicLevi (HasFace IsCommonKernelTorus leviRoots)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.SubtorusCentralizer (IsCentralizer)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)

/-- The split standard Levi through the specified maximal torus. Its roots
are the subsystem on the chosen subset of the actual attached base. -/
def IsSplitStandardLevi {k : Type u} [Field k] {P : SplitBorelPair k}
    (D : AttachedDatum P) (I : Set (AbstractPairing.Root P.T))
    {c : Cocharacter P.T.group} (L : LimitDecomposition (c ≫ P.T.inclusion)) : Prop :=
  letI := D.comm
  ∃ (Tₗ : ClosedSubgroup L.centralizer.group) (e : P.T.group ≅ Tₗ.group)
    (S : ClosedSubgroup P.T.group),
    IsCommonKernelTorus I S ∧ IsCentralizer (subgroupOfSubgroup P.T S) L.centralizer ∧
    IsParabolic P.G L.parabolic ∧ IsSubgroupOf P.B L.parabolic ∧
    IsReductive (closedSubgroupAlgebraicGroup L.centralizer) ∧
    e.hom ≫ Tₗ.inclusion ≫ L.centralizer.inclusion = P.T.inclusion ∧
    IsGeometricallyMaximal Tₗ ∧ GeometricRadicals.IsSplitTorus Tₗ.group ∧
    absoluteRoots Tₗ = (fun α : AbstractPairing.Root P.T => e.inv ≫ α.val) '' leviRoots D.datum I

def SplitStandardLevi : Prop :=
  ∀ {k : Type u} [Field k] (P : SplitBorelPair k) (D : AttachedDatum P),
    letI := D.comm
    ∀ I : Set (AbstractPairing.Root P.T), I ⊆ D.base.support →
      ∃ (c : Cocharacter P.T.group) (L : LimitDecomposition (c ≫ P.T.inclusion)),
        HasFace D.base I c ∧ IsSplitStandardLevi D I L

/-- In a simply connected group, all coroots in the face subsystem generate
the same saturated sublattice as the selected simple coroots. -/
def FaceCorootSpan : Prop :=
  ∀ {k : Type u} [Field k] (P : SplitBorelPair k) (D : AttachedDatum P),
    IsSemisimple P.G → GeometricallySimplyConnected P.G →
    letI := D.comm
    ∀ I : Set (AbstractPairing.Root P.T), I ⊆ D.base.support →
      let L := Submodule.span ℤ (D.datum.rootDatum.coroot '' I)
      Submodule.span ℤ (D.datum.rootDatum.coroot '' leviRoots D.datum I) = L ∧
        ∀ (y : D.toBased.Y) (n : ℕ), n ≠ 0 → n • y ∈ L → y ∈ L

/-- The cocharacters of the ambient torus factoring through the actual
derived group of the split Levi are exactly the indicated integral span. -/
def SplitLeviCocharacterSpan : Prop :=
  ∀ {k : Type u} [Field k] (P : SplitBorelPair k) (D : AttachedDatum P),
    IsSemisimple P.G → GeometricallySimplyConnected P.G →
    letI := D.comm
    ∀ (I : Set (AbstractPairing.Root P.T)), I ⊆ D.base.support →
      ∀ (c : Cocharacter P.T.group) (L : LimitDecomposition (c ≫ P.T.inclusion)),
        IsSplitStandardLevi D I L →
        ∀ (H : ClosedSubgroup L.centralizer.group), IsDerivedSubgroup H →
          ∀ y : D.toBased.Y,
            (∃ d : Cocharacter H.group,
              d ≫ H.inclusion ≫ L.centralizer.inclusion = y.toMul ≫ P.T.inclusion) ↔
            y ∈ Submodule.span ℤ (D.datum.rootDatum.coroot '' I)

end SplitLevi

section DerivedCoroots

open AbstractPairing (IsAttachedCoroot Root)
open CharacterDescent (Cocharacter)
open Pinning (SplitBorelPair AttachedDatum)
open SchemeDerivedGroup (IsCommutative IsDerivedSubgroup)
open SimplyConnectedLattice (corootLattice)

/-- The actual attached coroot is killed by every commutative quotient. -/
def AttachedCorootToCommutative : Prop :=
  ∀ {k : Type u} [Field k] (G Q : AffineAlgebraicGroup k)
    (T : ClosedSubgroup G.val) (α : Root T) (c : Cocharacter T.group),
    IsAttachedCoroot T α c → ∀ q : G.val ⟶ Q.val,
      IsCommutative Q.val → c ≫ T.inclusion ≫ q = 0

/-- A cocharacter of a split maximal torus factors through the actual
derived subgroup exactly when it lies in the saturation of the coroot lattice. -/
def SplitDerivedCocharacterSaturation : Prop :=
  ∀ {k : Type u} [Field k] (P : SplitBorelPair k) (D : AttachedDatum P)
    (H : ClosedSubgroup P.G.val), IsDerivedSubgroup H →
    ∀ c : Cocharacter P.T.group, letI := D.comm
      (∃ d : Cocharacter H.group, d ≫ H.inclusion = c ≫ P.T.inclusion) ↔
        ∃ n : ℕ, n ≠ 0 ∧ n • Additive.ofMul c ∈ corootLattice D

end DerivedCoroots

section RationalLevi

open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricRadicals (IsReductive IsSemisimple IsTorus)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.SchemeDerivedGroup (IsDerivedSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition)
open GeometricRadicals (baseChangedSubgroup)
open SchemeDerivedGroup (IsSubgroupOf)
open BorelProper (IsParabolic)
open Pinning (AttachedDatum)
open StandardParabolicLevi (HasFace leviRoots)

/-- The rational centralizer of any cocharacter in the chosen maximal torus
has a scheme-theoretic derived subgroup, with its semisimple structure. -/
def DerivedLeviFromRationalCocharacter : Prop :=
  ∀ {F : Type u} [Field F] (G : AffineAlgebraicGroup F)
    (T : ClosedSubgroup G.val), IsReductive G → IsTorus T.group →
    IsGeometricallyMaximal T → ∀ c : Cocharacter T.group,
    ∃ (D : LimitDecomposition (c ≫ T.inclusion)) (H : ClosedSubgroup D.centralizer.group),
      IsReductive (closedSubgroupAlgebraicGroup D.centralizer) ∧
      IsDerivedSubgroup H ∧ IsSemisimple
        (closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup D.centralizer) H)

/-- The standard Levi of an invariant face and its derived group are defined
over the ground field. The displayed splitting identifies their inclusions. -/
def RationalFaceDerivedLevi : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (G : AffineAlgebraicGroup F) (T B : ClosedSubgroup G.val) (S : SplitPairOver (K := K) G T B)
    (D : AttachedDatum S.pair) (e : MultiplicativeComparison F K) (ω : Gal(K/F) →* Aut D.toBased),
    IsReductive G → IsTorus T.group → IsGeometricallyMaximal T →
    PreservesUnits e → IsActualDiagramAction D e ω →
    ∀ I : Set (AbstractPairing.Root S.pair.T),
      letI := D.comm
      I ⊆ D.base.support →
      (∀ (g : Gal(K/F)) (i : AbstractPairing.Root S.pair.T),
        (ω g).asIso.hom.val.indexEquiv i ∈ I ↔ i ∈ I) →
      ∃ c : Cocharacter T.group,
        let cK := e.hom ≫ (groupBaseChange F K).map c
        HasFace D.base I cK ∧
        ∃ (L : LimitDecomposition (c ≫ T.inclusion)) (H : ClosedSubgroup L.centralizer.group)
          (Lk : LimitDecomposition (cK ≫ S.pair.T.inclusion)),
          IsParabolic G L.parabolic ∧ IsSubgroupOf B L.parabolic ∧
          IsReductive (closedSubgroupAlgebraicGroup L.centralizer) ∧ IsDerivedSubgroup H ∧
          IsSemisimple (closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup L.centralizer) H) ∧
          IsSplitStandardLevi D I Lk ∧
          ∃ j : (groupBaseChange F K).obj L.centralizer.group ≅ Lk.centralizer.group,
            j.hom ≫ Lk.centralizer.inclusion = (groupBaseChange F K).map L.centralizer.inclusion ∧
            ∃ hH, IsDerivedSubgroup (baseChangedSubgroup K H hH) ∧
              ∀ α ∈ leviRoots D.datum I,
                ∃ cH : Cocharacter ((groupBaseChange F K).obj H.group),
                  cH ≫ (groupBaseChange F K).map (H.inclusion ≫ L.centralizer.inclusion) =
                    (D.datum.rootDatum.coroot α).toMul ≫ S.pair.T.inclusion


/-- The scheme intersection of a maximal torus with the derived subgroup
is a geometrically maximal torus of the derived subgroup. -/
def DerivedMaximalTorusIntersection : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (T : ClosedSubgroup G.val), IsGeometricallyMaximal T →
    ∀ (H : ClosedSubgroup G.val), IsDerivedSubgroup H →
      ∃ (V : ClosedSubgroup H.group) (i : V.group ⟶ T.group),
        IsPullback i V.inclusion T.inclusion H.inclusion ∧
        IsClosedImmersion i.hom.hom.left ∧ IsTorus V.group ∧ IsGeometricallyMaximal V ∧
        (GeometricRadicals.IsSplitTorus T.group → GeometricRadicals.IsSplitTorus V.group)

/-- The maximal torus of the derived centralizer is the scheme intersection
with the ambient maximal torus. It splits over every field that splits that torus. -/
def RationalDerivedLeviTorus : Prop :=
  ∀ {F : Type u} [Field F] (G : AffineAlgebraicGroup F)
    (T : ClosedSubgroup G.val), IsTorus T.group → IsGeometricallyMaximal T →
    ∀ (c : Cocharacter T.group) (L : LimitDecomposition (c ≫ T.inclusion)),
      IsReductive (closedSubgroupAlgebraicGroup L.centralizer) →
      ∀ (H : ClosedSubgroup L.centralizer.group), IsDerivedSubgroup H →
        ∃ (V : ClosedSubgroup H.group) (i : V.group ⟶ T.group),
          IsPullback i V.inclusion T.inclusion (H.inclusion ≫ L.centralizer.inclusion) ∧
          IsClosedImmersion i.hom.hom.left ∧ IsTorus V.group ∧ IsGeometricallyMaximal V ∧
          ∀ (K : Type u) [Field K] [Algebra F K],
            GeometricRadicals.IsSplitTorus ((groupBaseChange F K).obj T.group) →
            GeometricRadicals.IsSplitTorus ((groupBaseChange F K).obj V.group)

/-- The derived torus of the rational face, with its embedding into the
ambient torus and its exact cocharacter sublattice over the splitting field. -/
def RationalFaceDerivedTorus : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (G : AffineAlgebraicGroup F) (T B : ClosedSubgroup G.val) (S : SplitPairOver (K := K) G T B)
    (D : AttachedDatum S.pair) (e : MultiplicativeComparison F K) (ω : Gal(K/F) →* Aut D.toBased),
    IsReductive G → IsTorus T.group → IsGeometricallyMaximal T →
    IsSemisimple S.pair.G → GeometricallySimplyConnected S.pair.G →
    PreservesUnits e → IsActualDiagramAction D e ω →
    ∀ I : Set (AbstractPairing.Root S.pair.T),
      letI := D.comm
      I ⊆ D.base.support →
      (∀ (g : Gal(K/F)) (i : AbstractPairing.Root S.pair.T),
        (ω g).asIso.hom.val.indexEquiv i ∈ I ↔ i ∈ I) →
      ∃ c : Cocharacter T.group,
        HasFace D.base I (e.hom ≫ (groupBaseChange F K).map c) ∧
        ∃ (L : LimitDecomposition (c ≫ T.inclusion)) (H : ClosedSubgroup L.centralizer.group),
          IsParabolic G L.parabolic ∧ IsSubgroupOf B L.parabolic ∧
          IsReductive (closedSubgroupAlgebraicGroup L.centralizer) ∧ IsDerivedSubgroup H ∧
          IsSemisimple (closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup L.centralizer) H) ∧
          ∃ (V : ClosedSubgroup H.group) (i : V.group ⟶ T.group),
            IsPullback i V.inclusion T.inclusion (H.inclusion ≫ L.centralizer.inclusion) ∧
            IsClosedImmersion i.hom.hom.left ∧ IsTorus V.group ∧ IsGeometricallyMaximal V ∧
            GeometricRadicals.IsSplitTorus ((groupBaseChange F K).obj V.group) ∧
            ∀ y : D.toBased.Y,
              (∃ z : Cocharacter ((groupBaseChange F K).obj V.group),
                z ≫ (groupBaseChange F K).map i = y.toMul) ↔
              y ∈ Submodule.span ℤ (D.datum.rootDatum.coroot '' I)

end RationalLevi

section TorusDescent

open LinearAlgebraicGroups.Descent (SemilinearAction)
open Specs.CharacterDescent (GeometricCharacters)
open AdjointBorelCohomology (PermutedCharacterBasis IsOrbitWeilProduct)

/-- Over a Galois splitting field, it suffices to test descent of a torus
coordinate map on its geometric characters. -/
def DescentOnGeometricCharacters : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {A B : HopfAlgebraCategory k} (f : extendedHopf K A ⟶ extendedHopf K B),
    CharacterDescent.IsDiagonalizable (extendedHopf K A) →
    (∀ (g : Gal(K/k)) (x : GeometricCharacters K A),
      f.hom ((SemilinearAction.scalarExtension (K := K) A).act g x.val) =
        (SemilinearAction.scalarExtension (K := K) B).act g (f.hom x.val)) →
    ∃ q : A ⟶ B, extendedHopfMap K q = f

/-- A permutation basis of the actual geometric characters of a torus
gives the product of restrictions of scalars from the orbit fields. -/
def PermutationTorusProduct : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    {I : Type u} [Finite I] (ρ : Gal(K/F) →* Equiv.Perm I) (T : AffineAlgebraicGroup F),
    GeometricRadicals.IsSplitTorus ((groupBaseChange F K).obj T.val) →
    PermutedCharacterBasis K I T ρ → IsOrbitWeilProduct K ρ T

end TorusDescent

section MatrixDatum

open Pinning (AttachedDatum)
open GeneralLinearStructure (SpecialMatrixPoints)
open Specs.SpecialLinearDatum
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)

/-- The adjacent pair of row and column indices in the canonical determinant-one matrix model. -/
def adjacentRootIndex {r : ℕ} (i : Fin r) : RootIndices (r + 1) :=
  ⟨(i.castSucc, i.succ), ((Fin.castSucc_lt_succ_iff).mpr le_rfl).ne⟩

/-- The matrix of the attached simple coroot of the canonical determinant-one
model on an arbitrary test algebra. This identifies the actual coroot,
including in the two matrix ranks used for orbit Levis. -/
def AttachedMatrixCoroots : Prop :=
  ∀ {k : Type u} [Field k] (r : ℕ) (S : AffineAlgebraicGroup k)
    (s : SpecialMatrixPoints S (r + 1)),
    ∃ (T : DiagonalTorus s) (L : LatticeIdentification T) (M : RootIdentification T L)
      (B : UpperTriangularBorel T L M) (D : AttachedDatum B.pair),
      IsMatrixBasedDatum B D ∧ HasTransvectionPinning B ∧
      SimplyConnectedLattice.GeometricallySimplyConnected S ∧
      letI := D.comm
      (∀ i : Fin r, M.indices (adjacentRootIndex i) ∈ D.base.support) ∧
      ∀ (i : Fin r) (R : TestAlgebra k) (t : Rˣ),
        let c := Additive.toMul (D.datum.rootDatum.coroot (M.indices (adjacentRootIndex i)))
        (s.hom.app R
          (cocharacterPoint c R t ≫ T.subgroup.inclusion.hom.hom)).val =
          Matrix.diagonal (fun j => (coordinatePairUnits i.castSucc i.succ t j.down : R))

end MatrixDatum

section HermitianModel

open Matrix

/-- The anti-diagonal Gram matrix of the hyperbolic Hermitian form with
middle coefficient one. -/
def hyperbolicGram (R : Type u) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![0, 0, 1; 0, 1, 0; 1, 0, 0]

/-- The determinant-one fixed equation is the Hermitian equation on every
test algebra, with its induced scalar involution. -/
def HyperbolicFixedEquation : Prop :=
  ∀ {R : Type u} [CommRing R] (σ : R ≃+* R) (g : SL₃ R),
    unitaryDescentOperator σ g = g ↔
      (g.val.map σ).transpose * hyperbolicGram R * g.val = hyperbolicGram R

/-- The two factors of the scalar splitting are natural in algebras of the
splitting field. It suffices to specify the two projections on pure tensors. -/
def UnitaryScalarSplittingNaturality : Prop :=
  ∀ (F E : Type u) [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    {R S : Type v} [CommRing R] [CommRing S]
    [Algebra F R] [Algebra F S] [Algebra E R] [Algebra E S]
    [IsScalarTower F E R] [IsScalarTower F E S] (f : R →ₐ[E] S)
    (eR : R ⊗[F] E ≃ₐ[R] R × R) (eS : S ⊗[F] E ≃ₐ[S] S × S),
    let σ := UnitaryRankOne.quadraticConjugation F E
    (∀ x y, eR (x ⊗ₜ[F] y) = (x * algebraMap E R y, x * algebraMap E R (σ y))) →
    (∀ x y, eS (x ⊗ₜ[F] y) = (x * algebraMap E S y, x * algebraMap E S (σ y))) →
    ∀ z, eS (Algebra.TensorProduct.map (f.restrictScalars F) (AlgHom.id F E) z) =
      (f (eR z).1, f (eR z).2)

end HermitianModel

section UnitaryScheme

open LinearAlgebraicGroups.WeilRestriction (extendScalars)

/-- The standard determinant-one matrices with three rows and columns. -/
def specialLinearThreePoints (k : Type u) [Field k] : TestAlgebra k ⥤ GrpCat.{u} where
  obj R := GrpCat.of (SL₃ R)
  map f := GrpCat.ofHom (Matrix.SpecialLinearGroup.map f.hom.toRingHom)
  map_id _ := by ext g; rfl
  map_comp _ _ := by ext g; rfl

/-- The hyperbolic special unitary group represents the determinant-one
Hermitian equation inside the restriction of scalars of the split group. -/
def RepresentsHyperbolicUnitary {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    {W : AffineAlgebraicGroup F} (U : ClosedSubgroup W.val)
    (m : (groupPointsFunctor F).obj W.val ≅ extendScalars F E ⋙ specialLinearThreePoints E) : Prop :=
  ∀ (R : TestAlgebra F) (g : SL₃ (R ⊗[F] E)),
    let σ := (quadraticTensorInvolution F E R).toRingEquiv
    (g.val.map σ).transpose * hyperbolicGram (R ⊗[F] E) * g.val = hyperbolicGram (R ⊗[F] E) ↔
    ∃ p : AdjointRepresentation.GroupPoints U.group R,
      m.hom.app R (((groupPointsFunctor F).map U.inclusion).app R p) = g

def HyperbolicUnitaryModel : Prop :=
  ∀ (F E : Type u) [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E],
    ∃ (W : AffineAlgebraicGroup F) (U : ClosedSubgroup W.val)
      (m : (groupPointsFunctor F).obj W.val ≅ extendScalars F E ⋙ specialLinearThreePoints E),
      RepresentsHyperbolicUnitary (E := E) U m

/-- The first scalar projection is multiplication along the chosen
embedding of the quadratic field in the test algebra. -/
def unitaryFirstProjection {F E : Type u} [Field F] [Field E] [Algebra F E]
    (R : TestAlgebra E) : ((restrictTestAlgebra F E).obj R ⊗[F] E) →+* R := by
  let R₀ := (restrictTestAlgebra F E).obj R
  letI : Algebra E R₀ := inferInstanceAs (Algebra E R)
  letI : IsScalarTower F E R₀ := IsScalarTower.of_algebraMap_eq' rfl
  exact (Algebra.TensorProduct.lift (AlgHom.id F R₀)
    ((Algebra.ofId E R₀).restrictScalars F) (fun _ _ => Commute.all _ _)).toRingHom

/-- Over the quadratic field the determinant-one unitary model is the
split special linear group via the first matrix projection on every test algebra. -/
def HyperbolicUnitaryBaseChange : Prop :=
  ∀ (F E : Type u) [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    (W : AffineAlgebraicGroup F) (U : ClosedSubgroup W.val)
    (m : (groupPointsFunctor F).obj W.val ≅ extendScalars F E ⋙ specialLinearThreePoints E),
    RepresentsHyperbolicUnitary (E := E) U m →
    ∀ (A : AffineAlgebraicGroup E)
      (a : (groupPointsFunctor E).obj A.val ≅ specialLinearThreePoints E),
      ∃ e : (groupBaseChange F E).obj U.group ≅ A.val,
        ∀ (R : TestAlgebra E) (x : AdjointRepresentation.GroupPoints ((groupBaseChange F E).obj U.group) R),
          let R₀ := (restrictTestAlgebra F E).obj R
          a.hom.app R (((groupPointsFunctor E).map e.hom).app R x) =
            Matrix.SpecialLinearGroup.map (unitaryFirstProjection (F := F) R)
              (m.hom.app R₀ (baseChangePoint F E U.group.X R x ≫ U.inclusion.hom.hom))

/-- Over the ground field the represented unitary group has exactly the
Hermitian determinant-one matrices over the quadratic extension. -/
def HyperbolicUnitaryRationalPoints : Prop :=
  ∀ (F E : Type u) [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    (W : AffineAlgebraicGroup F) (U : ClosedSubgroup W.val)
    (m : (groupPointsFunctor F).obj W.val ≅ extendScalars F E ⋙ specialLinearThreePoints E),
    RepresentsHyperbolicUnitary (E := E) U m →
    let R := CommAlgCat.of F F
    ∃ (M : Subgroup (SL₃ E)) (e : AdjointRepresentation.GroupPoints U.group R ≃* M),
      (∀ g, g ∈ M ↔ UnitaryRankOne.PreservesForm (UnitaryRankOne.quadraticConjugation F E) 1 g.val) ∧
      ∀ p, (e p).val = Matrix.SpecialLinearGroup.map
        (Algebra.TensorProduct.lid F E).toRingEquiv.toRingHom
          (m.hom.app R (p ≫ U.inclusion.hom.hom))

end UnitaryScheme

section OrbitAssembly

open Specs.AbstractPairing (Root)
open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricRadicals (IsReductive IsSemisimple IsSplitTorus IsTorus baseChangedSubgroup)
open Specs.GeometricBorelConjugacy (IsKBorel subgroupOfSubgroup)
open Specs.Pinning (AttachedDatum)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.SchemeDerivedGroup (IsDerivedSubgroup IsSubgroupOf)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.StandardParabolicLevi (HasFace IsCommonKernelTorus leviRoots)
open Specs.SubtorusCentralizer (IsCentralizer)
open Specs.BorelProper (IsParabolic)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open CategoryTheory.Limits
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition)

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
variable {G : AffineAlgebraicGroup F} {T B : ClosedSubgroup G.val}
variable {P : SplitPairOver (K := K) G T B}

variable (D : AttachedDatum P.pair)

-- Compose an embedded subgroup with a change of presentation of its ambient group.
def subgroupAlongIso {k : Type u} [Field k] {G H : GroupScheme k} (e : G ≅ H)
    (S : ClosedSubgroup G) : ClosedSubgroup H := by
  have hi := S.isClosedImmersion
  have he : IsIso e.hom.hom.hom.left :=
    (Grp.forget (SchemeOver k) ⋙ Over.forget _).map_isIso e.hom
  exact ⟨S.group, S.inclusion ≫ e.hom, IsClosedImmersion.comp _ _⟩

/-- The rational standard Levi of a stable face, its scheme-derived group,
and the embedded scheme intersection with the given ambient torus. The
two presentations over the splitting field identify the actual inclusions. -/
structure RationalStandardFace (I : Set (Root P.pair.T)) where
  simple : letI := D.comm; I ⊆ D.base.support
  scalar : MultiplicativeComparison F K
  cocharacter : Cocharacter T.group
  limit : LimitDecomposition (cocharacter ≫ T.inclusion)
  parabolic : IsParabolic G limit.parabolic
  containsBorel : IsSubgroupOf B limit.parabolic
  reductive : IsReductive (closedSubgroupAlgebraicGroup limit.centralizer)
  derived : ClosedSubgroup limit.centralizer.group
  isDerived : IsDerivedSubgroup derived
  semisimple : IsSemisimple
    (closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup limit.centralizer) derived)
  torus : ClosedSubgroup derived.group
  torusMap : torus.group ⟶ T.group
  torusClosed : IsClosedImmersion torusMap.hom.hom.left
  intersection : IsPullback torusMap torus.inclusion T.inclusion
    (derived.inclusion ≫ limit.centralizer.inclusion)
  isTorus : IsTorus torus.group
  maximal : IsGeometricallyMaximal torus
  splitClosed : IsClosedImmersion ((groupBaseChange F K).map torus.inclusion).hom.hom.left
  splitMaximal : IsGeometricallyMaximal (baseChangedSubgroup K torus splitClosed)
  splitTorus : IsSplitTorus ((groupBaseChange F K).obj torus.group)
  integralImage : letI := D.comm
    ∀ y : D.toBased.Y,
      (∃ c : Cocharacter ((groupBaseChange F K).obj torus.group),
        c ≫ (groupBaseChange F K).map torusMap = y.toMul) ↔
      y ∈ Submodule.span ℤ (D.datum.rootDatum.coroot '' I)
  saturatedImage : letI := D.comm
    ∀ y : D.toBased.Y,
      (∃ c : Cocharacter ((groupBaseChange F K).obj torus.group),
        c ≫ (groupBaseChange F K).map torusMap = y.toMul) ↔
      ∃ n : ℕ, n ≠ 0 ∧ n • y ∈ Submodule.span ℤ (D.datum.rootDatum.coroot '' I)
  hasFace : letI := D.comm; HasFace D.base I (scalar.hom ≫ (groupBaseChange F K).map cocharacter)
  splitLimit : LimitDecomposition
    ((scalar.hom ≫ (groupBaseChange F K).map cocharacter) ≫ P.pair.T.inclusion)
  comparison : (groupBaseChange F K).obj limit.centralizer.group ≅ splitLimit.centralizer.group
  comparisonSquare :
    comparison.hom ≫ splitLimit.centralizer.inclusion = (groupBaseChange F K).map limit.centralizer.inclusion
  kernelTorus : ClosedSubgroup P.pair.T.group
  kernel : IsCommonKernelTorus I kernelTorus
  splitCentralizer : IsCentralizer (subgroupOfSubgroup P.pair.T kernelTorus) splitLimit.centralizer
  splitReductive : IsReductive (closedSubgroupAlgebraicGroup splitLimit.centralizer)
  splitLeviTorus : ClosedSubgroup splitLimit.centralizer.group
  splitLeviTorusIso : P.pair.T.group ≅ splitLeviTorus.group
  splitLeviTorusSquare : splitLeviTorusIso.hom ≫ splitLeviTorus.inclusion ≫
    splitLimit.centralizer.inclusion = P.pair.T.inclusion
  splitLeviTorusMaximal : IsGeometricallyMaximal splitLeviTorus
  splitLeviRoots : letI := D.comm
    CharacterPairing.absoluteRoots splitLeviTorus =
      (fun α : Root P.pair.T => splitLeviTorusIso.inv ≫ α.val) '' leviRoots D.datum I
  splitDerivedClosed : IsClosedImmersion ((groupBaseChange F K).map derived.inclusion).hom.hom.left
  splitIsDerived : IsDerivedSubgroup
    (subgroupAlongIso comparison (baseChangedSubgroup K derived splitDerivedClosed))
  splitIntersection : IsPullback ((groupBaseChange F K).map torusMap)
    ((groupBaseChange F K).map torus.inclusion) P.pair.T.inclusion
    ((subgroupAlongIso comparison (baseChangedSubgroup K derived splitDerivedClosed)).inclusion ≫
      splitLimit.centralizer.inclusion)

abbrev RationalStandardFace.embeddedTorus {I : Set (Root P.pair.T)}
    (L : RationalStandardFace D I) : ClosedSubgroup T.group :=
  ⟨L.torus.group, L.torusMap, L.torusClosed⟩

def RationalStandardFace.splitFace {I : Set (Root P.pair.T)}
    (L : RationalStandardFace D I) : QuasiSplitOrbitDerivedRoots.SplitFace D I where
  simple := L.simple
  kernelTorus := L.kernelTorus
  kernel := L.kernel
  levi := L.splitLimit.centralizer
  centralizer := L.splitCentralizer
  reductive := L.splitReductive
  leviTorus := L.splitLeviTorus
  torusIso := L.splitLeviTorusIso
  torusInclusion := L.splitLeviTorusSquare
  leviTorusMaximal := L.splitLeviTorusMaximal
  leviRoots_eq := L.splitLeviRoots
  derived := subgroupAlongIso L.comparison (baseChangedSubgroup K L.derived L.splitDerivedClosed)
  isDerived := L.splitIsDerived
  torus := baseChangedSubgroup K L.torus L.splitClosed
  toAmbientTorus := (groupBaseChange F K).map L.torusMap
  intersection := L.splitIntersection
  torusSplit := L.splitTorus
  torusMaximal := L.splitMaximal

/-- The rational opposite Borels meet in the specified maximal torus,
with its given embedding into the ambient group. -/
structure RationalOppositePair {G : AffineAlgebraicGroup F} (T B N : ClosedSubgroup G.val) where
  positive : IsKBorel B
  negative : IsKBorel N
  toPositive : T.group ⟶ B.group
  toNegative : T.group ⟶ N.group
  intersection : IsPullback toPositive toNegative B.inclusion N.inclusion
  positiveSquare : toPositive ≫ B.inclusion = T.inclusion

set_option backward.isDefEq.respectTransparency false in
def RationalStandardFace.rationalFace {I : Set (Root P.pair.T)} {N : ClosedSubgroup G.val}
    (L : RationalStandardFace D I) (pair : RationalOppositePair T B N)
    (hG : IsReductive G) (hT : IsTorus T.group) (hmax : IsGeometricallyMaximal T) :
    QuasiSplitOrbitDerivedRoots.RationalFace F (L.splitFace D) where
  ambient := G
  ambientReductive := hG
  ambientTorus := T
  ambientTorusIsTorus := hT
  ambientTorusMaximal := hmax
  positive := B
  negative := N
  positiveBorel := pair.positive
  negativeBorel := pair.negative
  positiveTorus := pair.toPositive
  negativeTorus := pair.toNegative
  opposite := pair.intersection
  positiveTorusSquare := pair.positiveSquare
  levi := L.limit.centralizer
  leviReductive := L.reductive
  derived := L.derived
  isDerived := L.isDerived
  torus := L.torus
  toAmbientTorus := L.torusMap
  intersection := L.intersection
  torusIsTorus := L.isTorus
  torusMaximal := L.maximal
  groupComparison := Iso.refl _
  ambientTorusComparison := Iso.refl _
  ambientTorusSquare := by
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  positiveComparison := Iso.refl _
  positiveSquare := by
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  leviComparison := L.comparison
  leviSquare := by
    simp only [Iso.refl_hom, Category.comp_id]
    exact L.comparisonSquare
  derivedComparison := Iso.refl _
  derivedSquare := by
    change (𝟙 _) ≫ ((groupBaseChange F K).map L.derived.inclusion ≫ L.comparison.hom) = _
    rw [Category.id_comp]
  torusComparison := Iso.refl _
  torusSquare := by
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  torusMapSquare := by
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  integralImage := L.integralImage

open QuasiSplitOrbitDerivedRoots (ActualPinnedAction InducedBorel coefficientAction comparedAction
  diagramRoot diagramSimple pinnedRootMap)
open Pinning (PinnedGroup SimpleRoot Pinning)
open RootGroups (AdditiveLine)
open OrderedRootProducts (RootSubgroupFamily)

/-- The given pinning realizes the diagram action for the actual scalar
extensions of the ambient group, the torus and the additive line. -/
structure IsAmbientPinnedAction {A₀ : AdditiveLine F} {A : AdditiveLine K}
    {U : RootSubgroupFamily P.pair.T} (p : Pinning A P.pair U)
    (a : (groupBaseChange F K).obj A₀.group ≅ A.group)
    (m : MultiplicativeComparison F K) (ω : Gal(K/F) →* Aut D.toBased) : Prop where
  characters : ∀ (σ : Gal(K/F)) (α : Root P.pair.T),
    fieldConjugation σ⁻¹ T.group ≫ (diagramRoot ω σ α).val.hom.hom.left =
      α.val.hom.hom.left ≫ comparedAction σ⁻¹ m.symm
  cocharacters : IsActualDiagramAction D m ω
  pinning : ∀ (σ : Gal(K/F)) (α : SimpleRoot P.pair),
    comparedAction σ⁻¹ a ≫ (pinnedRootMap p (diagramSimple ω σ α)).hom.hom.left =
      (pinnedRootMap p α).hom.hom.left ≫ fieldConjugation σ⁻¹ G.val

/-- The full split root comparison on the actual rational face. It records
the two induced Borels, the attached coroots and the inherited pinning. -/
structure InducedFaceData {I : Set (Root P.pair.T)} {N : ClosedSubgroup G.val}
    {L : RationalStandardFace D I} {pair : RationalOppositePair T B N}
    {hG : IsReductive G} {hT : IsTorus T.group} {hmax : IsGeometricallyMaximal T}
    {A₀ : AdditiveLine F} {A : AdditiveLine K}
    {U : RootSubgroupFamily P.pair.T} (p : Pinning A P.pair U)
    (a : (groupBaseChange F K).obj A₀.group ≅ A.group)
    (ω : Gal(K/F) →* Aut D.toBased) where
  reductive : IsReductive (L.splitFace D).group
  positive : InducedBorel (L.rationalFace D pair hG hT hmax) B
  negative : InducedBorel (L.rationalFace D pair hG hT hmax) N
  posDatum : AttachedDatum (positive.pair reductive)
  negDatum : AttachedDatum (negative.pair reductive)
  roots : letI := D.comm
    ↥(leviRoots D.datum I) ≃ Root (G := (L.splitFace D).group) (L.splitFace D).torus
  opposite : ∃ (ip : L.torus.group ⟶ positive.rational.group)
      (in' : L.torus.group ⟶ negative.rational.group),
    IsPullback ip in' positive.rational.inclusion negative.rational.inclusion ∧
      ip ≫ positive.rational.inclusion = L.torus.inclusion
  simplyConnected : GeometricallySimplyConnected (L.rationalFace D pair hG hT hmax).group
  stable : letI := D.comm; ∀ (σ : Gal(K/F)) (α : ↥(leviRoots D.datum I)),
    diagramRoot ω σ α.val ∈ leviRoots D.datum I
  rootComparison : letI := D.comm; letI := posDatum.comm; letI := negDatum.comm
    ∀ α, (roots α).val = (L.splitFace D).toAmbientTorus ≫ α.val.val ∧
      (posDatum.datum.rootDatum.coroot (roots α)).toMul ≫ (L.splitFace D).toAmbientTorus =
        (D.datum.rootDatum.coroot α.val).toMul ∧
      ((roots α) ∈ posDatum.base.support ↔ α.val ∈ I) ∧
      ((roots α) ∈ negDatum.base.support ↔ ∃ δ ∈ I, α.val.val = δ.val⁻¹) ∧
      ∀ Z : ClosedSubgroup P.pair.G.val, RootGroups.IsRootSubgroup P.pair.T Z α.val.val →
        ∃ V : ClosedSubgroup (L.splitFace D).group.val,
          RootGroups.IsRootSubgroup (L.splitFace D).torus V (roots α).val ∧
          ∃ r : V.group ≅ Z.group, r.hom ≫ Z.inclusion = V.inclusion ≫ (L.splitFace D).inclusion
  rootGroups : RootSubgroupFamily (positive.pair reductive).T
  pinning : Pinning A (positive.pair reductive) rootGroups
  pinningComparison : letI := D.comm; ∀ (α : ↥(leviRoots D.datum I)) (i : SimpleRoot P.pair)
      (j : SimpleRoot (positive.pair reductive)), i.val = α.val → j.val = roots α →
    pinnedRootMap pinning j ≫ (L.splitFace D).inclusion = pinnedRootMap p i
  action : letI := D.comm; letI := posDatum.comm
    ∀ (σ : Gal(K/F)) (α α' : ↥(leviRoots D.datum I)), α'.val = diagramRoot ω σ α.val →
      comparedAction σ⁻¹ (L.rationalFace D pair hG hT hmax).torusComparison ≫ (roots α').val.hom.hom.left =
        (roots α).val.hom.hom.left ≫ comparedAction σ⁻¹ L.scalar.symm ∧
      comparedAction σ⁻¹ L.scalar.symm ≫ (posDatum.datum.rootDatum.coroot (roots α')).toMul.hom.hom.left =
        (posDatum.datum.rootDatum.coroot (roots α)).toMul.hom.hom.left ≫
          comparedAction σ⁻¹ (L.rationalFace D pair hG hT hmax).torusComparison ∧
      ∀ (i : SimpleRoot P.pair) (j j' : SimpleRoot (positive.pair reductive)),
        i.val = α.val → j.val = roots α → j'.val = roots α' →
        comparedAction σ⁻¹ a ≫ (pinnedRootMap pinning j').hom.hom.left =
          (pinnedRootMap pinning j).hom.hom.left ≫
            comparedAction σ⁻¹ (L.rationalFace D pair hG hT hmax).derivedComparison

def RationalFacePinning : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    {G : AffineAlgebraicGroup F} {T B N : ClosedSubgroup G.val} {P : SplitPairOver (K := K) G T B}
    (D : AttachedDatum P.pair) (pair : RationalOppositePair T B N)
    (hG : IsReductive G) (hT : IsTorus T.group) (hmax : IsGeometricallyMaximal T)
    {A₀ : AdditiveLine F} {A : AdditiveLine K}
    (U : RootSubgroupFamily P.pair.T) (p : Pinning A P.pair U)
    (a : (groupBaseChange F K).obj A₀.group ≅ A.group)
    (ω : Gal(K/F) →* Aut D.toBased) (I : Set (Root P.pair.T)) (L : RationalStandardFace D I),
    IsAmbientPinnedAction D p a L.scalar ω →
    (∀ (σ : Gal(K/F)) (α : Root P.pair.T), diagramRoot ω σ α ∈ I ↔ α ∈ I) →
    Nonempty (InducedFaceData D (L := L) (pair := pair) (hG := hG) (hT := hT) (hmax := hmax) p a ω)

open QuasiSplitOrbitAmbientWords (BorelRadical OrbitLevi SplitOrbit)

def HasSplitAmbientOrbit {B₀ : Bool → BorelRadical G}
    {P : SplitPairOver (K := K) G T (B₀ true).borel} (D : AttachedDatum P.pair)
    {pair : RationalOppositePair T (B₀ true).borel (B₀ false).borel}
    {hG : IsReductive G} {hT : IsTorus T.group} {hmax : IsGeometricallyMaximal T}
    {A₀ : AdditiveLine F} {A : AdditiveLine K}
    {U : RootSubgroupFamily P.pair.T} {p : Pinning A P.pair U}
    {a : (groupBaseChange F K).obj A₀.group ≅ A.group}
    {ω : Gal(K/F) →* Aut D.toBased} {I : Set (Root P.pair.T)} {L : RationalStandardFace D I}
    (d : InducedFaceData D (L := L) (pair := pair) (hG := hG) (hT := hT) (hmax := hmax) p a ω) :
    Prop :=
  ∃ O : OrbitLevi F, O.G = G ∧ HEq O.B B₀ ∧ HEq O.T T ∧
    HEq O.L L.limit.centralizer ∧ HEq O.deriv L.derived ∧ HEq O.S L.torus ∧
    HEq O.torusMap L.torusMap ∧
    HEq (O.Hpair true).borel d.positive.rational ∧
    HEq (O.Hpair false).borel d.negative.rational ∧
    (∀ s, IsSubgroupOf (O.derivedRadical s) (O.radical s)) ∧
    letI := D.comm
    ∃ S : SplitOrbit O K, HEq S.D D.datum ∧ HEq S.face I ∧ HEq S.rootGroups U ∧
      HEq S.derivedRootGroups d.rootGroups

/-- The unipotent radicals of the actual two intersections are included
scheme-theoretically in the two specified ambient radicals. -/
def RationalFaceAmbientRadicals : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K]
    {G : AffineAlgebraicGroup F} {T : ClosedSubgroup G.val}
    (B : Bool → BorelRadical G) {P : SplitPairOver (K := K) G T (B true).borel}
    (D : AttachedDatum P.pair) (pair : RationalOppositePair T (B true).borel (B false).borel)
    (hG : IsReductive G) (hT : IsTorus T.group) (hmax : IsGeometricallyMaximal T)
    {A₀ : AdditiveLine F} {A : AdditiveLine K}
    {U : RootSubgroupFamily P.pair.T} {p : Pinning A P.pair U}
    {a : (groupBaseChange F K).obj A₀.group ≅ A.group}
    {ω : Gal(K/F) →* Aut D.toBased} {I : Set (Root P.pair.T)} {L : RationalStandardFace D I}
    (d : InducedFaceData D (L := L) (pair := pair) (hG := hG) (hT := hT) (hmax := hmax) p a ω),
    HasSplitAmbientOrbit D d

/-- The Cartan matrix of the actual derived Levi is the inherited principal
submatrix on the selected simple roots. -/
def RationalFaceCartanComparison : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K]
    {G : AffineAlgebraicGroup F} {T B N : ClosedSubgroup G.val} {P : SplitPairOver (K := K) G T B}
    (D : AttachedDatum P.pair) {pair : RationalOppositePair T B N}
    {hG : IsReductive G} {hT : IsTorus T.group} {hmax : IsGeometricallyMaximal T}
    {A₀ : AdditiveLine F} {A : AdditiveLine K}
    {U : RootSubgroupFamily P.pair.T} {p : Pinning A P.pair U}
    {a : (groupBaseChange F K).obj A₀.group ≅ A.group}
    {ω : Gal(K/F) →* Aut D.toBased} {I : Set (Root P.pair.T)} {L : RationalStandardFace D I}
    (d : InducedFaceData D (L := L) (pair := pair) (hG := hG) (hT := hT) (hmax := hmax) p a ω),
    letI := D.comm
    letI := d.posDatum.comm
    ∃ v : I ≃ d.posDatum.base.support,
      (∀ (i : I) (α : ↥(leviRoots D.datum I)), i.val = α.val → (v i).val = d.roots α) ∧
      ∀ i j, d.posDatum.datum.rootDatum.pairing (v i).val (v j).val =
        D.datum.rootDatum.pairing i.val j.val

open QuasiSplitOrbitTorusProduct (CocharacterLattice OrbitTorusDecomposition)

/-- The multiplication decomposition for the actual embedded tori of all
rational standard orbit Levis, with the orbit field of each summand. -/
def RationalOrbitTorusProduct : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (G : AffineAlgebraicGroup F) (T B : ClosedSubgroup G.val) (P : SplitPairOver (K := K) G T B)
    (D : AttachedDatum P.pair) (e : MultiplicativeComparison F K) (ω : Gal(K/F) →* Aut D.toBased),
    IsReductive G → IsTorus T.group → IsGeometricallyMaximal T →
    IsSemisimple P.pair.G → GeometricallySimplyConnected P.pair.G →
    PreservesUnits e → IsActualDiagramAction D e ω →
    letI := D.comm
    let ρ : Gal(K/F) →* Equiv.Perm D.base.support := (simplePermutation D).comp ω
    letI : MulAction Gal(K/F) D.base.support := MulAction.compHom D.base.support ρ
    let O := MulAction.orbitRel.Quotient Gal(K/F) D.base.support
    let q : D.base.support → O := Quotient.mk (MulAction.orbitRel Gal(K/F) D.base.support)
    let I (o : O) : Set (Root P.pair.T) := Subtype.val '' {i | q i = o}
    ∃ (L : ∀ o, RationalStandardFace D (I o))
      (b : Module.Basis D.base.support ℤ (CocharacterLattice K (closedSubgroupAlgebraicGroup T)))
      (c : D.toBased.Y ≃ₗ[ℤ] CocharacterLattice K (closedSubgroupAlgebraicGroup T)),
      (∀ i, b i = c (D.datum.rootDatum.coroot i.val)) ∧
      (∀ o, (L o).scalar = e) ∧
      haveI := D.datum.finiteRoots
      OrbitTorusDecomposition ρ (closedSubgroupAlgebraicGroup T) b
        (fun o => (L o).embeddedTorus D)

/-- Existence of the rational standard Levi, the actual derived torus and
its split comparison for any stable face. -/
def RationalStandardFaceExists : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (G : AffineAlgebraicGroup F) (T B : ClosedSubgroup G.val) (P : SplitPairOver (K := K) G T B)
    (D : AttachedDatum P.pair) (e : MultiplicativeComparison F K) (ω : Gal(K/F) →* Aut D.toBased),
    IsReductive G → IsTorus T.group → IsGeometricallyMaximal T →
    IsSemisimple P.pair.G → GeometricallySimplyConnected P.pair.G →
    PreservesUnits e → IsActualDiagramAction D e ω →
    letI := D.comm
    ∀ I : Set (Root P.pair.T), I ⊆ D.base.support →
      (∀ (g : Gal(K/F)) (i : Root P.pair.T), (ω g).asIso.hom.val.indexEquiv i ∈ I ↔ i ∈ I) →
      ∃ L : RationalStandardFace D I, L.scalar = e

/-- Absolute almost simplicity and geometric simple connectedness give the
irreducible Cartan classification on the actual datum over the chosen
finite splitting field. -/
def AbsoluteClassificationOfSplitPair : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {G : AffineAlgebraicGroup F} {T B : ClosedSubgroup G.val}
    (P : SplitPairOver (K := K) G T B) (D : AttachedDatum P.pair),
    AbsoluteDynkinTypes.IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G →
    IsSemisimple P.pair.G ∧ GeometricallySimplyConnected P.pair.G ∧ ClassifiedDatum D

/-- The standard orbit Levis in the specified quasi-split pair, including
their induced pinnings, radical inclusions and embedded torus product. -/
def RationalOrbitLeviStructure : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (G : AffineAlgebraicGroup F) (T : ClosedSubgroup G.val) (B : Bool → BorelRadical G)
    (P : SplitPairOver (K := K) G T (B true).borel) (D : AttachedDatum P.pair)
    (pair : RationalOppositePair T (B true).borel (B false).borel)
    (hG : IsReductive G) (hT : IsTorus T.group) (hmax : IsGeometricallyMaximal T),
    AbsoluteDynkinTypes.IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G →
    ∀ {A₀ : AdditiveLine F} {A : AdditiveLine K} (U : RootSubgroupFamily P.pair.T)
      (p : Pinning A P.pair U) (a : (groupBaseChange F K).obj A₀.group ≅ A.group)
      (m : MultiplicativeComparison F K) (ω : Gal(K/F) →* Aut D.toBased),
    PreservesUnits m → IsAmbientPinnedAction D p a m ω →
    letI := D.comm
    let ρ : Gal(K/F) →* Equiv.Perm D.base.support := (simplePermutation D).comp ω
    letI : MulAction Gal(K/F) D.base.support := MulAction.compHom D.base.support ρ
    let O := MulAction.orbitRel.Quotient Gal(K/F) D.base.support
    let q : D.base.support → O := Quotient.mk (MulAction.orbitRel Gal(K/F) D.base.support)
    let I (o : O) : Set (Root P.pair.T) := Subtype.val '' {i | q i = o}
    ∃ (L : ∀ o, RationalStandardFace D (I o))
      (b : Module.Basis D.base.support ℤ (CocharacterLattice K (closedSubgroupAlgebraicGroup T)))
      (c : D.toBased.Y ≃ₗ[ℤ] CocharacterLattice K (closedSubgroupAlgebraicGroup T)),
      (∀ i, b i = c (D.datum.rootDatum.coroot i.val)) ∧
      (∀ o, (L o).scalar = m) ∧
      (haveI := D.datum.finiteRoots
       OrbitTorusDecomposition ρ (closedSubgroupAlgebraicGroup T) b (fun o => (L o).embeddedTorus D)) ∧
      (∀ i, OrbitShape (integralCartan D.datum.rootDatum D.base) ρ i) ∧
      ∀ o, ∃ d : InducedFaceData D (L := L o) (pair := pair) (hG := hG) (hT := hT)
        (hmax := hmax) p a ω, HasSplitAmbientOrbit D d

open AdjointBorelCohomology (PinnedTwist)
open AdjointCocharacters (coordinateHopf)
open AutomorphismSequence (forgetPinning)
open QuasiSplitOrbitPinnedModels (PinnedOrbitDescent)

/-- A comparison of the actual schemes and their embedded Borel and torus
gives the corresponding pinned descent comparison of the coordinate Hopf
algebras. -/
def PinnedTwistFromSchemeComparison : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K]
    {A₀ : AdditiveLine F} (P₀ : PinnedGroup A₀) (D₀ : AttachedDatum P₀.pair)
    (lift : Aut D₀.toBased ≃* Aut P₀) {H : AffineAlgebraicGroup F} (B S : ClosedSubgroup H.val)
    (ω₀ : Gal(K/F) →* Aut D₀.toBased),
    let C := groupBaseChange F K
    ∀ (g : C.obj H.val ≅ C.obj P₀.pair.G.val)
      (b : C.obj B.group ≅ C.obj P₀.pair.B.group) (t : C.obj S.group ≅ C.obj P₀.pair.T.group),
      b.hom ≫ C.map P₀.pair.B.inclusion = C.map B.inclusion ≫ g.hom →
      t.hom ≫ C.map P₀.pair.T.inclusion = C.map S.inclusion ≫ g.hom →
      (∀ σ : Gal(K/F),
        let f := (Functor.mapAut P₀ (forgetPinning (A := A₀)) (lift (ω₀ σ))).asIso.inv
        coefficientAction σ H.val ≫ g.hom.hom.hom.left =
          g.hom.hom.hom.left ≫ (C.map f).hom.hom.left ≫ coefficientAction σ P₀.pair.G.val) →
      ∃ d : PinnedTwist (P := P₀) K D₀ lift B S, d.outer = ω₀ ∧
        ∀ (a : ∀ U : HopfAlgebraCategory F,
          specGroup (extendedHopf K U) ≅ C.obj (specGroup U)),
          Descent.Forms.IsScalarExtensionComparison a →
          (((a (coordinateHopf H) ≪≫ C.mapIso (AdjointCocharacters.coordinateHopfIso H)).symm ≪≫
              (hopfSpec (CommRingCat.of K)).mapIso d.groupIso.op) ≪≫
            (a (coordinateHopf P₀.pair.G) ≪≫
              C.mapIso (AdjointCocharacters.coordinateHopfIso P₀.pair.G))) = g

open Pinning (BasedRootDatum)
open IntegralSemisimpleModel (Model fibre)
open RationalRealization (Realization)

section IntegralMarks
open CharacterPairing (characterValue)

open AdjointRepresentation (GroupPoints)
open IntegralSemisimpleModel (Integers TorusValues torusPoint splitTorus forgetFibrePoint)

attribute [local instance] IntegralSemisimpleModel.integerAlgebra

/-- The coordinates of an integral pinned realization are the actual
scalar extensions of the marked root morphisms. -/
def IntegralFibreRootMaps : Prop :=
  ∀ (D : BasedRootDatum.{u}) (M : Model D) (k : Type u) [Field k],
    ∃ (A : AdditiveLine k) (R : Realization D A)
      (g : (fibre k).obj M.group ≅ R.pinned.pair.G.val)
      (t : (fibre k).obj (IntegralSemisimpleModel.splitTorus D) ≅ R.pinned.pair.T.group)
      (a : A.group ≅ (fibre k).obj M.line.group)
      (x : ∀ i : D.I, Pinning.RootCoordinate A R.pinned.pair.T
        (R.pinned.roots (R.datumIso.val.indexEquiv i)).val (R.datumIso.val.indexEquiv i).val),
      (fibre k).map M.torus ≫ g.hom = t.hom ≫ R.pinned.pair.T.inclusion ∧
      (∀ i : D.base.support, x i.val = R.pinned.pin (R.simpleRoot i)) ∧
      (∀ (S : TestAlgebra k) (s : GroupPoints ((fibre k).obj (splitTorus D)) S)
          (v : TorusValues D (CommAlgCat.of Integers.{u} S)),
        forgetFibrePoint (splitTorus D) S s = torusPoint D (CommAlgCat.of Integers.{u} S) v →
        ∀ x : D.X, characterValue (Additive.toMul (R.datumIso.val.weightEquiv x)) S
          (s ≫ t.hom.hom.hom) = (v (Multiplicative.ofAdd x) : S)) ∧
      ∀ i : D.I,
        (x i).val.hom ≫ (R.pinned.roots (R.datumIso.val.indexEquiv i)).val.inclusion =
          a.hom ≫ (fibre k).map (M.root i) ≫ g.hom

/-- The integral pinned model compares its two field fibres, with the
given torus and labelled simple root maps. -/
def IntegralSplitComparison : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] (D : BasedRootDatum.{u}),
    let C := groupBaseChange F K
    ∃ (A₀ : AdditiveLine F) (A : AdditiveLine K) (R₀ : Realization D A₀)
      (R : Realization D A) (g : R.pinned.pair.G.val ≅ C.obj R₀.pinned.pair.G.val)
      (t : R.pinned.pair.T.group ≅ C.obj R₀.pinned.pair.T.group) (a : A.group ≅ C.obj A₀.group),
      ∃ b : R.pinned.pair.B.group ≅ C.obj R₀.pinned.pair.B.group,
        R.pinned.pair.T.inclusion ≫ g.hom = t.hom ≫ C.map R₀.pinned.pair.T.inclusion ∧
        R.pinned.pair.B.inclusion ≫ g.hom = b.hom ≫ C.map R₀.pinned.pair.B.inclusion ∧
        (∀ i : D.base.support, R.rootMap i ≫ g.hom = a.hom ≫ C.map (R₀.rootMap i)) ∧
        letI := R.attached.comm
        letI := R₀.attached.comm
        ∀ (m : MultiplicativeComparison F K), PreservesUnits m → ∀ y : D.Y,
          (R.datumIso.val.coweightEquiv.symm y).toMul ≫ t.hom =
            m.hom ≫ C.map (R₀.datumIso.val.coweightEquiv.symm y).toMul

end IntegralMarks

/-- A Cartan permutation action on a simply connected semisimple datum
lifts to the same action on its actual paired lattices and roots. -/
def CartanActionLift : Prop :=
  ∀ {Γ : Type u} [Group Γ] (D : BasedRootDatum.{u}),
    Submodule.span ℤ (Set.range D.datum.coroot) = ⊤ →
    ∀ (ρ : Γ →* Equiv.Perm D.base.support),
      (∀ g, PreservesCartan (integralCartan D.datum D.base) (integralCartan D.datum D.base) (ρ g)) →
      ∃ θ : Γ →* Aut D,
        ∀ g (i : D.base.support), (θ g).asIso.hom.val.indexEquiv i.val = (ρ g i).val

/-- The labelled simple diagram action on the actual derived face datum. -/
def RationalFaceDiagram : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K]
    {G : AffineAlgebraicGroup F} {T B N : ClosedSubgroup G.val} {P : SplitPairOver (K := K) G T B}
    (D : AttachedDatum P.pair) {pair : RationalOppositePair T B N}
    {hG : IsReductive G} {hT : IsTorus T.group} {hmax : IsGeometricallyMaximal T}
    {A₀ : AdditiveLine F} {A : AdditiveLine K}
    {U : RootSubgroupFamily P.pair.T} {p : Pinning A P.pair U}
    {a : (groupBaseChange F K).obj A₀.group ≅ A.group}
    {ω : Gal(K/F) →* Aut D.toBased} {I : Set (Root P.pair.T)} {L : RationalStandardFace D I}
    (d : InducedFaceData D (L := L) (pair := pair) (hG := hG) (hT := hT) (hmax := hmax) p a ω),
    ∀ (hs : ∀ (σ : Gal(K/F)) (α : Root P.pair.T), diagramRoot ω σ α ∈ I ↔ α ∈ I),
    letI := D.comm
    letI := d.posDatum.comm
    ∃ (v : I ≃ d.posDatum.base.support) (action : Gal(K/F) →* Aut d.posDatum.toBased),
      (∀ (i : I) (α : ↥(leviRoots D.datum I)), i.val = α.val → (v i).val = d.roots α) ∧
      (∀ i j, d.posDatum.datum.rootDatum.pairing (v i).val (v j).val =
        D.datum.rootDatum.pairing i.val j.val) ∧
      ∀ (σ : Gal(K/F)) (i : I),
        (action σ).asIso.hom.val.indexEquiv (v i).val =
          (v ⟨diagramRoot ω σ i.val, (hs σ i.val).mpr i.property⟩).val

/-- The Cartan entries on the actual orbit face are those of the product
of rank-one diagrams, or those of the two consecutively labelled vertices
of a single A₂. -/
def OrbitFaceCartan : Prop :=
  ∀ {k : Type u} [Field k] {P : SplitBorelPair k} (D : AttachedDatum P),
    ClassifiedDatum D → ∀ {Γ : Type u} [Group Γ] (ω : Γ →* Aut D.toBased)
      (i : D.toBased.base.support),
    letI := D.comm
    let I := orbitRootSet D ω i
    (∀ a b : I, a ≠ b → D.datum.rootDatum.pairing a.val b.val = 0) ∨
      ∃ j : Fin 2 ≃ I, ∀ a b : Fin 2,
        D.datum.rootDatum.pairing (j a).val (j b).val = if a = b then 2 else -1

open QuasiSplitOrbitAmbientWords (RationalPoints extendPoint onRational IsFaceLongest)
open BorelsAndChambers (IsRegular)
open SimpleRoots (IsBaseFor evaluate)

/-- A rational point of the derived face Levi that normalizes its torus
over the splitting field normalizes the full ambient torus over the ground field. -/
def RationalFaceNormalizerTransfer : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K]
    {G : AffineAlgebraicGroup F} {T B : ClosedSubgroup G.val} {P : SplitPairOver (K := K) G T B}
    (D : AttachedDatum P.pair) (I : Set (Root P.pair.T)) (L : RationalStandardFace D I)
    (x : RationalPoints L.derived.group),
    Normalizes ((groupBaseChange F K).map L.torus.inclusion) (extendPoint (K := K) L.derived.group x) →
    Normalizes T.inclusion (onRational (L.derived.inclusion ≫ L.limit.centralizer.inclusion) x)

/-- A label in the actual absolute Weyl group is the face longest element
when its conjugation fixes the defining face cocharacter and sends the
simple coroots of the face to the negatives of a permutation of them. -/
def LongestFaceLabelFromCoroots : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K]
    {O : OrbitLevi F} (A : SplitOrbit O K),
    letI := A.comm
    ∀ (c lam : Cocharacter A.T.group),
      IsRegular A.T c → IsBaseFor A.rootDatum (evaluate A.D c) A.base →
      HasFace A.base A.face lam →
      ∀ (w : A.rootDatum.weylGroup),
        lam ≫ (A.W.image.conjugation (A.W.labelEquiv w)).hom = lam →
        ∀ π : Equiv.Perm A.face,
          (∀ i : A.face,
            w.val.coweightEquiv.symm (A.rootDatum.coroot i.val) = - A.rootDatum.coroot (π i).val) →
          IsFaceLongest A w

end OrbitAssembly

section FacePinnedDescent

open Pinning (PinnedGroup AttachedDatum SimpleRoot Pinning)
open RootGroups (AdditiveLine)
open QuasiSplitOrbitDerivedRoots (pinnedRootMap diagramRoot)
open GeometricRadicals (IsReductive IsTorus IsSemisimple)
open RankOneFlag (IsGeometricallyMaximal)
open OrderedRootProducts (RootSubgroupFamily)
open AbstractPairing (Root)
open AdjointBorelCohomology (PinnedTwist)
open RationalRealization (Realization)
open StandardParabolicLevi (leviRoots)
open SimplyConnectedLattice (GeometricallySimplyConnected)

def simpleRootsOfAttachedDatum {k : Type u} [Field k] {A : AdditiveLine k}
    (Q : PinnedGroup A) (D : AttachedDatum Q.pair) : D.toBased.base.support ≃ SimpleRoot Q.pair :=
  Equiv.subtypeEquivRight (fun α => D.simple_iff α)

def simpleCorootOfAttachedDatum {k : Type u} [Field k] {A : AdditiveLine k}
    (Q : PinnedGroup A) (D : AttachedDatum Q.pair) (j : SimpleRoot Q.pair) :
    CharacterDescent.Cocharacter Q.pair.T.group :=
  letI := D.comm
  (D.datum.rootDatum.coroot j.val).toMul

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
variable {G : AffineAlgebraicGroup F} {T B N : ClosedSubgroup G.val}
variable {P : SplitPairOver (K := K) G T B}
variable {D : AttachedDatum P.pair} {I : Set (Root P.pair.T)} {L : RationalStandardFace D I}
variable {pair : RationalOppositePair T B N}
variable {hG : IsReductive G} {hT : IsTorus T.group} {hmax : IsGeometricallyMaximal T}
variable {A₀ : AdditiveLine F} {A : AdditiveLine K}
variable {U : RootSubgroupFamily P.pair.T} {p : Pinning A P.pair U}
variable {a : (groupBaseChange F K).obj A₀.group ≅ A.group} {ω : Gal(K/F) →* Aut D.toBased}

/-- Pinned comparison of the actual rational face with a split realization of
its attached datum. The scalar comparison keeps the same root labels and
the same embedded coroots. -/
structure FacePinnedForm
    (d : InducedFaceData D (L := L) (pair := pair) (hG := hG) (hT := hT) (hmax := hmax) p a ω) where
  vertices : letI := d.posDatum.comm; I ≃ d.posDatum.base.support
  diagram : Gal(K/F) →* Aut d.posDatum.toBased
  vertexRoot : letI := D.comm; letI := d.posDatum.comm; ∀ (i : I) (α : ↥(leviRoots D.datum I)),
    i.val = α.val → (vertices i).val = d.roots α
  pairings : letI := D.comm; letI := d.posDatum.comm; ∀ i j,
    d.posDatum.datum.rootDatum.pairing (vertices i).val (vertices j).val =
      D.datum.rootDatum.pairing i.val j.val
  vertexAction : letI := d.posDatum.comm; ∀ (σ : Gal(K/F)) (i j : I), diagramRoot ω σ i.val = j.val →
    (diagram σ).asIso.hom.val.indexEquiv (vertices i).val = (vertices j).val
  line : AdditiveLine F
  splitModel : Realization d.posDatum.toBased line
  lift : Aut splitModel.attached.toBased ≃* Aut splitModel.pinned
  descent : PinnedTwist (P := splitModel.pinned) K splitModel.attached lift d.positive.rational L.torus
  groupComparison : (groupBaseChange F K).obj (L.rationalFace D pair hG hT hmax).group.val ≅
    (groupBaseChange F K).obj splitModel.pinned.pair.G.val
  torusComparison : (groupBaseChange F K).obj L.torus.group ≅
    (groupBaseChange F K).obj splitModel.pinned.pair.T.group
  torusSquare : let C := groupBaseChange F K
    C.map L.torus.inclusion ≫ groupComparison.hom =
      torusComparison.hom ≫ C.map splitModel.pinned.pair.T.inclusion
  simpleAction : ∀ (σ : Gal(K/F)) (i : d.posDatum.toBased.base.support),
    Specs.Pinning.transportCharacter (lift (descent.outer σ)).asIso.hom.torus
      (splitModel.simpleRoot i).val.val =
      (splitModel.simpleRoot (simplePermutation d.posDatum (diagram σ) i)).val.val
  normalizedLine : A₀.group ≅ line.group
  rootMap : let Q : PinnedGroup A := ⟨d.positive.pair d.reductive, d.rootGroups, d.pinning⟩
    ∀ i : d.posDatum.toBased.base.support,
      pinnedRootMap Q.pin (simpleRootsOfAttachedDatum Q d.posDatum i) ≫ groupComparison.hom =
        a.inv ≫ (groupBaseChange F K).map (normalizedLine.hom ≫ splitModel.rootMap i)
  coroot : let Q : PinnedGroup A := ⟨d.positive.pair d.reductive, d.rootGroups, d.pinning⟩
    ∀ i : d.posDatum.toBased.base.support,
      simpleCorootOfAttachedDatum Q d.posDatum (simpleRootsOfAttachedDatum Q d.posDatum i) ≫ torusComparison.hom =
        L.scalar.hom ≫ (groupBaseChange F K).map
          (simpleCorootOfAttachedDatum splitModel.pinned splitModel.attached (splitModel.simpleRoot i))
  comparison_eq : let C := groupBaseChange F K
    let H := (L.rationalFace D pair hG hT hmax).group
    ∀ (t : ∀ V : HopfAlgebraCategory F, specGroup (extendedHopf K V) ≅ C.obj (specGroup V)),
      Descent.Forms.IsScalarExtensionComparison t →
      (((t (Specs.AdjointCocharacters.coordinateHopf H) ≪≫
          C.mapIso (Specs.AdjointCocharacters.coordinateHopfIso H)).symm ≪≫
          (hopfSpec (CommRingCat.of K)).mapIso descent.groupIso.op) ≪≫
        (t (Specs.AdjointCocharacters.coordinateHopf splitModel.pinned.pair.G) ≪≫
          C.mapIso (Specs.AdjointCocharacters.coordinateHopfIso splitModel.pinned.pair.G))) =
        groupComparison
  splitSemisimple : IsSemisimple splitModel.pinned.pair.G
  splitSimplyConnected : GeometricallySimplyConnected splitModel.pinned.pair.G

/-- Descent of the actual induced pinned face, with the inherited diagram action. -/
def RationalFacePinnedForm : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K]
    {G : AffineAlgebraicGroup F} {T B N : ClosedSubgroup G.val}
    {P : SplitPairOver (K := K) G T B} {D : AttachedDatum P.pair}
    {I : Set (Root P.pair.T)} {L : RationalStandardFace D I}
    {pair : RationalOppositePair T B N}
    {hG : IsReductive G} {hT : IsTorus T.group} {hmax : IsGeometricallyMaximal T}
    {A₀ : AdditiveLine F} {A : AdditiveLine K} {U : RootSubgroupFamily P.pair.T}
    {p : Pinning A P.pair U} {a : (groupBaseChange F K).obj A₀.group ≅ A.group}
    {ω : Gal(K/F) →* Aut D.toBased}
    (d : InducedFaceData D (L := L) (pair := pair) (hG := hG) (hT := hT) (hmax := hmax) p a ω),
    PreservesUnits L.scalar →
    (∀ (σ : Gal(K/F)) (α : Root P.pair.T), diagramRoot ω σ α ∈ I ↔ α ∈ I) →
    Nonempty (FacePinnedForm d)

open GeometricBorelConjugacy (subgroupOfSubgroup)
open GeometricRadicals (IsUnipotentRadical)
open Unipotent (closedSubgroupAlgebraicGroup)
open QuasiSplitOrbitPinnedModels (PinnedOrbitDescent)

/-- The radicals of the two Borels induced on the actual derived Levi. -/
structure FaceRadicals
    (d : InducedFaceData D (L := L) (pair := pair) (hG := hG) (hT := hT) (hmax := hmax) p a ω) where
  positive : ClosedSubgroup d.positive.rational.group
  negative : ClosedSubgroup d.negative.rational.group
  isPositive : IsUnipotentRadical (closedSubgroupAlgebraicGroup d.positive.rational) positive
  isNegative : IsUnipotentRadical (closedSubgroupAlgebraicGroup d.negative.rational) negative

/-- The ground split model's simple roots retain their labels under realization. -/
noncomputable def realizationSimpleEquiv {k : Type u} [Field k] {A' : AdditiveLine k}
    {E : Specs.Pinning.BasedRootDatum.{u}} (M : Realization E A') :
    E.base.support ≃ SimpleRoot M.pinned.pair :=
  Equiv.ofBijective M.simpleRoot (by
    constructor
    · intro i j h
      exact Subtype.ext (M.datumIso.val.indexEquiv.injective (congrArg Subtype.val h))
    · intro j
      let _ := M.attached.comm
      have hj : j.val ∈ (M.attached.base.support : Set (AbstractPairing.Root M.pinned.pair.T)) :=
        (M.attached.simple_iff _).mpr j.property
      have he : M.datumIso.val.indexEquiv '' (E.base.support : Set E.I) =
          (M.attached.base.support : Set (AbstractPairing.Root M.pinned.pair.T)) :=
        M.datumIso.property
      rw [← he] at hj
      obtain ⟨i, hi, he⟩ := hj
      exact ⟨⟨i, hi⟩, Subtype.ext he⟩)

variable {d : InducedFaceData D (L := L) (pair := pair) (hG := hG) (hT := hT) (hmax := hmax) p a ω}

/-- The simple roots of the model are indexed by the actual ambient face. -/
noncomputable def FacePinnedForm.modelVertices (q : FacePinnedForm d) :
    I ≃ SimpleRoot q.splitModel.pinned.pair :=
  q.vertices.trans (realizationSimpleEquiv q.splitModel)

noncomputable def FacePinnedForm.modelAction (q : FacePinnedForm d) :
    Gal(K/F) →* Equiv.Perm (SimpleRoot q.splitModel.pinned.pair) :=
  (realizationSimpleEquiv q.splitModel).permCongrHom.toMonoidHom.comp
    ((simplePermutation d.posDatum).comp q.diagram)

/-- The marked group supplied to pinned rank-one descent is the actual
derived face group with the induced opposite Borels and their radicals. -/
noncomputable def FacePinnedForm.orbitDescent (q : FacePinnedForm d) (V : FaceRadicals d)
    (hop : UnipotentRadicalIntersection.IsSchemeIntersection
      {d.positive.rational, d.negative.rational} L.torus)
    (hact : ∀ σ j, Specs.Pinning.transportCharacter
      (q.lift (q.descent.outer σ)).asIso.hom.torus j.val.val = (q.modelAction σ j).val.val)
    (htrans : ∀ i j, ∃ σ, q.modelAction σ i = j) : PinnedOrbitDescent F K where
  G := (L.rationalFace D pair hG hT hmax).group
  semisimple := L.semisimple
  simplyConnected := d.simplyConnected
  T := L.torus
  Bpos := d.positive.rational
  Bneg := d.negative.rational
  torus := L.isTorus
  maximal := L.maximal
  isBorelPos := d.positive.isKBorel
  isBorelNeg := d.negative.isKBorel
  opposite := hop
  Upos := V.positive
  Uneg := V.negative
  isRadicalPos := V.isPositive
  isRadicalNeg := V.isNegative
  A := q.line
  P := q.splitModel.pinned
  D := q.splitModel.attached
  splitSemisimple := q.splitSemisimple
  splitSimplyConnected := q.splitSimplyConnected
  lift := q.lift
  descent := q.descent
  action := q.modelAction
  action_eq := hact
  transitive := htrans


open QuasiSplitOrbitPinnedModels
  (MatrixMark specialLinearPointsOfSize)

section RankOneModels

open Matrix
open Specs.RootGroups (rootPoint)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open LinearAlgebraicGroups.WeilRestriction (extendScalars)
open CategoryTheory.Limits

/-- The marked Weil restriction from the stabilizer field of a simple root. -/
def HasOrthogonalOrbitModel (d : PinnedOrbitDescent F K) (i : SimpleRoot d.P.pair) : Prop :=
  let E := QuasiSplitOrbitPinnedModels.orbitField d.action i
    ∃ (W : AffineAlgebraicGroup F) (f : d.G.val ≅ W.val)
      (m : (groupPointsFunctor F).obj W.val ≅ extendScalars F E ⋙ specialLinearPointsOfSize 2 E)
      (emb : (SimpleRoot d.P.pair) → (E →ₐ[F] K))
      (t : ∀ C : HopfAlgebraCategory F,
        specGroup (extendedHopf K C) ≅ (groupBaseChange F K).obj (specGroup C))
      (p : ∀ R : TestAlgebra K, AdjointRepresentation.GroupPoints ((groupBaseChange F K).obj d.P.pair.G.val) R ≃*
        ((SimpleRoot d.P.pair) → SpecialLinearGroup (Fin 2) R)),
      Descent.Forms.IsScalarExtensionComparison t ∧
      d.MatchesMarks (fun R x => m.hom.app R (((groupPointsFunctor F).map f.hom).app R x)) ∧
      (∀ (σ : Gal(K/F)) (y : E), emb (d.action σ i) y = σ y.val) ∧
      (∀ {R S : TestAlgebra K} (a : R ⟶ S) (j : SimpleRoot d.P.pair)
          (x : AdjointRepresentation.GroupPoints
            ((groupBaseChange F K).obj d.P.pair.G.val) R),
        p S (mapPoints a x) j = SpecialLinearGroup.map a.hom.toRingHom (p R x j)) ∧
      (∀ (R : TestAlgebra K) (j : (SimpleRoot d.P.pair))
        (x : AdjointRepresentation.GroupPoints ((groupBaseChange F K).obj d.G.val) R),
        let R₀ := (restrictTestAlgebra F K).obj R
        letI : Algebra K R₀ := inferInstanceAs (Algebra K R)
        letI : IsScalarTower F K R₀ := IsScalarTower.of_algebraMap_eq' rfl
        let f₀ := Algebra.TensorProduct.lift (AlgHom.id F R₀)
          (((Algebra.ofId K R₀).restrictScalars F).comp (emb j)) (fun _ _ => Commute.all _ _)
        p R (((groupPointsFunctor K).map (d.trivialization t).hom).app R x) j =
          SpecialLinearGroup.map f₀.toRingHom (m.hom.app R₀
            (((groupPointsFunctor F).map f.hom).app R₀
              (baseChangePoint F K d.G.val.X R x)))) ∧
      letI := d.D.comm
      ∀ (R : TestAlgebra K) (j : (SimpleRoot d.P.pair)) (a : R) (v : Rˣ),
        let R₀ := (restrictTestAlgebra F K).obj R
        let α := j
        let c := Additive.toMul (d.D.datum.rootDatum.coroot j.val)
        let x := rootPoint ((d.P.pin α).val.hom ≫ (d.P.roots α.val).val.inclusion) R₀ a
        let y := cocharacterPoint c R₀ v ≫ d.P.pair.T.inclusion.hom.hom
        ∀ x' y', baseChangePoint F K d.P.pair.G.val.X R x' = x →
          baseChangePoint F K d.P.pair.G.val.X R y' = y →
          (p R x' j).val = 1 + Matrix.single 0 1 a ∧
          (p R y' j).val = Matrix.diagonal ![(v : R), (↑v⁻¹ : R)] ∧
          ∀ l : SimpleRoot d.P.pair, l ≠ j → p R x' l = 1 ∧ p R y' l = 1

/-- The marked determinant-one group of the hyperbolic Hermitian form over
the fixed field of the kernel of the actual two-vertex action. -/
def HasAdjacentOrbitModel (d : PinnedOrbitDescent F K) (j : Fin 2 ≃ SimpleRoot d.P.pair) : Prop :=
  let E := QuasiSplitOrbitPinnedModels.orbitField (d.adjacentAction j) 0
    ∃ (_ : Algebra.IsQuadraticExtension F E) (_ : Algebra.IsSeparable F E)
      (W : AffineAlgebraicGroup F) (U : ClosedSubgroup W.val)
      (m : (groupPointsFunctor F).obj W.val ≅ extendScalars F E ⋙ QuasiSplitOrbitPinnedModels.specialLinearThreePoints E)
      (f : d.G.val ≅ U.group)
      (t : ∀ C : HopfAlgebraCategory F,
        specGroup (extendedHopf K C) ≅ (groupBaseChange F K).obj (specGroup C))
      (p : (groupPointsFunctor K).obj ((groupBaseChange F K).obj d.P.pair.G.val) ≅
        QuasiSplitOrbitPinnedModels.specialLinearThreePoints K),
      E = IntermediateField.fixedField d.action.ker ∧
      QuasiSplitOrbitPinnedModels.RepresentsHyperbolicUnitary (E := E) U m ∧
      Descent.Forms.IsScalarExtensionComparison t ∧
      (∀ b, ∀ (R : TestAlgebra F) (x : AdjointRepresentation.GroupPoints d.G.val R),
        b.Holds (m.hom.app R (((groupPointsFunctor F).map (f.hom ≫ U.inclusion)).app R x)) ↔
          x ∈ SubgroupSections (d.mark b) ((testSpec F).obj (Opposite.op R))) ∧
      (∀ (R : TestAlgebra K)
        (x : AdjointRepresentation.GroupPoints ((groupBaseChange F K).obj d.G.val) R),
        let R₀ := (restrictTestAlgebra F K).obj R
        letI : Algebra K R₀ := inferInstanceAs (Algebra K R)
        letI : IsScalarTower F K R₀ := IsScalarTower.of_algebraMap_eq' rfl
        let f₀ := Algebra.TensorProduct.lift (AlgHom.id F R₀)
          (((Algebra.ofId K R₀).restrictScalars F).comp E.val) (fun _ _ => Commute.all _ _)
        p.hom.app R (((groupPointsFunctor K).map (d.trivialization t).hom).app R x) =
          SpecialLinearGroup.map f₀.toRingHom (m.hom.app R₀
            (((groupPointsFunctor F).map (f.hom ≫ U.inclusion)).app R₀
              (baseChangePoint F K d.G.val.X R x)))) ∧
      letI := d.D.comm
      ∀ (R : TestAlgebra K) (i : Fin 2) (a : R) (v : Rˣ),
        let R₀ := (restrictTestAlgebra F K).obj R
        let α := j i
        let c := Additive.toMul (d.D.datum.rootDatum.coroot (j i).val)
        let x := rootPoint ((d.P.pin α).val.hom ≫ (d.P.roots α.val).val.inclusion) R₀ a
        let y := cocharacterPoint c R₀ v ≫ d.P.pair.T.inclusion.hom.hom
        ∀ x' y', baseChangePoint F K d.P.pair.G.val.X R x' = x →
          baseChangePoint F K d.P.pair.G.val.X R y' = y →
          (p.hom.app R x').val = 1 + Matrix.single i.castSucc i.succ (QuasiSplitOrbitPinnedModels.signedParameter i a) ∧
          p.hom.app R y' = QuasiSplitOrbitPinnedModels.matrixSimpleCoroot i v

/-- The two comparisons of the actual induced face, keeping the labels from
the ambient diagram and the coordinate maps of the split pinned models. -/
def HasRankOneOrbitModel (q : FacePinnedForm d) (V : FaceRadicals d)
    (hop : UnipotentRadicalIntersection.IsSchemeIntersection
      {d.positive.rational, d.negative.rational} L.torus)
    (hact : ∀ σ j, Specs.Pinning.transportCharacter
      (q.lift (q.descent.outer σ)).asIso.hom.torus j.val.val = (q.modelAction σ j).val.val)
    (htrans : ∀ i j, ∃ σ, q.modelAction σ i = j) : Prop :=
  let H := q.orbitDescent V hop hact htrans
  letI := D.comm
  ((∀ i j : I, i ≠ j → D.datum.rootDatum.pairing i.val j.val = 0) ∧
    ∀ i : I, HasOrthogonalOrbitModel H (q.modelVertices i)) ∨
  ∃ j : Fin 2 ≃ I,
    (∀ a b, D.datum.rootDatum.pairing (j a).val (j b).val = if a = b then 2 else -1) ∧
    HasAdjacentOrbitModel H (j.trans q.modelVertices)

/-- The actual derived Levi attached to a simple-root orbit has the
rank-one matrix model of that orbit. -/
def RationalOrbitRankOneModels : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    {G : AffineAlgebraicGroup F} {T B N : ClosedSubgroup G.val}
    {P : SplitPairOver (K := K) G T B} {D : AttachedDatum P.pair}
    {pair : RationalOppositePair T B N}
    {hG : IsReductive G} {hT : IsTorus T.group} {hmax : IsGeometricallyMaximal T}
    {A₀ : AdditiveLine F} {A : AdditiveLine K} {U : RootSubgroupFamily P.pair.T}
    {p : Pinning A P.pair U} {a : (groupBaseChange F K).obj A₀.group ≅ A.group}
    {ω : Gal(K/F) →* Aut D.toBased} (i : D.toBased.base.support)
    {L : RationalStandardFace D (orbitRootSet D ω i)}
    (d : InducedFaceData D (L := L) (pair := pair) (hG := hG) (hT := hT) (hmax := hmax) p a ω),
    ClassifiedDatum D → PreservesUnits L.scalar →
    ∃ (q : FacePinnedForm d) (V : FaceRadicals d) (hop : _) (hact : _) (htrans : _),
      HasRankOneOrbitModel q V hop hact htrans

end RankOneModels

section OrbitWords

open CategoryTheory.CartesianMonoidalCategory
open QuasiSplitOrbitAmbientWords (RationalPoints BorelRadical onRational extendPoint)
open BorelsAndChambers (IsRegular)
open SimpleRoots (IsBaseFor evaluate)
open DatumAndWeyl (Identification)

/-- The subgroup generated by the two specified rational unipotent radicals. -/
def oppositeRadicalWords (B₀ : Bool → BorelRadical G) : Subgroup (RationalPoints G.val) :=
  Subgroup.closure {g | ∃ s, g ∈ (onRational (B₀ s).inAmbient.inclusion).range}

/-- The subgroup of the derived Levi generated by its two rational radicals. -/
def derivedOrbitWords (V : FaceRadicals d) : Subgroup (RationalPoints L.derived.group) :=
  Subgroup.closure {x |
    x ∈ SubgroupSections (subgroupOfSubgroup d.positive.rational V.positive) _ ∨
    x ∈ SubgroupSections (subgroupOfSubgroup d.negative.rational V.negative) _}

/-- Word generation for the embedded orbit torus and a representative of the
longest element in the actual absolute normalizer quotient. -/
def HasOrbitWords (B₀ : Bool → BorelRadical G) (V : FaceRadicals d) : Prop :=
  letI := D.comm
  let Γ := oppositeRadicalWords B₀
  (∀ t : RationalPoints L.torus.group,
    onRational L.torus.inclusion t ∈ derivedOrbitWords V ∧
    onRational (L.torusMap ≫ T.inclusion) t ∈ Γ) ∧
  ∃ (c : Cocharacter P.pair.T.group) (W : Identification D.datum)
    (x : RationalPoints L.derived.group) (w : D.datum.rootDatum.weylGroup)
    (n : RationalPoints W.normalizer.group),
    let g := onRational (L.derived.inclusion ≫ L.limit.centralizer.inclusion) x
    IsRegular P.pair.T c ∧ IsBaseFor D.datum.rootDatum (evaluate D.datum c) D.base ∧
    x ∈ derivedOrbitWords V ∧ g ∈ Γ ∧ Normalizes T.inclusion g ∧
    w ∈ StandardParabolicLevi.parabolicWeylGroup D.datum I ∧
    (∀ j ∈ leviRoots D.datum I, 0 < evaluate D.datum c (D.datum.rootDatum.root j) →
      evaluate D.datum c (w.val.weightEquiv (D.datum.rootDatum.root j)) < 0) ∧
    onRational W.normalizer.inclusion n = extendPoint (K := K) G.val g ∧
    onRational W.quotient n = toUnit _ ≫ W.image.constantGroup.sectionPoint (W.labelEquiv w)

/-- The words and the marked matrix identification use the same derived Levi
and the same two unipotent radicals. -/
def HasMarkedOrbitWords (B₀ : Bool → BorelRadical G)
    (d : InducedFaceData D (L := L) (pair := pair) (hG := hG) (hT := hT) (hmax := hmax) p a ω) : Prop :=
  ∃ (q : FacePinnedForm d) (V : FaceRadicals d) (hop : _) (hact : _) (htrans : _),
    HasRankOneOrbitModel q V hop hact htrans ∧ HasOrbitWords B₀ V

/-- Apply the rank-one words on the orbit Levi of the specified rational pair. -/
def RationalOrbitWords : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [Infinite F]
    [FiniteDimensional F K] [IsGalois F K]
    {G : AffineAlgebraicGroup F} {T : ClosedSubgroup G.val} (B₀ : Bool → BorelRadical G)
    {P : SplitPairOver (K := K) G T (B₀ true).borel} {D : AttachedDatum P.pair}
    {pair : RationalOppositePair T (B₀ true).borel (B₀ false).borel}
    {hG : IsReductive G} {hT : IsTorus T.group} {hmax : IsGeometricallyMaximal T}
    {A₀ : AdditiveLine F} {A : AdditiveLine K} {U : RootSubgroupFamily P.pair.T}
    {p : Pinning A P.pair U} {a : (groupBaseChange F K).obj A₀.group ≅ A.group}
    {ω : Gal(K/F) →* Aut D.toBased} (i : D.toBased.base.support)
    {L : RationalStandardFace D (orbitRootSet D ω i)}
    (d : InducedFaceData D (L := L) (pair := pair) (hG := hG) (hT := hT) (hmax := hmax) p a ω),
    ClassifiedDatum D → PreservesUnits L.scalar → HasMarkedOrbitWords B₀ d

open QuasiSplitOrbitTorusProduct (CocharacterLattice OrbitTorusDecomposition)

/-- The orbit Levis for a fixed opposite rational Borel pair, with their
embedded torus decomposition, marked rank-one forms and rational words. -/
def RationalOrbitLevis : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [Infinite F]
    [FiniteDimensional F K] [IsGalois F K]
    (G : AffineAlgebraicGroup F) (T : ClosedSubgroup G.val) (B : Bool → BorelRadical G)
    (P : SplitPairOver (K := K) G T (B true).borel) (D : AttachedDatum P.pair)
    (pair : RationalOppositePair T (B true).borel (B false).borel)
    (hG : IsReductive G) (hT : IsTorus T.group) (hmax : IsGeometricallyMaximal T),
    AbsoluteDynkinTypes.IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G →
    ∀ {A₀ : AdditiveLine F} {A : AdditiveLine K} (U : RootSubgroupFamily P.pair.T)
      (p : Pinning A P.pair U) (a : (groupBaseChange F K).obj A₀.group ≅ A.group)
      (m : MultiplicativeComparison F K) (ω : Gal(K/F) →* Aut D.toBased),
    PreservesUnits m → IsAmbientPinnedAction D p a m ω →
    letI := D.comm
    let ρ : Gal(K/F) →* Equiv.Perm D.base.support := (simplePermutation D).comp ω
    letI : MulAction Gal(K/F) D.base.support := MulAction.compHom D.base.support ρ
    let O := MulAction.orbitRel.Quotient Gal(K/F) D.base.support
    let q : D.base.support → O := Quotient.mk (MulAction.orbitRel Gal(K/F) D.base.support)
    let I (o : O) : Set (Root P.pair.T) := Subtype.val '' {i | q i = o}
    ∃ (L : ∀ o, RationalStandardFace D (I o))
      (b : Module.Basis D.base.support ℤ (CocharacterLattice K (closedSubgroupAlgebraicGroup T)))
      (c : D.toBased.Y ≃ₗ[ℤ] CocharacterLattice K (closedSubgroupAlgebraicGroup T)),
      (∀ i, b i = c (D.datum.rootDatum.coroot i.val)) ∧
      (∀ o, (L o).scalar = m) ∧
      (haveI := D.datum.finiteRoots
       OrbitTorusDecomposition ρ (closedSubgroupAlgebraicGroup T) b (fun o => (L o).embeddedTorus D)) ∧
      (∀ i, OrbitShape (integralCartan D.datum.rootDatum D.base) ρ i) ∧
      ∀ o, ∃ d : InducedFaceData D (L := L o) (pair := pair) (hG := hG) (hT := hT)
        (hmax := hmax) p a ω,
        HasSplitAmbientOrbit D d ∧ HasMarkedOrbitWords B d

end OrbitWords

end FacePinnedDescent

end

end LinearAlgebraicGroups.Specs.QuasiSplitOrbitLevis
