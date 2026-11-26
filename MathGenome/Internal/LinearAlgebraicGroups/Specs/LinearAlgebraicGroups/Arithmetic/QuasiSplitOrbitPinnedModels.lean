import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.Forms
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.UnitaryRankOne
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SpecialLinearDatum
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.PinnedPairDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.RingTheory.TensorProduct.Pi

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits
open Module
open scoped BigOperators CategoryTheory.MonObj TensorProduct

universe u v w

namespace LinearAlgebraicGroups.Specs.QuasiSplitOrbitPinnedModels

noncomputable section



/-- The orbit of a simple vertex under the action on the chosen based datum. -/
def diagramOrbit {Γ : Type u} {I : Type v} [Group Γ]
    (ρ : Γ →* Equiv.Perm I) (i : I) : Set I :=
  Set.range (fun g => ρ g i)


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

open Matrix.SpecialLinearGroup in
def hyperbolicDual {R : Type v} [CommRing R] : SL₃ R →* SL₃ R where
  toFun := hyperbolicInverseTranspose
  map_one' := by
    apply Subtype.ext
    simp [hyperbolicInverseTranspose, Matrix.submatrix_one_equiv]
  map_mul' a b := by
    apply Subtype.ext
    change ((a * b)⁻¹).val.transpose.submatrix Fin.revPerm Fin.revPerm =
      (a⁻¹).val.transpose.submatrix Fin.revPerm Fin.revPerm *
      (b⁻¹).val.transpose.submatrix Fin.revPerm Fin.revPerm
    rw [_root_.mul_inv_rev, coe_mul, Matrix.transpose_mul, Matrix.submatrix_mul_equiv]

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


/-- In a transitive action on the two adjacent vertices, the field of either
vertex is the separable quadratic extension cut out by the swap. -/
def QuadraticOrbitField : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (ρ : Gal(K/F) →* Equiv.Perm (Fin 2)) (i : Fin 2),
    (∀ j, ∃ σ, ρ σ i = j) →
    let E := orbitField ρ i
    E = IntermediateField.fixedField ρ.ker ∧
    ∃ (_ : Algebra.IsQuadraticExtension F E) (_ : Algebra.IsSeparable F E),
      ∀ (σ : Gal(K/F)) (y : E),
        σ y.val = if ρ σ = 1 then y.val else (UnitaryRankOne.quadraticConjugation F E y).val

end OrbitField
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

end UnitaryScheme

section PinnedComparison

open Pinning (AttachedDatum BasedIso PinnedGroup PinnedIso)
open RootGroups (AdditiveLine)
open SimplyConnectedLattice (corootLattice)

/-- On simply connected split groups, a Cartan relabelling gives a pinned
isomorphism and sends the attached simple coroots to the labelled coroots. -/
def PinnedCartanComparison : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} (P Q : PinnedGroup A)
    (D : AttachedDatum P.pair) (E : AttachedDatum Q.pair),
    letI := D.comm
    letI := E.comm
    corootLattice D = ⊤ → corootLattice E = ⊤ →
    ∀ e : D.base.support ≃ E.base.support,
      AbsoluteDynkinTypes.PreservesCartan
        (RootData.integralCartan D.datum.rootDatum D.base)
        (RootData.integralCartan E.datum.rootDatum E.base) e →
      ∃ f : PinnedIso P Q, ∀ i : D.base.support,
        Pinning.transportCharacter f.torus i.val.val = (e i).val.val ∧
        Additive.toMul (D.datum.rootDatum.coroot i.val) ≫ f.torus.hom =
          Additive.toMul (E.datum.rootDatum.coroot (e i).val)

end PinnedComparison


section EquivariantComparison

open _root_.LinearAlgebraicGroups.Descent (SemilinearAction)
open AdjointCocharacters (coordinateHopf coordinateHopfMap)

/-- A Hopf isomorphism for the scalar-extended coordinate rings, compatible
with the coefficient action on the two actual ground-field models. -/
def IsCoefficientEquivariant {F K : Type u} [Field F] [Field K] [Algebra F K]
    {A B : HopfAlgebraCategory F} (e : extendedHopf K A ≅ extendedHopf K B) : Prop :=
  ∀ (σ : Gal(K/F)) (x : extendedHopf K A),
    e.hom.hom ((SemilinearAction.scalarExtension (K := K) A).act σ x) =
      (SemilinearAction.scalarExtension (K := K) B).act σ (e.hom.hom x)

/-- Descent of a split group comparison preserving any specified finite
family of closed subgroup schemes through their actual inclusions. -/
def MarkedHopfComparison : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [IsGalois F K]
    {I : Type u} (G H : AffineAlgebraicGroup F)
    (S : I → ClosedSubgroup G.val) (T : I → ClosedSubgroup H.val)
    (e : extendedHopf K (coordinateHopf H) ≅ extendedHopf K (coordinateHopf G))
    (m : ∀ i, extendedHopf K (coordinateHopf (Unipotent.closedSubgroupAlgebraicGroup (T i))) ≅
      extendedHopf K (coordinateHopf (Unipotent.closedSubgroupAlgebraicGroup (S i)))),
    IsCoefficientEquivariant e →
    (∀ i, e.hom ≫ extendedHopfMap K (coordinateHopfMap
        (G := Unipotent.closedSubgroupAlgebraicGroup (S i)) (H := G) (S i).inclusion) =
      extendedHopfMap K (coordinateHopfMap
        (G := Unipotent.closedSubgroupAlgebraicGroup (T i)) (H := H) (T i).inclusion) ≫ (m i).hom) →
    ∃ (f : G.val ≅ H.val) (g : ∀ i, (S i).group ≅ (T i).group),
      extendedHopfMap K (coordinateHopfMap (G := G) (H := H) f.hom) = e.hom ∧
      ∀ i, (S i).inclusion ≫ f.hom = (g i).hom ≫ (T i).inclusion ∧
        extendedHopfMap K (coordinateHopfMap
          (G := Unipotent.closedSubgroupAlgebraicGroup (S i))
          (H := Unipotent.closedSubgroupAlgebraicGroup (T i)) (g i).hom) = (m i).hom

end EquivariantComparison


section PermutedMatrices

open Matrix

/-- The diagonal torus, both triangular Borels, and their unitriangular radicals. -/
inductive MatrixMark
  | torus | positiveBorel | negativeBorel | positiveRadical | negativeRadical

/-- The defining equations of each marked matrix subgroup. -/
def MatrixMark.Holds (m : MatrixMark) {n : ℕ} {R : Type u} [CommRing R]
    (g : SpecialLinearGroup (Fin n) R) : Prop :=
  match m with
  | .torus => ∀ i j, i ≠ j → g.val i j = 0
  | .positiveBorel => g.val.IsUpperTriangular
  | .negativeBorel => g.val.IsLowerTriangular
  | .positiveRadical => g.val.IsUpperTriangular ∧ ∀ i, g.val i i = 1
  | .negativeRadical => g.val.IsLowerTriangular ∧ ∀ i, g.val i i = 1

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

/-- Insert the orbit field in the split scalar algebra of a test algebra. -/
def orbitScalarEmbedding (R : TestAlgebra F) (J : Subgroup Gal(K/F)) :
    R ⊗[F] IntermediateField.fixedField J →ₐ[F] K ⊗[F] R :=
  (Algebra.TensorProduct.map (IntermediateField.val _) (AlgHom.id F R)).comp
    (Algebra.TensorProduct.comm F R (IntermediateField.fixedField J)).toAlgHom

/-- Coefficient action on the test algebra after extension. -/
def coefficientRingMap (R : TestAlgebra F) (σ : Gal(K/F)) :
    K ⊗[F] R →+* K ⊗[F] R :=
  (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id F R)).toRingHom

/-- The fixed matrices for coefficient action combined with permutation of
the labelled split factors. -/
def permutedMatrices {I : Type u} (ρ : Gal(K/F) →* Equiv.Perm I)
    (R : TestAlgebra F) (n : ℕ) : Subgroup (I → SpecialLinearGroup (Fin n) (K ⊗[F] R)) where
  carrier := {v | ∀ (σ : Gal(K/F)) j, v (ρ σ j) = SpecialLinearGroup.map (coefficientRingMap R σ) (v j)}
  one_mem' := fun σ _ => (map_one (SpecialLinearGroup.map (coefficientRingMap R σ))).symm
  mul_mem' := fun ha hb σ j => (congrArg₂ (· * ·) (ha σ j) (hb σ j)).trans (map_mul _ _ _).symm
  inv_mem' := fun ha σ j => (congrArg Inv.inv (ha σ j)).trans (map_inv _ _).symm

/-- Fixed split matrix families for one orbit are exactly the matrices over
the orbit-field tensor product, with the marked subgroups recognized
componentwise. This point calculation applies in particular to SL₂. -/
def PermutedMatrixPoints : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K]
    {I : Type u} (ρ : Gal(K/F) →* Equiv.Perm I) (i : I)
    (_ : ∀ j, ∃ σ, ρ σ i = j) (n : ℕ) (R : TestAlgebra F),
    letI := MulAction.compHom I ρ
    let J := MulAction.stabilizer Gal(K/F) i
    let E := orbitField ρ i
    ∃ e : permutedMatrices ρ R n ≃* SpecialLinearGroup (Fin n) (R ⊗[F] E),
      (∀ x, SpecialLinearGroup.map (orbitScalarEmbedding R J).toRingHom (e x) = x.val i) ∧
      ∀ (m : MatrixMark) x, m.Holds (e x) ↔ ∀ j, m.Holds (x.val j)

end PermutedMatrices

section UnitaryMarks

/-- On arbitrary algebras of the quadratic field, the first scalar projection
preserves and reflects each of the five matrix subgroup conditions on the
determinant-one Hermitian fixed group. -/
def UnitaryMarkedPoints : Prop :=
  ∀ (F E : Type u) [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    (R : Type u) [CommRing R] [Algebra F R] [Algebra E R] [IsScalarTower F E R],
    ∃ (e : R ⊗[F] E ≃ₐ[R] R × R)
      (U : Subgroup (SL₃ (R ⊗[F] E))) (p : U ≃* SL₃ R),
      (∀ x y, e (x ⊗ₜ[F] y) =
        (x * algebraMap E R y, x * algebraMap E R (UnitaryRankOne.quadraticConjugation F E y))) ∧
      (∀ g, g ∈ U ↔ (g.val.map (quadraticTensorInvolution F E R).toRingEquiv).transpose *
        hyperbolicGram (R ⊗[F] E) * g.val = hyperbolicGram (R ⊗[F] E)) ∧
      (∀ g : U, p g = Matrix.SpecialLinearGroup.map
        ((RingHom.fst R R).comp e.toRingEquiv.toRingHom) g.val) ∧
      ∀ (m : MatrixMark) (g : U), m.Holds (p g) ↔ m.Holds g.val

end UnitaryMarks

section SplitMatrixModels

open Pinning (AttachedDatum PinnedGroup PinnedIso SimpleRoot RootCoordinate)
open RootGroups (AdditiveLine rootPoint)
open GeneralLinearStructure (SpecialMatrixPoints)
open SpecialLinearDatum (DiagonalTorus LatticeIdentification
  RootIdentification UpperTriangularBorel IsMatrixBasedDatum coordinatePairUnits)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)

/-- The two orientations of the standard A₂ pinning use opposite parameter
signs at the two adjacent simple vertices. -/
def signedParameter {R : Type u} [CommRing R] {r : ℕ} (i : Fin r) (a : R) : R :=
  if i.val = 1 then -a else a

/-- The canonical pinning and coroots of the split determinant-one model,
with the second coordinate negated when the rank is two. -/
def SignedMatrixPinning : Prop :=
  ∀ {k : Type u} [Field k] (A : AdditiveLine k) (r : ℕ)
    (S : AffineAlgebraicGroup k) (s : SpecialMatrixPoints S (r + 1)),
    ∃ (T : DiagonalTorus s) (L : LatticeIdentification T) (M : RootIdentification T L)
      (B : UpperTriangularBorel T L M) (D : AttachedDatum B.pair)
      (U : OrderedRootProducts.RootSubgroupFamily T.subgroup)
      (q : Pinning.Pinning A B.pair U),
      letI := D.comm
      ∃ e : Fin r ≃ D.base.support,
      IsMatrixBasedDatum B D ∧ SimplyConnectedLattice.GeometricallySimplyConnected S ∧
      (∀ i : Fin r, (e i).val = M.indices (adjacentRootIndex i)) ∧
      (∀ i j : Fin r, RootData.integralCartan D.datum.rootDatum D.base (e i) (e j) =
        if i = j then 2 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0) ∧
      (∀ (i : Fin r) (R : TestAlgebra k) (a : R),
        let α : SimpleRoot B.pair := ⟨(e i).val, (D.simple_iff _).mp (e i).property⟩
        (s.hom.app R (rootPoint ((q α).val.hom ≫ (U α.val).val.inclusion) R a)).val =
          1 + Matrix.single ⟨i.castSucc⟩ ⟨i.succ⟩ (signedParameter i a)) ∧
      ∀ (i : Fin r) (R : TestAlgebra k) (a : Rˣ),
        let c := Additive.toMul (D.datum.rootDatum.coroot (e i).val)
        (s.hom.app R (cocharacterPoint c R a ≫ T.subgroup.inclusion.hom.hom)).val =
          Matrix.diagonal (fun j => (coordinatePairUnits i.castSucc i.succ a j.down : R))

end SplitMatrixModels

section PinnedFixedPoints

open _root_.LinearAlgebraicGroups.Descent (SemilinearAction)
open Pinning (AttachedDatum PinnedGroup)
open AdjointBorelCohomology (PinnedTwist)
open AutomorphismSequence (forgetPinning)
open AdjointCocharacters (coordinateHopf coordinateHopfMap)
open RootGroups (AdditiveLine)

/-- On every test algebra, extension of a point followed by the actual
pinned trivialization has exactly the twisted semilinear fixed locus as
its image. The comparison uses the given Hopf isomorphism, including
the inverse pullback in the action on coordinates. -/
def PinnedFixedPoints : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [IsGalois F K]
    {A : AdditiveLine F} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {G : AffineAlgebraicGroup F}
    {B T : ClosedSubgroup G.val} (d : PinnedTwist K D l B T) (R : TestAlgebra F),
    let C := coordinateHopf P.pair.G
    let H := coordinateHopf G
    let e := fun f : H →ₐ[F] R =>
      (Algebra.TensorProduct.map (AlgHom.id K K) f).comp d.groupIso.hom.hom.toAlgHom
    Function.Injective e ∧
      ∀ (p : extendedHopf K C →ₐ[K] K ⊗[F] R),
        p ∈ Set.range e ↔ ∀ (σ : Gal(K/F)) (x : extendedHopf K C),
          let a := (Functor.mapAut P (forgetPinning (A := A)) (l (d.outer σ))).asIso.inv
          p ((extendedHopfMap K (coordinateHopfMap (G := P.pair.G) (H := P.pair.G) a)).hom
            ((SemilinearAction.scalarExtension (K := K) C).act σ x)) =
          (SemilinearAction.scalarExtension (K := K) R).act σ (p x)

end PinnedFixedPoints

section OrbitModels

open Matrix
open Pinning (AttachedDatum PinnedGroup SimpleRoot)
open RootGroups (AdditiveLine rootPoint)
open CharacterDescent (Cocharacter)
open GeometricRadicals (IsSemisimple IsUnipotentRadical)
open GeometricBorelConjugacy (IsKBorel subgroupOfSubgroup)
open Unipotent (closedSubgroupAlgebraicGroup)
open UnipotentRadicalIntersection (IsSchemeIntersection)
open AdjointBorelCohomology (PinnedTwist)
open AdjointCocharacters (coordinateHopf coordinateHopfIso)
open AutomorphismSequence (forgetPinning)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open LinearAlgebraicGroups.WeilRestriction (extendScalars)

/-- The rational group, the specified opposite Borel pair and its radicals,
and the actual finite Galois descent of the pinned split group. -/
structure PinnedOrbitDescent (F K : Type u) [Field F] [Field K] [Algebra F K] where
  G : AffineAlgebraicGroup F
  semisimple : IsSemisimple G
  simplyConnected : SimplyConnectedLattice.GeometricallySimplyConnected G
  T : ClosedSubgroup G.val
  Bpos : ClosedSubgroup G.val
  Bneg : ClosedSubgroup G.val
  torus : GeometricRadicals.IsTorus T.group
  maximal : RankOneFlag.IsGeometricallyMaximal T
  isBorelPos : IsKBorel Bpos
  isBorelNeg : IsKBorel Bneg
  opposite : IsSchemeIntersection {Bpos, Bneg} T
  Upos : ClosedSubgroup Bpos.group
  Uneg : ClosedSubgroup Bneg.group
  isRadicalPos : IsUnipotentRadical (closedSubgroupAlgebraicGroup Bpos) Upos
  isRadicalNeg : IsUnipotentRadical (closedSubgroupAlgebraicGroup Bneg) Uneg
  A : AdditiveLine F
  P : PinnedGroup A
  D : AttachedDatum P.pair
  splitSemisimple : IsSemisimple P.pair.G
  splitSimplyConnected : SimplyConnectedLattice.GeometricallySimplyConnected P.pair.G
  lift : Aut D.toBased ≃* Aut P
  descent : PinnedTwist K D lift Bpos T
  action : Gal(K/F) →* Equiv.Perm (SimpleRoot P.pair)
  action_eq : ∀ σ (i : SimpleRoot P.pair),
    Pinning.transportCharacter (lift (descent.outer σ)).asIso.hom.torus i.val.val =
      (action σ i).val.val
  transitive : ∀ i j, ∃ σ, action σ i = j

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

/-- Cartan coefficients of the actual simple roots, with coroots indexing rows. -/
def PinnedOrbitDescent.cartan (d : PinnedOrbitDescent F K) (a b : SimpleRoot d.P.pair) : ℤ :=
  letI := d.D.comm
  d.D.datum.rootDatum.pairing b.val a.val

/-- The five source subgroups embedded in the same rational group. -/
def PinnedOrbitDescent.mark (d : PinnedOrbitDescent F K) : MatrixMark → ClosedSubgroup d.G.val
  | .torus => d.T
  | .positiveBorel => d.Bpos
  | .negativeBorel => d.Bneg
  | .positiveRadical => subgroupOfSubgroup d.Bpos d.Upos
  | .negativeRadical => subgroupOfSubgroup d.Bneg d.Uneg

/-- The split comparison supplied by the given descent isomorphism. -/
def PinnedOrbitDescent.trivialization (d : PinnedOrbitDescent F K)
    (t : ∀ C : HopfAlgebraCategory F,
      specGroup (extendedHopf K C) ≅ (groupBaseChange F K).obj (specGroup C)) :
    (groupBaseChange F K).obj d.G.val ≅ (groupBaseChange F K).obj d.P.pair.G.val :=
  ((t (AdjointCocharacters.coordinateHopf d.G)) ≪≫
      (groupBaseChange F K).mapIso (coordinateHopfIso d.G)).symm ≪≫
    (hopfSpec (CommRingCat.of K)).mapIso d.descent.groupIso.op ≪≫
    (t (AdjointCocharacters.coordinateHopf d.P.pair.G)) ≪≫
    (groupBaseChange F K).mapIso (coordinateHopfIso d.P.pair.G)

/-- Matrix points of the canonical determinant-one split group. -/
def specialLinearPointsOfSize (n : ℕ) (k : Type u) [Field k] : TestAlgebra k ⥤ GrpCat.{u} where
  obj R := GrpCat.of (SpecialLinearGroup (Fin n) R)
  map f := GrpCat.ofHom (SpecialLinearGroup.map f.hom.toRingHom)
  map_id _ := by ext g; rfl
  map_comp _ _ := by ext g; rfl

/-- Apply the five defining conditions to the isomorphism on test points
of specified rational subgroup schemes. -/
def PinnedOrbitDescent.MatchesMarks (d : PinnedOrbitDescent F K)
    {E : Type u} [Field E] [Algebra F E] {n : ℕ}
    (m : ∀ R : TestAlgebra F, AdjointRepresentation.GroupPoints d.G.val R →
      SpecialLinearGroup (Fin n) (R ⊗[F] E)) : Prop :=
  ∀ (j : MatrixMark) (R : TestAlgebra F) (x : AdjointRepresentation.GroupPoints d.G.val R),
    j.Holds (m R x) ↔ x ∈ SubgroupSections (d.mark j) ((testSpec F).obj (Opposite.op R))

/-- The actual action expressed in the two labelled adjacent vertices. -/
def PinnedOrbitDescent.adjacentAction (d : PinnedOrbitDescent F K)
    (j : Fin 2 ≃ SimpleRoot d.P.pair) : Gal(K/F) →* Equiv.Perm (Fin 2) :=
  j.symm.permCongrHom.toMonoidHom.comp d.action

/-- The orthogonal orbit model, with the orbit-field embeddings and the
matrix pinning and simple coroot in each factor over the splitting field. -/
def OrthogonalPinnedOrbitModel : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (d : PinnedOrbitDescent F K) (i : (SimpleRoot d.P.pair)),
    (∀ a b : (SimpleRoot d.P.pair), a ≠ b →
      d.cartan a b = 0) →
    let E := orbitField d.action i
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

/-- The scheme comparison and its matrix coordinates on the indicated
subgroups. The full orbit model uses all five marks. -/
def AdjacentOrbitComparison (marks : Set MatrixMark) : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (d : PinnedOrbitDescent F K) (j : Fin 2 ≃ (SimpleRoot d.P.pair)),
    (∀ a b, d.cartan (j a) (j b) =
      if a = b then 2 else -1) →
    let E := orbitField (d.adjacentAction j) 0
    ∃ (_ : Algebra.IsQuadraticExtension F E) (_ : Algebra.IsSeparable F E)
      (W : AffineAlgebraicGroup F) (U : ClosedSubgroup W.val)
      (m : (groupPointsFunctor F).obj W.val ≅ extendScalars F E ⋙ specialLinearThreePoints E)
      (f : d.G.val ≅ U.group)
      (t : ∀ C : HopfAlgebraCategory F,
        specGroup (extendedHopf K C) ≅ (groupBaseChange F K).obj (specGroup C))
      (p : (groupPointsFunctor K).obj ((groupBaseChange F K).obj d.P.pair.G.val) ≅
        specialLinearThreePoints K),
      E = IntermediateField.fixedField d.action.ker ∧
      RepresentsHyperbolicUnitary (E := E) U m ∧
      Descent.Forms.IsScalarExtensionComparison t ∧
      (∀ b ∈ marks, ∀ (R : TestAlgebra F) (x : AdjointRepresentation.GroupPoints d.G.val R),
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
          (p.hom.app R x').val = 1 + Matrix.single i.castSucc i.succ (signedParameter i a) ∧
          p.hom.app R y' = matrixSimpleCoroot i v

/-- The adjacent orbit comparison preserves the entire marked pair,
including each unipotent radical. -/
def AdjacentPinnedOrbitModel : Prop := AdjacentOrbitComparison.{u} Set.univ

end OrbitModels

section SplitSpecialLinearComparison

open Pinning (AttachedDatum PinnedGroup SimpleRoot)
open RootGroups (AdditiveLine rootPoint)
open GeometricRadicals (IsSemisimple)
open GeneralLinearStructure (SpecialMatrixPoints)
open SpecialLinearDatum (coordinatePairUnits)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)

/-- The Cartan identification with a single type-A component carries the
specified pinned roots and actual coroots to the canonical matrix formulas. -/
def SplitPinnedSpecialLinearComparison : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} (P : PinnedGroup A)
    (D : AttachedDatum P.pair),
    IsSemisimple P.pair.G → SimplyConnectedLattice.GeometricallySimplyConnected P.pair.G →
    ∀ (r : ℕ) (S : AffineAlgebraicGroup k) (s : SpecialMatrixPoints S (r + 1)),
    letI := D.comm
    ∀ j : Fin r ≃ D.base.support,
      (∀ i l, RootData.integralCartan D.datum.rootDatum D.base (j i) (j l) =
        if i = l then 2 else if i.val + 1 = l.val ∨ l.val + 1 = i.val then -1 else 0) →
      ∃ f : P.pair.G.val ≅ S.val,
        (∀ (R : TestAlgebra k) (g : AdjointRepresentation.GroupPoints P.pair.G.val R),
          g ∈ SubgroupSections P.pair.T ((testSpec k).obj (Opposite.op R)) ↔
            ∀ i j, i ≠ j → (s.hom.app R (g ≫ f.hom.hom.hom)).val i j = 0) ∧
        (∀ (R : TestAlgebra k) (g : AdjointRepresentation.GroupPoints P.pair.G.val R),
          g ∈ SubgroupSections P.pair.B ((testSpec k).obj (Opposite.op R)) ↔
            (s.hom.app R (g ≫ f.hom.hom.hom)).val.IsUpperTriangular) ∧
        ∀ (i : Fin r) (R : TestAlgebra k) (a : R) (v : Rˣ),
          let α : SimpleRoot P.pair := ⟨(j i).val, (D.simple_iff _).mp (j i).property⟩
          let c := Additive.toMul (D.datum.rootDatum.coroot (j i).val)
          (s.hom.app R (rootPoint ((P.pin α).val.hom ≫ (P.roots α.val).val.inclusion) R a ≫
            f.hom.hom.hom)).val = 1 + Matrix.single ⟨i.castSucc⟩ ⟨i.succ⟩ (signedParameter i a) ∧
          (s.hom.app R (cocharacterPoint c R v ≫ P.pair.T.inclusion.hom.hom ≫
            f.hom.hom.hom)).val =
            Matrix.diagonal (fun l => (coordinatePairUnits i.castSucc i.succ v l.down : R))

end SplitSpecialLinearComparison

section QuadraticMatrixDescent

open Matrix

/-- The split matrices fixed by the coefficient action twisted by the swap. -/
def unitaryOrbitMatrices {F K : Type u} [Field F] [Field K] [Algebra F K]
    (ρ : Gal(K/F) →* Equiv.Perm (Fin 2)) (R : TestAlgebra F) :
    Subgroup (SL₃ (K ⊗[F] R)) where
  carrier := {x | ∀ σ, SpecialLinearGroup.map (coefficientRingMap R σ) x =
    if ρ σ = 1 then x else hyperbolicDual x}
  one_mem' := by
    intro σ
    split_ifs
    · exact map_one _
    · rw [map_one, map_one]
  mul_mem' := by
    intro x y hx hy σ
    change ∀ σ, _ at hx hy
    rw [map_mul, hx σ, hy σ]
    split_ifs
    · rfl
    · exact (map_mul hyperbolicDual x y).symm
  inv_mem' := by
    intro x hx σ
    change ∀ σ, _ at hx
    rw [map_inv, hx σ]
    split_ifs
    · rfl
    · exact (map_inv hyperbolicDual x).symm

/-- Matrix descent in the adjacent orbit, over every ground-field test
algebra. The comparison to the Hermitian fixed locus is coefficientwise. -/
def QuadraticOrbitMatrixPoints : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (ρ : Gal(K/F) →* Equiv.Perm (Fin 2)) (i : Fin 2)
    (_hρ : ∀ j, ∃ σ, ρ σ i = j) (R : TestAlgebra F),
    letI := MulAction.compHom (Fin 2) ρ
    let J := MulAction.stabilizer Gal(K/F) i
    let E := orbitField ρ i
    ∃ (_ : Algebra.IsQuadraticExtension F E) (_ : Algebra.IsSeparable F E)
      (U : Subgroup (SL₃ (R ⊗[F] E))) (e : U ≃* unitaryOrbitMatrices ρ R),
      (∀ g, g ∈ U ↔
        (g.val.map (quadraticTensorInvolution F E R).toRingEquiv).transpose *
          hyperbolicGram (R ⊗[F] E) * g.val = hyperbolicGram (R ⊗[F] E)) ∧
      (∀ g, (e g).val = SpecialLinearGroup.map (orbitScalarEmbedding R J).toRingHom g.val) ∧
      ∀ (m : MatrixMark) g, m.Holds (e g).val ↔ m.Holds g.val

end QuadraticMatrixDescent

section AdjacentAutomorphism

open Pinning (AttachedDatum PinnedGroup PinnedIso SimpleRoot transportCharacter)
open RootGroups (AdditiveLine rootPoint)
open GeometricRadicals (IsSemisimple)
open CharacterDescent (Character)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)

/-- The two possible permutations on the adjacent simple roots. -/
def adjacentPermutation (swap : Bool) (i : Fin 2) : Fin 2 :=
  if swap then i.rev else i

/-- Over the field of the split pinned datum, its actual pinned lift acts on
the canonical determinant-one matrix model by identity or reverse inverse
transpose, according to the action on the two adjacent simple vertices. -/
def AdjacentPinnedAutomorphisms : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} (P : PinnedGroup A)
    (D : AttachedDatum P.pair), IsSemisimple P.pair.G →
    SimplyConnectedLattice.GeometricallySimplyConnected P.pair.G →
    letI := D.comm
    ∀ j : Fin 2 ≃ D.base.support,
      (∀ i l, RootData.integralCartan D.datum.rootDatum D.base (j i) (j l) =
        if i = l then 2 else -1) →
      ∃ m : (groupPointsFunctor k).obj P.pair.G.val ≅ specialLinearThreePoints k,
        (∀ (R : TestAlgebra k) (x : AdjointRepresentation.GroupPoints P.pair.G.val R),
          x ∈ SubgroupSections P.pair.T ((testSpec k).obj (Opposite.op R)) ↔
            MatrixMark.torus.Holds (m.hom.app R x)) ∧
        (∀ (R : TestAlgebra k) (x : AdjointRepresentation.GroupPoints P.pair.G.val R),
          x ∈ SubgroupSections P.pair.B ((testSpec k).obj (Opposite.op R)) ↔
            MatrixMark.positiveBorel.Holds (m.hom.app R x)) ∧
        (∀ (i : Fin 2) (R : TestAlgebra k) (x : R) (v : Rˣ),
          let α : SimpleRoot P.pair := ⟨(j i).val, (D.simple_iff _).mp (j i).property⟩
          let c := Additive.toMul (D.datum.rootDatum.coroot (j i).val)
          (m.hom.app R (rootPoint ((P.pin α).val.hom ≫ (P.roots α.val).val.inclusion) R x)).val =
            1 + Matrix.single i.castSucc i.succ (signedParameter i x) ∧
          m.hom.app R (cocharacterPoint c R v ≫ P.pair.T.inclusion.hom.hom) =
            matrixSimpleCoroot i v) ∧
        ∀ (swap : Bool) (f : PinnedIso P P),
          (∀ i, transportCharacter f.torus (j i).val.val =
            (j (adjacentPermutation swap i)).val.val) →
          ∀ (R : TestAlgebra k) (g : AdjointRepresentation.GroupPoints P.pair.G.val R),
            m.hom.app R (g ≫ f.group.hom.hom.hom) =
              if swap then hyperbolicDual (m.hom.app R g) else m.hom.app R g

end AdjacentAutomorphism

section RestrictedCoordinates

open _root_.LinearAlgebraicGroups.Descent (SemilinearAction)

/-- Restrict an extended coordinate point to the coordinates over the ground
field without changing its target scalar algebra. -/
def restrictExtendedPoint {F K : Type u} [Field F] [Field K] [Algebra F K]
    {C : HopfAlgebraCategory F} (R : TestAlgebra F)
    (p : extendedHopf K C →ₐ[K] K ⊗[F] R) : C →ₐ[F] K ⊗[F] R :=
  (p.restrictScalars F).comp Algebra.TensorProduct.includeRight

/-- The equation expressing the twisted semilinear action on a point can
be tested on the coordinates defined over the ground field. -/
def RestrictedCoefficientEquation : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K]
    {C : HopfAlgebraCategory F} (R : TestAlgebra F)
    (p : extendedHopf K C →ₐ[K] K ⊗[F] R) (b : C ⟶ C) (σ : Gal(K/F)),
    (∀ x, p ((extendedHopfMap K b).hom
      ((SemilinearAction.scalarExtension (K := K) C).act σ x)) =
      coefficientRingMap R σ (p x)) ↔
    ∀ c : C, restrictExtendedPoint R p (b.hom c) =
      coefficientRingMap R σ (restrictExtendedPoint R p c)

/-- An extended algebra point is uniquely determined by its restriction
to the ground-field coordinate algebra. -/
def RestrictExtendedPointBijective : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] {C : HopfAlgebraCategory F}
    (R : TestAlgebra F),
    Function.Bijective (restrictExtendedPoint (K := K) (C := C) R)

end RestrictedCoordinates

end

end LinearAlgebraicGroups.Specs.QuasiSplitOrbitPinnedModels
