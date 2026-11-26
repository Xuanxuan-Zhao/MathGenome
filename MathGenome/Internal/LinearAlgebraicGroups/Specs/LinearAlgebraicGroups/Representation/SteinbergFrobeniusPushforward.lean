import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagRelativeFrobeniusAtlas
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.AssociatedFlagLineSheaves
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.LinePushforwardProjection
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.SteinbergDimension
import Mathlib.Algebra.MvPolynomial.Expand
import Mathlib.Algebra.Ring.ULift
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Data.Matrix.Mul

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite WithConv
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u

noncomputable section

namespace LinearAlgebraicGroups.Specs.SteinbergFrobeniusPushforward

open CharacterDescent (Character)
open FlagLineBundle
open SimpleClassification (SocleModel)
open QuotientEmbedding (Presentation)
open LinearAlgebraicGroups.FiniteDistributions (twistCoordinates)

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
  {P : OppositeBorelPair G} {U : ClosedSubgroup P.positive.group}
  {χ : Character P.torus.group}

/-- The inclusion of the socle into the regular functions on the group. -/
def socleFunction (S : SocleModel P U χ) : S.socle →ₗ[k] S.A :=
  (covariantFunctions S.restriction S.coordinate).subtype.comp
    (S.inducedBasis.equivFun.symm.toLinearMap.comp S.socle.subtype)

/-- Evaluation at a lift of a geometric point in the trivialization on the group. -/
def EvaluationOnGroup : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    {P : OppositeBorelPair G} {U : ClosedSubgroup P.positive.group}
    {χ : Character P.torus.group} (S : SocleModel P U χ)
    (K : Type u) [Field K] [Algebra k K] (g : S.A →ₐ[k] K),
      ∃ s : S.socle, g (socleFunction S s) ≠ 0

/-- The point over (y) representing the zero section in the group
trivialization, using a lift (g) through the quotient projection. -/
def BundleEvaluationNonvanishing : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    {P : OppositeBorelPair G} {U : ClosedSubgroup P.positive.group}
    {χ : Character P.torus.group} (S : SocleModel P U χ)
    (Q : Presentation P.negative) (a : ModObj G.val.X Q.scheme)
    (L : AssociatedBundle Q a S.projection χ)
    (E : BundleSection L ≃ covariantFunctions S.restriction S.coordinate),
    (∀ s : BundleSection L, Q.projection ≫ s.val =
      prod.lift (𝟙 G.val.X)
        (S.groupIso.inv.hom.hom ≫ linePoint (CommAlgCat.of k S.A) (E s : S.A)) ≫
      L.trivialization) →
    ∀ (K : Type u) [Field K] [Algebra k K] (y : Points Q.scheme (CommAlgCat.of k K)),
      ∃ (g : Points G.val.X (CommAlgCat.of k K)) (s : S.socle),
        g ≫ Q.projection = y ∧
        y ≫ (E.symm (S.inducedBasis.equivFun.symm (s : S.I → k))).val ≠
          prod.lift g (linePoint (CommAlgCat.of k K) 0) ≫ L.trivialization

/-- Contracting the vector factor of a coaction with a linear functional
gives the coordinate function on the acting coalgebra. -/
def coefficientMap {C V : Type u}
    [AddCommGroup C] [Module k C] [Coalgebra k C] [AddCommGroup V] [Module k V]
    (δ : RightComodule k C V) (ℓ : V →ₗ[k] k) : V →ₗ[k] C :=
  (TensorProduct.lid k C).toLinearMap.comp ((ℓ.rTensor C).comp δ.coaction)

/-- The orbit coefficient map for a nonzero evaluation on a simple comodule
is injective. -/
def SimpleCoefficientInjection : Prop :=
  ∀ {k C V : Type u} [Field k]
    [AddCommGroup C] [Module k C] [Coalgebra k C] [AddCommGroup V] [Module k V]
    (δ : RightComodule k C V) (ℓ : V →ₗ[k] k),
    (∀ W : Submodule k V, δ.IsSubcomodule W → W = ⊥ ∨ W = ⊤) →
    ℓ ≠ 0 → Function.Injective (coefficientMap δ ℓ)

open LinearAlgebraicGroups.FiniteDistributions (FrobeniusFormula)
open SteinbergDimension (IsHalfPositiveRootSum)

/-- Restriction of the functions in the Steinberg socle to the orbit of
the scheme Frobenius kernel through a lifted rational flag point. The
universal kernel point acts by its inverse, as in left translation. -/
def KernelOrbitInjection : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (p r : ℕ) [Fact p.Prime] [CharP k p],
    1 ≤ r → ∀ {G : AffineAlgebraicGroup k} (P : OppositeBorelPair G)
      [IsCommMonObj P.torus.group.X]
      (U : ClosedSubgroup P.positive.group),
      GeometricRadicals.IsUnipotentRadical (Unipotent.closedSubgroupAlgebraicGroup P.positive)
        U →
      ∀ (ρ : Character P.torus.group), IsHalfPositiveRootSum P ρ →
      ∀ (S : SocleModel P U (Additive.toMul ((p ^ r - 1) • Additive.ofMul ρ)))
        (F : twistCoordinates k p r S.A ⟶ S.A), FrobeniusFormula k p r S.A F →
      ∀ (h : (kernelIdeal F).IsHopfIdeal k) (g : S.A →ₐ[k] k),
        letI := h
        let C := hopfQuotient S.A (kernelIdeal F)
        let q := hopfQuotientMap S.A (kernelIdeal F)
        let R : TestAlgebra k := CommAlgCat.of k C
        letI := convolutionGroup S.A R
        let gg : WithConv (S.A →ₐ[k] R) :=
          toConv ((Algebra.ofId k C).comp g)
        let hh : WithConv (S.A →ₐ[k] R) := toConv q.hom.toAlgHom
        Function.Injective (fun s : S.socle ↦ (hh⁻¹ * gg) (socleFunction S s))

/-- The exponent vector of a monomial whose exponents are all below (q). -/
def boundedExponents {n q : ℕ} (i : Fin n → Fin q) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j ↦ (i j).val)

/-- The coordinate-ring map with a separate copy for the source affine space. -/
def polynomialPowerMap (k : Type u) [Field k] (n q : ℕ) :
    MvPolynomial (Fin n) k →+* ULift.{0} (MvPolynomial (Fin n) k) :=
  ULift.ringEquiv.symm.toRingHom.comp (MvPolynomial.expand q).toRingHom

/-- On the affine-space charts of the split model, the power map is finite
free, with the indicated basis of size (q^n) over its target. -/
def PolynomialPowerBasis : Prop :=
  ∀ (k : Type u) [Field k] (n q : ℕ), 0 < q →
    letI := (polynomialPowerMap k n q).toAlgebra.toModule
    ∃ b : Module.Basis (Fin n → Fin q) (MvPolynomial (Fin n) k)
        (ULift.{0} (MvPolynomial (Fin n) k)),
      (∀ i, (b i).down = MvPolynomial.monomial (boundedExponents i) 1) ∧
      Fintype.card (Fin n → Fin q) = q ^ n

/-- The power map on affine space is finite flat with constant degree (q^n). -/
def PolynomialPowerDegree : Prop :=
  ∀ (k : Type u) [Field k] (n q : ℕ), 0 < q →
    let f := Spec.map (CommRingCat.ofHom (polynomialPowerMap k n q))
    IsFinite f ∧ Flat f ∧ ∀ x, f.finrank x = q ^ n

/-- The actual relative Frobenius on the flag is finite and flat with degree
`(p ^ r) ^ dim(Y)`. The affine-cell dimension is also the number of positive roots. -/
def FlagFrobeniusDegree : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (p r : ℕ) [Fact p.Prime] [CharP k p],
    1 ≤ r → ∀ {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
      (Q : Presentation P.negative)
      (F : Q.scheme ⟶ (FlagRelativeFrobeniusAtlas.twist p r).obj Q.scheme),
      FlagRelativeFrobeniusAtlas.IsRelativeFrobenius p r Q.scheme F →
      let n := (BorelsAndChambers.subgroupRoots P.torus P.positive).ncard
      topologicalKrullDim Q.scheme.left = n ∧
      IsFinite F.left ∧ Flat F.left ∧ ∀ y, F.left.finrank y = (p ^ r) ^ n

/-- The scalar twist is modeled by changing the structure map to the base
field, with the identity on the underlying scheme. In that model the
twisted associated line has the same underlying module sheaf. The
adjoint of the comparison is the power map on covariant functions. -/
def FlagFrobeniusLinePullback : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (p r : ℕ) [Fact p.Prime] [CharP k p],
    ∀ {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
      {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
      {b : BorelProjection P} {ν : Character P.torus.group}
      {L : AssociatedBundle Q a b ν} {Lq : AssociatedBundle Q a b (ν ^ (p ^ r))}
      (M : AssociatedFlagLineSheaves.SectionRealization L)
      (Mq : AssociatedFlagLineSheaves.SectionRealization Lq)
      (F : Q.scheme ⟶ (FlagRelativeFrobeniusAtlas.twist p r).obj Q.scheme),
      ∀ hF : FlagRelativeFrobeniusAtlas.IsRelativeFrobenius p r Q.scheme F,
      ∃ e : (Scheme.Modules.pullback F.left).obj M.sheaf ≅ Mq.sheaf,
        ∀ (U : Q.scheme.left.Opens) (s : Γ(M.sheaf, U)),
          Mq.functionVal (F.left ⁻¹ᵁ U)
            (((Scheme.Modules.pullbackPushforwardAdjunction F.left).homEquiv
              M.sheaf Mq.sheaf e.hom).app U s) =
            G.val.X.left.presheaf.map
              (eqToHom (show Q.projection.left ⁻¹ᵁ (F.left ⁻¹ᵁ U) =
                  Q.projection.left ⁻¹ᵁ U from
                congrArg (fun V ↦ Q.projection.left ⁻¹ᵁ V)
                  (by ext x; change F.left x ∈ U ↔ x ∈ U; exact Iff.of_eq (congrArg (fun z : Q.scheme.left ↦ z ∈ U) (hF.1 x))))).op
              ((M.functionVal U s) ^ (p ^ r))

/-- A map of free modules of equal finite rank on an affine-space chart
is invertible when it is injective on every closed fiber. -/
def PolynomialMatrixCriterion : Prop :=
  ∀ {k I : Type u} [Field k] [IsAlgClosed k] [Fintype I] [DecidableEq I]
    {n : ℕ} (A : Matrix I I (MvPolynomial (Fin n) k)),
    (∀ x : Fin n → k, Function.Injective (A.map (MvPolynomial.aeval x)).mulVec) →
    IsUnit A

open AssociatedFlagLineSheaves (SectionRealization)
open GeometricRadicals (IsSemisimple IsUnipotentRadical)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open Unipotent (closedSubgroupAlgebraicGroup)

/-- The constant vector space in its given basis, tensored with the structure
sheaf. -/
abbrev freeModule (X : Scheme.{u}) (I : Type u) : X.Modules :=
  SheafOfModules.free (R := X.ringCatSheaf) I

/-- The global section corresponding to a basis vector. -/
def freeGenerator (X : Scheme.{u}) {I : Type u} (i : I) : Γ(freeModule X I, ⊤) :=
  Scheme.Modules.Hom.app (X := X) (M := LinePushforwardProjection.structureModule X)
    (N := freeModule X I) (SheafOfModules.ιFree i) ⊤ (1 : Γ(X, ⊤))

/-- The adjoint evaluation is determined by the actual socle sections. The
formula is in the E04 trivialization after pulling back to the group. -/
def IsSocleEvaluation {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
    (S : SocleModel P U χ) {L : AssociatedBundle Q a S.projection χ}
    (M : SectionRealization L) {Y : Scheme.{u}} (F : Q.scheme.left ⟶ Y)
    (e : freeModule Y S.J ⟶ (Scheme.Modules.pushforward F).obj M.sheaf) : Prop :=
  ∀ i : S.J, Q.projection.left ≫ Q.scheme.left.topIso.inv ≫
      (M.sections ⊤ (e.app ⊤ (freeGenerator Y i))).val =
    (prod.lift (𝟙 G.val.X) (S.groupIso.inv.hom.hom ≫
      linePoint (CommAlgCat.of k S.A) (socleFunction S (S.socleBasis i))) ≫ L.trivialization).left

/-- The sections in the Steinberg socle induce the isomorphism to the direct
image along the relative Frobenius. -/
def SteinbergEvaluationIso : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (p r : ℕ) [Fact p.Prime] [CharP k p],
    1 ≤ r → ∀ {G : AffineAlgebraicGroup k}, IsSemisimple G → GeometricallySimplyConnected G →
    ∀ (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X]
      (U : ClosedSubgroup P.positive.group),
      IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U →
    ∀ (ρ : Character P.torus.group), IsHalfPositiveRootSum P ρ →
    ∀ (S : SocleModel P U (Additive.toMul ((p ^ r - 1) • Additive.ofMul ρ)))
      {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
      {L : AssociatedBundle Q a S.projection (Additive.toMul ((p ^ r - 1) • Additive.ofMul ρ))}
      (M : SectionRealization L)
      (F : Q.scheme ⟶ (FlagRelativeFrobeniusAtlas.twist p r).obj Q.scheme),
      FlagRelativeFrobeniusAtlas.IsRelativeFrobenius p r Q.scheme F →
      ∃ e : freeModule ((FlagRelativeFrobeniusAtlas.twist p r).obj Q.scheme).left S.J ≅
          (Scheme.Modules.pushforward F.left).obj M.sheaf,
        IsSocleEvaluation S M F.left e.hom

/-- The direct image of the line of weight `σᵣ + pʳλ` is the Steinberg
module tensored with the line of weight `λ` on the scalar twist. The twist
model keeps the underlying scheme and changes its structure map to `Spec k`,
so the base-changed line is represented by the original module sheaf. -/
def SteinbergFrobeniusFormula : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (p r : ℕ) [Fact p.Prime] [CharP k p],
    1 ≤ r → ∀ {G : AffineAlgebraicGroup k}, IsSemisimple G → GeometricallySimplyConnected G →
    ∀ (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X]
      (U : ClosedSubgroup P.positive.group),
      IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U →
    ∀ (ρ : Character P.torus.group), IsHalfPositiveRootSum P ρ →
    let σ := Additive.toMul ((p ^ r - 1) • Additive.ofMul ρ)
    ∀ (S : SocleModel P U σ) (ν : Character P.torus.group)
      {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
      {Lσ : AssociatedBundle Q a S.projection σ}
      {Lν : AssociatedBundle Q a S.projection ν}
      {Lsum : AssociatedBundle Q a S.projection (σ * ν ^ (p ^ r))}
      (_Mσ : SectionRealization Lσ) (Mν : SectionRealization Lν) (Msum : SectionRealization Lsum),
      μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul →
    ∀
      (F : Q.scheme ⟶ (FlagRelativeFrobeniusAtlas.twist p r).obj Q.scheme),
      FlagRelativeFrobeniusAtlas.IsRelativeFrobenius p r Q.scheme F →
      Nonempty ((Scheme.Modules.pushforward F.left).obj Msum.sheaf ≅
        LinePushforwardProjection.tensorModule
          (freeModule ((FlagRelativeFrobeniusAtlas.twist p r).obj Q.scheme).left S.J) Mν.sheaf)

section MarkedTarget

open AssociatedFlagLineSheaves (HasCanonicalPullback QuotientMap)
open FlagRelativeFrobeniusAtlas (MarkedFlagTwist)

/-- The Frobenius square with both flags presented as opposite Borel quotients. -/
def markedQuotientMap {p r : ℕ} [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    {Q : Presentation P.negative} {b : BorelProjection P} (t : MarkedFlagTwist p r Q b) :
    QuotientMap Q t.quotient where
  group := t.groupFrobenius
  borel := t.borelFrobenius
  flag := t.flagFrobenius
  commutesBorel := t.inclusion_square
  commutesFlag := t.quotient_square

/-- Pullback of the line for the transported character on the marked target
gives the line for `ν ^ (p ^ r)` on the source. -/
def MarkedFlagFrobeniusLinePullback : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (p r : ℕ) [Fact p.Prime] [CharP k p]
    {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G} {Q : Presentation P.negative}
    {b : BorelProjection P} (t : MarkedFlagTwist p r Q b) (ν : Character P.torus.group)
    {a : ModObj G.val.X Q.scheme} {a' : ModObj (FlagRelativeFrobeniusAtlas.twistAffineGroup p r G).val.X
      t.quotient.scheme}
    {Lq : AssociatedBundle Q a b (ν ^ (p ^ r))}
    {L' : AssociatedBundle t.quotient a' t.borel (t.characters ν)}
    (Mq : SectionRealization Lq) (M' : SectionRealization L'),
      HasCanonicalPullback Mq M' (markedQuotientMap t)

/-- The same socle evaluation on the marked flag presentation of the target. -/
def MarkedSteinbergEvaluationIso : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (p r : ℕ) [Fact p.Prime] [CharP k p],
    1 ≤ r → ∀ {G : AffineAlgebraicGroup k}, IsSemisimple G → GeometricallySimplyConnected G →
    ∀ (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X]
      (U : ClosedSubgroup P.positive.group),
      IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U →
    ∀ (ρ : Character P.torus.group), IsHalfPositiveRootSum P ρ →
    let σ := Additive.toMul ((p ^ r - 1) • Additive.ofMul ρ)
    ∀ (S : SocleModel P U σ) {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
      {Lσ : AssociatedBundle Q a S.projection σ} (Mσ : SectionRealization Lσ)
      (t : MarkedFlagTwist p r Q S.projection),
      ∃ e : freeModule t.quotient.scheme.left S.J ≅
          (Scheme.Modules.pushforward t.flagFrobenius.left).obj Mσ.sheaf,
        IsSocleEvaluation S Mσ t.flagFrobenius.left e.hom

/-- The Steinberg pushforward formula on the marked flag target, with the
associated line formed using the explicitly transported character. -/
def MarkedSteinbergFrobeniusFormula : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (p r : ℕ) [Fact p.Prime] [CharP k p],
    1 ≤ r → ∀ {G : AffineAlgebraicGroup k}, IsSemisimple G → GeometricallySimplyConnected G →
    ∀ (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X]
      (U : ClosedSubgroup P.positive.group),
      IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U →
    ∀ (ρ : Character P.torus.group), IsHalfPositiveRootSum P ρ →
    let σ := Additive.toMul ((p ^ r - 1) • Additive.ofMul ρ)
    ∀ (S : SocleModel P U σ) (ν : Character P.torus.group)
      {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
      (t : MarkedFlagTwist p r Q S.projection)
      {a' : ModObj (FlagRelativeFrobeniusAtlas.twistAffineGroup p r G).val.X t.quotient.scheme}
      {Lσ : AssociatedBundle Q a S.projection σ}
      {Lsum : AssociatedBundle Q a S.projection (σ * ν ^ (p ^ r))}
      {Lν' : AssociatedBundle t.quotient a' t.borel (t.characters ν)}
      (_Mσ : SectionRealization Lσ) (Msum : SectionRealization Lsum) (Mν' : SectionRealization Lν'),
      μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul →
      Nonempty ((Scheme.Modules.pushforward t.flagFrobenius.left).obj Msum.sheaf ≅
        LinePushforwardProjection.tensorModule (freeModule t.quotient.scheme.left S.J) Mν'.sheaf)

end MarkedTarget

end LinearAlgebraicGroups.Specs.SteinbergFrobeniusPushforward
