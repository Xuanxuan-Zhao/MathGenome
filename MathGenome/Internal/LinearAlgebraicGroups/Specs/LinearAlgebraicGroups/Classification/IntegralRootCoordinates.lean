import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.Pinning
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralCentralQuotient

open AlgebraicGeometry CategoryTheory Opposite WithConv
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.IntegralRootCoordinates

open IntegralCentralQuotient (IntegralRing HopfSpectrum spectrumOfHopfHom spectrumOfAlgHom RootScalarAction)
open Pinning (AttachedDatum BasedIso BasedRootDatum SplitBorelPair)
open CharacterDescent (Character)
open DiagonalizableGroups (IntegerCharacters integerGenerator)

noncomputable section

section Tangents

variable {R A : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]

/-- A relative tangent vector at the identity, expressed by its dual-number point. -/
abbrev Tangent (R A : Type u) [CommRing R] [CommRing A] [HopfAlgebra R A] :=
  {v : A →ₐ[R] DualNumber R //
    (TrivSqZeroExt.fstHom R R R).comp v = Bialgebra.counitAlgHom R A}

/-- Extension of both dual-number coefficients to a test algebra. -/
def dualCoefficients (S : Type u) [CommRing S] [Algebra R S] :
    DualNumber R →ₐ[R] DualNumber S where
  toRingHom := InfinitesimalCommutator.mapCoefficients (algebraMap R S)
  commutes' _ := TrivSqZeroExt.ext rfl (map_zero (algebraMap R S))

/-- The adjoint action on the tangent vector is by the given character on every test algebra. -/
def HasWeight {X : Type u} [CommGroup X] (t : A →ₐc[R] MonoidAlgebra R X) (α : X)
    (v : Tangent R A) : Prop :=
  ∀ (S : CommAlgCat.{u} R) (s : MonoidAlgebra R X →ₐ[R] S),
    let g := toConv ((TrivSqZeroExt.inlAlgHom R S S).comp (s.comp t.toAlgHom))
    let p := (dualCoefficients S).comp v.val
    let c := s (MonoidAlgebra.of R X α)
    let scale := (TrivSqZeroExt.map (c • (LinearMap.id : S →ₗ[S] S))).restrictScalars R
    g * toConv p * toConv (g.ofConv.comp (HopfAlgebra.antipodeAlgHom R A)) =
      toConv (scale.comp p)

/-- The marked vector is a basis of the integral tangent weight line. -/
def IsWeightBasis {X : Type u} [CommGroup X] (t : A →ₐc[R] MonoidAlgebra R X) (α : X)
    (v : Tangent R A) : Prop :=
  HasWeight t α v ∧ ∀ w : Tangent R A, HasWeight t α w →
    ∃! c : R, ∀ a : A, (w.val a).snd = c * (v.val a).snd

end Tangents

/-- The character represented by a field character is read on the Laurent generator. -/
def characterMonomial {K C : Type u} [Field K] [CommRing C] [HopfAlgebra K C]
    (χ : Character (HopfSpectrum K C)) : C :=
  let f := ((algSpec.fullyFaithful (R := CommRingCat.of K)).preimage χ.hom.hom).unop
  f.hom (MonoidAlgebra.of K IntegerCharacters integerGenerator)

/-- The geometric fibre has the indicated based datum on the actual marked split torus.
The equality on monomials calibrates its entire character lattice. -/
def HasFibreDatum {R A : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]
    (D : BasedRootDatum.{u}) (t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X))
    (K : Type u) [Field K] [Algebra R K] : Prop :=
  let tK := Bialgebra.TensorProduct.map (BialgHom.id K K) t
  ∃ (P : SplitBorelPair K) (e : HopfSpectrum K (K ⊗[R] A) ≅ P.G.val)
    (s : HopfSpectrum K (K ⊗[R] MonoidAlgebra R (Multiplicative D.X)) ≅ P.T.group)
    (E : AttachedDatum P) (d : BasedIso D E.toBased),
    spectrumOfHopfHom tK ≫ e.hom = s.hom ≫ P.T.inclusion ∧
      ∀ χ : D.X,
        characterMonomial (s.hom ≫ Additive.toMul (d.val.weightEquiv χ)) =
          (1 : K) ⊗ₜ[R] MonoidAlgebra.of R (Multiplicative D.X) (Multiplicative.ofAdd χ)

open RootGroups (AdditiveLine HasScalarAction IsRootSubgroup)
open RankOneFlag (SameSubgroup)

section Coordinates

variable {R A : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]

/-- Evaluate a polynomial root coordinate on a test algebra. -/
def coordinatePoint (x : A →ₐ[R] Polynomial R) (S : CommAlgCat.{u} R) (a : S) :
    WithConv (A →ₐ[R] S) :=
  toConv ((Polynomial.aeval a).comp x)

/-- Scalar extension of the polynomial pullback, with the variable unchanged. -/
def fibreCoordinate (K : Type u) [Field K] [Algebra R K] (x : A →ₐ[R] Polynomial R) :
    K ⊗[R] A →ₐ[K] Polynomial K :=
  (AlgHom.liftEquiv R K A (Polynomial K))
    ((Polynomial.mapAlgHom (Algebra.ofId R K)).comp x)

/-- The scalar extension parametrizes the actual root subgroup in each calibrated
geometric fibre, for every choice of calibration realizing the marked datum. -/
def IsFibreRootCoordinate {D : BasedRootDatum.{u}}
    (t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X)) (i : D.I)
    (x : A →ₐ[R] Polynomial R) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K]
    (Q : SplitBorelPair K) (e : HopfSpectrum K (K ⊗[R] A) ≅ Q.G.val)
    (s : HopfSpectrum K (K ⊗[R] MonoidAlgebra R (Multiplicative D.X)) ≅ Q.T.group)
    (E : AttachedDatum Q) (d : BasedIso D E.toBased),
    spectrumOfHopfHom (Bialgebra.TensorProduct.map (BialgHom.id K K) t) ≫ e.hom =
        s.hom ≫ Q.T.inclusion →
    (∀ χ : D.X, characterMonomial (s.hom ≫ Additive.toMul (d.val.weightEquiv χ)) =
      (1 : K) ⊗ₜ[R] MonoidAlgebra.of R (Multiplicative D.X) (Multiplicative.ofAdd χ)) →
    let α := (d.val.indexEquiv i).val
    ∃ (U : ClosedSubgroup Q.G.val) (L : AdditiveLine K) (p : L.group ≅ U.group),
      IsRootSubgroup Q.T U α ∧
      (∀ V : ClosedSubgroup Q.G.val, IsRootSubgroup Q.T V α → SameSubgroup U V) ∧
      HasScalarAction Q.T α (p.hom ≫ U.inclusion) ∧
      spectrumOfAlgHom (fibreCoordinate K x) ≫ e.hom.hom.hom =
        (p.hom ≫ U.inclusion).hom.hom

end Coordinates

set_option backward.isDefEq.respectTransparency false in
/-- The integral root coordinates of a smooth marked affine integral model. -/
def IntegralRootCoordinates : Prop :=
  ∀ {D : BasedRootDatum.{u}} {A : Type u} [CommRing A] [HopfAlgebra IntegralRing.{u} A]
    (t : A →ₐc[IntegralRing.{u}] MonoidAlgebra IntegralRing.{u} (Multiplicative D.X)),
    Algebra.FinitePresentation IntegralRing.{u} A →
    Smooth (HopfSpectrum IntegralRing.{u} A).X.hom →
    Function.Surjective t →
    (∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra IntegralRing.{u} K], HasFibreDatum D t K) →
    ∀ (pin : ↥D.base.support → Tangent IntegralRing.{u} A),
    (∀ i : ↥D.base.support, IsWeightBasis t (Multiplicative.ofAdd (D.datum.root i.val)) (pin i)) →
    ∃ x : D.I → A →ₐ[IntegralRing.{u}] Polynomial IntegralRing.{u},
      (∀ i, Function.Surjective (x i)) ∧
      (∀ i (S : CommAlgCat.{u} IntegralRing.{u}) (a b : S),
        coordinatePoint (x i) S (a + b) = coordinatePoint (x i) S a * coordinatePoint (x i) S b) ∧
      (∀ i (S : CommAlgCat.{u} IntegralRing.{u}), coordinatePoint (x i) S 0 = 1) ∧
      (∀ i, RootScalarAction t (x i) (Multiplicative.ofAdd (D.datum.root i))) ∧
      (∀ i : ↥D.base.support, (Polynomial.aeval (DualNumber.eps : DualNumber IntegralRing.{u})).comp
        (x i.val) = (pin i).val) ∧
      (∀ i, IsFibreRootCoordinate t i (x i))

end

end LinearAlgebraicGroups.Specs.IntegralRootCoordinates
