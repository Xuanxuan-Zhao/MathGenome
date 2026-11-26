import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.Pinning
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralCentralQuotient

open AlgebraicGeometry CategoryTheory Opposite WithConv
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.IntegralRecognition

open IntegralCentralQuotient (IntegralRing HopfSpectrum spectrumOfHopfHom IsCentral IsRightTorsor)
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

/-- A smooth affine integral model with its split maximal torus, fixed based datum, and
a basis of each simple tangent root line. -/
structure Model (D : BasedRootDatum.{u}) where
  A : Type u
  [ring : CommRing A]
  [hopf : HopfAlgebra IntegralRing.{u} A]
  finitePresentation : Algebra.FinitePresentation IntegralRing.{u} A
  smooth : Smooth (HopfSpectrum IntegralRing.{u} A).X.hom
  torus : A →ₐc[IntegralRing.{u}] MonoidAlgebra IntegralRing.{u} (Multiplicative D.X)
  torus_surjective : Function.Surjective torus
  fibreDatum : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra IntegralRing.{u} K], HasFibreDatum D torus K
  pin : ↥D.base.support → Tangent IntegralRing.{u} A
  pin_basis : ∀ i : ↥D.base.support, IsWeightBasis torus
    (Multiplicative.ofAdd (D.datum.root i.val)) (pin i)

attribute [instance] Model.ring Model.hopf

/-- A based ordinary isogeny, contravariant on characters and covariant on roots.
The equation on pairings is the transpose condition on coroots. -/
structure LatticeMap (D E : BasedRootDatum.{u}) where
  characters : Multiplicative E.X →* Multiplicative D.X
  injective : Function.Injective characters
  finiteIndex : Finite (Multiplicative D.X ⧸ characters.range)
  roots : D.I ≃ E.I
  simple_iff : ∀ i, roots i ∈ E.base.support ↔ i ∈ D.base.support
  root_eq : ∀ i, characters (Multiplicative.ofAdd (E.datum.root (roots i))) =
    Multiplicative.ofAdd (D.datum.root i)
  coroot_eq : ∀ i (χ : E.X),
    D.datum.toLinearMap (Multiplicative.toAdd (characters (Multiplicative.ofAdd χ)))
        (D.datum.coroot i) =
      E.datum.toLinearMap χ (E.datum.coroot (roots i))

/-- Compatibility with the full torus restriction and the specified simple tangent vectors. -/
def LiftsMarking {D E : BasedRootDatum.{u}} (P : Model D) (Q : Model E)
    (h : Multiplicative E.X →* Multiplicative D.X) (d : D.I ≃ E.I)
    (hd : ∀ i, i ∈ D.base.support → d i ∈ E.base.support) (f : Q.A →ₐc[IntegralRing.{u}] P.A) : Prop :=
  P.torus.comp f = (MonoidAlgebra.mapDomainBialgHom IntegralRing.{u} h).comp Q.torus ∧
    ∀ i : ↥D.base.support, (P.pin i).val.comp f.toAlgHom =
      (Q.pin ⟨d i.val, hd i.val i.property⟩).val

/-- Every specified based datum isomorphism lifts to a unique integral pinned isomorphism. -/
def PinnedIsomorphisms : Prop :=
  ∀ {D E : BasedRootDatum.{u}} (P : Model D) (Q : Model E) (e : BasedIso D E),
    let h : Multiplicative E.X →* Multiplicative D.X :=
      e.val.weightEquiv.symm.toAddEquiv.toAddMonoidHom.toMultiplicative
    let he : ∀ i, i ∈ D.base.support → e.val.indexEquiv i ∈ E.base.support :=
      fun i hi => by
        change e.val.indexEquiv i ∈ (E.base.support : Set E.I)
        exact (congrArg (fun s : Set E.I => e.val.indexEquiv i ∈ s) e.property).mp
          (Set.mem_image_of_mem e.val.indexEquiv hi)
    ∃! f : Q.A ≃ₐc[IntegralRing.{u}] P.A, LiftsMarking P Q h e.val.indexEquiv he f.toBialgHom

/-- The finite diagonalizable kernel has character group the quotient by the character image. -/
def kernelRestriction {D E : BasedRootDatum.{u}} (P : Model D) (h : LatticeMap D E) :
    P.A →ₐc[IntegralRing.{u}] MonoidAlgebra IntegralRing.{u} (Multiplicative D.X ⧸ h.characters.range) :=
  (MonoidAlgebra.mapDomainBialgHom IntegralRing.{u} (QuotientGroup.mk' h.characters.range)).comp P.torus

/-- Every ordinary based isogeny lifts integrally and compatibly with the pins.
The torsor square is for the scheme kernel, including in residue characteristics
in which that kernel is nonreduced. -/
def CentralIsogenies : Prop :=
  ∀ {D E : BasedRootDatum.{u}} (P : Model D) (Q : Model E) (h : LatticeMap D E),
    ∃ f : Q.A →ₐc[IntegralRing.{u}] P.A,
      LiftsMarking P Q h.characters h.roots (fun i hi => (h.simple_iff i).mpr hi) f ∧
        IsCentral (kernelRestriction P h) ∧ IsRightTorsor f (kernelRestriction P h)

end

end LinearAlgebraicGroups.Specs.IntegralRecognition
