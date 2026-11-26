import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralCentralQuotient
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.Pinning

open AlgebraicGeometry CategoryTheory Opposite WithConv
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.IntegralLinkedRoots

open IntegralCentralQuotient (IntegralRing HopfSpectrum spectrumOfHopfHom RootScalarAction
  cocharacterEval)
open Pinning (AttachedDatum BasedIso BasedRootDatum SplitBorelPair)
open RootGroups (AdditiveLine IsRootSubgroup rootPoint)
open CharacterDescent (Character)
open DiagonalizableGroups (IntegerCharacters integerGenerator)

noncomputable section

variable {R A : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]

/-- The points of the affine group, given by convolution on algebra maps. -/
abbrev HopfPoints (R A S : Type u) [CommRing R] [CommRing A] [HopfAlgebra R A]
    [CommRing S] [Algebra R S] := WithConv (A →ₐ[R] S)

/-- The antipode defines inverse points over every commutative test algebra. -/
@[instance_reducible] def pointGroup {S : Type u} [CommRing S] [Algebra R S] : Group (HopfPoints R A S) where
  inv f := toConv (f.ofConv.comp (HopfAlgebra.antipodeAlgHom R A))
  inv_mul_cancel f := by
    change toConv (f.ofConv.comp (HopfAlgebra.antipodeAlgHom R A)) * f = 1
    have h := AlgHom.comp_convMul_distrib f.ofConv
      (toConv (HopfAlgebra.antipodeAlgHom R A)) (toConv (AlgHom.id R A))
    rw [AlgHom.antipode_id_cancel, AlgHom.convOne_def, AlgHom.comp_id] at h
    apply WithConv.ext
    rw [← h]
    ext a
    exact f.ofConv.commutes _

attribute [local instance] pointGroup

/-- The test point of a polynomial coordinate. -/
def evaluate {S : Type u} [CommRing S] [Algebra R S] (x : A →ₐ[R] Polynomial R) (a : S) :
    HopfPoints R A S :=
  toConv ((Polynomial.aeval a).comp x)

/-- Additive coordinates are group homomorphisms on every test algebra. -/
def IsAdditive (x : A →ₐ[R] Polynomial R) : Prop :=
  ∀ (S : CommAlgCat.{u} R),
    evaluate x (0 : S) = 1 ∧
      ∀ a b : S, evaluate x (a + b) = evaluate x a * evaluate x b

/-- The datum is calibrated on the specified torus, including its full character lattice. -/
structure FibreFrame (D : BasedRootDatum.{u})
    (t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X))
    (K : Type u) [Field K] [Algebra R K] where
  pair : SplitBorelPair K
  groupIso : HopfSpectrum K (K ⊗[R] A) ≅ pair.G.val
  torusIso : HopfSpectrum K (K ⊗[R] MonoidAlgebra R (Multiplicative D.X)) ≅ pair.T.group
  datum : AttachedDatum pair
  marking : BasedIso D datum.toBased
  torus_eq :
    spectrumOfHopfHom (Bialgebra.TensorProduct.map (BialgHom.id K K) t) ≫ groupIso.hom =
      torusIso.hom ≫ pair.T.inclusion
  character_eq : ∀ χ : D.X,
    let c := torusIso.hom ≫ Additive.toMul (marking.val.weightEquiv χ)
    let f := ((algSpec.fullyFaithful (R := CommRingCat.of K)).preimage c.hom.hom).unop
    f.hom (MonoidAlgebra.of K IntegerCharacters integerGenerator) =
      (1 : K) ⊗ₜ[R] MonoidAlgebra.of R (Multiplicative D.X) (Multiplicative.ofAdd χ)

/-- A relative tangent vector at the identity is an identity-reducing dual-number point. -/
abbrev Tangent (R A : Type u) [CommRing R] [CommRing A] [HopfAlgebra R A] :=
  {v : A →ₐ[R] DualNumber R //
    (TrivSqZeroExt.fstHom R R R).comp v = Bialgebra.counitAlgHom R A}

def dualCoefficients (K : Type u) [CommRing K] [Algebra R K] : DualNumber R →ₐ[R] DualNumber K where
  toRingHom := InfinitesimalCommutator.mapCoefficients (algebraMap R K)
  commutes' _ := TrivSqZeroExt.ext rfl (map_zero (algebraMap R K))

/-- The torus acts on the tangent vector by the indicated character. -/
def HasWeight {X : Type u} [CommGroup X] (t : A →ₐc[R] MonoidAlgebra R X)
    (χ : X) (v : Tangent R A) : Prop :=
  ∀ (S : CommAlgCat.{u} R) (s : MonoidAlgebra R X →ₐ[R] S),
    let g : HopfPoints R A (DualNumber S) :=
      toConv ((TrivSqZeroExt.inlAlgHom R S S).comp (s.comp t.toAlgHom))
    let p := (dualCoefficients S).comp v.val
    let c := s (MonoidAlgebra.of R X χ)
    let scale := (TrivSqZeroExt.map (c • (LinearMap.id : S →ₗ[S] S))).restrictScalars R
    g * toConv p * g⁻¹ = toConv (scale.comp p)

/-- The pinned vector is a basis of its integral tangent weight line. -/
def IsWeightBasis {X : Type u} [CommGroup X] (t : A →ₐc[R] MonoidAlgebra R X)
    (χ : X) (v : Tangent R A) : Prop :=
  HasWeight t χ v ∧ ∀ w : Tangent R A, HasWeight t χ w →
    ∃! c : R, ∀ a : A, (w.val a).snd = c * (v.val a).snd

variable {K : Type u} [Field K] [Algebra R K]

/-- Base change of a polynomial pullback. -/
def extendRoot (x : A →ₐ[R] Polynomial R) : K ⊗[R] A →ₐ[K] Polynomial K :=
  AlgHom.liftEquiv R K A (Polynomial K) ((Polynomial.mapAlgHom (Algebra.ofId R K)).comp x)

/-- The displayed coordinate is a parametrization of the actual geometric root subgroup. -/
def FibreCoordinate {D : BasedRootDatum.{u}}
    {t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X)} (F : FibreFrame D t K)
    (i : D.I) (x : A →ₐ[R] Polynomial R) : Prop :=
  let α := (F.marking.val.indexEquiv i).val
  ∃ (U : ClosedSubgroup F.pair.G.val) (L : AdditiveLine K) (j : L.group ≅ U.group),
    IsRootSubgroup F.pair.T U α ∧
    ∀ (S : CommAlgCat.{u} K) (a : S),
      (testSpec K).map (CommAlgCat.ofHom (evaluate (extendRoot (K := K) x) a).ofConv).op ≫
        F.groupIso.hom.hom.hom = rootPoint (j.hom ≫ U.inclusion) S a

/-- The initial root coordinates, including their given specialization in every geometric fibre. -/
def RootCoordinates {D : BasedRootDatum.{u}}
    (t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X))
    (pin : ↥D.base.support → Tangent R A) (x : D.I → A →ₐ[R] Polynomial R) : Prop :=
  (∀ i, Function.Surjective (x i) ∧ IsAdditive (x i) ∧
    RootScalarAction t (x i) (Multiplicative.ofAdd (D.datum.root i))) ∧
  (∀ i : ↥D.base.support, (evaluate (x i.val) (DualNumber.eps : DualNumber R)).ofConv =
    (pin i).val) ∧
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K],
    ∃ F : FibreFrame D t K, ∀ i, FibreCoordinate F i (x i)

/-- Contravariant on characters, covariant on root indices, and ordinary on all roots and coroots. -/
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

def LatticeMap.simple {D E : BasedRootDatum.{u}} (h : LatticeMap D E) :
    ↥D.base.support → ↥E.base.support := fun i => ⟨h.roots i.val, (h.simple_iff i.val).mpr i.property⟩

/-- The ordinary rank-one word for a positive and a negative additive coordinate. -/
def rankOneWord (x y : A →ₐ[R] Polynomial R) {S : Type u} [CommRing S] [Algebra R S]
    (a : Sˣ) : HopfPoints R A S :=
  evaluate x (a : S) * evaluate y (-(↑a⁻¹ : S)) * evaluate x (a : S)

/-- The pairing with a marked coroot is an integral torus cocharacter. -/
def coroot {D : BasedRootDatum.{u}} (i : D.I) : Multiplicative D.X →* Multiplicative ℤ where
  toFun χ := Multiplicative.ofAdd (D.datum.toLinearMap χ.toAdd (D.datum.coroot i))
  map_one' := by change Multiplicative.ofAdd (D.datum.toLinearMap 0 _) = _; simp
  map_mul' χ ψ := by change Multiplicative.ofAdd (D.datum.toLinearMap (_ + _) _) = _; simp

/-- The rescaled negative coordinate is linked to the pinned positive coordinate by the coroot. -/
def IsLinked {D : BasedRootDatum.{u}}
    (t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X)) (i : D.I)
    (x y : A →ₐ[R] Polynomial R) : Prop :=
  ∀ (S : CommAlgCat.{u} R) (a : Sˣ),
    rankOneWord x y a * (rankOneWord x y (1 : Sˣ))⁻¹ =
      toConv ((cocharacterEval (coroot i) S a).comp t.toAlgHom)

/-- Apply a list of simple reflections, with the head acting last. -/
def reflectWord {D : BasedRootDatum.{u}} (w : List ↥D.base.support) (i : D.I) : D.I :=
  w.foldr (fun j k => D.datum.reflectionPerm j.val k) i

/-- The corresponding integral normalizer word, using source integral coordinates. -/
def evaluateWord {D : BasedRootDatum.{u}} (x : D.I → A →ₐ[R] Polynomial R)
    (w : List ↥D.base.support) (S : CommAlgCat.{u} R) : HopfPoints R A S :=
  (w.map fun i =>
    rankOneWord (x i.val) (x (D.datum.reflectionPerm i.val i.val)) (1 : Sˣ)).prod

/-- A choice of a simple root, one of its two linked coordinates, and a Weyl word. -/
structure RootWord (D : BasedRootDatum.{u}) where
  simple : ↥D.base.support
  negative : Bool
  word : List ↥D.base.support

def RootWord.start {D : BasedRootDatum.{u}} (w : RootWord D) : D.I :=
  if w.negative then D.datum.reflectionPerm w.simple.val w.simple.val else w.simple.val

def RootWord.map {D E : BasedRootDatum.{u}} (h : LatticeMap D E) (w : RootWord D) : RootWord E :=
  ⟨h.simple w.simple, w.negative, w.word.map h.simple⟩

/-- A chosen family is obtained from the linked simple pairs by these words. -/
def UsesWords {D : BasedRootDatum.{u}} (x : D.I → A →ₐ[R] Polynomial R)
    (choices : D.I → RootWord D) : Prop :=
  ∀ i, let w := choices i
    reflectWord w.word w.start = i ∧
      ∀ (S : CommAlgCat.{u} R) (a : S),
        evaluate (x i) a =
          evaluateWord x w.word S * evaluate (x w.start) a * (evaluateWord x w.word S)⁻¹

/-- Extend a dual-number point to the geometric fibre. -/
def extendTangent (v : Tangent R A) : K ⊗[R] A →ₐ[K] DualNumber K :=
  AlgHom.liftEquiv R K A (DualNumber K) ((dualCoefficients K).comp v.val)

/-- The full marked torus and the marked simple tangent vectors on the generic fibre. -/
def GenericMarking {D E : BasedRootDatum.{u}} {B : Type u} [CommRing B] [HopfAlgebra R B]
    (t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X))
    (s : B →ₐc[R] MonoidAlgebra R (Multiplicative E.X))
    (p : ↥D.base.support → Tangent R A) (q : ↥E.base.support → Tangent R B)
    (h : LatticeMap D E) (f : K ⊗[R] B →ₐc[K] K ⊗[R] A) : Prop :=
  let extend := fun {C C' : Type u} [CommRing C] [CommRing C'] [Bialgebra R C] [Bialgebra R C']
    (g : C →ₐc[R] C') => Bialgebra.TensorProduct.map (BialgHom.id K K) g
  (extend t).comp f = (extend (MonoidAlgebra.mapDomainBialgHom R h.characters)).comp (extend s) ∧
  ∀ (i : ↥D.base.support) (b : B),
    extendTangent (K := K) (p i) (f ((1 : K) ⊗ₜ[R] b)) =
      dualCoefficients K ((q ⟨h.roots i.val, (h.simple_iff i.val).mpr i.property⟩).val b)

/-- A finite surjective homomorphism whose scheme kernel is central. -/
def IsCentralIsogeny {B C : Type u} [CommRing B] [CommRing C] [HopfAlgebra K B] [HopfAlgebra K C]
    (f : B →ₐc[K] C) : Prop :=
  let g := (spectrumOfHopfHom f).hom.hom.left
  IsFinite g ∧ Surjective g ∧
    ∀ (S : CommAlgCat.{u} K) (p q : HopfPoints K C S),
      p.ofConv.comp f.toAlgHom = (1 : HopfPoints K B S).ofConv → p * q = q * p

/-- Normalization and Weyl transport are integral and can be chosen before the generic lift. -/
def LinkedCoordinatesOver (R : Type u) [CommRing R] : Prop :=
  ∀ {D E : BasedRootDatum.{u}} {A B : Type u}
    [CommRing A] [CommRing B] [HopfAlgebra R A] [HopfAlgebra R B],
    Algebra.FinitePresentation R A → Algebra.FinitePresentation R B →
    Smooth (HopfSpectrum R A).X.hom → Smooth (HopfSpectrum R B).X.hom →
    ∀ (t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X))
      (s : B →ₐc[R] MonoidAlgebra R (Multiplicative E.X)),
      Function.Surjective t → Function.Surjective s →
      ∀ (p : ↥D.base.support → Tangent R A) (q : ↥E.base.support → Tangent R B),
        (∀ i, IsWeightBasis t (Multiplicative.ofAdd (D.datum.root i.val)) (p i)) →
        (∀ i, IsWeightBasis s (Multiplicative.ofAdd (E.datum.root i.val)) (q i)) →
        ∀ (h : LatticeMap D E) (x : D.I → A →ₐ[R] Polynomial R)
          (y : E.I → B →ₐ[R] Polynomial R),
          RootCoordinates t p x → RootCoordinates s q y →
          ∃ (x' : D.I → A →ₐ[R] Polynomial R) (y' : E.I → B →ₐ[R] Polynomial R)
            (w : D.I → RootWord D),
            RootCoordinates t p x' ∧ RootCoordinates s q y' ∧
            (∀ i : ↥D.base.support, x' i.val = x i.val ∧
              IsLinked t i.val (x' i.val) (x' (D.datum.reflectionPerm i.val i.val))) ∧
            (∀ i : ↥E.base.support, y' i.val = y i.val ∧
              IsLinked s i.val (y' i.val) (y' (E.datum.reflectionPerm i.val i.val))) ∧
            UsesWords x' w ∧
            UsesWords y' (fun j => (w (h.roots.symm j)).map h) ∧
            ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K]
              (f : K ⊗[R] B →ₐc[K] K ⊗[R] A),
              IsCentralIsogeny f → GenericMarking t s p q h f →
              ∀ i, (extendRoot (K := K) (x' i)).comp f.toAlgHom =
                extendRoot (K := K) (y' (h.roots i))

/-- The linked-root construction for marked models over the integers. -/
def Statement : Prop := LinkedCoordinatesOver IntegralRing.{u}

end

end LinearAlgebraicGroups.Specs.IntegralLinkedRoots
