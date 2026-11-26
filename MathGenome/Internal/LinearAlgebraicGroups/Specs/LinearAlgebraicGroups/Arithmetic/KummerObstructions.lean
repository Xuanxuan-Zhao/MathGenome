import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.CentralCover
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.CentralCoverSpreading
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.FppfTorsors
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

noncomputable section

universe u v

namespace LinearAlgebraicGroups.Arithmetic.Kummer

/-- The group of unit classes modulo (n)-th powers. -/
abbrev Classes (R : Type*) [CommRing R] (n : ℕ) :=
  Rˣ ⧸ (powMonoidHom (α := Rˣ) n).range

/-- The class of a unit. -/
abbrev classOf {R : Type*} [CommRing R] (n : ℕ) (a : Rˣ) : Classes R n :=
  QuotientGroup.mk' (powMonoidHom (α := Rˣ) n).range a

/-- Change of coefficient ring on unit classes. -/
def map {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T) (n : ℕ) :
    Classes R n →* Classes T n :=
  QuotientGroup.map _ _ (Units.map f.toMonoidHom) (by
    rintro _ ⟨x, rfl⟩
    exact ⟨Units.map f.toMonoidHom x, (map_pow (Units.map f.toMonoidHom) x n).symm⟩)

/-- The inverse image of local unit classes in the global group. -/
def localUnitCondition {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K)
    (w : D.FinitePlace) (n : ℕ) : Subgroup (Classes K n) :=
  (map (D.integers w).subtype n).range.comap (map (D.embedding (.inl w)) n)

/-- Classes whose localizations come from local units at every nonarchimedean
place outside the allowed set. This formulation uses the valuation modulo (n),
independently of a choice of uniformizer. -/
def UnramifiedOutside {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K)
    (S : Set D.Place) (n : ℕ) : Subgroup (Classes K n) :=
  ⨅ w : {w : D.FinitePlace // Sum.inl w ∉ S}, localUnitCondition D w n

/-- Finiteness of the subgroup of global classes with valuations divisible by
(n) outside the allowed finite set. Archimedean places impose no valuation condition. -/
def GlobalFiniteness : Prop :=
  ∀ {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K)
    (S : Set D.Place), S.Finite → ∀ n : ℕ, 0 < n → Finite (UnramifiedOutside D S n)


open scoped TensorProduct
open Algebra.TensorProduct

/-- The character group of the group scheme of (n)-th roots of unity. -/
abbrev Characters (n : ℕ) := Multiplicative (ZMod n)

/-- The Hopf algebra of (\mu_n) over the indicated coefficient ring. -/
abbrev Mu (R : Type*) [CommRing R] (n : ℕ) := MonoidAlgebra R (Characters n)

/-- A coordinate action of (\mu_n). The two equations express associativity
of the action and the identity action. -/
structure Coaction (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) where
  hom : A →ₐ[R] A ⊗[R] Mu R n
  coassoc : ∀ x : A,
    hom.toLinearMap.rTensor (Mu R n) (hom x) =
      (TensorProduct.assoc R A (Mu R n) (Mu R n)).symm
        ((Coalgebra.comul (R := R) (A := Mu R n)).lTensor A (hom x))
  counit : ∀ x : A,
    (TensorProduct.rid R A) ((Coalgebra.counit (R := R) (A := Mu R n)).lTensor A (hom x)) = x

/-- Pullback along the map ((x,g) \mapsto (x,xg)) to the double fibre product. -/
def comparison {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}
    (ρ : Coaction R A n) : A ⊗[R] A →ₐ[R] A ⊗[R] Mu R n :=
  lift includeLeft ρ.hom fun _ _ => Commute.all _ _

/-- The affine faithfully flat torsor criterion. -/
def IsAffineTorsor {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}
    (ρ : Coaction R A n) : Prop :=
  Module.FaithfullyFlat R A ∧ Algebra.FinitePresentation R A ∧ Function.Bijective (comparison ρ)

/-- The equation defining the torsor of (n)-th roots of a unit. -/
def rootEquation {R : Type*} [CommRing R] (n : ℕ) (a : Rˣ) : Polynomial R :=
  Polynomial.X ^ n - Polynomial.C (a : R)

abbrev RootAlgebra {R : Type*} [CommRing R] (n : ℕ) (a : Rˣ) :=
  AdjoinRoot (rootEquation n a)

set_option maxHeartbeats 800000 in
/-- A degree-one unit generating a torsor coordinate ring presents it as the
algebra of roots of a scalar unit. The class of the scalar is independent
of the degree-one unit, without any invertibility hypothesis on (n). -/
def AffineTorsorPresentation : Prop :=
  ∀ {R A : Type u} [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A]
    (n : ℕ), 0 < n → ∀ (ρ : Coaction R A n), IsAffineTorsor ρ →
    ∃ (a : Rˣ) (e : RootAlgebra n a ≃ₐ[R] A),
      ρ.hom (e (AdjoinRoot.root (rootEquation n a))) =
        e (AdjoinRoot.root (rootEquation n a)) ⊗ₜ[R]
          MonoidAlgebra.of R (Characters n) (Multiplicative.ofAdd 1) ∧
      ∀ (b : Rˣ) (x : Aˣ),
        ρ.hom (x : A) = (x : A) ⊗ₜ[R] MonoidAlgebra.of R (Characters n) (Multiplicative.ofAdd 1) →
        (x : A) ^ n = algebraMap R A (b : R) →
        classOf n b = classOf n a

set_option maxHeartbeats 800000 in
/-- The finite-image implication used for obstruction coordinates of integral
pullbacks. Classes over completed valuation rings map to the corresponding
global unramified condition by restriction of scalars to their fraction fields. -/
def FiniteIntegralCoordinates : Prop :=
  ∀ {E : Type u} [Field E] (D : GlobalFieldData.{u, v} E) (S : Set D.Place), S.Finite →
    ∀ {I : Type} [Finite I] (n : I → ℕ), (∀ i, 0 < n i) →
    ∀ {X : Type u} (c : X → ((i : I) → Classes E (n i))),
      (∀ (x : X) (i : I) (w : D.FinitePlace), Sum.inl w ∉ S →
        ∃ q : Classes (D.integers w) (n i),
          map (D.integers w).subtype (n i) q =
            map (D.embedding (.inl w)) (n i) (c x i)) →
      (Set.range c).Finite


/-- Taking the (n)-th root of any unit defines a finite faithfully flat
torsor, with the action given by multiplying the root by the character. -/
def RootTorsor : Prop :=
  ∀ {R : Type u} [CommRing R] [Nontrivial R] (n : ℕ), 0 < n → ∀ a : Rˣ,
    ∃ ρ : Coaction R (RootAlgebra n a) n, IsAffineTorsor ρ ∧
      ρ.hom (AdjoinRoot.root (rootEquation n a)) =
        AdjoinRoot.root (rootEquation n a) ⊗ₜ[R]
          MonoidAlgebra.of R (Characters n) (Multiplicative.ofAdd 1)


/-- The scalar read off from the nth power of a homogeneous unit in degree one. -/
def HasClass {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}
    (ρ : Coaction R A n) (c : Classes R n) : Prop :=
  ∃ (a : Rˣ) (x : Aˣ), classOf n a = c ∧
    ρ.hom (x : A) = (x : A) ⊗ₜ[R] MonoidAlgebra.of R (Characters n) (Multiplicative.ofAdd 1) ∧
    (x : A) ^ n = algebraMap R A (a : R)

/-- Every affine torsor over a local ring has a unique scalar class. -/
def AffineTorsorClass : Prop :=
  ∀ {R A : Type u} [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A]
    (n : ℕ), 0 < n → ∀ (ρ : Coaction R A n), IsAffineTorsor ρ →
    ∃! c : Classes R n, HasClass ρ c

/-- The map on coaction tensors for a coefficient map and a compatible
map of coordinate rings. -/
def coactionTensorMap {R T A B : Type*} [CommRing R] [CommRing T] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra T B] (f : R →+* T) (g : A →+* B)
    (hg : g.comp (algebraMap R A) = (algebraMap T B).comp f) (n : ℕ) :
    A ⊗[R] Mu R n →+* B ⊗[T] Mu T n := by
  letI : Algebra R (B ⊗[T] Mu T n) :=
    ((algebraMap T (B ⊗[T] Mu T n)).comp f).toAlgebra
  let b : A →ₐ[R] B ⊗[T] Mu T n :=
    { toRingHom := (includeLeft : B →ₐ[T] B ⊗[T] Mu T n).toRingHom.comp g
      commutes' := fun r => by
        change (includeLeft : B →ₐ[T] B ⊗[T] Mu T n) (g (algebraMap R A r)) =
          algebraMap T (B ⊗[T] Mu T n) (f r)
        rw [show g (algebraMap R A r) = algebraMap T B (f r) from DFunLike.congr_fun hg r]
        exact (includeLeft : B →ₐ[T] B ⊗[T] Mu T n).commutes (f r) }
  let h : Mu R n →ₐ[R] B ⊗[T] Mu T n :=
    (MonoidAlgebra.lift R _ (Characters n))
      ((includeRight : Mu T n →ₐ[T] B ⊗[T] Mu T n).toMonoidHom.comp
        (MonoidAlgebra.of T (Characters n)))
  exact (Algebra.TensorProduct.lift b h (fun _ _ => Commute.all _ _)).toRingHom

/-- Functoriality of the Kummer class under an equivariant scalar extension
of a torsor, in particular under passage from a local ring to its fraction field. -/
def AffineClassNaturality : Prop :=
  ∀ {R T A B : Type u} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra T B] (n : ℕ)
    (ρ : Coaction R A n) (σ : Coaction T B n)
    (f : R →+* T) (g : A →+* B) (hg : g.comp (algebraMap R A) = (algebraMap T B).comp f),
    (∀ z, coactionTensorMap f g hg n (ρ.hom z) = σ.hom (g z)) →
    ∀ c : Classes R n, HasClass ρ c → HasClass σ (map f n c)


open scoped WithZero in
/-- The local unit condition is precisely divisibility of the normalized
discrete valuation of a representative. The sign convention on the
multiplicative valuation does not affect divisibility. -/
def ValuationCriterion : Prop :=
  ∀ {E : Type u} [Field E] (D : GlobalFieldData.{u, v} E) (w : D.FinitePlace),
    ∃ ν : Valuation (D.FiniteCompletion w) ℤᵐ⁰,
      Function.Surjective ν ∧ ν.valuationSubring = D.integers w ∧
      ∀ (n : ℕ) (a : Eˣ), classOf n a ∈ localUnitCondition D w n ↔
        (n : ℤ) ∣ (ν (D.embedding (.inl w) (a : E))).log


/-- Affine torsors over a local ring represent all scalar classes, and two
affine torsors represent the same class precisely when they are equivariantly
isomorphic over that ring. -/
def AffineTorsorClassification : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (n : ℕ), 0 < n →
    (∀ c : Classes R n, ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A)
      (ρ : Coaction R A n), IsAffineTorsor ρ ∧ HasClass ρ c) ∧
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
      (ρ : Coaction R A n) (σ : Coaction R B n),
      IsAffineTorsor ρ → IsAffineTorsor σ →
      ((∃ e : A ≃ₐ[R] B, ∀ x,
        Algebra.TensorProduct.map e.toAlgHom (AlgHom.id R (Mu R n)) (ρ.hom x) = σ.hom (e x)) ↔
        ∃ c : Classes R n, HasClass ρ c ∧ HasClass σ c)

section Cover

open AlgebraicGeometry CategoryTheory
open Specs.IntegralCentralQuotient (OverBase HopfSpectrum spectrumOfHopfHom rightCoaction IsRightTorsor)
open Specs.CentralCover (FiniteKernelTorsor integersOutside integralRootsOfUnityProduct)
open Specs.CentralCoverSpreading (KernelCoordinates)

/-- The character whose evaluation is projection to the indicated cyclic factor. -/
def coordinateCharacter {I : Type} (n : I → ℕ) (i : I) :
    ULift.{u} (∀ j, Characters (n j)) := by
  classical
  exact ⟨Pi.mulSingle i (Multiplicative.ofAdd 1)⟩

/-- Read the obstruction of a fibre from a homogeneous coordinate on the
source of the cover. The tensor product is the coordinate ring of the fibre
at the specified point. -/
def PullbackHasClass {R B A T : Type u} [CommRing R] [CommRing B] [CommRing A]
    [CommRing T] [HopfAlgebra R A] [Algebra R B] [Algebra B A] [Algebra R T]
    {I : Type} (n : I → ℕ) (π : A →ₐc[R] KernelCoordinates R n)
    (p : B →ₐ[R] T) (i : I) (c : Classes T (n i)) : Prop :=
  letI : Algebra B T := p.toAlgebra
  ∃ (b : A) (a : Tˣ),
    rightCoaction π b = b ⊗ₜ[R] MonoidAlgebra.of R _ (coordinateCharacter n i) ∧
    IsUnit ((1 : T) ⊗ₜ[B] b) ∧
    ((1 : T) ⊗ₜ[B] b) ^ n i = algebraMap T (T ⊗[B] A) (a : T) ∧
    classOf (n i) a = c

/-- The canonical map from the integers away from the exceptional set to a
completed valuation ring at a place outside that set. -/
def integersOutsideToLocal {E : Type u} [Field E] (D : GlobalFieldData.{u, v} E)
    (S : Set D.FinitePlace) (w : D.FinitePlace) (hw : w ∉ S) :
    integersOutside D S →+* D.integers w :=
  ((D.embedding (.inl w)).comp (integersOutside D S).subtype).codRestrict
    (D.integers w).toSubring fun a => Subring.mem_iInf.mp a.property ⟨w, hw⟩

/-- The target points that extend to the valuation ring outside the exceptional
set. They are given on the coordinate ring of the target integral model. -/
def IntegralModelPoints {E R B : Type u} [Field E] [CommRing R] [CommRing B]
    [Algebra R B] [Algebra R E] (D : GlobalFieldData.{u, v} E)
    (S : Set D.FinitePlace) (ι : ∀ w : D.FinitePlace, w ∉ S → R →+* D.integers w) :=
  {p : B →ₐ[R] E // ∀ (w : D.FinitePlace) (hw : w ∉ S),
    letI : Algebra R (D.integers w) := (ι w hw).toAlgebra
    ∃ pᵥ : B →ₐ[R] D.integers w,
      (D.integers w).subtype.comp pᵥ.toRingHom =
        (D.embedding (.inl w)).comp p.toRingHom}

/-- Pullbacks of the finite flat cover with split kernel have canonical
Kummer coordinates. On points integral away from a finite set their image
is finite. -/
def CoverPullbackFiniteness : Prop :=
  ∀ {E : Type u} [Field E] (D : GlobalFieldData.{u, v} E)
    (S : Set D.FinitePlace), S.Finite →
    let R := ↥(integersOutside D S)
    ∀ {I : Type} [Finite I] (n : I → ℕ), (∀ i, 0 < n i) →
    ∀ {G H Z : Grp (OverBase R)} (q : H ⟶ G) (j : Z ⟶ H),
      IsAffine G.X.left → IsAffine H.X.left →
      FiniteKernelTorsor q j →
      ∀ eZ : Z ≅ integralRootsOfUnityProduct R n,
      ∃ (B A : Type u) (_ : CommRing B) (_ : CommRing A)
        (_ : HopfAlgebra R B) (_ : HopfAlgebra R A)
        (eG : HopfSpectrum R B ≅ G) (eH : HopfSpectrum R A ≅ H)
        (q₀ : B →ₐc[R] A) (π : A →ₐc[R] KernelCoordinates R n),
        spectrumOfHopfHom q₀ ≫ eG.hom = eH.hom ≫ q ∧
        spectrumOfHopfHom π ≫ eH.hom = eZ.inv ≫ j ∧
        IsRightTorsor q₀ π ∧
        letI : Algebra B A := q₀.toAlgHom.toAlgebra
        (∀ {T : Type u} [CommRing T] [Algebra R T] [IsLocalRing T] (p : B →ₐ[R] T) (i : I),
          ∃! c, PullbackHasClass n π p i c) ∧
        ∃ c : (B →ₐ[R] E) → ((i : I) → Classes E (n i)),
          (∀ p i, PullbackHasClass n π p i (c p i) ∧
            ∀ d, PullbackHasClass n π p i d → d = c p i) ∧
          (Set.range (fun p : IntegralModelPoints D S (integersOutsideToLocal D S) => c p.val)).Finite

/-- A point of a closed affine model extends across an injective coefficient map
if all the ambient coordinates extend. -/
def ClosedModelPointLift : Prop :=
  ∀ {R C B V L : Type u} [CommRing R] [CommRing C] [CommRing B] [CommRing V]
    [CommRing L] [Algebra R C] [Algebra R B] [Algebra R V] [Algebra R L]
    (j : C →ₐ[R] B), Function.Surjective j → ∀ (ι : V →ₐ[R] L),
    Function.Injective ι → ∀ (p : B →ₐ[R] L) (a : C →ₐ[R] V),
      p.comp j = ι.comp a → ∃ p₀ : B →ₐ[R] V, ι.comp p₀ = p

/-- Extending the coefficient ring transports the class of the fibre at a
point to the class at the extended point. -/
def PullbackClassNaturality : Prop :=
  ∀ {R B A T U : Type u} [CommRing R] [CommRing B] [CommRing A] [CommRing T]
    [CommRing U] [HopfAlgebra R A] [Algebra R B] [Algebra B A] [Algebra R T] [Algebra R U]
    {I : Type} (n : I → ℕ) (π : A →ₐc[R] KernelCoordinates R n)
    (p : B →ₐ[R] T) (p' : B →ₐ[R] U) (f : T →+* U),
    f.comp p.toRingHom = p'.toRingHom → ∀ (i : I) (c : Classes T (n i)),
    PullbackHasClass n π p i c → PullbackHasClass n π p' i (map f (n i) c)

/-- The scalar class is realized by the indicated root torsor, with a map from
the actual fibre equivariant for the projection to the chosen cyclic factor. -/
def PullbackRootMap : Prop :=
  ∀ {R B A T : Type u} [CommRing R] [CommRing B] [CommRing A] [CommRing T]
    [HopfAlgebra R A] [Algebra R B] [Algebra B A] [Algebra R T] {I : Type}
    (n : I → ℕ) (π : A →ₐc[R] KernelCoordinates R n) (p : B →ₐ[R] T)
    (i : I) (c : Classes T (n i)), PullbackHasClass n π p i c →
    letI : Algebra B T := p.toAlgebra
    ∃ (a : Tˣ) (b : A) (e : RootAlgebra (n i) a →ₐ[T] T ⊗[B] A),
      classOf (n i) a = c ∧
        e (AdjoinRoot.root (rootEquation (n i) a)) = (1 : T) ⊗ₜ[B] b ∧
        (∀ {L : Type u} [CommRing L] [Algebra R L]
          (x : A →ₐ[R] L) (z : KernelCoordinates R n →ₐ[R] L),
          let ζ := z (MonoidAlgebra.of R _ (coordinateCharacter n i))
          ζ ^ n i = 1 ∧
            (lift x z (fun _ _ => Commute.all _ _)) (rightCoaction π b) = x b * ζ)

end Cover

open AlgebraicGeometry CategoryTheory Opposite
open Specs.IntegralCentralQuotient (OverBase)
open Specs.Fppf (Torsor RightAction RightActionIso)

section Sheaves

variable {R : Type u} [CommRing R]

/-- The big fppf site over the given coefficient ring. -/
abbrev topology (R : Type u) [CommRing R] :=
  Scheme.fppfTopology.over (Spec (CommRingCat.of R))

abbrev globalRing (X : OverBase R) := ((algΓ (CommRingCat.of R)).obj X).unop

abbrev globalMap {X Y : OverBase R} (f : X ⟶ Y) : globalRing Y →ₐ[R] globalRing X :=
  ((algΓ (CommRingCat.of R)).map f).unop.hom

/-- The group of nth roots of unity on each test scheme, with restriction on
its global sections. -/
def rootsGroup (R : Type u) [CommRing R] (n : ℕ) : (OverBase R)ᵒᵖ ⥤ GrpCat.{u} where
  obj X := GrpCat.of (rootsOfUnity n (globalRing X.unop))
  map f := GrpCat.ofHom (restrictRootsOfUnity (globalMap f.unop).toRingHom n)
  map_id X := by
    apply GrpCat.ext
    intro x
    apply Subtype.ext
    apply Units.ext
    exact congrArg (fun f => f.unop.hom x.val.val) ((algΓ (CommRingCat.of R)).map_id X.unop)
  map_comp f g := by
    apply GrpCat.ext
    intro x
    apply Subtype.ext
    apply Units.ext
    change (((algΓ (CommRingCat.of R)).map (g.unop ≫ f.unop)).unop.hom x.val.val) = _
    rw [Functor.map_comp]
    rfl

/-- Sections of the specified root equation, evaluated on a test algebra. -/
abbrev RootSolutions (n : ℕ) (a : Rˣ) (T : Type*) [CommRing T] [Algebra R T] :=
  {b : Tˣ // b ^ n = Units.map (algebraMap R T).toMonoidHom a}

namespace RootSolutions

def map {T U : Type*} [CommRing T] [CommRing U] [Algebra R T] [Algebra R U]
    {n : ℕ} {a : Rˣ} (f : T →ₐ[R] U) (b : RootSolutions n a T) : RootSolutions n a U :=
  ⟨Units.map f.toMonoidHom b.val, by
    rw [← map_pow, b.property]
    exact Units.ext (f.commutes a.val)⟩

def act {T : Type*} [CommRing T] [Algebra R T] {n : ℕ} {a : Rˣ}
    (b : RootSolutions n a T) (g : rootsOfUnity n T) : RootSolutions n a T :=
  ⟨b.val * g.val, by rw [mul_pow, b.property, (mem_rootsOfUnity n g.val).mp g.property, mul_one]⟩

end RootSolutions

abbrev MuTorsor (R : Type u) [CommRing R] (n : ℕ) :=
  Torsor (topology R) (rootsGroup R n)

/-- A right mu_n-torsor is presented by a root equation when its sections are
the roots on all test schemes, naturally and equivariantly. -/
structure RootPresentation {n : ℕ} (P : MuTorsor R n) (a : Rˣ) where
  equiv : ∀ X : OverBase R, P.val.Section X ≃ RootSolutions n a (globalRing X)
  natural : ∀ {X Y : OverBase R} (f : X ⟶ Y) (x : P.val.Section Y),
    equiv X (P.val.res f x) = RootSolutions.map (globalMap f) (equiv Y x)
  equivariant : ∀ {X : OverBase R} (x : P.val.Section X) (g : (rootsGroup R n).obj (op X)),
    equiv X (P.val.act x g) = (equiv X x).act g

/-- The fppf Kummer classification over a local ring, with its root equations
and with no restriction on the residue characteristic. -/
def FppfTorsorClassification : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ), 0 < n →
    Presheaf.IsSheaf (topology R) (rootsGroup R n ⋙ forget GrpCat) ∧
    (∀ a : Rˣ, ∃ P : MuTorsor R n, Nonempty (RootPresentation P a)) ∧
    (∀ P : MuTorsor R n, ∃ a : Rˣ, Nonempty (RootPresentation P a)) ∧
    ∀ (P Q : MuTorsor R n) (a b : Rˣ), RootPresentation P a → RootPresentation Q b →
      (Nonempty (RightActionIso P.val Q.val) ↔ classOf n a = classOf n b)

end Sheaves

end LinearAlgebraicGroups.Arithmetic.Kummer
