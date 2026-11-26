import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SpinScalarExtension
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.RationalRepresentations

/-! Descent of the regular odd Clifford model and rigidity of the based type-B datum. -/

open CategoryTheory
open scoped TensorProduct CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.OddSpinInnerDescent

open LinearAlgebraicGroups.Descent (SemilinearAction)
open LinearAlgebraicGroups.Albert.CliffordSpecification (coefficientForm)
open Pinning (BasedRootDatum BasedIso)

noncomputable section

/-- Regularity includes the odd characteristic-two case of a polar radical line
on which the quadratic norm is nonzero. -/
def IsRegular {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
    (q : QuadraticForm k V) : Prop :=
  LinearMap.ker q.polarBilin = ⊥ ∨
    ∃ r : V, q r ≠ 0 ∧ LinearMap.ker q.polarBilin = k ∙ r

/-- Type-B Cartan entries, with roots indexing rows and coroots indexing columns.
The terminal simple root is short. -/
def typeBCartan (n : ℕ) (i j : Fin (n + 1)) : ℤ :=
  if i = j then 2
  else if i.val + 1 = j.val ∧ j.val = n then -2
  else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1
  else 0

/-- The based type-B diagram has trivial automorphism group, with the directed
double edge retained, including in ranks one and two. -/
def DiagramRigidity : Prop :=
  ∀ (n : ℕ) (p : Equiv.Perm (Fin (n + 1))),
    (∀ i j, typeBCartan n (p i) (p j) = typeBCartan n i j) → p = Equiv.refl _

/-- The simple vectors of a semisimple based datum span the lattice rationally. -/
def SpansRationally {L : Type u} [AddCommGroup L] (s : Set L) : Prop :=
  ∀ x : L, ∃ m : ℤ, m ≠ 0 ∧ m • x ∈ Submodule.span ℤ s

/-- The coroot lattice criterion for simple connectedness gives rational
spanning by the simple coroots. -/
def SimpleCorootsSpan : Prop :=
  ∀ (D : BasedRootDatum.{u}) (n : ℕ) (b : Fin (n + 1) ≃ D.base.support),
    Submodule.span ℤ (Set.range D.datum.coroot) = ⊤ →
    SpansRationally (Set.range fun i => D.datum.coroot (b i).val)

/-- Rigidity for the complete based datum, including its two integral
lattices, when the simple coroots span the rational cocharacter space. -/
def BasedDatumRigidity : Prop :=
  ∀ (D : BasedRootDatum.{u}) (n : ℕ) (b : Fin (n + 1) ≃ D.base.support),
    (∀ i j, D.datum.pairing (b i).val (b j).val = typeBCartan n i j) →
    SpansRationally (Set.range fun i => D.datum.coroot (b i).val) →
    ∀ f : Aut D, f = 1

/-- An invariant regular quadratic form descends to the fixed vector space
with the canonical scalar-extension isometry and the same dimension. -/
def QuadraticDescent : Prop :=
  ∀ {k K V : Type u} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] [AddCommGroup V]
    [Module k V] [Module K V] [IsScalarTower k K V] [Module.Finite K V]
    (a : SemilinearAction k K V) (Q : QuadraticForm K V),
    (∀ σ x, Q (a.act σ x) = σ (Q x)) →
    ∃ q : QuadraticForm k a.fixed,
      (∀ x, algebraMap k K (q x) = Q x.val) ∧
      (∀ {I : Type u} [LinearOrder I] (b : Module.Basis I k a.fixed),
        ∃ e : (K ⊗[k] a.fixed) ≃ₗ[K] V,
          e.toLinearMap = a.descentMap ∧
          ∀ x, Q (e x) = coefficientForm K q b x) ∧
      Module.finrank k a.fixed = Module.finrank K V ∧
      (IsRegular Q → IsRegular q)

section Clifford

open CliffordAlgebra
open LinearAlgebraicGroups.Albert
open LinearAlgebraicGroups.Albert.SpinSpecification
  (ScalarClifford vectors reversion evenPart spinUnits coefficientMap)

/-- An isometry induces the prescribed vector-preserving Clifford isomorphisms
on all test algebras, commuting with reversion and carrying the spin equations
in both directions. -/
def CliffordIsometryComparison : Prop :=
  ∀ {k V W : Type u} [Field k] [AddCommGroup V] [AddCommGroup W]
    [Module k V] [Module k W] (q : QuadraticForm k V) (Q : QuadraticForm k W)
    (e : q.IsometryEquiv Q),
    ∃ E : ∀ (S : TestAlgebra k), ScalarClifford q S ≃ₐ[S] ScalarClifford Q S,
      (∀ (S : TestAlgebra k) x, E S (vectors q S x) = vectors Q S (LinearEquiv.baseChange k S V W e.toLinearEquiv x)) ∧
      (∀ (S : TestAlgebra k) x, E S (reversion q S x) = reversion Q S (E S x)) ∧
      (∀ (S : TestAlgebra k), (evenPart q S).map (E S).toLinearMap = evenPart Q S) ∧
      (∀ (S : TestAlgebra k) a, Units.map (E S).toMonoidHom a ∈ spinUnits Q S ↔ a ∈ spinUnits q S) ∧
      ∀ {S T : TestAlgebra k} (f : S ⟶ T) x,
        E T (coefficientMap q S f.hom x) = coefficientMap Q S f.hom (E S x)

/-- The group-scheme comparison is induced by the isometry on Clifford
generators and gives the same maps on every test algebra. -/
def SpinIsometryGroupComparison : Prop :=
  ∀ {k V W : Type u} [Field k] [AddCommGroup V] [AddCommGroup W]
    [Module k V] [Module k W] (q : QuadraticForm k V) (Q : QuadraticForm k W)
    (e : q.IsometryEquiv Q) (G H : AffineAlgebraicGroup k)
    (g : ∀ S : TestAlgebra k, SpinSpecification.SchemePoints G.val S →* (ScalarClifford q S)ˣ)
    (h : ∀ S : TestAlgebra k, SpinSpecification.SchemePoints H.val S →* (ScalarClifford Q S)ˣ),
    SpinSpecification.IsSpinPointRepresentation q G.val g →
    SpinSpecification.IsSpinPointRepresentation Q H.val h →
    ∃ j : G.val ≅ H.val, ∀ (S : TestAlgebra k) (x : SpinSpecification.SchemePoints G.val S),
      h S (x ≫ j.hom.hom.hom) = Units.map
        (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
          (equivOfIsometry e)).toMonoidHom (g S x)

end Clifford

section Isotropy

open DiagonalizableGroups (groupAlgebra IntegerCharacters)
open _root_.LinearAlgebraicGroups.RationalRepresentations (trivialLinearMap)

/-- The nontrivial orthogonal action of a split multiplicative group forces
rational isotropy. The hypothesis is the norm identity at the universal
Laurent point, so it also applies over finite fields. -/
def IsotropicOfOrthogonalCoaction : Prop :=
  ∀ {k V I : Type u} [Field k] [AddCommGroup V] [Module k V] [LinearOrder I]
    (q : QuadraticForm k V) (b : Module.Basis I k V),
    let A := groupAlgebra k IntegerCharacters
    ∀ ρ : RightComodule k A V,
      ρ.coaction ≠ trivialLinearMap A →
      (∀ x, coefficientForm A q b ((TensorProduct.comm k V A) (ρ.coaction x)) =
        coefficientForm A q b (1 ⊗ₜ[k] x)) →
      ∃ v : V, v ≠ 0 ∧ q v = 0

open CharacterDescent (Cocharacter)
open AdjointRepresentation (GroupPoints)
open LinearAlgebraicGroups.Albert.SpinSpecification (ScalarClifford IsSpinPointRepresentation)

/-- A noncentral split cocharacter of a represented regular Clifford spin
group produces a nonzero isotropic vector over the ground field. -/
def SpinCocharacterIsotropy : Prop :=
  ∀ {k V I : Type u} [Field k] [AddCommGroup V] [Module k V] [LinearOrder I] [Fintype I]
    (q : QuadraticForm k V) (_b : Module.Basis I k V) (G : AffineAlgebraicGroup k)
    (e : ∀ S : TestAlgebra k, GroupPoints G.val S →* (ScalarClifford q S)ˣ),
    IsRegular q → IsSpinPointRepresentation q G.val e →
    ∀ c : Cocharacter G.val,
      (∃ (X : SchemeOver k) (g : X ⟶ G.val.X), ¬ Centralizes c g) →
      ∃ v : V, v ≠ 0 ∧ q v = 0

end Isotropy

section InnerForms

open Opposite
open AutomorphismSequence (relativePoints groupSections automorphisms SplitSequence AdjointQuotient)
open RelativeFormComparison (fieldTest transportedAut)
open Pinning (PinnedGroup AttachedDatum)
open RootGroups (AdditiveLine)
open _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology

local notation "FieldPoints" => _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points

/-- For a based type-B split sequence, the displacement of every chosen
trivialization is in the actual adjoint image. -/
def TypeBInnerDisplacement : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S]
    {A : AdditiveLine k} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    (E : SplitSequence P D l Q)
    (n : ℕ) (b : Fin (n + 1) ≃ D.toBased.base.support),
    (∀ i j, D.toBased.datum.pairing (b i).val (b j).val = typeBCartan n i j) →
    SpansRationally (Set.range fun i => D.toBased.datum.coroot (b i).val) →
    ∀ (H : AffineAlgebraicGroup k)
      (i : relativePoints P.pair.G.val (fieldTest k S) ≅ relativePoints H.val (fieldTest k S))
      (σ : Gal(S/k)),
      transportedAut k S i σ ∈ (E.toExactSequence.inner.app (op (fieldTest k S))).hom.range

/-- The displacement of the prescribed trivialization lifts to an adjoint
cocycle on an actual finite Galois layer above any prescribed starting layer. -/
def FiniteInnerCocycle : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (G H Q : AffineAlgebraicGroup k) (inn : groupSections Q.val ⟶ automorphisms G.val)
    (i : relativePoints G.val (fieldTest k S) ≅ relativePoints H.val (fieldTest k S))
    (L₀ : FiniteGaloisIntermediateField k S),
    Function.Injective (inn.app (op (fieldTest k S))) →
    (∀ σ, transportedAut k S i σ ∈ (inn.app (op (fieldTest k S))).hom.range) →
    ∃ (L : FiniteGaloisIntermediateField k S)
      (d : Gal(L/k) → FieldPoints k L Q.val.X), L₀ ≤ L ∧
      (∀ σ τ, d (σ * τ) = d σ * pointAction k L Q.val.X σ (d τ)) ∧
      ∀ σ, inn.app (op (fieldTest k S))
          ⟨pointMap k L Q.val.X L.toIntermediateField.val (d (restriction L σ))⟩ =
        transportedAut k S i σ

open _root_.LinearAlgebraicGroups.Descent.Forms (raiseIso IsScalarExtensionComparison)
open RelativeFormComparison (IsInducedByHopf)

/-- Both the original trivialization and its adjoint displacement are defined
on one finite Galois layer, in coordinate Hopf algebras and adjoint points
respectively. -/
def FiniteInnerTrivialization : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (G H Q : AffineAlgebraicGroup k) (inn : groupSections Q.val ⟶ automorphisms G.val)
    (i : relativePoints G.val (fieldTest k S) ≅ relativePoints H.val (fieldTest k S))
    (P B : HopfAlgebraCategory k) (g : specGroup P ≅ G.val) (h : specGroup B ≅ H.val)
    (t : ∀ C : HopfAlgebraCategory k,
      specGroup (extendedHopf S C) ≅ (groupBaseChange k S).obj (specGroup C)),
    Algebra.FiniteType k P → Algebra.FiniteType k B → IsScalarExtensionComparison t →
    Function.Injective (inn.app (op (fieldTest k S))) →
    (∀ σ, transportedAut k S i σ ∈ (inn.app (op (fieldTest k S))).hom.range) →
    ∃ (L : FiniteGaloisIntermediateField k S) (j : extendedHopf L P ≅ extendedHopf L B)
      (d : Gal(L/k) → FieldPoints k L Q.val.X),
      IsInducedByHopf t g h (raiseIso j) i ∧
      (∀ σ τ, d (σ * τ) = d σ * pointAction k L Q.val.X σ (d τ)) ∧
      ∀ σ, inn.app (op (fieldTest k S))
          ⟨pointMap k L Q.val.X L.toIntermediateField.val (d (restriction L σ))⟩ =
        transportedAut k S i σ

/-- A finite-level adjoint cocycle acting isometrically on the split module
descends its quadratic form using the cocycle times the standard action. -/
def AdjointQuadraticDescent : Prop :=
  ∀ {k K V I : Type u} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] [AddCommGroup V] [Module k V]
    [Module.Finite k V] [LinearOrder I]
    (q₀ : QuadraticForm k V) (b₀ : Module.Basis I k V) (J : AffineAlgebraicGroup k),
    let Q := coefficientForm K q₀ b₀
    let a₀ := SemilinearAction.scalarExtension (k := k) (K := K) V
    ∀ (ρ : FieldPoints k K J.val.X →* ((K ⊗[k] V) ≃ₗ[K] (K ⊗[k] V))),
      (∀ g x, Q (ρ g x) = Q x) →
      (∀ σ g x, a₀.act σ (ρ g x) = ρ (pointAction k K J.val.X σ g) (a₀.act σ x)) →
      ∀ d : Gal(K/k) → FieldPoints k K J.val.X,
        (∀ σ τ, d (σ * τ) = d σ * pointAction k K J.val.X σ (d τ)) →
        ∃ a : SemilinearAction k K (K ⊗[k] V),
          (∀ σ x, a.act σ x = ρ (d σ) (a₀.act σ x)) ∧
          ∃ q : QuadraticForm k a.fixed,
            (∀ x, algebraMap k K (q x) = Q x.val) ∧
            (∀ {L : Type u} [LinearOrder L] (b : Module.Basis L k a.fixed),
              ∃ e : (K ⊗[k] a.fixed) ≃ₗ[K] (K ⊗[k] V),
                e.toLinearMap = a.descentMap ∧
                ∀ x, Q (e x) = coefficientForm K q b x) ∧
            Module.finrank k a.fixed = Module.finrank k V ∧
            (IsRegular Q → IsRegular q)

open LinearAlgebraicGroups.Albert.SpinSpecification
  (ScalarClifford SchemePoints IsSpinPointRepresentation)

open AutomorphismSequence (restrictIso)
open RelativeFormComparison (fieldMap)

/-- A comparison which intertwines the Galois data descends to an actual
group-scheme isomorphism, identifying the intrinsic spin points on the original
group on every algebra. -/
def DescendCompatibleSpinComparison : Prop :=
  ∀ {k K W : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    [AddCommGroup W] [Module k W] (q : QuadraticForm k W)
    (H G : AffineAlgebraicGroup k)
    (h : ∀ R : TestAlgebra k, SchemePoints H.val R →* (ScalarClifford q R)ˣ),
    IsSpinPointRepresentation q H.val h →
    ∀ i : relativePoints H.val (fieldTest k K) ≅ relativePoints G.val (fieldTest k K),
      (∀ σ, restrictIso (fieldMap k K σ) i = i) →
      ∃ (j : H.val ≅ G.val)
        (g : ∀ R : TestAlgebra k, SchemePoints G.val R →* (ScalarClifford q R)ˣ),
        IsSpinPointRepresentation q G.val g ∧
        ∀ (R : TestAlgebra k) (x : SchemePoints H.val R), g R (x ≫ j.hom.hom.hom) = h R x

open AutomorphismSequence (ExactSequence)
open LinearAlgebraicGroups.Albert.SpinSpecification (vectors)

/-- The given action of the actual adjoint group on the split quadratic space.
The induced action on Clifford generators agrees with the inner action on the
specified split spin model over every test algebra. -/
structure SpinAdjointAction {k V I : Type u} [Field k] [AddCommGroup V] [Module k V]
    [LinearOrder I] (q : QuadraticForm k V) (b : Module.Basis I k V)
    (G J : AffineAlgebraicGroup k) (inn : groupSections J.val ⟶ automorphisms G.val)
    (g : ∀ R : TestAlgebra k, SchemePoints G.val R →* (ScalarClifford q R)ˣ) where
  linear : ∀ R : TestAlgebra k, SchemePoints J.val R →*
    ((R ⊗[k] V) ≃ₗ[R] (R ⊗[k] V))
  preserves : ∀ (R : TestAlgebra k) (p : SchemePoints J.val R) x,
    coefficientForm R q b (linear R p x) = coefficientForm R q b x
  natural : ∀ {R T : TestAlgebra k} (f : R ⟶ T) (p : SchemePoints J.val R) x,
    let fV := TensorProduct.map f.hom.toLinearMap (LinearMap.id : V →ₗ[k] V)
    fV (linear R p x) = linear T (mapPoints f p) (fV x)
  clifford : ∀ (R : TestAlgebra k), SchemePoints J.val R →
    ScalarClifford q R ≃ₐ[R] ScalarClifford q R
  generators : ∀ (R : TestAlgebra k) (p : SchemePoints J.val R) x,
    clifford R p (vectors q R x) = vectors q R (linear R p x)
  innerAction : ∀ {R T : TestAlgebra k} (f : R ⟶ T) (p : SchemePoints J.val R)
    (x : SchemePoints G.val T),
    let U := Over.mk ((testSpec k).map f.op)
    let a := inn.app (op ((testSpec k).obj (op R))) ⟨p⟩
    g T ((a.asIso.hom.app (op U)).hom x) =
      Units.map (clifford T (mapPoints f p)).toMonoidHom (g T x)

/-- Descent of the prescribed split intrinsic spin model along an inner
trivialization. The representation produced is on the original affine group
and is defined on every commutative test algebra. -/
def EffectiveOddSpinDescent : Prop :=
  ∀ {k S V I : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    [AddCommGroup V] [Module k V] [Module.Finite k V] [LinearOrder I]
    (q₀ : QuadraticForm k V) (b₀ : Module.Basis I k V)
    (G₀ G : AffineAlgebraicGroup k) (J : AdjointQuotient G₀)
    {O : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u + 1}} (E : ExactSequence G₀ J O)
    (g₀ : ∀ R : TestAlgebra k, SchemePoints G₀.val R →* (ScalarClifford q₀ R)ˣ)
    (A : SpinAdjointAction q₀ b₀ G₀ J.quotient E.inner g₀)
    (i : relativePoints G₀.val (fieldTest k S) ≅ relativePoints G.val (fieldTest k S)),
    IsRegular q₀ → Odd (Module.finrank k V) → IsSpinPointRepresentation q₀ G₀.val g₀ →
    (∀ σ, transportedAut k S i σ ∈ (E.inner.app (op (fieldTest k S))).hom.range) →
    ∃ (K : FiniteGaloisIntermediateField k S) (d : Gal(K/k) → FieldPoints k K J.quotient.val.X)
      (a : SemilinearAction k K (K ⊗[k] V)) (q : QuadraticForm k a.fixed)
      (g : ∀ R : TestAlgebra k, SchemePoints G.val R →* (ScalarClifford q R)ˣ),
      (∃ (P B : HopfAlgebraCategory k) (p : specGroup P ≅ G₀.val) (b : specGroup B ≅ G.val)
        (t : ∀ C : HopfAlgebraCategory k,
          specGroup (extendedHopf S C) ≅ (groupBaseChange k S).obj (specGroup C))
        (j : extendedHopf K P ≅ extendedHopf K B),
        Algebra.FiniteType k P ∧ Algebra.FiniteType k B ∧
          IsScalarExtensionComparison t ∧ IsInducedByHopf t p b (raiseIso j) i) ∧
      (∀ σ τ, d (σ * τ) = d σ * pointAction k K J.quotient.val.X σ (d τ)) ∧
      (∀ σ, E.inner.app (op (fieldTest k S))
        ⟨pointMap k K J.quotient.val.X K.toIntermediateField.val (d (restriction K σ))⟩ =
          transportedAut k S i σ) ∧
      (∀ σ x, a.act σ x = A.linear (CommAlgCat.of k K) (d σ)
        ((SemilinearAction.scalarExtension (k := k) (K := K) V).act σ x)) ∧
      (∀ x, algebraMap k K (q x) = coefficientForm K q₀ b₀ x.val) ∧
      (∀ {L : Type u} [LinearOrder L] (b : Module.Basis L k a.fixed),
        ∃ e : (K ⊗[k] a.fixed) ≃ₗ[K] (K ⊗[k] V), e.toLinearMap = a.descentMap ∧
          ∀ x, coefficientForm K q₀ b₀ (e x) = coefficientForm K q b x) ∧
      IsRegular q ∧ FiniteDimensional k a.fixed ∧ Module.finrank k a.fixed = Module.finrank k V ∧
      IsSpinPointRepresentation q G.val g ∧
      ∃ (H : AffineAlgebraicGroup k)
        (h : ∀ R : TestAlgebra k, SchemePoints H.val R →* (ScalarClifford q R)ˣ)
        (l : H.val ≅ G.val), IsSpinPointRepresentation q H.val h ∧
        ∀ (R : TestAlgebra k) (x : SchemePoints H.val R), g R (x ≫ l.hom.hom.hom) = h R x

end InnerForms

end

end LinearAlgebraicGroups.Specs.Arithmetic.OddSpinInnerDescent
