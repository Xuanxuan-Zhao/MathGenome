import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralRootRelations
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricRadicals
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.FinitePresentation

open scoped TensorProduct
open Algebra.TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.IntegralCentralQuotient

noncomputable section

variable {R A M : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A] [CommGroup M]

/-- Right translation by the diagonalizable group with coordinate restriction `π`. -/
def rightCoaction (π : A →ₐc[R] MonoidAlgebra R M) : A →ₐ[R] A ⊗[R] MonoidAlgebra R M :=
  (Algebra.TensorProduct.map (AlgHom.id R A) π.toAlgHom).comp (Bialgebra.comulAlgHom R A)

/-- The functions in degree `m` for right translation. -/
def HasDegree (π : A →ₐc[R] MonoidAlgebra R M) (m : M) (a : A) : Prop :=
  rightCoaction π a = a ⊗ₜ[R] MonoidAlgebra.of R M m

/-- The subgroup is central when left and right translation agree.
Both maps here are pullbacks on the full product with the subgroup scheme. -/
def IsCentral (π : A →ₐc[R] MonoidAlgebra R M) : Prop :=
  rightCoaction π =
    (Algebra.TensorProduct.comm R (MonoidAlgebra R M) A).toAlgHom.comp
      ((Algebra.TensorProduct.map π.toAlgHom (AlgHom.id R A)).comp (Bialgebra.comulAlgHom R A))

/-- The degree-zero coordinate ring, using multiplicative notation for the grading group. -/
def invariants (π : A →ₐc[R] MonoidAlgebra R M) : Subalgebra R A where
  carrier := {a | HasDegree π 1 a}
  mul_mem' := by
    intro a b ha hb
    change rightCoaction π a = _ at ha
    change rightCoaction π b = _ at hb
    change rightCoaction π (a * b) = _
    rw [map_mul, ha, hb, tmul_mul_tmul, ← map_mul, mul_one]
  add_mem' := by
    intro a b ha hb
    change rightCoaction π a = _ at ha
    change rightCoaction π b = _ at hb
    change rightCoaction π (a + b) = _
    rw [map_add, ha, hb, TensorProduct.add_tmul]
  algebraMap_mem' r := by
    change rightCoaction π (algebraMap R A r) =
      algebraMap R A r ⊗ₜ[R] MonoidAlgebra.of R M 1
    rw [AlgHom.commutes, map_one]
    rfl

/-- Pullback on functions along `(g,z) ↦ (g,gz)`. -/
def orbitMap (π : A →ₐc[R] MonoidAlgebra R M) : A ⊗[R] A →ₐ[R] A ⊗[R] MonoidAlgebra R M :=
  lift includeLeft (rightCoaction π) fun _ _ => Commute.all _ _

/-- Having a finite sum of products equal to one in every pair of opposite degrees
is the strong-grading criterion. -/
def StrongGrading (π : A →ₐc[R] MonoidAlgebra R M) : Prop :=
  ∀ m : M, ∃ (n : ℕ) (a b : Fin n → A),
    (∀ i, HasDegree π m⁻¹ (a i)) ∧ (∀ i, HasDegree π m (b i)) ∧
    ∑ i, a i * b i = 1

/-- The coordinate part of the finite diagonalizable torsor construction. -/
def CoordinateQuotient : Prop :=
  ∀ {R A M : Type u} [CommRing R] [IsNoetherianRing R] [CommRing A]
    [HopfAlgebra R A] [CommGroup M] [Finite M] [Algebra.FinitePresentation R A]
    [Module.Flat R A] (π : A →ₐc[R] MonoidAlgebra R M), Function.Surjective π →
      Function.Surjective (orbitMap π) ∧ StrongGrading π ∧
      Module.Finite (invariants π) A ∧ Module.FaithfullyFlat (invariants π) A ∧
      Module.Flat R (invariants π) ∧ Algebra.FinitePresentation R (invariants π) ∧
      ∃ e : A ⊗[invariants π] A ≃ₐ[invariants π] A ⊗[R] MonoidAlgebra R M,
        ∀ a b : A, e (a ⊗ₜ[invariants π] b) = (includeLeft : A →ₐ[R] A ⊗[R] MonoidAlgebra R M) a * rightCoaction π b

/-- Centrality allows the invariant ring to inherit the Hopf structure from the source. -/
def HopfQuotient : Prop :=
  ∀ {R A M : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A] [CommGroup M]
    [Finite M] (π : A →ₐc[R] MonoidAlgebra R M), IsCentral π →
      ∃ (hopf : HopfAlgebra R ↥(invariants π)),
        letI : Algebra R ↥(invariants π) := hopf.toHopfAlgebraStruct.toBialgebra.toAlgebra
        letI : HopfAlgebra R ↥(invariants π) := hopf
        ∃ j : ↥(invariants π) →ₐc[R] A, ∀ b : invariants π, j b = (b : A)

section Geometry

open AlgebraicGeometry CategoryTheory Opposite WithConv
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

abbrev IntegralRing := ULift.{u} ℤ

/-- Schemes over the specified base ring, including the integral base. -/
abbrev OverBase (R : Type u) [CommRing R] := Over (Spec (CommRingCat.of R))

abbrev HopfSpectrum (R C : Type u) [CommRing R] [CommRing C] [HopfAlgebra R C] :
    Grp (OverBase R) :=
  (hopfSpec (CommRingCat.of R)).obj (op (CommHopfAlgCat.of R C))

abbrev spectrumOfAlgHom {C D : Type u} [CommRing C] [CommRing D] [Algebra R C]
    [Algebra R D] (f : C →ₐ[R] D) :
    (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R D)) ⟶
      (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R C)) :=
  (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom f).op

abbrev spectrumOfHopfHom {C D : Type u} [CommRing C] [CommRing D] [HopfAlgebra R C]
    [HopfAlgebra R D] (f : C →ₐc[R] D) : HopfSpectrum R D ⟶ HopfSpectrum R C :=
  (hopfSpec (CommRingCat.of R)).map (CommHopfAlgCat.ofHom f).op

abbrev fibreGroup (K : Type u) [Field K] [Algebra R K] :
    Grp (OverBase R) ⥤ GroupScheme K :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).mapGrp

/-- Connected reductivity and maximality of the indicated torus in every geometric fibre. -/
def ReductiveFibres {T G : Grp (OverBase R)} (j : T ⟶ G) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K],
    ∃ (H : AffineAlgebraicGroup K) (e : (fibreGroup K).obj G ≅ H.val),
      let incl := (fibreGroup K).map j ≫ e.hom
      ∃ hc : IsClosedImmersion incl.hom.hom.left,
        GeometricRadicals.IsReductive H ∧
          GeometricRadicals.IsMaximalTorus ⟨_, incl, hc⟩

/-- The product of the given root line factors in list order. -/
def lineProduct (R : Type u) [CommRing R] {I : Type u} : List I → OverBase R
  | [] => 𝟙_ (OverBase R)
  | _ :: l => (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R (Polynomial R))) ⊗
      lineProduct R l

/-- Evaluation of the ordered root coordinates by multiplication in the ambient group. -/
def rootProduct {I : Type u} (x : I → A →ₐ[R] Polynomial R) :
    (l : List I) → lineProduct R l ⟶ (HopfSpectrum R A).X
  | [] => 1
  | i :: l =>
    let L := (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R (Polynomial R)))
    let xi : L ⟶ (HopfSpectrum R A).X := spectrumOfAlgHom (x i)
    (fst L (lineProduct R l) ≫ xi) *
      (snd L (lineProduct R l) ≫ rootProduct x l)

/-- The marked ordered cell with the torus between the two lists of root groups. -/
def cellMap {X I : Type u} [CommGroup X] (t : A →ₐc[R] MonoidAlgebra R X)
    (x : I → A →ₐ[R] Polynomial R) (negative positive : List I) :
    lineProduct R negative ⊗ ((HopfSpectrum R (MonoidAlgebra R X)).X ⊗
      lineProduct R positive) ⟶ (HopfSpectrum R A).X :=
  let N := lineProduct R negative
  let P := lineProduct R positive
  let T := (HopfSpectrum R (MonoidAlgebra R X)).X
  (fst N (T ⊗ P) ≫ rootProduct x negative) *
    (snd N (T ⊗ P) ≫ ((fst T P ≫ (spectrumOfHopfHom t).hom.hom) *
      (snd T P ≫ rootProduct x positive)))

/-- Changing only the torus in an ordered cell by restricting its characters to a sublattice. -/
def cellTorusQuotient {X I : Type u} [CommGroup X] (z : X →* M)
    (negative positive : List I) :
    lineProduct R negative ⊗ ((HopfSpectrum R (MonoidAlgebra R X)).X ⊗
      lineProduct R positive) ⟶
    lineProduct R negative ⊗ ((HopfSpectrum R (MonoidAlgebra R ↥z.ker)).X ⊗
      lineProduct R positive) :=
  (𝟙 _) ⊗ₘ (spectrumOfAlgHom (MonoidAlgebra.mapDomainBialgHom R z.ker.subtype).toAlgHom ⊗ₘ
    (𝟙 _))

/-- A rank-one map is an SL₂ homomorphism on all test algebras, naturally in the test algebra. -/
structure RankOneMap (R A : Type u) [CommRing R] [CommRing A] [HopfAlgebra R A] where
  hom : ∀ S : CommAlgCat.{u} R, Matrix.SpecialLinearGroup (Fin 2) S →*
    WithConv (A →ₐ[R] S)
  naturality : ∀ {S T : CommAlgCat.{u} R} (f : S ⟶ T) (s : Matrix.SpecialLinearGroup (Fin 2) S),
    (hom T (Matrix.SpecialLinearGroup.map f.hom.toRingHom s)).ofConv =
      f.hom.comp (hom S s).ofConv

/-- Evaluate a torus cocharacter at a test-algebra unit. -/
def cocharacterEval {X : Type u} [CommGroup X] (cochar : X →* Multiplicative ℤ)
    (S : CommAlgCat.{u} R) (s : Sˣ) : MonoidAlgebra R X →ₐ[R] S :=
  MonoidAlgebra.lift R S X ((Units.coeHom S).comp
    ((show Multiplicative ℤ →* Sˣ from
      { toFun := fun n => s ^ Multiplicative.toAdd n
        map_one' := zpow_zero s
        map_mul' := fun m n => zpow_add s m.toAdd n.toAdd }).comp cochar))

/-- The marked rank-one map has the given upper and lower root coordinates and coroot. -/
def RankOneCompatibility {X : Type u} [CommGroup X]
    (t : A →ₐc[R] MonoidAlgebra R X) (x y : A →ₐ[R] Polynomial R)
    (cochar : X →* Multiplicative ℤ) (r : RankOneMap R A) : Prop :=
  (∀ (S : CommAlgCat.{u} R) (a : S),
    (r.hom S (IntegralRootRelations.upper a)).ofConv = (Polynomial.aeval a).comp x ∧
    (r.hom S (IntegralRootRelations.lower a)).ofConv = (Polynomial.aeval a).comp y) ∧
  ∀ (S : CommAlgCat.{u} R) (s : Sˣ),
    (r.hom S (IntegralRootRelations.diagonal s)).ofConv =
      (cocharacterEval cochar S s).comp t.toAlgHom

/-- Scalar conjugation in the parameter of the marked root subgroup. -/
def RootScalarAction {X : Type u} [CommGroup X]
    (t : A →ₐc[R] MonoidAlgebra R X) (x : A →ₐ[R] Polynomial R) (α : X) : Prop :=
  ∀ (S : CommAlgCat.{u} R) (a : S) (s : MonoidAlgebra R X →ₐ[R] S),
    let st := toConv (s.comp t.toAlgHom)
    st * toConv ((Polynomial.aeval a).comp x) *
      toConv (st.ofConv.comp (HopfAlgebra.antipodeAlgHom R A)) =
      toConv ((Polynomial.aeval (s (MonoidAlgebra.of R X α) * a)).comp x)

/-- The finite fppf projection with its right-translation torsor square, expressed
on the spectra of the product and the two coordinate morphisms. -/
def IsRightTorsor {B : Type u} [CommRing B] [HopfAlgebra R B]
    (j : B →ₐc[R] A) (π : A →ₐc[R] MonoidAlgebra R M) : Prop :=
  let q := (spectrumOfHopfHom j).hom.hom.left
  IsFinite q ∧ Flat q ∧ Surjective q ∧ LocallyOfFinitePresentation q ∧
    IsPullback
      (spectrumOfAlgHom (R := R) (includeLeft : A →ₐ[R] A ⊗[R] MonoidAlgebra R M)).left
      (spectrumOfAlgHom (rightCoaction π)).left q q

/-- The integral quotient of an existing split model with marked ordered root cell.
The central subgroup is specified by restriction of characters of the source torus. -/
def GeometricQuotient : Prop :=
  let R := IntegralRing.{u}
  ∀ {A X M I : Type u} [CommRing A] [HopfAlgebra R A] [CommGroup X] [CommGroup M]
    [Finite M] [Module.Free ℤ (Additive X)] [Module.Finite ℤ (Additive X)]
    (z : X →* M) (t : A →ₐc[R] MonoidAlgebra R X),
    let π := (MonoidAlgebra.mapDomainBialgHom R z).comp t
    ∀ (x : I → A →ₐ[R] Polynomial R) (negative positive : List I) (opposite : I → I)
      (α : I → X) (coroot : I → X →* Multiplicative ℤ) (rankOne : I → RankOneMap R A),
      Function.Surjective z → Function.Surjective t → IsCentral π →
      Smooth (HopfSpectrum R A).X.hom → ReductiveFibres (spectrumOfHopfHom t) →
      (negative ++ positive).Nodup → (∀ i, i ∈ negative ++ positive) →
      IsOpenImmersion (cellMap t x negative positive).left →
      (∀ i, Function.Surjective (x i) ∧ RootScalarAction t (x i) (α i) ∧
        RankOneCompatibility t (x i) (x (opposite i)) (coroot i) (rankOne i)) →
      let B := ↥(invariants π)
      ∃ hB : HopfAlgebra R B,
        letI : Algebra R B := hB.toHopfAlgebraStruct.toBialgebra.toAlgebra
        letI : HopfAlgebra R B := hB
        ∃ (j : B →ₐc[R] A) (t₀ : B →ₐc[R] MonoidAlgebra R ↥z.ker),
          (∀ b, j b = (b : A)) ∧
          IsRightTorsor j π ∧
          Flat (HopfSpectrum R B).X.hom ∧ LocallyOfFinitePresentation (HopfSpectrum R B).X.hom ∧
          ReductiveFibres (spectrumOfHopfHom t₀) ∧
          Module.Free ℤ (Additive ↥z.ker) ∧ Module.Finite ℤ (Additive ↥z.ker) ∧
          (MonoidAlgebra.mapDomainBialgHom R z.ker.subtype).comp t₀ = t.comp j ∧
          let x₀ := fun i => (x i).comp j.toAlgHom
          IsOpenImmersion (cellMap t₀ x₀ negative positive).left ∧
          IsPullback (cellTorusQuotient z negative positive) (cellMap t x negative positive)
            (cellMap t₀ x₀ negative positive) (spectrumOfHopfHom j).hom.hom ∧
          ∀ i, Function.Surjective (x₀ i) ∧
            ∃ hα : z (α i) = 1,
              RootScalarAction t₀ (x₀ i) (⟨α i, hα⟩ : z.ker) ∧
              ∃ r₀ : RankOneMap R B,
                (∀ S s, (r₀.hom S s).ofConv = ((rankOne i).hom S s).ofConv.comp j.toAlgHom) ∧
                RankOneCompatibility t₀ (x₀ i) (x₀ (opposite i))
                  ((coroot i).comp z.ker.subtype) r₀

/-- The coordinate construction and its geometric applications to the marked integral model. -/
def Statement : Prop := CoordinateQuotient.{u} ∧ HopfQuotient.{u} ∧ GeometricQuotient.{u}

end Geometry

end

end LinearAlgebraicGroups.Specs.IntegralCentralQuotient
