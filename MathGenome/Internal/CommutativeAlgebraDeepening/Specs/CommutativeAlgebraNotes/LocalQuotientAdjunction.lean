import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.MatlisDualFunctor
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CechGeneratorIndependence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.CategoryTheory.Adjunction.Additive

noncomputable section

open CategoryTheory
open ModuleCat (restrictScalars coextendScalars)
open IsLocalRing (ResidueField maximalIdeal)

namespace Specs.CommutativeAlgebraNotes.LocalQuotientAdjunction

universe u

variable {S R : Type u} [CommRing S] [CommRing R]

/-- The action on `Hom_S(X,J)` comes from scalar multiplication on the source. -/
@[instance_reducible]
def precompositionModule (f : S →+* R) (X : ModuleCat.{u} R) (J : ModuleCat.{u} S) :
    Module R ((restrictScalars f).obj X ⟶ J) where
  smul r h := (restrictScalars f).map (r • 𝟙 X) ≫ h
  one_smul h := by
    apply ModuleCat.hom_ext
    ext x
    change h ((1 : R) • (x : X)) = h x
    rw [one_smul]
  mul_smul r t h := by
    apply ModuleCat.hom_ext
    ext x
    change h ((r * t) • (x : X)) = h (t • (r • (x : X)))
    rw [mul_comm, mul_smul]
  smul_zero r := by
    apply ModuleCat.hom_ext
    ext x
    change (0 : (restrictScalars f).obj X ⟶ J) (r • (x : X)) = 0
    rfl
  smul_add r h g := by apply ModuleCat.hom_ext; ext x; rfl
  add_smul r t h := by
    apply ModuleCat.hom_ext
    ext x
    change h ((r + t) • (x : X)) = h (r • (x : X)) + h (t • (x : X))
    rw [add_smul]
    exact h.hom.map_add _ _
  zero_smul h := by
    apply ModuleCat.hom_ext
    ext x
    change h ((0 : R) • (x : X)) = 0
    rw [zero_smul]
    exact h.hom.map_zero

/-- The coinduction adjunction, linear for the source action. -/
def adjunction (f : S →+* R) (X : ModuleCat.{u} R) (J : ModuleCat.{u} S) :
    letI := precompositionModule f X J
    (X ⟶ (coextendScalars f).obj J) ≃ₗ[R] ((restrictScalars f).obj X ⟶ J) := by
  letI := precompositionModule f X J
  refine { toAddEquiv := ((ModuleCat.restrictCoextendScalarsAdj f).homAddEquiv X J).symm
           map_smul' := ?_ }
  intro r g
  apply ModuleCat.hom_ext
  ext x
  change (r • g (x : X)) (1 : R) = g (r • (x : X)) (1 : R)
  exact congrArg (fun t : (coextendScalars f).obj J => t (1 : R))
    (g.hom.map_smul r (x : X)).symm

def AdjunctionType :=
  ∀ {S R : Type u} [CommRing S] [CommRing R]
    (f : S →+* R) (X : ModuleCat.{u} R) (J : ModuleCat.{u} S),
    letI := precompositionModule f X J
    (X ⟶ (coextendScalars f).obj J) ≃ₗ[R] ((restrictScalars f).obj X ⟶ J)

def AdjunctionFormulas : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R]
    (f : S →+* R) (X : ModuleCat.{u} R) (J : ModuleCat.{u} S),
    (∀ (g : X ⟶ (coextendScalars f).obj J) (x : X),
      adjunction f X J g x = g x (1 : R)) ∧
    (∀ (h : (restrictScalars f).obj X ⟶ J) (x : X) (r : R),
      (adjunction f X J).symm h x r = h (r • x))

def AdjunctionNaturality : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R]
    (f : S →+* R) {X Y : ModuleCat.{u} R} {J K : ModuleCat.{u} S}
    (a : X ⟶ Y) (b : J ⟶ K) (g : Y ⟶ (coextendScalars f).obj J),
    adjunction f X K (a ≫ g ≫ (coextendScalars f).map b) =
      (restrictScalars f).map a ≫ adjunction f Y J g ≫ b

def CoinductionInjective : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] (f : S →+* R)
    (J : ModuleCat.{u} S), Injective J → Injective ((coextendScalars f).obj J)

abbrev kernelAnnihilator (f : S →+* R) (J : ModuleCat.{u} S) : Submodule S J :=
  Submodule.torsionBySet S J (RingHom.ker f : Set S)

abbrev evaluateOne (f : S →+* R) (J : ModuleCat.{u} S) :
    (restrictScalars f).obj ((coextendScalars f).obj J) ⟶ J :=
  (ModuleCat.restrictCoextendScalarsAdj f).counit.app J

/-- Evaluation at one identifies coinduction with the kernel annihilator. -/
def EvaluationAnnihilator : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] (f : S →+* R),
    Function.Surjective f → ∀ (J : ModuleCat.{u} S),
    ∃ e : (restrictScalars f).obj ((coextendScalars f).obj J) ≃ₗ[S] kernelAnnihilator f J,
      (∀ g, (e g : J) = (show (coextendScalars f).obj J from g) (1 : R)) ∧
      (∀ (s : S) (g : (coextendScalars f).obj J), e (f s • g) = s • e g)


section Complexes

open CochainComplex HomComplex

abbrev RestrictedComplex (f : S →+* R) (U : CochainComplex (ModuleCat.{u} R) ℤ) :=
  ((restrictScalars f).mapHomologicalComplex (.up ℤ)).obj U

/-- Apply coinduction in every degree, with postcomposition on the differentials. -/
abbrev CoinducedComplex (f : S →+* R) (V : CochainComplex (ModuleCat.{u} S) ℤ) :=
  letI := (ModuleCat.restrictCoextendScalarsAdj.{u, u, u} f).right_adjoint_additive
  ((coextendScalars f).mapHomologicalComplex (.up ℤ)).obj V

@[instance_reducible]
def precompositionCochainModule (f : S →+* R)
    (U : CochainComplex (ModuleCat.{u} R) ℤ) (V : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℤ) :
    Module R (Cochain (RestrictedComplex f U) V n) :=
  @Pi.module (Triplet n) (fun T => (RestrictedComplex f U).X T.p ⟶ V.X T.q) R
    _ (fun _ => inferInstance) (fun T => precompositionModule f (U.X T.p) (V.X T.q))

private theorem precomposition_smul_v (f : S →+* R)
    (U : CochainComplex (ModuleCat.{u} R) ℤ) (V : CochainComplex (ModuleCat.{u} S) ℤ)
    (n : ℤ) (r : R) (z : Cochain (RestrictedComplex f U) V n) (p q : ℤ)
    (hpq : p + n = q) :
    (@SMul.smul R _ (precompositionCochainModule f U V n).toSMul r z).v p q hpq =
      (restrictScalars f).map (r • 𝟙 (U.X p)) ≫ z.v p q hpq := rfl

private theorem restrictedDifferential_smul (f : S →+* R)
    (U : CochainComplex (ModuleCat.{u} R) ℤ) (V : CochainComplex (ModuleCat.{u} S) ℤ)
    (n m : ℤ) (r : R) (z : Cochain (RestrictedComplex f U) V n) :
    @δ _ _ _ _ _ n m (@SMul.smul R _ (precompositionCochainModule f U V n).toSMul r z) =
      @SMul.smul R _ (precompositionCochainModule f U V m).toSMul r (δ n m z) := by
  have comm (p q : ℤ) :
      (restrictScalars f).map (U.d p q) ≫ (restrictScalars f).map (r • 𝟙 (U.X q)) =
        (restrictScalars f).map (r • 𝟙 (U.X p)) ≫ (restrictScalars f).map (U.d p q) := by
    rw [← Functor.map_comp, ← Functor.map_comp, Linear.comp_smul, Linear.smul_comp,
      Category.comp_id, Category.id_comp]
  apply Cochain.ext
  intro p q hpq
  rw [precomposition_smul_v]
  simp only [δ, Cochain.mk_v, precomposition_smul_v,
    Functor.mapHomologicalComplex_obj_d, Category.assoc, Preadditive.comp_add,
    Linear.comp_units_smul]
  rw [← Category.assoc ((restrictScalars f).map (U.d p _)), comm, Category.assoc]

private def restrictedHomTerm (f : S →+* R)
    (U : CochainComplex (ModuleCat.{u} R) ℤ) (V : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℤ) :
    ModuleCat.{u} R := by
  letI : Module R (Cochain (RestrictedComplex f U) V n) := precompositionCochainModule f U V n
  exact ModuleCat.of R (Cochain (RestrictedComplex f U) V n)

/-- The signed Hom complex over S, with R acting by multiplication on the source. -/
def restrictedHomComplex (f : S →+* R)
    (U : CochainComplex (ModuleCat.{u} R) ℤ) (V : CochainComplex (ModuleCat.{u} S) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ where
  X := restrictedHomTerm f U V
  d n m := ConcreteCategory.ofHom (C := ModuleCat R)
    (X := restrictedHomTerm f U V n) (Y := restrictedHomTerm f U V m)
    { toFun := δ n m
      map_add' := δ_add n m
      map_smul' := restrictedDifferential_smul f U V n m }
  shape n m h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact δ_shape n m h z
  d_comp_d' n m l _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact δ_δ n m l z

def RestrictedHomComplexType :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] (_f : S →+* R)
    (_U : CochainComplex (ModuleCat.{u} R) ℤ) (_V : CochainComplex (ModuleCat.{u} S) ℤ),
    CochainComplex (ModuleCat.{u} R) ℤ

/-- The comparison of signed Hom complexes uses the adjunction on each component. -/
def CochainAdjunction : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] (f : S →+* R)
    (U : CochainComplex (ModuleCat.{u} R) ℤ) (V : CochainComplex (ModuleCat.{u} S) ℤ),
    ∃ e : linearHomComplex R U (CoinducedComplex f V) ≅ restrictedHomComplex f U V,
      ∀ (n : ℤ) (z : Cochain U (CoinducedComplex f V) n) (p q : ℤ) (hpq : p + n = q),
        (show Cochain (RestrictedComplex f U) V n from e.hom.f n z).v p q hpq =
          adjunction f (U.X p) (V.X q) (z.v p q hpq)

end Complexes

section Cech

open HomologicalComplex

/-- The augmented Čech complex with coefficients in a module in degree zero. -/
noncomputable abbrev cechWithCoefficients (rs : List S) :=
  single (ModuleCat.{u} S) (.up ℤ) 0 ⋙ AugmentedCechComplex.tensorFunctor S rs

/-- A fixed list gives the same coefficient complex after restricting from the image list. -/
def CechRestriction : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] (f : S →+* R) (rs : List S),
    Nonempty (restrictScalars f ⋙ cechWithCoefficients rs ≅
      cechWithCoefficients (rs.map f) ⋙ (restrictScalars f).mapHomologicalComplex (.up ℤ))

/-- The local cohomology over the target is computed by the source Čech model.
The isomorphism is natural in target modules, so in particular commutes with
the action of their target scalar endomorphisms. -/
def LocalQuotientCech : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] [IsLocalRing S] [IsLocalRing R]
    [IsNoetherianRing S] [IsNoetherianRing R] (f : S →+* R) [IsLocalHom f],
    Function.Surjective f → ∀ (rs : List S), Ideal.span {s | s ∈ rs} = maximalIdeal S →
    Ideal.span {r | r ∈ rs.map f} = maximalIdeal R ∧
      ∀ q : ℤ,
        ∃ e : IdealTorsion.localCohomology.{u} (maximalIdeal R) q ⋙ restrictScalars f ≅
            restrictScalars f ⋙ CechGeneratorIndependence.cechCohomology rs q,
          ∀ (X : ModuleCat.{u} R) (r : R),
            (restrictScalars f).map
                (r • 𝟙 ((IdealTorsion.localCohomology.{u} (maximalIdeal R) q).obj X)) ≫
              e.hom.app X =
              e.hom.app X ≫ (restrictScalars f ⋙ CechGeneratorIndependence.cechCohomology rs q).map
                (r • 𝟙 X)

end Cech

variable [IsLocalRing S] [IsLocalRing R]

/-- The residue map induced by the local surjection is the identification of the two fields. -/
def ResidueIdentification : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] [IsLocalRing S] [IsLocalRing R]
    (f : S →+* R) [IsLocalHom f], Function.Surjective f →
      Function.Bijective (ResidueField.map f)

/-- The hull has the indicated coinduced carrier. Its inclusion extends the source
hull's inclusion along the canonical map of residue fields. -/
def CoinducedEnvelope : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] [IsLocalRing S] [IsLocalRing R]
    [IsNoetherianRing S] [IsNoetherianRing R] (f : S →+* R) [IsLocalHom f],
    Function.Surjective f →
    ∀ (E : _root_.CommutativeAlgebraNotes.MatlisDualFunctorSpecs.residueFieldEnvelopeValue S),
    ∃ i : ResidueField R →ₗ[R] (coextendScalars f).obj (ModuleCat.of S E.carrier),
      AdvCommAlg.Gorenstein.IsInjectiveEnvelope i ∧
        ∀ a : ResidueField S, i (ResidueField.map f a) (1 : R) = E.inclusion a

/-- Any chosen target hull identifies with the coinduced source hull through an
isomorphism that respects the identified copy of the residue field. -/
def EnvelopeComparison : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] [IsLocalRing S] [IsLocalRing R]
    [IsNoetherianRing S] [IsNoetherianRing R] (f : S →+* R) [IsLocalHom f],
    Function.Surjective f →
    ∀ (E : _root_.CommutativeAlgebraNotes.MatlisDualFunctorSpecs.residueFieldEnvelopeValue S)
      (F : _root_.CommutativeAlgebraNotes.MatlisDualFunctorSpecs.residueFieldEnvelopeValue R),
    ∃ e : F.carrier ≃ₗ[R] (coextendScalars f).obj (ModuleCat.of S E.carrier),
      ∀ a : ResidueField S, e (F.inclusion (ResidueField.map f a)) (1 : R) = E.inclusion a

end Specs.CommutativeAlgebraNotes.LocalQuotientAdjunction
