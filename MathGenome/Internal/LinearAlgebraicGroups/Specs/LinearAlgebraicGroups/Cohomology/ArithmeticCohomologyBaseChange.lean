import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Cohomology.ClosedImmersionCohomology
import Mathlib.Algebra.Field.ZMod
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.RingTheory.Localization.Away.Basic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite

universe u

namespace LinearAlgebraicGroups.Specs.ArithmeticCohomologyBaseChange

noncomputable section

open OrderedCechComparison

variable {A B : Type u} [CommRing A] [CommRing B]

abbrev changeBase (φ : A →+* B) : SchemeOverRing A ⥤ SchemeOverRing B :=
  Over.pullback (Spec.map (CommRingCat.ofHom φ))

abbrev fibreProjection (φ : A →+* B) (X : SchemeOverRing A) :
    ((changeBase φ).obj X).left ⟶ X.left :=
  pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ))

theorem fibreProjection_over (φ : A →+* B) (X : SchemeOverRing A) :
    fibreProjection φ X ≫ X.hom =
      ((changeBase φ).obj X).hom ≫ Spec.map (CommRingCat.ofHom φ) :=
  pullback.condition

abbrev fibreSheaf (φ : A →+* B) (X : SchemeOverRing A) (F : X.left.Modules) :=
  (Scheme.Modules.pullback (fibreProjection φ X)).obj F

abbrev fibreCoefficientMap (φ : A →+* B) (X : SchemeOverRing A) (F : X.left.Modules) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (fibreProjection φ X)).unit.app F

/-- Local freeness with arbitrary rank, which can vary between trivializing opens. -/
def IsLocallyFree {X : Scheme.{u}} (F : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ I : Type u,
    Nonempty (F.restrict U.ι ≅ SheafOfModules.free I)

def IsFiniteAffineCover {X : Scheme.{u}} {Idx : Type u} [LinearOrder Idx]
    (U : Idx → X.Opens) : Prop :=
  (⨆ i, U i) = ⊤ ∧ ∀ (n : ℕ) (e : Fin (n + 1) ↪o Idx), IsAffineOpen (tupleOpen U e)

/-- The sheaf endomorphism given by multiplication by a scalar from the base. -/
def multiply (X : SchemeOverRing A) (a : A) (F : X.left.Modules) : F ⟶ F :=
  ⟨{ app U := by
       let aU : X.left.ringCatSheaf.obj.obj U := groundRingHomOpen X U.unop a
       exact ModuleCat.ofHom
         { toFun := fun x => aU • x
           map_add' := fun x y => smul_add _ x y
           map_smul' := fun r x => by
             change aU • (r • x) = r • (aU • x)
             rw [smul_smul, smul_smul]
             exact congrArg (fun t : X.left.ringCatSheaf.obj.obj U => t • x)
               (@mul_comm Γ(X.left, U.unop) _ aU r) }
     naturality {U V} i := by
       apply ModuleCat.hom_ext
       ext x
       let r : X.left.ringCatSheaf.obj.obj U := groundRingHomOpen X U.unop a
       let s : X.left.ringCatSheaf.obj.obj V := groundRingHomOpen X V.unop a
       symm
       change F.val.map i (r • x) = s • (F.val.map i x : F.val.obj V)
       rw [F.val.map_smul]
       have h := DFunLike.congr_fun (localScalars_comp (X := X) i.unop) a
       exact congrArg (fun t : X.left.ringCatSheaf.obj.obj V =>
         t • (F.val.map i x : F.val.obj V)) h.symm }⟩

/-- The comparison is determined by the actual closed-immersion resolution comparison. -/
def IsClosedComparison (φ : A →+* B) (X : SchemeOverRing A) (F : X.left.Modules) (n : ℕ)
    (c : (cohomology X n).obj ((Scheme.Modules.pushforward (fibreProjection φ X)).obj
      (fibreSheaf φ X F)) ≅ (ModuleCat.restrictScalars.{u} φ).obj
      ((cohomology ((changeBase φ).obj X) n).obj (fibreSheaf φ X F))) : Prop :=
  ∀ (J : InjectiveResolution (fibreSheaf φ X F))
    (I : InjectiveResolution ((Scheme.Modules.pushforward (fibreProjection φ X)).obj
      (fibreSheaf φ X F))),
    (∃ l, ClosedImmersionCohomology.LiftsIdentity J I l) ∧
    ∀ l, ClosedImmersionCohomology.LiftsIdentity J I l →
      ClosedImmersionCohomology.inverseComparisonOfLift φ (fibreProjection_over φ X) J I l n =
        c.inv

/-- The flat base-change isomorphism is adjoint to restriction on derived
sections for the pullback–pushforward unit. -/
def CohomologyBaseChange (φ : A →+* B) (X : SchemeOverRing A) (F : X.left.Modules) : Prop :=
  ∀ n : ℕ, ∃ e : (ModuleCat.extendScalars.{u,u,u} φ).obj ((cohomology X n).obj F) ≅
      (cohomology ((changeBase φ).obj X) n).obj (fibreSheaf φ X F),
    IsCohomologyMap φ (fibreProjection φ X) (fibreProjection_over φ X)
      (fibreCoefficientMap φ X F) n
      ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _ e.hom)

/-- Compatible injective resolutions of the three terms of a short complex,
forming a degreewise split short exact sequence of complexes. -/
structure ShortExactResolution {C : Type*} [Category* C] [Abelian C] (S : ShortComplex C) where
  I₁ : InjectiveResolution S.X₁
  I₂ : InjectiveResolution S.X₂
  I₃ : InjectiveResolution S.X₃
  f : I₁.cocomplex ⟶ I₂.cocomplex
  g : I₂.cocomplex ⟶ I₃.cocomplex
  zero : f ≫ g = 0
  comm_f : I₁.ι.f 0 ≫ f.f 0 = ((CochainComplex.single₀ C).map S.f).f 0 ≫ I₂.ι.f 0
  comm_g : I₂.ι.f 0 ≫ g.f 0 = ((CochainComplex.single₀ C).map S.g).f 0 ≫ I₃.ι.f 0
  splitting (n : ℕ) : Nonempty ((ShortComplex.mk f g zero).map
    (HomologicalComplex.eval C (.up ℕ) n)).Splitting

abbrev ShortExactResolution.row {C : Type*} [Category* C] [Abelian C] {S : ShortComplex C}
    (R : ShortExactResolution S) : ShortComplex (CochainComplex C ℕ) :=
  ShortComplex.mk R.f R.g R.zero

/-- The boundary on derived sections computed on any compatible injective resolutions. -/
def IsCohomologyBoundary (X : SchemeOverRing A) (S : ShortComplex X.left.Modules) (n : ℕ)
    (δ : (cohomology X n).obj S.X₃ ⟶ (cohomology X (n + 1)).obj S.X₁) : Prop :=
  ∀ R : ShortExactResolution S,
    ∃ h : (R.row.map ((sectionsFunctor X).mapHomologicalComplex (.up ℕ))).ShortExact,
      δ = (R.I₃.isoRightDerivedObj (sectionsFunctor X) n).hom ≫ h.δ n (n + 1) rfl ≫
        (R.I₁.isoRightDerivedObj (sectionsFunctor X) (n + 1)).inv

/-- Principal reduction in actual sheaf cohomology. The Čech complex of
the direct-image coefficient sheaf uses the sections on inverse images
of the intersections, with scalars restricted to the original base ring. -/
def CohomologyReduction (φ : A →+* B) (a : A) (X : SchemeOverRing A)
    (F : X.left.Modules) : Prop :=
  let G := fibreSheaf φ X F
  let P := (Scheme.Modules.pushforward (fibreProjection φ X)).obj G
  let η := fibreCoefficientMap φ X F
  ∃ hzero : multiply X a F ≫ η = 0,
    let S := ShortComplex.mk (multiply X a F) η hzero
    S.ShortExact ∧ Nonempty (ShortExactResolution S) ∧
    ∀ {Idx : Type u} [LinearOrder Idx] [Fintype Idx] (U : Idx → X.left.Opens),
      IsFiniteAffineCover U →
      (sheafCechFunctor U).map S.f = a • 𝟙 (SheafCech U F) ∧
        ∃ hS : (S.map (sheafCechFunctor U)).ShortExact,
        ∀ n : ℕ,
          let H := (cohomology X n).obj F
          let H' := (cohomology X (n + 1)).obj F
          let K := (ModuleCat.restrictScalars.{u} φ).obj
            ((cohomology ((changeBase φ).obj X) n).obj G)
          let m : H ⟶ H := a • 𝟙 H
          let m' : H' ⟶ H' := a • 𝟙 H'
          ∃ (c : (cohomology X n).obj P ≅ K)
            (e : H' ≅ (SheafCech U F).homology (n + 1))
            (d : (cohomology X n).obj P ≅ (SheafCech U P).homology n)
            (f : H ⧸ LinearMap.range m.hom →ₗ[A] K)
            (g : K →ₗ[A] LinearMap.ker m'.hom),
            IsClosedComparison φ X F n c ∧
            (∀ I : InjectiveResolution F, IsComparisonFromResolution U I (n + 1) e) ∧
            (∀ J : InjectiveResolution P, IsComparisonFromResolution U J n d) ∧
            IsCohomologyBoundary X S n (d.hom ≫ hS.δ n (n + 1) rfl ≫ e.inv) ∧
            (∀ x : H, f ((LinearMap.range m.hom).mkQ x) =
              ((cohomology X n).map η ≫ c.hom) x) ∧
            (∀ y : K, (g y).val = (c.inv ≫ d.hom ≫ hS.δ n (n + 1) rfl ≫ e.inv) y) ∧
            Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g

def FlatBaseChange : Prop :=
  ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B),
    φ.Flat → ∀ (X : SchemeOverRing A) [CompactSpace X.left]
      [IsSeparated (terminal.from X.left)] (F : X.left.Modules),
      F.IsQuasicoherent → CohomologyBaseChange φ X F

def PrincipalReduction : Prop :=
  ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (a : A),
    Function.Injective (a * · : A → A) → Function.Surjective φ →
    RingHom.ker φ = Ideal.span {a} →
    ∀ (X : SchemeOverRing A) [CompactSpace X.left]
      [IsSeparated (terminal.from X.left)] [Flat X.hom] (F : X.left.Modules),
      F.IsQuasicoherent → IsLocallyFree F → CohomologyReduction φ a X F

/-- The localization of the integers inverting the indicated integer. -/
abbrev IntegerAway (m : ℤ) : Type u := Localization.Away (ULift.up.{u} m)

/-- The map of the generic fibre induced by the inclusion of the integers
in the rationals. -/
def rationalMap {m : ℤ} (hm : m ≠ 0) : IntegerAway.{u} m →+* ULift.{u} ℚ :=
  let f : ULift.{u} ℤ →+* ULift.{u} ℚ := (Int.castRingHom _).comp ULift.ringEquiv.toRingHom
  IsLocalization.Away.lift (ULift.up m) (g := f) (isUnit_iff_ne_zero.mpr fun hz => by
    have h := congrArg (fun x : ULift.{u} ℚ => x.down) hz
    change (m : ℚ) = 0 at h
    exact hm (Int.cast_eq_zero.mp h))

/-- The map of the special fibre induced by reduction of the integers
modulo a prime not inverted on the base. -/
def primeMap {m : ℤ} {p : ℕ} [Fact p.Prime] (hp : ¬ (p : ℤ) ∣ m) :
    IntegerAway.{u} m →+* ULift.{u} (ZMod p) :=
  let f : ULift.{u} ℤ →+* ULift.{u} (ZMod p) :=
    (Int.castRingHom _).comp ULift.ringEquiv.toRingHom
  IsLocalization.Away.lift (ULift.up m) (g := f) (isUnit_iff_ne_zero.mpr fun hz => by
    have h := congrArg (fun x : ULift.{u} (ZMod p) => x.down) hz
    change (m : ZMod p) = 0 at h
    exact hp ((ZMod.intCast_zmod_eq_zero_iff_dvd m p).mp h))

/-- Generic base change and the principal reduction sequence over the
localized integer base, with the actual residue field maps. -/
def ArithmeticBaseChange : Prop :=
  ∀ (m : ℤ) (hm : m ≠ 0) (X : SchemeOverRing (IntegerAway.{u} m))
    [IsProper X.hom] [Flat X.hom] (F : X.left.Modules),
    F.IsQuasicoherent → IsLocallyFree F →
    CohomologyBaseChange (rationalMap hm) X F ∧
    ∀ (p : ℕ) [Fact p.Prime] (hp : ¬ (p : ℤ) ∣ m),
      (∃ e : (IntegerAway.{u} m ⧸ Ideal.span {(p : IntegerAway.{u} m)}) ≃+* ULift.{u} (ZMod p),
        ∀ x : IntegerAway.{u} m, e (Ideal.Quotient.mk _ x) = primeMap hp x) ∧
      CohomologyReduction (primeMap hp) (p : IntegerAway.{u} m) X F

end

end LinearAlgebraicGroups.Specs.ArithmeticCohomologyBaseChange
