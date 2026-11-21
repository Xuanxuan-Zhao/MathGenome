import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GroupCochainComparison
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.TorBalance
import Mathlib.Algebra.Category.ModuleCat.Ulift

/-! HA-A01 and HA-A02 on the original modules, with independent universes. -/
noncomputable section
open CategoryTheory
open scoped MonoidAlgebra ModuleCat.Algebra

namespace Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients

set_option linter.checkUnivs false
universe u v w
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

abbrev Coeff := ModuleCat.{w} k[G]

/-- The original scalar carrier with the group-algebra augmentation action. -/
def trivial : ModuleCat.{u} k[G] :=
  ModuleCat.of k[G] (Representation.trivial k G k).asModule

def trivialElement (a : k) : trivial k G :=
  (Representation.trivial k G k).asModuleEquiv.symm a

def invariants (M : Coeff.{u,v,w} k G) : Submodule k M where
  carrier := {m | ∀ g : G, MonoidAlgebra.single g (1 : k) • m = m}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy g; simp [smul_add, hx g, hy g]
  smul_mem' := by intro a x hx g; rw [smul_comm, hx g]

def invariantsFunctor : Coeff.{u,v,w} k G ⥤ ModuleCat.{w} k where
  obj M := ModuleCat.of k (invariants k G M)
  map f := ModuleCat.ofHom
    { toFun m := ⟨f.hom m, fun g => by rw [← f.hom.map_smul, m.property g]⟩
      map_add' := by intros; apply Subtype.ext; exact f.hom.map_add _ _
      map_smul' := by intros; apply Subtype.ext; exact f.hom.map_smul_of_tower _ _ }

abbrev lift : Coeff.{u,v,w} k G ⥤ GroupDerivedInvariants.GroupModule.{u,v,w} k G :=
  ModuleCat.uliftFunctor.{max u v,w} k[G]

abbrev derived (n : ℕ) :=
  lift.{u,v,w} k G ⋙ GroupDerivedInvariants.cohomology.{u,v,w} k G n

abbrev OriginalHom (M : Coeff.{u,v,w} k G) := trivial k G →ₗ[k[G]] M

def evaluationType : Prop :=
  ∃ e : ∀ M : Coeff.{u,v,w} k G, OriginalHom k G M ≃ₗ[k] invariants k G M,
    (∀ M f, (e M f).val = f (trivialElement k G 1)) ∧
    (∀ M m a, (e M).symm m (trivialElement k G a) = a • m.val) ∧
    (∀ (M N : Coeff.{u,v,w} k G) (b : M ⟶ N) f,
      e N (b.hom.comp f) = ((invariantsFunctor k G).map b).hom (e M f))

abbrev TupleCochain (M : Coeff.{u,v,w} k G) (n : ℕ) := (Fin n → G) → M

private def action (M : Coeff.{u,v,w} k G) (g : G) : M →ₗ[k] M where
  toFun m := MonoidAlgebra.single g (1 : k) • m
  map_add' _ _ := smul_add _ _ _
  map_smul' r m := smul_comm (MonoidAlgebra.single g (1 : k)) r m

/-- The unsigned bar precomposition differential in the original coordinates. -/
def differential (M : Coeff.{u,v,w} k G) (n : ℕ) :
    TupleCochain k G M n →ₗ[k] TupleCochain k G M (n+1) :=
  LinearMap.pi fun g =>
    (action k G M (g 0)).comp
        (LinearMap.proj (fun i : Fin n => g i.succ)) +
      (∑ i : Fin n, ((-1 : k) ^ (i.val+1)) •
        LinearMap.proj (Fin.contractNth i.castSucc (· * ·) g)) +
      ((-1 : k) ^ (n+1)) • LinearMap.proj (fun i : Fin n => g i.castSucc)

lemma differential_apply (M : Coeff.{u,v,w} k G) (n : ℕ)
    (f : TupleCochain k G M n) (g : Fin (n+1) → G) :
    differential k G M n f g =
      MonoidAlgebra.single (g 0) (1 : k) • f (fun i => g i.succ) +
      (∑ i : Fin n, (-1 : k) ^ (i.val+1) • f (Fin.contractNth i.castSucc (· * ·) g)) +
      (-1 : k) ^ (n+1) • f (fun i => g i.castSucc) := by
  simp only [differential, LinearMap.pi_apply]
  simp only [LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  rfl

def SquareZero : Prop :=
  ∀ (M : Coeff.{u,v,w} k G) (n : ℕ),
    (differential k G M (n+1)).comp (differential k G M n) = 0

def rawComplex (h : SquareZero.{u,v,w} k G) (M : Coeff.{u,v,w} k G) :
    CochainComplex (ModuleCat.{max v w} k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k (TupleCochain k G M n))
    (fun n => ModuleCat.ofHom (differential k G M n))
    (fun n => ModuleCat.hom_ext (h M n))

def rawFunctor (h : SquareZero.{u,v,w} k G) :
    Coeff.{u,v,w} k G ⥤ CochainComplex (ModuleCat.{max v w} k) ℕ where
  obj := rawComplex k G h
  map b :=
    { f n := ModuleCat.ofHom (LinearMap.pi fun g =>
        (b.hom.restrictScalars k).comp (LinearMap.proj g))
      comm' i j hij := by
        have hji : j = i + 1 := hij.symm
        subst j
        simp only [rawComplex, CochainComplex.of_d]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro f
        funext g
        change differential k G _ i (fun a => b.hom (f a)) g =
          b.hom (differential k G _ i f g)
        simp only [differential_apply, map_add, map_sum, LinearMap.map_smul,
          LinearMap.map_smul_of_tower] }
  map_id _ := by ext n f; rfl
  map_comp _ _ := by ext n f; rfl

abbrev scalarLift : ModuleCat.{max v w} k ⥤ ModuleCat.{max u v w} k :=
  ModuleCat.uliftFunctor.{u,max v w} k

abbrev ambientBar := lift.{u,v,w} k G ⋙
  GroupCochainComparison.Large.homogeneousFunctor.{u,v,w} k G

/-- The raw functions inherit no quotient or restriction on their tuple inputs. -/
def tupleLift (M : Coeff.{u,v,w} k G) (n : ℕ) :
    ULift.{u} (TupleCochain k G M n) ≃ₗ[k]
      GroupCochainComparison.Large.coordinates k G ((lift k G).obj M) n where
  toFun f g := ULift.up (f.down g)
  invFun f := ULift.up (fun g => (f g).down)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev rawLifted (h : SquareZero.{u,v,w} k G) :=
  rawFunctor k G h ⋙ (scalarLift.{u,v,w} k).mapHomologicalComplex (.up ℕ)

abbrev ambientBarCohomology (n : ℕ) := ambientBar.{u,v,w} k G ⋙
  HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} k) (.up ℕ) n

abbrev rawCohomology (h : SquareZero.{u,v,w} k G) (n : ℕ) := rawFunctor k G h ⋙
  HomologicalComplex.homologyFunctor (ModuleCat.{max v w} k) (.up ℕ) n

def liftExactType : Prop :=
  Limits.PreservesFiniteLimits (lift.{u,v,w} k G) ∧
    Limits.PreservesFiniteColimits (lift.{u,v,w} k G)

def barTransportType : Prop :=
  ∃ (h : SquareZero.{u,v,w} k G) (e : ambientBar k G ≅ rawLifted k G h),
    (∀ (M : Coeff.{u,v,w} k G) (n : ℕ)
      (φ : GroupBar.Large.B.{u,v,w} k G n ⟶
        GroupCochainComparison.Large.representation k G ((lift k G).obj M)) (g : Fin n → G),
      (((e.hom.app M).f n).hom φ).down g =
        (φ.hom (GroupBar.Large.single k G (Fin.partialProd g) 1)).down) ∧
    (∀ (M : Coeff.{u,v,w} k G) (n : ℕ)
      (f : TupleCochain k G M n) (g : Fin n → G),
      (((e.inv.app M).f n).hom (ULift.up f) : GroupBar.Large.B.{u,v,w} k G n ⟶
        GroupCochainComparison.Large.representation k G ((lift k G).obj M)).hom
        (GroupBar.Large.single k G (Fin.partialProd g) 1) = ULift.up (f g)) ∧
    (∀ n : ℕ, ∃ (a : derived.{u,v,w} k G n ≅ ambientBarCohomology k G n)
        (r : derived.{u,v,w} k G n ≅ rawCohomology k G h n ⋙ scalarLift.{u,v,w} k),
      ∀ M : Coeff.{u,v,w} k G,
        r.hom.app M = a.hom.app M ≫ HomologicalComplex.homologyMap (e.hom.app M) n ≫
          (((rawComplex k G h M).sc n).mapHomologyIso (scalarLift.{u,v,w} k)).hom)


local instance barToModuleAdditive :
    (Rep.toModuleMonoidAlgebra (k := k) (G := G) :
      Rep.{max u v} k G ⥤ ModuleCat.{max u v} k[G]).Additive where
  map_add := by intros; rfl

/-- The bar terms with the original tuple basis, at the universe of the group ring. -/
abbrev originalBar : ChainComplex (ModuleCat.{max u v} k[G]) ℕ :=
  (Rep.toModuleMonoidAlgebra.mapHomologicalComplex (.down ℕ)).obj
    (GroupBar.Large.complex.{u,v,0} k G)

abbrev basisElement (n : ℕ) (c : Fin (n+1) → G) : (originalBar k G).X n :=
  (GroupBar.Large.B.{u,v,0} k G n).ρ.asModuleEquiv.symm (GroupBar.Large.single k G c 1)

def originalBarCoordinatesType : Prop :=
  ∃ e : ∀ (M : Coeff.{u,v,w} k G) (n : ℕ),
      ((originalBar k G).X n →ₗ[k[G]] M) ≃ₗ[k] TupleCochain k G M n,
    (∀ M n f g, e M n f g = f (basisElement k G n (Fin.partialProd g))) ∧
    (∀ M n f, e M (n+1) (f.comp ((originalBar k G).d (n+1) n).hom) =
      differential k G M n (e M n f)) ∧
    (∀ (M N : Coeff.{u,v,w} k G) (b : M ⟶ N) n f g,
      e N n (b.hom.comp f) g = b.hom (e M n f g))

abbrev invariantLift : ModuleCat.{w} k ⥤ ModuleCat.{max u v w} k :=
  ModuleCat.uliftFunctor.{max u v,w} k

abbrev ambientInvariants := lift.{u,v,w} k G ⋙
  GroupDerivedInvariants.invariantsFunctor.{u,v,w} k G

def invariantsTransportType : Prop :=
  ∃ e : ambientInvariants.{u,v,w} k G ≅ invariantsFunctor k G ⋙ invariantLift.{u,v,w} k,
    (∀ (M : Coeff.{u,v,w} k G) m,
      ((e.hom.app M).hom m).down.val = m.val.down) ∧
    Nonempty (derived.{u,v,w} k G 0 ≅ invariantsFunctor k G ⋙ invariantLift.{u,v,w} k)

abbrev rawInvariantLift : ModuleCat.{w} k ⥤ ModuleCat.{max v w} k :=
  ModuleCat.uliftFunctor.{v,w} k

def barDegreeZeroType : Prop :=
  ∀ h : SquareZero.{u,v,w} k G,
    ∃ e : invariantsFunctor k G ⋙ rawInvariantLift.{u,v,w} k ≅ rawCohomology k G h 0,
      ∀ (M : Coeff.{u,v,w} k G) (m : invariants k G M),
        ∃ z : (rawComplex k G h M).cycles 0,
          ((rawComplex k G h M).iCycles 0).hom z = (fun _ : Fin 0 → G => m.val) ∧
          (e.hom.app M).hom (ULift.up m) = ((rawComplex k G h M).homologyπ 0).hom z

open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions (ExtWith homComplex homPreMap homPostMap)
open ExtShiftedHom

local instance canonicalDerived (A : Type*) [Category A] [Abelian A] :
    HasDerivedCategory A := HasDerivedCategory.standard A

abbrev liftedTrivial :=
  (firstLift.{max u v,u,w,0} k[G]).obj (trivial k G)

abbrev ambientExt (M : Coeff.{u,v,w} k G) (n : ℕ) :=
  Ext (liftedTrivial.{u,v,w} k G) ((lift k G).obj M) (n : ℤ)

def originalBarResolutionType : Prop :=
  ∃ (P : LeftResolution k[G] (trivial k G)) (h : P.complex = originalBar k G),
    P.IsProjective ∧ ∀ c : Fin 1 → G,
      P.ε (h.symm ▸ basisElement k G 0 c) = trivialElement k G 1

abbrev liftOriginalHom (M : Coeff.{u,v,w} k G) (f : OriginalHom k G M) :
    liftedTrivial.{u,v,w} k G ⟶ (lift k G).obj M :=
  ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp
    (f.comp ULift.moduleEquiv.toLinearMap))

def projectiveComputationType : Prop :=
  ∃ (t : liftedTrivial.{u,v,w} k G ≅ GroupDerivedInvariants.trivialModule.{u,v,w} k G)
    (C : IndependentModuleComparison.{max u v,u,w,0,max (u+1) (v+1) (w+1)} k[G])
    (e : ∀ (M : Coeff.{u,v,w} k G) (n : ℕ), (derived k G n).obj M ≃+ ambientExt k G M n),
    (∀ a : k, t.hom.hom (ULift.up (trivialElement k G a)) =
      GroupDerivedInvariants.trivialElement k G a) ∧
    (∀ (M N : Coeff.{u,v,w} k G) (b : M ⟶ N) n x,
      e N n (((derived k G n).map b).hom x) =
        extMap (𝟙 _) ((lift k G).map b) (n : ℤ) (e M n x)) ∧
    ∃ E : ∀ (M : Coeff.{u,v,w} k G) (P : LeftResolution k[G] (trivial k G)),
        P.IsProjective → ∀ n, ExtWith P M n ≃+ (derived k G n).obj M,
      (∀ M P hP n x, e M n (E M P hP n x) = C.equiv (trivial k G) M P hP n x) ∧
      (∀ (M N : Coeff.{u,v,w} k G) (b : M ⟶ N)
        (P Q : LeftResolution k[G] (trivial k G)) (hP : P.IsProjective) (hQ : Q.IsProjective)
        (g : Q.complex ⟶ P.complex) (_ : ChainLift Q P LinearMap.id g) n x,
        E N Q hQ n (homologyMap (homPreMap g M ≫ homPostMap Q.complex b.hom) n x) =
          ((derived k G n).map b).hom (E M P hP n x)) ∧
      ∃ z : ∀ M : Coeff.{u,v,w} k G, (derived k G 0).obj M ≃+ invariants k G M,
        (∀ M (f : OriginalHom k G M),
          (z M ((e M 0).symm (zeroHom (liftOriginalHom k G M f)))).val =
            f (trivialElement k G 1)) ∧
        (∀ (M N : Coeff.{u,v,w} k G) (b : M ⟶ N) (x : (derived k G 0).obj M),
          z N (((derived k G 0).map b).hom x) = ((invariantsFunctor k G).map b).hom (z M x)) ∧
        (∀ (M : Coeff.{u,v,w} k G) (P : LeftResolution k[G] (trivial k G))
          (hP : P.IsProjective) (x : cycles (homComplex P.complex M) 0) (f : OriginalHom k G M),
          f.comp P.ε = x.val →
          (z M (E M P hP 0 (homologyClass _ 0 x))).val = f (trivialElement k G 1))


def injectiveComputationType : Prop :=
  ∃ E : ∀ (M : Coeff.{u,v,w} k G)
      (I : CochainComplex (GroupDerivedInvariants.GroupModule.{u,v,w} k G) ℤ) [I.IsStrictlyGE 0]
      (i : (CochainComplex.singleFunctor _ 0).obj ((lift k G).obj M) ⟶ I),
      QuasiIso i → (∀ q, Injective (I.X q)) → ∀ n : ℕ,
      (derived k G n).obj M ≅
        (((GroupDerivedInvariants.invariantsFunctor k G).mapHomologicalComplex (.up ℤ)).obj I).homology
          (n : ℤ),
    ∀ (M N : Coeff.{u,v,w} k G)
      (I J : CochainComplex (GroupDerivedInvariants.GroupModule.{u,v,w} k G) ℤ)
      [I.IsStrictlyGE 0] [J.IsStrictlyGE 0]
      (i : (CochainComplex.singleFunctor _ 0).obj ((lift k G).obj M) ⟶ I)
      (j : (CochainComplex.singleFunctor _ 0).obj ((lift k G).obj N) ⟶ J)
      (hi : QuasiIso i) (hj : QuasiIso j) (hI : ∀ q, Injective (I.X q))
      (hJ : ∀ q, Injective (J.X q)) (b : M ⟶ N) (g : I ⟶ J)
      (_ : Homotopy (i ≫ g) ((CochainComplex.singleFunctor _ 0).map ((lift k G).map b) ≫ j))
      (n : ℕ),
      ((derived k G n).map b) ≫ (E N J j hj hJ n).hom = (E M I i hi hI n).hom ≫
        HomologicalComplex.homologyMap
          (((GroupDerivedInvariants.invariantsFunctor k G).mapHomologicalComplex (.up ℤ)).map g) (n : ℤ)

def resolutionLiftsType : Prop :=
  (∀ (P Q : LeftResolution k[G] (trivial k G)), Q.IsProjective →
    ∃ g : Q.complex ⟶ P.complex, ChainLift Q P LinearMap.id g) ∧
  (∀ (M N : Coeff.{u,v,w} k G) (b : M ⟶ N)
    (I J : CochainComplex (GroupDerivedInvariants.GroupModule.{u,v,w} k G) ℤ)
    [J.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor _ 0).obj ((lift k G).obj M) ⟶ I)
    (j : (CochainComplex.singleFunctor _ 0).obj ((lift k G).obj N) ⟶ J),
    QuasiIso i → (∀ q, Injective (J.X q)) →
    ∃ g : I ⟶ J, Nonempty (Homotopy (i ≫ g)
      ((CochainComplex.singleFunctor _ 0).map ((lift k G).map b) ≫ j)))

end Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients

namespace Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients

universe u v w

def evaluationExpected : Prop := ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
  evaluationType.{u,v,w} k G

def liftExactExpected : Prop := ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
  liftExactType.{u,v,w} k G

def squareZeroExpected : Prop := ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
  SquareZero.{u,v,w} k G

def barTransportExpected : Prop := ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
  barTransportType.{u,v,w} k G

def originalBarComparisonExpected : Prop := ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
  originalBarCoordinatesType.{u,v,w} k G

def originalBarResolutionExpected : Prop := ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
  originalBarResolutionType k G

def barDegreeZeroExpected : Prop := ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
  barDegreeZeroType.{u,v,w} k G

def invariantsTransportExpected : Prop := ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
  invariantsTransportType.{u,v,w} k G

def projectiveComputationExpected : Prop := ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
  projectiveComputationType.{u,v,w} k G

def injectiveComputationExpected : Prop := ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
  injectiveComputationType.{u,v,w} k G

def resolutionLiftsExpected : Prop := ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
  resolutionLiftsType.{u,v,w} k G

end Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients

namespace Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.IndependentResolution

open AdvancedHomologicalAlgebra.TorBalance (AugmentedResolution LinearChainMap)
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions (ExtWith homComplex)

universe u v w w' a b
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

abbrev Resolution (k : Type u) (G : Type v) [CommRing k] [Group G] :=
  AugmentedResolution.{max u v,u,a} k[G] (trivial k G)

/-- The actual unsigned Hom quotient on the given resolution terms and coefficient. -/
abbrev Cohomology (P : Resolution.{u,v,a} k G) (M : Coeff.{u,v,w} k G) (n : ℕ) :=
  Homology (homComplex P.complex M) n

/-- On the given Hom terms use precomposition by the resolution lift and
postcomposition by the coefficient map, even when the resolution levels differ. -/
def homMap {P : Resolution.{u,v,a} k G} {Q : Resolution.{u,v,b} k G}
    {M : Coeff.{u,v,w} k G} {N : Coeff.{u,v,w'} k G}
    (g : LinearChainMap Q.complex P.complex)
    (f : M →ₗ[k[G]] N) : LinearChainMap (homComplex P.complex M) (homComplex Q.complex N) where
  app n :=
    { toFun z := f.comp (z.comp (g.app n))
      map_add' z z' := by
        change P.complex.X n →ₗ[k[G]] M at z z'
        change f.comp ((z + z').comp (g.app n)) =
          f.comp (z.comp (g.app n)) + f.comp (z'.comp (g.app n))
        rw [LinearMap.add_comp, LinearMap.comp_add]
      map_smul' r z := by
        change P.complex.X n →ₗ[k[G]] M at z
        change f.comp ((r • z).comp (g.app n)) = r • f.comp (z.comp (g.app n))
        rw [LinearMap.smul_comp, LinearMap.comp_smul] }
  comm i j := by
    apply LinearMap.ext
    intro z
    change P.complex.X i →ₗ[k[G]] M at z
    apply LinearMap.ext
    intro x
    change f (z (g.app i ((Q.complex.d j i).hom x))) =
      f (z ((P.complex.d j i).hom (g.app j x)))
    exact congrArg (fun y => f (z y)) (LinearMap.congr_fun (g.comm j i).symm x)

abbrev OriginalLift {P : Resolution.{u,v,a} k G} {Q : Resolution.{u,v,b} k G}
    (g : LinearChainMap Q.complex P.complex) :=
  Q.Lifts P LinearMap.id g

/-- Any chosen ordinary P103 projective resolution, including the original
bar resolution, supplies the anchor in the original coefficient universe. -/
structure Comparison (B : LeftResolution k[G] (trivial k G)) (hB : B.IsProjective) where
  equiv : ∀ (P : Resolution.{u,v,a} k G) (M : Coeff.{u,v,w} k G) (n : ℕ),
    Cohomology k G P M n ≃+ ExtWith B M n
  precompose : ∀ (P : Resolution.{u,v,a} k G)
    (g : LinearChainMap B.complex P.complex),
    OriginalLift k G (Q := AugmentedResolution.ofP103 B hB) g →
    ∀ (M : Coeff.{u,v,w} k G) (n : ℕ) (z : Cohomology k G P M n),
      equiv P M n z =
        (homMap k G (Q := AugmentedResolution.ofP103 B hB) (N := M) g LinearMap.id).homologyMap n z

def resolutionLiftsExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G]
    (P : Resolution.{u,v,a} k G) (Q : Resolution.{u,v,b} k G),
    ∃ g : LinearChainMap Q.complex P.complex, OriginalLift k G g

local instance canonicalDerived (A : Type*) [Category A] [Abelian A] :
    HasDerivedCategory A := HasDerivedCategory.standard A

abbrev liftedInvariant (M : Coeff.{u,v,w} k G) (m : invariants k G M) :
    GroupDerivedInvariants.invariants k G ((lift k G).obj M) :=
  ⟨ULift.up m.val, fun g => congrArg ULift.up (m.property g)⟩

abbrev degreeZeroUnit :=
  ClassicalDerivedValues.rightDegreeZeroUnit (GroupDerivedInvariants.invariantsFunctor.{u,v,w} k G)

open ExtShiftedHom

/-- The cohomology of the given resolution computes the previously specified
derived value by first passing to the ordinary P103 quotient. This ties the
comparison to the actual Ext comparison in the original ambient category. -/
def projectiveComputationType : Prop :=
  ∃ (C : IndependentModuleComparison.{max u v,u,w,0,max (u+1) (v+1) (w+1)} k[G])
    (e : ∀ (M : Coeff.{u,v,w} k G) (n : ℕ), (derived k G n).obj M ≃+ ambientExt k G M n)
    (d₀ : ∀ M : Coeff.{u,v,w} k G, (derived k G 0).obj M ≃+ invariants k G M),
    (∀ (M N : Coeff.{u,v,w} k G) (f : M ⟶ N) n z,
      e N n (((derived k G n).map f).hom z) =
        extMap (𝟙 _) ((lift k G).map f) (n : ℤ) (e M n z)) ∧
    (∀ (M : Coeff.{u,v,w} k G) (m : invariants k G M),
      d₀ M (((degreeZeroUnit k G).app ((lift k G).obj M)).hom (liftedInvariant k G M m)) = m) ∧
    ∀ (B : LeftResolution k[G] (trivial k G)) (hB : B.IsProjective),
      ∃ (D : Comparison.{u,v,w,a} k G B hB) (D' : Comparison.{u,v,w,b} k G B hB),
        let toDerived := fun M n => (C.equiv (trivial k G) M B hB n).trans (e M n).symm
        (∀ (P : Resolution.{u,v,a} k G) (Q : Resolution.{u,v,b} k G)
          (M N : Coeff.{u,v,w} k G) (f : M ⟶ N)
          (g : LinearChainMap Q.complex P.complex), OriginalLift k G g →
          ∀ n (z : Cohomology k G P M n),
            toDerived N n (D'.equiv Q N n ((homMap k G g f.hom).homologyMap n z)) =
              ((derived k G n).map f).hom (toDerived M n (D.equiv P M n z))) ∧
        ∀ (P : Resolution.{u,v,a} k G) (M : Coeff.{u,v,w} k G)
          (z : cycles (homComplex P.complex M) 0) (f : OriginalHom k G M),
          f.comp P.ε = z.val →
          (d₀ M (toDerived M 0 (D.equiv P M 0 (homologyClass _ 0 z)))).val =
            f (trivialElement k G 1)

def projectiveComputationExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G], projectiveComputationType.{u,v,w,a,b} k G

end Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.IndependentResolution

namespace Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NormalizedBar

universe u v s
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

abbrev Ambient := GroupDerivedInvariants.GroupModule.{u,v,s} k G
abbrev cochains := GroupCochainComparison.Large.homogeneousFunctor.{u,v,s} k G
abbrev cohomology (n : ℕ) :=
  cochains.{u,v,s} k G ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{max u v s} k) (.up ℕ) n

local instance cochainsAdditive : (cochains.{u,v,s} k G).Additive where
  map_add := by
    intro M N f g
    ext n φ
    rfl

local instance canonicalDerived (A : Type*) [Category A] [Abelian A] :
    HasDerivedCategory A := HasDerivedCategory.standard A

abbrev degreeZeroUnit :=
  ClassicalDerivedValues.rightDegreeZeroUnit (GroupDerivedInvariants.invariantsFunctor.{u,v,s} k G)

/-- The comparison with the actual homogeneous cochains extending evaluation
at the original vertex 1 and commuting with their connecting maps. -/
structure Comparison where
  iso : ∀ n : ℕ, GroupDerivedInvariants.cohomology.{u,v,s} k G n ≅ cohomology.{u,v,s} k G n
  exact : ∀ {S : ShortComplex (Ambient.{u,v,s} k G)}, S.ShortExact →
    (S.map (cochains.{u,v,s} k G)).ShortExact
  degreeZero : ∀ (M : Ambient.{u,v,s} k G) (m : GroupDerivedInvariants.invariants k G M),
    let C := (cochains.{u,v,s} k G).obj M
    ∃ (z : C.X 0) (hz : (C.d 0 1).hom z = 0),
      z.hom (GroupBar.Large.single k G (fun _ : Fin 1 => 1) 1) = m.val ∧
      ((iso 0).hom.app M).hom (((degreeZeroUnit.{u,v,s} k G).app M).hom m) =
        (C.homologyπ 0).hom (C.cyclesMk z 1 (by simp) hz)
  boundary : ∀ {S : ShortComplex (Ambient.{u,v,s} k G)} (hS : S.ShortExact) (n : ℕ),
    ClassicalDerivedValues.rightBoundary (GroupDerivedInvariants.invariantsFunctor k G) hS n ≫
      (iso (n+1)).hom.app S.X₁ =
    (iso n).hom.app S.X₃ ≫ (exact hS).δ n (n+1) rfl

def comparisonExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
    Nonempty (Comparison.{u,v,s} k G)

end Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NormalizedBar

namespace Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NativeTransport

set_option linter.checkUnivs false

universe u v w t s
open CategoryTheory
open scoped MonoidAlgebra
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

/-- Enlarge the coefficient category over the same group algebra. -/
abbrev coefficientLift :
    GroupDerivedInvariants.GroupModule.{u,v,w} k G ⥤
      GroupDerivedInvariants.GroupModule.{u,v,max w s} k G :=
  ModuleCat.uliftFunctor.{s,max u v w} k[G]

/-- Enlarge the scalar category over the same coefficient ring. -/
abbrev valueLift : ModuleCat.{max u v w} k ⥤ ModuleCat.{max u v w s} k :=
  ModuleCat.uliftFunctor.{s,max u v w} k

/-- Carry the original coefficient first to its native category and then to
the common category over the same group algebra. -/
abbrev commonCoefficient (M : Coeff.{u,v,w} k G) :
    GroupDerivedInvariants.GroupModule.{u,v,max w s} k G :=
  (coefficientLift.{u,v,w,s} k G).obj ((lift.{u,v,w} k G).obj M)

abbrev commonCoefficientIso (M : Coeff.{u,v,w} k G) :
    M ≃ₗ[k[G]] commonCoefficient.{u,v,w,s} k G M :=
  (ULift.moduleEquiv.symm : M ≃ₗ[k[G]] (lift.{u,v,w} k G).obj M).trans
    ULift.moduleEquiv.symm

/-- The actual original coefficient map conjugated into the common category. -/
def commonCoefficientMap {M : Coeff.{u,v,w} k G} {N : Coeff.{u,v,t} k G}
    (f : M →ₗ[k[G]] N) :
    commonCoefficient.{u,v,w,max t s} k G M ⟶ commonCoefficient.{u,v,t,max w s} k G N :=
  ModuleCat.ofHom ((commonCoefficientIso.{u,v,t,max w s} k G N).toLinearMap.comp
    (f.comp (commonCoefficientIso.{u,v,w,max t s} k G M).symm.toLinearMap))

local instance canonicalDerived (A : Type*) [Category A] [Abelian A] :
    HasDerivedCategory A := HasDerivedCategory.standard A

abbrev degreeZeroUnit :=
  ClassicalDerivedValues.rightDegreeZeroUnit
    (GroupDerivedInvariants.invariantsFunctor.{u,v,w} k G)

/-- Derived carrier transport is required to intertwine the actual derived
connecting maps, starting at the pointwise lift of the original fixed elements. -/
structure Comparison where
  iso : ∀ n : ℕ, GroupDerivedInvariants.cohomology.{u,v,w} k G n ⋙
      valueLift.{u,v,w,s} k ≅
    coefficientLift.{u,v,w,s} k G ⋙ GroupDerivedInvariants.cohomology.{u,v,max w s} k G n
  degreeZero : ∀ (M : GroupDerivedInvariants.GroupModule.{u,v,w} k G)
    (m : GroupDerivedInvariants.invariants k G M),
      ((iso 0).hom.app M).hom (ULift.up (((degreeZeroUnit.{u,v,w} k G).app M).hom m)) =
        ((degreeZeroUnit.{u,v,max w s} k G).app ((coefficientLift.{u,v,w,s} k G).obj M)).hom
          ⟨ULift.up m.val, fun g => congrArg ULift.up (m.property g)⟩
  boundary : ∀ (S : ShortComplex (GroupDerivedInvariants.GroupModule.{u,v,w} k G))
    (h : S.ShortExact) (n : ℕ),
    (valueLift.{u,v,w,s} k).map
        (ClassicalDerivedValues.rightBoundary (GroupDerivedInvariants.invariantsFunctor k G) h n) ≫
      (iso (n+1)).hom.app S.X₁ =
    (iso n).hom.app S.X₃ ≫
      ClassicalDerivedValues.rightBoundary
        (GroupDerivedInvariants.invariantsFunctor.{u,v,max w s} k G)
        (h.map_of_exact (coefficientLift.{u,v,w,s} k G)) n

/-- The comparison on the prescribed native value of the original coefficient. -/
def Comparison.onOriginal (T : Comparison.{u,v,w,s} k G)
    (M : Coeff.{u,v,w} k G) (n : ℕ) :
    (derived.{u,v,w} k G n).obj M ≃ₗ[k]
      (GroupDerivedInvariants.cohomology.{u,v,max w s} k G n).obj
        (commonCoefficient.{u,v,w,s} k G M) :=
  ULift.moduleEquiv.symm.trans (((T.iso n).app ((lift.{u,v,w} k G).obj M)).toLinearEquiv)

def comparisonExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
    Nonempty (Comparison.{u,v,w,s} k G)

end Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NativeTransport

namespace Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.IndependentInjective

open AdvancedHomologicalAlgebra.TorBalance (LinearChainMap)
open ClassicalDerivedValues (rightValue rightDegreeZeroUnit)
open NativeTransport (commonCoefficient commonCoefficientMap)

set_option linter.checkUnivs false
attribute [local instance] HasDerivedCategory.standard

universe u v w a b s t
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

/-- A coaugmented injective resolution of the original coefficient. The Baer
condition tests the actual term against left ideals of the original group ring
even when that term's carrier universe is smaller than the group ring. -/
structure Resolution (M : Coeff.{u,v,w} k G) where
  complex : CochainComplex (Coeff.{u,v,a} k G) ℤ
  nonnegative : complex.IsStrictlyGE 0
  ι : M →ₗ[k[G]] complex.X 0
  ι_injective : Function.Injective ι
  exact_zero : LinearMap.range ι = LinearMap.ker (complex.d 0 1).hom
  exact_succ (n : ℕ) : LinearMap.range (complex.d (n : ℤ) ((n : ℤ) + 1)).hom =
    LinearMap.ker (complex.d ((n : ℤ) + 1) ((n : ℤ) + 2)).hom
  baer (n : ℤ) : Module.Baer k[G] (complex.X n)

local instance : (invariantsFunctor.{u,v,a} k G).Additive where

abbrev Resolution.fixedComplex {M : Coeff.{u,v,w} k G} (I : Resolution.{u,v,w,a} k G M) :=
  ((invariantsFunctor.{u,v,a} k G).mapHomologicalComplex (.up ℤ)).obj I.complex

abbrev Resolution.fixedCohomology {M : Coeff.{u,v,w} k G}
    (I : Resolution.{u,v,w,a} k G M) (n : ℕ) :=
  (I.fixedComplex k G).homology (n : ℤ)

variable {k G} in
/-- A cochain map of resolutions lifting the given original coefficient map. -/
def Lifts {M : Coeff.{u,v,w} k G} {N : Coeff.{u,v,s} k G}
    {I : Resolution.{u,v,w,a} k G M} {J : Resolution.{u,v,s,b} k G N}
    (f : M →ₗ[k[G]] N) (g : LinearChainMap I.complex J.complex) : Prop :=
  ∀ m, g.app 0 (I.ι m) = J.ι (f m)

/-- Restriction to the fixed submodules over the original scalars. -/
def fixedMap {M : Coeff.{u,v,w} k G} {N : Coeff.{u,v,s} k G}
    {I : Resolution.{u,v,w,a} k G M} {J : Resolution.{u,v,s,b} k G N}
    (g : LinearChainMap I.complex J.complex) :
    LinearChainMap (I.fixedComplex k G) (J.fixedComplex k G) where
  app n :=
    { toFun x := ⟨g.app n x.val, fun t => by rw [← (g.app n).map_smul, x.property t]⟩
      map_add' x y := Subtype.ext ((g.app n).map_add x.val y.val)
      map_smul' r x := Subtype.ext ((g.app n).map_smul_of_tower r x.val) }
  comm i j := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact LinearMap.congr_fun (g.comm i j) z.val

def resolutionLiftsExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G]
    (M : Coeff.{u,v,w} k G) (N : Coeff.{u,v,s} k G) (f : M →ₗ[k[G]] N)
    (I : Resolution.{u,v,w,a} k G M) (J : Resolution.{u,v,s,b} k G N),
    ∃ g : LinearChainMap I.complex J.complex, Lifts f g

/-- Map from the cohomology of an augmented ambient model to the prescribed
right-derived value, using the derivative of the actual localized coaugmentation
and the actual right-derived unit on the model. -/
def resolutionModelMap {A : Type*} {B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [EnoughInjectives A] (F : A ⥤ B) [F.Additive]
    {M : A} {I : CochainComplex A ℤ} [I.IsStrictlyGE 0]
    (ι : (CochainComplex.singleFunctor A 0).obj M ⟶ I) (hι : QuasiIso ι) (n : ℕ) :
    ((F.mapHomologicalComplex (.up ℤ)).obj I).homology (n : ℤ) ⟶ (rightValue F n).obj M := by
  let K : CochainComplex.Plus A := ⟨I, 0, inferInstance⟩
  let L : CochainComplex.Plus A := ⟨(CochainComplex.singleFunctor A 0).obj M, 0, inferInstance⟩
  let q : L ⟶ K := ObjectProperty.homMk ι
  haveI : IsIso (DerivedCategory.Plus.Q.map q) :=
    Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso A) q hι
  exact (DerivedCategory.homologyFunctorFactors B (n : ℤ)).inv.app _ ≫
    (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).map
      (F.rightDerivedFunctorPlusUnit.app K ≫ F.rightDerivedFunctorPlus.map
        (inv (DerivedCategory.Plus.Q.map q)))

abbrev termLift : Coeff.{u,v,a} k G ⥤ GroupDerivedInvariants.GroupModule.{u,v,max a s} k G :=
  ModuleCat.uliftFunctor.{max u v s,a} k[G]

abbrev fixedTermLift : ModuleCat.{a} k ⥤ ModuleCat.{max u a s} k :=
  ModuleCat.uliftFunctor.{max u s,a} k

abbrev liftComplex {M : Coeff.{u,v,w} k G} (I : Resolution.{u,v,w,a} k G M) :
    CochainComplex (GroupDerivedInvariants.GroupModule.{u,v,max w a s} k G) ℤ :=
  ((termLift.{u,v,a,max w s} k G).mapHomologicalComplex (.up ℤ)).obj I.complex

abbrev commonInvariants :=
  GroupDerivedInvariants.invariantsFunctor.{u,v,max w a s} k G

/-- Exact enlargement of the actual resolution and pointwise identification of
the fixed submodules. The coaugmentation on the ambient stalk is prescribed
by the original coaugmentation. -/
structure AmbientModel {M : Coeff.{u,v,w} k G} (I : Resolution.{u,v,w,a} k G M) where
  nonnegative : (liftComplex.{u,v,w,a,s} k G I).IsStrictlyGE 0
  coaugmentation :
    (CochainComplex.singleFunctor _ 0).obj (commonCoefficient.{u,v,w,max a s} k G M) ⟶
      liftComplex.{u,v,w,a,s} k G I
  coaugmentation_apply : ∀ m : M,
    (coaugmentation.f 0).hom
      ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (commonCoefficient.{u,v,w,max a s} k G M)).inv.hom (ULift.up (ULift.up m))) =
        ULift.up (I.ι m)
  exact : QuasiIso coaugmentation
  injective : ∀ q : ℤ, Injective ((liftComplex.{u,v,w,a,s} k G I).X q)
  fixedIso :
    (((fixedTermLift.{u,a,max v w s} k).mapHomologicalComplex (.up ℤ)).obj
      (I.fixedComplex k G)) ≅
      (((commonInvariants.{u,v,w,a,s} k G).mapHomologicalComplex (.up ℤ)).obj
        (liftComplex.{u,v,w,a,s} k G I))
  fixedIso_apply : ∀ n (x : invariants k G (I.complex.X n)),
    ((fixedIso.hom.f n).hom (ULift.up x)).val = ULift.up x.val

/-- The comparison of categorical homology induced by the exact scalar lift. -/
def homologyLift {C : CochainComplex (ModuleCat.{a} k) ℤ} (n : ℤ) :
    (fixedTermLift.{u,a,s} k).obj (C.homology n) ≅
      (((fixedTermLift.{u,a,s} k).mapHomologicalComplex (.up ℤ)).obj C).homology n :=
  ((C.sc n).mapHomologyIso (fixedTermLift.{u,a,s} k)).symm

/-- The map on actual fixed-submodule cohomology induced by the pointwise
carrier isomorphism and the right-derived comparison of this resolution. -/
def AmbientModel.toDerived {M : Coeff.{u,v,w} k G} {I : Resolution.{u,v,w,a} k G M}
    (A : AmbientModel.{u,v,w,a,s} k G I) (n : ℕ) :
    I.fixedCohomology k G n →ₗ[k]
      (GroupDerivedInvariants.cohomology.{u,v,max w a s} k G n).obj
        (commonCoefficient.{u,v,w,max a s} k G M) := by
  letI := A.nonnegative
  exact (resolutionModelMap (commonInvariants.{u,v,w,a,s} k G)
      A.coaugmentation A.exact n).hom
    ∘ₗ (HomologicalComplex.homologyMap A.fixedIso.hom (n : ℤ)).hom
    ∘ₗ (ULift.moduleEquiv.symm.trans
      (homologyLift.{u,a,max v w s} k (C := I.fixedComplex k G) (n : ℤ)).toLinearEquiv).toLinearMap

/-- Computation on the given resolution in its original terms, pinned to the
specified derived-invariants value through its normalized carrier comparison. -/
structure Computation (T : NativeTransport.Comparison.{u,v,w,max a s} k G)
    (M : Coeff.{u,v,w} k G) (I : Resolution.{u,v,w,a} k G M) where
  model : AmbientModel.{u,v,w,a,s} k G I
  comparison (n : ℕ) : I.fixedCohomology k G n ≃ₗ[k] (derived.{u,v,w} k G n).obj M
  agrees (n : ℕ) (z : I.fixedCohomology k G n) :
    T.onOriginal k G M n (comparison n z) = model.toDerived k G n z
  degreeZero (m : invariants k G M) :
    ∃ z : (I.fixedComplex k G).cycles 0,
      (((I.fixedComplex k G).iCycles 0).hom z).val = I.ι m.val ∧
      comparison 0 (((I.fixedComplex k G).homologyπ 0).hom z) =
        ((NativeTransport.degreeZeroUnit.{u,v,w} k G).app ((lift.{u,v,w} k G).obj M)).hom
          (IndependentResolution.liftedInvariant k G M m)

def computationExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G]
    (T : NativeTransport.Comparison.{u,v,w,max a s} k G)
    (M : Coeff.{u,v,w} k G) (I : Resolution.{u,v,w,a} k G M),
    Nonempty (Computation.{u,v,w,a,s} k G T M I)

/-- Turn an original mixed map into a chain map between the two exact carrier
lifts. On each degree use the unchanged original map in ULift coordinates. -/
def liftFixedMap {C : CochainComplex (ModuleCat.{a} k) ℤ}
    {D : CochainComplex (ModuleCat.{b} k) ℤ} (g : LinearChainMap C D) :
    (((fixedTermLift.{u,a,max b s} k).mapHomologicalComplex (.up ℤ)).obj C) ⟶
    (((fixedTermLift.{u,b,max a s} k).mapHomologicalComplex (.up ℤ)).obj D) where
  f n := ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp
    ((g.app n).comp ULift.moduleEquiv.toLinearMap))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ULift.up ((D.d i j).hom (g.app i x.down)) =
      ULift.up (g.app j ((C.d i j).hom x.down))
    exact congrArg ULift.up (LinearMap.congr_fun (g.comm i j) x.down)

/-- The map of original cohomology classes induced by a mixed map of fixed
submodule complexes. The cycle and boundary maps are the ones from the exact
scalar lifts and the original degreewise map. -/
def fixedCohomologyMap {C : CochainComplex (ModuleCat.{a} k) ℤ}
    {D : CochainComplex (ModuleCat.{b} k) ℤ} (g : LinearChainMap C D) (n : ℕ) :
    C.homology (n : ℤ) →ₗ[k] D.homology (n : ℤ) :=
  ((homologyLift.{u,b,max a s} k (C := D) (n : ℤ)).toLinearEquiv.symm.trans
      ULift.moduleEquiv).toLinearMap
    ∘ₗ (HomologicalComplex.homologyMap (liftFixedMap.{u,a,b,s} k g) (n : ℤ)).hom
    ∘ₗ (ULift.moduleEquiv.symm.trans
      (homologyLift.{u,a,max b s} k (C := C) (n : ℤ)).toLinearEquiv).toLinearMap

/-- Naturality for every given mixed coaugmentation-preserving comparison
map, including the identity on the coefficient and independent choices of
resolution terms. -/
def naturalityExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G]
    (S : NativeTransport.Comparison.{u,v,w,max t a b s} k G)
    (T : NativeTransport.Comparison.{u,v,t,max w a b s} k G)
    (M : Coeff.{u,v,w} k G) (N : Coeff.{u,v,t} k G) (f : M →ₗ[k[G]] N)
    (I : Resolution.{u,v,w,a} k G M) (J : Resolution.{u,v,t,b} k G N)
    (C : Computation.{u,v,w,a,max t b s} k G S M I)
    (D : Computation.{u,v,t,b,max w a s} k G T N J)
    (g : LinearChainMap I.complex J.complex), Lifts f g →
    ∀ (n : ℕ) (z : I.fixedCohomology k G n),
      T.onOriginal k G N n
          (D.comparison n (fixedCohomologyMap.{u,a,b,max v w t s} k (fixedMap k G g) n z)) =
        ((GroupDerivedInvariants.cohomology.{u,v,max w t a b s} k G n).map
          (commonCoefficientMap.{u,v,w,t,max a b s} k G f)).hom
          (S.onOriginal k G M n (C.comparison n z))

end Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.IndependentInjective

namespace Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.MixedProjective

open AdvancedHomologicalAlgebra.TorBalance (AugmentedResolution LinearChainMap)
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions (ExtWith homComplex)
open IndependentResolution (Resolution Cohomology homMap OriginalLift)
open ExtShiftedHom
open NativeTransport (commonCoefficient commonCoefficientIso commonCoefficientMap)

universe u v a b p q s

variable (k : Type u) (G : Type v) [CommRing k] [Group G]

abbrev nativeCoeffIso (M : Coeff.{u,v,a} k G) :
    M ≃ₗ[k[G]] (lift.{u,v,a} k G).obj M :=
  ULift.moduleEquiv.symm

abbrev homBar (N : GroupDerivedInvariants.GroupModule.{u,v,s} k G) :=
  (NormalizedBar.cochains.{u,v,s} k G).obj N

abbrev integralHomBar (N : GroupDerivedInvariants.GroupModule.{u,v,s} k G) :=
  ((ModuleCat.restrictScalars (Int.castRingHom k)).mapHomologicalComplex (.up ℕ)).obj
    (homBar.{u,v,s} k G N)

/-- The comparison transports the actual original Hom cochains to the
homogeneous cochains by the original tuple generators. The homology map is
induced by this same comparison on each original cycle. -/
structure BarComparison (B : LeftResolution k[G] (trivial k G))
    (hB : B.complex = originalBar k G) (M : Coeff.{u,v,a} k G)
    (N : GroupDerivedInvariants.GroupModule.{u,v,s} k G) (iota : M ≃ₗ[k[G]] N) where
  cochain : LinearChainMap (homComplex B.complex M) (integralHomBar.{u,v,s} k G N)
  term_bijective : ∀ n, Function.Bijective (cochain.app n)
  coordinates : ∀ (n : ℕ) (z : B.complex.X n →ₗ[k[G]] M) (g : Fin n → G),
    (show GroupBar.Large.B.{u,v,s} k G n ⟶
      GroupCochainComparison.Large.representation.{u,v,s} k G N from cochain.app n z).hom
        (GroupBar.Large.single.{u,v,s} k G (Fin.partialProd g) 1) =
      iota (z (hB.symm ▸ basisElement k G n (Fin.partialProd g)))
  classes : ∀ n, ExtWith B M n ≃+ (homBar.{u,v,s} k G N).homology n
  class_formula : ∀ (n : ℕ) (z : cycles (homComplex B.complex M) n),
    ∃ y : (homBar.{u,v,s} k G N).cycles n,
      ((homBar.{u,v,s} k G N).iCycles n).hom y = cochain.app n z.val ∧
      classes n (homologyClass _ n z) = ((homBar.{u,v,s} k G N).homologyπ n).hom y

local instance canonicalDerived (A : Type*) [Category A] [Abelian A] :
    HasDerivedCategory A := HasDerivedCategory.standard A

/-- For each native carrier level, the projective computation uses the
specified P103 Ext comparison, with its values fixed by the normalized
homogeneous bar comparison at the ordinary bar resolution. -/
structure NativeComparison (A : NormalizedBar.Comparison.{u,v,a} k G)
    (B : LeftResolution k[G] (trivial k G)) (hB : B.IsProjective)
    (bar : B.complex = originalBar k G) where
  p103 : IndependentModuleComparison.{max u v,u,a,0,max (u+1) (v+1) (a+1)} k[G]
  ext : ∀ (M : Coeff.{u,v,a} k G) (n : ℕ), (derived k G n).obj M ≃+ ambientExt k G M n
  ext_natural : ∀ (M N : Coeff.{u,v,a} k G) (f : M ⟶ N) n x,
    ext N n (((derived k G n).map f).hom x) =
      extMap (𝟙 _) ((lift k G).map f) (n : ℤ) (ext M n x)
  original : IndependentResolution.Comparison.{u,v,a,p} k G B hB
  bar_comparison : ∀ M : Coeff.{u,v,a} k G,
    BarComparison.{u,v,a,a} k G B bar M ((lift k G).obj M) (nativeCoeffIso k G M)
  bar_agreement : ∀ (M : Coeff.{u,v,a} k G) n (x : ExtWith B M n),
    ((A.iso n).hom.app ((lift k G).obj M)).hom
        ((ext M n).symm (p103.equiv (trivial k G) M B hB n x)) =
      (bar_comparison M).classes n x

def NativeComparison.value {A : NormalizedBar.Comparison.{u,v,a} k G}
    {B : LeftResolution k[G] (trivial k G)} {hB : B.IsProjective}
    {bar : B.complex = originalBar k G}
    (E : NativeComparison.{u,v,a,p} k G A B hB bar)
    (P : Resolution.{u,v,p} k G) (M : Coeff.{u,v,a} k G) (n : ℕ) :
    Cohomology k G P M n ≃+ (derived k G n).obj M :=
  (E.original.equiv P M n).trans
    ((E.p103.equiv (trivial k G) M B hB n).trans (E.ext M n).symm)

/-- The normalized computation on the native derived value also agrees with
precomposition to any other ordinary P103 anchor of the same trivial module. -/
def NativeComparison.agreesWithOrdinary {A : NormalizedBar.Comparison.{u,v,a} k G}
    {B : LeftResolution k[G] (trivial k G)} {hB : B.IsProjective}
    {bar : B.complex = originalBar k G}
    (E : NativeComparison.{u,v,a,p} k G A B hB bar) : Prop :=
  ∀ (P : Resolution.{u,v,p} k G) (B' : LeftResolution k[G] (trivial k G))
    (hB' : B'.IsProjective) (g : LinearChainMap B'.complex P.complex),
    OriginalLift k G (Q := AugmentedResolution.ofP103 B' hB') g →
    ∀ (M : Coeff.{u,v,a} k G) n (x : Cohomology k G P M n),
      E.ext M n (E.value k G P M n x) =
        E.p103.equiv (trivial k G) M B' hB' n
          ((homMap k G (Q := AugmentedResolution.ofP103 B' hB') (N := M) g
            LinearMap.id).homologyMap n x)

/-- The calculation on the given degree-zero cycle uses the actual derived unit
and evaluates the uniquely descended map on the original scalar 1. -/
def NativeComparison.agreesAtDegreeZero {A : NormalizedBar.Comparison.{u,v,a} k G}
    {B : LeftResolution k[G] (trivial k G)} {hB : B.IsProjective}
    {bar : B.complex = originalBar k G}
    (E : NativeComparison.{u,v,a,p} k G A B hB bar) : Prop :=
  ∀ (M : Coeff.{u,v,a} k G) (P : Resolution.{u,v,p} k G)
    (z : cycles (homComplex P.complex M) 0) (f : OriginalHom k G M),
    f.comp P.ε = z.val →
    ∃ m : invariants k G M,
      m.val = f (trivialElement k G 1) ∧
      E.value k G P M 0 (homologyClass _ 0 z) =
        ((NativeTransport.degreeZeroUnit.{u,v,a} k G).app ((lift k G).obj M)).hom
          (IndependentResolution.liftedInvariant k G M m)

/-- Both native computations are transported to one normalized projective
computation through the same original bar quotient. The mixed coefficient map
on original cochains and on the common derived values is the given map. -/
def computationType : Prop :=
  ∃ (B : LeftResolution k[G] (trivial k G)) (hB : B.IsProjective)
    (bar : B.complex = originalBar k G)
    (A : NormalizedBar.Comparison.{u,v,a} k G)
    (A' : NormalizedBar.Comparison.{u,v,b} k G)
    (C : NormalizedBar.Comparison.{u,v,max a b s} k G)
    (T : NativeTransport.Comparison.{u,v,a,max b s} k G)
    (T' : NativeTransport.Comparison.{u,v,b,max a s} k G)
    (E : NativeComparison.{u,v,a,p} k G A B hB bar)
    (E' : NativeComparison.{u,v,b,q} k G A' B hB bar)
    (J : ∀ M : Coeff.{u,v,a} k G, BarComparison.{u,v,a,max a b s} k G B bar M
      (commonCoefficient.{u,v,a,max b s} k G M) (commonCoefficientIso.{u,v,a,max b s} k G M))
    (J' : ∀ N : Coeff.{u,v,b} k G, BarComparison.{u,v,b,max a b s} k G B bar N
      (commonCoefficient.{u,v,b,max a s} k G N) (commonCoefficientIso.{u,v,b,max a s} k G N)),
    (∀ c : Fin 1 → G, B.ε (bar.symm ▸ basisElement k G 0 c) = trivialElement k G 1) ∧
    E.agreesWithOrdinary k G ∧ E'.agreesWithOrdinary k G ∧
    E.agreesAtDegreeZero k G ∧ E'.agreesAtDegreeZero k G ∧
    (∀ (M : Coeff.{u,v,a} k G) (P : Resolution.{u,v,p} k G) n (x : Cohomology k G P M n),
      ((C.iso n).hom.app (commonCoefficient.{u,v,a,max b s} k G M)).hom
        (T.onOriginal k G M n (E.value k G P M n x)) =
      (J M).classes n (E.original.equiv P M n x)) ∧
    (∀ (N : Coeff.{u,v,b} k G) (Q : Resolution.{u,v,q} k G) n (x : Cohomology k G Q N n),
      ((C.iso n).hom.app (commonCoefficient.{u,v,b,max a s} k G N)).hom
        (T'.onOriginal k G N n (E'.value k G Q N n x)) =
      (J' N).classes n (E'.original.equiv Q N n x)) ∧
    ∀ (M : Coeff.{u,v,a} k G) (N : Coeff.{u,v,b} k G)
      (P : Resolution.{u,v,p} k G) (Q : Resolution.{u,v,q} k G)
      (f : M →ₗ[k[G]] N) (g : LinearChainMap Q.complex P.complex),
      OriginalLift k G g → ∀ n (x : Cohomology k G P M n),
      T'.onOriginal k G N n
        (E'.value k G Q N n ((homMap k G g f).homologyMap n x)) =
      (((GroupDerivedInvariants.cohomology.{u,v,max a b s} k G n).map
          (commonCoefficientMap.{u,v,a,b,s} k G f)).hom
        (T.onOriginal k G M n (E.value k G P M n x)))

def computationExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G], computationType.{u,v,a,b,p,q,s} k G

end Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.MixedProjective
