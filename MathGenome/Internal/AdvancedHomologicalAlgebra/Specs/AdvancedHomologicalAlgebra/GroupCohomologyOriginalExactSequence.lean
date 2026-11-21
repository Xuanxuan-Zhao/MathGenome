import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GroupLowDegreesAndCoefficients
import Mathlib.Algebra.Homology.ConcreteCategory

/-! HA-A03 on the original coefficient modules. The two coefficient maps in the
sequence are applied to every original tuple. The ambient module category is used
for the right-derived functor, while the original cochain classes are retained. -/

noncomputable section
set_option linter.checkUnivs false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalExactSequence

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra ModuleCat.Algebra
open GroupCohomologyOriginalCoefficients UniversalDeltaFunctors

universe u v w

variable (k : Type u) (G : Type v) [CommRing k] [Group G]

abbrev act (M : Coeff.{u,v,w} k G) (g : G) (m : M) :=
  MonoidAlgebra.single g (1 : k) • m

/-- Crossed homomorphisms into the original carrier. -/
def crossed (M : Coeff.{u,v,w} k G) : Submodule k (G → M) where
  carrier := {f | ∀ g h : G, f (g*h) = f g + act k G M g (f h)}
  zero_mem' := by intro g h; simp
  add_mem' {f f'} hf hf' := by
    intro g h
    change f (g*h) + f' (g*h) = (f g + f' g) + act k G M g (f h + f' h)
    rw [hf g h, hf' g h]
    simp only [act, smul_add]
    abel
  smul_mem' c f hf := by
    intro g h
    change c • f (g*h) = c • f g + act k G M g (c • f h)
    rw [hf g h]
    simp only [act, smul_add, smul_comm (MonoidAlgebra.single g (1 : k)) c]

/-- The principal crossed homomorphism attached to an original element. -/
def principal (M : Coeff.{u,v,w} k G) : M →ₗ[k] crossed k G M where
  toFun m := ⟨fun g => act k G M g m - m, by
    intro g h
    change act k G M (g*h) m - m =
      act k G M g m - m + act k G M g (act k G M h m - m)
    simp only [act, smul_sub, smul_smul, MonoidAlgebra.single_mul_single, one_mul]
    abel⟩
  map_add' m m' := by
    apply Subtype.ext
    funext g
    change act k G M g (m + m') - (m + m') =
      (act k G M g m - m) + (act k G M g m' - m')
    simp only [act, smul_add]
    abel
  map_smul' c m := by
    apply Subtype.ext
    funext g
    change act k G M g (c • m) - c • m = c • (act k G M g m - m)
    simp only [act, smul_sub, smul_comm (MonoidAlgebra.single g (1 : k)) c]

abbrev boundaries (M : Coeff.{u,v,w} k G) := (principal k G M).range

abbrev quotient (M : Coeff.{u,v,w} k G) :=
  crossed k G M ⧸ boundaries k G M

def crossedMap {M N : Coeff.{u,v,w} k G} (a : M ⟶ N) :
    crossed k G M →ₗ[k] crossed k G N where
  toFun f := ⟨fun g => a.hom (f.val g), by
    intro g h
    change a.hom (f.val (g*h)) = _
    rw [show f.val (g*h) = _ from f.property g h, map_add, act, act, map_smul]⟩
  map_add' _ _ := Subtype.ext (funext fun _ => map_add a.hom _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => a.hom.map_smul_of_tower _ _)

def quotientMap {M N : Coeff.{u,v,w} k G} (a : M ⟶ N) :
    ModuleCat.of k (quotient k G M) ⟶ ModuleCat.of k (quotient k G N) :=
  ModuleCat.ofHom <| (boundaries k G M).mapQ (boundaries k G N) (crossedMap k G a) (by
    rintro _ ⟨m, rfl⟩
    refine ⟨a.hom m, Subtype.ext (funext fun g => ?_)⟩
    change act k G N g (a.hom m) - a.hom m = a.hom (act k G M g m - m)
    rw [act, act, map_sub, map_smul])

abbrev raw (h : SquareZero.{u,v,w} k G) := rawFunctor k G h
abbrev complex (h : SquareZero.{u,v,w} k G) (M : Coeff.{u,v,w} k G) := (raw k G h).obj M
abbrev lifted (h : SquareZero.{u,v,w} k G) := rawLifted k G h

instance rawAdditive (h : SquareZero.{u,v,w} k G) : (raw k G h).Additive where
  map_add := by intros; ext n f; rfl

abbrev RawExact (h : SquareZero.{u,v,w} k G) :=
  ∀ {S : ShortComplex (Coeff.{u,v,w} k G)}, S.ShortExact → (S.map (raw k G h)).ShortExact

abbrev AmbientExact :=
  ∀ {S : ShortComplex (Coeff.{u,v,w} k G)}, S.ShortExact → (S.map (ambientBar k G)).ShortExact

/-- Both coefficient maps are the original maps on every tuple, even before applying
the carrier lift to the complex. -/
def rawExactType : Prop :=
  ∀ h : SquareZero.{u,v,w} k G, RawExact k G h ∧
    ∀ (M N : Coeff.{u,v,w} k G) (a : M ⟶ N) n (f : TupleCochain k G M n) g,
      (((raw k G h).map a).f n).hom f g = a.hom (f g)

/-- The comparison and its inverse evaluated on every normalized bar generator. -/
def Pointwise {h : SquareZero.{u,v,w} k G} (e : lifted k G h ≅ ambientBar.{u,v,w} k G) : Prop :=
  (∀ (M : Coeff.{u,v,w} k G) n (f : TupleCochain k G M n) (g : Fin n → G),
    (((e.hom.app M).f n).hom (ULift.up f) :
      GroupBar.Large.B.{u,v,w} k G n ⟶
        GroupCochainComparison.Large.representation k G ((lift k G).obj M)).hom
        (GroupBar.Large.single k G (Fin.partialProd g) 1) = ULift.up (f g)) ∧
  (∀ (M : Coeff.{u,v,w} k G) n (φ : GroupBar.Large.B.{u,v,w} k G n ⟶
      GroupCochainComparison.Large.representation k G ((lift k G).obj M)) (g : Fin n → G),
      (((e.inv.app M).f n).hom φ).down g =
        (φ.hom (GroupBar.Large.single k G (Fin.partialProd g) 1)).down)

def SequenceComparison {h : SquareZero.{u,v,w} k G}
    (e : lifted k G h ≅ ambientBar.{u,v,w} k G) : Prop :=
  ∀ {S : ShortComplex (Coeff.{u,v,w} k G)} (_hS : S.ShortExact),
    (S.map (lift k G)).ShortExact ∧ (S.map (lifted k G h)).ShortExact ∧
    (S.map (ambientBar k G)).ShortExact ∧
    ∃ i : S.map (lifted k G h) ≅ (S.map (lift k G)).map
        (GroupCochainComparison.Large.homogeneousFunctor k G),
      i.hom.τ₁ = e.hom.app S.X₁ ∧ i.hom.τ₂ = e.hom.app S.X₂ ∧ i.hom.τ₃ = e.hom.app S.X₃

def sequenceComparisonType : Prop :=
  ∀ h : SquareZero.{u,v,w} k G,
    ∃ e : lifted k G h ≅ ambientBar.{u,v,w} k G, Pointwise k G e ∧ SequenceComparison k G e

abbrev rawBoundary {h : SquareZero.{u,v,w} k G}
    {S : ShortComplex (Coeff.{u,v,w} k G)} (hs : (S.map (raw k G h)).ShortExact) (n : ℕ) :=
  hs.δ n (n+1) rfl

def rawSystem {h : SquareZero.{u,v,w} k G} (exact : RawExact k G h) :
    CohomologicalSystem (Coeff.{u,v,w} k G) (ModuleCat.{max v w} k) where
  value := rawCohomology k G h
  δ hs := rawBoundary k G (exact hs)

local instance canonicalDerived (A : Type*) [Category A] [Abelian A] :
    HasDerivedCategory A := HasDerivedCategory.standard A

abbrev derivedBoundary {S : ShortComplex (Coeff.{u,v,w} k G)}
    (hS : S.ShortExact) (n : ℕ) :=
  ClassicalDerivedValues.rightBoundary (GroupDerivedInvariants.invariantsFunctor k G)
    (hS.map_of_exact (lift k G)) n

def derivedSystem : CohomologicalSystem (Coeff.{u,v,w} k G) (ModuleCat.{max u v w} k) where
  value := derived k G
  δ := derivedBoundary k G

def longExactType : Prop :=
  (∀ (h : SquareZero.{u,v,w} k G) (exact : RawExact k G h),
      IsCohomological (rawSystem k G exact)) ∧
    IsCohomological (derivedSystem.{u,v,w} k G)

abbrev classOf (h : SquareZero.{u,v,w} k G) (M : Coeff.{u,v,w} k G) (n : ℕ)
    (z : TupleCochain k G M n) (hz : differential k G M n z = 0) :
    (rawCohomology k G h n).obj M :=
  let K := complex k G h M
  K.homologyπ n (K.cyclesMk z (n+1) (by simp) (by
    change (K.d n (n+1)).hom z = 0
    simpa only [K, raw, rawFunctor, complex, rawComplex, CochainComplex.of_d, ModuleCat.hom_ofHom] using hz))

/-- Every class has a cocycle representative. Every cocycle has lifts and
every such pair of lifts gives the indicated class of the differential.
In particular the formula is independent of all choices. -/
def liftedBoundaryType : Prop :=
  ∀ (h : SquareZero.{u,v,w} k G) (exact : RawExact k G h)
    {S : ShortComplex (Coeff.{u,v,w} k G)} (hS : S.ShortExact) (n : ℕ),
    (∀ a : (rawCohomology k G h n).obj S.X₃,
      ∃ (z : TupleCochain k G S.X₃ n) (hz : differential k G S.X₃ n z = 0),
        classOf k G h S.X₃ n z hz = a) ∧
    ∀ (z : TupleCochain k G S.X₃ n) (hz : differential k G S.X₃ n z = 0),
      (∃ (y : TupleCochain k G S.X₂ n) (x : TupleCochain k G S.X₁ (n+1)),
        (∀ g, S.g.hom (y g) = z g) ∧ (∀ g, S.f.hom (x g) = differential k G S.X₂ n y g)) ∧
      ∀ (y : TupleCochain k G S.X₂ n) (x : TupleCochain k G S.X₁ (n+1)),
        (∀ g, S.g.hom (y g) = z g) → (∀ g, S.f.hom (x g) = differential k G S.X₂ n y g) →
        ∃ hx : differential k G S.X₁ (n+1) x = 0,
          (rawBoundary k G (exact hS) n).hom (classOf k G h S.X₃ n z hz) =
            classOf k G h S.X₁ (n+1) x hx

def zeroIdentification {h : SquareZero.{u,v,w} k G}
    (e : invariantsFunctor k G ⋙ rawInvariantLift.{u,v,w} k ≅ rawCohomology k G h 0) : Prop :=
  ∀ (M : Coeff.{u,v,w} k G) (m : invariants k G M),
    ∃ hz : differential k G M 0 (fun _ => m.val) = 0,
      (e.hom.app M).hom (ULift.up m) = classOf k G h M 0 (fun _ => m.val) hz

def oneIdentification {h : SquareZero.{u,v,w} k G}
    (e : ∀ M : Coeff.{u,v,w} k G, (rawCohomology k G h 1).obj M ≅ ModuleCat.of k (quotient k G M)) :
    Prop :=
  (∀ (M N : Coeff.{u,v,w} k G) (a : M ⟶ N),
    (rawCohomology k G h 1).map a ≫ (e N).hom = (e M).hom ≫ quotientMap k G a) ∧
  (∀ (M : Coeff.{u,v,w} k G) (z : TupleCochain k G M 1) (hz : differential k G M 1 z = 0),
    ∃ f : crossed k G M, (∀ g, f.val g = z (fun _ => g)) ∧
      (e M).hom (classOf k G h M 1 z hz) = (boundaries k G M).mkQ f)

/-- Remove the carrier lifts to land in the actual fixed submodule. -/
def degreeZeroEquiv {h : SquareZero.{u,v,w} k G}
    (e : derived k G 0 ≅ rawCohomology k G h 0 ⋙ scalarLift.{u,v,w} k)
    (e₀ : invariantsFunctor k G ⋙ rawInvariantLift.{u,v,w} k ≅ rawCohomology k G h 0)
    (M : Coeff.{u,v,w} k G) : (derived k G 0).obj M ≃ₗ[k] invariants k G M :=
  (e.app M).toLinearEquiv.trans
    (ULift.moduleEquiv.trans ((e₀.app M).symm.toLinearEquiv.trans ULift.moduleEquiv))

/-- Remove the carrier lift to land in the actual crossed-homomorphism quotient. -/
def degreeOneEquiv {h : SquareZero.{u,v,w} k G}
    (e : derived k G 1 ≅ rawCohomology k G h 1 ⋙ scalarLift.{u,v,w} k)
    (M : Coeff.{u,v,w} k G)
    (e₁ : (rawCohomology k G h 1).obj M ≅ ModuleCat.of k (quotient k G M)) :
    (derived k G 1).obj M ≃ₗ[k] quotient k G M :=
  (e.app M).toLinearEquiv.trans (ULift.moduleEquiv.trans e₁.toLinearEquiv)

def OriginalLowDegrees {h : SquareZero.{u,v,w} k G}
    (e : ∀ n, derived.{u,v,w} k G n ≅ rawCohomology k G h n ⋙ scalarLift.{u,v,w} k)
    (e₀ : invariantsFunctor k G ⋙ rawInvariantLift.{u,v,w} k ≅ rawCohomology k G h 0)
    (e₁ : ∀ M : Coeff.{u,v,w} k G,
      (rawCohomology k G h 1).obj M ≅ ModuleCat.of k (quotient k G M)) : Prop :=
  (∀ (M N : Coeff.{u,v,w} k G) (b : M ⟶ N) (x : (derived k G 0).obj M),
    degreeZeroEquiv k G (e 0) e₀ N (((derived k G 0).map b).hom x) =
      ((invariantsFunctor k G).map b).hom (degreeZeroEquiv k G (e 0) e₀ M x)) ∧
  (∀ (M N : Coeff.{u,v,w} k G) (b : M ⟶ N) (x : (derived k G 1).obj M),
    degreeOneEquiv k G (e 1) N (e₁ N) (((derived k G 1).map b).hom x) =
      (quotientMap k G b).hom (degreeOneEquiv k G (e 1) M (e₁ M) x)) ∧
  (∀ (M : Coeff.{u,v,w} k G) (z : TupleCochain k G M 1) (hz : differential k G M 1 z = 0),
    ∃ f : crossed k G M, (∀ g, f.val g = z (fun _ => g)) ∧
      degreeOneEquiv k G (e 1) M (e₁ M)
        (((e 1).inv.app M).hom (ULift.up (classOf k G h M 1 z hz))) =
          (boundaries k G M).mkQ f)

/-- The sequence comparison uses the ambient boundary normalized at invariants.
Its map to the original cochain classes factors through the pointwise cochain
comparison and the canonical exact lift of scalar homology. -/
def DerivedAgreement {h : SquareZero.{u,v,w} k G} (exact : RawExact k G h)
    (ae : AmbientExact.{u,v,w} k G) (b : lifted k G h ≅ ambientBar.{u,v,w} k G) : Prop :=
  ∃ (a : ∀ n, derived.{u,v,w} k G n ≅ ambientBarCohomology k G n)
    (e : ∀ n, derived.{u,v,w} k G n ≅ rawCohomology k G h n ⋙ scalarLift.{u,v,w} k)
    (e₀ : invariantsFunctor k G ⋙ rawInvariantLift.{u,v,w} k ≅ rawCohomology k G h 0)
    (e₁ : ∀ M : Coeff.{u,v,w} k G,
      (rawCohomology k G h 1).obj M ≅ ModuleCat.of k (quotient k G M)),
    zeroIdentification k G e₀ ∧ oneIdentification k G e₁ ∧ OriginalLowDegrees k G e e₀ e₁ ∧
    (∀ n (M : Coeff.{u,v,w} k G),
      (e n).hom.app M = (a n).hom.app M ≫ HomologicalComplex.homologyMap (b.inv.app M) n ≫
        (((complex k G h M).sc n).mapHomologyIso (scalarLift.{u,v,w} k)).hom) ∧
    (∀ (M : Coeff.{u,v,w} k G) (m : (GroupDerivedInvariants.invariantsFunctor k G).obj
        ((lift k G).obj M)),
      ((e 0).hom.app M).hom
        ((ClassicalDerivedValues.rightDegreeZeroUnit (GroupDerivedInvariants.invariantsFunctor k G)
          |>.app ((lift k G).obj M)).hom m) =
        ULift.up ((e₀.hom.app M).hom (ULift.up
          (⟨m.val.down, fun g => congrArg ULift.down (m.property g)⟩ : invariants k G M)))) ∧
    ∀ {S : ShortComplex (Coeff.{u,v,w} k G)} (hS : S.ShortExact) (n : ℕ),
      (derivedBoundary k G hS n ≫ (a (n+1)).hom.app S.X₁ =
        (a n).hom.app S.X₃ ≫ (ae hS).δ n (n+1) rfl) ∧
      (derivedBoundary k G hS n ≫ (e (n+1)).hom.app S.X₁ =
        (e n).hom.app S.X₃ ≫ (scalarLift.{u,v,w} k).map (rawBoundary k G (exact hS) n))

def derivedAgreementType : Prop :=
  ∃ (h : SquareZero.{u,v,w} k G) (hex : RawExact k G h) (ae : AmbientExact.{u,v,w} k G)
    (b : lifted k G h ≅ ambientBar.{u,v,w} k G),
    Pointwise k G b ∧ SequenceComparison k G b ∧ DerivedAgreement k G hex ae b

def rawExactExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G], rawExactType.{u,v,w} k G

def sequenceComparisonExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G], sequenceComparisonType.{u,v,w} k G

def longExactExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G], longExactType.{u,v,w} k G

def liftedBoundaryExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G], liftedBoundaryType.{u,v,w} k G

def derivedAgreementExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G], derivedAgreementType.{u,v,w} k G

end Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalExactSequence

namespace Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalExactSequence.Mixed

open CategoryTheory
open GroupCohomologyOriginalCoefficients
open scoped MonoidAlgebra ModuleCat.Algebra

universe u v a b c a' b' c' s

variable (k : Type u) (G : Type v) [CommRing k] [Group G]
variable {M : Coeff.{u,v,a} k G} {N : Coeff.{u,v,b} k G} {P : Coeff.{u,v,c} k G}

/-- Exactness on the three given carriers over the same group algebra. -/
structure ShortExact (i : M →ₗ[k[G]] N) (p : N →ₗ[k[G]] P) : Prop where
  injective : Function.Injective i
  exact : Function.Exact i p
  surjective : Function.Surjective p

/-- The original cochain map is pointwise postcomposition. -/
def post (f : M →ₗ[k[G]] N) (n : ℕ) : TupleCochain k G M n →ₗ[k] TupleCochain k G N n :=
  LinearMap.pi fun g => (f.restrictScalars k).comp (LinearMap.proj g)

theorem post_differential (f : M →ₗ[k[G]] N) (n : ℕ) (z : TupleCochain k G M n) :
    differential k G N n (post k G f n z) =
      post k G f (n+1) (differential k G M n z) := by
  funext g
  change differential k G N n (fun t => f (z t)) g = f (differential k G M n z g)
  simp only [differential_apply, map_add, map_sum, LinearMap.map_smul,
    LinearMap.map_smul_of_tower]

abbrev H {M : Coeff.{u,v,a} k G} (h : SquareZero.{u,v,a} k G) (n : ℕ) :=
  (rawCohomology k G h n).obj M

variable {hM : SquareZero.{u,v,a} k G} {hN : SquareZero.{u,v,b} k G}
  {hP : SquareZero.{u,v,c} k G}

/-- Each induced map is specified on every class of an original cocycle. -/
structure InducedMap (hM : SquareZero.{u,v,a} k G) (hN : SquareZero.{u,v,b} k G)
    (f : M →ₗ[k[G]] N) where
  hom : ∀ n, H k G (M := M) hM n →ₗ[k] H k G (M := N) hN n
  on_class : ∀ n (z : TupleCochain k G M n) (hz : differential k G M n z = 0),
    hom n (classOf k G hM M n z hz) =
      classOf k G hN N n (post k G f n z) (by rw [post_differential, hz, map_zero])

def rawExactType (i : M →ₗ[k[G]] N) (p : N →ₗ[k[G]] P) : Prop :=
  ∀ n, Function.Injective (post k G i n) ∧ Function.Exact (post k G i n) (post k G p n) ∧
    Function.Surjective (post k G p n)

def HasRepresentatives (M : Coeff.{u,v,a} k G) (h : SquareZero.{u,v,a} k G) : Prop :=
  ∀ n (x : H k G (M := M) h n), ∃ (z : TupleCochain k G M n)
    (hz : differential k G M n z = 0), classOf k G h M n z hz = x

def Lifts (i : M →ₗ[k[G]] N) (p : N →ₗ[k[G]] P) (n : ℕ)
    (z : TupleCochain k G P n) (y : TupleCochain k G N n) (x : TupleCochain k G M (n+1)) : Prop :=
  (∀ g, p (y g) = z g) ∧ (∀ g, i (x g) = differential k G N n y g)

/-- The original map of fixed elements under a change of coefficients. -/
def invariantsPost (f : M →ₗ[k[G]] N) : invariants k G M →ₗ[k] invariants k G N where
  toFun m := ⟨f m.val, fun g => by rw [← f.map_smul, m.property g]⟩
  map_add' _ _ := Subtype.ext (f.map_add _ _)
  map_smul' _ _ := Subtype.ext (f.map_smul_of_tower _ _)

/-- Apply the original coefficient map to every value of a crossed homomorphism. -/
def crossedPost (f : M →ₗ[k[G]] N) : crossed k G M →ₗ[k] crossed k G N where
  toFun z := ⟨fun g => f (z.val g), fun g h => by
    change f (z.val (g*h)) = _
    rw [show z.val (g*h) = _ from z.property g h, map_add, act, act, map_smul]⟩
  map_add' _ _ := Subtype.ext (funext fun _ => f.map_add _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => f.map_smul_of_tower _ _)

def quotientPost (f : M →ₗ[k[G]] N) : quotient k G M →ₗ[k] quotient k G N :=
  (boundaries k G M).mapQ (boundaries k G N) (crossedPost k G f) (by
    rintro _ ⟨m, rfl⟩
    refine ⟨f m, Subtype.ext (funext fun g => ?_)⟩
    change act k G N g (f m) - f m = f (act k G M g m - m)
    rw [act, act, map_sub, map_smul])

/-- Low degrees identified by the values of original cocycles. -/
structure LowDegrees (hM : SquareZero.{u,v,a} k G) (M : Coeff.{u,v,a} k G) where
  zero : invariants k G M ≃ₗ[k] H k G (M := M) hM 0
  one : H k G (M := M) hM 1 ≃ₗ[k] quotient k G M
  on_zero : ∀ (m : invariants k G M),
    ∃ hz : differential k G M 0 (fun _ => m.val) = 0,
      zero m = classOf k G hM M 0 (fun _ => m.val) hz
  on_one : ∀ (z : TupleCochain k G M 1) (hz : differential k G M 1 z = 0),
    ∃ t : crossed k G M, (∀ g, t.val g = z (fun _ => g)) ∧
      one (classOf k G hM M 1 z hz) = (boundaries k G M).mkQ t

def lowDegreesType (hM : SquareZero.{u,v,a} k G) (hN : SquareZero.{u,v,b} k G) : Prop :=
  ∃ (eM : LowDegrees k G hM M) (eN : LowDegrees k G hN N),
    ∀ (f : M →ₗ[k[G]] N), ∃ F : InducedMap k G hM hN f,
      (∀ x, F.hom 0 (eM.zero x) = eN.zero (invariantsPost k G f x)) ∧
      ∀ x, eN.one (F.hom 1 x) = quotientPost k G f (eM.one x)

/-- The positive connecting map on the original cohomology classes. -/
structure Sequence (hM : SquareZero.{u,v,a} k G) (hN : SquareZero.{u,v,b} k G)
    (hP : SquareZero.{u,v,c} k G) (i : M →ₗ[k[G]] N) (p : N →ₗ[k[G]] P) where
  inclusion : InducedMap k G hM hN i
  projection : InducedMap k G hN hP p
  boundary : ∀ n, H k G (M := P) hP n →ₗ[k] H k G (M := M) hM (n+1)
  initial : Function.Injective (inclusion.hom 0)
  exactness : ∀ n, Function.Exact (inclusion.hom n) (projection.hom n) ∧
    Function.Exact (projection.hom n) (boundary n) ∧ Function.Exact (boundary n) (inclusion.hom (n+1))
  lift_boundary : ∀ n (z : TupleCochain k G P n) (hz : differential k G P n z = 0)
    (y : TupleCochain k G N n) (x : TupleCochain k G M (n+1)),
    Lifts k G i p n z y x → ∃ hx : differential k G M (n+1) x = 0,
      boundary n (classOf k G hP P n z hz) = classOf k G hM M (n+1) x hx

def longExactType (hM : SquareZero.{u,v,a} k G) (hN : SquareZero.{u,v,b} k G)
    (hP : SquareZero.{u,v,c} k G) : Prop :=
  HasRepresentatives k G M hM ∧ HasRepresentatives k G N hN ∧ HasRepresentatives k G P hP ∧
    ∀ (i : M →ₗ[k[G]] N) (p : N →ₗ[k[G]] P), ShortExact k G i p →
      rawExactType k G i p ∧ Nonempty (Sequence k G hM hN hP i p) ∧
      ∀ n (z : TupleCochain k G P n), differential k G P n z = 0 →
        ∃ (y : TupleCochain k G N n) (x : TupleCochain k G M (n+1)), Lifts k G i p n z y x

/-- The maps of the two original cohomology sequences, with six independent carriers. -/
def naturalityType {M' : Coeff.{u,v,a'} k G} {N' : Coeff.{u,v,b'} k G} {P' : Coeff.{u,v,c'} k G}
    (hM' : SquareZero.{u,v,a'} k G) (hN' : SquareZero.{u,v,b'} k G)
    (hP' : SquareZero.{u,v,c'} k G) : Prop :=
  ∀ {i : M →ₗ[k[G]] N} {p : N →ₗ[k[G]] P} {i' : M' →ₗ[k[G]] N'} {p' : N' →ₗ[k[G]] P'}
    (α : M →ₗ[k[G]] M') (β : N →ₗ[k[G]] N') (γ : P →ₗ[k[G]] P'),
    β.comp i = i'.comp α → γ.comp p = p'.comp β →
    ShortExact k G i p → ShortExact k G i' p' →
    ∀ (S : Sequence k G hM hN hP i p) (T : Sequence k G hM' hN' hP' i' p'),
      ∃ (A : InducedMap k G hM hM' α) (B : InducedMap k G hN hN' β)
        (C : InducedMap k G hP hP' γ),
        ∀ n, (B.hom n).comp (S.inclusion.hom n) = (T.inclusion.hom n).comp (A.hom n) ∧
          (C.hom n).comp (S.projection.hom n) = (T.projection.hom n).comp (B.hom n) ∧
          (A.hom (n+1)).comp (S.boundary n) = (T.boundary n).comp (C.hom n)

/-- Lift just the carrier and retain the same group algebra and action. -/
abbrev commonCoeff (M : Coeff.{u,v,a} k G) : Coeff.{u,v,max a s} k G :=
  ModuleCat.of k[G] (ULift.{s} M)

abbrev down (M : Coeff.{u,v,a} k G) : commonCoeff.{u,v,a,s} k G M ≃ₗ[k[G]] M :=
  ULift.moduleEquiv

abbrev commonSequence {i : M →ₗ[k[G]] N} {p : N →ₗ[k[G]] P} (h : ShortExact k G i p) :
    ShortComplex (GroupDerivedInvariants.GroupModule.{u,v,max a b c s} k G) :=
  ModuleCat.shortComplexOfConj (down.{u,v,a,max u v a b c s} k G M)
    (down.{u,v,b,max u v a b c s} k G N) (down.{u,v,c,max u v a b c s} k G P)
    i p h.exact.linearMap_comp_eq_zero

abbrev toCommonScalars :=
  ModuleCat.uliftFunctor.{max u v a s,max v a} k

abbrev commonRaw (hM : SquareZero.{u,v,a} k G) (M : Coeff.{u,v,a} k G) :=
  ((toCommonScalars.{u,v,a,s} k).mapHomologicalComplex (.up ℕ)).obj (rawComplex k G hM M)

abbrev ambient := GroupCochainComparison.Large.homogeneousFunctor.{u,v,s} k G

abbrev commonBar (M : Coeff.{u,v,a} k G) :=
  (ambient.{u,v,max a s} k G).obj (commonCoeff.{u,v,a,max u v a s} k G M)

abbrev ambientCoordinates (M : Coeff.{u,v,a} k G) (n : ℕ) (φ : (commonBar.{u,v,a,s} k G M).X n)
    (g : Fin n → G) : commonCoeff.{u,v,a,max u v a s} k G M :=
  φ.hom (GroupBar.Large.single k G (Fin.partialProd g) 1)

/-- The scalar lift of the original complex is identified with the homogeneous
bar complex by the original normalized generators, in both directions. -/
structure BarComparison (hM : SquareZero.{u,v,a} k G) (M : Coeff.{u,v,a} k G) where
  iso : commonRaw.{u,v,a,s} k G hM M ≅ commonBar.{u,v,a,s} k G M
  forward : ∀ n (z : TupleCochain k G M n) g,
    ambientCoordinates k G M n ((iso.hom.f n).hom (ULift.up z)) g = ULift.up (z g)
  backward : ∀ n (φ : (commonBar.{u,v,a,s} k G M).X n) g,
    ((iso.inv.f n).hom φ).down g = (ambientCoordinates k G M n φ g).down

variable {k G} in
/-- The induced cohomology identification uses exactness of the same scalar
lift and the map on homology of the specified bar comparison. -/
def BarComparison.homology (e : BarComparison.{u,v,a,s} k G hM M) (n : ℕ) :
    H k G (M := M) hM n ≃ₗ[k] (commonBar.{u,v,a,s} k G M).homology n :=
  ULift.moduleEquiv.symm.trans
    ((((rawComplex k G hM M).sc n).mapHomologyIso (toCommonScalars.{u,v,a,s} k)).symm.toLinearEquiv.trans
      (((HomologicalComplex.homologyFunctor _ (.up ℕ) n).mapIso e.iso).toLinearEquiv))

/-- Lift the actual postcomposition maps to the common scalar category. -/
def commonPost (f : M →ₗ[k[G]] N) :
    commonRaw.{u,v,a,max a b s} k G hM M ⟶ commonRaw.{u,v,b,max a b s} k G hN N where
  f n := ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp
    ((post k G f n).comp ULift.moduleEquiv.toLinearMap))
  comm' n j h := by
    obtain rfl : j = n + 1 := h.symm
    simp only [commonRaw, Functor.mapHomologicalComplex_obj_d, rawComplex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change ULift.up (differential k G N n (post k G f n z.down)) =
      ULift.up (post k G f (n+1) (differential k G M n z.down))
    rw [post_differential]

def commonRawSequence {i : M →ₗ[k[G]] N} {p : N →ₗ[k[G]] P} (h : ShortExact k G i p) :
    ShortComplex (CochainComplex (ModuleCat.{max u v a b c s} k) ℕ) :=
  ShortComplex.mk (commonPost.{u,v,a,b,max c s} k G (hM := hM) (hN := hN) i)
    (commonPost.{u,v,b,c,max a s} k G (hM := hN) (hN := hP) p) (by
      ext n z
      change ULift.up (fun g => p (i (z.down g))) = ULift.up 0
      exact congrArg ULift.up (funext fun g => h.exact.apply_apply_eq_zero (z.down g)))

/-- The termwise comparison identifies the two specified exact cochain sequences. -/
structure SequenceComparison (hM : SquareZero.{u,v,a} k G) (hN : SquareZero.{u,v,b} k G)
    (hP : SquareZero.{u,v,c} k G) {i : M →ₗ[k[G]] N} {p : N →ₗ[k[G]] P}
    (h : ShortExact k G i p) where
  coefficient_exact : (commonSequence.{u,v,a,b,c,s} k G h).ShortExact
  bar_exact : ((commonSequence.{u,v,a,b,c,s} k G h).map
    (ambient.{u,v,max a b c s} k G)).ShortExact
  raw_exact : (commonRawSequence.{u,v,a,b,c,s} k G (hM := hM) (hN := hN) (hP := hP) h).ShortExact
  first : BarComparison.{u,v,a,max a b c s} k G hM M
  second : BarComparison.{u,v,b,max a b c s} k G hN N
  third : BarComparison.{u,v,c,max a b c s} k G hP P
  iso : commonRawSequence.{u,v,a,b,c,s} k G (hM := hM) (hN := hN) (hP := hP) h ≅
    (commonSequence.{u,v,a,b,c,s} k G h).map (ambient.{u,v,max a b c s} k G)
  on_first : iso.hom.τ₁ = first.iso.hom
  on_second : iso.hom.τ₂ = second.iso.hom
  on_third : iso.hom.τ₃ = third.iso.hom

def sequenceComparisonType (hM : SquareZero.{u,v,a} k G) (hN : SquareZero.{u,v,b} k G)
    (hP : SquareZero.{u,v,c} k G) : Prop :=
  ∀ {i : M →ₗ[k[G]] N} {p : N →ₗ[k[G]] P} (h : ShortExact k G i p),
    Nonempty (SequenceComparison.{u,v,a,b,c,s} k G hM hN hP h)

local instance canonicalDerived (A : Type*) [Category A] [Abelian A] :
    HasDerivedCategory A := HasDerivedCategory.standard A

abbrev ambientH := GroupLowDegreesAndCoefficients.Large.cohomology.{u,v,s} k G

abbrev derivedH := GroupDerivedInvariants.cohomology.{u,v,s} k G

abbrev invariantUnit := ClassicalDerivedValues.rightDegreeZeroUnit
  (GroupDerivedInvariants.invariantsFunctor.{u,v,s} k G)

/-- The comparison is natural in the common coefficient category, normalized
on the actual degree-zero unit and compatible with its derived boundary. -/
def AmbientAgreement (e : ∀ n, derivedH.{u,v,s} k G n ≅ ambientH.{u,v,s} k G n) : Prop :=
  (∀ (B : GroupDerivedInvariants.GroupModule.{u,v,s} k G)
    (m : GroupDerivedInvariants.invariants k G B),
    ∃ (z : ((ambient.{u,v,s} k G).obj B).X 0)
      (hz : (((ambient.{u,v,s} k G).obj B).d 0 1).hom z = 0),
      GroupLowDegreesAndCoefficients.Large.coordinates k G B 0 z Fin.elim0 = m.val ∧
      ((e 0).hom.app B).hom (((invariantUnit k G).app B).hom m) =
        GroupLowDegreesAndCoefficients.Large.classOf k G B 0 z hz) ∧
  ∀ (S : ShortComplex (GroupDerivedInvariants.GroupModule.{u,v,s} k G)) (hS : S.ShortExact)
    (hB : (S.map (ambient.{u,v,s} k G)).ShortExact) (n : ℕ),
    ClassicalDerivedValues.rightBoundary (GroupDerivedInvariants.invariantsFunctor k G) hS n ≫
        (e (n+1)).hom.app S.X₁ =
      (e n).hom.app S.X₃ ≫ hB.δ n (n+1) rfl

/-- All three squares compare the same original maps with the maps of the
ambient bar sequence, including its actual connecting map. -/
def BarSequenceAgreement {i : M →ₗ[k[G]] N} {p : N →ₗ[k[G]] P}
    (T : Sequence k G hM hN hP i p) {h : ShortExact k G i p}
    (B : SequenceComparison.{u,v,a,b,c,s} k G hM hN hP h) : Prop :=
  let S := commonSequence.{u,v,a,b,c,s} k G h
  ∀ n,
    (∀ x, B.second.homology n (T.inclusion.hom n x) =
      (((ambientH k G n).map S.f).hom (B.first.homology n x))) ∧
    (∀ x, B.third.homology n (T.projection.hom n x) =
      (((ambientH k G n).map S.g).hom (B.second.homology n x))) ∧
    ∀ x, B.first.homology (n+1) (T.boundary n x) =
      (B.bar_exact.δ n (n+1) rfl).hom (B.third.homology n x)

/-- The natural ambient comparison intertwines the actual derived boundary
with the original differential-of-a-lift boundary on the original quotient. -/
def derivedAgreementType (hM : SquareZero.{u,v,a} k G) (hN : SquareZero.{u,v,b} k G)
    (hP : SquareZero.{u,v,c} k G) : Prop :=
  ∃ e : ∀ n, derivedH.{u,v,max a b c s} k G n ≅ ambientH.{u,v,max a b c s} k G n,
    AmbientAgreement k G e ∧
    ∀ {M : Coeff.{u,v,a} k G} {N : Coeff.{u,v,b} k G} {P : Coeff.{u,v,c} k G}
      {i : M →ₗ[k[G]] N} {p : N →ₗ[k[G]] P} (h : ShortExact k G i p)
      (T : Sequence k G hM hN hP i p)
      (B : SequenceComparison.{u,v,a,b,c,s} k G hM hN hP h),
      let S := commonSequence.{u,v,a,b,c,s} k G h
      BarSequenceAgreement k G T B ∧
      ∀ n x, ((e (n+1)).inv.app S.X₁).hom (B.first.homology (n+1) (T.boundary n x)) =
        (ClassicalDerivedValues.rightBoundary (GroupDerivedInvariants.invariantsFunctor k G)
          B.coefficient_exact n).hom (((e n).inv.app S.X₃).hom (B.third.homology n x))

def lowDegreesExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G]
    (M : Coeff.{u,v,a} k G) (N : Coeff.{u,v,b} k G)
    (hM : SquareZero.{u,v,a} k G) (hN : SquareZero.{u,v,b} k G),
    lowDegreesType k G (M := M) (N := N) hM hN

def longExactExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G]
    {M : Coeff.{u,v,a} k G} {N : Coeff.{u,v,b} k G} {P : Coeff.{u,v,c} k G}
    (hM : SquareZero.{u,v,a} k G) (hN : SquareZero.{u,v,b} k G) (hP : SquareZero.{u,v,c} k G),
    longExactType k G (M := M) (N := N) (P := P) hM hN hP

def naturalityExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G]
    {M : Coeff.{u,v,a} k G} {N : Coeff.{u,v,b} k G} {P : Coeff.{u,v,c} k G}
    {M' : Coeff.{u,v,a'} k G} {N' : Coeff.{u,v,b'} k G} {P' : Coeff.{u,v,c'} k G}
    (hM : SquareZero.{u,v,a} k G) (hN : SquareZero.{u,v,b} k G) (hP : SquareZero.{u,v,c} k G)
    (hM' : SquareZero.{u,v,a'} k G) (hN' : SquareZero.{u,v,b'} k G) (hP' : SquareZero.{u,v,c'} k G),
    naturalityType k G (M := M) (N := N) (P := P) (M' := M') (N' := N') (P' := P')
      (hM := hM) (hN := hN) (hP := hP) hM' hN' hP'

def sequenceComparisonExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G]
    {M : Coeff.{u,v,a} k G} {N : Coeff.{u,v,b} k G} {P : Coeff.{u,v,c} k G}
    (hM : SquareZero.{u,v,a} k G) (hN : SquareZero.{u,v,b} k G) (hP : SquareZero.{u,v,c} k G),
    sequenceComparisonType.{u,v,a,b,c,s} k G (M := M) (N := N) (P := P) hM hN hP

def derivedAgreementExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G]
    (hM : SquareZero.{u,v,a} k G) (hN : SquareZero.{u,v,b} k G) (hP : SquareZero.{u,v,c} k G),
    derivedAgreementType.{u,v,a,b,c,s} k G hM hN hP

end Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalExactSequence.Mixed
