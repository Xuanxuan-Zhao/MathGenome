import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GroupCochainComparison
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-! HA-A03, notes/002/advanced-homological-algebra.tex, lines 2953–2989.
The chapter assumes a commutative ring, an arbitrary discrete group, and left
modules over its group algebra. See the Large namespace for the original inputs at independent
universe levels. The cohomology on the derived side is HA-A01's right-derived invariants;
the cochain differential and coefficient maps are HA-A02's unsigned ones. -/
noncomputable section
set_option linter.checkUnivs false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra ModuleCat.Algebra

namespace Specs.AdvancedHomologicalAlgebra.GroupLowDegreesAndCoefficients
open GroupCochainComparison
variable (k G : Type u) [CommRing k] [Group G]

abbrev oneCocycles (M : Coeff k G) := groupCohomology.cocycles₁ (representation k G M)

/-- The image of m ↦ (g ↦ gm-m), with codomain the crossed homomorphisms. -/
abbrev oneBoundaries (M : Coeff k G) : Submodule k (oneCocycles k G M) :=
  (groupCohomology.shortComplexH1 (representation k G M)).moduleCatToCycles.range

abbrev oneQuotient (M : Coeff k G) := oneCocycles k G M ⧸ oneBoundaries k G M

/-- The quotient map on actual crossed homomorphisms. -/
abbrev oneClass (M : Coeff k G) : oneCocycles k G M →ₗ[k] oneQuotient k G M :=
  (oneBoundaries k G M).mkQ

/-- Coefficient maps act on the quotient by postcomposition, using the explicit
kernel/image homology data of the low-degree cochain complex. -/
def oneQuotientMap {M N : Coeff k G} (b : M ⟶ N) :
    ModuleCat.of k (oneQuotient k G M) ⟶ ModuleCat.of k (oneQuotient k G N) :=
  ShortComplex.leftHomologyMap'
    (groupCohomology.mapShortComplexH1 (MonoidHom.id G) (Rep.ofModuleMonoidAlgebra.map b))
    (groupCohomology.shortComplexH1 (representation k G M)).moduleCatLeftHomologyData
    (groupCohomology.shortComplexH1 (representation k G N)).moduleCatLeftHomologyData

/-- A short exact coefficient sequence, regarded as representations. -/
abbrev repSequence (S : ShortComplex (Coeff k G)) := S.map Rep.ofModuleMonoidAlgebra

abbrev repSequenceExact {S : ShortComplex (Coeff k G)} (hS : S.ShortExact) :
    (repSequence k G S).ShortExact := hS.map_of_exact Rep.ofModuleMonoidAlgebra

/-- The connecting morphism of the actual inhomogeneous cochain complex. -/
abbrev coefficientBoundary {S : ShortComplex (Coeff k G)} (hS : S.ShortExact) (n : ℕ) :=
  groupCohomology.δ (repSequenceExact k G hS) n (n+1) rfl

def cochainSystem : UniversalDeltaFunctors.CohomologicalSystem (Coeff k G) (ModuleCat.{u} k) where
  value := cochainCohomology k G
  δ := coefficientBoundary k G

local instance canonicalDerived (A : Type*) [Category A] [Abelian A] :
    HasDerivedCategory A := HasDerivedCategory.standard A

/-- Explicit crossed homomorphism and principal crossed homomorphism conditions. -/
def lowDegreeConditionsType : Prop :=
  (∀ (M : Coeff k G) (f : G → representation k G M),
    f ∈ oneCocycles k G M ↔ ∀ g h : G,
      f (g*h) = f g + (representation k G M).ρ g (f h)) ∧
  (∀ (M : Coeff k G) (f : oneCocycles k G M),
    f ∈ oneBoundaries k G M ↔ ∃ m : representation k G M,
      ∀ g : G, f g = (representation k G M).ρ g m - m)

/-- Naturality of H⁰ = fixed elements, with its concrete action on cocycles. -/
def zeroType : Prop :=
  ∃ e : cochainCohomology k G 0 ≅ GroupDerivedInvariants.invariantsFunctor.{u,u,0} k G,
    ∀ (M : Coeff k G) (z : groupCohomology.cocycles (representation k G M) 0),
      ((e.hom.app M).hom (groupCohomology.π (representation k G M) 0 z)).val =
        (groupCohomology.iCocycles (representation k G M) 0).hom z Fin.elim0

/-- H¹ is the displayed quotient, naturally with respect to the explicit
postcomposition maps. The classes of all crossed homomorphisms are retained. -/
def oneType : Prop :=
  ∃ e : ∀ M : Coeff k G,
      (cochainCohomology k G 1).obj M ≅ ModuleCat.of k (oneQuotient k G M),
    (∀ (M N : Coeff k G) (b : M ⟶ N),
      (cochainCohomology k G 1).map b ≫ (e N).hom = (e M).hom ≫ oneQuotientMap k G b) ∧
    (∀ (M : Coeff k G) (f : oneCocycles k G M),
      (e M).hom (groupCohomology.H1π (representation k G M) f) = oneClass k G M f)

/-- All consecutive pairs, the initial zero, and naturality for every morphism
of short exact coefficient sequences. -/
def longExactType : Prop := UniversalDeltaFunctors.IsCohomological (cochainSystem k G)

/-- Coefficient sequences remain short exact as actual cochain complexes. -/
def cochainExactType : Prop := ∀ {S : ShortComplex (Coeff k G)}, S.ShortExact →
  (S.map (cochainsFunctor k G)).ShortExact

/-- Lifts needed to evaluate the boundary always exist, for every cocycle. -/
def liftsExistType : Prop := ∀ {S : ShortComplex (Coeff k G)} (_hS : S.ShortExact) (n : ℕ)
    (z : (Fin n → G) → representation k G S.X₃),
    (cochains k G S.X₃).d n (n+1) z = 0 →
    ∃ (y : (Fin n → G) → representation k G S.X₂)
      (x : (Fin (n+1) → G) → representation k G S.X₁),
      (groupCohomology.cochainsMap (MonoidHom.id G)
        (Rep.ofModuleMonoidAlgebra.map S.g)).f n y = z ∧
      (Rep.ofModuleMonoidAlgebra.map S.f).hom ∘ x = (cochains k G S.X₂).d n (n+1) y

/-- For every choice of lifts, the boundary is represented by the differential
of that lift. The construction on the right includes the proof that x is a
cocycle; equality with this fixed boundary gives independence of all choices. -/
def liftedBoundaryType : Prop := ∀ {S : ShortComplex (Coeff k G)} (hS : S.ShortExact) (n : ℕ)
    (z : (Fin n → G) → representation k G S.X₃)
    (hz : (cochains k G S.X₃).d n (n+1) z = 0)
    (y : (Fin n → G) → representation k G S.X₂)
    (hy : (groupCohomology.cochainsMap (MonoidHom.id G)
      (Rep.ofModuleMonoidAlgebra.map S.g)).f n y = z)
    (x : (Fin (n+1) → G) → representation k G S.X₁)
    (hx : (Rep.ofModuleMonoidAlgebra.map S.f).hom ∘ x = (cochains k G S.X₂).d n (n+1) y),
    coefficientBoundary k G hS n
      (groupCohomology.π (representation k G S.X₃) n
        (groupCohomology.cocyclesMk z (by simpa [CochainComplex.of.d] using hz))) =
      groupCohomology.π (representation k G S.X₁) (n+1)
        (groupCohomology.cocyclesMkOfCompEqD (repSequenceExact k G hS) hx)

/-- Any chosen degree-zero identification with invariants extends to a natural
isomorphism in all degrees commuting with the actual right-derived boundaries.
The equality at zero says that the comparison acts as the identity on invariants.
In particular one may use the HA-R09 degree-zero identification. -/
def derivedCompatibilityType : Prop :=
  ∀ (c₀ : cochainCohomology k G 0 ≅ GroupDerivedInvariants.invariantsFunctor.{u,u,0} k G)
    (d₀ : GroupDerivedInvariants.cohomology.{u,u,0} k G 0 ≅
      GroupDerivedInvariants.invariantsFunctor.{u,u,0} k G),
    ∃ e : ∀ n : ℕ, GroupDerivedInvariants.cohomology.{u,u,0} k G n ≅ cochainCohomology k G n,
      (e 0).hom ≫ c₀.hom = d₀.hom ∧
      ∀ {S : ShortComplex (Coeff k G)} (hS : S.ShortExact) (n : ℕ),
        ClassicalDerivedValues.rightBoundary (GroupDerivedInvariants.invariantsFunctor k G) hS n ≫
          (e (n+1)).hom.app S.X₁ =
        (e n).hom.app S.X₃ ≫ coefficientBoundary k G hS n

/-- Explicit action on quotient representatives: it is postcomposition by the
coefficient map, including its value at every group element. -/
def quotientMapType : Prop := ∀ (M N : Coeff k G) (b : M ⟶ N) (f : oneCocycles k G M),
  oneQuotientMap k G b (oneClass k G M f) = oneClass k G N
    (groupCohomology.mapCocycles₁ (MonoidHom.id G) (Rep.ofModuleMonoidAlgebra.map b) f) ∧
  ∀ g : G,
    (groupCohomology.mapCocycles₁ (MonoidHom.id G) (Rep.ofModuleMonoidAlgebra.map b) f) g =
      b.hom (f g)

/-- The source's low-degree identifications for the actual derived invariants,
with naturality of the quotient identification made explicit. -/
def derivedLowDegreesType : Prop :=
  ∃ e₀ : GroupDerivedInvariants.cohomology.{u,u,0} k G 0 ≅
      GroupDerivedInvariants.invariantsFunctor.{u,u,0} k G,
    ∃ e₁ : ∀ M : Coeff k G,
        (GroupDerivedInvariants.cohomology.{u,u,0} k G 1).obj M ≅
          ModuleCat.of k (oneQuotient k G M),
      ∀ (M N : Coeff k G) (b : M ⟶ N),
        (GroupDerivedInvariants.cohomology k G 1).map b ≫ (e₁ N).hom =
          (e₁ M).hom ≫ oneQuotientMap k G b

def lowDegreeConditionsExpected : Prop :=
  ∀ (k G : Type u) [CommRing k] [Group G], lowDegreeConditionsType k G

def zeroExpected : Prop :=
  ∀ (k G : Type u) [CommRing k] [Group G], zeroType k G

def oneExpected : Prop :=
  ∀ (k G : Type u) [CommRing k] [Group G], oneType k G

def cochainExactExpected : Prop :=
  ∀ (k G : Type u) [CommRing k] [Group G], cochainExactType k G

def longExactExpected : Prop :=
  ∀ (k G : Type u) [CommRing k] [Group G], longExactType k G

def liftsExistExpected : Prop :=
  ∀ (k G : Type u) [CommRing k] [Group G], liftsExistType k G

def liftedBoundaryExpected : Prop :=
  ∀ (k G : Type u) [CommRing k] [Group G], liftedBoundaryType k G

def derivedCompatibilityExpected : Prop :=
  ∀ (k G : Type u) [CommRing k] [Group G], derivedCompatibilityType k G

def quotientMapExpected : Prop :=
  ∀ (k G : Type u) [CommRing k] [Group G], quotientMapType k G

def derivedLowDegreesExpected : Prop :=
  ∀ (k G : Type u) [CommRing k] [Group G], derivedLowDegreesType k G

end Specs.AdvancedHomologicalAlgebra.GroupLowDegreesAndCoefficients

namespace Specs.AdvancedHomologicalAlgebra.GroupLowDegreesAndCoefficients.Large

open GroupCochainComparison.Large

universe v w

variable (k : Type u) (G : Type v) [CommRing k] [Group G]

abbrev Coeff := GroupCochainComparison.Large.Coeff.{u,v,w} k G

abbrev cochains := homogeneousFunctor.{u,v,w} k G

instance cochainsAdditive : (cochains.{u,v,w} k G).Additive where
  map_add := by
    intro M N a b
    ext n φ
    rfl

abbrev complex (M : Coeff.{u,v,w} k G) := (cochains k G).obj M

abbrev representation (M : Coeff.{u,v,w} k G) := GroupCochainComparison.Large.representation k G M

abbrev cohomology (n : ℕ) : (Coeff.{u,v,w} k G) ⥤ ModuleCat.{max u v w} k :=
  cochains.{u,v,w} k G ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} k) (.up ℕ) n

/-- The unsigned homogeneous cochains identified with functions on the original
group tuples by evaluating at the normalized bar generators. -/
def coordinates (M : Coeff.{u,v,w} k G) (n : ℕ) (z : (complex k G M).X n)
    (g : Fin n → G) : representation k G M :=
  z.hom (GroupBar.Large.single k G (Fin.partialProd g) 1)

/-- In degree one the normalized tuple is (1,g). -/
abbrev oneCoordinates (M : Coeff.{u,v,w} k G) (z : (complex k G M).X 1) (g : G) :
    representation k G M :=
  coordinates k G M 1 z (fun _ => g)

/-- The actual kernel in inhomogeneous degree-one coordinates. -/
def crossed (M : Coeff.{u,v,w} k G) : Submodule k (G → representation k G M) where
  carrier := {f | ∀ g h : G, f (g * h) = f g + (representation k G M).ρ g (f h)}
  zero_mem' := by
    intro g h
    simp
  add_mem' {f f'} hf hf' := by
    intro g h
    change f (g * h) + f' (g * h) = f g + f' g + (representation k G M).ρ g (f h + f' h)
    rw [hf g h, hf' g h, map_add]
    abel
  smul_mem' c f hf := by
    intro g h
    change c • f (g * h) = c • f g + (representation k G M).ρ g (c • f h)
    rw [hf g h, map_smul, smul_add]

/-- The map m ↦ (g ↦ gm−m) into the crossed homomorphisms. -/
def principal (M : Coeff.{u,v,w} k G) : representation k G M →ₗ[k] crossed k G M where
  toFun m := ⟨fun g => (representation k G M).ρ g m - m, by
    intro g h
    change (representation k G M).ρ (g * h) m - m =
      (representation k G M).ρ g m - m +
        (representation k G M).ρ g ((representation k G M).ρ h m - m)
    rw [map_mul, Module.End.mul_apply, map_sub]
    abel⟩
  map_add' x y := by
    ext g
    change (representation k G M).ρ g (x + y) - (x + y) =
      ((representation k G M).ρ g x - x) + ((representation k G M).ρ g y - y)
    rw [map_add]
    abel
  map_smul' c x := by
    ext g
    change (representation k G M).ρ g (c • x) - c • x =
      c • ((representation k G M).ρ g x - x)
    rw [map_smul, smul_sub]

abbrev boundaries (M : Coeff.{u,v,w} k G) : Submodule k (crossed k G M) :=
  (principal k G M).range

abbrev quotient (M : Coeff.{u,v,w} k G) :=
  crossed k G M ⧸ boundaries k G M

/-- Coefficient maps on crossed homomorphisms are pointwise postcomposition. -/
def crossedMap {M N : Coeff.{u,v,w} k G} (a : M ⟶ N) : crossed k G M →ₗ[k] crossed k G N where
  toFun f := ⟨fun g => (Rep.ofModuleMonoidAlgebra.map a).hom (f.val g), by
    intro g h
    change (Rep.ofModuleMonoidAlgebra.map a).hom (f.val (g * h)) = _
    rw [show f.val (g * h) = _ from f.property g h, map_add, Rep.hom_comm_apply]⟩
  map_add' x y := by
    ext g
    exact map_add (Rep.ofModuleMonoidAlgebra.map a).hom _ _
  map_smul' c x := by
    ext g
    exact map_smul (Rep.ofModuleMonoidAlgebra.map a).hom _ _

def quotientMap {M N : Coeff.{u,v,w} k G} (a : M ⟶ N) :
    ModuleCat.of k (quotient k G M) ⟶ ModuleCat.of k (quotient k G N) :=
  ModuleCat.ofHom <| (boundaries k G M).mapQ (boundaries k G N) (crossedMap k G a) (by
    rintro _ ⟨m, rfl⟩
    refine ⟨(Rep.ofModuleMonoidAlgebra.map a).hom m, ?_⟩
    ext g
    change (representation k G N).ρ g ((Rep.ofModuleMonoidAlgebra.map a).hom m) -
      (Rep.ofModuleMonoidAlgebra.map a).hom m =
      (Rep.ofModuleMonoidAlgebra.map a).hom ((representation k G M).ρ g m - m)
    rw [map_sub, Rep.hom_comm_apply])

/-- The degree-one cocycles and boundaries of the fixed cochain complex in
the source's coordinates. -/
def lowDegreeConditionsType : Prop :=
  (∀ (M : Coeff.{u,v,w} k G) (f : G → representation k G M),
    (∃ z : (complex k G M).X 1, ((complex k G M).d 1 2).hom z = 0 ∧ oneCoordinates k G M z = f) ↔
      f ∈ crossed k G M) ∧
  (∀ (M : Coeff.{u,v,w} k G) (f : crossed k G M),
    (∃ y : (complex k G M).X 0, oneCoordinates k G M (((complex k G M).d 0 1).hom y) = f.val) ↔
      f ∈ boundaries k G M)

/-- Degree zero is evaluation on the vertex 1 followed by identification
with the fixed elements of the original coefficient module. -/
def zeroType : Prop :=
  ∃ e : cohomology.{u,v,w} k G 0 ≅ GroupDerivedInvariants.invariantsFunctor.{u,v,w} k G,
    ∀ (M : Coeff.{u,v,w} k G) (z : (complex k G M).cycles 0),
      ((e.hom.app M).hom (((complex k G M).homologyπ 0).hom z)).val =
        coordinates k G M 0 (((complex k G M).iCycles 0).hom z) Fin.elim0

/-- Naturality of the degree-one identification is for the quotient maps
induced by pointwise postcomposition. -/
def oneType : Prop :=
  ∃ e : ∀ M : Coeff.{u,v,w} k G, (cohomology.{u,v,w} k G 1).obj M ≅ ModuleCat.of k (quotient k G M),
    (∀ (M N : Coeff.{u,v,w} k G) (a : M ⟶ N),
      (cohomology.{u,v,w} k G 1).map a ≫ (e N).hom = (e M).hom ≫ quotientMap k G a) ∧
    (∀ (M : Coeff.{u,v,w} k G) (z : (complex k G M).cycles 1), ∃ f : crossed k G M,
      f.val = oneCoordinates k G M (((complex k G M).iCycles 1).hom z) ∧
      (e M).hom (((complex k G M).homologyπ 1).hom z) = (boundaries k G M).mkQ f)

def quotientMapType : Prop :=
  ∀ (M N : Coeff.{u,v,w} k G) (a : M ⟶ N) (f : crossed k G M),
    (quotientMap k G a).hom ((boundaries k G M).mkQ f) =
      (boundaries k G N).mkQ (crossedMap k G a f) ∧
    ∀ g, (crossedMap k G a f).val g = (Rep.ofModuleMonoidAlgebra.map a).hom (f.val g)

def cochainExactType : Prop :=
  ∀ {S : ShortComplex (Coeff.{u,v,w} k G)}, S.ShortExact → (S.map (cochains.{u,v,w} k G)).ShortExact

/-- The boundary of the short exact sequence of the actual cochain complexes.
The required exactness is a separate target for every coefficient sequence. -/
abbrev coefficientBoundary {S : ShortComplex (Coeff.{u,v,w} k G)}
    (hC : (S.map (cochains.{u,v,w} k G)).ShortExact) (n : ℕ) :=
  hC.δ n (n + 1) rfl

def cochainSystem (h : cochainExactType.{u,v,w} k G) :
    UniversalDeltaFunctors.CohomologicalSystem (Coeff.{u,v,w} k G) (ModuleCat.{max u v w} k) where
  value := cohomology k G
  δ hS := coefficientBoundary k G (h hS)

def longExactType : Prop :=
  ∀ h : cochainExactType.{u,v,w} k G, UniversalDeltaFunctors.IsCohomological (cochainSystem k G h)

/-- The lift equations in the original inhomogeneous coordinates. In
particular, the second equation uses the HA-A02 alternating differential. -/
def Lifts {S : ShortComplex (Coeff.{u,v,w} k G)} (n : ℕ)
    (z : (complex k G S.X₃).X n) (y : (complex k G S.X₂).X n) (x : (complex k G S.X₁).X (n+1)) : Prop :=
  (∀ g, (Rep.ofModuleMonoidAlgebra.map S.g).hom (coordinates k G S.X₂ n y g) =
    coordinates k G S.X₃ n z g) ∧
  (∀ g, (Rep.ofModuleMonoidAlgebra.map S.f).hom (coordinates k G S.X₁ (n+1) x g) =
    differential k G S.X₂ n (coordinates k G S.X₂ n y) g)

def liftsExistType : Prop :=
  ∀ {S : ShortComplex (Coeff.{u,v,w} k G)} (_hS : S.ShortExact) (n : ℕ)
    (z : (complex k G S.X₃).X n), ((complex k G S.X₃).d n (n+1)).hom z = 0 →
    ∃ (y : (complex k G S.X₂).X n) (x : (complex k G S.X₁).X (n+1)), Lifts k G n z y x

/-- Convert an actual cocycle to its actual cohomology class. -/
abbrev classOf (M : Coeff.{u,v,w} k G) (n : ℕ) (z : (complex k G M).X n)
    (hz : ((complex k G M).d n (n+1)).hom z = 0) : (cohomology.{u,v,w} k G n).obj M :=
  ((complex k G M).homologyπ n).hom ((complex k G M).cyclesMk z (n+1) (by simp) hz)

def liftedBoundaryType : Prop :=
  ∀ {S : ShortComplex (Coeff.{u,v,w} k G)} (hC : (S.map (cochains.{u,v,w} k G)).ShortExact) (n : ℕ)
    (z : (complex k G S.X₃).X n) (hz : ((complex k G S.X₃).d n (n+1)).hom z = 0)
    (y : (complex k G S.X₂).X n) (x : (complex k G S.X₁).X (n+1)), Lifts k G n z y x →
      ∃ hx : ((complex k G S.X₁).d (n+1) (n+2)).hom x = 0,
        (coefficientBoundary k G hC n).hom (classOf k G S.X₃ n z hz) =
          classOf k G S.X₁ (n+1) x hx

local instance canonicalDerived (A : Type*) [Category A] [Abelian A] :
    HasDerivedCategory A := HasDerivedCategory.standard A

/-- The comparison is the identity on invariants and commutes with the
actual right-derived boundaries of HA-A01 and HA-R09. -/
def derivedCompatibilityType : Prop :=
  ∀ (h : cochainExactType.{u,v,w} k G)
    (c₀ : cohomology.{u,v,w} k G 0 ≅ GroupDerivedInvariants.invariantsFunctor.{u,v,w} k G)
    (d₀ : GroupDerivedInvariants.cohomology.{u,v,w} k G 0 ≅
      GroupDerivedInvariants.invariantsFunctor.{u,v,w} k G),
    ∃! e : ∀ n : ℕ, GroupDerivedInvariants.cohomology.{u,v,w} k G n ≅ cohomology.{u,v,w} k G n,
      (e 0).hom ≫ c₀.hom = d₀.hom ∧
      ∀ {S : ShortComplex (Coeff.{u,v,w} k G)} (hS : S.ShortExact) (n : ℕ),
        ClassicalDerivedValues.rightBoundary (GroupDerivedInvariants.invariantsFunctor k G) hS n ≫
          (e (n+1)).hom.app S.X₁ =
        (e n).hom.app S.X₃ ≫ coefficientBoundary k G (h hS) n

def derivedLowDegreesType : Prop :=
  ∃ _e₀ : GroupDerivedInvariants.cohomology.{u,v,w} k G 0 ≅
      GroupDerivedInvariants.invariantsFunctor.{u,v,w} k G,
    ∃ e₁ : ∀ M : Coeff.{u,v,w} k G, (GroupDerivedInvariants.cohomology.{u,v,w} k G 1).obj M ≅
      ModuleCat.of k (quotient k G M),
      ∀ (M N : Coeff.{u,v,w} k G) (a : M ⟶ N),
        (GroupDerivedInvariants.cohomology.{u,v,w} k G 1).map a ≫ (e₁ N).hom =
          (e₁ M).hom ≫ quotientMap k G a

def lowDegreeConditionsExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G], lowDegreeConditionsType.{u,v,w} k G

def zeroExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G], zeroType.{u,v,w} k G

def oneExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G], oneType.{u,v,w} k G

def cochainExactExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G], cochainExactType.{u,v,w} k G

def longExactExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G], longExactType.{u,v,w} k G

def liftsExistExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G], liftsExistType.{u,v,w} k G

def liftedBoundaryExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G], liftedBoundaryType.{u,v,w} k G

def derivedCompatibilityExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G], derivedCompatibilityType.{u,v,w} k G

def quotientMapExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G], quotientMapType.{u,v,w} k G

def derivedLowDegreesExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G], derivedLowDegreesType.{u,v,w} k G

end Specs.AdvancedHomologicalAlgebra.GroupLowDegreesAndCoefficients.Large
