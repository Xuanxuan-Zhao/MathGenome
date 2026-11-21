import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupCochainComparison
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.TorBalance
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.UniversalDeltaFunctors
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Batteries.Tactic.OpenPrivate

noncomputable section
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra ModuleCat.Algebra

namespace AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients

open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients
universe u v w
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

private lemma trivial_single_smul (g : G) (r a : k) :
    MonoidAlgebra.single g r • trivialElement k G a = trivialElement k G (r * a) := by
  apply (Representation.trivial k G k).asModuleEquiv.injective
  change (Representation.trivial k G k).asAlgebraHom (MonoidAlgebra.single g r) a = r * a
  simp [Representation.asAlgebraHom_single, LinearMap.smul_apply]

private lemma trivial_base_smul (r a : k) :
    r • trivialElement k G a = trivialElement k G (r * a) := by
  change (algebraMap k k[G] r) • trivialElement k G a = _
  simpa [MonoidAlgebra.coe_algebraMap] using trivial_single_smul k G (1 : G) r a

private def fromFixed (M : Coeff.{u,v,w} k G) (m : invariants k G M) : OriginalHom k G M where
  toFun a := (Representation.trivial k G k).asModuleEquiv a • m.val
  map_add' := by intro a b; simp only [map_add]; exact add_smul _ _ _
  map_smul' := by
    intro r a
    simp only [RingHom.id_apply]
    change (Representation.trivial k G k).asModuleEquiv (r • a) • m.val =
      r • ((Representation.trivial k G k).asModuleEquiv a • m.val)
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add r s hr hs => simp only [add_smul, map_add, hr, hs]
    | single g b =>
        obtain ⟨c, rfl⟩ := (Representation.trivial k G k).asModuleEquiv.symm.surjective a
        change (Representation.trivial k G k).asModuleEquiv
          (MonoidAlgebra.single g b • trivialElement k G c) • m.val =
          MonoidAlgebra.single g b • (c • m.val)
        rw [trivial_single_smul]
        have hb : MonoidAlgebra.single g b = b • MonoidAlgebra.single g (1 : k) := by simp
        rw [hb, smul_assoc, smul_comm (MonoidAlgebra.single g (1 : k)), m.property g]
        exact mul_smul b c m.val

def evaluationEquiv (M : Coeff.{u,v,w} k G) : OriginalHom k G M ≃ₗ[k] invariants k G M where
  toFun f := ⟨f (trivialElement k G 1), fun g => by
    rw [← f.map_smul, trivial_single_smul, one_mul]⟩
  invFun := fromFixed k G M
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by
    apply LinearMap.ext
    intro a
    obtain ⟨a, rfl⟩ := (Representation.trivial k G k).asModuleEquiv.symm.surjective a
    change a • f (trivialElement k G 1) = f (trivialElement k G a)
    rw [← f.map_smul_of_tower, trivial_base_smul, mul_one]
  right_inv m := by
    apply Subtype.ext
    exact one_smul k m.val

theorem evaluation : evaluationType.{u,v,w} k G :=
  ⟨evaluationEquiv k G, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

private abbrev ambientCochains (M : Coeff.{u,v,w} k G) :=
  (ambientBar k G).obj M

/-- Explicit evaluation on the original cumulative-product tuples, followed by carrier descent. -/
def ambientEvaluation (M : Coeff.{u,v,w} k G) (n : ℕ) :
    (ambientCochains k G M).X n ≃ₗ[k] ULift.{u} (TupleCochain k G M n) :=
  (GroupCochainComparison.LargeCoordinates.coordinatesEquiv k G ((lift k G).obj M) n).trans
    (tupleLift k G M n).symm

private lemma ambientEvaluation_d (M : Coeff.{u,v,w} k G) (n : ℕ)
    (φ : (ambientCochains k G M).X n) :
    ambientEvaluation k G M (n+1) (((ambientCochains k G M).d n (n+1)).hom φ) =
      ULift.up (differential k G M n (ambientEvaluation k G M n φ).down) := by
  apply ULift.ext
  funext g
  change (GroupCochainComparison.LargeCoordinates.coordinatesEquiv k G ((lift k G).obj M) (n+1)
    (((ambientCochains k G M).d n (n+1)).hom φ) g).down = _
  have h := GroupCochainComparison.LargeCoordinates.comparison.{u,v,w} k G
  let e := h.choose
  have he (j : ℕ) (ψ : (ambientCochains k G M).X j) :
      e ((lift k G).obj M) j ψ =
        GroupCochainComparison.LargeCoordinates.coordinatesEquiv k G ((lift k G).obj M) j ψ :=
    funext (fun t => h.choose_spec.1 _ _ ψ t)
  have hd := h.choose_spec.2.1 ((lift k G).obj M) n φ g
  change e _ _ _ _ = _ at hd
  rw [he, he] at hd
  let down : Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large.representation k G ((lift k G).obj M) →ₗ[k] M :=
    ULift.moduleEquiv.toLinearMap
  refine (congrArg down hd).trans ?_
  change down (Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large.differential k G
    ((lift k G).obj M) n
    (GroupCochainComparison.LargeCoordinates.coordinatesEquiv k G ((lift k G).obj M) n φ) g) =
      differential k G M n (ambientEvaluation k G M n φ).down g
  rw [differential_apply]
  simp only [Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large.differential,
    map_add, map_sum, map_smul]
  rfl

theorem squareZero : SquareZero.{u,v,w} k G := by
  intro M n
  apply LinearMap.ext
  intro f
  obtain ⟨φ, hf⟩ := (ambientEvaluation k G M n).surjective (ULift.up f)
  have h := congrArg (fun e : (ambientCochains k G M).X n ⟶
        (ambientCochains k G M).X (n+2) =>
      ambientEvaluation k G M (n+2) (e.hom φ))
    ((ambientCochains k G M).d_comp_d n (n+1) (n+2))
  change ambientEvaluation k G M (n+2)
      (((ambientCochains k G M).d (n+1) (n+2)).hom
        (((ambientCochains k G M).d n (n+1)).hom φ)) = _ at h
  rw [ambientEvaluation_d, ambientEvaluation_d, hf] at h
  rw [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero] at h
  exact congrArg ULift.down h

/-- The cochain map is the pointwise `ULift` equivalence composed with bar evaluation. -/
def barIso : ambientBar.{u,v,w} k G ≅ rawLifted k G (squareZero k G) := by
  refine NatIso.ofComponents (fun M => HomologicalComplex.Hom.isoOfComponents
    (fun n => (ambientEvaluation k G M n).toModuleIso) ?_) ?_
  · intro i j hij
    have hji : j = i + 1 := hij.symm
    subst j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    symm
    change ambientEvaluation k G M (i+1) (((ambientCochains k G M).d i (i+1)).hom φ) =
      ((scalarLift.{u,v,w} k).map ((rawComplex k G (squareZero k G) M).d i (i+1))).hom
        (ambientEvaluation k G M i φ)
    simp only [rawComplex, CochainComplex.of_d]
    exact ambientEvaluation_d k G M i φ
  · intro M N b
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply ULift.ext
    rfl

/-- Homology commutes with the exact scalar carrier lift. -/
def rawHomologyLiftIso (n : ℕ) :
    rawLifted.{u,v,w} k G (squareZero k G) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} k) (.up ℕ) n ≅
    rawCohomology k G (squareZero k G) n ⋙ scalarLift.{u,v,w} k := by
  let F := scalarLift.{u,v,w} k
  let K := rawFunctor k G (squareZero.{u,v,w} k G)
  refine NatIso.ofComponents (fun M => ((K.obj M).sc n).mapHomologyIso F) ?_
  intro M N b
  exact ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map (K.map b)) F

/-- The ambient comparison uses HA-R11's degree sign in the bar-to-Ext
class map. The subsequent tuple and carrier comparisons preserve cochains. -/
def ambientBarCohomologyIso (n : ℕ) :
    derived.{u,v,w} k G n ≅ ambientBarCohomology k G n :=
  Functor.isoWhiskerLeft (lift k G) (GroupCochainComparison.Large.cohomologyIso k G n) ≪≫
    (Functor.associator _ _ _).symm

theorem liftExact : liftExactType.{u,v,w} k G :=
  ⟨inferInstance, inferInstance⟩

/-- The derived comparison is induced by the cochain isomorphism `barIso`. -/
def rawCohomologyIso (n : ℕ) :
    derived.{u,v,w} k G n ≅ rawCohomology k G (squareZero k G) n ⋙ scalarLift.{u,v,w} k :=
  ambientBarCohomologyIso k G n ≪≫
    (Functor.isoWhiskerRight (barIso k G) _ ≪≫ rawHomologyLiftIso k G n)

theorem barTransport : barTransportType.{u,v,w} k G := by
  refine ⟨squareZero k G, barIso k G, ?_, ?_, fun n => ⟨ambientBarCohomologyIso k G n, rawCohomologyIso k G n, fun _ => rfl⟩⟩
  · intro M n φ g
    rfl
  · intro M n f g
    have h := (ambientEvaluation k G M n).apply_symm_apply (ULift.up f)
    exact congrArg (fun x : ULift.{u} (TupleCochain k G M n) =>
      (ULift.up (x.down g) : (lift k G).obj M)) h

private abbrev largeBarTerm (n : ℕ) :=
  Rep.toModuleMonoidAlgebra.obj (GroupBar.Large.B.{u,v,w} k G n)

private abbrev largeVertex (n : ℕ) (c : Fin (n+1) → G) : largeBarTerm.{u,v,w} k G n :=
  (GroupBar.Large.B.{u,v,w} k G n).ρ.asModuleEquiv.symm (GroupBar.Large.single k G c 1)

/-- Changing the size of the tuple presentation sends each vertex tuple to itself. -/
private def tupleBasisEquiv (n : ℕ) :
    GroupBar.Large.B.{u,v,w} k G n ≃ₗ[k] GroupBar.Large.B.{u,v,0} k G n :=
  (GroupBar.Large.originalBasis.{u,v,w} k G n).trans
    (GroupBar.Large.originalBasis.{u,v,0} k G n).symm

private lemma tupleBasisEquiv_single {n : ℕ} (c : Fin (n+1) → G) (r : k) :
    tupleBasisEquiv.{u,v,w} k G n (GroupBar.Large.single k G c r) =
      GroupBar.Large.single k G c r := by
  apply (GroupBar.Large.originalBasis.{u,v,0} k G n).injective
  simp only [tupleBasisEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  exact (GroupBar.Large.originalBasis_single.{u,v,w} k G n c r).trans
    (GroupBar.Large.originalBasis_single.{u,v,0} k G n c r).symm

private def barTermEquiv (n : ℕ) :
    largeBarTerm.{u,v,w} k G n ≃ₗ[k[G]] (originalBar k G).X n := by
  let ρ := (GroupBar.Large.B.{u,v,w} k G n).ρ
  let σ := (GroupBar.Large.B.{u,v,0} k G n).ρ
  let b := tupleBasisEquiv.{u,v,w} k G n
  let f : Representation.IntertwiningMap ρ σ :=
    ⟨b.toLinearMap, fun g => by
      apply MonoidAlgebra.lhom_ext'
      rintro ⟨c⟩
      apply LinearMap.ext_ring
      change b (ρ g (GroupBar.Large.single k G c 1)) =
        σ g (b (GroupBar.Large.single k G c 1))
      change tupleBasisEquiv.{u,v,w} k G n ((GroupBar.Large.B.{u,v,w} k G n).ρ g
          (GroupBar.Large.single k G c 1)) =
        (GroupBar.Large.B.{u,v,0} k G n).ρ g
          (tupleBasisEquiv.{u,v,w} k G n (GroupBar.Large.single k G c 1))
      rw [GroupBar.Large.diagonal_action.{u,v,w}, tupleBasisEquiv_single.{u,v,w},
        tupleBasisEquiv_single.{u,v,w}, GroupBar.Large.diagonal_action.{u,v,0}]⟩
  let f' : largeBarTerm.{u,v,w} k G n →ₗ[k[G]] (originalBar k G).X n :=
    Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f
  exact LinearEquiv.ofBijective f' b.bijective

private lemma barTermEquiv_apply {n : ℕ} (x : largeBarTerm.{u,v,w} k G n) :
    barTermEquiv k G n x =
      (GroupBar.Large.B.{u,v,0} k G n).ρ.asModuleEquiv.symm
        (tupleBasisEquiv k G n ((GroupBar.Large.B.{u,v,w} k G n).ρ.asModuleEquiv x)) :=
  rfl

private lemma barTermEquiv_vertex (n : ℕ) (c : Fin (n+1) → G) :
    barTermEquiv.{u,v,w} k G n (largeVertex k G n c) = basisElement k G n c := by
  rw [barTermEquiv_apply]
  simp only [largeVertex, LinearEquiv.apply_symm_apply]
  exact congrArg (GroupBar.Large.B.{u,v,0} k G n).ρ.asModuleEquiv.symm
    (tupleBasisEquiv_single.{u,v,w} k G c 1)

private lemma barTermEquiv_boundary (n : ℕ) (x : largeBarTerm.{u,v,w} k G (n+1)) :
    barTermEquiv k G n (Rep.toModuleMonoidAlgebra.map
        (GroupBar.Large.boundary.{u,v,w} k G n) x) =
      ((originalBar k G).d (n+1) n).hom (barTermEquiv k G (n+1) x) := by
  have h : (tupleBasisEquiv.{u,v,w} k G n).toLinearMap.comp (GroupBar.Large.d k G n) =
      (GroupBar.Large.d.{u,v,0} k G n).comp
        (tupleBasisEquiv.{u,v,w} k G (n+1)).toLinearMap := by
    apply MonoidAlgebra.lhom_ext'
    rintro ⟨c⟩
    apply LinearMap.ext_ring
    change tupleBasisEquiv k G n (GroupBar.Large.d k G n (GroupBar.Large.single k G c 1)) =
      GroupBar.Large.d k G n (tupleBasisEquiv k G (n+1) (GroupBar.Large.single k G c 1))
    rw [GroupBar.Large.boundary_single.{u,v,w}, tupleBasisEquiv_single.{u,v,w},
      GroupBar.Large.boundary_single.{u,v,0}, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact tupleBasisEquiv_single.{u,v,w} k G _ _
  rw [barTermEquiv_apply, barTermEquiv_apply]
  exact congrArg (GroupBar.Large.B.{u,v,0} k G n).ρ.asModuleEquiv.symm (LinearMap.congr_fun h ((GroupBar.Large.B.{u,v,w} k G (n+1)).ρ.asModuleEquiv x))

private def liftBarHom (M : Coeff.{u,v,w} k G) (n : ℕ) :
    ((originalBar k G).X n →ₗ[k[G]] M) ≃ₗ[k] (largeBarTerm.{u,v,w} k G n ⟶ (lift k G).obj M) where
  toFun f := ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp
    (f.comp (barTermEquiv k G n).toLinearMap))
  invFun f := ULift.moduleEquiv.toLinearMap.comp
    (f.hom.comp (barTermEquiv k G n).symm.toLinearMap)
  left_inv f := by
    apply LinearMap.ext
    intro x
    exact congrArg f ((barTermEquiv.{u,v,w} k G n).apply_symm_apply x)
  right_inv f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg f.hom ((barTermEquiv.{u,v,w} k G n).symm_apply_apply x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def barRepHomEquiv (M : Coeff.{u,v,w} k G) (n : ℕ) :
    (largeBarTerm.{u,v,w} k G n ⟶ (lift k G).obj M) ≃ₗ[k]
      (ambientCochains k G M).X n :=
  { (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)).toAdjunction.homEquiv
      (GroupBar.Large.B.{u,v,w} k G n) ((lift k G).obj M) with
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

def originalBarCoordinates (M : Coeff.{u,v,w} k G) (n : ℕ) :
    ((originalBar k G).X n →ₗ[k[G]] M) ≃ₗ[k] TupleCochain k G M n :=
  (liftBarHom k G M n).trans ((barRepHomEquiv k G M n).trans
    ((ambientEvaluation k G M n).trans ULift.moduleEquiv))

lemma originalBarCoordinates_apply (M : Coeff.{u,v,w} k G) (n : ℕ)
    (f : (originalBar k G).X n →ₗ[k[G]] M) (g : Fin n → G) :
    originalBarCoordinates k G M n f g = f (basisElement k G n (Fin.partialProd g)) := by
  change f (barTermEquiv.{u,v,w} k G n (largeVertex k G n (Fin.partialProd g))) = _
  rw [barTermEquiv_vertex]

lemma originalBarCoordinates_d (M : Coeff.{u,v,w} k G) (n : ℕ)
    (f : (originalBar k G).X n →ₗ[k[G]] M) :
    originalBarCoordinates k G M (n+1) (f.comp ((originalBar k G).d (n+1) n).hom) =
      differential k G M n (originalBarCoordinates k G M n f) := by
  let φ := barRepHomEquiv k G M n (liftBarHom k G M n f)
  have hd := congrArg ULift.down (ambientEvaluation_d k G M n φ)
  have hφ : barRepHomEquiv k G M (n+1)
      (liftBarHom k G M (n+1) (f.comp ((originalBar k G).d (n+1) n).hom)) =
      (((ambientCochains k G M).d n (n+1)).hom φ) := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.toLinearMap_injective
    apply LinearMap.ext
    intro x
    change ULift.up (f (((originalBar k G).d (n+1) n).hom
        (barTermEquiv k G (n+1) ((GroupBar.Large.B.{u,v,w} k G (n+1)).ρ.asModuleEquiv.symm x)))) =
      ULift.up (f (barTermEquiv k G n (Rep.toModuleMonoidAlgebra.map
        (GroupBar.Large.boundary.{u,v,w} k G n)
        ((GroupBar.Large.B.{u,v,w} k G (n+1)).ρ.asModuleEquiv.symm x))))
    rw [barTermEquiv_boundary]
  change (ambientEvaluation k G M (n+1) _).down = _
  exact (congrArg (fun a => (ambientEvaluation k G M (n+1) a).down) hφ).trans hd

theorem originalBarComparison : originalBarCoordinatesType.{u,v,w} k G := by
  refine ⟨originalBarCoordinates k G, originalBarCoordinates_apply k G,
    originalBarCoordinates_d k G, ?_⟩
  intro M N b n f g
  simp only [originalBarCoordinates_apply, LinearMap.comp_apply]

private lemma differential_zero_apply (M : Coeff.{u,v,w} k G)
    (f : TupleCochain k G M 0) (g : Fin 1 → G) :
    differential k G M 0 f g =
      MonoidAlgebra.single (g 0) (1 : k) • f Fin.elim0 - f Fin.elim0 := by
  rw [differential_apply, Subsingleton.elim (fun i : Fin 0 => g i.succ) Fin.elim0,
    Subsingleton.elim (fun i : Fin 0 => g i.castSucc) Fin.elim0]
  simp [sub_eq_add_neg]

private def constantCochain (M : Coeff.{u,v,w} k G) :
    (invariantsFunctor k G ⋙ rawInvariantLift.{u,v,w} k).obj M ⟶
      ModuleCat.of k (TupleCochain k G M 0) :=
  ModuleCat.ofHom (LinearMap.pi fun _ => (invariants k G M).subtype.comp ULift.moduleEquiv.toLinearMap)

private def barZeroCyclesMap (h : SquareZero.{u,v,w} k G) (M : Coeff.{u,v,w} k G) :
    (invariantsFunctor k G ⋙ rawInvariantLift.{u,v,w} k).obj M ⟶
      (rawComplex k G h M).cycles 0 := by
  refine (rawComplex k G h M).liftCycles (constantCochain k G M) 1 (by simp) ?_
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  simp only [rawComplex]
  funext g
  change differential k G M 0 (fun _ => m.down.val) g = 0
  rw [differential_zero_apply, m.down.property (g 0), sub_self]

private lemma barZeroCyclesMap_i (h : SquareZero.{u,v,w} k G) (M : Coeff.{u,v,w} k G) :
    barZeroCyclesMap k G h M ≫ (rawComplex k G h M).iCycles 0 = constantCochain k G M := by
  simp [barZeroCyclesMap]

private def barZeroCyclesIso (h : SquareZero.{u,v,w} k G) (M : Coeff.{u,v,w} k G) :
    (invariantsFunctor k G ⋙ rawInvariantLift.{u,v,w} k).obj M ≅ (rawComplex k G h M).cycles 0 := by
  let K := rawComplex k G h M
  let f := barZeroCyclesMap k G h M
  have hf (m : ULift.{v} (invariants k G M)) :
      (K.iCycles 0).hom (f.hom m) = fun _ => m.down.val :=
    congrArg (fun t => ModuleCat.Hom.hom t m) (barZeroCyclesMap_i k G h M)
  refine (LinearEquiv.ofBijective f.hom ⟨?_, ?_⟩).toModuleIso
  · intro m m' e
    apply ULift.ext
    apply Subtype.ext
    exact congrFun ((hf m).symm.trans ((congrArg (K.iCycles 0).hom e).trans (hf m'))) Fin.elim0
  · intro z
    let x : TupleCochain k G M 0 := (K.iCycles 0).hom z
    have hx (g : G) : MonoidAlgebra.single g (1 : k) • x Fin.elim0 = x Fin.elim0 := by
      have hh := congrArg (fun t => ModuleCat.Hom.hom t z)
        (K.iCycles_d 0 1)
      simp only [K, rawComplex] at hh
      have hg := congrFun hh (fun _ => g)
      change differential k G M 0 x (fun _ => g) = 0 at hg
      rwa [differential_zero_apply, sub_eq_zero] at hg
    refine ⟨ULift.up ⟨x Fin.elim0, hx⟩, ?_⟩
    apply (ModuleCat.mono_iff_injective (K.iCycles 0)).mp inferInstance
    change (K.iCycles 0).hom (f.hom (ULift.up ⟨x Fin.elim0, hx⟩)) = x
    rw [hf]
    funext g
    exact congrArg x (Subsingleton.elim Fin.elim0 g)

private lemma barZeroCyclesIso_i (h : SquareZero.{u,v,w} k G) (M : Coeff.{u,v,w} k G) :
    (barZeroCyclesIso k G h M).hom ≫ (rawComplex k G h M).iCycles 0 = constantCochain k G M := by
  change barZeroCyclesMap k G h M ≫ (rawComplex k G h M).iCycles 0 = _
  exact barZeroCyclesMap_i k G h M

/-- In degree zero the bar class of the constant cochain recovers the fixed element. -/
def barDegreeZeroIso (h : SquareZero.{u,v,w} k G) :
    invariantsFunctor k G ⋙ rawInvariantLift.{u,v,w} k ≅ rawCohomology k G h 0 := by
  let K := rawFunctor k G h
  refine NatIso.ofComponents (fun M => barZeroCyclesIso k G h M ≪≫ (K.obj M).isoHomologyπ₀) ?_
  intro M N b
  have hh : (invariantsFunctor k G ⋙ rawInvariantLift.{u,v,w} k).map b ≫ (barZeroCyclesIso k G h N).hom =
      (barZeroCyclesIso k G h M).hom ≫ HomologicalComplex.cyclesMap (K.map b) 0 := by
    rw [← cancel_mono ((K.obj N).iCycles 0)]
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i]
    change (invariantsFunctor k G ⋙ rawInvariantLift.{u,v,w} k).map b ≫
        ((barZeroCyclesIso k G h N).hom ≫ (rawComplex k G h N).iCycles 0) =
      (barZeroCyclesIso k G h M).hom ≫ ((rawComplex k G h M).iCycles 0 ≫ (K.map b).f 0)
    rw [barZeroCyclesIso_i, ← Category.assoc, barZeroCyclesIso_i]
    rfl
  change _ ≫ (_ ≫ (K.obj N).homologyπ 0) =
    ((barZeroCyclesIso k G h M).hom ≫ (K.obj M).homologyπ 0) ≫
      HomologicalComplex.homologyMap (K.map b) 0
  rw [← Category.assoc, hh, Category.assoc, Category.assoc,
    HomologicalComplex.homologyπ_naturality]

theorem barDegreeZero : barDegreeZeroType.{u,v,w} k G := by
  intro h
  refine ⟨barDegreeZeroIso k G h, ?_⟩
  intro M m
  refine ⟨(barZeroCyclesIso k G h M).hom.hom (ULift.up m), ?_, rfl⟩
  exact congrArg (fun f => ModuleCat.Hom.hom f (ULift.up m)) (barZeroCyclesIso_i k G h M)

private def fixedEquiv (M : Coeff.{u,v,w} k G) :
    Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariants k G ((lift k G).obj M) ≃ₗ[k]
      ULift.{max u v} (invariants k G M) where
  toFun m := ULift.up ⟨m.val.down, fun g => congrArg ULift.down (m.property g)⟩
  invFun m := ⟨ULift.up m.down.val, fun g => congrArg ULift.up (m.down.property g)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def invariantsIso : ambientInvariants.{u,v,w} k G ≅
    invariantsFunctor k G ⋙ invariantLift.{u,v,w} k :=
  NatIso.ofComponents (fun M => (fixedEquiv k G M).toModuleIso) (by
    intro M N b
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl)

local instance canonicalDerived (A : Type*) [Category A] [Abelian A] :
    HasDerivedCategory A := HasDerivedCategory.standard A

def derivedZeroIso : derived.{u,v,w} k G 0 ≅
    invariantsFunctor k G ⋙ invariantLift.{u,v,w} k := by
  let F := Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor.{u,v,w} k G
  let := GroupDerivedInvariants.leftExact.{u,v,w} k G
  let := ClassicalDerivedValues.rightZero _ _ F
  exact Functor.isoWhiskerLeft (lift k G)
    (asIso (Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues.rightDegreeZeroUnit F)).symm ≪≫
      invariantsIso k G

theorem invariantsTransport : invariantsTransportType.{u,v,w} k G :=
  ⟨invariantsIso k G, by intros; rfl, ⟨derivedZeroIso k G⟩⟩

theorem injectiveComputation : injectiveComputationType.{u,v,w} k G := by
  refine ⟨fun _ _ _ i hi hI n => GroupDerivedInvariants.injectiveValueIso i hi hI n, ?_⟩
  intro M N I J _ _ i j hi hj hI hJ b g hg n
  exact GroupDerivedInvariants.injectiveValueIso_naturality i hi j hj hI hJ
    ((lift k G).map b) g hg n

open Specs.AdvancedHomologicalAlgebra.ExtShiftedHom
open Specs.AdvancedHomologicalAlgebra.StandardHeart (stalk)
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions (ExtWith homComplex homPreMap homPostMap)

private def barAugmentation : (originalBar k G).X 0 →ₗ[k[G]] trivial k G := by
  let ρ := (GroupBar.Large.B.{u,v,0} k G 0).ρ
  let σ := Representation.trivial k G k
  let aug : Representation.IntertwiningMap ρ σ :=
    ⟨GroupBar.Large.ε.{u,v,0} k G, fun g => by
      apply MonoidAlgebra.lhom_ext'
      rintro ⟨c⟩
      apply LinearMap.ext_ring
      change GroupBar.Large.ε.{u,v,0} k G
          ((GroupBar.Large.B.{u,v,0} k G 0).ρ g (GroupBar.Large.single k G c 1)) =
        GroupBar.Large.ε.{u,v,0} k G (GroupBar.Large.single k G c 1)
      rw [GroupBar.Large.diagonal_action.{u,v,0}, GroupBar.Large.augmentation_single.{u,v,0},
        GroupBar.Large.augmentation_single.{u,v,0}]⟩
  exact Representation.IntertwiningMap.equivLinearMapAsModule ρ σ aug

/-- The original augmented bar resolution, with augmentation in the scalar carrier itself. -/
def barResolution : LeftResolution k[G] (trivial k G) where
  complex := originalBar k G
  ε := barAugmentation k G
  surjective := by
    intro a
    obtain ⟨a, rfl⟩ := (Representation.trivial k G k).asModuleEquiv.symm.surjective a
    obtain ⟨x, hx⟩ := GroupBar.Large.augmentation_surjective.{u,v,0} k G a
    refine ⟨(GroupBar.Large.B.{u,v,0} k G 0).ρ.asModuleEquiv.symm x, ?_⟩
    exact congrArg (trivialElement k G) hx
  exact_zero := by
    ext x
    change (∃ y : (GroupBar.Large.B.{u,v,0} k G 1).ρ.asModule,
      GroupBar.Large.d.{u,v,0} k G 0 y = x) ↔ GroupBar.Large.ε.{u,v,0} k G x = 0
    exact (GroupBar.Large.exact_zero.{u,v,0} k G x).symm
  exact_succ n := by
    ext x
    change (∃ y : (GroupBar.Large.B.{u,v,0} k G (n+2)).ρ.asModule,
      GroupBar.Large.d.{u,v,0} k G (n+1) y = x) ↔ GroupBar.Large.d.{u,v,0} k G n x = 0
    exact (GroupBar.Large.exact_succ.{u,v,0} k G n x).symm

lemma barResolution_isProjective : (barResolution k G).IsProjective := by
  intro n
  change Module.Projective k[G] (GroupBar.Large.B.{u,v,0} k G n).ρ.asModule
  let := GroupBar.Large.degree_free.{u,v,0} k G n
  exact Module.Projective.of_free

theorem originalBarResolution : originalBarResolutionType k G := by
  refine ⟨barResolution k G, rfl, barResolution_isProjective k G, ?_⟩
  intro c
  exact congrArg (trivialElement k G) (GroupBar.Large.augmentation_single.{u,v,0} k G c 1)

/-- Identifies the two carrier presentations of the same augmented trivial module. -/
def trivialLiftIso :
    liftedTrivial.{u,v,w} k G ≅
      Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.trivialModule.{u,v,w} k G := by
  let e₀ := (Representation.trivial k G k).asModuleEquiv
  let e₁ := (Representation.trivial k G (ULift.{max v w} k)).asModuleEquiv
  let er : liftedTrivial.{u,v,w} k G ≃ₗ[k[G]]
      Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.trivialModule.{u,v,w} k G :=
    { toFun x := e₁.symm (ULift.up (e₀ x.down))
      invFun x := ULift.up (e₀.symm (e₁ x).down)
      left_inv x := by rcases x with ⟨x⟩; simp
      right_inv x := by
        simp only [LinearEquiv.apply_symm_apply]
        exact e₁.symm_apply_apply x
      map_add' x y := by
        change e₁.symm (ULift.up (e₀ (x.down + y.down))) =
          e₁.symm (ULift.up (e₀ x.down)) + e₁.symm (ULift.up (e₀ y.down))
        rw [← map_add, map_add]
        rfl
      map_smul' r x := by
        change e₁.symm (ULift.up (e₀ (r • x.down))) =
          r • e₁.symm (ULift.up (e₀ x.down))
        induction r using MonoidAlgebra.induction_linear with
        | zero => simp only [zero_smul, map_zero]; rfl
        | add r s hr hs =>
            simp only [add_smul, map_add]
            exact congrArg₂ (· + ·) hr hs
        | single g b =>
            obtain ⟨x⟩ := x
            obtain ⟨a, rfl⟩ := e₀.symm.surjective x
            change e₁.symm (ULift.up (e₀ (MonoidAlgebra.single g b • trivialElement k G a))) =
              MonoidAlgebra.single g b •
                Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.trivialElement k G a
            rw [trivial_single_smul, GroupDerivedInvariants.trivial_single_smul]
            rfl }
  exact er.toModuleIso

private abbrev ambientTrivial :=
  Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.trivialModule.{u,v,w} k G

private def extChangeTrivial (M : Coeff.{u,v,w} k G) (n : ℕ) :
    Ext (ambientTrivial.{u,v,w} k G) ((lift k G).obj M) (n : ℤ) ≃+ ambientExt k G M n :=
  (Linear.homCongr ℤ ((stalk _).mapIso (trivialLiftIso k G)).symm (Iso.refl _)).toAddEquiv

private lemma extChangeTrivial_apply (M : Coeff.{u,v,w} k G) (n : ℕ)
    (x : Ext (ambientTrivial.{u,v,w} k G) ((lift k G).obj M) (n : ℤ)) :
    extChangeTrivial k G M n x = (stalk _).map (trivialLiftIso k G).hom ≫ x := by
  change ((stalk _).map (trivialLiftIso k G).hom ≫ x) ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- Derived invariants as the shifted Hom of the carrier lifts of the original modules. -/
def derivedExtEquiv (M : Coeff.{u,v,w} k G) (n : ℕ) :
    (derived k G n).obj M ≃+ ambientExt k G M n :=
  (GroupDerivedInvariants.derivedExtEquiv ((lift k G).obj M) n).trans (extChangeTrivial k G M n)

lemma derivedExtEquiv_natural {M N : Coeff.{u,v,w} k G} (b : M ⟶ N)
    (n : ℕ) (x : (derived k G n).obj M) :
    derivedExtEquiv k G N n (((derived k G n).map b).hom x) =
      extMap (𝟙 _) ((lift k G).map b) (n : ℤ) (derivedExtEquiv k G M n x) := by
  simp only [derivedExtEquiv, AddEquiv.trans_apply]
  change extChangeTrivial k G N n (GroupDerivedInvariants.derivedExtEquiv ((lift k G).obj N) n
    (((Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.cohomology k G n).map
      ((lift k G).map b)).hom x)) = _
  rw [GroupDerivedInvariants.derivedExtEquiv_naturality]
  simp only [extChangeTrivial_apply, extMap, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.assoc]
  rfl

/-- The unlifted P103 cycle quotient for every supplied projective resolution. -/
def projectiveEquiv (M : Coeff.{u,v,w} k G) (P : LeftResolution k[G] (trivial k G))
    (hP : P.IsProjective) (n : ℕ) : ExtWith P M n ≃+ (derived k G n).obj M :=
  (ExtShiftedHom.LiftedP103.signedModuleEquiv.{max u v,u,w,0,max (u+1) (v+1) (w+1)}
    k[G] P hP M n).trans (derivedExtEquiv k G M n).symm

open private invariantClassEquiv exists_injectiveExtEquiv
  from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupDerivedInvariants
open private moduleHomFunctorIso moduleHomComplexIso
  from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupCochainComparison

local instance barModuleHasExt :
    HasExt.{max u v w}
      (Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.GroupModule.{u,v,w} k G) :=
  hasExt_of_enoughInjectives _

private lemma derivedExtLinearIso_hom (M : Coeff.{u,v,w} k G) (n : ℕ)
    (x : (derived k G n).obj M) :
    (((GroupCochainComparison.derivedExtLinearIso k G n).hom.app
      ((lift k G).obj M)).hom x).hom =
      GroupDerivedInvariants.derivedExtEquiv ((lift k G).obj M) n x := by
  let N := (lift k G).obj M
  let I := injectiveResolution N
  have hI (q : ℤ) : Injective (I.cochainComplex.X q) := inferInstance
  rw [← GroupDerivedInvariants.derivedExtVia_eq I.ι' inferInstance hI n]
  let z := invariantClassEquiv I.cochainComplex (n : ℤ)
    ((GroupDerivedInvariants.injectiveValueIso I.ι' inferInstance hI n).hom.hom x)
  change (Abelian.Ext.homLinearEquiv (R := k)
    ((Abelian.Ext.homLinearEquiv (R := k)).symm
      (GroupCochainComparison.injectiveClassLinearEquiv k
        (ambientTrivial k G) N I.cochainComplex I.ι' (n : ℤ) z))) =
    (exists_injectiveExtEquiv I.ι' inferInstance hI n).choose z
  rw [LinearEquiv.apply_symm_apply, (exists_injectiveExtEquiv I.ι' inferInstance hI n).choose_spec]
  rfl

open ExtShiftedHom.LiftedP103
open GroupCochainComparison.Large (moduleBarResolution)

private abbrev liftedBarResolution :=
  ExtShiftedHom.LiftedP103.resolution.{max u v,u,w,0} k[G] (barResolution k G)
    (barResolution_isProjective k G)

/-- Send each ambient bar tuple to the lift of the corresponding original
tuple, using the two augmentations of the same bar resolution. -/
private def barResolutionHom :
    ProjectiveResolution.Hom (moduleBarResolution.{u,v,w} k G)
      (liftedBarResolution.{u,v,w} k G) (trivialLiftIso k G).inv where
  hom :=
    { f n := ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp
        (barTermEquiv k G n).toLinearMap)
      comm' i j hij := by
        have h : i = j + 1 := hij.symm
        subst i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact congrArg ULift.up (barTermEquiv_boundary k G j x).symm }
  hom_f_zero_comp_π_f_zero := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have h : (GroupBar.Large.ε.{u,v,0} k G).comp
        (tupleBasisEquiv.{u,v,w} k G 0).toLinearMap = GroupBar.Large.ε.{u,v,w} k G := by
      apply MonoidAlgebra.lhom_ext'
      rintro ⟨c⟩
      apply LinearMap.ext_ring
      change GroupBar.Large.ε.{u,v,0} k G
          (tupleBasisEquiv.{u,v,w} k G 0 (GroupBar.Large.single k G c 1)) =
        GroupBar.Large.ε.{u,v,w} k G (GroupBar.Large.single k G c 1)
      rw [tupleBasisEquiv_single, GroupBar.Large.augmentation_single,
        GroupBar.Large.augmentation_single]
    exact congrArg (fun a => ULift.up (trivialElement k G a))
      (LinearMap.congr_fun h ((GroupBar.Large.B.{u,v,w} k G 0).ρ.asModuleEquiv x))

open GroupCochainComparison.ResolutionBridge
open GroupCochainComparison (derivedExtLinearIso)

private abbrev ambientBarHom (M : Coeff.{u,v,w} k G) :=
  (moduleBarResolution.{u,v,w} k G).complex.linearYonedaObj k ((lift k G).obj M)

/-- A vanishing unsigned coboundary identifies an ambient module-bar cycle. -/
private def ambientBarHomCycle (M : Coeff.{u,v,w} k G) (n : ℕ)
    (f : (moduleBarResolution.{u,v,w} k G).complex.X n ⟶ (lift k G).obj M)
    (hf : (moduleBarResolution.{u,v,w} k G).complex.d (n+1) n ≫ f = 0) :
    (ambientBarHom k G M).cycles n :=
  let K := ambientBarHom k G M
  let D : (K.sc' (n - 1) n (n + 1)).LeftHomologyData :=
    extLeftHomologyData k (Y := (lift k G).obj M) (moduleBarResolution k G) n
  ((K.cyclesIsoSc' (n-1) n (n+1) (prev_up_nat n) (CochainComplex.next ℕ n)).inv.hom)
    (D.cyclesIso.inv.hom ⟨f, hf⟩)

/-- The same cycle in the ambient homogeneous bar cochains. -/
private def ambientBarCycle (M : Coeff.{u,v,w} k G) (n : ℕ)
    (f : (moduleBarResolution.{u,v,w} k G).complex.X n ⟶ (lift k G).obj M)
    (hf : (moduleBarResolution.{u,v,w} k G).complex.d (n+1) n ≫ f = 0) :
    (ambientCochains k G M).cycles n :=
  (HomologicalComplex.cyclesMap (moduleHomComplexIso k G ((lift k G).obj M)).hom n).hom
    (ambientBarHomCycle k G M n f hf)

private lemma ambientBarCycle_i (M : Coeff.{u,v,w} k G) (n : ℕ)
    (f : (moduleBarResolution.{u,v,w} k G).complex.X n ⟶ (lift k G).obj M)
    (hf : (moduleBarResolution.{u,v,w} k G).complex.d (n+1) n ≫ f = 0) :
    ((ambientCochains k G M).iCycles n).hom (ambientBarCycle k G M n f hf) =
      ((moduleHomComplexIso k G ((lift k G).obj M)).hom.f n).hom f := by
  let K := ambientBarHom k G M
  let D : (K.sc' (n - 1) n (n + 1)).LeftHomologyData :=
    extLeftHomologyData k (Y := (lift k G).obj M) (moduleBarResolution k G) n
  let e : K ≅ ambientCochains k G M := moduleHomComplexIso k G ((lift k G).obj M)
  have he : D.cyclesIso.inv ≫
      (K.cyclesIsoSc' (n-1) n (n+1) (prev_up_nat n) (CochainComplex.next ℕ n)).inv ≫
      HomologicalComplex.cyclesMap e.hom n ≫ (ambientCochains k G M).iCycles n = D.i ≫ e.hom.f n := by
    rw [HomologicalComplex.cyclesMap_i, K.cyclesIsoSc'_inv_iCycles_assoc,
      D.cyclesIso_inv_comp_iCycles_assoc]
  exact congrArg (fun (p : D.K ⟶ (ambientCochains k G M).X n) => p.hom ⟨f, hf⟩) he

/-- The ambient bar comparison is induced by the augmented bar resolution and
the degree sign of the signed shifted-Hom convention. -/
private lemma ambientBarClassExt (M : Coeff.{u,v,w} k G) (n : ℕ)
    (f : (moduleBarResolution.{u,v,w} k G).complex.X n ⟶ (lift k G).obj M)
    (hf : (moduleBarResolution.{u,v,w} k G).complex.d (n+1) n ≫ f = 0) :
    ((derivedExtLinearIso k G n).hom.app ((lift k G).obj M)).hom
      (((ambientBarCohomologyIso k G n).inv.app M).hom
        (((ambientCochains k G M).homologyπ n).hom (ambientBarCycle k G M n f hf))) =
      resolutionSign n • (moduleBarResolution k G).extMk f (n+1) rfl hf := by
  let N := (lift k G).obj M
  let K := ambientBarHom k G M
  let D : (K.sc' (n - 1) n (n + 1)).LeftHomologyData :=
    extLeftHomologyData k (Y := N) (moduleBarResolution k G) n
  let z := ambientBarHomCycle k G M n f hf
  let e := derivedExtLinearIso k G n
  let a := homologyExtNatIso k (moduleBarResolution.{u,v,w} k G) n
  let b := Functor.isoWhiskerRight (moduleHomFunctorIso k G)
      (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} k) (.up ℕ) n)
  have hb : (b.hom.app N) ≫ ((ambientBarCohomologyIso k G n).inv.app M) ≫ e.hom.app N =
      a.hom.app N := by
    change (b.hom.app N) ≫ ((e ≪≫ a.symm ≪≫ b).inv.app N) ≫ (e.hom.app N) = a.hom.app N
    simp
  have hc : ((ambientCochains k G M).homologyπ n).hom (ambientBarCycle k G M n f hf) =
      (b.hom.app N).hom ((K.homologyπ n).hom z) := by
    exact (congrArg (fun (p : K.cycles n ⟶ (ambientCochains k G M).homology n) => p.hom z)
      (HomologicalComplex.homologyπ_naturality (moduleHomComplexIso k G N).hom n)).symm
  rw [hc]
  have hd : D.cyclesIso.inv ≫
      (K.cyclesIsoSc' (n-1) n (n+1) (prev_up_nat n) (CochainComplex.next ℕ n)).inv ≫
      K.homologyπ n ≫ a.hom.app N = D.π := by
    change D.cyclesIso.inv ≫
      (K.cyclesIsoSc' (n-1) n (n+1) (prev_up_nat n) (CochainComplex.next ℕ n)).inv ≫
      K.homologyπ n ≫
      (K.homologyIsoSc' (n-1) n (n+1) (prev_up_nat n) (CochainComplex.next ℕ n)).hom ≫
      D.homologyIso.hom = D.π
    rw [HomologicalComplex.π_homologyIsoSc'_hom_assoc, Iso.inv_hom_id_assoc,
      D.homologyπ_comp_homologyIso_hom, Iso.inv_hom_id_assoc]
  exact (congrArg (fun (p : K.homology n ⟶ D.H) => p.hom ((K.homologyπ n).hom z)) hb).trans
    (congrArg (fun (p : D.K ⟶ D.H) => p.hom ⟨f, hf⟩) hd)

private lemma uliftHomology_class.{R,L,V} {r : Type R} [CommRing r]
    (S : ShortComplex (ModuleCat.{V} r))
    (z : S.cycles) (z' : (S.map (ModuleCat.uliftFunctor.{L,V} r)).cycles)
    (hz : (S.map (ModuleCat.uliftFunctor.{L,V} r)).iCycles.hom z' = ULift.up (S.iCycles.hom z)) :
    (S.mapHomologyIso (ModuleCat.uliftFunctor.{L,V} r)).hom.hom ((S.map (ModuleCat.uliftFunctor.{L,V} r)).homologyπ.hom z') =
      ULift.up (S.homologyπ.hom z) := by
  let L := ModuleCat.uliftFunctor.{L,V} r
  let h := S.homologyData.left
  let h' := h.map L
  have hleft : h'.cyclesIso.hom.hom z' = ULift.up (h.cyclesIso.hom.hom z) := by
    apply (ModuleCat.mono_iff_injective h'.i).mp inferInstance
    change (h'.cyclesIso.hom ≫ h'.i).hom z' = ULift.up ((h.cyclesIso.hom ≫ h.i).hom z)
    rwa [h'.cyclesIso_hom_comp_i, h.cyclesIso_hom_comp_i]
  change ((S.map L).homologyπ ≫ (S.mapHomologyIso L).hom).hom z' = _
  rw [h.mapHomologyIso_eq L, Iso.trans_hom, ← Category.assoc, h'.homologyπ_comp_homologyIso_hom]
  change (L.map h.homologyIso.inv).hom (h'.π.hom (h'.cyclesIso.hom.hom z')) = _
  rw [hleft]
  change ULift.up ((h.cyclesIso.hom ≫ (h.π ≫ h.homologyIso.inv)).hom z) = _
  rw [h.π_comp_homologyIso_inv, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

private lemma liftedBarCocycle_condition (M : Coeff.{u,v,w} k G) (n : ℕ)
    (z : cycles (homComplex (barResolution k G).complex M) n) :
    (liftedBarResolution k G).complex.d (n+1) n ≫
      liftCochain.{max u v,u,w,0} k[G] (barResolution k G) M n z.val = 0 := by
  let P := barResolution k G
  let P₁ := leftResolution.{max u v,u,w,0} k[G] P
  have hz := ExtShiftedHom.P103Bridge.cycle_condition P₁ ((lift k G).obj M) n
    (liftCycle.{max u v,u,w,0} k[G] P M n z)
  rw [liftCycle_val] at hz
  exact ModuleCat.hom_ext hz

private lemma signedProjectiveBarClass (M : Coeff.{u,v,w} k G) (n : ℕ)
    (z : cycles (homComplex (barResolution k G).complex M) n) :
    derivedExtEquiv k G M n
        (projectiveEquiv k G M (barResolution k G) (barResolution_isProjective k G) n
          (homologyClass _ n z)) =
      resolutionSign n • ((liftedBarResolution k G).extMk
        (liftCochain.{max u v,u,w,0} k[G] (barResolution k G) M n z.val)
        (n+1) rfl (liftedBarCocycle_condition k G M n z)).hom := by
  simp only [projectiveEquiv, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [signedModuleEquiv_apply, liftExtEquiv_class]
  erw [ExtShiftedHom.P103Bridge.moduleEquiv_class_hom]
  congr 1
  let : HasExt.{max (u+1) (v+1) (w+1)}
      (Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.GroupModule.{u,v,w} k G) :=
    hasExt_of_hasDerivedCategory _
  have hf : (liftedBarResolution k G).complex.d (n+1) n ≫ ModuleCat.ofHom
      (liftCycle.{max u v,u,w,0} k[G] (barResolution k G) M n z).val = 0 := by
    rw [liftCycle_val]
    exact liftedBarCocycle_condition k G M n z
  change (ProjectiveResolution.extMk.{max (u+1) (v+1) (w+1)} (liftedBarResolution k G)
    (ModuleCat.ofHom (liftCycle.{max u v,u,w,0} k[G] (barResolution k G) M n z).val)
    (n+1) rfl hf).hom = _
  simp only [ProjectiveResolution.extMk_hom, liftCycle_val, ModuleCat.ofHom_hom]

private def ambientBarCocycle (M : Coeff.{u,v,w} k G) (n : ℕ)
    (z : cycles (homComplex (barResolution k G).complex M) n) :
    (GroupCochainComparison.ResolutionBridge.homShortComplex k
      (Y := (lift k G).obj M) (moduleBarResolution.{u,v,w} k G) n).moduleCatLeftHomologyData.K :=
  ⟨liftBarHom k G M n z.val, by
    change (moduleBarResolution.{u,v,w} k G).complex.d (n+1) n ≫
      liftBarHom k G M n z.val = 0
    change (moduleBarResolution.{u,v,w} k G).complex.d (n+1) n ≫
      ((barResolutionHom.{u,v,w} k G).hom.f n ≫
        liftCochain.{max u v,u,w,0} k[G] (barResolution k G) M n z.val) = 0
    rw [← (barResolutionHom.{u,v,w} k G).hom.comm_assoc,
      liftedBarCocycle_condition, comp_zero]⟩

private lemma extChangeTrivial_signedBarClass (M : Coeff.{u,v,w} k G) (n : ℕ)
    (z : cycles (homComplex (barResolution k G).complex M) n) :
    extChangeTrivial k G M n
      ((GroupCochainComparison.ResolutionBridge.cyclesExtMap k
        (moduleBarResolution.{u,v,w} k G) n (ambientBarCocycle k G M n z)).hom) =
      resolutionSign n • ((liftedBarResolution k G).extMk
        (liftCochain.{max u v,u,w,0} k[G] (barResolution k G) M n z.val)
        (n+1) rfl (liftedBarCocycle_condition k G M n z)).hom := by
  rw [cyclesExtMap_apply]
  let c := ambientBarCocycle k G M n z
  change extChangeTrivial k G M n (Abelian.Ext.homAddEquiv
    (resolutionSign n • (moduleBarResolution k G).extMk c.val (n+1) rfl c.property)) = _
  rw [map_zsmul, map_zsmul]
  congr 1
  let f := liftCochain.{max u v,u,w,0} k[G] (barResolution k G) M n z.val
  have h := (liftedBarResolution k G).mk₀_comp_extMk f (n+1) rfl
    (liftedBarCocycle_condition k G M n z) (barResolutionHom.{u,v,w} k G)
  have hh := congrArg Abelian.Ext.hom h
  rw [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, ShiftedHom.mk₀_comp] at hh
  change extChangeTrivial k G M n ((moduleBarResolution k G).extMk
    c.val (n+1) rfl c.property).hom = _
  have hh' : ((moduleBarResolution k G).extMk c.val (n+1) rfl c.property).hom =
      (stalk _).map (trivialLiftIso k G).inv ≫
        ((liftedBarResolution k G).extMk f (n+1) rfl
          (liftedBarCocycle_condition k G M n z)).hom := hh.symm
  rw [extChangeTrivial_apply, hh', ← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

private def originalHomLiftEquiv (M : Coeff.{u,v,w} k G) :
    OriginalHom k G M ≃+ (liftedTrivial.{u,v,w} k G ⟶ (lift k G).obj M) where
  toFun := liftOriginalHom k G M
  invFun f := ULift.moduleEquiv.toLinearMap.comp
    (f.hom.comp ULift.moduleEquiv.symm.toLinearMap)
  left_inv f := by ext a; rfl
  right_inv f := by ext a; rfl
  map_add' _ _ := rfl

private def zeroExtEquiv (M : Coeff.{u,v,w} k G) :
    (liftedTrivial.{u,v,w} k G ⟶ (lift k G).obj M) ≃+ ambientExt k G M 0 :=
  (ExtShiftedHom.zero _ (liftedTrivial.{u,v,w} k G) ((lift k G).obj M)).choose

private lemma zeroExtEquiv_apply (M : Coeff.{u,v,w} k G)
    (f : liftedTrivial.{u,v,w} k G ⟶ (lift k G).obj M) :
    zeroExtEquiv k G M f = zeroHom f :=
  (ExtShiftedHom.zero _ _ _).choose_spec f

/-- The comparison in degree zero is evaluation at the original scalar 1. -/
def degreeZeroEquiv (M : Coeff.{u,v,w} k G) : (derived k G 0).obj M ≃+ invariants k G M :=
  (derivedExtEquiv k G M 0).trans ((zeroExtEquiv k G M).symm.trans
    ((originalHomLiftEquiv k G M).symm.trans (evaluationEquiv k G M).toAddEquiv))

lemma degreeZeroEquiv_evaluation (M : Coeff.{u,v,w} k G) (f : OriginalHom k G M) :
    degreeZeroEquiv k G M ((derivedExtEquiv k G M 0).symm
      (zeroHom (liftOriginalHom k G M f))) = evaluationEquiv k G M f := by
  rw [← zeroExtEquiv_apply]
  change (evaluationEquiv k G M)
    ((originalHomLiftEquiv k G M).symm ((zeroExtEquiv k G M).symm
      (derivedExtEquiv k G M 0
        ((derivedExtEquiv k G M 0).symm (zeroExtEquiv k G M
          (originalHomLiftEquiv k G M f)))))) = _
  simp only [AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]

lemma degreeZeroEquiv_natural {M N : Coeff.{u,v,w} k G} (b : M ⟶ N)
    (x : (derived k G 0).obj M) :
    degreeZeroEquiv k G N (((derived k G 0).map b).hom x) =
      ((invariantsFunctor k G).map b).hom (degreeZeroEquiv k G M x) := by
  let c := ((originalHomLiftEquiv k G M).trans (zeroExtEquiv k G M)).trans
    (derivedExtEquiv k G M 0).symm
  obtain ⟨f, rfl⟩ := c.surjective x
  have hcf : c f = (derivedExtEquiv k G M 0).symm (zeroHom (liftOriginalHom k G M f)) := by
    exact congrArg (derivedExtEquiv k G M 0).symm
      (zeroExtEquiv_apply k G M (liftOriginalHom k G M f))
  have hb : derivedExtEquiv k G N 0 (((derived k G 0).map b).hom (c f)) =
      zeroHom (liftOriginalHom k G N (b.hom.comp f)) := by
    rw [derivedExtEquiv_natural, hcf, AddEquiv.apply_symm_apply]
    have hh := ExtShiftedHom.zero_natural _ (liftedTrivial.{u,v,w} k G)
      (liftedTrivial.{u,v,w} k G) ((lift k G).obj M) ((lift k G).obj N)
      (𝟙 _) ((lift k G).map b) (liftOriginalHom k G M f)
    rw [Category.id_comp] at hh
    exact hh.symm
  have hp := congrArg (derivedExtEquiv k G N 0).symm hb
  rw [AddEquiv.symm_apply_apply] at hp
  rw [hp, hcf, degreeZeroEquiv_evaluation, degreeZeroEquiv_evaluation]
  rfl

theorem projectiveComputation : projectiveComputationType.{u,v,w} k G := by
  let C := ExtShiftedHom.LiftedP103.independentComparison.{max u v,u,w,0,max (u+1) (v+1) (w+1)} k[G]
  refine ⟨trivialLiftIso k G, C, derivedExtEquiv k G, fun a => rfl,
    fun _ _ b n x => derivedExtEquiv_natural k G b n x, projectiveEquiv k G, ?_, ?_, ?_⟩
  · intro M P hP n x
    exact (derivedExtEquiv k G M n).apply_symm_apply _
  · intro M N b P Q hP hQ g hg n x
    apply (derivedExtEquiv k G N n).injective
    rw [derivedExtEquiv_natural]
    simp only [projectiveEquiv, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
    have h := C.natural (trivial k G) (trivial k G) M N P Q hP hQ (𝟙 _) b g hg n x
    have he : (firstLift.{max u v,u,w,0} k[G]).map (𝟙 (trivial k G)) =
        𝟙 (liftedTrivial.{u,v,w} k G) :=
      (firstLift.{max u v,u,w,0} k[G]).map_id _
    rw [he] at h
    exact h
  · refine ⟨degreeZeroEquiv k G, ?_, fun _ _ b x => degreeZeroEquiv_natural k G b x, ?_⟩
    · intro M f
      rw [degreeZeroEquiv_evaluation]
      rfl
    · intro M P hP x f hf
      have hh := C.zero (trivial k G) M P hP x f hf
      change C.equiv (trivial k G) M P hP 0 (homologyClass _ 0 x) =
        zeroHom (liftOriginalHom k G M f) at hh
      change (degreeZeroEquiv k G M ((derivedExtEquiv k G M 0).symm
        (C.equiv (trivial k G) M P hP 0 (homologyClass _ 0 x)))).val = _
      rw [hh, degreeZeroEquiv_evaluation]
      rfl

/-- On the original augmented bar resolution, the projective computation and
the comparison with tuple cochains send a cocycle to the same class. -/
theorem rawCohomologyIso_projectiveClass (M : Coeff.{u,v,w} k G) (n : ℕ)
    (z : cycles (homComplex (barResolution k G).complex M) n)
    (y : (rawComplex k G (squareZero k G) M).cycles n)
    (hy : ((rawComplex k G (squareZero k G) M).iCycles n).hom y =
      originalBarCoordinates k G M n z.val) :
    ((rawCohomologyIso k G n).hom.app M).hom
      (projectiveEquiv k G M (barResolution k G) (barResolution_isProjective k G) n
        (homologyClass _ n z)) =
      ULift.up (((rawComplex k G (squareZero k G) M).homologyπ n).hom y) := by
  let f := ambientBarCocycle k G M n z
  let t := ambientBarCycle k G M n f.val f.property
  let K := ambientCochains k G M
  let a := ambientBarCohomologyIso k G n
  have hpre : (a.inv.app M).hom ((K.homologyπ n).hom t) =
      projectiveEquiv k G M (barResolution k G) (barResolution_isProjective k G) n
        (homologyClass _ n z) := by
    apply (derivedExtEquiv k G M n).injective
    rw [signedProjectiveBarClass]
    change extChangeTrivial k G M n
      (GroupDerivedInvariants.derivedExtEquiv ((lift k G).obj M) n _) = _
    rw [← derivedExtLinearIso_hom]
    dsimp only [a, t]
    rw [ambientBarClassExt]
    exact extChangeTrivial_signedBarClass k G M n z
  rw [← hpre]
  let e := (barIso k G).hom.app M
  let Kraw := rawComplex k G (squareZero k G) M
  let y' := (HomologicalComplex.cyclesMap e n).hom t
  have hcycle : (((rawLifted k G (squareZero k G)).obj M).iCycles n).hom y' =
      ULift.up ((Kraw.iCycles n).hom y) := by
    have h := congrArg (fun (p : K.cycles n ⟶ _) => p.hom t)
      (HomologicalComplex.cyclesMap_i e n)
    have h' : (((rawLifted k G (squareZero k G)).obj M).iCycles n).hom y' =
        (e.f n).hom ((K.iCycles n).hom t) := h
    refine h'.trans ?_
    change (e.f n).hom ((K.iCycles n).hom (ambientBarCycle k G M n f.val f.property)) = _
    rw [ambientBarCycle_i]
    change ULift.up (originalBarCoordinates k G M n z.val) = ULift.up ((Kraw.iCycles n).hom y)
    exact congrArg ULift.up hy.symm
  have ha : (a.hom.app M).hom ((a.inv.app M).hom ((K.homologyπ n).hom t)) =
      (K.homologyπ n).hom t :=
    congrArg (fun (p : K.homology n ⟶ K.homology n) => p.hom ((K.homologyπ n).hom t))
      (a.app M).inv_hom_id
  change ((rawHomologyLiftIso k G n).hom.app M).hom
    ((HomologicalComplex.homologyMap e n).hom
      ((a.hom.app M).hom ((a.inv.app M).hom ((K.homologyπ n).hom t)))) = _
  rw [ha]
  have h := congrArg (fun (p : K.cycles n ⟶ _) => p.hom t)
    (HomologicalComplex.homologyπ_naturality e n)
  have hh : (HomologicalComplex.homologyMap e n).hom ((K.homologyπ n).hom t) =
      (((rawLifted k G (squareZero k G)).obj M).homologyπ n).hom y' := h
  rw [hh]
  exact uliftHomology_class (Kraw.sc n) y y' hcycle

/-- Every original projective bar cocycle has the indicated tuple representative
in the unlifted coefficient complex. -/
theorem rawBarRepresentative (M : Coeff.{u,v,w} k G) (n : ℕ)
    (z : cycles (homComplex (barResolution k G).complex M) n) :
    ∃ y : (rawComplex k G (squareZero k G) M).cycles n,
      ((rawComplex k G (squareZero k G) M).iCycles n).hom y =
        originalBarCoordinates k G M n z.val := by
  let S := (rawComplex k G (squareZero k G) M).sc n
  let f := originalBarCoordinates k G M n z.val
  have hf : S.g.hom f = 0 := by
    change ((rawComplex k G (squareZero k G) M).d n ((ComplexShape.up ℕ).next n)).hom f = 0
    rw [CochainComplex.next]
    simp only [rawComplex, CochainComplex.of_d]
    change differential k G M n (originalBarCoordinates k G M n z.val) = 0
    have hz := z.property
    change ((homComplex (barResolution k G).complex M).d n
      ((ComplexShape.up ℕ).next n)).hom z.val = 0 at hz
    rw [CochainComplex.next] at hz
    change z.val.comp ((originalBar k G).d (n+1) n).hom = 0 at hz
    rw [← originalBarCoordinates_d, hz, map_zero]
  refine ⟨S.moduleCatCyclesIso.inv.hom ⟨f, hf⟩, ?_⟩
  exact congrArg (fun (p : S.moduleCatLeftHomologyData.K ⟶ S.X₂) => p.hom ⟨f, hf⟩)
    S.moduleCatCyclesIso_inv_iCycles

set_option maxRecDepth 3000 in
/-- The normalized derived-to-bar map in degree zero is evaluation at one,
with a fixed element represented by its constant cochain. -/
theorem rawCohomologyIso_degreeZero (M : Coeff.{u,v,w} k G)
    (x : (derived k G 0).obj M) :
    ((rawCohomologyIso k G 0).hom.app M).hom x =
      ULift.up (((barDegreeZeroIso k G (squareZero k G)).hom.app M).hom
        (ULift.up (degreeZeroEquiv k G M x))) := by
  let P := barResolution k G
  let f := (evaluationEquiv k G M).symm (degreeZeroEquiv k G M x)
  have hf : (f.comp P.ε).comp (P.complex.d 1 0).hom = 0 := by
    apply LinearMap.ext
    intro b
    have hb : (P.complex.d 1 0).hom b ∈ LinearMap.ker P.ε := by
      rw [← P.exact_zero]
      exact ⟨b, rfl⟩
    change f (P.ε ((P.complex.d 1 0).hom b)) = 0
    rw [LinearMap.mem_ker.mp hb, map_zero]
  let z : cycles (homComplex P.complex M) 0 := ⟨f.comp P.ε, by
    change ((homComplex P.complex M).d 0 ((ComplexShape.up ℕ).next 0)).hom _ = 0
    rw [CochainComplex.next]
    exact hf⟩
  let p := projectiveEquiv k G M P (barResolution_isProjective k G) 0
    (homologyClass _ 0 z)
  have hp : p = x := by
    apply (degreeZeroEquiv k G M).injective
    change degreeZeroEquiv k G M ((derivedExtEquiv k G M 0).symm
      (signedModuleEquiv.{max u v,u,w,0,max (u+1) (v+1) (w+1)} k[G] P
        (barResolution_isProjective k G) M 0 (homologyClass _ 0 z))) = _
    rw [signedModuleEquiv_zero _ _ _ _ z f rfl]
    change degreeZeroEquiv k G M ((derivedExtEquiv k G M 0).symm
      (zeroHom (liftOriginalHom k G M f))) = _
    rw [degreeZeroEquiv_evaluation]
    exact (evaluationEquiv k G M).apply_symm_apply _
  let K := rawComplex k G (squareZero k G) M
  let y := (barZeroCyclesIso k G (squareZero k G) M).hom.hom
    (ULift.up (degreeZeroEquiv k G M x))
  have hy : (K.iCycles 0).hom y = originalBarCoordinates k G M 0 z.val := by
    have h := congrArg (fun (a : (invariantsFunctor k G ⋙ rawInvariantLift.{u,v,w} k).obj M ⟶
        K.X 0) => a.hom (ULift.up (degreeZeroEquiv k G M x)))
      (barZeroCyclesIso_i k G (squareZero k G) M)
    change (K.iCycles 0).hom y = (fun _ => (degreeZeroEquiv k G M x).val) at h
    rw [h]
    funext g
    rw [originalBarCoordinates_apply]
    change (degreeZeroEquiv k G M x).val = f (P.ε (basisElement k G 0 (Fin.partialProd g)))
    rw [show P.ε (basisElement k G 0 (Fin.partialProd g)) = trivialElement k G 1 from
      congrArg (trivialElement k G) (GroupBar.Large.augmentation_single.{u,v,0} k G
        (Fin.partialProd g) 1)]
    exact (congrArg Subtype.val ((evaluationEquiv k G M).apply_symm_apply
      (degreeZeroEquiv k G M x))).symm
  exact (congrArg ((rawCohomologyIso k G 0).hom.app M).hom hp.symm).trans
    (rawCohomologyIso_projectiveClass k G M 0 z y hy)

theorem resolutionLifts : resolutionLiftsType.{u,v,w} k G := by
  refine ⟨?_, ?_⟩
  · intro P Q hQ
    exact P103.Ch10.Comparison.chain_exists k[G] _ _ Q P hQ LinearMap.id
  · intro M N b I J _ i j hi hJ
    let := hi
    let : J.IsKInjective := (BoundedKModels.kInjective_iff _ _).mp
      (BoundedKModels.boundedBelow_injective _ J 0
        (fun q hq => J.isZero_of_isStrictlyGE 0 q hq) hJ)
    exact ExtShiftedHom.injective_lift _ _ I J i j ((lift k G).map b)

end AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients

namespace AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.IndependentResolution

open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients
open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.IndependentResolution
open TorBalance (AugmentedResolution LinearChainMap)
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions (ExtWith homComplex homPreMap homPostMap)

universe u v w w' w'' a b c
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

theorem resolutionLifts : Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.IndependentResolution.resolutionLiftsExpected.{u,v,a,b} := by
  intro k G _ _ P Q
  exact LinearChainMap.exists_augmentedLift Q P LinearMap.id

private lemma homMap_homotopic {P : Resolution.{u,v,a} k G} {Q : Resolution.{u,v,b} k G}
    {M : Coeff.{u,v,w} k G} {N : Coeff.{u,v,w'} k G} {g g' : LinearChainMap Q.complex P.complex}
    (h : g.Homotopic g') (f : M →ₗ[k[G]] N) :
    (homMap k G (P := P) (Q := Q) g f).Homotopic (homMap k G g' f) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨fun i j =>
    { toFun z := f.comp (z.comp (s j i))
      map_add' z z' := by
        change f.comp ((z + z').comp (s j i)) = _
        rw [LinearMap.add_comp, LinearMap.comp_add]
      map_smul' r z := by
        change f.comp ((r • z).comp (s j i)) = _
        rw [LinearMap.smul_comp, LinearMap.comp_smul]
        rfl }, ?_⟩
  intro n
  apply LinearMap.ext
  intro z
  change P.complex.X n →ₗ[k[G]] M at z
  apply LinearMap.ext
  intro x
  let d := ComplexShape.down ℕ
  change f (z (g.app n x)) =
    f (z ((P.complex.d (d.prev n) n).hom (s n (d.prev n) x))) +
    f (z (s (d.next n) n ((Q.complex.d n (d.next n)).hom x))) + f (z (g'.app n x))
  rw [LinearMap.congr_fun (hs n) x]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add, add_comm, d]

private lemma homMap_comp {P : Resolution.{u,v,a} k G} {Q : Resolution.{u,v,b} k G}
    {R : Resolution.{u,v,c} k G} {M : Coeff.{u,v,w} k G} {N : Coeff.{u,v,w'} k G}
    {L : Coeff.{u,v,w''} k G} (g : LinearChainMap Q.complex P.complex)
    (h : LinearChainMap R.complex Q.complex) (f : M →ₗ[k[G]] N) (f' : N →ₗ[k[G]] L) :
    (homMap k G (P := Q) (Q := R) h f').comp (homMap k G (P := P) (Q := Q) g f) =
      homMap k G (g.comp h) (f'.comp f) := by
  apply LinearChainMap.eq_of_app_eq
  funext n
  rfl

private lemma homMap_id (P : Resolution.{u,v,a} k G) (M : Coeff.{u,v,w} k G) :
    homMap k G (P := P) (Q := P) (LinearChainMap.id P.complex) (LinearMap.id : M →ₗ[k[G]] M) =
      LinearChainMap.id (homComplex P.complex M) := by
  apply LinearChainMap.eq_of_app_eq
  funext n
  rfl

private lemma homologyMap_eq {P : Resolution.{u,v,a} k G} {Q : Resolution.{u,v,b} k G}
    {M : Coeff.{u,v,w} k G} {N : Coeff.{u,v,w'} k G} {g g' : LinearChainMap Q.complex P.complex}
    (hg : OriginalLift k G (P := P) (Q := Q) g) (hg' : OriginalLift k G (P := P) (Q := Q) g')
    (f : M →ₗ[k[G]] N) (n : ℕ) :
    (homMap k G (P := P) (Q := Q) g f).homologyMap n =
      (homMap k G (P := P) (Q := Q) g' f).homologyMap n :=
  congrFun (LinearChainMap.homologyMap_eq_of_homotopic
    (homMap_homotopic k G (P := P) (Q := Q)
      (LinearChainMap.augmentedLifts_homotopic Q P LinearMap.id g g' hg hg') f)) n

private lemma homMap_quasiIso {P : Resolution.{u,v,a} k G} {Q : Resolution.{u,v,b} k G}
    {g : LinearChainMap Q.complex P.complex} (hg : OriginalLift k G (P := P) (Q := Q) g)
    (M : Coeff.{u,v,w} k G) :
    (homMap k G (P := P) (Q := Q) g (LinearMap.id : M →ₗ[k[G]] M)).IsQuasiIso := by
  obtain ⟨h, hh⟩ := resolutionLifts k G Q P
  apply LinearChainMap.isQuasiIso_of_homology_inverse _
    (homMap k G (P := Q) (Q := P) h (LinearMap.id : M →ₗ[k[G]] M))
  · intro n
    rw [homMap_comp, LinearMap.id_comp, ← LinearChainMap.homologyMap_id (K := homComplex P.complex M) n,
      ← homMap_id k G P M]
    exact homologyMap_eq k G (P := P) (Q := P) (fun z => (hg (h.app 0 z)).trans (hh z))
      (fun _ => rfl) LinearMap.id n
  · intro n
    rw [homMap_comp, LinearMap.id_comp, ← LinearChainMap.homologyMap_id (K := homComplex Q.complex M) n,
      ← homMap_id k G Q M]
    exact homologyMap_eq k G (P := Q) (Q := Q) (fun z => (hh (g.app 0 z)).trans (hg z))
      (fun _ => rfl) LinearMap.id n

/-- Precomposition with any augmented resolution lift induces the same
equivalence on the original Hom quotients. -/
def compare (B : LeftResolution k[G] (trivial k G)) (hB : B.IsProjective) :
    Comparison.{u,v,w,a} k G B hB := by
  let Q := AugmentedResolution.ofP103 B hB
  let liftTo (P : Resolution.{u,v,a} k G) := (resolutionLifts k G P Q).choose
  have hLift (P : Resolution.{u,v,a} k G) := (resolutionLifts k G P Q).choose_spec
  refine ⟨fun P M n => ((homMap k G (P := P) (Q := Q) (liftTo P) LinearMap.id).homologyEquiv
    (homMap_quasiIso k G (P := P) (Q := Q) (hLift P) M) n).toAddEquiv, ?_⟩
  intro P g hg M n z
  exact LinearMap.congr_fun (homologyMap_eq k G (P := P) (Q := Q) (hLift P) hg LinearMap.id n) z

lemma compare_natural (B : LeftResolution k[G] (trivial k G)) (hB : B.IsProjective)
    (P : Resolution.{u,v,a} k G) (Q : Resolution.{u,v,b} k G)
    (M : Coeff.{u,v,w} k G) (N : Coeff.{u,v,w'} k G) (f : M →ₗ[k[G]] N)
    (g : LinearChainMap Q.complex P.complex) (hg : OriginalLift k G g)
    (n : ℕ) (z : Cohomology k G P M n) :
    (compare k G B hB).equiv Q N n ((homMap k G g f).homologyMap n z) =
      (homMap k G (P := AugmentedResolution.ofP103 B hB) (Q := AugmentedResolution.ofP103 B hB)
        (LinearChainMap.id B.complex) f).homologyMap n ((compare k G B hB).equiv P M n z) := by
  let B₀ := AugmentedResolution.ofP103 B hB
  obtain ⟨l, hl⟩ := resolutionLifts k G Q B₀
  obtain ⟨j, hj⟩ := resolutionLifts k G P B₀
  rw [(compare k G B hB).precompose Q l hl, (compare k G B hB).precompose P j hj]
  have h₁ := LinearChainMap.homologyMap_comp
    (homMap k G (P := Q) (Q := B₀) l (LinearMap.id : N →ₗ[k[G]] N))
    (homMap k G (P := P) (Q := Q) g f) n
  have h₂ := LinearChainMap.homologyMap_comp
    (homMap k G (P := B₀) (Q := B₀) (LinearChainMap.id B.complex) f)
    (homMap k G (P := P) (Q := B₀) j (LinearMap.id : M →ₗ[k[G]] M)) n
  rw [← LinearMap.comp_apply, ← h₁, homMap_comp, LinearMap.id_comp]
  rw [← LinearMap.comp_apply, ← h₂, homMap_comp, LinearMap.comp_id]
  exact LinearMap.congr_fun (homologyMap_eq k G (P := P) (Q := B₀)
    (fun x => (hg (l.app 0 x)).trans (hl x)) (fun x => hj x) f n) z

private lemma homologyMap_ofHom {B B' : LeftResolution k[G] (trivial k G)}
    (hB : B.IsProjective) (hB' : B'.IsProjective)
    {M N : Coeff.{u,v,w} k G} (g : B'.complex ⟶ B.complex) (f : M →ₗ[k[G]] N) (n : ℕ) :
    (homMap k G (P := AugmentedResolution.ofP103 B hB) (Q := AugmentedResolution.ofP103 B' hB')
      (LinearChainMap.ofHom g) f).homologyMap n =
      P103.Specs.Ch10.Complexes.homologyMap (homPreMap g M ≫ homPostMap B'.complex f) n := by
  apply (cycleBoundaries (homComplex B.complex M) n).quot_hom_ext
  intro z
  rfl

lemma compare_ordinary (B B' : LeftResolution k[G] (trivial k G))
    (hB : B.IsProjective) (hB' : B'.IsProjective)
    (P : Resolution.{u,v,a} k G) (g : LinearChainMap B'.complex P.complex)
    (hg : OriginalLift k G (P := P) (Q := AugmentedResolution.ofP103 B' hB') g)
    (h : B'.complex ⟶ B.complex) (hh : ChainLift B' B LinearMap.id h)
    (M : Coeff.{u,v,w} k G) (n : ℕ) (z : Cohomology k G P M n) :
    (homMap k G (P := P) (Q := AugmentedResolution.ofP103 B' hB') g
      (LinearMap.id : M →ₗ[k[G]] M)).homologyMap n z =
    P103.Specs.Ch10.Complexes.homologyMap (homPreMap h M ≫ homPostMap B'.complex LinearMap.id) n
      ((compare k G B hB).equiv P M n z) := by
  let B₀ := AugmentedResolution.ofP103 B hB
  let B₀' := AugmentedResolution.ofP103 B' hB'
  obtain ⟨l, hl⟩ := resolutionLifts k G P B₀
  rw [(compare k G B hB).precompose P l hl, ← homologyMap_ofHom k G hB hB']
  have hc := LinearChainMap.homologyMap_comp
    (homMap k G (P := B₀) (Q := B₀') (LinearChainMap.ofHom h) (LinearMap.id : M →ₗ[k[G]] M))
    (homMap k G (P := P) (Q := B₀) l (LinearMap.id : M →ₗ[k[G]] M)) n
  change (homMap k G (P := P) (Q := B₀') g (LinearMap.id : M →ₗ[k[G]] M)).homologyMap n z =
    (homMap k G (P := B₀) (Q := B₀') (LinearChainMap.ofHom h) (LinearMap.id : M →ₗ[k[G]] M)).homologyMap n
      ((homMap k G (P := P) (Q := B₀) l (LinearMap.id : M →ₗ[k[G]] M)).homologyMap n z)
  rw [← LinearMap.comp_apply, ← hc, homMap_comp, LinearMap.id_comp]
  exact LinearMap.congr_fun (homologyMap_eq k G (P := P) (Q := B₀') hg
    (fun x => (hl ((h.f 0).hom x)).trans (LinearMap.congr_fun hh x)) LinearMap.id n) z

lemma compare_zero (B : LeftResolution k[G] (trivial k G)) (hB : B.IsProjective)
    (P : Resolution.{u,v,a} k G) (M : Coeff.{u,v,w} k G)
    (z : cycles (homComplex P.complex M) 0) (f : OriginalHom k G M) (hf : f.comp P.ε = z.val) :
    ∃ z' : cycles (homComplex B.complex M) 0,
      f.comp B.ε = z'.val ∧
      (compare k G B hB).equiv P M 0 (homologyClass _ 0 z) = homologyClass _ 0 z' := by
  let B₀ := AugmentedResolution.ofP103 B hB
  obtain ⟨l, hl⟩ := resolutionLifts k G P B₀
  let e := homMap k G (P := P) (Q := B₀) l (LinearMap.id : M →ₗ[k[G]] M)
  refine ⟨e.cyclesMap 0 z, ?_, (compare k G B hB).precompose P l hl _ _ _⟩
  apply LinearMap.ext
  intro x
  change f (B.ε x) = (show P.complex.X 0 →ₗ[k[G]] M from z.val) (l.app 0 x)
  rw [← hf]
  exact congrArg f (hl x).symm

end AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.IndependentResolution

namespace AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients

open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients
open Specs.AdvancedHomologicalAlgebra.UniversalDeltaFunctors
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues (rightDegreeZeroUnit)
open UniversalDeltaFunctors

attribute [local instance] HasDerivedCategory.standard

section Delta
variable {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
  {T U V : CohomologicalSystem A B}

private def deltaId (T : CohomologicalSystem A B) : CohomologicalMorphism T T where
  component n := 𝟙 _
  comm := by intros; simp

private def deltaComp (f : CohomologicalMorphism T U) (g : CohomologicalMorphism U V) :
    CohomologicalMorphism T V where
  component n := f.component n ≫ g.component n
  comm h n := by
    simp only [NatTrans.comp_app]
    rw [← Category.assoc, f.comm, Category.assoc, g.comm, Category.assoc]

private structure DeltaIso (T U : CohomologicalSystem A B) where
  iso : ∀ n, T.value n ≅ U.value n
  boundary : ∀ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ),
    T.δ hS n ≫ (iso (n + 1)).hom.app S.X₁ = (iso n).hom.app S.X₃ ≫ U.δ hS n

private def deltaIso (hT : IsCohomological T) (hU : IsCohomological U)
    (uT : IsUniversalCohomological T) (uU : IsUniversalCohomological U)
    (e : T.value 0 ≅ U.value 0) :
    { D : DeltaIso T U // (D.iso 0).hom = e.hom } := by
  let h := uT U hU e.hom
  let h' := uU T hT e.inv
  let f := h.choose
  let g := h'.choose
  have hf : f.component 0 = e.hom := h.choose_spec.1
  have hg : g.component 0 = e.inv := h'.choose_spec.1
  have hfg : deltaComp f g = deltaId T :=
    ((uT T hT (𝟙 _)).unique (by change f.component 0 ≫ g.component 0 = _; simp [hf, hg]) rfl)
  have hgf : deltaComp g f = deltaId U :=
    ((uU U hU (𝟙 _)).unique (by change g.component 0 ≫ f.component 0 = _; simp [hf, hg]) rfl)
  exact ⟨⟨fun n => ⟨f.component n, g.component n,
    congrArg (fun h : CohomologicalMorphism T T => h.component n) hfg,
    congrArg (fun h : CohomologicalMorphism U U => h.component n) hgf⟩, f.comm⟩, hf⟩

private def snakesMap {ι : Type*} {c : ComplexShape ι}
    {S S' : ShortComplex (HomologicalComplex B c)} (hS : S.ShortExact) (hS' : S'.ShortExact)
    (f : S ⟶ S') (i j : ι) (hij : c.Rel i j) :
    HomologicalComplex.HomologySequence.snakeInput hS i j hij ⟶
      HomologicalComplex.HomologySequence.snakeInput hS' i j hij where
  f₀ := (HomologicalComplex.homologyFunctor B c i).mapShortComplex.map f
  f₁ := (HomologicalComplex.opcyclesFunctor B c i).mapShortComplex.map f
  f₂ := (HomologicalComplex.cyclesFunctor B c j).mapShortComplex.map f
  f₃ := (HomologicalComplex.homologyFunctor B c j).mapShortComplex.map f
  comm₀₁ := by
    ext
    all_goals first
      | exact (HomologicalComplex.natTransHomologyι B c i).naturality f.τ₁
      | exact (HomologicalComplex.natTransHomologyι B c i).naturality f.τ₂
      | exact (HomologicalComplex.natTransHomologyι B c i).naturality f.τ₃
  comm₁₂ := by
    ext
    all_goals first
      | exact (HomologicalComplex.natTransOpCyclesToCycles B c i j).naturality f.τ₁
      | exact (HomologicalComplex.natTransOpCyclesToCycles B c i j).naturality f.τ₂
      | exact (HomologicalComplex.natTransOpCyclesToCycles B c i j).naturality f.τ₃
  comm₂₃ := by
    ext
    all_goals first
      | exact (HomologicalComplex.natTransHomologyπ B c j).naturality f.τ₁
      | exact (HomologicalComplex.natTransHomologyπ B c j).naturality f.τ₂
      | exact (HomologicalComplex.natTransHomologyπ B c j).naturality f.τ₃

private lemma complexBoundary_natural {ι : Type*} {c : ComplexShape ι}
    {S S' : ShortComplex (HomologicalComplex B c)} (hS : S.ShortExact) (hS' : S'.ShortExact)
    (f : S ⟶ S') (i j : ι) (hij : c.Rel i j) :
    HomologicalComplex.homologyMap f.τ₃ i ≫ hS'.δ i j hij =
      hS.δ i j hij ≫ HomologicalComplex.homologyMap f.τ₁ j :=
  (ShortComplex.SnakeInput.naturality_δ (snakesMap hS hS' f i j hij)).symm

private def complexSystem (F : A ⥤ CochainComplex B ℕ) [F.Additive]
    (shortExact : ∀ {S : ShortComplex A}, S.ShortExact → (S.map F).ShortExact) :
    CohomologicalSystem A B where
  value n := F ⋙ HomologicalComplex.homologyFunctor B (.up ℕ) n
  δ h n := (shortExact h).δ n (n + 1) rfl

private lemma complexSystem_cohomological (F : A ⥤ CochainComplex B ℕ) [F.Additive]
    (shortExact : ∀ {S : ShortComplex A}, S.ShortExact → (S.map F).ShortExact) :
    IsCohomological (complexSystem F @shortExact) where
  additive := fun n => by dsimp [complexSystem]; infer_instance
  naturality h h' f n := complexBoundary_natural (shortExact h) (shortExact h')
    (F.mapShortComplex.map f) n (n + 1) rfl
  exact₁ h n := ⟨(shortExact h).δ_comp n (n + 1) rfl,
    (shortExact h).homology_exact₁ n (n + 1) rfl⟩
  exact₂ {S} h n := ⟨by
    change HomologicalComplex.homologyMap (F.map S.f) n ≫
      HomologicalComplex.homologyMap (F.map S.g) n = 0
    rw [← HomologicalComplex.homologyMap_comp, ← F.map_comp, S.zero, F.map_zero,
      HomologicalComplex.homologyMap_zero],
    (shortExact h).homology_exact₂ n⟩
  exact₃ h n := ⟨(shortExact h).comp_δ n (n + 1) rfl,
    (shortExact h).homology_exact₃ n (n + 1) rfl⟩
  mono_zero {S} h := by
    letI := (shortExact h).mono_f
    have hm := (HomologicalComplex.shortExact_iff_degreewise_shortExact (S.map F)).mp (shortExact h) 0
    letI : Mono ((F.map S.f).f 0) := hm.mono_f
    exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel (F.map S.f) 0
      (fun i hi => by have : i + 1 = 0 := hi; omega)

end Delta

namespace NormalizedBar
open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NormalizedBar
open GroupCochainComparison.LargeCoordinates (coordinatesEquiv)
open Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large (representation)
open private differential_coordinates from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupCochainComparison

universe u v s
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

private local instance : (cochains.{u,v,s} k G).Additive where
  map_add := by intro M N f g; ext n φ; rfl

private lemma coordinates_map {M N : Ambient.{u,v,s} k G} (f : M ⟶ N) (n : ℕ)
    (z : ((cochains.{u,v,s} k G).obj M).X n) (g : Fin n → G) :
    coordinatesEquiv.{u,v,s} k G N n ((((cochains.{u,v,s} k G).map f).f n).hom z) g =
      f.hom (coordinatesEquiv.{u,v,s} k G M n z g) := rfl

lemma shortExact {S : ShortComplex (Ambient.{u,v,s} k G)} (h : S.ShortExact) :
    (S.map (cochains.{u,v,s} k G)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let L := S.map (cochains.{u,v,s} k G ⋙ HomologicalComplex.eval _ (.up ℕ) n)
  change L.ShortExact
  have h₁ : Function.Injective S.f.hom := h.moduleCat_injective_f
  have h₂ : Function.Surjective S.g.hom := h.moduleCat_surjective_g
  have h₃ := (ShortComplex.moduleCat_exact_iff S).mp h.exact
  refine { exact := (ShortComplex.moduleCat_exact_iff L).mpr ?_
           mono_f := (ModuleCat.mono_iff_injective L.f).mpr ?_
           epi_g := (ModuleCat.epi_iff_surjective L.g).mpr ?_ }
  · intro z hz
    have hz' (g : Fin n → G) : S.g.hom (coordinatesEquiv.{u,v,s} k G S.X₂ n z g) = 0 := by
      rw [← coordinates_map, show (((cochains.{u,v,s} k G).map S.g).f n).hom z = 0 from hz]
      exact congrFun (map_zero (coordinatesEquiv.{u,v,s} k G S.X₃ n)) g
    choose a ha using fun g => h₃ _ (hz' g)
    let y := (coordinatesEquiv.{u,v,s} k G S.X₁ n).symm a
    refine ⟨y, (coordinatesEquiv.{u,v,s} k G S.X₂ n).injective (funext fun g => ?_)⟩
    change coordinatesEquiv.{u,v,s} k G S.X₂ n ((((cochains.{u,v,s} k G).map S.f).f n).hom y) g = _
    rw [coordinates_map, LinearEquiv.apply_symm_apply]
    exact ha g
  · intro x y hxy
    apply (coordinatesEquiv.{u,v,s} k G S.X₁ n).injective
    funext g
    apply h₁
    rw [← coordinates_map, ← coordinates_map]
    exact congrArg (fun z => coordinatesEquiv.{u,v,s} k G S.X₂ n z g) hxy
  · intro y
    choose a ha using fun g : Fin n → G => h₂ (coordinatesEquiv.{u,v,s} k G S.X₃ n y g)
    let x := (coordinatesEquiv.{u,v,s} k G S.X₂ n).symm a
    refine ⟨x, (coordinatesEquiv.{u,v,s} k G S.X₃ n).injective (funext fun g => ?_)⟩
    change coordinatesEquiv.{u,v,s} k G S.X₃ n ((((cochains.{u,v,s} k G).map S.g).f n).hom x) g = _
    rw [coordinates_map, LinearEquiv.apply_symm_apply]
    exact ha g

private abbrev bar (M : Ambient.{u,v,s} k G) := (cochains.{u,v,s} k G).obj M

private def zeroCoordinates (M : Ambient.{u,v,s} k G) : (bar.{u,v,s} k G M).X 0 ≃ₗ[k] M :=
  (coordinatesEquiv.{u,v,s} k G M 0).trans (LinearEquiv.funUnique (Fin 0 → G) k _)

private lemma zeroCoordinates_apply (M : Ambient.{u,v,s} k G) (z : (bar.{u,v,s} k G M).X 0) :
    zeroCoordinates k G M z =
      (show GroupBar.Large.B.{u,v,s} k G 0 ⟶ representation.{u,v,s} k G M from z).hom
        (GroupBar.Large.single k G (fun _ : Fin 1 => 1) 1) := by
  change (show GroupBar.Large.B.{u,v,s} k G 0 ⟶ representation.{u,v,s} k G M from z).hom
    (GroupBar.Large.single k G (Fin.partialProd Fin.elim0) 1) = _
  have h : Fin.partialProd (Fin.elim0 : Fin 0 → G) = (fun _ : Fin 1 => (1 : G)) := by
    funext i
    rw [Fin.eq_zero i, Fin.partialProd_zero]
  rw [h]

private lemma zeroCoordinates_d (M : Ambient.{u,v,s} k G) (z : (bar.{u,v,s} k G M).X 0)
    (g : Fin 1 → G) :
    coordinatesEquiv.{u,v,s} k G M 1 (((bar.{u,v,s} k G M).d 0 1).hom z) g =
      MonoidAlgebra.single (g 0) (1 : k) • zeroCoordinates k G M z - zeroCoordinates k G M z := by
  rw [differential_coordinates]
  simp only [Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large.differential,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero, Nat.zero_add, pow_one, neg_smul, one_smul, sub_eq_add_neg]
  have h₁ : (fun i : Fin 0 => g i.succ) = Fin.elim0 := Subsingleton.elim _ _
  have h₂ : (fun i : Fin 0 => g i.castSucc) = Fin.elim0 := Subsingleton.elim _ _
  rw [h₁, h₂]
  rfl

private lemma zeroCoordinates_fixed (M : Ambient.{u,v,s} k G) (z : (bar.{u,v,s} k G M).X 0) :
    ((bar.{u,v,s} k G M).d 0 1).hom z = 0 ↔
      ∀ a : G, MonoidAlgebra.single a (1 : k) • zeroCoordinates k G M z =
        zeroCoordinates k G M z := by
  constructor
  · intro hz a
    have h := zeroCoordinates_d k G M z (fun _ => a)
    rw [hz, map_zero, Pi.zero_apply] at h
    exact sub_eq_zero.mp h.symm
  · intro hz
    apply (coordinatesEquiv.{u,v,s} k G M 1).injective
    rw [map_zero]
    funext g
    rw [zeroCoordinates_d, hz, sub_self]
    rfl

private def barZeroCycles (M : Ambient.{u,v,s} k G) :
    Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariants.{u,v,s} k G M ≃ₗ[k] (bar.{u,v,s} k G M).cycles 0 := by
  let C := bar.{u,v,s} k G M
  let S := C.sc 0
  let e := zeroCoordinates k G M
  have hnext : (ComplexShape.up ℕ).next 0 = 1 := by simp [CochainComplex.next]
  let toKernel : Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariants.{u,v,s} k G M ≃ₗ[k]
      S.moduleCatLeftHomologyData.K := by
    refine
      { toFun := fun m => ⟨e.symm m.val, ?_⟩
        invFun := fun z => ⟨e z.val, ?_⟩
        left_inv := fun m => Subtype.ext (e.apply_symm_apply m.val)
        right_inv := fun z => Subtype.ext (e.symm_apply_apply z.val)
        map_add' := fun a b => Subtype.ext (e.symm.map_add a.val b.val)
        map_smul' := fun c a => Subtype.ext (e.symm.map_smul c a.val) }
    · change (C.d 0 ((ComplexShape.up ℕ).next 0)).hom (e.symm m.val) = 0
      rw [hnext]
      apply (zeroCoordinates_fixed k G M _).mpr
      intro g
      change MonoidAlgebra.single g (1 : k) • e (e.symm m.val) = e (e.symm m.val)
      rw [LinearEquiv.apply_symm_apply]
      exact m.property g
    · have hz : (C.d 0 ((ComplexShape.up ℕ).next 0)).hom z.val = 0 := z.property
      rw [hnext] at hz
      exact (zeroCoordinates_fixed k G M _).mp hz
  exact toKernel.trans S.moduleCatCyclesIso.symm.toLinearEquiv

private lemma barZeroCycles_i (M : Ambient.{u,v,s} k G)
    (m : Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariants.{u,v,s} k G M) :
    ((bar.{u,v,s} k G M).iCycles 0).hom (barZeroCycles.{u,v,s} k G M m) = (zeroCoordinates k G M).symm m.val := by
  let S := (bar.{u,v,s} k G M).sc 0
  let x := (zeroCoordinates k G M).symm m.val
  have hx : S.g.hom x = 0 := by
    change ((bar.{u,v,s} k G M).d 0 ((ComplexShape.up ℕ).next 0)).hom x = 0
    rw [CochainComplex.next]
    exact (zeroCoordinates_fixed k G M x).mpr (by simpa only [x, LinearEquiv.apply_symm_apply] using (show ∀ g : G, MonoidAlgebra.single g (1 : k) • m.val = m.val from m.property))
  change (S.moduleCatCyclesIso.inv ≫ S.iCycles).hom ⟨x, hx⟩ = x
  rw [S.moduleCatCyclesIso_inv_iCycles]
  rfl

private def barZeroIso : Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor.{u,v,s} k G ≅ cohomology.{u,v,s} k G 0 := by
  have πIso (M : Ambient.{u,v,s} k G) : IsIso ((bar.{u,v,s} k G M).homologyπ 0) :=
    HomologicalComplex.isIso_homologyπ _ 0 0 (by rw [GroupCochainComparison.ResolutionBridge.prev_up_nat])
      ((bar.{u,v,s} k G M).shape 0 0 (by decide))
  refine NatIso.ofComponents (fun M => (barZeroCycles.{u,v,s} k G M).toModuleIso ≪≫
    asIso ((bar.{u,v,s} k G M).homologyπ 0)) ?_
  intro M N f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  let g := (cochains.{u,v,s} k G).map f
  have hπ := congrArg (fun (h : (bar.{u,v,s} k G M).cycles 0 ⟶ _) => h.hom (barZeroCycles.{u,v,s} k G M m))
    (HomologicalComplex.homologyπ_naturality g 0)
  change ((bar.{u,v,s} k G N).homologyπ 0).hom (barZeroCycles.{u,v,s} k G N
    (((Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor.{u,v,s} k G).map f).hom m)) =
      (HomologicalComplex.homologyMap g 0).hom (((bar.{u,v,s} k G M).homologyπ 0).hom (barZeroCycles.{u,v,s} k G M m))
  have he : (HomologicalComplex.homologyMap g 0).hom
      (((bar.{u,v,s} k G M).homologyπ 0).hom (barZeroCycles.{u,v,s} k G M m)) =
      ((bar.{u,v,s} k G N).homologyπ 0).hom
        ((HomologicalComplex.cyclesMap g 0).hom (barZeroCycles.{u,v,s} k G M m)) := hπ
  rw [he]
  apply congrArg ((bar.{u,v,s} k G N).homologyπ 0).hom
  apply (ModuleCat.mono_iff_injective ((bar.{u,v,s} k G N).iCycles 0)).mp inferInstance
  rw [barZeroCycles_i]
  change _ = (HomologicalComplex.cyclesMap g 0 ≫ (bar.{u,v,s} k G N).iCycles 0).hom (barZeroCycles.{u,v,s} k G M m)
  rw [HomologicalComplex.cyclesMap_i]
  change _ = (g.f 0).hom (((bar.{u,v,s} k G M).iCycles 0).hom (barZeroCycles.{u,v,s} k G M m))
  rw [barZeroCycles_i]
  apply (zeroCoordinates k G N).injective
  rw [LinearEquiv.apply_symm_apply]
  have hh := coordinates_map k G f 0 ((zeroCoordinates k G M).symm m.val) Fin.elim0
  change zeroCoordinates k G N ((g.f 0).hom ((zeroCoordinates k G M).symm m.val)) =
    f.hom (zeroCoordinates k G M ((zeroCoordinates k G M).symm m.val)) at hh
  rw [LinearEquiv.apply_symm_apply] at hh
  exact hh.symm

def normalized : Comparison.{u,v,s} k G := by
  let F := Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor.{u,v,s} k G
  letI : PreservesFiniteLimits F := GroupDerivedInvariants.leftExact.{u,v,s} k G
  letI : IsIso (degreeZeroUnit.{u,v,s} k G) := ClassicalDerivedValues.rightZero _ _ F
  let D := rightSystem F
  let C := complexSystem (cochains.{u,v,s} k G) (shortExact k G)
  have hD : IsCohomological D := UniversalDeltaFunctors.rightDelta _ _ F
  have hC : IsCohomological C := complexSystem_cohomological _ _
  have vD (M : Ambient.{u,v,s} k G) [Injective M] (n : ℕ) : IsZero ((D.value (n+1)).obj M) :=
    ClassicalDerivedValues.rightInjectiveVanishing _ _ F M n
  have vC (M : Ambient.{u,v,s} k G) [Injective M] (n : ℕ) : IsZero ((C.value (n+1)).obj M) :=
    ((GroupCochainComparison.Large.cohomologyIso k G (n+1)).app M).isZero_iff.mp (vD M n)
  let e := deltaIso hD hC (universal_of_injective_vanishing D hD vD)
    (universal_of_injective_vanishing C hC vC)
    ((asIso (degreeZeroUnit.{u,v,s} k G)).symm ≪≫ barZeroIso k G)
  refine ⟨e.val.iso, shortExact k G, ?_, e.val.boundary⟩
  intro M m
  let z := barZeroCycles.{u,v,s} k G M m
  let x := ((bar.{u,v,s} k G M).iCycles 0).hom z
  have hx : ((bar.{u,v,s} k G M).d 0 1).hom x = 0 :=
    congrArg (fun (h : (bar.{u,v,s} k G M).cycles 0 ⟶ _) => h.hom z)
      ((bar.{u,v,s} k G M).iCycles_d 0 1)
  have hz : (bar.{u,v,s} k G M).cyclesMk x 1 (by simp [CochainComplex.next]) hx = z := by
    apply (ModuleCat.mono_iff_injective ((bar.{u,v,s} k G M).iCycles 0)).mp inferInstance
    exact (bar.{u,v,s} k G M).i_cyclesMk _ _ _ _
  refine ⟨x, hx, ?_, ?_⟩
  · refine (zeroCoordinates_apply k G M x).symm.trans ?_
    change zeroCoordinates k G M (((bar.{u,v,s} k G M).iCycles 0).hom (barZeroCycles.{u,v,s} k G M m)) = _
    rw [barZeroCycles_i, LinearEquiv.apply_symm_apply]
  · rw [hz]
    have h : degreeZeroUnit.{u,v,s} k G ≫ (e.val.iso 0).hom = (barZeroIso k G).hom := by
      rw [e.property]
      change (degreeZeroUnit.{u,v,s} k G) ≫ inv (degreeZeroUnit.{u,v,s} k G) ≫
        (barZeroIso k G).hom = _
      rw [IsIso.hom_inv_id_assoc]
    exact congrArg (fun (t : F ⟶ cohomology.{u,v,s} k G 0) => (t.app M).hom m) h

theorem comparison :
    Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NormalizedBar.comparisonExpected.{u,v,s} :=
  fun k G _ _ => ⟨normalized k G⟩

end NormalizedBar
section MapDelta

variable {A B E : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
  [Category E] [Abelian E]

private def postcomposeSystem (T : CohomologicalSystem A B) (F : B ⥤ E) [F.Additive] :
    CohomologicalSystem A E where
  value n := T.value n ⋙ F
  δ h n := F.map (T.δ h n)

private lemma postcomposeSystem_cohomological {T : CohomologicalSystem A B}
    (hT : IsCohomological T) (F : B ⥤ E) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    IsCohomological (postcomposeSystem T F) where
  additive n := by
    let := hT.additive n
    change ((T.value n) ⋙ F).Additive
    infer_instance
  naturality h h' f n := by
    change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
    rw [← F.map_comp, ← F.map_comp, hT.naturality h h' f n]
  exact₁ h n :=
    ⟨by simpa only [postcomposeSystem, Functor.comp_map, ← F.map_comp, F.map_zero]
        using congrArg F.map (hT.exact₁ h n).zero,
      (hT.exact₁ h n).exact.map F⟩
  exact₂ h n :=
    ⟨by simpa only [postcomposeSystem, Functor.comp_map, ← F.map_comp, F.map_zero]
        using congrArg F.map (hT.exact₂ h n).zero,
      (hT.exact₂ h n).exact.map F⟩
  exact₃ h n :=
    ⟨by simpa only [postcomposeSystem, Functor.comp_map, ← F.map_comp, F.map_zero]
        using congrArg F.map (hT.exact₃ h n).zero,
      (hT.exact₃ h n).exact.map F⟩
  mono_zero h := by
    let := hT.mono_zero h
    change Mono (F.map ((T.value 0).map _))
    infer_instance

private def precomposeSystem (T : CohomologicalSystem B E) (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] : CohomologicalSystem A E where
  value n := F ⋙ T.value n
  δ h n := T.δ (h.map_of_exact F) n

private lemma precomposeSystem_cohomological {T : CohomologicalSystem B E}
    (hT : IsCohomological T) (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    IsCohomological (precomposeSystem T F) where
  additive n := by
    let := hT.additive n
    change (F ⋙ T.value n).Additive
    infer_instance
  naturality h h' f n :=
    hT.naturality (h.map_of_exact F) (h'.map_of_exact F) (F.mapShortComplex.map f) n
  exact₁ h n := hT.exact₁ (h.map_of_exact F) n
  exact₂ h n := hT.exact₂ (h.map_of_exact F) n
  exact₃ h n := hT.exact₃ (h.map_of_exact F) n
  mono_zero h := hT.mono_zero (h.map_of_exact F)

end MapDelta

namespace NativeTransport
open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NativeTransport
open Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants (GroupModule)

set_option linter.checkUnivs false

universe u v w s
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

private def fixedLiftIso : Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor.{u,v,w} k G ⋙ valueLift.{u,v,w,s} k ≅
    coefficientLift.{u,v,w,s} k G ⋙ Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor.{u,v,max w s} k G := by
  refine NatIso.ofComponents (fun M => LinearEquiv.toModuleIso ?_) ?_
  · exact
      { toFun := fun m => ⟨ULift.up m.down.val, fun g => congrArg ULift.up (m.down.property g)⟩
        invFun := fun m => ULift.up ⟨m.val.down, fun g => congrArg ULift.down (m.property g)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  · intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl

def normalized : Comparison.{u,v,w,s} k G := by
  let F := Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor.{u,v,w} k G
  let F' := Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor.{u,v,max w s} k G
  let L := coefficientLift.{u,v,w,s} k G
  let V := valueLift.{u,v,w,s} k
  letI : PreservesFiniteLimits F := GroupDerivedInvariants.leftExact.{u,v,w} k G
  letI : PreservesFiniteLimits F' := GroupDerivedInvariants.leftExact.{u,v,max w s} k G
  letI : IsIso (degreeZeroUnit.{u,v,w} k G) := ClassicalDerivedValues.rightZero _ _ F
  letI : IsIso (degreeZeroUnit.{u,v,max w s} k G) := ClassicalDerivedValues.rightZero _ _ F'
  let D := postcomposeSystem (rightSystem F) V
  let D' := precomposeSystem (rightSystem F') L
  have hD : IsCohomological D :=
    postcomposeSystem_cohomological (UniversalDeltaFunctors.rightDelta _ _ F) _
  have hD' : IsCohomological D' :=
    precomposeSystem_cohomological (UniversalDeltaFunctors.rightDelta _ _ F') _
  have vD (M : GroupModule.{u,v,w} k G) [Injective M] (n : ℕ) :
      IsZero ((D.value (n+1)).obj M) :=
    V.map_isZero (ClassicalDerivedValues.rightInjectiveVanishing _ _ F M n)
  have vD' (M : GroupModule.{u,v,w} k G) [Injective M] (n : ℕ) :
      IsZero ((D'.value (n+1)).obj M) := by
    letI : Injective (L.obj M) := Functor.PreservesInjectiveObjects.injective_obj (F := L) inferInstance
    exact ClassicalDerivedValues.rightInjectiveVanishing _ _ F' (L.obj M) n
  let e₀ : D.value 0 ≅ D'.value 0 :=
    Functor.isoWhiskerRight (asIso (degreeZeroUnit.{u,v,w} k G)).symm V ≪≫ fixedLiftIso.{u,v,w,s} k G ≪≫
      Functor.isoWhiskerLeft L (asIso (degreeZeroUnit.{u,v,max w s} k G))
  let e := deltaIso hD hD' (universal_of_injective_vanishing D hD vD)
    (universal_of_injective_vanishing D' hD' vD') e₀
  refine ⟨e.val.iso, ?_, fun _ h n => e.val.boundary h n⟩
  intro M m
  have h₀ := congrArg (fun t : D.value 0 ⟶ D'.value 0 =>
    (t.app M).hom (ULift.up (((degreeZeroUnit.{u,v,w} k G).app M).hom m))) e.property
  refine h₀.trans ?_
  have h : V.map ((degreeZeroUnit.{u,v,w} k G).app M) ≫ e₀.hom.app M =
      (fixedLiftIso.{u,v,w,s} k G).hom.app M ≫ (degreeZeroUnit.{u,v,max w s} k G).app (L.obj M) := by
    change V.map ((degreeZeroUnit.{u,v,w} k G).app M) ≫
      V.map ((inv (degreeZeroUnit.{u,v,w} k G)).app M) ≫ _ = _
    rw [← V.map_comp_assoc]
    simp
  exact congrArg (fun t : (F ⋙ V).obj M ⟶ (D'.value 0).obj M => t.hom (ULift.up m)) h

theorem comparison :
    Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NativeTransport.comparisonExpected.{u,v,w,s} :=
  fun k G _ _ => ⟨normalized k G⟩

end NativeTransport

end AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients

namespace AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients

open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients
open TorBalance (LinearChainMap)
open P103.Specs.Ch10.Complexes

section CycleQuotient

private lemma cycleBoundaries_eq_range {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat R) c) (n : ι) :
    cycleBoundaries K n = LinearMap.range (K.sc n).moduleCatToCycles := by
  ext z
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, congrArg Subtype.val hx⟩

private def cycleQuotientIso {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat R) c) (n : ι) :
    Homology K n ≃ₗ[R] K.homology n :=
  (Submodule.quotEquivOfEq _ _ (cycleBoundaries_eq_range K n)).trans
    (K.sc n).moduleCatHomologyIso.symm.toLinearEquiv

private lemma cycleQuotientIso_class {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat R) c) (n : ι) (z : cycles K n) :
    cycleQuotientIso K n (homologyClass K n z) =
      (K.homologyπ n).hom ((K.sc n).moduleCatCyclesIso.inv.hom z) := by
  let S := K.sc n
  apply S.moduleCatHomologyIso.toLinearEquiv.injective
  change S.moduleCatHomologyIso.toLinearEquiv
      (S.moduleCatHomologyIso.toLinearEquiv.symm ((LinearMap.range S.moduleCatToCycles).mkQ z)) =
    (S.moduleCatCyclesIso.inv ≫ S.homologyπ ≫ S.moduleCatHomologyIso.hom).hom z
  rw [LinearEquiv.apply_symm_apply]
  have h : S.moduleCatCyclesIso.inv ≫ (S.homologyπ ≫ S.moduleCatHomologyIso.hom) =
      S.moduleCatLeftHomologyData.π := by
    rw [S.π_moduleCatCyclesIso_hom, Iso.inv_hom_id_assoc]
  exact (congrArg (fun f : S.moduleCatLeftHomologyData.K ⟶ S.moduleCatLeftHomologyData.H =>
    f.hom z) h).symm

private lemma mapHomologyIso_π {B E : Type*} [Category B] [Abelian B] [Category E] [Abelian E]
    (S : ShortComplex B) (F : B ⥤ E) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  let h := S.homologyData.left
  let h' := h.map F
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  change (S.map F).homologyπ ≫ (h'.homologyIso.hom ≫ F.map h.homologyIso.inv) =
    (h'.cyclesIso.hom ≫ F.map h.cyclesIso.inv) ≫ F.map S.homologyπ
  rw [← Category.assoc, h'.homologyπ_comp_homologyIso_hom, Category.assoc,
    Category.assoc]
  change h'.cyclesIso.hom ≫ F.map h.π ≫ F.map h.homologyIso.inv =
    h'.cyclesIso.hom ≫ F.map h.cyclesIso.inv ≫ F.map S.homologyπ
  rw [← F.map_comp, ← F.map_comp, h.π_comp_homologyIso_inv]

end CycleQuotient

namespace MixedProjective
open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.MixedProjective
open Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants (GroupModule)
open GroupCochainComparison.LargeCoordinates (coordinatesEquiv)
open Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large (representation)
open P103.Specs.Ch11.ExtTorDefinitions (ExtWith homComplex homPreMap homPostMap)
open private differential_coordinates from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupCochainComparison

universe u v a s
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

private def homogeneousCochain (M : Coeff.{u,v,a} k G) (N : GroupModule.{u,v,s} k G)
    (ι : M ≃ₗ[k[G]] N) (n : ℕ) :
    ((originalBar k G).X n →ₗ[k[G]] M) ≃ₗ[k] (homBar.{u,v,s} k G N).X n :=
  (originalBarCoordinates k G M n).trans
    ((LinearEquiv.piCongrRight (fun _ : Fin n → G => ι.restrictScalars k)).trans
      (coordinatesEquiv.{u,v,s} k G N n).symm)

private lemma homogeneousCochain_coordinates (M : Coeff.{u,v,a} k G)
    (N : GroupModule.{u,v,s} k G) (ι : M ≃ₗ[k[G]] N)
    (n : ℕ) (z : (originalBar k G).X n →ₗ[k[G]] M) (g : Fin n → G) :
    coordinatesEquiv.{u,v,s} k G N n (homogeneousCochain.{u,v,a,s} k G M N ι n z) g =
      ι (originalBarCoordinates k G M n z g) := by
  change coordinatesEquiv.{u,v,s} k G N n
    ((coordinatesEquiv.{u,v,s} k G N n).symm _) g = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

private lemma homogeneousCochain_d (M : Coeff.{u,v,a} k G) (N : GroupModule.{u,v,s} k G)
    (ι : M ≃ₗ[k[G]] N) (n : ℕ) (z : (originalBar k G).X n →ₗ[k[G]] M) :
    ((homBar.{u,v,s} k G N).d n (n+1)).hom (homogeneousCochain.{u,v,a,s} k G M N ι n z) =
      homogeneousCochain.{u,v,a,s} k G M N ι (n+1) (z.comp ((originalBar k G).d (n+1) n).hom) := by
  apply (coordinatesEquiv.{u,v,s} k G N (n+1)).injective
  funext g
  rw [differential_coordinates, homogeneousCochain_coordinates, originalBarCoordinates_d, differential_apply]
  let t := homogeneousCochain.{u,v,a,s} k G M N ι n z
  have h (g' : Fin n → G) := homogeneousCochain_coordinates.{u,v,a,s} k G M N ι n z g'
  change Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large.differential.{u,v,s} k G N n
    (coordinatesEquiv.{u,v,s} k G N n t) g = _
  have hsmul (r : k) (m : M) : ι (r • m) = r • ι m := (ι.restrictScalars k).map_smul r m
  simp only [Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large.differential,
    show ∀ g', coordinatesEquiv.{u,v,s} k G N n t g' = _ from h,
    map_add, map_sum, LinearEquiv.map_smul, hsmul]
  rfl

private def barChainMap (M : Coeff.{u,v,a} k G) (N : GroupModule.{u,v,s} k G)
    (ι : M ≃ₗ[k[G]] N) :
    LinearChainMap (homComplex (originalBar k G) M) (integralHomBar.{u,v,s} k G N) where
  app n :=
    { toFun := homogeneousCochain.{u,v,a,s} k G M N ι n
      map_add' := (homogeneousCochain.{u,v,a,s} k G M N ι n).map_add
      map_smul' := fun r x => by
        change _ = (r : k) • homogeneousCochain.{u,v,a,s} k G M N ι n x
        rw [Int.cast_smul_eq_zsmul, map_zsmul] }
  comm i j := by
    by_cases hij : (ComplexShape.up ℕ).Rel i j
    · have hji : j = i + 1 := hij.symm
      subst j
      apply LinearMap.ext
      intro z
      exact homogeneousCochain_d.{u,v,a,s} k G M N ι i z
    · simp only [(integralHomBar.{u,v,s} k G N).shape _ _ hij,
        (homComplex (originalBar k G) M).shape _ _ hij, ModuleCat.hom_zero,
        LinearMap.zero_comp, LinearMap.comp_zero]

private lemma barChainMap_bijective (M : Coeff.{u,v,a} k G) (N : GroupModule.{u,v,s} k G)
    (ι : M ≃ₗ[k[G]] N) (n : ℕ) : Function.Bijective ((barChainMap.{u,v,a,s} k G M N ι).app n) :=
  (homogeneousCochain.{u,v,a,s} k G M N ι n).bijective

private def inverseBarChainMap (M : Coeff.{u,v,a} k G) (N : GroupModule.{u,v,s} k G)
    (ι : M ≃ₗ[k[G]] N) :
    LinearChainMap (integralHomBar.{u,v,s} k G N) (homComplex (originalBar k G) M) where
  app n :=
    { toFun := (homogeneousCochain.{u,v,a,s} k G M N ι n).symm
      map_add' := (homogeneousCochain.{u,v,a,s} k G M N ι n).symm.map_add
      map_smul' := fun r x => by
        change (homogeneousCochain.{u,v,a,s} k G M N ι n).symm ((r : k) • (show (homBar.{u,v,s} k G N).X n from x)) = _
        rw [Int.cast_smul_eq_zsmul, map_zsmul]
        rfl }
  comm i j := by
    apply LinearMap.ext
    intro x
    let f := barChainMap.{u,v,a,s} k G M N ι
    let e (n : ℕ) := homogeneousCochain.{u,v,a,s} k G M N ι n
    apply (e j).injective
    change e j (((homComplex (originalBar k G) M).d i j).hom ((e i).symm x)) =
      e j ((e j).symm (((integralHomBar.{u,v,s} k G N).d i j).hom x))
    rw [LinearEquiv.apply_symm_apply]
    have h := f.comm_apply i j ((e i).symm x)
    change ((integralHomBar.{u,v,s} k G N).d i j).hom (e i ((e i).symm x)) = _ at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

private lemma barChainMap_quasiIso (M : Coeff.{u,v,a} k G) (N : GroupModule.{u,v,s} k G)
    (ι : M ≃ₗ[k[G]] N) : (barChainMap.{u,v,a,s} k G M N ι).IsQuasiIso := by
  apply LinearChainMap.isQuasiIso_of_inverse _ (inverseBarChainMap.{u,v,a,s} k G M N ι)
  all_goals
    apply LinearChainMap.eq_of_app_eq
    funext n
    apply LinearMap.ext
    intro x
  · exact (homogeneousCochain.{u,v,a,s} k G M N ι n).symm_apply_apply x
  · exact (homogeneousCochain.{u,v,a,s} k G M N ι n).apply_symm_apply x

private abbrev restrictInt := ModuleCat.restrictScalars (Int.castRingHom k)

private def barHomologyEquiv (M : Coeff.{u,v,a} k G) (N : GroupModule.{u,v,s} k G)
    (ι : M ≃ₗ[k[G]] N) (n : ℕ) :
    ExtWith (barResolution k G) M n ≃+ (homBar.{u,v,s} k G N).homology n := by
  let f := (barChainMap.{u,v,a,s} k G M N ι).homologyMap n
  let e₁ : ExtWith (barResolution k G) M n ≃+ Homology (integralHomBar.{u,v,s} k G N) n :=
    { Equiv.ofBijective f.toFun (barChainMap_quasiIso.{u,v,a,s} k G M N ι n) with
      map_add' := fun x y => f.map_add' x y }
  let f₂ := cycleQuotientIso (integralHomBar.{u,v,s} k G N) n
  let e₂ : Homology (integralHomBar.{u,v,s} k G N) n ≃+ (integralHomBar.{u,v,s} k G N).homology n :=
    { f₂.toEquiv with map_add' := fun x y => f₂.map_add' x y }
  let iso := ((homBar.{u,v,s} k G N).sc n).mapHomologyIso (restrictInt.{u,max u v s} k)
  exact e₁.trans (e₂.trans iso.toLinearEquiv.toAddEquiv)

private lemma barHomologyEquiv_class (M : Coeff.{u,v,a} k G) (N : GroupModule.{u,v,s} k G)
    (ι : M ≃ₗ[k[G]] N) (n : ℕ) (z : cycles (homComplex (originalBar k G) M) n) :
    ∃ y : (homBar.{u,v,s} k G N).cycles n,
      ((homBar.{u,v,s} k G N).iCycles n).hom y = (barChainMap.{u,v,a,s} k G M N ι).app n z.val ∧
      barHomologyEquiv.{u,v,a,s} k G M N ι n (homologyClass _ n z) =
        ((homBar.{u,v,s} k G N).homologyπ n).hom y := by
  let F := restrictInt.{u,max u v s} k
  let C := homBar.{u,v,s} k G N
  let D := integralHomBar.{u,v,s} k G N
  let f := barChainMap.{u,v,a,s} k G M N ι
  let z' := (D.sc n).moduleCatCyclesIso.inv.hom (f.cyclesMap n z)
  let y : C.cycles n := ((C.sc n).mapCyclesIso F).hom.hom z'
  refine ⟨y, ?_, ?_⟩
  · let S := C.sc n
    have h : (S.mapCyclesIso F).hom ≫ F.map S.iCycles = (S.map F).iCycles :=
      S.mapCyclesIso_hom_iCycles F
    refine (congrArg (fun p : (S.map F).cycles ⟶ F.obj S.X₂ => p.hom z') h).trans ?_
    have h' := (D.sc n).moduleCatCyclesIso_inv_iCycles
    exact congrArg (fun p : (D.sc n).moduleCatLeftHomologyData.K ⟶ (D.sc n).X₂ =>
      p.hom (f.cyclesMap n z)) h'
  · change ((C.sc n).mapHomologyIso F).hom.hom
      (cycleQuotientIso D n (homologyClass D n (f.cyclesMap n z))) = _
    rw [cycleQuotientIso_class]
    change (((C.sc n).map F).homologyπ ≫ ((C.sc n).mapHomologyIso F).hom).hom z' = _
    exact congrArg (fun p : ((C.sc n).map F).cycles ⟶ F.obj (C.sc n).homology =>
      p.hom z') (mapHomologyIso_π (C.sc n) F)

/-- The actual cochains on the original bar and the ambient homogeneous bar
are compared by coefficient conjugation at every normalized generator. -/
def compareBar (M : Coeff.{u,v,a} k G) (N : GroupModule.{u,v,s} k G)
    (ι : M ≃ₗ[k[G]] N) :
    BarComparison.{u,v,a,s} k G (barResolution k G) rfl M N ι := by
  refine ⟨barChainMap.{u,v,a,s} k G M N ι, barChainMap_bijective.{u,v,a,s} k G M N ι, ?_,
    barHomologyEquiv.{u,v,a,s} k G M N ι, barHomologyEquiv_class.{u,v,a,s} k G M N ι⟩
  intro n z g
  exact (homogeneousCochain_coordinates.{u,v,a,s} k G M N ι n z g).trans
    (congrArg ι (originalBarCoordinates_apply k G M n z g))

end MixedProjective
end AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients

namespace AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.MixedProjective

open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients
open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.MixedProjective
open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.IndependentResolution
  (Cohomology Resolution homMap OriginalLift liftedInvariant)
open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NativeTransport
  (commonCoefficient commonCoefficientIso commonCoefficientMap degreeZeroUnit)
open Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants (GroupModule)
open Specs.AdvancedHomologicalAlgebra.ExtShiftedHom
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions (ExtWith homComplex homPreMap homPostMap)
open TorBalance (AugmentedResolution LinearChainMap)
open GroupCochainComparison.LargeCoordinates (coordinatesEquiv)
open scoped MonoidAlgebra

attribute [local instance] HasDerivedCategory.standard

universe u v a b p q s
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

private abbrev barProjective := barResolution_isProjective k G

private abbrev originalBarModel := AugmentedResolution.ofP103 (barResolution k G) (barProjective k G)

private lemma barAugmentation_vertex (c : Fin 1 → G) :
    (barResolution k G).ε (basisElement k G 0 c) = trivialElement k G 1 :=
  congrArg (trivialElement k G) (GroupBar.Large.augmentation_single.{u,v,0} k G c 1)

private abbrev barPost {M : Coeff.{u,v,a} k G} {N : Coeff.{u,v,b} k G}
    (f : M →ₗ[k[G]] N) :=
  homMap k G (P := originalBarModel k G) (Q := originalBarModel k G)
    (LinearChainMap.id (barResolution k G).complex) f

private lemma barClasses_natural
    {M : Coeff.{u,v,a} k G} {N : Coeff.{u,v,b} k G}
    {R S : GroupModule.{u,v,s} k G}
    {iM : M ≃ₗ[k[G]] R} {iN : N ≃ₗ[k[G]] S}
    (J : BarComparison.{u,v,a,s} k G (barResolution k G) rfl M R iM)
    (J' : BarComparison.{u,v,b,s} k G (barResolution k G) rfl N S iN)
    (f : M →ₗ[k[G]] N) (g : R ⟶ S) (h : ∀ m, g.hom (iM m) = iN (f m))
    (n : ℕ) (x : ExtWith (barResolution k G) M n) :
    J'.classes n ((barPost k G f).homologyMap n x) =
      ((NormalizedBar.cohomology.{u,v,s} k G n).map g).hom (J.classes n x) := by
  obtain ⟨z, rfl⟩ := (cycleBoundaries (homComplex (originalBar k G) M) n).mkQ_surjective x
  let l := barPost k G f
  obtain ⟨y, hy, hy'⟩ := J.class_formula n z
  obtain ⟨y', hz, hz'⟩ := J'.class_formula n (l.cyclesMap n z)
  let α := (Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NormalizedBar.cochains.{u,v,s}
    k G).map g
  have hcyc : (HomologicalComplex.cyclesMap α n).hom y = y' := by
    apply (ModuleCat.mono_iff_injective ((homBar.{u,v,s} k G S).iCycles n)).mp inferInstance
    have h₁ := congrArg (fun e : (homBar.{u,v,s} k G R).cycles n ⟶ (homBar.{u,v,s} k G S).X n =>
      e.hom y) (HomologicalComplex.cyclesMap_i α n)
    change ((homBar.{u,v,s} k G S).iCycles n).hom ((HomologicalComplex.cyclesMap α n).hom y) =
      (α.f n).hom (((homBar.{u,v,s} k G R).iCycles n).hom y) at h₁
    rw [h₁, hy, hz]
    apply (coordinatesEquiv.{u,v,s} k G S n).injective
    funext t
    change g.hom (coordinatesEquiv.{u,v,s} k G R n (J.cochain.app n z.val) t) =
      coordinatesEquiv.{u,v,s} k G S n (J'.cochain.app n (l.cyclesMap n z).val) t
    rw [show coordinatesEquiv.{u,v,s} k G R n (J.cochain.app n z.val) t = _ from
      J.coordinates n z.val t, show coordinatesEquiv.{u,v,s} k G S n
        (J'.cochain.app n (l.cyclesMap n z).val) t = _ from J'.coordinates n _ t]
    exact h _
  change J'.classes n (homologyClass _ n (l.cyclesMap n z)) =
    (HomologicalComplex.homologyMap α n).hom (J.classes n (homologyClass _ n z))
  rw [hz', hy', ← hcyc]
  exact (congrArg (fun e : (homBar.{u,v,s} k G R).cycles n ⟶ (homBar.{u,v,s} k G S).homology n =>
    e.hom y) (HomologicalComplex.homologyπ_naturality α n)).symm

private abbrev p103Comparison :=
  ExtShiftedHom.LiftedP103.independentComparison.{max u v,u,a,0,max (u+1) (v+1) (a+1)} k[G]

private lemma p103_natural {M N : Coeff.{u,v,a} k G} (f : M ⟶ N)
    (B B' : LeftResolution k[G] (trivial k G)) (hB : B.IsProjective) (hB' : B'.IsProjective)
    (g : B'.complex ⟶ B.complex) (hg : ChainLift B' B LinearMap.id g)
    (n : ℕ) (x : ExtWith B M n) :
    (p103Comparison.{u,v,a} k G).equiv (trivial k G) N B' hB' n
      (P103.Specs.Ch10.Complexes.homologyMap (homPreMap g M ≫ homPostMap B'.complex f.hom) n x) =
      extMap (𝟙 _) ((lift.{u,v,a} k G).map f) (n : ℤ)
        ((p103Comparison.{u,v,a} k G).equiv (trivial k G) M B hB n x) := by
  have hn := (p103Comparison.{u,v,a} k G).natural (trivial k G) (trivial k G)
    M N B B' hB hB' (𝟙 _) f g hg n x
  rw [(firstLift.{max u v,u,a,0} k[G]).map_id] at hn
  exact hn

private def nativeBar (M : Coeff.{u,v,a} k G) :
    BarComparison.{u,v,a,a} k G (barResolution k G) rfl M ((lift.{u,v,a} k G).obj M)
      (nativeCoeffIso k G M) :=
  compareBar.{u,v,a,a} k G M _ (nativeCoeffIso k G M)

private def nativeExt
    (A : Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NormalizedBar.Comparison.{u,v,a} k G)
    (M : Coeff.{u,v,a} k G) (n : ℕ) : (derived.{u,v,a} k G n).obj M ≃+ ambientExt k G M n :=
  (((A.iso n).app ((lift.{u,v,a} k G).obj M)).toLinearEquiv.toAddEquiv.trans
    ((nativeBar k G M).classes n).symm).trans
    ((p103Comparison.{u,v,a} k G).equiv (trivial k G) M (barResolution k G) (barProjective k G) n)

private lemma nativeExt_natural
    (A : Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NormalizedBar.Comparison.{u,v,a} k G)
    (M N : Coeff.{u,v,a} k G) (f : M ⟶ N) (n : ℕ) (x : (derived.{u,v,a} k G n).obj M) :
    nativeExt k G A N n (((derived.{u,v,a} k G n).map f).hom x) =
      extMap (𝟙 _) ((lift.{u,v,a} k G).map f) (n : ℤ) (nativeExt k G A M n x) := by
  let e := p103Comparison.{u,v,a} k G
  let l := (lift.{u,v,a} k G).map f
  let y := ((nativeBar k G M).classes n).symm (((A.iso n).hom.app ((lift.{u,v,a} k G).obj M)).hom x)
  have hn := p103_natural k G f (barResolution k G) (barResolution k G) (barProjective k G)
    (barProjective k G) (𝟙 _) (by rfl) n y
  change e.equiv (trivial k G) N (barResolution k G) (barProjective k G) n
    (((nativeBar k G N).classes n).symm
      (((A.iso n).hom.app ((lift.{u,v,a} k G).obj N)).hom (((derived.{u,v,a} k G n).map f).hom x))) =
    _
  refine Eq.trans ?_ hn
  apply congrArg (e.equiv (trivial k G) N (barResolution k G) (barProjective k G) n)
  apply ((nativeBar k G N).classes n).injective
  rw [AddEquiv.apply_symm_apply]
  have hp : (barPost k G f.hom).homologyMap n =
      P103.Specs.Ch10.Complexes.homologyMap
        (homPreMap (𝟙 (barResolution k G).complex) M ≫ homPostMap (barResolution k G).complex f.hom) n :=
    IndependentResolution.homologyMap_ofHom k G (barProjective k G) (barProjective k G) (𝟙 _) f.hom n
  refine Eq.trans ?_ (congrArg ((nativeBar k G N).classes n) (LinearMap.congr_fun hp y))
  refine Eq.trans ?_ (barClasses_natural k G (nativeBar k G M) (nativeBar k G N)
    f.hom l (fun _ => rfl) n y).symm
  change ((A.iso n).hom.app ((lift.{u,v,a} k G).obj N)).hom (((derived.{u,v,a} k G n).map f).hom x) =
    ((NormalizedBar.cohomology.{u,v,a} k G n).map l).hom
      (((nativeBar k G M).classes n) (((nativeBar k G M).classes n).symm _))
  rw [AddEquiv.apply_symm_apply]
  exact congrArg (fun h => h.hom x) ((A.iso n).hom.naturality l)

private def nativeComparison
    (A : Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NormalizedBar.Comparison.{u,v,a} k G) :
    NativeComparison.{u,v,a,p} k G A (barResolution k G) (barProjective k G) rfl := by
  refine ⟨p103Comparison.{u,v,a} k G, nativeExt k G A, nativeExt_natural k G A,
    IndependentResolution.compare.{u,v,a,p} k G _ _, nativeBar k G, ?_⟩
  intro M n x
  change ((A.iso n).app ((lift.{u,v,a} k G).obj M)).toLinearEquiv.toAddEquiv
    ((nativeExt k G A M n).symm _) = _
  let e := ((A.iso n).app ((lift.{u,v,a} k G).obj M)).toLinearEquiv.toAddEquiv
  let f := (nativeBar k G M).classes n
  let p := (p103Comparison.{u,v,a} k G).equiv (trivial k G) M (barResolution k G) (barProjective k G) n
  change e (e.symm (f (p.symm (p x)))) = f x
  rw [AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]

private lemma nativeValue_bar
    (A : Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NormalizedBar.Comparison.{u,v,a} k G)
    (P : Resolution.{u,v,p} k G) (M : Coeff.{u,v,a} k G) (n : ℕ) (x : Cohomology k G P M n) :
    ((A.iso n).hom.app ((lift.{u,v,a} k G).obj M)).hom
      ((nativeComparison.{u,v,a,p} k G A).value k G P M n x) =
    (nativeBar k G M).classes n ((IndependentResolution.compare.{u,v,a,p} k G
      (barResolution k G) (barProjective k G)).equiv P M n x) :=
  (nativeComparison.{u,v,a,p} k G A).bar_agreement M n _

set_option maxRecDepth 5000 in
private lemma nativeComparison_ordinary
    (A : Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NormalizedBar.Comparison.{u,v,a} k G) :
    (nativeComparison.{u,v,a,p} k G A).agreesWithOrdinary k G := by
  intro P B' hB' g hg M n x
  let B := barResolution k G
  let hB := barProjective k G
  let e := p103Comparison.{u,v,a} k G
  let C := IndependentResolution.compare.{u,v,a,p} k G B hB
  obtain ⟨l, hl⟩ := P103.Ch10.Comparison.chain_exists k[G] _ _ B' B hB' LinearMap.id
  change nativeExt k G A M n ((nativeExt k G A M n).symm (e.equiv (trivial k G) M B hB n
    (C.equiv P M n x))) = _
  rw [AddEquiv.apply_symm_apply, IndependentResolution.compare_ordinary k G B B' hB hB'
    P g hg l hl M n x]
  symm
  refine (p103_natural k G (𝟙 M) B B' hB hB' l hl n (C.equiv P M n x)).trans ?_
  rw [(lift.{u,v,a} k G).map_id]
  unfold extMap
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

private lemma nativeComparison_zero
    (A : Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NormalizedBar.Comparison.{u,v,a} k G) :
    (nativeComparison.{u,v,a,p} k G A).agreesAtDegreeZero k G := by
  intro M P z f hf
  let m := evaluationEquiv k G M f
  refine ⟨m, rfl, ?_⟩
  let B := barResolution k G
  let hB := barProjective k G
  let M' := (lift.{u,v,a} k G).obj M
  let m' := liftedInvariant k G M m
  let K := homBar.{u,v,a} k G M'
  let J := nativeBar k G M
  obtain ⟨z', hz', hclass⟩ := IndependentResolution.compare_zero k G B hB P M z f hf
  obtain ⟨y, hy, hy'⟩ := J.class_formula 0 z'
  obtain ⟨c, hc, hcoord, hunit⟩ := A.degreeZero M' m'
  apply ((A.iso 0).app M').toLinearEquiv.injective
  change ((A.iso 0).hom.app M').hom _ = _
  rw [nativeValue_bar, hclass, hy']
  change (K.homologyπ 0).hom y = ((A.iso 0).hom.app M').hom
    (((NormalizedBar.degreeZeroUnit.{u,v,a} k G).app M').hom m')
  rw [hunit]
  apply congrArg (K.homologyπ 0).hom
  apply (ModuleCat.mono_iff_injective (K.iCycles 0)).mp inferInstance
  have hnext : (ComplexShape.up ℕ).next 0 = 1 := by simp [CochainComplex.next]
  have hcyc : (K.iCycles 0).hom (K.cyclesMk c 1 hnext hc) = c := K.i_cyclesMk c 1 hnext hc
  change (K.iCycles 0).hom y = (K.iCycles 0).hom (K.cyclesMk c 1 hnext hc)
  rw [hy, hcyc]
  apply (NormalizedBar.zeroCoordinates.{u,v,a} k G M').injective
  have he := J.coordinates 0 z'.val Fin.elim0
  change NormalizedBar.zeroCoordinates.{u,v,a} k G M' (J.cochain.app 0 z'.val) =
    NormalizedBar.zeroCoordinates.{u,v,a} k G M' c
  have he' : NormalizedBar.zeroCoordinates.{u,v,a} k G M' (J.cochain.app 0 z'.val) =
      (nativeCoeffIso k G M) ((show (originalBar k G).X 0 →ₗ[k[G]] M from z'.val)
        (basisElement k G 0 (Fin.partialProd Fin.elim0))) := he
  rw [he', ← hz', NormalizedBar.zeroCoordinates_apply]
  refine Eq.trans ?_ hcoord.symm
  exact congrArg (fun z => ULift.up (f z)) (barAugmentation_vertex k G (Fin.partialProd Fin.elim0))

end AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.MixedProjective

namespace AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.MixedProjective

open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients
open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.MixedProjective
open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.IndependentResolution
  (Cohomology Resolution homMap OriginalLift)
open Specs.AdvancedHomologicalAlgebra.ExtShiftedHom
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes
open TorBalance (AugmentedResolution LinearChainMap)
attribute [local instance] HasDerivedCategory.standard

universe u v a p q
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

private lemma nativeValue_natural
    (A : Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NormalizedBar.Comparison.{u,v,a} k G)
    (P : Resolution.{u,v,p} k G) (Q : Resolution.{u,v,q} k G)
    (M N : Coeff.{u,v,a} k G) (f : M ⟶ N)
    (g : LinearChainMap Q.complex P.complex) (hg : OriginalLift k G g) (n : ℕ) (z : Cohomology k G P M n) :
    (nativeComparison.{u,v,a,q} k G A).value k G Q N n ((homMap k G g f.hom).homologyMap n z) =
      ((derived.{u,v,a} k G n).map f).hom ((nativeComparison.{u,v,a,p} k G A).value k G P M n z) := by
  let M' := (lift.{u,v,a} k G).obj M
  let N' := (lift.{u,v,a} k G).obj N
  let f' := (lift.{u,v,a} k G).map f
  apply ((A.iso n).app N').toLinearEquiv.injective
  change ((A.iso n).hom.app N').hom _ = ((A.iso n).hom.app N').hom _
  rw [nativeValue_bar, IndependentResolution.compare_natural k G (barResolution k G)
    (barProjective k G) P Q M N f.hom g hg n z]
  rw [barClasses_natural k G (nativeBar k G M) (nativeBar k G N) f.hom f' (fun _ => rfl)]
  rw [← nativeValue_bar k G A P M n z]
  exact (congrArg (fun h => h.hom ((nativeComparison.{u,v,a,p} k G A).value k G P M n z))
    ((A.iso n).hom.naturality f')).symm

private lemma nativeValue_eq_ordinary
    (A : Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NormalizedBar.Comparison.{u,v,a} k G)
    (B : LeftResolution k[G] (trivial k G)) (hB : B.IsProjective)
    (P : Resolution.{u,v,p} k G) (M : Coeff.{u,v,a} k G) (n : ℕ) (z : Cohomology k G P M n) :
    (nativeComparison.{u,v,a,p} k G A).value k G P M n z =
      (nativeExt k G A M n).symm
        ((p103Comparison.{u,v,a} k G).equiv (trivial k G) M B hB n
          ((IndependentResolution.compare.{u,v,a,p} k G B hB).equiv P M n z)) := by
  obtain ⟨g, hg⟩ := IndependentResolution.resolutionLifts k G P (AugmentedResolution.ofP103 B hB)
  apply (nativeExt k G A M n).injective
  rw [AddEquiv.apply_symm_apply, (IndependentResolution.compare.{u,v,a,p} k G B hB).precompose P g hg]
  exact nativeComparison_ordinary.{u,v,a,p} k G A P B hB g hg M n z

end AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.MixedProjective

namespace AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.IndependentResolution

open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients
open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.IndependentResolution
open Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants (GroupModule)
open Specs.AdvancedHomologicalAlgebra.ExtShiftedHom
open P103.Specs.Ch10.Complexes
open MixedProjective (nativeComparison nativeExt p103Comparison nativeExt_natural nativeComparison_zero
  nativeValue_eq_ordinary nativeValue_natural)

attribute [local instance] HasDerivedCategory.standard
universe u v w a b
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

private def normalizedDegreeZero (M : Coeff.{u,v,w} k G) :
    (derived.{u,v,w} k G 0).obj M ≃+ invariants k G M :=
  (((derivedZeroIso k G).app M).toLinearEquiv.trans ULift.moduleEquiv).toAddEquiv

private lemma normalizedDegreeZero_unit (M : Coeff.{u,v,w} k G) (m : invariants k G M) :
    normalizedDegreeZero k G M (((degreeZeroUnit.{u,v,w} k G).app ((lift.{u,v,w} k G).obj M)).hom
      (liftedInvariant k G M m)) = m := by
  let F := Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor.{u,v,w} k G
  letI : PreservesFiniteLimits F := GroupDerivedInvariants.leftExact.{u,v,w} k G
  letI : IsIso (degreeZeroUnit.{u,v,w} k G) := ClassicalDerivedValues.rightZero _ _ F
  let M' := (lift.{u,v,w} k G).obj M
  let e := ((asIso (degreeZeroUnit.{u,v,w} k G)).app M').toLinearEquiv
  change (((invariantsIso k G).hom.app M).hom (e.symm (e (liftedInvariant k G M m)))).down = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem projectiveComputation :
    Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.IndependentResolution.projectiveComputationExpected.{u,v,w,a,b} := by
  intro k G _ _
  let A := NormalizedBar.normalized.{u,v,w} k G
  let e := nativeExt k G A
  let C := p103Comparison.{u,v,w} k G
  let d₀ := normalizedDegreeZero k G
  refine ⟨C, e, d₀, nativeExt_natural k G A, normalizedDegreeZero_unit k G, ?_⟩
  intro B hB
  refine ⟨compare.{u,v,w,a} k G B hB, compare.{u,v,w,b} k G B hB, ?_, ?_⟩
  · intro P Q M N f g hg n z
    dsimp only [AddEquiv.trans_apply]
    rw [← nativeValue_eq_ordinary k G A B hB P M n z, ← nativeValue_eq_ordinary k G A B hB Q N n]
    exact nativeValue_natural k G A P Q M N f g hg n z
  · intro P M z f hf
    dsimp only [AddEquiv.trans_apply]
    rw [← nativeValue_eq_ordinary k G A B hB P M 0 (homologyClass _ 0 z)]
    obtain ⟨m, hv, he⟩ := nativeComparison_zero.{u,v,w,a} k G A M P z f hf
    rw [he, normalizedDegreeZero_unit]
    exact hv

end AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.IndependentResolution

namespace AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients

open TorBalance (LinearChainMap)
open P103.Specs.Ch10.Complexes

section MixedHomology

universe u a b
variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  {K : HomologicalComplex (ModuleCat.{a} R) c} {L : HomologicalComplex (ModuleCat.{b} R) c}

private def mixedHomologyMap (f : LinearChainMap K L) (n : ι) : K.homology n →ₗ[R] L.homology n :=
  (cycleQuotientIso L n).toLinearMap ∘ₗ f.homologyMap n ∘ₗ (cycleQuotientIso K n).symm.toLinearMap

private lemma mixedHomologyMap_class (f : LinearChainMap K L) (n : ι)
    (x : K.cycles n) (y : L.cycles n)
    (h : (L.iCycles n).hom y = f.app n ((K.iCycles n).hom x)) :
    mixedHomologyMap f n ((K.homologyπ n).hom x) = (L.homologyπ n).hom y := by
  let z := (K.sc n).moduleCatCyclesIso.hom.hom x
  have hz : (K.sc n).moduleCatCyclesIso.inv.hom z = x :=
    ((K.sc n).moduleCatCyclesIso.toLinearEquiv).symm_apply_apply x
  have h₁ : z.val = (K.iCycles n).hom x :=
    congrArg (fun p : K.cycles n ⟶ K.X n => p.hom x) (K.sc n).moduleCatCyclesIso_hom_i
  have h₂ : (L.sc n).moduleCatCyclesIso.inv.hom (f.cyclesMap n z) = y := by
    apply (ModuleCat.mono_iff_injective (L.iCycles n)).mp inferInstance
    have he : (L.iCycles n).hom ((L.sc n).moduleCatCyclesIso.inv.hom (f.cyclesMap n z)) =
        f.app n z.val :=
      congrArg (fun p : (L.sc n).moduleCatLeftHomologyData.K ⟶ L.X n => p.hom (f.cyclesMap n z))
        (L.sc n).moduleCatCyclesIso_inv_iCycles
    rw [he, h₁, h]
  have hq : cycleQuotientIso K n (homologyClass K n z) = (K.homologyπ n).hom x :=
    (cycleQuotientIso_class K n z).trans (congrArg (K.homologyπ n).hom hz)
  rw [← hq]
  change cycleQuotientIso L n (f.homologyMap n
    ((cycleQuotientIso K n).symm (cycleQuotientIso K n (homologyClass K n z)))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact (cycleQuotientIso_class L n (f.cyclesMap n z)).trans (congrArg (L.homologyπ n).hom h₂)

private lemma mixedHomologyMap_comp {T : HomologicalComplex (ModuleCat R) c}
    (f : LinearChainMap K L) (g : LinearChainMap L T) (n : ι) (z : K.homology n) :
    mixedHomologyMap g n (mixedHomologyMap f n z) = mixedHomologyMap (g.comp f) n z := by
  simp only [mixedHomologyMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, LinearChainMap.homologyMap_comp]

private lemma mixedHomologyMap_ofHom {L : HomologicalComplex (ModuleCat.{a} R) c}
    (f : K ⟶ L) (n : ι) (z : K.homology n) :
    mixedHomologyMap (LinearChainMap.ofHom f) n z = (HomologicalComplex.homologyMap f n).hom z := by
  obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance z
  let y := (HomologicalComplex.cyclesMap f n).hom x
  have hy : (L.iCycles n).hom y = (LinearChainMap.ofHom f).app n ((K.iCycles n).hom x) :=
    congrArg (fun p : K.cycles n ⟶ L.X n => p.hom x) (HomologicalComplex.cyclesMap_i f n)
  exact (mixedHomologyMap_class _ _ x y hy).trans
    (congrArg (fun p : K.cycles n ⟶ L.homology n => p.hom x)
      (HomologicalComplex.homologyπ_naturality f n)).symm

private lemma mixedBoundary_natural
    {S : ShortComplex (CochainComplex (ModuleCat.{a} R) ℕ)}
    {T : ShortComplex (CochainComplex (ModuleCat.{b} R) ℕ)}
    (hS : S.ShortExact) (hT : T.ShortExact)
    (f₁ : LinearChainMap S.X₁ T.X₁) (f₂ : LinearChainMap S.X₂ T.X₂) (f₃ : LinearChainMap S.X₃ T.X₃)
    (h₁₂ : ∀ n x, f₂.app n ((S.f.f n).hom x) = (T.f.f n).hom (f₁.app n x))
    (h₂₃ : ∀ n x, f₃.app n ((S.g.f n).hom x) = (T.g.f n).hom (f₂.app n x))
    (n : ℕ) (x : S.X₃.homology n) :
    mixedHomologyMap f₁ (n+1) ((hS.δ n (n+1) rfl).hom x) =
      (hT.δ n (n+1) rfl).hom (mixedHomologyMap f₃ n x) := by
  let m := n + 1
  let l := m + 1
  let hm : (ComplexShape.up ℕ).next n = m := CochainComplex.next _ _
  let hl : (ComplexShape.up ℕ).next m = l := CochainComplex.next _ _
  obtain ⟨z₃, rfl⟩ := (ModuleCat.epi_iff_surjective (S.X₃.homologyπ n)).mp inferInstance x
  let x₃ := (S.X₃.iCycles n).hom z₃
  have hx₃ : (S.X₃.d n m).hom x₃ = 0 :=
    congrArg (fun p : S.X₃.cycles n ⟶ S.X₃.X m => p.hom z₃) (S.X₃.iCycles_d n m)
  have hSn := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n
  have hSm := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS m
  obtain ⟨x₂, hx₂⟩ := hSn.moduleCat_surjective_g x₃
  have hkernel : (S.g.f m).hom ((S.X₂.d n m).hom x₂) = 0 := by
    have h := congrArg (fun p : S.X₂.X n ⟶ S.X₃.X m => p.hom x₂) (S.g.comm n m)
    change (S.X₃.d n m).hom ((S.g.f n).hom x₂) = _ at h
    rw [show (S.g.f n).hom x₂ = x₃ from hx₂, hx₃] at h
    exact h.symm
  obtain ⟨x₁, hx₁⟩ := (ShortComplex.moduleCat_exact_iff _).mp hSm.exact _ hkernel
  have hx₁' : (S.f.f m).hom x₁ = (S.X₂.d n m).hom x₂ := hx₁
  have hq₃ : S.X₃.cyclesMk x₃ m hm hx₃ = z₃ := by
    apply (ModuleCat.mono_iff_injective (S.X₃.iCycles n)).mp inferInstance
    exact S.X₃.i_cyclesMk x₃ m hm hx₃
  have hx₄ : (T.X₃.d n m).hom (f₃.app n x₃) = 0 := by
    rw [f₃.comm_apply, hx₃, map_zero]
  have hx₅ : (T.g.f n).hom (f₂.app n x₂) = f₃.app n x₃ :=
    (h₂₃ n x₂).symm.trans (congrArg (f₃.app n) hx₂)
  have hx₆ : (T.f.f m).hom (f₁.app m x₁) = (T.X₂.d n m).hom (f₂.app n x₂) := by
    rw [← h₁₂, hx₁', f₂.comm_apply]
  have hδ₁ := hS.δ_apply n m rfl x₃ hx₃ x₂ hx₂ x₁ hx₁' l hl
  have hδ₂ := hT.δ_apply n m rfl (f₃.app n x₃) hx₄ (f₂.app n x₂) hx₅ (f₁.app m x₁) hx₆ l hl
  let z₁ := S.X₁.cyclesMk x₁ l hl (hS.d_eq_zero_of_f_eq_d_apply n m x₂ x₁ hx₁' l)
  let w₁ := T.X₁.cyclesMk (f₁.app m x₁) l hl
    (hT.d_eq_zero_of_f_eq_d_apply n m (f₂.app n x₂) (f₁.app m x₁) hx₆ l)
  let w₃ := T.X₃.cyclesMk (f₃.app n x₃) m hm hx₄
  have hS' : (hS.δ n m rfl).hom ((S.X₃.homologyπ n).hom (S.X₃.cyclesMk x₃ m hm hx₃)) =
      (S.X₁.homologyπ m).hom z₁ := hδ₁
  have hT' : (hT.δ n m rfl).hom ((T.X₃.homologyπ n).hom w₃) =
      (T.X₁.homologyπ m).hom w₁ := hδ₂
  have h₁ : (T.X₁.iCycles m).hom w₁ = f₁.app m ((S.X₁.iCycles m).hom z₁) := by
    rw [show (S.X₁.iCycles m).hom z₁ = x₁ from S.X₁.i_cyclesMk ..]
    exact T.X₁.i_cyclesMk ..
  have h₃ : (T.X₃.iCycles n).hom w₃ = f₃.app n ((S.X₃.iCycles n).hom z₃) := T.X₃.i_cyclesMk ..
  rw [hq₃] at hS'
  rw [hS', mixedHomologyMap_class _ _ _ _ h₁, mixedHomologyMap_class _ _ _ _ h₃, hT']

end MixedHomology
end AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients

namespace AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NormalizedBar

open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients
open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NormalizedBar
open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NativeTransport
  (coefficientLift valueLift)
open Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants (GroupModule)
open Specs.AdvancedHomologicalAlgebra.UniversalDeltaFunctors
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues (rightBoundary)
open TorBalance (LinearChainMap)
open GroupCochainComparison.LargeCoordinates (coordinatesEquiv)
open private differential_coordinates from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupCochainComparison

attribute [local instance] HasDerivedCategory.standard

universe u v a b s
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

private def cochainLinearMap {M : Ambient.{u,v,a} k G} {N : Ambient.{u,v,b} k G}
    (f : M →ₗ[k[G]] N) : LinearChainMap (bar.{u,v,a} k G M) (bar.{u,v,b} k G N) where
  app n := (coordinatesEquiv.{u,v,b} k G N n).symm.toLinearMap ∘ₗ
    (LinearMap.pi fun t : Fin n → G => (f.restrictScalars k).comp (LinearMap.proj t)) ∘ₗ
      (coordinatesEquiv.{u,v,a} k G M n).toLinearMap
  comm i j := by
    by_cases h : (ComplexShape.up ℕ).Rel i j
    · have hj : j = i + 1 := h.symm
      subst j
      apply LinearMap.ext
      intro z
      let e := coordinatesEquiv.{u,v,a} k G M i
      let e' := coordinatesEquiv.{u,v,b} k G N i
      let z' := e'.symm (fun t => f (e z t))
      apply (coordinatesEquiv.{u,v,b} k G N (i+1)).injective
      funext t
      change coordinatesEquiv.{u,v,b} k G N (i+1) (((bar.{u,v,b} k G N).d i (i+1)).hom z') t =
        coordinatesEquiv.{u,v,b} k G N (i+1) ((coordinatesEquiv.{u,v,b} k G N (i+1)).symm _) t
      have hz' : coordinatesEquiv.{u,v,b} k G N i z' = fun t => f (e z t) :=
        e'.apply_symm_apply _
      simp only [differential_coordinates, LinearEquiv.apply_symm_apply, hz']
      change Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large.differential.{u,v,b} k G N i
          (fun t => f (e z t)) t =
        f (coordinatesEquiv.{u,v,a} k G M (i+1) (((bar.{u,v,a} k G M).d i (i+1)).hom z) t)
      rw [differential_coordinates]
      have hsmul (r : k) (m : M) : f (r • m) = r • f m :=
        (f.restrictScalars k).map_smul r m
      have hact (g : G) (m : M) :
          f ((Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large.representation.{u,v,a} k G M).ρ g m) =
            (Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large.representation.{u,v,b} k G N).ρ g (f m) :=
        f.map_smul (MonoidAlgebra.single g (1 : k)) m
      simp only [e, Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large.differential, map_add, map_sum,
        hact, hsmul]
    · simp only [(bar.{u,v,a} k G M).shape _ _ h, (bar.{u,v,b} k G N).shape _ _ h,
        ModuleCat.hom_zero, LinearMap.zero_comp, LinearMap.comp_zero]

private lemma cochainLinearMap_coordinates {M : Ambient.{u,v,a} k G} {N : Ambient.{u,v,b} k G}
    (f : M →ₗ[k[G]] N) (n : ℕ) (y : (bar.{u,v,a} k G M).X n) (t : Fin n → G) :
    coordinatesEquiv.{u,v,b} k G N n ((cochainLinearMap.{u,v,a,b} k G f).app n y) t =
      f (coordinatesEquiv.{u,v,a} k G M n y t) := by
  change coordinatesEquiv.{u,v,b} k G N n ((coordinatesEquiv.{u,v,b} k G N n).symm _) t = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

private lemma cochainLinearMap_ofHom {M N : Ambient.{u,v,a} k G} (f : M ⟶ N) :
    cochainLinearMap.{u,v,a,a} k G f.hom = LinearChainMap.ofHom ((cochains.{u,v,a} k G).map f) := by
  apply LinearChainMap.eq_of_app_eq
  funext n
  apply LinearMap.ext
  intro z
  apply (coordinatesEquiv.{u,v,a} k G N n).injective
  funext t
  exact (cochainLinearMap_coordinates k G f.hom n z t).trans (coordinates_map k G f n z t).symm

private lemma cochainLinearMap_comp {M : Ambient.{u,v,a} k G} {N : Ambient.{u,v,b} k G}
    {P : Ambient.{u,v,s} k G} (f : M →ₗ[k[G]] N) (g : N →ₗ[k[G]] P) :
    (cochainLinearMap.{u,v,b,s} k G g).comp (cochainLinearMap.{u,v,a,b} k G f) =
      cochainLinearMap.{u,v,a,s} k G (g.comp f) := by
  apply LinearChainMap.eq_of_app_eq
  funext n
  apply LinearMap.ext
  intro z
  apply (coordinatesEquiv.{u,v,s} k G P n).injective
  funext t
  change coordinatesEquiv.{u,v,s} k G P n ((cochainLinearMap.{u,v,b,s} k G g).app n
    ((cochainLinearMap.{u,v,a,b} k G f).app n z)) t = _
  rw [cochainLinearMap_coordinates, cochainLinearMap_coordinates, cochainLinearMap_coordinates]
  rfl

private def cochainLift (M : Ambient.{u,v,a} k G) :
    LinearChainMap (bar.{u,v,a} k G M)
      (bar.{u,v,max a s} k G ((coefficientLift.{u,v,a,s} k G).obj M)) :=
  cochainLinearMap.{u,v,a,max a s} k G ULift.moduleEquiv.symm.toLinearMap

private lemma cochainLift_natural {M N : Ambient.{u,v,a} k G} (f : M ⟶ N) :
    (cochainLift.{u,v,a,s} k G N).comp (LinearChainMap.ofHom ((cochains.{u,v,a} k G).map f)) =
    (LinearChainMap.ofHom ((cochains.{u,v,max a s} k G).map
      ((coefficientLift.{u,v,a,s} k G).map f))).comp (cochainLift.{u,v,a,s} k G M) := by
  rw [← cochainLinearMap_ofHom k G f,
    ← cochainLinearMap_ofHom k G ((coefficientLift.{u,v,a,s} k G).map f)]
  change (cochainLinearMap.{u,v,a,max a s} k G _).comp _ =
    (cochainLinearMap.{u,v,max a s,max a s} k G _).comp (cochainLinearMap.{u,v,a,max a s} k G _)
  rw [cochainLinearMap_comp, cochainLinearMap_comp]
  rfl

private def homologyTransport (n : ℕ) :
    cohomology.{u,v,a} k G n ⋙ valueLift.{u,v,a,s} k ⟶
      coefficientLift.{u,v,a,s} k G ⋙ cohomology.{u,v,max a s} k G n where
  app M := ModuleCat.ofHom
    ((mixedHomologyMap (cochainLift.{u,v,a,s} k G M) n).comp ULift.moduleEquiv.toLinearMap)
  naturality {M N} f := by
    let f' := (coefficientLift.{u,v,a,s} k G).map f
    let B := cochains.{u,v,a} k G
    let B' := cochains.{u,v,max a s} k G
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨z⟩
    change mixedHomologyMap (cochainLift.{u,v,a,s} k G N) n ((HomologicalComplex.homologyMap (B.map f) n).hom z) =
      (HomologicalComplex.homologyMap (B'.map f') n).hom (mixedHomologyMap (cochainLift.{u,v,a,s} k G M) n z)
    rw [← mixedHomologyMap_ofHom, ← mixedHomologyMap_ofHom, ← cochainLinearMap_ofHom k G f,
      ← cochainLinearMap_ofHom k G f', mixedHomologyMap_comp, mixedHomologyMap_comp]
    change mixedHomologyMap ((cochainLinearMap.{u,v,a,max a s} k G _).comp _) n z =
      mixedHomologyMap ((cochainLinearMap.{u,v,max a s,max a s} k G f'.hom).comp
        (cochainLinearMap.{u,v,a,max a s} k G _)) n z
    rw [cochainLinearMap_comp, cochainLinearMap_comp]
    rfl

private lemma homologyTransport_boundary
    (A : Comparison.{u,v,a} k G) (C : Comparison.{u,v,max a s} k G)
    {S : ShortComplex (Ambient.{u,v,a} k G)} (h : S.ShortExact) (n : ℕ) :
    (valueLift.{u,v,a,s} k).map ((A.exact h).δ n (n+1) rfl) ≫
      (homologyTransport.{u,v,a,s} k G (n+1)).app S.X₁ =
    (homologyTransport.{u,v,a,s} k G n).app S.X₃ ≫
      (C.exact (h.map_of_exact (coefficientLift.{u,v,a,s} k G))).δ n (n+1) rfl := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨z⟩
  apply mixedBoundary_natural (A.exact h) (C.exact (h.map_of_exact (coefficientLift.{u,v,a,s} k G)))
    (cochainLift.{u,v,a,s} k G S.X₁) (cochainLift.{u,v,a,s} k G S.X₂) (cochainLift.{u,v,a,s} k G S.X₃)
    ?_ ?_ n z
  · intro i x
    exact LinearMap.congr_fun
      (congrArg (fun p => p.app i) (cochainLift_natural.{u,v,a,s} k G S.f)) x
  · intro i x
    exact LinearMap.congr_fun
      (congrArg (fun p => p.app i) (cochainLift_natural.{u,v,a,s} k G S.g)) x

private lemma lift_degreeZero_class (M : Ambient.{u,v,a} k G)
    (z : (bar.{u,v,a} k G M).X 0)
    (z' : (bar.{u,v,max a s} k G ((coefficientLift.{u,v,a,s} k G).obj M)).X 0)
    (hz : ((bar.{u,v,a} k G M).d 0 1).hom z = 0)
    (hz' : ((bar.{u,v,max a s} k G ((coefficientLift.{u,v,a,s} k G).obj M)).d 0 1).hom z' = 0)
    (h : zeroCoordinates.{u,v,max a s} k G ((coefficientLift.{u,v,a,s} k G).obj M) z' =
      ULift.up (zeroCoordinates.{u,v,a} k G M z)) :
    let P := bar.{u,v,a} k G M
    let Q := bar.{u,v,max a s} k G ((coefficientLift.{u,v,a,s} k G).obj M)
    let hn : (ComplexShape.up ℕ).next 0 = 1 := by simp [CochainComplex.next]
    mixedHomologyMap (cochainLift.{u,v,a,s} k G M) 0
        ((P.homologyπ 0).hom (P.cyclesMk z 1 hn hz)) =
      (Q.homologyπ 0).hom (Q.cyclesMk z' 1 hn hz') := by
  dsimp only
  let P := bar.{u,v,a} k G M
  let N := (coefficientLift.{u,v,a,s} k G).obj M
  let Q := bar.{u,v,max a s} k G N
  let hn : (ComplexShape.up ℕ).next 0 = 1 := by simp [CochainComplex.next]
  let g := cochainLift.{u,v,a,s} k G M
  refine mixedHomologyMap_class (K := P) (L := Q) g 0 (P.cyclesMk z 1 hn hz)
    (Q.cyclesMk z' 1 hn hz') ?_
  have h₁ : (P.iCycles 0).hom (P.cyclesMk z 1 hn hz) = z := P.i_cyclesMk ..
  have h₂ : (Q.iCycles 0).hom (Q.cyclesMk z' 1 hn hz') = z' := Q.i_cyclesMk ..
  rw [h₁, h₂]
  apply (zeroCoordinates.{u,v,max a s} k G N).injective
  let f : M →ₗ[k[G]] N := ULift.moduleEquiv.symm.toLinearMap
  have he : zeroCoordinates.{u,v,max a s} k G N (g.app 0 z) =
      ULift.up (zeroCoordinates.{u,v,a} k G M z) :=
    cochainLinearMap_coordinates.{u,v,a,max a s} k G (M := M) (N := N) f 0 z Fin.elim0
  exact h.trans he.symm

private lemma homologyTransport_zero_onUnit
    (A : Comparison.{u,v,a} k G) (C : Comparison.{u,v,max a s} k G)
    (T : Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NativeTransport.Comparison.{u,v,a,s} k G)
    (M : Ambient.{u,v,a} k G)
    (m : Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariants.{u,v,a} k G M) :
    let N := (coefficientLift.{u,v,a,s} k G).obj M
    let x := ((degreeZeroUnit.{u,v,a} k G).app M).hom m
    mixedHomologyMap (cochainLift.{u,v,a,s} k G M) 0 (((A.iso 0).hom.app M).hom x) =
      ((C.iso 0).hom.app N).hom (((T.iso 0).hom.app M).hom (ULift.up x)) := by
  dsimp only
  let N := (coefficientLift.{u,v,a,s} k G).obj M
  let m' : Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariants.{u,v,max a s} k G N :=
    ⟨ULift.up m.val, fun g => congrArg ULift.up (m.property g)⟩
  let g := cochainLift.{u,v,a,s} k G M
  obtain ⟨z, hz, hcoord, ha⟩ := A.degreeZero M m
  obtain ⟨z', hz', hcoord', hc⟩ := C.degreeZero N m'
  have ht := T.degreeZero M m
  have he :
      zeroCoordinates.{u,v,max a s} k G N z' = ULift.up (zeroCoordinates.{u,v,a} k G M z) :=
    ((zeroCoordinates_apply.{u,v,max a s} k G N z').trans hcoord').trans
      (congrArg (fun x : M => (ULift.up x : N))
        ((zeroCoordinates_apply.{u,v,a} k G M z).trans hcoord)).symm
  exact (congrArg (mixedHomologyMap g 0) ha).trans
    ((lift_degreeZero_class.{u,v,a,s} k G M z z' hz hz' he).trans
      ((congrArg ((C.iso 0).hom.app N).hom ht).trans hc).symm)

private lemma homologyTransport_zero
    (A : Comparison.{u,v,a} k G) (C : Comparison.{u,v,max a s} k G)
    (T : Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NativeTransport.Comparison.{u,v,a,s} k G) :
    (Functor.isoWhiskerRight (A.iso 0) (valueLift.{u,v,a,s} k)).hom ≫
      homologyTransport.{u,v,a,s} k G 0 =
    (T.iso 0).hom ≫ Functor.whiskerLeft (coefficientLift.{u,v,a,s} k G) (C.iso 0).hom := by
  apply NatTrans.ext
  funext M
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨x⟩
  let F := Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor.{u,v,a} k G
  let := GroupDerivedInvariants.leftExact.{u,v,a} k G
  let : IsIso (degreeZeroUnit.{u,v,a} k G) := ClassicalDerivedValues.rightZero _ _ F
  obtain ⟨m, rfl⟩ := ((asIso (degreeZeroUnit.{u,v,a} k G)).app M).toLinearEquiv.surjective x
  exact homologyTransport_zero_onUnit.{u,v,a,s} k G A C T M m

private local instance : (cochains.{u,v,a} k G).Additive where
  map_add := by intro M N f g; ext n φ; rfl

private lemma normalized_carrier
    (A : Comparison.{u,v,a} k G) (C : Comparison.{u,v,max a s} k G)
    (T : Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NativeTransport.Comparison.{u,v,a,s} k G)
    (n : ℕ) :
    (Functor.isoWhiskerRight (A.iso n) (valueLift.{u,v,a,s} k)).hom ≫
      homologyTransport.{u,v,a,s} k G n =
    (T.iso n).hom ≫ Functor.whiskerLeft (coefficientLift.{u,v,a,s} k G) (C.iso n).hom := by
  let F := Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor.{u,v,a} k G
  let V := valueLift.{u,v,a,s} k
  let L := coefficientLift.{u,v,a,s} k G
  let D := postcomposeSystem (rightSystem F) V
  let U := precomposeSystem (complexSystem (cochains.{u,v,max a s} k G) (fun h => C.exact h)) L
  letI := GroupDerivedInvariants.leftExact.{u,v,a} k G
  let hD : IsCohomological D :=
    postcomposeSystem_cohomological (UniversalDeltaFunctors.rightDelta _ _ F) V
  let hU : IsCohomological U :=
    precomposeSystem_cohomological (complexSystem_cohomological (cochains.{u,v,max a s} k G)
      (fun h => C.exact h)) L
  let f : CohomologicalMorphism D U :=
    { component i := (Functor.isoWhiskerRight (A.iso i) V).hom ≫ homologyTransport.{u,v,a,s} k G i
      comm := by
        intro S h i
        change V.map (rightBoundary F h i) ≫
            (V.map ((A.iso (i+1)).hom.app S.X₁) ≫ (homologyTransport.{u,v,a,s} k G (i+1)).app S.X₁) =
          (V.map ((A.iso i).hom.app S.X₃) ≫ (homologyTransport.{u,v,a,s} k G i).app S.X₃) ≫
            (C.exact (h.map_of_exact L)).δ i (i+1) rfl
        rw [← Category.assoc, ← V.map_comp, A.boundary h i, V.map_comp]
        rw [Category.assoc]
        exact congrArg (fun α => V.map ((A.iso i).hom.app S.X₃) ≫ α)
          (homologyTransport_boundary k G A C h i) }
  let g : CohomologicalMorphism D U :=
    { component i := (T.iso i).hom ≫ Functor.whiskerLeft L (C.iso i).hom
      comm := by
        intro S h i
        let F' := Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor.{u,v,max a s} k G
        change V.map (rightBoundary F h i) ≫
            ((T.iso (i+1)).hom.app S.X₁ ≫ (C.iso (i+1)).hom.app (L.obj S.X₁)) =
          ((T.iso i).hom.app S.X₃ ≫ (C.iso i).hom.app (L.obj S.X₃)) ≫
            (C.exact (h.map_of_exact L)).δ i (i+1) rfl
        rw [← Category.assoc, T.boundary S h i]
        change (((T.iso i).hom.app S.X₃ ≫ rightBoundary F' (h.map_of_exact L) i) ≫ _) = _
        simp only [Category.assoc]
        exact congrArg (fun α => (T.iso i).hom.app S.X₃ ≫ α)
          (C.boundary (h.map_of_exact L) i) }

  let h := UniversalDeltaFunctors.universal_of_injective_vanishing D hD
    (fun M _ n => V.map_isZero (ClassicalDerivedValues.rightInjectiveVanishing _ _ F M n)) U hU (g.component 0)
  have he : f = g := h.unique (homologyTransport_zero k G A C T) rfl
  exact congrArg (fun c : CohomologicalMorphism D U => c.component n) he

end AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NormalizedBar

namespace AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.MixedProjective

open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients
open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.MixedProjective
open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.IndependentResolution
  (Cohomology Resolution homMap OriginalLift)
open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NativeTransport
  (coefficientLift commonCoefficient commonCoefficientIso commonCoefficientMap)
open Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants (GroupModule)
open P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions (ExtWith homComplex)
open TorBalance (LinearChainMap)
open GroupCochainComparison.LargeCoordinates (coordinatesEquiv)
attribute [local instance] HasDerivedCategory.standard

universe u v a b p q s
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

private def commonBar (M : Coeff.{u,v,a} k G) :
    BarComparison.{u,v,a,max a s} k G (barResolution k G) rfl M
      (commonCoefficient.{u,v,a,s} k G M) (commonCoefficientIso.{u,v,a,s} k G M) :=
  compareBar.{u,v,a,max a s} k G M _ (commonCoefficientIso.{u,v,a,s} k G M)

private lemma barClasses_transport (M : Coeff.{u,v,a} k G) (P : GroupModule.{u,v,a} k G)
    (e : M ≃ₗ[k[G]] P)
    (J : BarComparison.{u,v,a,a} k G (barResolution k G) rfl M P e)
    (J' : BarComparison.{u,v,a,max a s} k G (barResolution k G) rfl M
      ((coefficientLift.{u,v,a,s} k G).obj P) (e.trans ULift.moduleEquiv.symm))
    (n : ℕ) (x : ExtWith (barResolution k G) M n) :
    J'.classes n x =
      mixedHomologyMap (NormalizedBar.cochainLift.{u,v,a,s} k G P) n (J.classes n x) := by
  obtain ⟨z, rfl⟩ := (cycleBoundaries (homComplex (barResolution k G).complex M) n).mkQ_surjective x
  let Q := (coefficientLift.{u,v,a,s} k G).obj P
  let l := NormalizedBar.cochainLift.{u,v,a,s} k G P
  obtain ⟨y, hy, hy'⟩ := J.class_formula n z
  obtain ⟨y', hz, hz'⟩ := J'.class_formula n z
  have h :
      ((homBar.{u,v,max a s} k G Q).iCycles n).hom y' =
        l.app n (((homBar.{u,v,a} k G P).iCycles n).hom y) := by
    rw [hy, hz]
    apply (coordinatesEquiv.{u,v,max a s} k G Q n).injective
    funext t
    have hf := J'.coordinates n z.val t
    have hg := J.coordinates n z.val t
    change coordinatesEquiv.{u,v,max a s} k G Q n (J'.cochain.app n z.val) t = _ at hf
    change coordinatesEquiv.{u,v,a} k G P n (J.cochain.app n z.val) t = _ at hg
    change coordinatesEquiv.{u,v,max a s} k G Q n (J'.cochain.app n z.val) t =
      coordinatesEquiv.{u,v,max a s} k G Q n (l.app n (J.cochain.app n z.val)) t
    refine hf.trans ?_
    symm
    let f : P →ₗ[k[G]] Q := ULift.moduleEquiv.symm.toLinearMap
    have he : coordinatesEquiv.{u,v,max a s} k G Q n (l.app n (J.cochain.app n z.val)) t =
        ULift.up (coordinatesEquiv.{u,v,a} k G P n (J.cochain.app n z.val) t) :=
      NormalizedBar.cochainLinearMap_coordinates.{u,v,a,max a s} k G (M := P) (N := Q)
        f n (J.cochain.app n z.val) t
    exact he.trans (congrArg (fun x : P => (ULift.up x : Q)) hg)
  exact hz'.trans ((mixedHomologyMap_class l n y y' h).symm.trans
    (congrArg (mixedHomologyMap l n) hy'.symm))

private lemma barClasses_lift (M : Coeff.{u,v,a} k G) (n : ℕ)
    (x : ExtWith (barResolution k G) M n) :
    (commonBar.{u,v,a,s} k G M).classes n x =
    mixedHomologyMap (NormalizedBar.cochainLift.{u,v,a,s} k G ((lift.{u,v,a} k G).obj M)) n
      ((nativeBar k G M).classes n x) :=
  barClasses_transport.{u,v,a,s} k G M ((lift.{u,v,a} k G).obj M) (nativeCoeffIso k G M)
    (nativeBar k G M) (commonBar.{u,v,a,s} k G M) n x

private lemma nativeCommon_agreement
    (A : Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NormalizedBar.Comparison.{u,v,a} k G)
    (C : Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NormalizedBar.Comparison.{u,v,max a s} k G)
    (T : Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NativeTransport.Comparison.{u,v,a,s} k G)
    (M : Coeff.{u,v,a} k G) (P : Resolution.{u,v,p} k G) (n : ℕ) (x : Cohomology k G P M n) :
    ((C.iso n).hom.app (commonCoefficient.{u,v,a,s} k G M)).hom
      (T.onOriginal k G M n ((nativeComparison.{u,v,a,p} k G A).value k G P M n x)) =
    (commonBar.{u,v,a,s} k G M).classes n
      ((IndependentResolution.compare.{u,v,a,p} k G (barResolution k G) (barProjective k G)).equiv P M n x) := by
  let e := (nativeComparison.{u,v,a,p} k G A).value k G P M n x
  let P' := (lift.{u,v,a} k G).obj M
  let j := (IndependentResolution.compare.{u,v,a,p} k G
    (barResolution k G) (barProjective k G)).equiv P M n x
  have h := congrArg (fun α => (α.app P').hom (ULift.up e)) (NormalizedBar.normalized_carrier k G A C T n)
  change mixedHomologyMap (NormalizedBar.cochainLift.{u,v,a,s} k G P') n
    (((A.iso n).hom.app P').hom e) =
    ((C.iso n).hom.app (commonCoefficient.{u,v,a,s} k G M)).hom (T.onOriginal k G M n e) at h
  change _ = (commonBar.{u,v,a,s} k G M).classes n j
  refine h.symm.trans ?_
  change mixedHomologyMap (NormalizedBar.cochainLift.{u,v,a,s} k G P') n
    (((A.iso n).hom.app P').hom ((nativeComparison.{u,v,a,p} k G A).value k G P M n x)) = _
  rw [nativeValue_bar]
  exact (barClasses_lift.{u,v,a,s} k G M n j).symm

theorem computation :
    Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.MixedProjective.computationExpected.{u,v,a,b,p,q,s} := by
  intro k G _ _
  let B := barResolution k G
  let hB := barProjective k G
  let A := NormalizedBar.normalized.{u,v,a} k G
  let A' := NormalizedBar.normalized.{u,v,b} k G
  let C := NormalizedBar.normalized.{u,v,max a b s} k G
  let T := NativeTransport.normalized.{u,v,a,max b s} k G
  let T' := NativeTransport.normalized.{u,v,b,max a s} k G
  let E := nativeComparison.{u,v,a,p} k G A
  let E' := nativeComparison.{u,v,b,q} k G A'
  let J := commonBar.{u,v,a,max b s} k G
  let J' := commonBar.{u,v,b,max a s} k G
  refine ⟨B, hB, rfl, A, A', C, T, T', E, E', J, J', barAugmentation_vertex k G,
    nativeComparison_ordinary k G A, nativeComparison_ordinary k G A',
    nativeComparison_zero k G A, nativeComparison_zero k G A',
    nativeCommon_agreement k G A C T, nativeCommon_agreement k G A' C T', ?_⟩
  intro M N P Q f g hg n x
  let M' := commonCoefficient.{u,v,a,max b s} k G M
  let N' := commonCoefficient.{u,v,b,max a s} k G N
  let f' := commonCoefficientMap.{u,v,a,b,s} k G f
  let Mv := T.onOriginal k G M n (E.value k G P M n x)
  let y := (homMap k G g f).homologyMap n x
  apply ((C.iso n).app N').toLinearEquiv.injective
  change ((C.iso n).hom.app N').hom (T'.onOriginal k G N n (E'.value k G Q N n y)) =
    ((C.iso n).hom.app N').hom
      (((Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.cohomology.{u,v,max a b s} k G n).map f').hom Mv)
  rw [nativeCommon_agreement k G A' C T']
  have h := congrArg (fun r => r.hom Mv) ((C.iso n).hom.naturality f')
  change ((C.iso n).hom.app N').hom
      (((Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.cohomology.{u,v,max a b s} k G n).map f').hom Mv) =
    ((NormalizedBar.cohomology.{u,v,max a b s} k G n).map f').hom
      (((C.iso n).hom.app M').hom (T.onOriginal k G M n (E.value k G P M n x))) at h
  rw [h, nativeCommon_agreement k G A C T]
  change (J' N).classes n ((IndependentResolution.compare.{u,v,b,q} k G B hB).equiv Q N n
      ((homMap k G g f).homologyMap n x)) = _
  rw [IndependentResolution.compare_natural k G B hB P Q M N f g hg n x]
  exact barClasses_natural k G (J M) (J' N) f f' (fun _ => rfl) n _

end AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.MixedProjective

namespace AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.IndependentInjective

open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients
open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.IndependentInjective
open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.NativeTransport
  (commonCoefficient commonCoefficientIso commonCoefficientMap)
open Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants (GroupModule)
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues (rightDegreeZeroUnit)
open TorBalance (LinearChainMap)
open HomologicalComplex

attribute [local instance] HasDerivedCategory.standard

universe u v w t a b s
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

private local instance : (invariantsFunctor.{u,v,a} k G).Additive where

private lemma coaugmentation_quasiIso {R : Type*} [Ring R] {A : ModuleCat R}
    {K : CochainComplex (ModuleCat R) ℤ} [K.IsStrictlyGE 0]
    (j : (CochainComplex.singleFunctor _ 0).obj A ⟶ K)
    (inj : Function.Injective (j.f 0).hom)
    (exact₀ : LinearMap.range (j.f 0).hom = LinearMap.ker (K.d 0 1).hom)
    (exact_pos : ∀ i : ℤ, 0 < i → K.ExactAt i) : QuasiIso j := by
  constructor
  intro i
  by_cases hi : i = 0
  · subst i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    let X := (CochainComplex.singleFunctor (ModuleCat R) 0).obj A
    have hx : IsIso (X.homologyπ 0) := X.isIso_homologyπ (-1) 0
      (by simp [CochainComplex.prev]) (single_obj_d _ _ _ _ _)
    have hk : IsIso (K.homologyπ 0) := K.isIso_homologyπ (-1) 0
      (by simp [CochainComplex.prev]) ((K.isZero_of_isStrictlyGE 0 (-1) (by norm_num)).eq_of_src _ _)
    have hn : IsIso (cyclesMap j 0) := by
      apply (ConcreteCategory.isIso_iff_bijective (cyclesMap j 0)).mpr
      constructor
      · intro x y hxy
        apply (ModuleCat.mono_iff_injective (X.iCycles 0)).mp inferInstance
        apply inj
        have h' : (cyclesMap j 0 ≫ K.iCycles 0).hom x =
            (cyclesMap j 0 ≫ K.iCycles 0).hom y := congrArg (K.iCycles 0).hom hxy
        rw [cyclesMap_i] at h'
        exact h'
      · intro y
        have hy : (K.iCycles 0).hom y ∈ LinearMap.ker (K.d 0 1).hom :=
          LinearMap.mem_ker.mpr (congrArg (fun h : K.cycles 0 ⟶ K.X 1 => h.hom y)
            (K.iCycles_d 0 1))
        obtain ⟨x, hx⟩ := (show (K.iCycles 0).hom y ∈ LinearMap.range (j.f 0).hom by
          rwa [exact₀])
        have hx0 : (X.d 0 1).hom x = 0 := by
          have h : X.d 0 1 = 0 := single_obj_d _ _ _ _ _
          rw [h, ModuleCat.hom_zero, LinearMap.zero_apply]
        refine ⟨X.cyclesMk x 1 (by simp [CochainComplex.next]) hx0, ?_⟩
        apply (ModuleCat.mono_iff_injective (K.iCycles 0)).mp inferInstance
        change (cyclesMap j 0 ≫ K.iCycles 0).hom _ = _
        rw [cyclesMap_i]
        change (j.f 0).hom ((X.iCycles 0).hom (X.cyclesMk x 1 _ hx0)) = _
        exact (congrArg (j.f 0).hom (X.i_cyclesMk x 1 _ hx0)).trans hx
    have hh : IsIso (X.homologyπ 0 ≫ homologyMap j 0) := by
      rw [homologyπ_naturality]
      infer_instance
    exact IsIso.of_isIso_comp_left (X.homologyπ 0) (homologyMap j 0)
  · rw [quasiIsoAt_iff_exactAt j i (exactAt_single_obj _ _ A i hi)]
    by_cases h : 0 < i
    · exact exact_pos i h
    · exact ExactAt.of_isZero (K.isZero_of_isStrictlyGE 0 i (by omega))

private def liftedCoaugmentation {M : Coeff.{u,v,w} k G}
    (I : Resolution.{u,v,w,a} k G M) :
    commonCoefficient.{u,v,w,max a s} k G M ⟶ (liftComplex.{u,v,w,a,s} k G I).X 0 :=
  ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp
    (I.ι.comp (commonCoefficientIso.{u,v,w,max a s} k G M).symm.toLinearMap))

private lemma coaugmentation_exact {M : Coeff.{u,v,w} k G}
    (I : Resolution.{u,v,w,a} k G M) :
    LinearMap.range (liftedCoaugmentation.{u,v,w,a,s} k G I).hom =
      LinearMap.ker ((liftComplex.{u,v,w,a,s} k G I).d 0 1).hom := by
  ext y
  induction y using ULift.rec with
  | up y =>
    have h := SetLike.ext_iff.mp I.exact_zero y
    change (∃ m : ULift (ULift M), ULift.up (I.ι m.down.down) = ULift.up y) ↔
      ULift.up ((I.complex.d 0 1).hom y) = ULift.up 0
    constructor
    · rintro ⟨m, hm⟩
      exact congrArg ULift.up (h.mp ⟨m.down.down, congrArg ULift.down hm⟩)
    · intro hy
      obtain ⟨m, hm⟩ := h.mpr (congrArg ULift.down hy)
      exact ⟨ULift.up (ULift.up m), congrArg ULift.up hm⟩

private def coaugmentation {M : Coeff.{u,v,w} k G}
    (I : Resolution.{u,v,w,a} k G M) :
    (CochainComplex.singleFunctor _ 0).obj (commonCoefficient.{u,v,w,max a s} k G M) ⟶
      liftComplex.{u,v,w,a,s} k G I :=
  mkHomFromSingle (liftedCoaugmentation.{u,v,w,a,s} k G I) (by
    intro j hj
    change (0 : ℤ) + 1 = j at hj
    subst j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    have hm : (liftedCoaugmentation.{u,v,w,a,s} k G I).hom m ∈
        LinearMap.ker ((liftComplex.{u,v,w,a,s} k G I).d 0 1).hom := by
      rw [← coaugmentation_exact]
      exact ⟨m, rfl⟩
    exact LinearMap.mem_ker.mp hm)

private def fixedLiftEquiv (X : Coeff.{u,v,a} k G) :
    ULift.{max u v w s} (invariants k G X) ≃ₗ[k]
      Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariants.{u,v,max w a s} k G
        ((termLift.{u,v,a,max w s} k G).obj X) where
  toFun x := ⟨ULift.up x.down.val, fun g => congrArg ULift.up (x.down.property g)⟩
  invFun y := ULift.up ⟨y.val.down, fun g => congrArg ULift.down (y.property g)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def fixedLiftIso {M : Coeff.{u,v,w} k G} (I : Resolution.{u,v,w,a} k G M) :
    (((fixedTermLift.{u,a,max v w s} k).mapHomologicalComplex (.up ℤ)).obj
      (I.fixedComplex k G)) ≅
      (((commonInvariants.{u,v,w,a,s} k G).mapHomologicalComplex (.up ℤ)).obj
        (liftComplex.{u,v,w,a,s} k G I)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (fixedLiftEquiv.{u,v,w,a,s} k G (I.complex.X n)).toModuleIso)
    (by intro i j hij; apply ModuleCat.hom_ext; ext x; rfl)

def ambientModel {M : Coeff.{u,v,w} k G} (I : Resolution.{u,v,w,a} k G M) :
    AmbientModel.{u,v,w,a,s} k G I := by
  let L := termLift.{u,v,a,max w s} k G
  let K := liftComplex.{u,v,w,a,s} k G I
  let A := commonCoefficient.{u,v,w,max a s} k G M
  let ι := liftedCoaugmentation.{u,v,w,a,s} k G I
  let j := coaugmentation.{u,v,w,a,s} k G I
  letI : K.IsStrictlyGE 0 :=
    (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff I.complex L 0).mpr I.nonnegative
  have hj : j.f 0 = (singleObjXSelf (.up ℤ) 0 A).hom ≫ ι := mkHomFromSingle_f _ _
  refine ⟨inferInstance, j, ?_, ?_, ?_, fixedLiftIso.{u,v,w,a,s} k G I, fun _ _ => rfl⟩
  · intro m
    rw [hj]
    change ι.hom ((singleObjXSelf (.up ℤ) 0 A).hom.hom
      ((singleObjXSelf (.up ℤ) 0 A).inv.hom (ULift.up (ULift.up m)))) = ULift.up (I.ι m)
    let e := singleObjXSelf (.up ℤ) 0 A
    change ι.hom (e.toLinearEquiv (e.toLinearEquiv.symm (ULift.up (ULift.up m)))) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  · apply coaugmentation_quasiIso j
    · rw [hj]
      exact ULift.up_injective.comp (I.ι_injective.comp
        ((commonCoefficientIso.{u,v,w,max a s} k G M).symm.injective.comp
          (singleObjXSelf (.up ℤ) 0 A).toLinearEquiv.injective))
    · rw [hj]
      change LinearMap.range (ι.hom.comp (singleObjXSelf (.up ℤ) 0 A).hom.hom) = _
      rw [LinearMap.range_comp, ModuleCat.range_eq_top_of_epi,
        Submodule.map_top]
      exact coaugmentation_exact k G I
    · intro q hq
      let n : ℕ := (q - 1).toNat
      have hn : (n : ℤ) = q - 1 := Int.toNat_of_nonneg (by omega)
      have hd₀ : (ComplexShape.up ℤ).prev q = (n : ℤ) := by rw [CochainComplex.prev, hn]
      have hd₁ : (ComplexShape.up ℤ).next q = (n : ℤ) + 2 := by
        rw [CochainComplex.next, hn]; omega
      have hnq : q = (n : ℤ) + 1 := by omega
      rw [HomologicalComplex.exactAt_iff' _ _ _ _ hd₀ hd₁]
      have hI : (I.complex.sc' (n : ℤ) q ((n : ℤ) + 2)).Exact := by
        rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
        change LinearMap.range (I.complex.d (n : ℤ) q).hom =
          LinearMap.ker (I.complex.d q ((n : ℤ) + 2)).hom
        rw [hnq]
        exact I.exact_succ n
      exact hI.map L
  · intro q
    apply (Module.injective_iff_injective_object k[G] (K.X q)).mp
    exact ((I.baer q).of_equiv ULift.moduleEquiv.symm).injective

private def ambientMap {M : Coeff.{u,v,w} k G} {N : Coeff.{u,v,t} k G}
    {I : Resolution.{u,v,w,a} k G M} {J : Resolution.{u,v,t,b} k G N}
    (g : LinearChainMap I.complex J.complex) :
    liftComplex.{u,v,w,a,max t b s} k G I ⟶ liftComplex.{u,v,t,b,max w a s} k G J where
  f n := ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp
    ((g.app n).comp ULift.moduleEquiv.toLinearMap))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg ULift.up (g.comm_apply i j x.down)

private lemma singleMap_apply {R : Type*} [Ring R] {M N : ModuleCat R} (f : M ⟶ N) (x : M) :
    (((CochainComplex.singleFunctor _ 0).map f).f 0).hom
        ((singleObjXSelf (.up ℤ) 0 M).inv.hom x) =
      (singleObjXSelf (.up ℤ) 0 N).inv.hom (f.hom x) := by
  have h : (singleObjXSelf (.up ℤ) 0 M).inv ≫ ((CochainComplex.singleFunctor _ 0).map f).f 0 =
      f ≫ (singleObjXSelf (.up ℤ) 0 N).inv := by
    change (singleObjXSelf (.up ℤ) 0 M).inv ≫ ((single _ (.up ℤ) 0).map f).f 0 = _
    rw [single_map_f_self, Iso.inv_hom_id_assoc]
  exact congrArg (fun p => p.hom x) h

private lemma coaugmentation_square {M : Coeff.{u,v,w} k G} {N : Coeff.{u,v,t} k G}
    {I : Resolution.{u,v,w,a} k G M} {J : Resolution.{u,v,t,b} k G N}
    (A : AmbientModel.{u,v,w,a,max t b s} k G I)
    (B : AmbientModel.{u,v,t,b,max w a s} k G J)
    (f : M →ₗ[k[G]] N) (g : LinearChainMap I.complex J.complex) (hg : Lifts f g) :
    A.coaugmentation ≫ ambientMap.{u,v,w,t,a,b,s} k G g =
      (CochainComplex.singleFunctor _ 0).map (commonCoefficientMap.{u,v,w,t,max a b s} k G f) ≫
        B.coaugmentation := by
  apply from_single_hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let e := singleObjXSelf (.up ℤ) 0 (commonCoefficient.{u,v,w,max t a b s} k G M)
  obtain ⟨⟨⟨m⟩⟩, rfl⟩ := e.toLinearEquiv.symm.surjective x
  let f' := commonCoefficientMap.{u,v,w,t,max a b s} k G f
  have h := singleMap_apply f' (ULift.up (ULift.up m))
  change ((ambientMap.{u,v,w,t,a,b,s} k G g).f 0).hom
    ((A.coaugmentation.f 0).hom (e.inv.hom (ULift.up (ULift.up m)))) =
    (B.coaugmentation.f 0).hom
      ((((CochainComplex.singleFunctor _ 0).map f').f 0).hom (e.inv.hom (ULift.up (ULift.up m))))
  have hA := A.coaugmentation_apply m
  change (A.coaugmentation.f 0).hom (e.inv.hom (ULift.up (ULift.up m))) = _ at hA
  rw [hA, h]
  have hB := B.coaugmentation_apply (f m)
  change (B.coaugmentation.f 0).hom
    ((singleObjXSelf (.up ℤ) 0 (commonCoefficient.{u,v,t,max w a b s} k G N)).inv.hom
      (f'.hom (ULift.up (ULift.up m)))) = _ at hB
  rw [hB]
  exact congrArg ULift.up (hg m)

theorem resolutionLifts :
    Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.IndependentInjective.resolutionLiftsExpected.{u,v,w,a,b,s} := by
  intro k G _ _ M N f I J
  let A := ambientModel.{u,v,w,a,max s b} k G I
  let B := ambientModel.{u,v,s,b,max w a} k G J
  letI := B.nonnegative
  letI : (liftComplex.{u,v,s,b,max w a} k G J).IsKInjective :=
    (BoundedKModels.kInjective_iff _ _).mp (BoundedKModels.boundedBelow_injective _ _ 0
      (fun q hq => (liftComplex.{u,v,s,b,max w a} k G J).isZero_of_isStrictlyGE 0 q hq) B.injective)
  letI := A.exact
  let f' := commonCoefficientMap.{u,v,w,s,max a b} k G f
  obtain ⟨g, ⟨hg⟩⟩ := ExtShiftedHom.injective_lift _ _ _ _ A.coaugmentation B.coaugmentation f'
  let h : LinearChainMap I.complex J.complex :=
    { app n := ULift.moduleEquiv.toLinearMap.comp ((g.f n).hom.comp ULift.moduleEquiv.symm.toLinearMap)
      comm i j := by
        apply LinearMap.ext
        intro z
        exact congrArg (fun p => (p.hom (ULift.up z)).down) (g.comm i j) }
  refine ⟨h, fun m => ?_⟩
  have h0 := hg.comm 0
  let X := commonCoefficient.{u,v,w,max s a b} k G M
  let x := (singleObjXSelf (.up ℤ) 0 X).inv.hom (ULift.up (ULift.up m))
  have h₁ : ((CochainComplex.singleFunctor _ 0).obj X).d 0 1 = 0 := single_obj_d _ _ _ _ _
  have hz := (liftComplex.{u,v,s,b,max w a} k G J).isZero_of_isStrictlyGE 0 (-1) (by norm_num)
  have h₂ : (liftComplex.{u,v,s,b,max w a} k G J).d (-1) 0 = 0 := hz.eq_of_src _ _
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by decide),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by decide)] at h0
  change _ = _ ≫ hg.hom 1 0 + hg.hom 0 (-1) ≫ _ + _ at h0
  rw [h₁, h₂, zero_comp, comp_zero, zero_add, zero_add] at h0
  have he := congrArg (fun p => p.hom x) h0
  change (g.f 0).hom ((A.coaugmentation.f 0).hom x) =
    (B.coaugmentation.f 0).hom ((((CochainComplex.singleFunctor _ 0).map f').f 0).hom x) at he
  have hA : (A.coaugmentation.f 0).hom x = ULift.up (I.ι m) := A.coaugmentation_apply m
  have hB := B.coaugmentation_apply (f m)
  have hmap := singleMap_apply f' (ULift.up (ULift.up m))
  change (((CochainComplex.singleFunctor _ 0).map f').f 0).hom x =
    (singleObjXSelf (.up ℤ) 0 (commonCoefficient.{u,v,s,max w a b} k G N)).inv.hom
      (ULift.up (ULift.up (f m))) at hmap
  rw [hA, hmap, hB] at he
  exact congrArg ULift.down he

open private localizedAugmentation homologyFactors from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupDerivedInvariants

private lemma resolutionModelMap_eq {M : GroupModule.{u,v,w} k G}
    {I : CochainComplex (GroupModule.{u,v,w} k G) ℤ} [I.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor _ 0).obj M ⟶ I) (hi : QuasiIso i)
    (hI : ∀ q, Injective (I.X q)) (n : ℕ) :
    resolutionModelMap (Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor.{u,v,w} k G)
      i hi n = (GroupDerivedInvariants.injectiveValueIso i hi hI n).inv := by
  simp only [resolutionModelMap, GroupDerivedInvariants.injectiveValueIso, Iso.trans_inv, Iso.app_inv,
    Functor.mapIso_inv, Iso.symm_inv, homologyFactors, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Category.comp_id, DerivedCategory.Plus.QCompιIso_inv_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  let L : CochainComplex.Plus (GroupModule.{u,v,w} k G) :=
    ⟨(CochainComplex.singleFunctor _ 0).obj M, 0, inferInstance⟩
  let K : CochainComplex.Plus (GroupModule.{u,v,w} k G) := ⟨I, 0, inferInstance⟩
  let q : L ⟶ K := ObjectProperty.homMk i
  have h : DerivedCategory.Plus.Q.map q = localizedAugmentation i := by
    apply DerivedCategory.Plus.ι.map_injective
    dsimp only [localizedAugmentation]
    rw [CategoryTheory.Functor.map_preimage]
    rfl
  letI : IsIso (DerivedCategory.Plus.Q.map q) :=
    Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso _) q hi
  letI : IsIso (localizedAugmentation i) := h ▸ inferInstanceAs (IsIso (DerivedCategory.Plus.Q.map q))
  have hinv : inv (DerivedCategory.Plus.Q.map q) = inv (localizedAugmentation i) := by
    exact (Iso.inv_eq_inv (asIso (DerivedCategory.Plus.Q.map q)) (asIso (localizedAugmentation i))).mpr h
  let F := Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor.{u,v,w} k G
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat k) (n : ℤ)
  let a := (DerivedCategory.homologyFunctorFactors (ModuleCat k) (n : ℤ)).inv.app
    ((F.mapHomologicalComplex (.up ℤ)).obj I)
  exact congrArg (fun α => a ≫ H.map (F.rightDerivedFunctorPlusUnit.app K ≫
    F.rightDerivedFunctorPlus.map α)) hinv

private lemma fixedIso_square {M : Coeff.{u,v,w} k G} {N : Coeff.{u,v,t} k G}
    {I : Resolution.{u,v,w,a} k G M} {J : Resolution.{u,v,t,b} k G N}
    (A : AmbientModel.{u,v,w,a,max t b s} k G I)
    (B : AmbientModel.{u,v,t,b,max w a s} k G J)
    (g : LinearChainMap I.complex J.complex) :
    liftFixedMap.{u,a,b,max v w t s} k (fixedMap k G g) ≫ B.fixedIso.hom =
      A.fixedIso.hom ≫
        ((commonInvariants.{u,v,w,a,max t b s} k G).mapHomologicalComplex (.up ℤ)).map
          (ambientMap.{u,v,w,t,a,b,s} k G g) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨x⟩
  apply Subtype.ext
  change ((B.fixedIso.hom.f n).hom (ULift.up ((fixedMap k G g).app n x))).val =
    ULift.up (g.app n (((A.fixedIso.hom.f n).hom (ULift.up x)).val.down))
  rw [B.fixedIso_apply, A.fixedIso_apply]
  rfl

private lemma modelMap_natural {M N : GroupModule.{u,v,w} k G}
    {I J : CochainComplex (GroupModule.{u,v,w} k G) ℤ} [I.IsStrictlyGE 0] [J.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor _ 0).obj M ⟶ I) (j : (CochainComplex.singleFunctor _ 0).obj N ⟶ J)
    (hi : QuasiIso i) (hj : QuasiIso j)
    (hI : ∀ q, Injective (I.X q)) (hJ : ∀ q, Injective (J.X q))
    (f : M ⟶ N) (g : I ⟶ J)
    (h : i ≫ g = (CochainComplex.singleFunctor _ 0).map f ≫ j) (n : ℕ) :
    let F := Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor.{u,v,w} k G
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map g) (n : ℤ) ≫
      resolutionModelMap F j hj n =
    resolutionModelMap F i hi n ≫ (Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.cohomology.{u,v,w}
      k G n).map f := by
  dsimp only
  rw [resolutionModelMap_eq k G j hj hJ, resolutionModelMap_eq k G i hi hI]
  have he := GroupDerivedInvariants.injectiveValueIso_naturality i hi j hj hI hJ f g (Homotopy.ofEq h) n
  apply (cancel_mono (GroupDerivedInvariants.injectiveValueIso j hj hJ n).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, he,
    Iso.inv_hom_id_assoc]

theorem naturality :
    Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.IndependentInjective.naturalityExpected.{u,v,w,a,b,s,t} := by
  intro k G _ _ S T M N f I J C D g hg n z
  rw [D.agrees, C.agrees]
  let A := C.model
  let B := D.model
  letI := A.nonnegative
  letI := B.nonnegative
  let F := commonInvariants.{u,v,w,a,max t b s} k G
  let g' := ambientMap.{u,v,w,t,a,b,s} k G g
  let f' := commonCoefficientMap.{u,v,w,t,max a b s} k G f
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{max u v w t a b s} k) (.up ℤ) (n : ℤ)
  let e := ULift.moduleEquiv.symm.trans
    (homologyLift.{u,a,max v w t b s} k (C := I.fixedComplex k G) (n : ℤ)).toLinearEquiv
  let e' := ULift.moduleEquiv.symm.trans
    (homologyLift.{u,b,max v w t a s} k (C := J.fixedComplex k G) (n : ℤ)).toLinearEquiv
  let l := liftFixedMap.{u,a,b,max v w t s} k (fixedMap k G g)
  have hl : e' (fixedCohomologyMap.{u,a,b,max v w t s} k (fixedMap k G g) n z) =
      (H.map l).hom (e z) := e'.apply_symm_apply _
  have h := congrArg H.map (fixedIso_square.{u,v,w,t,a,b,s} k G A B g)
  rw [H.map_comp, H.map_comp] at h
  have hr := modelMap_natural.{u,v,max w t a b s} k G A.coaugmentation B.coaugmentation A.exact B.exact
    A.injective B.injective f' g' (coaugmentation_square.{u,v,w,t,a,b,s} k G A B f g hg) n
  change (resolutionModelMap F B.coaugmentation B.exact n).hom
      ((H.map B.fixedIso.hom).hom (e' (fixedCohomologyMap.{u,a,b,max v w t s} k (fixedMap k G g) n z))) =
    _
  rw [hl]
  have hc := congrArg (fun m => m.hom (e z)) h
  change (H.map B.fixedIso.hom).hom ((H.map l).hom (e z)) =
    (H.map ((F.mapHomologicalComplex (.up ℤ)).map g')).hom ((H.map A.fixedIso.hom).hom (e z)) at hc
  rw [hc]
  exact congrArg (fun m => m.hom ((H.map A.fixedIso.hom).hom (e z))) hr

section DegreeZero
open CategoryTheory.Functor
open private mappedStalkIso from MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B] [EnoughInjectives A]
  (F : A ⥤ B) [F.Additive]

private lemma degreeZeroUnit_onModel {M : A} {I : CochainComplex A ℤ} [I.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor A 0).obj M ⟶ I) (hi : QuasiIso i) :
    let S := (singleMapHomologicalComplex F (.up ℤ) 0).app M
    let E := singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)
    E.inv ≫ homologyMap (S.inv ≫ (F.mapHomologicalComplex (.up ℤ)).map i) 0 ≫
      resolutionModelMap F i hi 0 = (rightDegreeZeroUnit F).app M := by
  dsimp only
  let K : CochainComplex.Plus A := ⟨I, 0, inferInstance⟩
  let L : CochainComplex.Plus A := ⟨(CochainComplex.singleFunctor A 0).obj M, 0, inferInstance⟩
  let l : L ⟶ K := ObjectProperty.homMk i
  let S := (singleMapHomologicalComplex F (.up ℤ) 0).app M
  let E := singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)
  let R := F.rightDerivedFunctorPlus
  let H := DerivedCategory.Plus.homologyFunctor B 0
  let e := DerivedCategory.homologyFunctorFactors B 0
  let U := F.rightDerivedFunctorPlusUnit
  haveI : IsIso (DerivedCategory.Plus.Q.map l) :=
    Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso A) l hi
  change E.inv ≫ homologyMap (S.inv ≫ (F.mapHomologicalComplex (.up ℤ)).map i) 0 ≫
    (e.inv.app _ ≫ H.map (U.app K ≫ R.map (inv (DerivedCategory.Plus.Q.map l)))) = _
  simp only [homologyMap_comp, Category.assoc]
  have hn := e.inv.naturality ((F.mapHomologicalComplex (.up ℤ)).map i)
  have hn' : homologyMap ((F.mapHomologicalComplex (.up ℤ)).map i) 0 ≫ e.inv.app _ =
      e.inv.app _ ≫ H.map (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map l)) := hn
  rw [reassoc_of% hn', ← H.map_comp]
  have hu := U.naturality l
  change DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map l) ≫ U.app K =
    U.app L ≫ R.map (DerivedCategory.Plus.Q.map l) at hu
  rw [← Category.assoc (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map l)), hu,
    Category.assoc, ← R.map_comp, IsIso.hom_inv_id, R.map_id]
  erw [Category.comp_id]
  have hs := e.inv.naturality S.inv
  erw [reassoc_of% hs]
  simp only [rightDegreeZeroUnit, NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp, Functor.associator_inv_app, Category.id_comp]
  rw [F.rightDerivedFunctorPlusUnit_app]
  simp [DerivedCategory.singleFunctorCompHomologyFunctorIso, mappedStalkIso, Category.assoc,
    ← Functor.map_comp]
  let L' : CochainComplex.Plus B := ⟨(CochainComplex.singleFunctor _ 0).obj (F.obj M), 0, inferInstance⟩
  let α : L' ⟶ F.mapCochainComplexPlus.obj L := ObjectProperty.homMk S.inv
  let u := (DerivedCategory.Plus.quotientCompQhIso B).inv.app (F.mapCochainComplexPlus.obj L) ≫
    DerivedCategory.Plus.Qh.map (F.quotientCompMapHomotopyCategoryPlusIso.inv.app L) ≫
    F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient A).obj L) ≫
    F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.quotientCompQhIso A).hom.app L)
  change E.inv ≫ e.inv.app L'.obj ≫ H.map (DerivedCategory.Plus.Q.map α) ≫ H.map u = _
  rw [← H.map_comp]
  congr 2
  · apply congrArg H.map
    apply DerivedCategory.Plus.ι.map_injective
    have hA (J : CochainComplex A ℤ) :
        (DerivedCategory.quotientCompQhIso A).hom.app J = 𝟙 _ := rfl
    have hB (J : CochainComplex B ℤ) :
        (DerivedCategory.quotientCompQhIso B).inv.app J = 𝟙 _ := rfl
    have hB' (J : CochainComplex B ℤ) :
        (DerivedCategory.quotientCompQhIso B).hom.app J = 𝟙 _ := rfl
    have hfac (J : CochainComplex A ℤ) :
        (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app J = 𝟙 _ := rfl
    have hmap : F.quotientCompMapHomotopyCategoryPlusIso.inv.app L = 𝟙 _ := rfl
    have hα : (DerivedCategory.Plus.Q.map α).hom = DerivedCategory.Q.map S.inv := rfl
    simp [u, hα, hmap, hA, hB, hB', hfac,
      DerivedCategory.Plus.quotientCompQhIso, DerivedCategory.singleFunctorIsoCompQh,
      DerivedCategory.singleFunctorIsoCompQ, HomotopyCategory.singleFunctorPostcompQuotientIso,
      HomotopyCategory.singleFunctorsPostcompQuotientIso, DerivedCategory.singleFunctorsPostcompQhIso]
    let A₀ := DerivedCategory.Plus.Q.obj L
    let B₀ := DerivedCategory.Plus.Q.obj L'
    let B₁ := DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj L)
    let pB : B₀ ⟶ B₁ :=
      (FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι).preimage
        (𝟙 (DerivedCategory.Plus.ι.obj B₀) ≫ 𝟙 (DerivedCategory.Plus.ι.obj B₀) ≫
          DerivedCategory.Qh.map ((HomotopyCategory.quotient B (.up ℤ)).map S.inv))
    let pA : A₀ ⟶ A₀ :=
      (FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι).preimage (𝟙 (DerivedCategory.Plus.ι.obj A₀))
    have hpB : pB.hom = DerivedCategory.Q.map S.inv := by
      change _ =
        DerivedCategory.Qh.map ((HomotopyCategory.quotient B (.up ℤ)).map S.inv)
      have he : pB.hom =
          𝟙 (DerivedCategory.Plus.ι.obj B₀) ≫ 𝟙 (DerivedCategory.Plus.ι.obj B₀) ≫
            DerivedCategory.Qh.map ((HomotopyCategory.quotient B (.up ℤ)).map S.inv) :=
        (FullyFaithful.ofFullyFaithful (DerivedCategory.Plus.ι (C := B))).map_preimage
          (X := B₀) (Y := B₁)
          (𝟙 (DerivedCategory.Plus.ι.obj B₀) ≫ 𝟙 (DerivedCategory.Plus.ι.obj B₀) ≫
            DerivedCategory.Qh.map ((HomotopyCategory.quotient B (.up ℤ)).map S.inv))
      rw [he, Category.id_comp, Category.id_comp]
    have hpA : pA = 𝟙 A₀ :=
      (FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι).preimage_id
    let h := (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient A).obj L)).hom
    change DerivedCategory.Q.map S.inv ≫ 𝟙 (DerivedCategory.Plus.ι.obj B₁) ≫ h ≫
        (R.map (𝟙 A₀)).hom = pB.hom ≫ h ≫ (R.map pA).hom
    rw [hpA, hpB]
    erw [Category.id_comp]

end DegreeZero

private lemma model_degreeZero {M : Coeff.{u,v,w} k G}
    {I : Resolution.{u,v,w,a} k G M} (A : AmbientModel.{u,v,w,a,s} k G I)
    (m : invariants k G M) :
    ∃ z : (I.fixedComplex k G).cycles 0,
      (((I.fixedComplex k G).iCycles 0).hom z).val = I.ι m.val ∧
      A.toDerived k G 0 (((I.fixedComplex k G).homologyπ 0).hom z) =
        ((rightDegreeZeroUnit (commonInvariants.{u,v,w,a,s} k G)).app
          (commonCoefficient.{u,v,w,max a s} k G M)).hom
          ⟨ULift.up (ULift.up m.val), fun g => congrArg (fun z => ULift.up (ULift.up z)) (m.property g)⟩ := by
  letI := A.nonnegative
  let C := I.fixedComplex k G
  let F := commonInvariants.{u,v,w,a,s} k G
  let X := commonCoefficient.{u,v,w,max a s} k G M
  let x : F.obj X :=
    ⟨ULift.up (ULift.up m.val), fun g => congrArg (fun z => ULift.up (ULift.up z)) (m.property g)⟩
  let e := (singleMapHomologicalComplex F (.up ℤ) 0).app X
  let E := singleObjHomologySelfIso (.up ℤ) 0 (F.obj X)
  let C' := (F.mapHomologicalComplex (.up ℤ)).obj (liftComplex.{u,v,w,a,s} k G I)
  let f := e.inv ≫ (F.mapHomologicalComplex (.up ℤ)).map A.coaugmentation
  let z₀ := (singleObjCyclesSelfIso (.up ℤ) 0 (F.obj X)).inv.hom x
  let y := (cyclesMap f 0).hom z₀
  let z' := (cyclesMap A.fixedIso.inv 0).hom y
  let L := fixedTermLift.{u,a,max v w s} k
  let y₀ : L.obj (C.cycles 0) := ((C.sc 0).mapCyclesIso L).hom.hom z'
  let z := y₀.down
  have hy : (C'.iCycles 0).hom y = ⟨ULift.up (I.ι m.val), fun g => by
      change ULift.up (MonoidAlgebra.single g (1 : k) • I.ι m.val) = ULift.up (I.ι m.val)
      rw [← I.ι.map_smul, m.property g]⟩ := by
    apply Subtype.ext
    let Y := (CochainComplex.singleFunctor _ 0).obj (F.obj X)
    let eY := singleObjXSelf (.up ℤ) 0 (F.obj X)
    let eX := singleObjXSelf (.up ℤ) 0 X
    have hh : (singleObjCyclesSelfIso (.up ℤ) 0 (F.obj X)).inv ≫ Y.iCycles 0 ≫ f.f 0 =
        F.map (eX.inv ≫ A.coaugmentation.f 0) := by
      rw [singleObjCyclesSelfIso_inv_iCycles_assoc]
      change eY.inv ≫ (e.inv.f 0 ≫ F.map (A.coaugmentation.f 0)) = _
      have he : e.inv.f 0 = eY.hom ≫ F.map eX.inv :=
        singleMapHomologicalComplex_inv_app_self F (.up ℤ) 0 X
      rw [he]
      simp only [Category.assoc]
      rw [Iso.inv_hom_id_assoc, F.map_comp]
    have h : (C'.iCycles 0).hom y = (cyclesMap f 0 ≫ C'.iCycles 0).hom z₀ := rfl
    rw [h, cyclesMap_i]
    change (((singleObjCyclesSelfIso (.up ℤ) 0 (F.obj X)).inv ≫ Y.iCycles 0 ≫ f.f 0).hom x).val = _
    rw [hh]
    exact A.coaugmentation_apply m.val

  have hz' : (((L.mapHomologicalComplex (.up ℤ)).obj C).iCycles 0).hom z' =
      ULift.up ((C.iCycles 0).hom z) := by
    symm
    exact congrArg (fun p => p.hom z') ((C.sc 0).mapCyclesIso_hom_iCycles L)
  have hzy : (cyclesMap A.fixedIso.hom 0).hom z' = y := by
    change (cyclesMap A.fixedIso.hom 0).hom ((cyclesMap A.fixedIso.inv 0).hom y) = y
    have h := congrArg (fun p : C' ⟶ C' => (cyclesMap p 0).hom y) A.fixedIso.inv_hom_id
    rw [cyclesMap_comp] at h
    refine h.trans ?_
    exact congrArg (fun p : C'.cycles 0 ⟶ C'.cycles 0 => p.hom y) (cyclesMap_id C' 0)
  have hz : ULift.up (((C.iCycles 0).hom z).val) = ULift.up (I.ι m.val) := by
    have h := congrArg (fun p => p.hom z') (cyclesMap_i A.fixedIso.hom 0)
    change (C'.iCycles 0).hom ((cyclesMap A.fixedIso.hom 0).hom z') =
      (A.fixedIso.hom.f 0).hom ((((L.mapHomologicalComplex (.up ℤ)).obj C).iCycles 0).hom z') at h
    rw [hzy, hz'] at h
    rw [hy] at h
    exact (A.fixedIso_apply 0 _).symm.trans (congrArg Subtype.val h.symm)
  refine ⟨z, congrArg ULift.down hz, ?_⟩
  have hclass := uliftHomology_class (C.sc 0) z z' hz'
  have hclass' : (homologyLift.{u,a,max v w s} k (C := C) 0).hom.hom
      (ULift.up ((C.homologyπ 0).hom z)) =
      (((L.mapHomologicalComplex (.up ℤ)).obj C).homologyπ 0).hom z' :=
    by
      let E' := (homologyLift.{u,a,max v w s} k (C := C) 0).toLinearEquiv
      apply E'.symm.injective
      change E'.symm (E' _) = E'.symm _
      rw [LinearEquiv.symm_apply_apply]
      exact hclass.symm
  have hπ := congrArg (fun p => p.hom z') (homologyπ_naturality A.fixedIso.hom 0)
  change (homologyMap A.fixedIso.hom 0).hom
        ((((L.mapHomologicalComplex (.up ℤ)).obj C).homologyπ 0).hom z') =
      (C'.homologyπ 0).hom ((cyclesMap A.fixedIso.hom 0).hom z') at hπ
  have hπ' := congrArg (fun p => p.hom z₀) (homologyπ_naturality f 0)
  change (homologyMap f 0).hom ((((CochainComplex.singleFunctor _ 0).obj (F.obj X)).homologyπ 0).hom z₀) =
    (C'.homologyπ 0).hom y at hπ'
  have hE : (((CochainComplex.singleFunctor _ 0).obj (F.obj X)).homologyπ 0).hom z₀ = E.inv.hom x :=
    congrArg (fun p => p.hom x) (singleObjCyclesSelfIso_inv_homologyπ (.up ℤ) 0 (F.obj X))
  rw [hE] at hπ'
  change (resolutionModelMap F A.coaugmentation A.exact 0).hom
    ((homologyMap A.fixedIso.hom 0).hom
      ((homologyLift.{u,a,max v w s} k (C := C) 0).hom.hom (ULift.up ((C.homologyπ 0).hom z)))) = _
  rw [hclass', hπ, hzy, ← hπ']
  exact congrArg (fun p => p.hom x) (degreeZeroUnit_onModel F A.coaugmentation A.exact)

theorem computation :
    Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.IndependentInjective.computationExpected.{u,v,w,a,s} := by
  intro k G _ _ T M I
  let A := ambientModel.{u,v,w,a,s} k G I
  letI := A.nonnegative
  let F := commonInvariants.{u,v,w,a,s} k G
  let e (n : ℕ) :=
    ((ULift.moduleEquiv.symm.trans
      (homologyLift.{u,a,max v w s} k (C := I.fixedComplex k G) (n : ℤ)).toLinearEquiv).trans
      (((HomologicalComplex.homologyFunctor _ (.up ℤ) (n : ℤ)).mapIso A.fixedIso).toLinearEquiv)).trans
      (GroupDerivedInvariants.injectiveValueIso A.coaugmentation A.exact A.injective n).symm.toLinearEquiv
  refine ⟨⟨A, fun n => (e n).trans (T.onOriginal k G M n).symm, ?_, ?_⟩⟩
  · intro n x
    change T.onOriginal k G M n ((T.onOriginal k G M n).symm (e n x)) = _
    rw [LinearEquiv.apply_symm_apply]
    change (GroupDerivedInvariants.injectiveValueIso A.coaugmentation A.exact A.injective n).inv.hom _ =
      (resolutionModelMap F A.coaugmentation A.exact n).hom _
    rw [resolutionModelMap_eq k G _ _ A.injective]
    rfl
  · intro m
    obtain ⟨z, hz, hclass⟩ := model_degreeZero k G A m
    refine ⟨z, hz, ?_⟩
    apply (T.onOriginal k G M 0).injective
    change T.onOriginal k G M 0 ((T.onOriginal k G M 0).symm _) = _
    rw [LinearEquiv.apply_symm_apply]
    have ha := T.degreeZero ((lift.{u,v,w} k G).obj M)
      (Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.IndependentResolution.liftedInvariant k G M m)
    change _ = ((T.iso 0).hom.app _).hom (ULift.up _)
    rw [ha]
    rw [← hclass]
    change (GroupDerivedInvariants.injectiveValueIso A.coaugmentation A.exact A.injective 0).inv.hom _ =
      (resolutionModelMap F A.coaugmentation A.exact 0).hom _
    rw [resolutionModelMap_eq k G _ _ A.injective]
    rfl

end AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.IndependentInjective
