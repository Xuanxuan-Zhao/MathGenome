import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DerivedGroupHomologyOriginalCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DerivedGroupHomology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open CategoryTheory
open scoped MonoidAlgebra
open P103.Specs.Ch10.Complexes P103.Specs.Ch11.ExtTorDefinitions P103.BalancedTensor
open P103.Specs.Ch10.HomologySequence
namespace AdvancedHomologicalAlgebra.DerivedGroupHomologyOriginal
open DerivedGroupHomology TorBalance
universe u v a b c d e f s
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

def tensorAction {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]}
    (p : CoefficientMap k G M N) (P : Model) :
    LinearChainMap (P.complex k G M) (P.complex k G N) :=
  tensorLinearChainMap (l := {
    app := fun _ => LinearMap.id
    comm := by intros; simp }) p

private lemma restrictMap_action {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]}
    (p : CoefficientMap k G M N) (g : G) (m : RestrictScalars k k[G] M) :
    restrictMap k G p (GroupCoinvariants.coefficientRepresentation k G M g m) =
      GroupCoinvariants.coefficientRepresentation k G N g (restrictMap k G p m) := by
  apply (RestrictScalars.addEquiv k k[G] N).injective
  change p (RestrictScalars.addEquiv k k[G] M
      (GroupCoinvariants.coefficientRepresentation k G M g m)) =
    RestrictScalars.addEquiv k k[G] N
      (GroupCoinvariants.coefficientRepresentation k G N g (restrictMap k G p m))
  simp only [GroupCoinvariants.coefficientRepresentation, Representation.ofModule,
    MonoidAlgebra.lift_symm_apply, RestrictScalars.lsmul_apply_apply, AddEquiv.apply_symm_apply]
  exact p.map_smul (MonoidAlgebra.single g 1) (RestrictScalars.addEquiv k k[G] M m)

def coinvariantAction {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]}
    (p : CoefficientMap k G M N) :
    GroupCoinvariants.Coinvariants k G M →ₗ[k] GroupCoinvariants.Coinvariants k G N :=
  Representation.Coinvariants.map _ _ {
    toLinearMap := restrictMap k G p
    isIntertwining' g := by
      ext m
      exact restrictMap_action k G p g m }

def coefficientAction {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]}
    (p : CoefficientMap k G M N) : CoefficientAction k G p where
  chain := tensorAction k G p
  tensor := fun _ _ _ _ => rfl
  homology P := (tensorAction k G p P).homologyMap
  on_class P := (tensorAction k G p P).homologyMap_induces
  coinvariants := coinvariantAction k G p
  on_quotient := fun _ => rfl

theorem actions : ActionsType.{u,v,a,b} :=
  fun k G _ _ _ _ p => ⟨coefficientAction k G p⟩

section Composition
variable {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]} {Q : ModuleCat.{c} k[G]}

@[simp] lemma tensorAction_tmul (p : CoefficientMap k G M N) (P : Model)
    (n : ℕ) (z : (P.rightComplex k G).X n) (m : M) :
    (tensorAction k G p P).app n (tmul k[G] z m) = tmul k[G] z (p m) := rfl

lemma tensorAction_comp (p : CoefficientMap k G M N) (q : CoefficientMap k G N Q)
    (P : Model) (n : ℕ) :
    ((tensorAction k G q P).app n).comp ((tensorAction k G p P).app n) =
      (tensorAction k G (q.comp p) P).app n := by
  apply tensor_hom_ext
  intro z m
  rfl

lemma tensorAction_id (P : Model) (n : ℕ) :
    (tensorAction k G (LinearMap.id : CoefficientMap k G M M) P).app n = LinearMap.id := by
  apply tensor_hom_ext
  intro z m
  rfl

lemma tensorAction_homology_comp (p : CoefficientMap k G M N) (q : CoefficientMap k G N Q)
    (P : Model) (n : ℕ) :
    ((tensorAction k G q P).homologyMap n).comp ((tensorAction k G p P).homologyMap n) =
      (tensorAction k G (q.comp p) P).homologyMap n := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := (cycleBoundaries (P.complex k G M) n).mkQ_surjective z
  exact congrArg (homologyClass _ n)
    (Subtype.ext (LinearMap.congr_fun (tensorAction_comp k G p q P n) z.val))

lemma tensorAction_homology_id (P : Model) (n : ℕ) :
    (tensorAction k G (LinearMap.id : CoefficientMap k G M M) P).homologyMap n = LinearMap.id := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := (cycleBoundaries (P.complex k G M) n).mkQ_surjective z
  exact congrArg (homologyClass _ n)
    (Subtype.ext (LinearMap.congr_fun (tensorAction_id k G (M := M) P n) z.val))

@[simp] lemma coinvariantAction_mk (p : CoefficientMap k G M N)
    (m : RestrictScalars k k[G] M) :
    coinvariantAction k G p (GroupCoinvariants.quotientMap k G M m) =
      GroupCoinvariants.quotientMap k G N (restrictMap k G p m) := rfl

lemma coinvariantAction_comp (p : CoefficientMap k G M N) (q : CoefficientMap k G N Q) :
    (coinvariantAction k G q).comp (coinvariantAction k G p) =
      coinvariantAction k G (q.comp p) := by
  apply Representation.Coinvariants.hom_ext
  apply LinearMap.ext
  intro m
  rfl

lemma coinvariantAction_id :
    coinvariantAction k G (LinearMap.id : CoefficientMap k G M M) = LinearMap.id := by
  apply Representation.Coinvariants.hom_ext
  apply LinearMap.ext
  intro m
  rfl

end Composition

def tensorLift (P : Model) (M : ModuleCat.{a} k[G]) (n : ℕ) :
    (P.complex k G M).X n ≃ₗ[ℤ] (P.complex k G (Lift.{u,v,a,s} k G M)).X n :=
  LinearEquiv.ofLinearMap ((tensorAction k G (up.{u,v,a,s} k G M) P).app n)
    ((tensorAction k G (down.{u,v,a,s} k G M) P).app n)
    (by rw [tensorAction_comp]; exact tensorAction_id k G P n)
    (by rw [tensorAction_comp]; exact tensorAction_id k G P n)

def homologyLift (P : Model) (M : ModuleCat.{a} k[G]) (n : ℕ) :
    P.homology k G M n ≃ₗ[ℤ] P.homology k G (Lift.{u,v,a,s} k G M) n :=
  LinearEquiv.ofLinearMap ((tensorAction k G (up.{u,v,a,s} k G M) P).homologyMap n)
    ((tensorAction k G (down.{u,v,a,s} k G M) P).homologyMap n)
    (by rw [tensorAction_homology_comp]; exact tensorAction_homology_id k G P n)
    (by rw [tensorAction_homology_comp]; exact tensorAction_homology_id k G P n)

def coinvariantLift (M : ModuleCat.{a} k[G]) :
    GroupCoinvariants.Coinvariants k G M ≃ₗ[k]
      GroupCoinvariants.Coinvariants k G (Lift.{u,v,a,s} k G M) :=
  LinearEquiv.ofLinearMap (coinvariantAction k G (up.{u,v,a,s} k G M))
    (coinvariantAction k G (down.{u,v,a,s} k G M))
    (by rw [coinvariantAction_comp]; exact coinvariantAction_id k G)
    (by rw [coinvariantAction_comp]; exact coinvariantAction_id k G)


theorem liftComparisons : LiftComparisonType.{u,v,a,s} :=
  fun k G _ _ M => ⟨{
    action := coefficientAction k G (up.{u,v,a,s} k G M)
    terms := fun P n => (tensorLift.{u,v,a,s} k G P M n).bijective
    homology := fun P n => (homologyLift.{u,v,a,s} k G P M n).bijective
    coinvariants := (coinvariantLift.{u,v,a,s} k G M).bijective }⟩

def barCoordinates : BarCoordinates.{u,v,a} k G where
  coordinates := RightBar.tensorIso k G
  symbol := RightBar.tensorIso_symbol k G
  differential M n g m := by
    rw [tensor_differential, ← RightBar.chainBoundary_tensorIso,
      LinearEquiv.apply_symm_apply]
    exact RightBar.chainBoundary_single k G M n g m

lemma barAction_coordinates {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]}
    (p : CoefficientMap k G M N) (n : ℕ) (z : RightBar.TensorChains k G M n) :
    RightBar.tensorIso k G N n ((tensorAction k G p .bar).app n z) =
      symbolMap k G p n (RightBar.tensorIso k G M n z) := by
  obtain ⟨x, rfl⟩ := (RightBar.tensorIso k G M n).symm.surjective z
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single g m =>
    rw [LinearEquiv.apply_symm_apply, RightBar.tensorIso_symm_single, tensorAction_tmul]
    rw [show p (RestrictScalars.addEquiv k k[G] M m) =
      RestrictScalars.addEquiv k k[G] N (restrictMap k G p m) from rfl,
      RightBar.tensorIso_symbol]
    simp [symbolMap, Finsupp.mapRange.linearMap]

theorem barActions : BarActionType.{u,v,a,b} :=
  fun k G _ _ => ⟨barCoordinates k G, barCoordinates k G, coefficientAction k G,
    barAction_coordinates k G⟩

section LiftedSequences
variable {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]} {Q : ModuleCat.{c} k[G]}
  {i : CoefficientMap k G M N} {p : CoefficientMap k G N Q}

theorem liftedShortExact (h : ShortExact k G i p) :
    (liftedSequence.{u,v,a,b,c,s} k G h).ShortExact := by
  let S := liftedSequence.{u,v,a,b,c,s} k G h
  have hi : Function.Injective S.f := fun x y hxy =>
    ULift.ext (h.injective (congrArg ULift.down hxy))
  have hp : Function.Surjective S.g := by
    intro y
    obtain ⟨x, hx⟩ := h.surjective y.down
    exact ⟨ULift.up x, congrArg ULift.up hx⟩
  have hE : Function.Exact S.f S.g := by
    intro y
    constructor
    · intro hy
      obtain ⟨x, hx⟩ := (h.exact y.down).mp (congrArg ULift.down hy)
      exact ⟨ULift.up x, ULift.ext hx⟩
    · rintro ⟨x, rfl⟩
      exact congrArg ULift.up (h.exact.apply_apply_eq_zero x.down)
  let : Mono S.f := (ModuleCat.mono_iff_injective S.f).2 hi
  let : Epi S.g := (ModuleCat.epi_iff_surjective S.g).2 hp
  exact ⟨(CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).2 hE⟩

theorem liftedSequences : LiftedSequenceType.{u,v,a,b,c,s} :=
  fun k G _ _ _ _ _ _ _ h => liftedShortExact k G h

end LiftedSequences


lemma tensorAction_homogeneous {M N : ModuleCat.{a} k[G]} (p : M ⟶ N) (P : Model) (n : ℕ) :
    (tensorAction k G p.hom P).app n = ((tensorSecondMap (P.rightComplex k G) p.hom).f n).hom :=
  rfl

lemma tensorAction_homology_homogeneous {M N : ModuleCat.{a} k[G]} (p : M ⟶ N)
    (P : Model) (n : ℕ) : (tensorAction k G p.hom P).homologyMap n =
      homologyMap (tensorSecondMap (P.rightComplex k G) p.hom) n := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := (cycleBoundaries (P.complex k G M) n).mkQ_surjective z
  rfl

lemma coinvariantAction_homogeneous {M N : ModuleCat.{a} k[G]} (p : M ⟶ N) :
    coinvariantAction k G p.hom = (GroupCoinvariants.coinvariantsMap k G p).hom := by
  apply Representation.Coinvariants.hom_ext
  apply LinearMap.ext
  intro m
  rfl

section LiftSquares
variable {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]}
  (p : CoefficientMap k G M N)

lemma lift_conjugation :
    (liftedMap.{u,v,a,b,s} k G p).comp (up.{u,v,a,s} k G M) =
      (up.{u,v,b,s} k G N).comp p := rfl

lemma tensorLift_natural (P : Model) (n : ℕ) :
    ((tensorAction k G (liftedMap.{u,v,a,b,s} k G p) P).app n).comp
      (tensorLift.{u,v,a,s} k G P M n).toLinearMap =
    (tensorLift.{u,v,b,s} k G P N n).toLinearMap.comp ((tensorAction k G p P).app n) := by
  change ((tensorAction k G _ P).app n).comp ((tensorAction k G _ P).app n) =
    ((tensorAction k G _ P).app n).comp ((tensorAction k G _ P).app n)
  rw [tensorAction_comp, tensorAction_comp]
  rfl

lemma homologyLift_natural (P : Model) (n : ℕ) :
    ((tensorAction k G (liftedMap.{u,v,a,b,s} k G p) P).homologyMap n).comp
      (homologyLift.{u,v,a,s} k G P M n).toLinearMap =
    (homologyLift.{u,v,b,s} k G P N n).toLinearMap.comp ((tensorAction k G p P).homologyMap n) := by
  change ((tensorAction k G _ P).homologyMap n).comp ((tensorAction k G _ P).homologyMap n) =
    ((tensorAction k G _ P).homologyMap n).comp ((tensorAction k G _ P).homologyMap n)
  rw [tensorAction_homology_comp, tensorAction_homology_comp]
  rfl

lemma coinvariantLift_natural :
    (coinvariantAction k G (liftedMap.{u,v,a,b,s} k G p)).comp
      (coinvariantLift.{u,v,a,s} k G M).toLinearMap =
    (coinvariantLift.{u,v,b,s} k G N).toLinearMap.comp (coinvariantAction k G p) := by
  change (coinvariantAction k G _).comp (coinvariantAction k G _) =
    (coinvariantAction k G _).comp (coinvariantAction k G _)
  rw [coinvariantAction_comp, coinvariantAction_comp]
  rfl

end LiftSquares

section Transfer
variable {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]} {Q : ModuleCat.{c} k[G]}
  {i : CoefficientMap k G M N} {p : CoefficientMap k G N Q}

private lemma ambientTermwiseExact (h : ShortExact k G i p) (P : Model) :
    let S := liftedSequence.{u,v,a,b,c,s} k G h
    DegreewiseExact (tensorSecondMap (P.rightComplex k G) S.f.hom)
      (tensorSecondMap (P.rightComplex k G) S.g.hom) := by
  cases P
  · exact tor_degreewise_exact k G _ (liftedShortExact k G h)
  · exact coefficient_degreewise_exact k G _ (liftedShortExact k G h)

theorem termwiseExact (h : ShortExact k G i p) (P : Model) :
    TermwiseExact (tensorAction k G i P) (tensorAction k G p P) := by
  let S := liftedSequence.{u,v,a,b,c,0} k G h
  intro n
  let e₁ := tensorLift.{u,v,a,max a b c} k G P M n
  let e₂ := tensorLift.{u,v,b,max a b c} k G P N n
  let e₃ := tensorLift.{u,v,c,max a b c} k G P Q n
  have h₁ := tensorLift_natural.{u,v,a,b,max a b c} k G i P n
  have h₂ := tensorLift_natural.{u,v,b,c,max a b c} k G p P n
  change ((tensorSecondMap (P.rightComplex k G) S.f.hom).f n).hom.comp
    e₁.toLinearMap = e₂.toLinearMap.comp ((tensorAction k G i P).app n) at h₁
  change ((tensorSecondMap (P.rightComplex k G) S.g.hom).f n).hom.comp
    e₂.toLinearMap = e₃.toLinearMap.comp ((tensorAction k G p P).app n) at h₂
  obtain ⟨hi, hE, hp⟩ := ambientTermwiseExact.{u,v,a,b,c,0} k G h P n
  refine ⟨?_, (LinearMap.exact_iff_of_surjective_of_bijective_of_injective _ _ _ _ _ _ _
    h₁ h₂ e₁.surjective e₂.bijective e₃.injective).mpr hE, ?_⟩
  · intro x y he
    apply e₁.injective
    apply hi
    exact (LinearMap.congr_fun h₁ x).trans ((congrArg e₂ he).trans (LinearMap.congr_fun h₁ y).symm)
  · intro z
    obtain ⟨y, hy⟩ := hp (e₃ z)
    obtain ⟨x, hx⟩ := e₂.surjective y
    refine ⟨x, e₃.injective ?_⟩
    exact (LinearMap.congr_fun h₂ x).symm.trans ((congrArg _ hx).trans hy)

private def ambientBoundary (h : ShortExact k G i p) (P : Model) (n : ℕ) :
    let S := liftedSequence.{u,v,a,b,c,s} k G h
    P.homology k G S.X₃ (n+1) →ₗ[ℤ] P.homology k G S.X₁ n :=
  match P with
  | .tor => coefficientBoundary k G _ (liftedShortExact k G h) n
  | .bar => barBoundary k G _ (liftedShortExact k G h) n

private theorem ambientBoundary_spec (h : ShortExact k G i p) (P : Model) (n : ℕ) :
    let S := liftedSequence.{u,v,a,b,c,s} k G h
    let F := tensorSecondMap (P.rightComplex k G) S.f.hom
    let H := tensorSecondMap (P.rightComplex k G) S.g.hom
    Connecting F H (n+1) n (ambientBoundary.{u,v,a,b,c,s} k G h P n) ∧
      SequenceExact F H (n+1) n (ambientBoundary.{u,v,a,b,c,s} k G h P n) := by
  cases P
  · exact coefficientBoundary_spec k G _ (liftedShortExact k G h) n
  · exact barBoundary_spec k G _ (liftedShortExact k G h) n

/-- The connecting map on original quotients is transported from a common
category by tensoring the three carrier isomorphisms. -/
def boundaryViaLift (h : ShortExact k G i p) (P : Model) (n : ℕ) :
    P.homology k G Q (n+1) →ₗ[ℤ] P.homology k G M n :=
  (homologyLift.{u,v,a,max a b c s} k G P M n).symm.toLinearMap.comp
    ((ambientBoundary.{u,v,a,b,c,s} k G h P n).comp
      (homologyLift.{u,v,c,max a b c s} k G P Q (n+1)).toLinearMap)

@[simp] lemma boundaryViaLift_comm (h : ShortExact k G i p) (P : Model) (n : ℕ)
    (z : P.homology k G Q (n+1)) :
    homologyLift.{u,v,a,max a b c s} k G P M n
      (boundaryViaLift.{u,v,a,b,c,s} k G h P n z) =
        ambientBoundary.{u,v,a,b,c,s} k G h P n
          (homologyLift.{u,v,c,max a b c s} k G P Q (n+1) z) := by
  unfold boundaryViaLift
  exact LinearEquiv.apply_symm_apply _ _

abbrev boundary (h : ShortExact k G i p) (P : Model) (n : ℕ) :=
  boundaryViaLift.{u,v,a,b,c,0} k G h P n

theorem boundaryViaLift_positive (h : ShortExact k G i p) (P : Model) (n : ℕ) :
    PositiveBoundary (tensorAction k G i P) (tensorAction k G p P) n
      (boundaryViaLift.{u,v,a,b,c,s} k G h P n) := by
  intro z y x hz hx
  let α := tensorAction k G (up.{u,v,a,max a b c s} k G M) P
  let β := tensorAction k G (up.{u,v,b,max a b c s} k G N) P
  let γ := tensorAction k G (up.{u,v,c,max a b c s} k G Q) P
  apply (homologyLift.{u,v,a,max a b c s} k G P M n).injective
  rw [boundaryViaLift_comm]
  refine (ambientBoundary_spec.{u,v,a,b,c,s} k G h P n).1
    (γ.cyclesMap (n+1) z) (β.app (n+1) y) (α.cyclesMap n x) ?_ ?_
  · have H := LinearMap.congr_fun (tensorLift_natural.{u,v,b,c,max a b c s} k G p P (n+1)) y
    exact H.trans (congrArg (γ.app (n+1)) hz)
  · have H := LinearMap.congr_fun (tensorLift_natural.{u,v,a,b,max a b c s} k G i P n) x.val
    exact H.trans ((congrArg (β.app n) hx).trans (β.comm_apply (n+1) n y).symm)

theorem boundary_exact (h : ShortExact k G i p) (P : Model) (n : ℕ) :
    Function.Exact ((tensorAction k G i P).homologyMap (n+1))
      ((tensorAction k G p P).homologyMap (n+1)) ∧
    Function.Exact ((tensorAction k G p P).homologyMap (n+1)) (boundary k G h P n) ∧
    Function.Exact (boundary k G h P n) ((tensorAction k G i P).homologyMap n) := by
  let S := liftedSequence.{u,v,a,b,c,0} k G h
  let α := homologyLift.{u,v,a,max a b c} k G P M
  let β := homologyLift.{u,v,b,max a b c} k G P N
  let γ := homologyLift.{u,v,c,max a b c} k G P Q
  have hi (j : ℕ) :
      (homologyMap (tensorSecondMap (P.rightComplex k G) S.f.hom) j).comp (α j).toLinearMap =
        (β j).toLinearMap.comp ((tensorAction k G i P).homologyMap j) := by
    rw [← tensorAction_homology_homogeneous]
    exact homologyLift_natural.{u,v,a,b,max a b c} k G i P j
  have hp (j : ℕ) :
      (homologyMap (tensorSecondMap (P.rightComplex k G) S.g.hom) j).comp (β j).toLinearMap =
        (γ j).toLinearMap.comp ((tensorAction k G p P).homologyMap j) := by
    rw [← tensorAction_homology_homogeneous]
    exact homologyLift_natural.{u,v,b,c,max a b c} k G p P j
  have hd :
      (ambientBoundary.{u,v,a,b,c,0} k G h P n).comp (γ (n+1)).toLinearMap =
        (α n).toLinearMap.comp (boundary k G h P n) :=
    LinearMap.ext fun z => (boundaryViaLift_comm.{u,v,a,b,c,0} k G h P n z).symm
  obtain ⟨h₁, h₂, h₃⟩ := (ambientBoundary_spec.{u,v,a,b,c,0} k G h P n).2
  refine ⟨?_, ?_, ?_⟩
  · exact (LinearMap.exact_iff_of_surjective_of_bijective_of_injective _ _ _ _ _ _ _
      (hi _) (hp _) (α _).surjective (β _).bijective (γ _).injective).mpr h₁
  · exact (LinearMap.exact_iff_of_surjective_of_bijective_of_injective _ _ _ _ _ _ _
      (hp _) hd (β _).surjective (γ _).bijective (α _).injective).mpr h₂
  · exact (LinearMap.exact_iff_of_surjective_of_bijective_of_injective _ _ _ _ _ _ _
      hd (hi _) (γ _).surjective (α _).bijective (β _).injective).mpr h₃

theorem coinvariant_exact (h : ShortExact k G i p) :
    Function.Exact (coinvariantAction k G i) (coinvariantAction k G p) ∧
      Function.Surjective (coinvariantAction k G p) := by
  let S := liftedSequence.{u,v,a,b,c,0} k G h
  have hS := liftedShortExact.{u,v,a,b,c,0} k G h
  let e₁ := coinvariantLift.{u,v,a,max a b c} k G M
  let e₂ := coinvariantLift.{u,v,b,max a b c} k G N
  let e₃ := coinvariantLift.{u,v,c,max a b c} k G Q
  have hi :
      (GroupCoinvariants.coinvariantsMap k G S.f).hom.comp e₁.toLinearMap =
        e₂.toLinearMap.comp (coinvariantAction k G i) := by
    rw [← coinvariantAction_homogeneous]
    exact coinvariantLift_natural.{u,v,a,b,max a b c} k G i
  have hp :
      (GroupCoinvariants.coinvariantsMap k G S.g).hom.comp e₂.toLinearMap =
        e₃.toLinearMap.comp (coinvariantAction k G p) := by
    rw [← coinvariantAction_homogeneous]
    exact coinvariantLift_natural.{u,v,b,c,max a b c} k G p
  obtain ⟨hE, hP⟩ := GroupCoinvariants.coinvariants_rightExact S.f S.g
    ((CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact)
    hS.moduleCat_surjective_g
  refine ⟨(LinearMap.exact_iff_of_surjective_of_bijective_of_injective _ _ _ _ _ _ _
      hi hp e₁.surjective e₂.bijective e₃.injective).mpr hE, ?_⟩
  intro z
  obtain ⟨y, hy⟩ := hP (e₃ z)
  obtain ⟨x, hx⟩ := e₂.surjective y
  refine ⟨x, e₃.injective ?_⟩
  exact (LinearMap.congr_fun hp x).symm.trans ((congrArg _ hx).trans hy)

end Transfer

section PositiveBoundary
variable {R : Type*} [Ring R]
  {A : ChainComplex (ModuleCat.{a} R) ℕ}
  {B : ChainComplex (ModuleCat.{b} R) ℕ} {C : ChainComplex (ModuleCat.{c} R) ℕ}
  {i : LinearChainMap A B} {p : LinearChainMap B C}

private lemma positive_lifts (hex : TermwiseExact i p) (n : ℕ) (z : cycles C (n+1)) :
    ∃ (y : B.X (n+1)) (x : cycles A n),
      p.app (n+1) y = z.val ∧ i.app n x.val = (B.d (n+1) n).hom y := by
  obtain ⟨y, hy⟩ := (hex (n+1)).2.2 z.val
  have hz : (C.d (n+1) n).hom z.val = 0 :=
    (P103.Ch10.HomologySequence.cycle_iff C (show (ComplexShape.down ℕ).Rel (n+1) n by rfl) _).mp z.property
  have hpy : p.app n ((B.d (n+1) n).hom y) = 0 := by
    rw [← p.comm_apply (n+1) n, hy, hz]
  obtain ⟨x, hx⟩ := ((hex n).2.1 _).mp hpy
  refine ⟨y, ⟨x, ?_⟩, hy, hx⟩
  let j := (ComplexShape.down ℕ).next n
  change (A.d n j).hom x = 0
  apply (hex j).1
  rw [map_zero, ← i.comm_apply n j, hx]
  exact P103.Ch10.HomologySequence.square_zero B (n+1) n j y

private theorem positive_unique (hex : TermwiseExact i p) {n : ℕ}
    {δ ε : Homology C (n+1) →ₗ[R] Homology A n}
    (hδ : PositiveBoundary i p n δ) (hε : PositiveBoundary i p n ε) : δ = ε := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := (cycleBoundaries C (n+1)).mkQ_surjective z
  obtain ⟨y, x, hy, hx⟩ := positive_lifts hex n z
  exact (hδ z y x hy hx).trans (hε z y x hy hx).symm

theorem positive_naturality
    {A' : ChainComplex (ModuleCat.{d} R) ℕ}
    {B' : ChainComplex (ModuleCat.{e} R) ℕ}
    {C' : ChainComplex (ModuleCat.{f} R) ℕ}
    {i' : LinearChainMap A' B'} {p' : LinearChainMap B' C'}
    (α : LinearChainMap A A') (β : LinearChainMap B B') (γ : LinearChainMap C C')
    (hi : ∀ j, (i'.app j).comp (α.app j) = (β.app j).comp (i.app j))
    (hp : ∀ j, (p'.app j).comp (β.app j) = (γ.app j).comp (p.app j))
    (hex : TermwiseExact i p) {n : ℕ}
    {δ : Homology C (n+1) →ₗ[R] Homology A n}
    {ε : Homology C' (n+1) →ₗ[R] Homology A' n}
    (hδ : PositiveBoundary i p n δ) (hε : PositiveBoundary i' p' n ε) :
    (α.homologyMap n).comp δ = ε.comp (γ.homologyMap (n+1)) := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := (cycleBoundaries C (n+1)).mkQ_surjective z
  obtain ⟨y, x, hy, hx⟩ := positive_lifts hex n z
  change α.homologyMap n (δ (homologyClass C (n+1) z)) =
    ε (homologyClass C' (n+1) (γ.cyclesMap (n+1) z))
  rw [hδ z y x hy hx]
  symm
  refine hε (γ.cyclesMap (n+1) z) (β.app (n+1) y) (α.cyclesMap n x) ?_ ?_
  · exact (LinearMap.congr_fun (hp _) y).trans (congrArg (γ.app _) hy)
  · exact (LinearMap.congr_fun (hi _) x.val).trans
      ((congrArg (β.app _) hx).trans (β.comm_apply _ _ _).symm)

end PositiveBoundary

section Uniqueness
variable {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]}
  {p : CoefficientMap k G M N} (A : CoefficientAction k G p)

lemma chain_eq_tensorAction (P : Model) : A.chain P = tensorAction k G p P := by
  apply LinearChainMap.eq_of_app_eq
  funext n
  apply tensor_hom_ext
  exact A.tensor P n

lemma homology_eq_tensorAction (P : Model) (n : ℕ) :
    A.homology P n = (tensorAction k G p P).homologyMap n := by
  have H := A.on_class P
  rw [chain_eq_tensorAction k G A] at H
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := (cycleBoundaries (P.complex k G M) n).mkQ_surjective z
  obtain ⟨y, hy, hclass⟩ := H n z
  exact hclass.trans (congrArg (homologyClass _ n) (Subtype.ext hy))

lemma coinvariants_eq_coinvariantAction :
    A.coinvariants = coinvariantAction k G p := by
  apply Representation.Coinvariants.hom_ext
  exact LinearMap.ext A.on_quotient

end Uniqueness

theorem liftNaturality : LiftNaturalityType.{u,v,a,b,s} := by
  intro k G _ _ M N p A B U V
  simp only [chain_eq_tensorAction, homology_eq_tensorAction, coinvariants_eq_coinvariantAction]
  exact ⟨fun P n => ⟨tensorLift_natural k G p P n, homologyLift_natural k G p P n⟩,
    coinvariantLift_natural k G p⟩

section Sequences
variable {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]} {Q : ModuleCat.{c} k[G]}
  {i : CoefficientMap k G M N} {p : CoefficientMap k G N Q}

def coefficientSequence (h : ShortExact k G i p) : CoefficientSequence k G i p where
  first := coefficientAction k G i
  second := coefficientAction k G p
  boundary := boundary k G h
  chains_exact := termwiseExact k G h
  positive := boundaryViaLift_positive.{u,v,a,b,c,0} k G h
  exact := boundary_exact k G h
  zero_exact := (coinvariant_exact k G h).1
  zero_surjective := (coinvariant_exact k G h).2

theorem coefficientSequences : CoefficientSequenceType.{u,v,a,b,c} :=
  fun k G _ _ _ _ _ _ _ h => ⟨coefficientSequence k G h⟩

end Sequences

theorem sequenceNaturality : SequenceNaturalityType.{u,v,a,b,c,d,e,f} := by
  intro k G _ _ M N Q M' N' Q' i p i' p' α β γ hi hp S T A B C
  simp only [homology_eq_tensorAction, coinvariants_eq_coinvariantAction]
  refine ⟨fun P n => ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [tensorAction_homology_comp, tensorAction_homology_comp, hi]
  · rw [tensorAction_homology_comp, tensorAction_homology_comp, hp]
  · have hS := S.positive P n
    have hT := T.positive P n
    have hex := S.chains_exact P
    simp only [chain_eq_tensorAction] at hS hT hex
    apply positive_naturality (tensorAction k G α P) (tensorAction k G β P)
      (tensorAction k G γ P) _ _ hex hS hT
    · intro j
      rw [tensorAction_comp, tensorAction_comp, hi]
    · intro j
      rw [tensorAction_comp, tensorAction_comp, hp]
  · rw [coinvariantAction_comp, coinvariantAction_comp, hi]
  · rw [coinvariantAction_comp, coinvariantAction_comp, hp]

theorem barBoundaryOnSymbols : BarBoundaryOnSymbolsType.{u,v,a,b,c} := by
  intro k G _ _
  refine ⟨barCoordinates k G, barCoordinates k G, barCoordinates k G, ?_⟩
  intro M N Q i p S n z y x hy hx
  have hS := S.positive .bar n
  simp only [chain_eq_tensorAction] at hS
  refine hS z ((RightBar.tensorIso k G N (n+1)).symm y) x ?_ ?_
  · apply (RightBar.tensorIso k G Q (n+1)).injective
    rw [barAction_coordinates, LinearEquiv.apply_symm_apply]
    exact hy
  · apply (RightBar.tensorIso k G N n).injective
    rw [barAction_coordinates]
    exact hx


def normalizedComparisons : NormalizedComparisons.{u,v,a} k G where
  bar := torBarIso k G
  zero := zeroIso k G
  bar_normalized := torBarCoordinates k G
  zero_normalized := zeroCoordinates k G

section Normalization
variable {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]}
  (p : CoefficientMap k G M N)

theorem torBar_natural (n : ℕ) (z : GroupCoinvariants.GroupHomology k G M n) :
    torBarIso k G N n ((tensorAction k G p .tor).homologyMap n z) =
      (tensorAction k G p .bar).homologyMap n (torBarIso k G M n z) := by
  change (torBarIso k G N n).toLinearMap ((tensorAction k G p .tor).homologyMap n z) =
    (tensorAction k G p .bar).homologyMap n ((torBarIso k G M n).toLinearMap z)
  rw [torBarIso_eq_homologyMap, torBarIso_eq_homologyMap]
  let compareM := LinearChainMap.ofHom (tensorFirstMap (barComparisonLift k G) M)
  let compareN := LinearChainMap.ofHom (tensorFirstMap (barComparisonLift k G) N)
  have square (j : ℕ) :
      (compareN.app j).comp ((tensorAction k G p .tor).app j) =
        ((tensorAction k G p .bar).app j).comp (compareM.app j) := by
    apply tensor_hom_ext
    intro y m
    rfl
  exact LinearMap.congr_fun (LinearChainMap.homologyMap_square
    (tensorAction k G p .tor) (tensorAction k G p .bar) compareM compareN square n) z

theorem torZero_natural (z : GroupCoinvariants.GroupHomology k G M 0) :
    torZero k G N ((tensorAction k G p .tor).homologyMap 0 z) =
      tensorMap (LinearMap.id : trivial k G →ₗ[k[G]ᵐᵒᵖ] trivial k G) p
        (torZero k G M z) := by
  let P := (canonicalResolution k G).val
  obtain ⟨z, rfl⟩ := (cycleBoundaries (tensorComplex P.complex M) 0).mkQ_surjective z
  change P103.Ch11.ExtTorDefinitions.torZero P N
      (homologyClass _ 0 ((tensorAction k G p .tor).cyclesMap 0 z)) =
    tensorMap _ p (P103.Ch11.ExtTorDefinitions.torZero P M (homologyClass _ 0 z))
  rw [P103.Ch11.ExtTorDefinitions.torZero_class, P103.Ch11.ExtTorDefinitions.torZero_class]
  have h : (tensorMap P.ε (LinearMap.id : N →ₗ[k[G]] N)).comp
      ((tensorAction k G p .tor).app 0) =
      (tensorMap LinearMap.id p).comp (tensorMap P.ε (LinearMap.id : M →ₗ[k[G]] M)) := by
    apply tensor_hom_ext
    intro x m
    rfl
  exact LinearMap.congr_fun h z.val

theorem zeroIso_natural_original (z : GroupCoinvariants.GroupHomology k G M 0) :
    zeroIso k G N ((tensorAction k G p .tor).homologyMap 0 z) =
      coinvariantAction k G p (zeroIso k G M z) := by
  change (GroupCoinvariants.coinvariantTensorIso N).symm
      (torZero k G N ((tensorAction k G p .tor).homologyMap 0 z)) =
    coinvariantAction k G p ((GroupCoinvariants.coinvariantTensorIso M).symm (torZero k G M z))
  rw [torZero_natural]
  let qM := (GroupCoinvariants.coinvariantTensorIso M).symm.toAddEquiv.toAddMonoidHom.toIntLinearMap
  let qN := (GroupCoinvariants.coinvariantTensorIso N).symm.toAddEquiv.toAddMonoidHom.toIntLinearMap
  have h : qN.comp (tensorMap (LinearMap.id : trivial k G →ₗ[k[G]ᵐᵒᵖ] trivial k G) p) =
      (coinvariantAction k G p).toAddMonoidHom.toIntLinearMap.comp qM := by
    apply tensor_hom_ext
    intro x m
    change (GroupCoinvariants.coinvariantTensorIso N).symm (tmul k[G] x (p m)) =
      coinvariantAction k G p ((GroupCoinvariants.coinvariantTensorIso M).symm (tmul k[G] x m))
    simp only [GroupCoinvariants.coinvariantTensorIso_symm_tmul, map_smul, coinvariantAction_mk]
    rfl
  exact LinearMap.congr_fun h (torZero k G M z)

end Normalization

theorem comparisonNaturality : ComparisonNaturalityType.{u,v,a,b} := by
  intro k G _ _
  refine ⟨normalizedComparisons k G, normalizedComparisons k G, ?_⟩
  intro M N p A
  simp only [homology_eq_tensorAction, coinvariants_eq_coinvariantAction]
  exact ⟨torBar_natural k G p, zeroIso_natural_original k G p⟩

section Boundaries
variable {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]} {Q : ModuleCat.{c} k[G]}
  {i : CoefficientMap k G M N} {p : CoefficientMap k G N Q}

theorem boundary_compare (h : ShortExact k G i p) (n : ℕ)
    (z : GroupCoinvariants.GroupHomology k G Q (n+1)) :
    torBarIso k G M n (boundary k G h .tor n z) =
      boundary k G h .bar n (torBarIso k G Q (n+1) z) := by
  apply (homologyLift.{u,v,a,max a b c} k G .bar M n).injective
  change (tensorAction k G (up.{u,v,a,max a b c} k G M) .bar).homologyMap n
      (torBarIso k G M n (boundary k G h .tor n z)) =
    homologyLift.{u,v,a,max a b c} k G .bar M n
      (boundary k G h .bar n (torBarIso k G Q (n+1) z))
  rw [← torBar_natural]
  change torBarIso k G _ n (homologyLift.{u,v,a,max a b c} k G .tor M n
      (boundary k G h .tor n z)) = _
  rw [boundaryViaLift_comm, boundaryViaLift_comm]
  change torBarIso k G _ n (coefficientBoundary k G _ (liftedShortExact.{u,v,a,b,c,0} k G h) n
      (homologyLift.{u,v,c,max a b c} k G .tor Q (n+1) z)) =
    barBoundary k G _ (liftedShortExact.{u,v,a,b,c,0} k G h) n
      ((tensorAction k G (up.{u,v,c,max a b c} k G Q) .bar).homologyMap (n+1)
        (torBarIso k G Q (n+1) z))
  rw [← torBar_natural]
  exact torBarIso_boundary k G _ (liftedShortExact.{u,v,a,b,c,0} k G h) n _

theorem sequenceBoundary_viaLift (h : ShortExact k G i p) (S : CoefficientSequence k G i p)
    (P : Model) (n : ℕ) :
    S.boundary P n = boundaryViaLift.{u,v,a,b,c,s} k G h P n := by
  have hs := S.positive P n
  simp only [chain_eq_tensorAction] at hs
  exact positive_unique (termwiseExact k G h P) hs
    (boundaryViaLift_positive.{u,v,a,b,c,s} k G h P n)

theorem sequenceBoundary_eq (h : ShortExact k G i p) (S : CoefficientSequence k G i p)
    (P : Model) (n : ℕ) :
    S.boundary P n = boundary k G h P n :=
  sequenceBoundary_viaLift k G h S P n

theorem sequenceComparison : SequenceComparisonType.{u,v,a,b,c} := by
  intro k G _ _
  refine ⟨normalizedComparisons k G, normalizedComparisons k G, ?_⟩
  intro M N Q i p h S
  refine ⟨?_, ?_⟩
  · intro n z
    simp only [sequenceBoundary_eq k G h S]
    exact boundary_compare k G h n z
  · simp only [sequenceBoundary_eq k G h S, coinvariants_eq_coinvariantAction]
    intro z
    change coinvariantAction k G i (zeroIso k G M z) = 0 ↔ _
    rw [← zeroIso_natural_original]
    rw [map_eq_zero_iff _ (zeroIso k G N).injective]
    exact (boundary_exact k G h .tor 0).2.2 z

end Boundaries
section Derived

open DerivedGroupHomology.Specification
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
universe x y

section

variable [HasDerivedCategory.{x} (ModuleCat.{max u v a b c s} k[G])]
  [HasDerivedCategory.{y} (ModuleCat.{max u v a b c s} k)]
  [(minus (ModuleCat.{max u v a b c s} k[G])).IsTriangulated]
  [(minus (ModuleCat.{max u v a b c s} k)).IsTriangulated]
  (D : ExactLeftData.{(max u v a b c s)+1,max u v a b c s,
    (max u v a b c s)+1,max u v a b c s,x,y} (ambientCoinvariants.{u,v,max a b c s} k G))

set_option maxRecDepth 1800 in
/-- The normalized stalk boundary on the common lift acts by the original Tor
boundary under the prescribed maps on the original tensor classes. -/
theorem derivedBoundary_onTor
    {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]} {Q : ModuleCat.{c} k[G]}
    {i : CoefficientMap k G M N} {p : CoefficientMap k G N Q}
    (h : ShortExact k G i p) (O : CoefficientSequence k G i p) (n : ℕ)
    (z : GroupCoinvariants.GroupHomology k G Q (n+1)) :
    let S := liftedSequence.{u,v,a,b,c,max u v s} k G h
    let hS := liftedShortExact.{u,v,a,b,c,max u v s} k G h
    let E := derivedTorIso.{u,v,max a b c s,x,y} k G D
    homologyLift.{u,v,a,max u v a b c s} k G .tor M n (O.boundary .tor n z) =
      ((E (n+1)).inv.app S.X₃ ≫
        leftBoundary (ambientCoinvariants.{u,v,max a b c s} k G) D hS n ≫ (E n).hom.app S.X₁)
        (homologyLift.{u,v,c,max u v a b c s} k G .tor Q (n+1) z) := by
  let S := liftedSequence.{u,v,a,b,c,max u v s} k G h
  let hS := liftedShortExact.{u,v,a,b,c,max u v s} k G h
  let liftedZ := homologyLift.{u,v,c,max u v a b c s} k G .tor Q (n+1) z
  dsimp only
  rw [sequenceBoundary_viaLift.{u,v,a,b,c,max u v s} k G h O, boundaryViaLift_comm]
  change DerivedGroupHomology.coefficientBoundary k G S hS n liftedZ = _
  have agrees := transportedDerivedBoundary_agrees.{u,v,max a b c s,x,y} k G D S hS n liftedZ
  exact agrees.symm

end

theorem derivedAgreement : DerivedAgreementType.{u,v,a,b,c,s,x,y} := by
  intro k G _ _ _ _ hA hB
  let := hA
  let := hB
  intro F D
  let E := derivedTorIso.{u,v,max a b c s,x,y} k G D
  have hZ := derivedTorIso_zero_counit.{u,v,max a b c s,x,y} k G D
  refine ⟨E, hZ, derivedTorIso_connecting.{u,v,max a b c s,x,y} k G D, ?_⟩
  intro M N Q i p h O U V
  let S := liftedSequence.{u,v,a,b,c,max u v s} k G h
  have hS := liftedShortExact.{u,v,a,b,c,max u v s} k G h
  refine ⟨hS, ?_, ?_⟩
  · intro n z
    simp only [homology_eq_tensorAction]
    exact derivedBoundary_onTor.{u,v,a,b,c,s,x,y} k G D h O n z
  · intro a₀ m
    simp only [homology_eq_tensorAction, coinvariants_eq_coinvariantAction]
    have he :
        (tensorAction k G (up.{u,v,a,max u v a b c s} k G M) .tor).homologyMap 0
            ((torZero k G M).symm (tmul k[G] a₀ m)) =
          (torZero k G S.X₁).symm
            (tmul k[G] a₀ (up.{u,v,a,max u v a b c s} k G M m)) := by
      apply (torZero k G S.X₁).injective
      exact (torZero_natural k G (up.{u,v,a,max u v a b c s} k G M) _).trans (by
        rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
        rfl)
    rw [he, hZ, map_smul, coinvariantAction_mk]
    rfl

end Derived

def barToSymbols (M : ModuleCat.{a} k[G]) :
    LinearChainMap (chains k G M) ((barCoordinates k G).complex M) where
  app n := (RightBar.tensorIso k G M n).toAddEquiv.toAddMonoidHom.toIntLinearMap
  comm i j := LinearMap.ext fun z => by
    change RightBar.tensorIso k G M j (((chains k G M).d i j).hom
      ((RightBar.tensorIso k G M i).symm (RightBar.tensorIso k G M i z))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl

def symbolsToBar (M : ModuleCat.{a} k[G]) :
    LinearChainMap ((barCoordinates k G).complex M) (chains k G M) where
  app n := (RightBar.tensorIso k G M n).symm.toAddEquiv.toAddMonoidHom.toIntLinearMap
  comm i j := LinearMap.ext fun z => by
    change _ = (RightBar.tensorIso k G M j).symm
      (RightBar.tensorIso k G M j (((chains k G M).d i j).hom ((RightBar.tensorIso k G M i).symm z)))
    rw [LinearEquiv.symm_apply_apply]
    rfl

def barSymbolHomologyIso (M : ModuleCat.{a} k[G]) (n : ℕ) :
    barHomology k G M n ≃ₗ[ℤ] Homology ((barCoordinates k G).complex M) n :=
  LinearEquiv.ofLinearMap ((barToSymbols k G M).homologyMap n) ((symbolsToBar k G M).homologyMap n)
    (by
      apply LinearMap.ext
      intro z
      obtain ⟨z, rfl⟩ := (cycleBoundaries ((barCoordinates k G).complex M) n).mkQ_surjective z
      exact congrArg (homologyClass _ n) (Subtype.ext
        ((RightBar.tensorIso k G M n).apply_symm_apply z.val)))
    (by
      apply LinearMap.ext
      intro z
      obtain ⟨z, rfl⟩ := (cycleBoundaries (chains k G M) n).mkQ_surjective z
      exact congrArg (homologyClass _ n) (Subtype.ext
        ((RightBar.tensorIso k G M n).symm_apply_apply z.val)))

/-- The augmentation of the right bar resolution gives the coinvariant quotient
on degree-zero classes of the actual bar sums. -/
def barSymbolZeroIso (M : ModuleCat.{a} k[G]) :
    Homology ((barCoordinates k G).complex M) 0 ≃+ GroupCoinvariants.Coinvariants k G M :=
  (barSymbolHomologyIso k G M 0).symm.toAddEquiv.trans
    ((P103.Ch11.ExtTorDefinitions.torZero (barResolution k G) M).trans
      (GroupCoinvariants.coinvariantTensorIso M).symm.toAddEquiv)

theorem barSymbolZeroIso_class (M : ModuleCat.{a} k[G])
    (z : cycles ((barCoordinates k G).complex M) 0) :
    barSymbolZeroIso k G M (homologyClass _ 0 z) =
      GroupCoinvariants.quotientMap k G M (RightBar.degreeZeroIso k G M z.val) := by
  change (GroupCoinvariants.coinvariantTensorIso M).symm
    (P103.Ch11.ExtTorDefinitions.torZero (barResolution k G) M
      (homologyClass _ 0 ((symbolsToBar k G M).cyclesMap 0 z))) = _
  rw [P103.Ch11.ExtTorDefinitions.torZero_class]
  change (GroupCoinvariants.coinvariantTensorIso M).symm
    (tensorMap (RightBar.rightAugmentation k G) (LinearMap.id : M →ₗ[k[G]] M)
      ((RightBar.tensorIso k G M 0).symm z.val)) = _
  generalize z.val = w
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add y w hy hw => simp only [map_add, hy, hw]
  | single g m =>
    rw [RightBar.tensorIso_symm_single, RightBar.degreeZeroIso_single]
    have hε :
        RightBar.rightAugmentation k G
          ((RightBar.untwist k G _).symm
            (GroupBar.Large.single.{u,v,0} k G (RightBar.barTuple G g) 1)) = 1 :=
      GroupBar.Large.augmentation_single.{u,v,0} k G (RightBar.barTuple G g) 1
    change (GroupCoinvariants.coinvariantTensorIso M).symm (tmul k[G]
        (RightBar.rightAugmentation k G _) (RestrictScalars.addEquiv k k[G] M m)) = _
    rw [hε, GroupCoinvariants.coinvariantTensorIso_symm_tmul]
    simp [GroupCoinvariants.trivialScalar]

theorem barSymbolZeroIso_fromTor (M : ModuleCat.{a} k[G])
    (z : GroupCoinvariants.GroupHomology k G M 0) :
    barSymbolZeroIso k G M (barSymbolHomologyIso k G M 0 (torBarIso k G M 0 z)) =
      zeroIso k G M z := by
  change (GroupCoinvariants.coinvariantTensorIso M).symm
    (P103.Ch11.ExtTorDefinitions.torZero (barResolution k G) M
      ((barSymbolHomologyIso k G M 0).symm (barSymbolHomologyIso k G M 0 (torBarIso k G M 0 z)))) =
    (GroupCoinvariants.coinvariantTensorIso M).symm (torZero k G M z)
  rw [LinearEquiv.symm_apply_apply, torBarAugmentation_zero]

def barSymbolChainMap {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]}
    (p : CoefficientMap k G M N) :
    LinearChainMap ((barCoordinates k G).complex M) ((barCoordinates k G).complex N) where
  app n := (symbolMap k G p n).toAddMonoidHom.toIntLinearMap
  comm i j := LinearMap.ext fun z => by
    let F := tensorAction k G p .bar
    let eM := RightBar.tensorIso k G M
    let eN := RightBar.tensorIso k G N
    have hi := barAction_coordinates k G p i ((eM i).symm z)
    rw [LinearEquiv.apply_symm_apply] at hi
    change eN j (((chains k G N).d i j).hom ((eN i).symm (symbolMap k G p i z))) =
      symbolMap k G p j (eM j (((chains k G M).d i j).hom ((eM i).symm z)))
    rw [← hi, LinearEquiv.symm_apply_apply, F.comm_apply]
    exact barAction_coordinates k G p j _

theorem barSymbolChainMap_comp {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]}
    {Q : ModuleCat.{c} k[G]} (p : CoefficientMap k G M N) (q : CoefficientMap k G N Q) :
    (barSymbolChainMap k G q).comp (barSymbolChainMap k G p) =
      barSymbolChainMap k G (q.comp p) := by
  apply LinearChainMap.eq_of_app_eq
  funext n
  apply LinearMap.ext
  intro z
  change RightBar.C k G M n at z
  apply Finsupp.ext
  intro g
  change symbolMap k G q n (symbolMap k G p n z) g = symbolMap k G (q.comp p) n z g
  simp only [symbolMap, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply]
  change (RestrictScalars.addEquiv k k[G] Q).symm
    (q (RestrictScalars.addEquiv k k[G] N
      ((RestrictScalars.addEquiv k k[G] N).symm
        (p (RestrictScalars.addEquiv k k[G] M (z g)))))) =
    (RestrictScalars.addEquiv k k[G] Q).symm
      (q (p (RestrictScalars.addEquiv k k[G] M (z g))))
  rw [AddEquiv.apply_symm_apply]

theorem barSymbolHomology_natural {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]}
    (p : CoefficientMap k G M N) (n : ℕ) :
    ((barSymbolChainMap k G p).homologyMap n).comp (barSymbolHomologyIso k G M n).toLinearMap =
      (barSymbolHomologyIso k G N n).toLinearMap.comp ((tensorAction k G p .bar).homologyMap n) := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := (cycleBoundaries (chains k G M) n).mkQ_surjective z
  exact congrArg (homologyClass ((barCoordinates k G).complex N) n)
    (Subtype.ext (barAction_coordinates k G p n z.val).symm)

theorem barSymbolZeroIso_natural {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]}
    (p : CoefficientMap k G M N) (z : Homology ((barCoordinates k G).complex M) 0) :
    barSymbolZeroIso k G N ((barSymbolChainMap k G p).homologyMap 0 z) =
      coinvariantAction k G p (barSymbolZeroIso k G M z) := by
  obtain ⟨z, rfl⟩ := ((torBarIso k G M 0).trans (barSymbolHomologyIso k G M 0)).surjective z
  change barSymbolZeroIso k G N
    ((barSymbolChainMap k G p).homologyMap 0 (barSymbolHomologyIso k G M 0 (torBarIso k G M 0 z))) =
      coinvariantAction k G p (barSymbolZeroIso k G M (barSymbolHomologyIso k G M 0 (torBarIso k G M 0 z)))
  rw [show (barSymbolChainMap k G p).homologyMap 0
      (barSymbolHomologyIso k G M 0 (torBarIso k G M 0 z)) =
      barSymbolHomologyIso k G N 0 ((tensorAction k G p .bar).homologyMap 0 (torBarIso k G M 0 z)) from
    LinearMap.congr_fun (barSymbolHomology_natural k G p 0) (torBarIso k G M 0 z),
    ← torBar_natural, barSymbolZeroIso_fromTor, barSymbolZeroIso_fromTor, zeroIso_natural_original]

theorem explicitBarHomology : ExplicitBarHomologyType.{u,v,a,b} := by
  intro k G _ _
  refine ⟨barCoordinates k G, barCoordinates k G, barSymbolHomologyIso k G, barSymbolHomologyIso k G,
    fun M => (barToSymbols k G M).homologyMap_induces,
    fun N => (barToSymbols k G N).homologyMap_induces, ?_⟩
  intro M N p A
  let F := barSymbolChainMap k G p
  refine ⟨F, F.homologyMap, fun _ _ => rfl, F.homologyMap_induces, ?_⟩
  intro n z
  rw [homology_eq_tensorAction]
  exact LinearMap.congr_fun (barSymbolHomology_natural k G p n) z

theorem liftedSequenceNaturality : LiftedSequenceNaturalityType.{u,v,a,b,c,d,e,f,s} := by
  intro k G _ _ M N Q M' N' Q' i p i' p' α β γ hi hp h h'
  refine ⟨{
    τ₁ := ModuleCat.ofHom (liftedMap k G α)
    τ₂ := ModuleCat.ofHom (liftedMap k G β)
    τ₃ := ModuleCat.ofHom (liftedMap k G γ)
    comm₁₂ := ?_
    comm₂₃ := ?_ }, rfl, rfl, rfl⟩
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg ULift.up (LinearMap.congr_fun hi x.down)
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg ULift.up (LinearMap.congr_fun hp x.down)

variable {M : ModuleCat.{a} k[G]} {N : ModuleCat.{b} k[G]} {Q : ModuleCat.{c} k[G]}
  {i : CoefficientMap k G M N} {p : CoefficientMap k G N Q}

private theorem symbolTerms_exact (S : CoefficientSequence k G i p) :
    TermwiseExact (barSymbolChainMap k G i) (barSymbolChainMap k G p) := by
  intro n
  let α : (chains k G M).X n ≃ₗ[ℤ] ((barCoordinates k G).complex M).X n :=
    (RightBar.tensorIso k G M n).toAddEquiv.toIntLinearEquiv
  let β : (chains k G N).X n ≃ₗ[ℤ] ((barCoordinates k G).complex N).X n :=
    (RightBar.tensorIso k G N n).toAddEquiv.toIntLinearEquiv
  let γ : (chains k G Q).X n ≃ₗ[ℤ] ((barCoordinates k G).complex Q).X n :=
    (RightBar.tensorIso k G Q n).toAddEquiv.toIntLinearEquiv
  let f := (tensorAction k G i .bar).app n
  let g := (tensorAction k G p .bar).app n
  let F := (barSymbolChainMap k G i).app n
  let H := (barSymbolChainMap k G p).app n
  have hi : F.comp α.toLinearMap = β.toLinearMap.comp f :=
    LinearMap.ext fun z => (barAction_coordinates k G i n z).symm
  have hp : H.comp β.toLinearMap = γ.toLinearMap.comp g :=
    LinearMap.ext fun z => (barAction_coordinates k G p n z).symm
  have hex := S.chains_exact .bar n
  simp only [chain_eq_tensorAction] at hex
  obtain ⟨hf, hE, hg⟩ := hex
  refine ⟨?_, (LinearMap.exact_iff_of_surjective_of_bijective_of_injective _ _ _ _ _ _ _
    hi hp α.surjective β.bijective γ.injective).mp hE, ?_⟩
  · intro x y hxy
    obtain ⟨x, rfl⟩ := α.surjective x
    obtain ⟨y, rfl⟩ := α.surjective y
    exact congrArg α (hf (β.injective ((LinearMap.congr_fun hi x).symm.trans
      (hxy.trans (LinearMap.congr_fun hi y)))))
  · intro z
    obtain ⟨z, rfl⟩ := γ.surjective z
    obtain ⟨y, rfl⟩ := hg z
    exact ⟨β y, LinearMap.congr_fun hp y⟩

def barSymbolBoundary (S : CoefficientSequence k G i p) (n : ℕ) :
    Homology ((barCoordinates k G).complex Q) (n+1) →ₗ[ℤ]
      Homology ((barCoordinates k G).complex M) n :=
  (barSymbolHomologyIso k G M n).toLinearMap.comp
    ((S.boundary .bar n).comp (barSymbolHomologyIso k G Q (n+1)).symm.toLinearMap)

theorem barSymbolBoundary_onTensorClass (S : CoefficientSequence k G i p) (n : ℕ)
    (z : barHomology k G Q (n+1)) :
    barSymbolBoundary k G S n (barSymbolHomologyIso k G Q (n+1) z) =
      barSymbolHomologyIso k G M n (S.boundary .bar n z) := by
  change barSymbolHomologyIso k G M n
    (S.boundary .bar n ((barSymbolHomologyIso k G Q (n+1)).symm
      (barSymbolHomologyIso k G Q (n+1) z))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem barSymbolBoundary_onTorClass (h : ShortExact k G i p)
    (S : CoefficientSequence k G i p) (n : ℕ)
    (z : GroupCoinvariants.GroupHomology k G Q (n+1)) :
    barSymbolBoundary k G S n (barSymbolHomologyIso k G Q (n+1) (torBarIso k G Q (n+1) z)) =
      barSymbolHomologyIso k G M n (torBarIso k G M n (S.boundary .tor n z)) := by
  rw [barSymbolBoundary_onTensorClass, sequenceBoundary_eq k G h S .bar,
    sequenceBoundary_eq k G h S .tor, boundary_compare]

theorem barSymbolSequence_zero (S : CoefficientSequence k G i p) :
    Function.Exact (barSymbolBoundary k G S 0)
      (fun z => S.first.coinvariants (barSymbolZeroIso k G M z)) ∧
    Function.Exact S.first.coinvariants S.second.coinvariants ∧
    Function.Surjective S.second.coinvariants := by
  refine ⟨?_, S.zero_exact, S.zero_surjective⟩
  let e := (barSymbolHomologyIso k G N 0).toAddEquiv.trans (barSymbolZeroIso k G N)
  let first := S.first.coinvariants.toAddMonoidHom.toIntLinearMap.comp
    (barSymbolZeroIso k G M).toIntLinearEquiv.toLinearMap
  change Function.Exact (barSymbolBoundary k G S 0) first
  have square : first.comp (barSymbolHomologyIso k G M 0).toLinearMap =
      e.toIntLinearEquiv.toLinearMap.comp (S.first.homology .bar 0) := by
    apply LinearMap.ext
    intro z
    change S.first.coinvariants (barSymbolZeroIso k G M (barSymbolHomologyIso k G M 0 z)) =
      barSymbolZeroIso k G N (barSymbolHomologyIso k G N 0 (S.first.homology .bar 0 z))
    rw [coinvariants_eq_coinvariantAction, ← barSymbolZeroIso_natural, homology_eq_tensorAction]
    exact congrArg (barSymbolZeroIso k G N)
      (LinearMap.congr_fun (barSymbolHomology_natural k G i 0) z)
  exact (LinearMap.exact_iff_of_surjective_of_bijective_of_injective
    (S.boundary .bar 0) (S.first.homology .bar 0) (barSymbolBoundary k G S 0) first
    (barSymbolHomologyIso k G Q 1).toLinearMap
    (barSymbolHomologyIso k G M 0).toLinearMap e.toIntLinearEquiv.toLinearMap
    (LinearMap.ext (barSymbolBoundary_onTensorClass k G S 0)) square
    (barSymbolHomologyIso k G Q 1).surjective
    (barSymbolHomologyIso k G M 0).bijective e.injective).mp (S.exact .bar 0).2.2

theorem barSymbolBoundary_positive (S : CoefficientSequence k G i p) (n : ℕ) :
    PositiveBoundary (barSymbolChainMap k G i) (barSymbolChainMap k G p) n
      (barSymbolBoundary k G S n) := by
  intro z y x hy hx
  let α := symbolsToBar k G M
  let β := symbolsToBar k G N
  let γ := symbolsToBar k G Q
  have hS := S.positive .bar n
  simp only [chain_eq_tensorAction] at hS
  apply (barSymbolHomologyIso k G M n).symm.injective
  change (barSymbolHomologyIso k G M n).symm
    (barSymbolHomologyIso k G M n
      (S.boundary .bar n (homologyClass _ _ (γ.cyclesMap (n+1) z)))) =
    homologyClass _ n (α.cyclesMap n x)
  rw [LinearEquiv.symm_apply_apply]
  refine hS (γ.cyclesMap (n+1) z) (β.app (n+1) y) (α.cyclesMap n x) ?_ ?_
  · apply (RightBar.tensorIso k G Q (n+1)).injective
    change RightBar.tensorIso k G Q (n+1)
      ((tensorAction k G p .bar).app (n+1) ((RightBar.tensorIso k G N (n+1)).symm y)) =
      RightBar.tensorIso k G Q (n+1) ((RightBar.tensorIso k G Q (n+1)).symm z.val)
    rw [barAction_coordinates, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact hy
  · apply (RightBar.tensorIso k G N n).injective
    change RightBar.tensorIso k G N n
      ((tensorAction k G i .bar).app n ((RightBar.tensorIso k G M n).symm x.val)) =
      RightBar.tensorIso k G N n (((chains k G N).d (n+1) n).hom
        ((RightBar.tensorIso k G N (n+1)).symm y))
    rw [barAction_coordinates, LinearEquiv.apply_symm_apply]
    exact hx

theorem explicitBarSequence : ExplicitBarSequenceType.{u,v,a,b,c} := by
  intro k G _ _
  refine ⟨barCoordinates k G, barCoordinates k G, barCoordinates k G,
    barSymbolHomologyIso k G, barSymbolHomologyIso k G,
    fun M => (barToSymbols k G M).homologyMap_induces,
    fun Q => (barToSymbols k G Q).homologyMap_induces, ?_⟩
  intro M N Q i p S
  let I := barSymbolChainMap k G i
  let P := barSymbolChainMap k G p
  let α := barSymbolHomologyIso k G M
  let β := barSymbolHomologyIso k G N
  let γ := barSymbolHomologyIso k G Q
  refine ⟨I, P, I.homologyMap, P.homologyMap, barSymbolBoundary k G S, fun _ _ => rfl,
    fun _ _ => rfl, I.homologyMap_induces, P.homologyMap_induces, symbolTerms_exact k G S, ?_⟩
  intro n
  have hi (j : ℕ) : (I.homologyMap j).comp (α j).toLinearMap =
      (β j).toLinearMap.comp (S.first.homology .bar j) := by
    rw [homology_eq_tensorAction]
    exact barSymbolHomology_natural k G i j
  have hp (j : ℕ) : (P.homologyMap j).comp (β j).toLinearMap =
      (γ j).toLinearMap.comp (S.second.homology .bar j) := by
    rw [homology_eq_tensorAction]
    exact barSymbolHomology_natural k G p j
  have hd := barSymbolBoundary_onTensorClass k G S n
  have hd' : (barSymbolBoundary k G S n).comp (γ (n+1)).toLinearMap =
      (α n).toLinearMap.comp (S.boundary .bar n) := LinearMap.ext hd
  obtain ⟨h₁, h₂, h₃⟩ := S.exact .bar n
  refine ⟨barSymbolBoundary_positive k G S n, ?_, ?_, ?_, hd⟩
  · exact (LinearMap.exact_iff_of_surjective_of_bijective_of_injective _ _ _ _ _ _ _
      (hi _) (hp _) (α _).surjective (β _).bijective (γ _).injective).mp h₁
  · exact (LinearMap.exact_iff_of_surjective_of_bijective_of_injective _ _ _ _ _ _ _
      (hp _) hd' (β _).surjective (γ _).bijective (α _).injective).mp h₂
  · exact (LinearMap.exact_iff_of_surjective_of_bijective_of_injective _ _ _ _ _ _ _
      hd' (hi _) (γ _).surjective (α _).bijective (β _).injective).mp h₃

/-- Naturality on the cycle quotients of the original direct sums, including
the connecting square and the arrows at the coinvariant endpoint. -/
theorem barSymbolSequence_natural
    {M' : ModuleCat.{d} k[G]} {N' : ModuleCat.{e} k[G]} {Q' : ModuleCat.{f} k[G]}
    {i' : CoefficientMap k G M' N'} {p' : CoefficientMap k G N' Q'}
    (α : CoefficientMap k G M M') (β : CoefficientMap k G N N') (γ : CoefficientMap k G Q Q')
    (hi : i'.comp α = β.comp i) (hp : p'.comp β = γ.comp p)
    (S : CoefficientSequence k G i p) (T : CoefficientSequence k G i' p') :
    (∀ n : ℕ,
      ((barSymbolChainMap k G i').homologyMap n).comp ((barSymbolChainMap k G α).homologyMap n) =
        ((barSymbolChainMap k G β).homologyMap n).comp ((barSymbolChainMap k G i).homologyMap n) ∧
      ((barSymbolChainMap k G p').homologyMap n).comp ((barSymbolChainMap k G β).homologyMap n) =
        ((barSymbolChainMap k G γ).homologyMap n).comp ((barSymbolChainMap k G p).homologyMap n) ∧
      ((barSymbolChainMap k G α).homologyMap n).comp (barSymbolBoundary k G S n) =
        (barSymbolBoundary k G T n).comp ((barSymbolChainMap k G γ).homologyMap (n+1))) ∧
    T.first.coinvariants.comp (coinvariantAction k G α) =
      (coinvariantAction k G β).comp S.first.coinvariants ∧
    T.second.coinvariants.comp (coinvariantAction k G β) =
      (coinvariantAction k G γ).comp S.second.coinvariants := by
  refine ⟨?_, (sequenceNaturality k G α β γ hi hp S T
      (coefficientAction k G α) (coefficientAction k G β) (coefficientAction k G γ)).2⟩
  intro n
  have hi' := congrArg (barSymbolChainMap k G) hi
  have hp' := congrArg (barSymbolChainMap k G) hp
  rw [← barSymbolChainMap_comp, ← barSymbolChainMap_comp] at hi' hp'
  refine ⟨?_, ?_, ?_⟩
  · simpa only [LinearChainMap.homologyMap_comp] using congrArg (fun φ => φ.homologyMap n) hi'
  · simpa only [LinearChainMap.homologyMap_comp] using congrArg (fun φ => φ.homologyMap n) hp'
  · apply positive_naturality (barSymbolChainMap k G α) (barSymbolChainMap k G β)
      (barSymbolChainMap k G γ) _ _ (symbolTerms_exact k G S)
      (barSymbolBoundary_positive k G S n) (barSymbolBoundary_positive k G T n)
    · intro j
      exact congrArg (fun φ => φ.app j) hi'
    · intro j
      exact congrArg (fun φ => φ.app j) hp'

section DerivedBarSymbols
open DerivedGroupHomology.Specification
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
universe x y

variable [HasDerivedCategory.{x} (ModuleCat.{max u v a b c s} k[G])]
  [HasDerivedCategory.{y} (ModuleCat.{max u v a b c s} k)]
  [(minus (ModuleCat.{max u v a b c s} k[G])).IsTriangulated]
  [(minus (ModuleCat.{max u v a b c s} k)).IsTriangulated]
  (D : ExactLeftData.{(max u v a b c s)+1,max u v a b c s,
    (max u v a b c s)+1,max u v a b c s,x,y} (ambientCoinvariants.{u,v,max a b c s} k G))

/-- The same stalk-triangle boundary gives the positive boundary on the
original bar sums through the normalized Tor-to-bar comparison. -/
theorem derivedBoundary_onBarSymbols (h : ShortExact k G i p)
    (O : CoefficientSequence k G i p) (n : ℕ)
    (z : GroupCoinvariants.GroupHomology k G Q (n+1)) :
    let S := liftedSequence.{u,v,a,b,c,max u v s} k G h
    let hS := liftedShortExact.{u,v,a,b,c,max u v s} k G h
    let E := derivedTorIso.{u,v,max a b c s,x,y} k G D
    let q := homologyLift.{u,v,c,max u v a b c s} k G .tor Q (n+1)
    let l := homologyLift.{u,v,a,max u v a b c s} k G .tor M n
    barSymbolBoundary k G O n (barSymbolHomologyIso k G Q (n+1) (torBarIso k G Q (n+1) z)) =
      barSymbolHomologyIso k G M n (torBarIso k G M n
        (l.symm (((E (n+1)).inv.app S.X₃ ≫
          leftBoundary (ambientCoinvariants.{u,v,max a b c s} k G) D hS n ≫
          (E n).hom.app S.X₁) (q z)))) := by
  dsimp only
  rw [barSymbolBoundary_onTorClass k G h O, ← derivedBoundary_onTor.{u,v,a,b,c,s,x,y} k G D h O n z,
    LinearEquiv.symm_apply_apply]

end DerivedBarSymbols

end AdvancedHomologicalAlgebra.DerivedGroupHomologyOriginal
