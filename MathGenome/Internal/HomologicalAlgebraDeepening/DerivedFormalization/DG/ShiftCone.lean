import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.HomComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.ShiftCone
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v w

namespace DerivedFormalization.RightDGModule

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}
variable {M N : RightDGModule A}

/-- Shift a right dg module with the cohomological convention. -/
abbrev shift := @Specs.DerivedFormalization.DG.ShiftCone.shift

/-- Shift a homogeneous map of degree `r` with the sign `(-1)^(s*r)`. -/
abbrev shiftGraded (s r : ℤ) : GradedHom M N r →ₗ[k] GradedHom (shift M s) (shift N s) r :=
  Specs.DerivedFormalization.DG.ShiftCone.shiftGraded s r

/-- Shift a strict map, preserving its degree-zero components after reindexing. -/
abbrev shiftMap := @Specs.DerivedFormalization.DG.ShiftCone.shiftMap

/-- The signed shift on the dg category of right dg modules. -/
abbrev shiftDGFunctor := @Specs.DerivedFormalization.DG.ShiftCone.shiftDGFunctor

/-- The cone of a strict map, with the target in the first summand. -/
abbrev cone := @Specs.DerivedFormalization.DG.ShiftCone.cone

/-- The strict inclusion of the target into the cone. -/
abbrev coneInclusion := @Specs.DerivedFormalization.DG.ShiftCone.coneInclusion

/-- The strict quotient projection from the cone to the shifted source. -/
abbrev coneProjection := @Specs.DerivedFormalization.DG.ShiftCone.coneProjection

/-- The strict short complex underlying the cone sequence. -/
abbrev coneSequence := @Specs.DerivedFormalization.DG.ShiftCone.coneSequence

/-- Cohomology of the signed shift in degree `i` is cohomology in degree `i+s`. -/
noncomputable abbrev shiftHomologyIso := @Specs.DerivedFormalization.DG.ShiftCone.shiftHomologyIso

@[simp] theorem shiftGraded_app (s r : ℤ) (f : GradedHom M N r)
    (a : A.Obj) (i j : ℤ) (h : i+r = j) :
    (shiftGraded s r f).app a i j h =
      (s*r).negOnePow • f.app a (i+s) (j+s) (by omega) := rfl

/-- In degree zero the dg shift sends the cycle of a strict map to its shifted cycle. -/
@[simp] theorem shiftDGFunctor_map_strict (s : ℤ) (f : M ⟶ N) :
    ((shiftDGFunctor A s).map M N).f 0 (strictCycle f).val =
      (strictCycle (shiftMap s f)).val := by
  apply GradedHom.ext
  intro a i j h
  obtain rfl : i = j := by omega
  change (shiftGraded s 0 (strictCycle f).val).app a i i (add_zero i) =
    GradedHom.app (strictCycle (shiftMap s f)).val a i i (add_zero i)
  rw [shiftGraded_app, mul_zero, Int.negOnePow_zero, one_smul]
  rfl

/-- The cone acts on each summand by the original right action. -/
@[simp] theorem cone_act (f : M ⟶ N) {a b : A.Obj} (i j n : ℤ) (h : i+j = n)
    (p : ((cone f).complex b).X i) (z : (A.hom a b).X j) :
    (cone f).act i j n h p z =
      (N.act i j n h p.1 z, M.act (i+1) j (n+1) (by omega) p.2 z) := rfl

@[simp] theorem cone_d (f : M ⟶ N) (a : A.Obj) (i : ℤ) (p : ((cone f).complex a).X i) :
    ((cone f).complex a).d i (i+1) p =
      ((N.complex a).d i (i+1) p.1 + (f.app a).f (i+1) p.2,
        -(M.complex a).d (i+1) (i+1+1) p.2) :=
  Specs.DerivedFormalization.DG.ShiftCone.coneDiff_succ f a i p

@[simp] theorem coneInclusion_f (f : M ⟶ N) (a : A.Obj) (i : ℤ) (y : (N.complex a).X i) :
    ((coneInclusion f).app a).f i y = (y, 0) := rfl

@[simp] theorem coneProjection_f (f : M ⟶ N) (a : A.Obj) (i : ℤ)
    (p : ((cone f).complex a).X i) :
    ((coneProjection f).app a).f i p = p.2 := rfl

/-- The inclusion of the shifted source as a graded right-linear map. -/
def coneGradedSection (f : M ⟶ N) : GradedHom (shift M 1) (cone f) 0 :=
  GradedHom.mk (fun a i q e => by
    obtain rfl : i = q := by omega
    exact ModuleCat.ofHom (LinearMap.inr _ _ _)) (by
    intro a b i j n ir nr h hi hn x z
    obtain rfl : i = ir := by omega
    obtain rfl : n = nr := by omega
    apply Prod.ext
    · change (0 : (N.complex a).X n) = N.act i j n _ 0 z
      simp
    · rfl)

/-- Projection onto the target as a graded right-linear map. -/
def coneGradedRetraction (f : M ⟶ N) : GradedHom (cone f) N 0 :=
  GradedHom.mk (fun a i q e => by
    obtain rfl : i = q := by omega
    exact ModuleCat.ofHom (LinearMap.fst _ _ _)) (by
    intro a b i j n ir nr h hi hn p z
    obtain rfl : i = ir := by omega
    obtain rfl : n = nr := by omega
    rfl)

theorem coneGradedSplit : Specs.DerivedFormalization.DG.ShiftCone.GradedSplit.{u,v,w} := by
  intro k _ A M N f
  exact ⟨coneGradedSection f, coneGradedRetraction f, fun _ _ _ _ => ⟨rfl, rfl⟩⟩

private abbrev objectSequence (f : M ⟶ N) (a : A.Obj) :=
  Specs.DerivedFormalization.DG.ShiftCone.objectConeSequence f a

/-- The cone short exact sequence has the standard splitting in each degree. -/
def coneDegreeSplitting (f : M ⟶ N) (a : A.Obj) (i : ℤ) :
    ((objectSequence f a).map
      (HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℤ) i)).Splitting where
  r := (coneGradedRetraction f).app a i i (add_zero i)
  s := (coneGradedSection f).app a i i (add_zero i)
  f_r := rfl
  s_g := rfl
  id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro p
    change (p.1, (0 : (M.complex a).X (i+1))) + (0, p.2) = p
    exact Prod.ext (add_zero _) (zero_add _)

/-- Evaluating the cone sequence at any object gives a short exact sequence of complexes. -/
theorem coneShortExact (f : M ⟶ N) (a : A.Obj) : (objectSequence f a).ShortExact :=
  shortExact_of_degreewise_shortExact _ (fun i => (coneDegreeSplitting f a i).shortExact)

private theorem next_eq_succ (i : ℤ) : (ComplexShape.up ℤ).next i = i+1 :=
  (ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel i (i+1) from rfl)

private lemma shiftOneCycle (M : RightDGModule A) (a : A.Obj) (i : ℤ) :
    ((shift M 1).complex a).iCycles i ≫ (M.complex a).d (i+1) (i+1+1) = 0 := by
  have h := ((shift M 1).complex a).iCycles_d i (i+1)
  change _ ≫ ((1 : ℤ).negOnePow • (M.complex a).d (i+1) (i+1+1)) = 0 at h
  rwa [Int.negOnePow_one, Units.neg_smul, one_smul, Preadditive.comp_neg, neg_eq_zero] at h

/-- The positive quotient projection gives connecting homomorphism `H(f)`
under the canonical shift identification. -/
theorem coneConnectingMap (f : M ⟶ N) (a : A.Obj)
    (hS : (objectSequence f a).ShortExact) (i : ℤ) :
    hS.δ i (i+1) rfl = (shiftHomologyIso M 1 a i).hom ≫ homologyMap (f.app a) (i+1) := by
  let U := (shift M 1).complex a
  let x₃ := U.iCycles i
  let x₂ := x₃ ≫ (coneGradedSection f).app a i i (add_zero i)
  let x₁ := x₃ ≫ (f.app a).f (i+1)
  have hx₂ : x₂ ≫ (objectSequence f a).g.f i = x₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rfl
  have hx₁ : x₁ ≫ (objectSequence f a).f.f (i+1) =
      x₂ ≫ ((cone f).complex a).d i (i+1) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    have hz := CategoryTheory.congr_fun (shiftOneCycle M a i) z
    change (M.complex a).d (i+1) (i+1+1) (x₃ z) = 0 at hz
    change ((f.app a).f (i+1) (x₃ z), 0) =
      ((cone f).complex a).d i (i+1) (0, x₃ z)
    rw [cone_d]
    simp [hz]
  have hx₁cycle : x₁ ≫ (N.complex a).d (i+1) (i+1+1) = 0 := by
    dsimp only [x₁]
    rw [Category.assoc, (f.app a).comm, ← Category.assoc, shiftOneCycle M a i, zero_comp]
  have h := hS.δ_eq i (i+1) rfl x₃ (U.iCycles_d i (i+1)) x₂ hx₂ x₁ hx₁
    (i+1+1) (next_eq_succ (i+1))
  change U.liftCycles x₃ (i+1) (next_eq_succ i) (U.iCycles_d i (i+1)) ≫
    U.homologyπ i ≫ hS.δ i (i+1) rfl =
      (N.complex a).liftCycles x₁ (i+1+1) (next_eq_succ (i+1)) hx₁cycle ≫
        (N.complex a).homologyπ (i+1) at h
  have hl : U.liftCycles x₃ (i+1) (next_eq_succ i) (U.iCycles_d i (i+1)) = 𝟙 _ := by
    rw [← cancel_mono (U.iCycles i), liftCycles_i, Category.id_comp]
  rw [hl, Category.id_comp] at h
  apply (cancel_epi (U.homologyπ i)).1
  rw [h]
  have hs := (M.complex a).liftCycles_shift_homologyπ x₃ (i+1) (next_eq_succ i)
    (U.iCycles_d i (i+1)) (i+1) (add_comm 1 i) (i+1+1) (next_eq_succ (i+1))
  change U.liftCycles x₃ (i+1) (next_eq_succ i) (U.iCycles_d i (i+1)) ≫
    U.homologyπ i = _ at hs
  rw [hl, Category.id_comp] at hs
  have hs' : U.homologyπ i ≫ (shiftHomologyIso M 1 a i).hom =
      (M.complex a).liftCycles x₃ (i+1+1) (next_eq_succ (i+1)) (shiftOneCycle M a i) ≫
        (M.complex a).homologyπ (i+1) := by
    rw [← cancel_mono (shiftHomologyIso M 1 a i).inv, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
    simp only [CochainComplex.shiftFunctorObjXIso, XIsoOfEq, eqToIso_refl, Iso.refl_hom] at hs
    exact hs
  let e : U.homology i ≅ (M.complex a).homology (i+1) := shiftHomologyIso M 1 a i
  change U.homologyπ i ≫ e.hom = _ at hs'
  change (N.complex a).liftCycles x₁ (i+1+1) (next_eq_succ (i+1)) hx₁cycle ≫
    (N.complex a).homologyπ (i+1) = U.homologyπ i ≫ e.hom ≫ homologyMap (f.app a) (i+1)
  rw [← Category.assoc, hs', Category.assoc, homologyπ_naturality, ← Category.assoc,
    liftCycles_comp_cyclesMap]

private theorem objectQuasiIso_iff_coneAcyclic (f : M ⟶ N) (a : A.Obj) :
    QuasiIso (f.app a) ↔ ((cone f).complex a).Acyclic := by
  have hS := coneShortExact f a
  constructor
  · intro hf i
    have hδ (j : ℤ) : IsIso (hS.δ j (j+1) (by rfl)) := by
      rw [coneConnectingMap]
      exact IsIso.comp_isIso' (shiftHomologyIso M 1 a j).isIso_hom
        ((quasiIsoAt_iff_isIso_homologyMap (f.app a) (j+1)).1 (hf.quasiIsoAt _))
    rw [exactAt_iff_isZero_homology]
    apply (hS.homology_exact₂ i).isZero_X₂
    · have hi : i-1+1 = i := by omega
      obtain ⟨j, rfl⟩ : ∃ j : ℤ, j+1 = i := ⟨i-1, hi⟩
      have := hδ j
      change homologyMap (objectSequence f a).f (j+1) = 0
      rw [← cancel_epi (hS.δ j (j+1) (by rfl)), comp_zero]
      exact hS.δ_comp j (j+1) rfl
    · have := hδ i
      change homologyMap (objectSequence f a).g i = 0
      rw [← cancel_mono (hS.δ i (i+1) (by rfl)), zero_comp]
      exact hS.comp_δ i (i+1) rfl
  · intro h
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    obtain ⟨j, rfl⟩ : ∃ j : ℤ, j+1 = i := ⟨i-1, by omega⟩
    have e := hS.isIso_δ j (j+1) rfl (h j).isZero_homology (h (j+1)).isZero_homology
    rw [coneConnectingMap] at e
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ (shiftHomologyIso M 1 a j).hom
      (homologyMap (f.app a) (j+1)) (shiftHomologyIso M 1 a j).isIso_hom e

/-- A strict dg map is an objectwise quasi-isomorphism exactly when its cone is acyclic. -/
theorem quasiIso_iff_cone_acyclic (f : M ⟶ N) : IsQuasiIso f ↔ Acyclic (cone f) :=
  ⟨fun hf a => (objectQuasiIso_iff_coneAcyclic f a).1 (hf a),
    fun hc a => (objectQuasiIso_iff_coneAcyclic f a).2 (hc a)⟩

end DerivedFormalization.RightDGModule
