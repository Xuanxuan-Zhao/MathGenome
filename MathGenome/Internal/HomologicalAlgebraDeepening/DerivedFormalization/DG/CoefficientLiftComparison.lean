import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CoefficientLift
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.ShiftCone
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.Derived
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.CoefficientLiftComparison

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex.HomComplex

universe u v w t s

namespace DerivedFormalization.DG.CoefficientLift

open Specs.DerivedFormalization.DG.CoefficientLiftComparison
open RightDGModule (GradedHom homComplex)

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}
variable {M N P : RightDGModule A}

theorem componentComparison : ComponentComparison.{u,v,w,t} :=
  fun A => by constructor <;> intros <;> rfl

theorem cycleBoundaryComparison : CycleBoundaryComparison.{u,v,t} := by
  intro k _ C
  constructor
  · intro i j x
    exact ⟨congrArg ULift.down, ULift.ext⟩
  · intro i j y
    exact ⟨fun ⟨x, e⟩ => ⟨x.down, congrArg ULift.down e⟩,
      fun ⟨x, e⟩ => ⟨ULift.up x, ULift.ext e⟩⟩

set_option backward.isDefEq.respectTransparency false in
theorem homologyComparison : HomologyComparison.{u,v,t} := by
  intro k _
  constructor
  · intro C i
    let S := C.sc i
    let U := ModuleCat.uliftFunctor.{t,v} k
    let h := S.homologyData.left
    refine ⟨S.mapCyclesIso_hom_iCycles U, ?_⟩
    change (S.mapCyclesIso U).hom ≫ U.map S.homologyπ =
      (S.map U).homologyπ ≫ (S.mapHomologyIso U).hom
    rw [h.mapCyclesIso_eq U, h.mapHomologyIso_eq U]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc, ← Functor.map_comp]
    rw [(h.map U).homologyπ_comp_homologyIso_hom_assoc, ← h.π_comp_homologyIso_inv, U.map_comp]
    rfl
  · intro C D f i
    exact ShortComplex.mapHomologyIso_hom_naturality ((shortComplexFunctor _ _ i).map f)
      (ModuleCat.uliftFunctor.{t,v} k)

theorem lift_acyclic_iff (M : RightDGModule A) :
    (liftModule.{u,v,w,t} M).Acyclic ↔ M.Acyclic := by
  change (∀ a i, (CUp.{u,v,t} (M.complex a)).ExactAt i) ↔
    (∀ a i, (M.complex a).ExactAt i)
  simp only [exactAt_iff_isZero_homology]
  let U := ModuleCat.uliftFunctor.{t,v} k
  have compare (a : A.Obj) (i : ℤ) :
      IsZero ((CUp.{u,v,t} (M.complex a)).homology i) ↔ IsZero ((M.complex a).homology i) := by
    let H := (M.complex a).homology i
    have h : IsZero (U.obj H) ↔ IsZero H := by
      simp only [IsZero.iff_id_eq_zero, ← U.map_id, ← U.map_zero, U.map_injective.eq_iff]
    exact ⟨fun h' => h.mp (h'.of_iso (homologyIso.{u,v,t} (M.complex a) i).symm),
      fun h' => (h.mpr h').of_iso (homologyIso.{u,v,t} (M.complex a) i)⟩
  exact ⟨fun h a i => (compare a i).mp (h a i), fun h a i => (compare a i).mpr (h a i)⟩

theorem lift_quasiIso_iff (f : M ⟶ N) :
    RightDGModule.IsQuasiIso (liftMap.{u,v,w,t} f) ↔ RightDGModule.IsQuasiIso f := by
  change (∀ a, QuasiIso ((complexLift.{u,v,t} k).map (f.app a))) ↔
    (∀ a, QuasiIso (f.app a))
  apply forall_congr'
  intro a
  rw [quasiIso_iff, quasiIso_iff]
  apply forall_congr'
  intro i
  simp only [quasiIsoAt_iff_isIso_homologyMap]
  let U := ModuleCat.uliftFunctor.{t,v} k
  have e := (homologyComparison.{u,v,t} (k := k)).2 (f.app a) i
  constructor
  · intro h
    have : IsIso (U.map (homologyMap (f.app a) i)) := by
      rw [← isIso_comp_left_iff (homologyIso.{u,v,t} (M.complex a) i).hom, ← e]
      infer_instance
    exact isIso_of_reflects_iso _ U
  · intro h
    rw [← isIso_comp_right_iff _ (homologyIso.{u,v,t} (N.complex a) i).hom, e]
    infer_instance

theorem mapProperties : MapProperties.{u,v,w,t} := by
  intro k _ A M N
  refine ⟨lift_acyclic_iff M, ?_⟩
  intro f
  refine ⟨?_, ?_, lift_quasiIso_iff f⟩
  · apply forall_congr'
    intro a
    apply forall_congr'
    intro i
    change Function.Injective
      (ULift.up ∘ (f.app a).f i ∘ ULift.down) ↔ Function.Injective ((f.app a).f i)
    exact ⟨fun h x y e => congrArg ULift.down (h (congrArg ULift.up e)),
      fun h _ _ e => ULift.ext (h (congrArg ULift.down e))⟩
  · apply forall_congr'
    intro a
    apply forall_congr'
    intro i
    change Function.Surjective
      (ULift.up ∘ (f.app a).f i ∘ ULift.down) ↔ Function.Surjective ((f.app a).f i)
    exact ⟨fun h y => let ⟨x, e⟩ := h (ULift.up y); ⟨x.down, congrArg ULift.down e⟩,
      fun h y => let ⟨x, e⟩ := h y.down; ⟨ULift.up x, ULift.ext e⟩⟩

theorem evaluation : Evaluation.{u,v,w,t} := by
  intro k _ A M L f
  have H := (homologyComparison.{u,v,t} (k := k)).1
  let U := ModuleCat.uliftFunctor.{t,v} k
  constructor
  · intro a i j x
    exact congrArg ULift.down (CategoryTheory.congr_fun ((f.app a).comm i j) x).symm
  · intro a b i j n h x z
    exact congrArg ULift.down (f.comm_act i j n h x (ULift.up z))
  · intro a i x
    have e : (L.complex a).iCycles i ≫ (f.app a).f i =
        cyclesMap (f.app a) i ≫ (cyclesIso.{u,v,t} (M.complex a) i).hom ≫
          U.map ((M.complex a).iCycles i) := by
      rw [(H (M.complex a) i).1, cyclesMap_i]
    exact congrArg ULift.down (CategoryTheory.congr_fun e x)
  · intro a i x
    have e : (L.complex a).homologyπ i ≫
        (homologyMap (f.app a) i ≫ (homologyIso.{u,v,t} (M.complex a) i).hom) =
          (cyclesMap (f.app a) i ≫ (cyclesIso.{u,v,t} (M.complex a) i).hom) ≫
            U.map ((M.complex a).homologyπ i) := by
      rw [Category.assoc, (H (M.complex a) i).2, ← Category.assoc,
        homologyπ_naturality, Category.assoc]
    exact congrArg ULift.down (CategoryTheory.congr_fun e x)
  · intro a i
    exact Function.Surjective.of_comp_iff' (termDown (M.complex a) i).bijective _
  · intro a i
    let e := (homologyIso.{u,v,t} (M.complex a) i)
    exact ((ULift.moduleEquiv (R := k)).bijective.of_comp_iff'
      (homologyMap (f.app a) i ≫ e.hom)).trans
      ((ConcreteCategory.isIso_iff_bijective _).symm.trans (isIso_comp_right_iff _ _))

private def upGraded (r : ℤ) (f : GradedHom M N r) :
    GradedHom (liftModule.{u,v,w,t} M) (liftModule.{u,v,w,t} N) r :=
  GradedHom.mk (fun a i j h => (ModuleCat.uliftFunctor.{t,v} k).map (f.app a i j h))
    (fun i j n ir nr h hi hn x z => ULift.ext (f.comm_act i j n ir nr h hi hn x.down z.down))

private def downGraded (r : ℤ) (f : GradedHom (liftModule.{u,v,w,t} M) (liftModule.{u,v,w,t} N) r) :
    GradedHom M N r :=
  GradedHom.mk (fun a i j h => (ModuleCat.fullyFaithfulUliftFunctor.{u,v,t} k).preimage (f.app a i j h))
    (fun i j n ir nr h hi hn x z => congrArg ULift.down
      (f.comm_act i j n ir nr h hi hn (ULift.up x) (ULift.up z)))

/-- Conjugate a homogeneous right-linear map by the degreewise coefficient equivalences. -/
def gradedEquiv (M N : RightDGModule A) (r : ℤ) :
    GradedHom M N r ≃ₗ[k] GradedHom (liftModule.{u,v,w,t} M) (liftModule.{u,v,w,t} N) r where
  toFun := upGraded r
  invFun := downGraded r
  left_inv f := by
    apply GradedHom.ext
    intro a i j h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  right_inv f := by
    apply GradedHom.ext
    intro a i j h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ULift.ext rfl
  map_add' f g := by
    apply GradedHom.ext
    intro a i j h
    change (ModuleCat.uliftFunctor.{t,v} k).map ((f.val a + g.val a).v i j h) =
      (upGraded r f).app a i j h + (upGraded r g).app a i j h
    rw [Cochain.add_v, Functor.map_add]
    rfl
  map_smul' c f := by
    apply GradedHom.ext
    intro a i j h
    change (ModuleCat.uliftFunctor.{t,v} k).map ((c • f.val a).v i j h) =
      c • (upGraded r f).app a i j h
    rw [Cochain.smul_v, Functor.map_smul]
    rfl

@[simp] theorem gradedEquiv_apply_down (r : ℤ) (f : GradedHom M N r)
    (a : A.Obj) (i j : ℤ) (h : i+r = j) (x : ((liftModule.{u,v,w,t} M).complex a).X i) :
    ((gradedEquiv.{u,v,w,t} M N r f).app a i j h x).down = f.app a i j h x.down :=
  rfl

theorem gradedEquiv_comm_d (r q : ℤ) (f : GradedHom M N r) :
    gradedEquiv.{u,v,w,t} M N q ((homComplex M N).d r q f) =
      (homComplex (liftModule.{u,v,w,t} M) (liftModule.{u,v,w,t} N)).d r q
        (gradedEquiv.{u,v,w,t} M N r f) := by
  by_cases h : r+1 = q
  · subst q
    apply GradedHom.ext
    intro a i j e
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply ULift.ext
    change ((gradedEquiv.{u,v,w,t} M N (r+1) ((homComplex M N).d r (r+1) f)).app a i j e x).down =
      (GradedHom.app ((homComplex (liftModule.{u,v,w,t} M) (liftModule.{u,v,w,t} N)).d r (r+1)
        (gradedEquiv.{u,v,w,t} M N r f)) a i j e x).down
    rw [gradedEquiv_apply_down, RightDGModule.differentialFormula,
      RightDGModule.differentialFormula]
    rfl
  · have h' : ¬ (ComplexShape.up ℤ).Rel r q := h
    rw [(homComplex M N).shape _ _ h', (homComplex (liftModule.{u,v,w,t} M)
      (liftModule.{u,v,w,t} N)).shape _ _ h']
    simp

theorem gradedEquiv_comp (s r n : ℤ) (h : s+r = n) (g : GradedHom N P s) (f : GradedHom M N r) :
    gradedEquiv.{u,v,w,t} M P n ((RightDGModule.dgCategory A).comp s r n h g f) =
      (RightDGModule.dgCategory (liftCategory.{u,v,w,t} A)).comp s r n h
        (gradedEquiv.{u,v,w,t} N P s g) (gradedEquiv.{u,v,w,t} M N r f) := by
  apply GradedHom.ext (M := liftModule.{u,v,w,t} M) (N := liftModule.{u,v,w,t} P)
  intro a i j e
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply ULift.ext
  change ((gradedEquiv.{u,v,w,t} M P n ((RightDGModule.dgCategory A).comp s r n h g f)
    ).app a i j e x).down =
      (GradedHom.app ((RightDGModule.dgCategory (liftCategory.{u,v,w,t} A)).comp s r n h
        (gradedEquiv.{u,v,w,t} N P s g) (gradedEquiv.{u,v,w,t} M N r f)) a i j e x).down
  rw [gradedEquiv_apply_down, RightDGModule.compositionFormula s r n h g f a i (i+r) j
    rfl (by omega), RightDGModule.compositionFormula s r n h _ _ a i (i+r) j rfl (by omega)]
  rfl

theorem gradedEquiv_strict (f : M ⟶ N) :
    gradedEquiv.{u,v,w,t} M N 0 (Specs.DerivedFormalization.DG.HomComplex.ofStrict f) =
      Specs.DerivedFormalization.DG.HomComplex.ofStrict (liftMap.{u,v,w,t} f) := by
  apply GradedHom.ext
  intro a i j h
  obtain rfl : i = j := (add_zero i).symm.trans h
  change (ModuleCat.uliftFunctor.{t,v} k).map ((Cochain.ofHom (f.app a)).v i i (add_zero i)) =
    (Cochain.ofHom ((liftMap.{u,v,w,t} f).app a)).v i i (add_zero i)
  simp only [Cochain.ofHom_v]
  rfl

theorem gradedComparison : GradedComparison.{u,v,w,t} :=
  fun _ => ⟨gradedEquiv, ⟨fun _ _ _ _ _ _ _ => rfl,
    gradedEquiv_comm_d, gradedEquiv_comp, gradedEquiv_strict, fun _ _ _ _ => rfl⟩⟩

open RightDGModule (K D Q homotopyClass homotopyCriterion toHomotopyCategory instCategoryK)

theorem homotopyClass_lift_iff (f g : M ⟶ N) :
    homotopyClass (liftMap.{u,v,w,t} f) = homotopyClass (liftMap.{u,v,w,t} g) ↔
      homotopyClass f = homotopyClass g := by
  rw [homotopyCriterion, homotopyCriterion]
  let E := gradedEquiv.{u,v,w,t} M N (-1)
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨E.symm h, ?_⟩
    rw [← E.apply_symm_apply h] at hh
    intro a i x
    exact congrArg ULift.down (hh a i (ULift.up x))
  · rintro ⟨h, hh⟩
    exact ⟨E h, fun a i x => ULift.ext (hh a i x.down)⟩

theorem homotopyComparison : HomotopyComparison.{u,v,w,t} :=
  fun _ _ => homotopyClass_lift_iff _ _

private def downStrict (f : liftModule.{u,v,w,t} M ⟶ liftModule.{u,v,w,t} N) : M ⟶ N where
  app a := CochainComplex.ofHom
    (fun i => (ModuleCat.fullyFaithfulUliftFunctor.{u,v,t} k).preimage ((f.app a).f i))
    (by
      intro i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact congrArg ULift.down (CategoryTheory.congr_fun ((f.app a).comm i (i+1)) (ULift.up x)))
  comm_act := by
    intro a b i j n h x z
    exact congrArg ULift.down (f.comm_act i j n h (ULift.up x) (ULift.up z))

private theorem liftMap_downStrict (f : liftModule.{u,v,w,t} M ⟶ liftModule.{u,v,w,t} N) :
    liftMap.{u,v,w,t} (downStrict f) = f := by
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.hom_ext
  intro i
  exact (ModuleCat.fullyFaithfulUliftFunctor.{u,v,t} k).map_preimage ((f.app a).f i)

/-- Coefficient enlargement is fully faithful on strict maps. -/
def liftFullyFaithful (A : DGCategory.{u,v,w} k) : (liftFunctor.{u,v,w,t} A).FullyFaithful where
  preimage f := downStrict f
  map_preimage f := liftMap_downStrict f
  preimage_map f := by
    apply RightDGModuleModel.hom_ext
    intro a
    apply HomologicalComplex.hom_ext
    intro i
    exact (ModuleCat.fullyFaithfulUliftFunctor.{u,v,t} k).preimage_map ((f.app a).f i)

theorem strictFullFaithfulness : StrictFullFaithfulness.{u,v,w,t} := fun A => ⟨liftFullyFaithful A⟩

noncomputable section

private def strictRepresentative {M N : K A} (g : M ⟶ N) :
    RightDGModule.Hom M N :=
  (RightDGModule.homotopyClass_surjective g).choose

private theorem strictRepresentative_spec {M N : K A} (g : M ⟶ N) :
    homotopyClass (strictRepresentative g) = g :=
  (RightDGModule.homotopyClass_surjective g).choose_spec

/-- The coefficient lift on the degree-zero cohomology category. -/
@[reducible] def homotopyLift (A : DGCategory.{u,v,w} k) : K A ⥤ K (liftCategory.{u,v,w,t} A) where
  obj M := liftModule.{u,v,w,t} M
  map g := homotopyClass (liftMap.{u,v,w,t} (strictRepresentative g))
  map_id M := by
    let M₀ : RightDGModule A := M
    change homotopyClass (liftMap.{u,v,w,t} (strictRepresentative (𝟙 M))) =
      homotopyClass (liftMap.{u,v,w,t} (𝟙 M₀))
    apply (homotopyClass_lift_iff.{u,v,w,t} _ _).mpr
    exact strictRepresentative_spec _
  map_comp {M N P} f g := by
    let q := toHomotopyCategory A
    let q' := toHomotopyCategory (liftCategory.{u,v,w,t} A)
    change q'.map (liftMap.{u,v,w,t} (strictRepresentative (f ≫ g))) =
      q'.map (liftMap.{u,v,w,t} (strictRepresentative f)) ≫
        q'.map (liftMap.{u,v,w,t} (strictRepresentative g))
    rw [← q'.map_comp, ← (liftFunctor.{u,v,w,t} A).map_comp]
    apply (homotopyClass_lift_iff.{u,v,w,t} _ _).mpr
    change homotopyClass (strictRepresentative (f ≫ g)) =
      q.map (strictRepresentative f ≫ strictRepresentative g)
    rw [strictRepresentative_spec, q.map_comp]
    exact congrArg₂ (· ≫ ·) (strictRepresentative_spec f).symm (strictRepresentative_spec g).symm

@[simp] theorem homotopyLift_map_class (f : M ⟶ N) :
    (homotopyLift.{u,v,w,t} A).map (homotopyClass f) =
      homotopyClass (liftMap.{u,v,w,t} f) :=
  (homotopyClass_lift_iff.{u,v,w,t} _ _).mpr (strictRepresentative_spec _)

/-- Every class between coefficient lifts has a unique original class. -/
def homotopyLiftFullyFaithful (A : DGCategory.{u,v,w} k) :
    (homotopyLift.{u,v,w,t} A).FullyFaithful where
  preimage g := homotopyClass (downStrict (strictRepresentative g))
  map_preimage g := by
    rw [homotopyLift_map_class, liftMap_downStrict, strictRepresentative_spec]
  preimage_map g := by
    let f := strictRepresentative ((homotopyLift.{u,v,w,t} A).map g)
    change homotopyClass (downStrict f) = g
    rw [← strictRepresentative_spec g]
    apply (homotopyClass_lift_iff.{u,v,w,t} _ _).mp
    rw [liftMap_downStrict, strictRepresentative_spec]

private theorem liftInverts (A : DGCategory.{u,v,w} k) :
    (RightDGModule.quasiIsomorphisms A).IsInvertedBy
      (homotopyLift.{u,v,w,t} A ⋙ Q (liftCategory.{u,v,w,t} A) ⟨instCategoryK _, rfl⟩) := by
  intro M N g hg
  obtain ⟨f, rfl, hf⟩ := hg
  change IsIso ((Q (liftCategory.{u,v,w,t} A) ⟨instCategoryK _, rfl⟩).map
    ((homotopyLift.{u,v,w,t} A).map (homotopyClass f)))
  rw [homotopyLift_map_class]
  apply Localization.inverts (Q (liftCategory.{u,v,w,t} A) ⟨instCategoryK _, rfl⟩) (RightDGModule.quasiIsomorphisms _)
  exact (RightDGModule.quasiIsomorphisms_homotopyClass _).mpr ((lift_quasiIso_iff f).mpr hf)

/-- The functor induced by coefficient enlargement on the native localizations. -/
def derivedLift (A : DGCategory.{u,v,w} k) : D A ⟨instCategoryK A, rfl⟩ ⥤ D (liftCategory.{u,v,w,t} A) ⟨instCategoryK _, rfl⟩ :=
  Localization.lift (homotopyLift.{u,v,w,t} A ⋙ Q (liftCategory.{u,v,w,t} A) ⟨instCategoryK _, rfl⟩)
    (liftInverts A) (Q A ⟨instCategoryK A, rfl⟩)

def derivedLiftComparison (A : DGCategory.{u,v,w} k) :
    Q A ⟨instCategoryK A, rfl⟩ ⋙ derivedLift.{u,v,w,t} A ≅
      homotopyLift.{u,v,w,t} A ⋙ Q (liftCategory.{u,v,w,t} A) ⟨instCategoryK _, rfl⟩ :=
  Localization.fac _ (liftInverts A) (Q A ⟨instCategoryK A, rfl⟩)

theorem homotopyAndDerivedComparison : HomotopyAndDerivedComparison.{u,v,w,t} := by
  intro k _ A h h'
  exact ⟨homotopyLift A, ⟨homotopyLiftFullyFaithful A⟩, fun _ => rfl,
    fun f => heq_of_eq (homotopyLift_map_class f), derivedLift A, ⟨derivedLiftComparison A⟩⟩

end

/-- Build a strict isomorphism from linear isomorphisms commuting with differential and action. -/
def isoOfComponents (e : ∀ a i, (M.complex a).X i ≃ₗ[k] (N.complex a).X i)
    (hd : ∀ a i x, e a (i+1) ((M.complex a).d i (i+1) x) =
      (N.complex a).d i (i+1) (e a i x))
    (ha : ∀ {a b : A.Obj} i j n (h : i+j = n) x z,
      e a n (M.act i j n h x z) = N.act i j n h (e b i x) z) : M ≅ N := by
  let c (a : A.Obj) : M.complex a ≅ N.complex a :=
    HomologicalComplex.Hom.isoOfComponents (fun i => (e a i).toModuleIso) (by
      intro i j h
      obtain rfl : i+1 = j := h
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (hd a i x).symm)
  refine ⟨⟨fun a => (c a).hom, fun i j n h x z => ha i j n h x z⟩, ⟨fun a => (c a).inv, ?_⟩, ?_, ?_⟩
  · intro a b i j n h x z
    change (e a n).symm (N.act i j n h x z) = M.act i j n h ((e b i).symm x) z
    apply (e a n).injective
    rw [LinearEquiv.apply_symm_apply, ha, LinearEquiv.apply_symm_apply]
  · exact RightDGModuleModel.hom_ext fun a => (c a).hom_inv_id
  · exact RightDGModuleModel.hom_ext fun a => (c a).inv_hom_id

theorem representableComparison : RepresentableComparison.{u,v,w,t} := fun _ _ => rfl

/-- Yoneda extension transports by raising the coefficient of the represented element. -/
theorem gradedEquiv_yonedaExtend (a : A.Obj) (r : ℤ) (x : (M.complex a).X r) :
    gradedEquiv.{u,v,w,t} (RightDGModule.representable a) M r
      (RightDGModule.yonedaExtend a M r x) =
    RightDGModule.yonedaExtend (A := liftCategory.{u,v,w,t} A) a
      (liftModule.{u,v,w,t} M) r (ULift.up x) := by
  apply GradedHom.ext
  intro b i j h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rfl

theorem zeroComparison : ZeroComparison.{u,v,w,t} := by
  intro k _ A Z
  let F := liftFunctor.{u,v,w,t} A
  let h := liftFullyFaithful.{u,v,w,t} A
  have hz : F.map (0 : Z ⟶ Z) = 0 := by
    apply RightDGModuleModel.hom_ext
    intro a
    exact (complexLift.{u,v,t} k).map_zero _ _
  rw [IsZero.iff_id_eq_zero, IsZero.iff_id_eq_zero]
  change 𝟙 Z = 0 ↔ 𝟙 (F.obj Z) = 0
  rw [← F.map_id, ← hz]
  exact ⟨congrArg F.map, h.map_injective⟩

/-- The comparison with any chosen strict zero object is canonical. -/
noncomputable def zeroIso (hM : IsZero M)
    {Z : RightDGModule (liftCategory.{u,v,w,t} A)} (hZ : IsZero Z) :
    liftModule.{u,v,w,t} M ≅ Z :=
  ((zeroComparison.{u,v,w,t} M).mp hM).iso hZ

open RightDGModule (shift shiftMap cone coneInclusion coneProjection)

/-- The strict shift comparison leaves the lifted element in degree `i+s` unchanged. -/
def shiftIso (M : RightDGModule A) (s : ℤ) :
    liftModule.{u,v,w,t} (shift M s) ≅ shift (liftModule.{u,v,w,t} M) s :=
  isoOfComponents (fun _ _ => LinearEquiv.refl k _) (fun _ _ _ => rfl)
    (fun _ _ _ _ _ _ => rfl)

theorem shiftComparison : ShiftComparison.{u,v,w,t} := by
  intro k _ A s
  refine ⟨fun M => shiftIso M s, fun _ _ _ _ => rfl, ?_⟩
  intro M N f
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.hom_ext
  intro i
  rfl

private def coneTermEquiv (f : M ⟶ N) (a : A.Obj) (i : ℤ) :
    ((liftModule.{u,v,w,t} (cone f)).complex a).X i ≃ₗ[k]
      ((cone (liftMap.{u,v,w,t} f)).complex a).X i :=
  ULift.moduleEquiv.trans (ULift.moduleEquiv.symm.prodCongr ULift.moduleEquiv.symm)

/-- The strict cone comparison sends a lifted pair to the pair of lifted entries. -/
def coneIso (f : M ⟶ N) : liftModule.{u,v,w,t} (cone f) ≅ cone (liftMap.{u,v,w,t} f) :=
  isoOfComponents (coneTermEquiv f)
    (by
      intro a i x
      change (ULift.up (Specs.DerivedFormalization.DG.ShiftCone.coneDiff f a i (i+1) x.down).1,
          ULift.up (Specs.DerivedFormalization.DG.ShiftCone.coneDiff f a i (i+1) x.down).2) =
        Specs.DerivedFormalization.DG.ShiftCone.coneDiff (liftMap.{u,v,w,t} f) a i (i+1)
          (ULift.up x.down.1, ULift.up x.down.2)
      rw [Specs.DerivedFormalization.DG.ShiftCone.coneDiff_succ,
        Specs.DerivedFormalization.DG.ShiftCone.coneDiff_succ]
      rfl)
    (fun _ _ _ _ _ _ => rfl)

theorem coneComparison : ConeComparison.{u,v,w,t} := by
  intro k _ A
  refine ⟨fun M => shiftIso M 1, fun _ _ _ _ => rfl, fun f => coneIso f,
    fun _ _ _ _ => rfl, ?_, ?_⟩
  · intro M N f
    constructor <;> (
      apply RightDGModuleModel.hom_ext
      intro a
      apply HomologicalComplex.hom_ext
      intro i
      rfl)
  · intro M N M' N' f g p q h
    apply RightDGModuleModel.hom_ext
    intro a
    apply HomologicalComplex.hom_ext
    intro i
    rfl

private def nestedEquiv (C : ModuleCochain.{u,v} k) (i : ℤ) :
    (CUp.{u,max v t,s} (CUp.{u,v,t} C)).X i ≃ₗ[k] (CUp.{u,v,max t s} C).X i :=
  ULift.moduleEquiv.trans (ULift.moduleEquiv.trans ULift.moduleEquiv.symm)

private def flattenComplex (C : ModuleCochain.{u,v} k) :
    CUp.{u,max v t,s} (CUp.{u,v,t} C) ≅ CUp.{u,v,max t s} C :=
  HomologicalComplex.Hom.isoOfComponents (fun i => (nestedEquiv.{u,v,t,s} C i).toModuleIso)
    (fun _ _ _ => rfl)

/-- Identify the doubly lifted arrows with the one-step lift by flattening the lifts. -/
@[reducible] def flattenCategory (A : DGCategory.{u,v,w} k) :
    DGFunctor (doubleCategory.{u,v,w,t,s} A) (liftCategory.{u,v,w,max t s} A) where
  obj := id
  map a b := (flattenComplex.{u,v,t,s} (A.hom a b)).hom
  map_id _ := rfl
  map_comp _ _ _ _ _ _ := rfl

/-- Flatten the two lifts of every module coefficient over the arrow comparison. -/
def flattenModule (M : RightDGModule A) :
    doubleModule.{u,v,w,t,s} M ≅
      restrictModule (flattenCategory.{u,v,w,t,s} A) (liftModule.{u,v,w,max t s} M) :=
  isoOfComponents (fun a i => nestedEquiv.{u,v,t,s} (M.complex a) i) (fun _ _ _ => rfl)
    (fun _ _ _ _ _ _ => rfl)

theorem successiveComparison : SuccessiveComparison.{u,v,w,t,s} := by
  intro k _ A
  refine ⟨flattenCategory A, rfl, fun a b => (flattenComplex (A.hom a b)).isIso_hom,
    fun _ _ _ _ => HEq.rfl, flattenModule, fun _ _ _ _ => HEq.rfl, ?_⟩
  intro M N f
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.hom_ext
  intro i
  rfl

private def downComplex (C : ModuleCochain.{u,max v t} k) : CUp.{u,max v t,t} C ≅ C :=
  HomologicalComplex.Hom.isoOfComponents (fun i => (termDown.{u,max v t,t} C i).toModuleIso)
    (fun _ _ _ => rfl)

/-- Remove a coefficient lift that stays within the existing universe. -/
@[reducible] def downCategory (A : DGCategory.{u,max v t,w} k) :
    DGFunctor (liftCategory.{u,max v t,w,t} A) A where
  obj := id
  map a b := (downComplex.{u,v,t} (A.hom a b)).hom
  map_id _ := rfl
  map_comp _ _ _ _ _ _ := rfl

/-- Compare the lifted module to the original module restricted along the arrow identification. -/
def downModule {B : DGCategory.{u,max v t,w} k} (M : RightDGModule B) :
    liftModule.{u,max v t,w,t} M ≅ restrictModule (downCategory.{u,v,w,t} B) M :=
  isoOfComponents (fun a i => termDown.{u,max v t,t} (M.complex a) i)
    (fun _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl)

theorem sameUniverseComparison : SameUniverseComparison.{u,v,w,t} := by
  intro k _ A
  refine ⟨downCategory A, rfl, fun a b => (downComplex (A.hom a b)).isIso_hom,
    fun _ _ _ _ => HEq.rfl, downModule, fun _ _ _ _ => HEq.rfl, ?_⟩
  intro M N f
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.hom_ext
  intro i
  rfl

open Specs.DerivedFormalization.DG.Basic (cyclesZero boundariesZero h0Hom classOf)

private def liftHomCycles (M N : RightDGModule A) :
    cyclesZero (homComplex M N) →ₗ[k]
      cyclesZero (homComplex (liftModule.{u,v,w,t} M) (liftModule.{u,v,w,t} N)) where
  toFun z := ⟨gradedEquiv.{u,v,w,t} M N 0 z.val, by
    change (homComplex (liftModule.{u,v,w,t} M) (liftModule.{u,v,w,t} N)).d 0 1
      (gradedEquiv.{u,v,w,t} M N 0 z.val) = 0
    rw [← gradedEquiv_comm_d]
    exact (congrArg (gradedEquiv.{u,v,w,t} M N 1) z.property).trans (map_zero _)⟩
  map_add' f g := Subtype.ext ((gradedEquiv.{u,v,w,t} M N 0).map_add f.val g.val)
  map_smul' c f := Subtype.ext ((gradedEquiv.{u,v,w,t} M N 0).map_smul c f.val)

private theorem liftHomBoundaries (M N : RightDGModule A) :
    boundariesZero (homComplex M N) ≤
      (boundariesZero (homComplex (liftModule.{u,v,w,t} M) (liftModule.{u,v,w,t} N))).comap
        (liftHomCycles.{u,v,w,t} M N) := by
  intro z hz
  obtain ⟨h, rfl⟩ := hz
  refine ⟨gradedEquiv.{u,v,w,t} M N (-1) h, Subtype.ext ?_⟩
  exact (gradedEquiv_comm_d.{u,v,w,t} (-1) 0 h).symm

private def liftH0LinearMap (M N : RightDGModule A) :
    h0Hom (homComplex M N) →ₗ[k]
      h0Hom (homComplex (liftModule.{u,v,w,t} M) (liftModule.{u,v,w,t} N)) :=
  Submodule.mapQ _ _ (liftHomCycles.{u,v,w,t} M N) (liftHomBoundaries.{u,v,w,t} M N)

private theorem liftH0LinearMap_class (f : M ⟶ N) :
    liftH0LinearMap.{u,v,w,t} M N (homotopyClass f) = homotopyClass (liftMap.{u,v,w,t} f) := by
  change classOf (liftHomCycles.{u,v,w,t} M N (RightDGModule.strictCycle f)) =
    classOf (RightDGModule.strictCycle (liftMap.{u,v,w,t} f))
  exact congrArg classOf (Subtype.ext (gradedEquiv_strict f))

noncomputable section

/-- The map on Hom cohomology is the Hom map of the homotopy-category lift. -/
private theorem liftH0LinearMap_eq_map (z : h0Hom (homComplex M N)) :
    liftH0LinearMap.{u,v,w,t} M N z = (homotopyLift.{u,v,w,t} A).map z := by
  obtain ⟨f, rfl⟩ := RightDGModule.homotopyClass_surjective (M := M) (N := N) z
  exact (liftH0LinearMap_class f).trans (homotopyLift_map_class f).symm

/-- Linear equivalence on degree-zero Hom cohomology. -/
def h0LinearEquiv (M N : RightDGModule A) :
    h0Hom (homComplex M N) ≃ₗ[k]
      h0Hom (homComplex (liftModule.{u,v,w,t} M) (liftModule.{u,v,w,t} N)) :=
  LinearEquiv.ofBijective (liftH0LinearMap.{u,v,w,t} M N) (by
    change Function.Bijective (liftH0LinearMap.{u,v,w,t} M N : _ → _)
    have h : (liftH0LinearMap.{u,v,w,t} M N : _ → _) =
      (homotopyLift.{u,v,w,t} A).map (X := M) (Y := N) :=
      funext liftH0LinearMap_eq_map
    rw [h]
    exact ⟨fun _ _ he => (homotopyLiftFullyFaithful.{u,v,w,t} A).map_injective he,
      (homotopyLiftFullyFaithful.{u,v,w,t} A).map_surjective⟩)

theorem h0LinearComparison : H0LinearComparison.{u,v,w,t} :=
  fun M N => ⟨h0LinearEquiv M N, liftH0LinearMap_class⟩

end

end DerivedFormalization.DG.CoefficientLift
