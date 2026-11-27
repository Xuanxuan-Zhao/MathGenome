import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.ShiftCone

open CategoryTheory CategoryTheory.Limits

universe u v w

set_option linter.checkUnivs false

namespace Specs.DerivedFormalization.DG.Telescope

open _root_.DerivedFormalization
open ShiftCone (cone coneDiff coneDiff_succ coneTerm)
open HomComplex (gradedHom HomotopyEquation component)

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
variable {M N P : RightDGModuleModel A}

/-- The objectwise difference of two strict maps. -/
def subMap (f g : M ⟶ N) : M ⟶ N where
  app a := f.app a - g.app a
  comm_act := by
    intro a b i j n h x z
    change (f.app a).f n (M.act i j n h x z) - (g.app a).f n (M.act i j n h x z) =
      N.act i j n h ((f.app b).f i x - (g.app b).f i x) z
    rw [f.comm_act, g.comm_act, map_sub, LinearMap.sub_apply]

variable {X : ℕ → RightDGModuleModel A} (step : ∀ j, X j ⟶ X (j+1))

/-- On a coproduct of the sequence, the successor takes each summand to the next. -/
def successor {U : Cofan X} (hU : IsColimit U) : U.pt ⟶ U.pt :=
  hU.desc (Cofan.mk U.pt fun j => step j ≫ U.inj (j+1))

/-- The map defining the telescope. -/
def oneSubSuccessor {U : Cofan X} (hU : IsColimit U) : U.pt ⟶ U.pt :=
  subMap (𝟙 _) (successor step hU)

/-- The canonical map from the coproduct to a cocone of the sequence. -/
def sumToSequence {U : Cofan X} (hU : IsColimit U)
    (L : Cocone (Functor.ofSequence step)) : U.pt ⟶ L.pt :=
  hU.desc (Cofan.mk L.pt fun j => L.ι.app j)

theorem subMap_comp (f g : M ⟶ N) (p : N ⟶ P) :
    subMap f g ≫ p = subMap (f ≫ p) (g ≫ p) := by
  apply RightDGModuleModel.hom_ext
  intro a
  exact Preadditive.sub_comp _ _ _

theorem comp_subMap (p : M ⟶ N) (f g : N ⟶ P) :
    p ≫ subMap f g = subMap (p ≫ f) (p ≫ g) := by
  apply RightDGModuleModel.hom_ext
  intro a
  exact Preadditive.comp_sub _ _ _

theorem subMap_self (f : M ⟶ N) : subMap f f = 0 :=
  RightDGModuleModel.hom_ext fun a => sub_self (f.app a)

theorem subMap_eq_zero_iff (f g : M ⟶ N) : subMap f g = 0 ↔ f = g := by
  constructor
  · intro h
    apply RightDGModuleModel.hom_ext
    intro a
    exact sub_eq_zero.mp (congrArg (fun q : M ⟶ N => q.app a) h)
  · rintro rfl
    exact subMap_self f

@[reassoc] theorem inj_successor {U : Cofan X} (hU : IsColimit U) (j : ℕ) :
    U.inj j ≫ successor step hU = step j ≫ U.inj (j+1) :=
  hU.fac _ ⟨j⟩

@[reassoc] theorem inj_sumToSequence {U : Cofan X} (hU : IsColimit U)
    (L : Cocone (Functor.ofSequence step)) (j : ℕ) :
    U.inj j ≫ sumToSequence step hU L = L.ι.app j :=
  hU.fac _ ⟨j⟩

theorem oneSubSuccessor_sumToSequence {U : Cofan X} (hU : IsColimit U)
    (L : Cocone (Functor.ofSequence step)) :
    oneSubSuccessor step hU ≫ sumToSequence step hU L = 0 := by
  apply hU.hom_ext
  rintro ⟨j⟩
  change U.inj j ≫ subMap (𝟙 _) (successor step hU) ≫ sumToSequence step hU L = _
  rw [← Category.assoc, comp_subMap, subMap_comp, Category.comp_id, inj_successor,
    inj_sumToSequence, Category.assoc, inj_sumToSequence, comp_zero]
  apply (subMap_eq_zero_iff _ _).2
  have hw := L.w (homOfLE (j.le_add_right 1))
  rw [Functor.ofSequence_map_homOfLE_succ] at hw
  exact hw.symm

/-- The map induced from a cone by a strict map annihilating its source. -/
def coneComparison (f : M ⟶ N) (p : N ⟶ P) (hp : f ≫ p = 0) : cone f ⟶ P where
  app a := CochainComplex.ofHom
    (fun i => ModuleCat.ofHom (((p.app a).f i).hom.comp (LinearMap.fst _ _ _))) (by
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    symm
    change (p.app a).f (i+1) (coneDiff f a i (i+1) q).1 =
      (P.complex a).d i (i+1) ((p.app a).f i q.1)
    have hf := congrArg (fun g : M ⟶ P => (g.app a).f (i+1) q.2) hp
    change (p.app a).f (i+1) ((f.app a).f (i+1) q.2) = 0 at hf
    have hc := CategoryTheory.congr_fun ((p.app a).comm i (i+1)) q.1
    rw [coneDiff_succ, map_add, hf, add_zero]
    exact hc.symm)
  comm_act := by
    intro a b i j n h q z
    exact p.comm_act i j n h q.1 z

/-- The strict map from the identity cone into the cone of a map, given by (y,x) ↦ (f y,x). -/
def coneKernelInclusion (f : M ⟶ N) : cone (𝟙 M) ⟶ cone f where
  app a := CochainComplex.ofHom
    (fun i => ModuleCat.ofHom ((((f.app a).f i).hom.comp (LinearMap.fst _ _ _)).prod
      (LinearMap.snd _ _ _))) (by
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    symm
    change ((f.app a).f (i+1) (coneDiff (𝟙 M) a i (i+1) q).1,
        (coneDiff (𝟙 M) a i (i+1) q).2) =
      coneDiff f a i (i+1) ((f.app a).f i q.1, q.2)
    rw [coneDiff_succ, coneDiff_succ]
    apply Prod.ext
    · change (f.app a).f (i+1) ((M.complex a).d i (i+1) q.1 + q.2) = _
      rw [map_add]
      congr 1
      exact (CategoryTheory.congr_fun ((f.app a).comm i (i+1)) q.1).symm
    · rfl)
  comm_act := by
    intro a b i j n h q z
    exact Prod.ext (f.comm_act i j n h q.1 z) rfl

theorem coneKernelInclusion_comp (f : M ⟶ N) (p : N ⟶ P) (hp : f ≫ p = 0) :
    coneKernelInclusion f ≫ coneComparison f p hp = 0 := by
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  exact congrArg (fun g : M ⟶ P => (g.app a).f i q.1) hp

/-- The canonical telescope map restricts to the colimit cocone on the target summand. -/
def telescopeComparison {U : Cofan X} (hU : IsColimit U)
    (L : Cocone (Functor.ofSequence step)) : cone (oneSubSuccessor step hU) ⟶ L.pt :=
  coneComparison _ (sumToSequence step hU L) (oneSubSuccessor_sumToSequence step hU L)

def SuccessorType := ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {X : ℕ → RightDGModuleModel A}, (∀ j, X j ⟶ X (j+1)) →
    ∀ {U : Cofan X}, IsColimit U → (U.pt ⟶ U.pt)

def SumToSequenceType := ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {X : ℕ → RightDGModuleModel A} (step : ∀ j, X j ⟶ X (j+1))
    {U : Cofan X}, IsColimit U → (L : Cocone (Functor.ofSequence step)) → (U.pt ⟶ L.pt)

def ConeComparisonType := ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N P : RightDGModuleModel A} (f : M ⟶ N) (p : N ⟶ P),
    f ≫ p = 0 → (cone f ⟶ P)

def ConeKernelInclusionType := ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N : RightDGModuleModel A} (f : M ⟶ N), cone (𝟙 M) ⟶ cone f

def TelescopeComparisonType := ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {X : ℕ → RightDGModuleModel A} (step : ∀ j, X j ⟶ X (j+1))
    {U : Cofan X} (hU : IsColimit U) (L : Cocone (Functor.ofSequence step)),
    cone (oneSubSuccessor step hU) ⟶ L.pt

def OneSubSuccessorInjective : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {X : ℕ → RightDGModuleModel A} (step : ∀ j, X j ⟶ X (j+1))
    {U : Cofan X} (hU : IsColimit U) (a : A.Obj) (i : ℤ),
    Function.Injective (((oneSubSuccessor step hU).app a).f i)

def SequenceIsCokernel : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {X : ℕ → RightDGModuleModel A} (step : ∀ j, X j ⟶ X (j+1))
    {U : Cofan X} (hU : IsColimit U) {L : Cocone (Functor.ofSequence step)}
    (_hL : IsColimit L),
    Nonempty (IsColimit (CokernelCofork.ofπ (sumToSequence step hU L)
      (oneSubSuccessor_sumToSequence step hU L)))

def IdentityConeContractible : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    (M : RightDGModuleModel A),
    ∃ h : gradedHom (cone (𝟙 M)) (cone (𝟙 M)) (-1),
      HomotopyEquation (𝟙 (cone (𝟙 M))) (0 : cone (𝟙 M) ⟶ cone (𝟙 M)) h ∧
        ∀ (a : A.Obj) (i : ℤ) (q : coneTerm M M a (i+1)),
          component h a (i+1) i (by omega) q = (0, q.1)

def ConeToCokernel : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N P : RightDGModuleModel A} (f : M ⟶ N)
    (_hf : ∀ a i, Function.Injective ((f.app a).f i))
    (p : N ⟶ P) (hp : f ≫ p = 0) (_hc : IsColimit (CokernelCofork.ofπ p hp)),
    Nonempty (IsLimit (KernelFork.ofι (coneKernelInclusion f) (coneKernelInclusion_comp f p hp))) ∧
      Module.quasiIsomorphism (coneComparison f p hp)

def TelescopeQuasiIso : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {X : ℕ → RightDGModuleModel A} (step : ∀ j, X j ⟶ X (j+1))
    {U : Cofan X} (hU : IsColimit U) {L : Cocone (Functor.ofSequence step)}
    (_hL : IsColimit L),
    Module.quasiIsomorphism (telescopeComparison step hU L)

end Specs.DerivedFormalization.DG.Telescope
