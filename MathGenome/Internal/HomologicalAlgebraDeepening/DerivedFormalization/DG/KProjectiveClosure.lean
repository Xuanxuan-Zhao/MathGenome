import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.KProjective
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.ShiftCone
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.KProjectiveClosure
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainComplex.HomComplex

universe u v w j z

namespace DerivedFormalization.RightDGModule

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}
variable {M N P Q : RightDGModule A}

private theorem acyclic_iff_boundaries (C : ModuleCochain.{u,z} k) :
    C.Acyclic ↔ ∀ (r : ℤ) (x : C.X (r+1)), C.d (r+1) (r+1+1) x = 0 →
      ∃ y : C.X r, C.d r (r+1) y = x := by
  have exact_iff (r : ℤ) :
      C.ExactAt (r+1) ↔ ∀ (x : C.X (r+1)), C.d (r+1) (r+1+1) x = 0 →
        ∃ y : C.X r, C.d r (r+1) y = x := by
    rw [exactAt_iff' C r (r+1) (r+1+1) ((ComplexShape.up ℤ).prev_eq' (show
      (ComplexShape.up ℤ).Rel r (r+1) from rfl))
      ((ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel (r+1) (r+1+1) from rfl))]
    exact ShortComplex.moduleCat_exact_iff _
  constructor
  · intro h r
    exact (exact_iff r).1 (h (r+1))
  · intro h i
    obtain ⟨r, rfl⟩ : ∃ r : ℤ, r+1 = i := ⟨i-1, by omega⟩
    exact (exact_iff r).2 (h r)

private theorem d_d_apply (C : ModuleCochain.{u,z} k) (i j n : ℤ) (x : C.X i) :
    C.d j n (C.d i j x) = 0 :=
  CategoryTheory.congr_fun (C.d_comp_d i j n) x

private def shiftSource (s t r : ℤ) (e : t+s = r) :
    GradedHom M N t ≃ GradedHom (shift M s) N r where
  toFun f := ⟨fun a => (f.val a).leftShift s r e, by
    intro a b i j n ir nr h hi hn x z
    -- Use the degree reindexing of the source at both components.
    change ((f.val a).leftShift s r e).v n nr hn (M.act (i+s) j (n+s) _ x z) =
      N.act ir j nr _ (((f.val b).leftShift s r e).v i ir hi x) z
    rw [Cochain.leftShift_v _ s r e n nr hn (n+s) (by omega),
      Cochain.leftShift_v _ s r e i ir hi (i+s) (by omega)]
    simp only [CochainComplex.shiftFunctorObjXIso, XIsoOfEq, eqToIso_refl, Iso.refl_hom,
      ModuleCat.hom_smul, LinearMap.smul_apply, Units.smul_def, ModuleCat.comp_apply,
      map_zsmul]
    change (↑(s * r + s * (s - 1) / 2).negOnePow : ℤ) •
        f.app a (n+s) nr (by omega) (M.act (i+s) j (n+s) (by omega) x z) =
      (↑(s * r + s * (s - 1) / 2).negOnePow : ℤ) •
        N.act ir j nr (by omega) (f.app b (i+s) ir (by omega) x) z
    rw [f.comm_act (i+s) j (n+s) ir nr (by omega) (by omega) (by omega)]⟩
  invFun f := ⟨fun a => (f.val a).leftUnshift t e, by
    intro a b i j n ir nr h hi hn x z
    obtain ⟨i, rfl⟩ : ∃ p : ℤ, p+s = i := ⟨i-s, by omega⟩
    obtain ⟨n, rfl⟩ : ∃ p : ℤ, p+s = n := ⟨n-s, by omega⟩
    change ((f.val a).leftUnshift t e).v (n+s) nr hn ((shift M s).act i j n (by omega) x z) =
      N.act ir j nr _ (((f.val b).leftUnshift t e).v (i+s) ir hi x) z
    rw [Cochain.leftUnshift_v _ t e (n+s) nr hn n (by omega),
      Cochain.leftUnshift_v _ t e (i+s) ir hi i (by omega)]
    simp only [CochainComplex.shiftFunctorObjXIso, XIsoOfEq, eqToIso_refl, Iso.refl_inv,
      Category.id_comp, ModuleCat.hom_smul, LinearMap.smul_apply, Units.smul_def,
      map_zsmul]
    rw [f.comm_act i j n ir nr (by omega) (by omega) (by omega)]⟩
  left_inv f := Subtype.ext (funext fun a => Cochain.leftUnshift_leftShift (f.val a) s r e)
  right_inv f := Subtype.ext (funext fun a => Cochain.leftShift_leftUnshift (f.val a) t e)

private theorem shiftSource_zero (s t r : ℤ) (e : t+s = r) :
    shiftSource (M := M) (N := N) s t r e 0 = 0 :=
  Subtype.ext (funext fun _ => Cochain.leftShift_zero _ _ t s r e)

private theorem shiftSource_d (s t r : ℤ) (e : t+s = r) (f : GradedHom M N t) :
    (homComplex (shift M s) N).d r (r+1) (shiftSource s t r e f) =
      s.negOnePow • shiftSource s (t+1) (r+1) (by omega) ((homComplex M N).d t (t+1) f) :=
  Subtype.ext (funext fun a => Cochain.δ_leftShift (f.val a) s r (r+1) e (t+1) (by omega))

/-- Shifting the source of a Hom complex reindexes its cycles and their primitives. -/
theorem IsKProjective.shift (s : ℤ) (hM : M.IsKProjective) :
    IsKProjective (RightDGModule.shift M s) := by
  intro N hN
  apply (acyclic_iff_boundaries _).2
  intro r x hx
  obtain ⟨t, e⟩ : ∃ t : ℤ, t+s = r := ⟨r-s, by omega⟩
  obtain ⟨y, rfl⟩ := (shiftSource s (t+1) (r+1) (show t+1+s = r+1 by omega)).surjective x
  rw [shiftSource_d, smul_eq_zero_iff_eq, ← shiftSource_zero s (t+1+1) (r+1+1)
    (show t+1+1+s = r+1+1 by omega)] at hx
  obtain ⟨z, hz⟩ := (acyclic_iff_boundaries _).1 (hM N hN) t y
    ((shiftSource s (t+1+1) (r+1+1) (by omega)).injective hx)
  refine ⟨s.negOnePow • shiftSource s t r e z, ?_⟩
  have hd (g : GradedHom (RightDGModule.shift M s) N r) :
      (homComplex (RightDGModule.shift M s) N).d r (r+1) (s.negOnePow • g) =
        s.negOnePow • (homComplex (RightDGModule.shift M s) N).d r (r+1) g := by
    simp only [Units.smul_def, map_zsmul]
  rw [hd, shiftSource_d, hz, smul_smul, Int.units_mul_self, one_smul]

/-- Precomposition by a homogeneous right-linear map. -/
private def precomp {r : ℤ} (f : GradedHom M P 0) (g : GradedHom P N r) :
    GradedHom M N r :=
  (dgCategory A).comp r 0 r (add_zero r) g f

private theorem precomp_app {r : ℤ} (f : GradedHom M P 0) (g : GradedHom P N r)
    (a : A.Obj) (i q : ℤ) (e : i+r = q) (x : (M.complex a).X i) :
    (precomp f g).app a i q e x = g.app a i q e (f.app a i i (add_zero i) x) := by
  rw [precomp, compositionFormula r 0 r (add_zero r) _ _ a i i q (add_zero i) e]

private def restrict (f : M ⟶ P) {r : ℤ} (g : GradedHom P N r) : GradedHom M N r :=
  precomp (strictCycle f).val g

@[simp] private theorem restrict_zero (f : M ⟶ P) (r : ℤ) :
    restrict (N := N) f (0 : GradedHom P N r) = 0 := by
  unfold restrict precomp
  rw [map_zero, LinearMap.zero_apply]

@[simp] private theorem restrict_sub (f : M ⟶ P) {r : ℤ} (g h : GradedHom P N r) :
    restrict f (g - h) = restrict f g - restrict f h := by
  unfold restrict precomp
  rw [map_sub, LinearMap.sub_apply]

private theorem restrict_d (f : M ⟶ P) (r : ℤ) (g : GradedHom P N r) :
    restrict f ((homComplex P N).d r (r+1) g) =
      (homComplex M N).d r (r+1) (restrict f g) := by
  have h := (dgCategory A).toData.leibniz r 0 r (add_zero r) g (strictCycle f).val
  have hf : ((dgCategory A).toData.hom M P).d 0 (0+1) (strictCycle f).val = 0 :=
    (strictCycle f).property
  rw [hf] at h
  simpa only [restrict, precomp, map_zero, smul_zero, add_zero] using h.symm

private theorem restrict_app (f : M ⟶ P) {r : ℤ} (g : GradedHom P N r)
    (a : A.Obj) (i q : ℤ) (e : i+r = q) (x : (M.complex a).X i) :
    (restrict f g).app a i q e x = g.app a i q e ((f.app a).f i x) := by
  rw [restrict, precomp_app]
  change g.app a i q e ((Cochain.ofHom (f.app a)).v i i (add_zero i) x) = _
  rw [Cochain.ofHom_v]

private theorem gradedHom_ext_apply {r : ℤ} {f g : GradedHom M N r}
    (h : ∀ (a : A.Obj) (i q : ℤ) (e : i+r = q) (x : (M.complex a).X i),
      f.app a i q e x = g.app a i q e x) : f = g :=
  GradedHom.ext fun a i q e => ModuleCat.hom_ext (LinearMap.ext (h a i q e))

private theorem restrict_coneProjection_injective (f : P ⟶ Q) (r : ℤ) :
    Function.Injective (restrict (N := N) (coneProjection f) (r := r)) := by
  intro g h he
  apply gradedHom_ext_apply
  intro a i q e x
  have h' := congrArg (fun t : GradedHom (cone f) N r => t.app a i q e (0, x)) he
  change (restrict (coneProjection f) g).app a i q e (0, x) =
    (restrict (coneProjection f) h).app a i q e (0, x) at h'
  rw [restrict_app, restrict_app, coneProjection_f] at h'
  exact h'

private theorem restrict_coneInclusion_retraction (f : P ⟶ Q) {r : ℤ}
    (g : GradedHom Q N r) :
    restrict (coneInclusion f) (precomp (coneGradedRetraction f) g) = g := by
  apply gradedHom_ext_apply
  intro o i q e x
  rw [restrict_app, precomp_app, coneInclusion_f]
  rfl

private theorem restrict_coneProjection_section (f : P ⟶ Q) {r : ℤ}
    (g : GradedHom (cone f) N r) (hg : restrict (coneInclusion f) g = 0) :
    restrict (coneProjection f) (precomp (coneGradedSection f) g) = g := by
  apply gradedHom_ext_apply
  intro o i q e p
  rw [restrict_app, precomp_app, coneProjection_f]
  change g.app o i q e (0, p.2) = g.app o i q e p
  have hzero : g.app o i q e (p.1, 0) = 0 := by
    have h := congrArg (fun t : GradedHom Q N r => t.app o i q e p.1) hg
    change (restrict (coneInclusion f) g).app o i q e p.1 =
      (0 : GradedHom Q N r).app o i q e p.1 at h
    rw [restrict_app, coneInclusion_f] at h
    change g.app o i q e (p.1, 0) =
      (0 : Cochain (Q.complex o) (N.complex o) r).v i q e p.1 at h
    rw [Cochain.zero_v] at h
    exact h
  have hsum : ((p.1, 0) : ((cone f).complex o).X i) + (0, p.2) = p :=
    Prod.ext (add_zero _) (zero_add _)
  calc
    g.app o i q e (0, p.2) =
        g.app o i q e (((p.1, 0) : ((cone f).complex o).X i) + (0, p.2)) := by
      rw [map_add, hzero, zero_add]
    _ = g.app o i q e p := congrArg (fun x => g.app o i q e x) hsum

/-- The cone of a closed map between K-projective modules is K-projective. -/
theorem IsKProjective.cone (f : P ⟶ Q) (hP : P.IsKProjective) (hQ : Q.IsKProjective) :
    IsKProjective (RightDGModule.cone f) := by
  intro N hN
  let C := homComplex (RightDGModule.cone f) N
  apply (acyclic_iff_boundaries C).2
  intro r z hz
  let ι : Q ⟶ RightDGModule.cone f := coneInclusion f
  let π : RightDGModule.cone f ⟶ RightDGModule.shift P 1 := coneProjection f
  have hzι : (homComplex Q N).d (r+1) (r+1+1) (restrict ι z) = 0 := by
    rw [← restrict_d, hz, restrict_zero]
  obtain ⟨a, ha⟩ := (acyclic_iff_boundaries (homComplex Q N)).1 (hQ N hN) r _ hzι
  let b : GradedHom (RightDGModule.cone f) N r := precomp (coneGradedRetraction f) a
  have hb : restrict ι b = a := restrict_coneInclusion_retraction f a
  let y : GradedHom (RightDGModule.cone f) N (r+1) := z - C.d r (r+1) b
  have hdd : C.d (r+1) (r+1+1) (C.d r (r+1) b) = 0 :=
    d_d_apply C r (r+1) (r+1+1) b
  have hy : C.d (r+1) (r+1+1) y = 0 := by
    change C.d (r+1) (r+1+1) (z - C.d r (r+1) b) = 0
    rw [map_sub, hz, hdd, sub_zero]
  have hι : restrict ι y = 0 := by
    change restrict ι (z - C.d r (r+1) b) = 0
    rw [restrict_sub, restrict_d, hb, ha, sub_self]
  let c : GradedHom (RightDGModule.shift P 1) N (r+1) := precomp (coneGradedSection f) y
  have hc : restrict π c = y := restrict_coneProjection_section f y hι
  have hc_cycle : (homComplex (RightDGModule.shift P 1) N).d (r+1) (r+1+1) c = 0 := by
    apply restrict_coneProjection_injective f (r+1+1)
    change restrict π ((homComplex (RightDGModule.shift P 1) N).d (r+1) (r+1+1) c) =
      restrict π 0
    rw [restrict_zero, restrict_d, hc, hy]
  obtain ⟨d, hd⟩ := (acyclic_iff_boundaries (homComplex (RightDGModule.shift P 1) N)).1
    (hP.shift 1 N hN) r c hc_cycle
  refine ⟨b + restrict π d, ?_⟩
  change C.d r (r+1) (b + restrict π d) = z
  rw [map_add, ← restrict_d, hd, hc]
  change C.d r (r+1) b + (z - C.d r (r+1) b) = z
  rw [add_comm (C.d r (r+1) b), sub_add_cancel]

/-- A degree-zero graded map into the target determines a strict map into
the cone of the target identity. The second component is its negative Hom differential. -/
private def toIdentityCone (g : GradedHom M N 0) : M ⟶ cone (𝟙 N) := by
  let dg : GradedHom M N 1 := (homComplex M N).d 0 1 g
  let component (a : A.Obj) (i : ℤ) :
      (M.complex a).X i ⟶ ((cone (𝟙 N)).complex a).X i :=
    ModuleCat.ofHom ((g.app a i i (add_zero i)).hom.prod (-(dg.app a i (i+1) rfl).hom))
  refine ⟨fun a => CochainComplex.ofHom (component a) ?_, ?_⟩
  · intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    symm
    change (g.app a (i+1) (i+1) (add_zero _) ((M.complex a).d i (i+1) x),
      -dg.app a (i+1) (i+1+1) rfl ((M.complex a).d i (i+1) x)) =
      ((cone (𝟙 N)).complex a).d i (i+1)
        (g.app a i i (add_zero i) x, -dg.app a i (i+1) rfl x)
    rw [cone_d]
    apply Prod.ext
    · have h := CategoryTheory.congr_fun (δ_zero_cochain_v (g.val a) i (i+1) rfl) x
      change dg.app a i (i+1) rfl x =
        (N.complex a).d i (i+1) (g.app a i i (add_zero i) x) -
          g.app a (i+1) (i+1) (add_zero _) ((M.complex a).d i (i+1) x) at h
      change _ = (N.complex a).d i (i+1) (g.app a i i (add_zero i) x) +
        -dg.app a i (i+1) rfl x
      rw [← sub_eq_add_neg, h, sub_sub_cancel]
    · have h := differentialFormula 1 dg a i (i+1+1) (by omega) x
      have hz := d_d_apply (homComplex M N) 0 1 (1+1) g
      rw [show (homComplex M N).d 1 (1+1) dg = 0 from hz] at h
      change (0 : (N.complex a).X (i+1+1)) = _ at h
      simp only [Int.negOnePow_one, Units.neg_smul, one_smul, sub_neg_eq_add] at h
      change -dg.app a (i+1) (i+1+1) rfl ((M.complex a).d i (i+1) x) =
        -(N.complex a).d (i+1) (i+1+1) (-dg.app a i (i+1) rfl x)
      rw [map_neg, neg_neg]
      exact (eq_neg_of_add_eq_zero_left h.symm).symm
  · intro a b i j n h x z
    change (g.app a n n (add_zero n) (M.act i j n h x z),
      -dg.app a n (n+1) rfl (M.act i j n h x z)) =
      (cone (𝟙 N)).act i j n h (g.app b i i (add_zero i) x, -dg.app b i (i+1) rfl x) z
    rw [cone_act]
    apply Prod.ext
    · exact g.comm_act i j n i n h (add_zero i) (add_zero n) x z
    · change -dg.app a n (n+1) rfl (M.act i j n h x z) =
        N.act (i+1) j (n+1) (by omega) (-dg.app b i (i+1) rfl x) z
      rw [dg.comm_act i j n (i+1) (n+1) h rfl rfl, map_neg, LinearMap.neg_apply]

private theorem identityCone_hom_ext {f g : M ⟶ cone (𝟙 N)}
    (h : ∀ (a : A.Obj) (i : ℤ) (x : (M.complex a).X i),
      ((f.app a).f i x).1 = ((g.app a).f i x).1) : f = g := by
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Prod.ext (h a i x)
  have component (f : M ⟶ cone (𝟙 N)) :
      ((f.app a).f (i+1) ((M.complex a).d i (i+1) x)).1 =
        (N.complex a).d i (i+1) ((f.app a).f i x).1 + ((f.app a).f i x).2 := by
    have e := CategoryTheory.congr_fun ((f.app a).comm i (i+1)) x
    symm at e
    change (f.app a).f (i+1) ((M.complex a).d i (i+1) x) =
      ((cone (𝟙 N)).complex a).d i (i+1) ((f.app a).f i x) at e
    rw [cone_d] at e
    exact congrArg Prod.fst e
  have e := (component f).symm.trans ((h a (i+1) _).trans (component g))
  rw [h a i x, add_right_inj] at e
  exact e

/-- Take the first component of a strict map into the cone of the identity
on the shifted target, and express it in its original degree. -/
private def fromShiftedIdentityCone (r : ℤ) (f : M ⟶ cone (𝟙 (shift N r))) :
    GradedHom M N r :=
  GradedHom.mk (fun a i q h => by
    subst q
    exact (f.app a).f i ≫ ModuleCat.ofHom (LinearMap.fst _ _ _)) (by
      intro a b i j n ir nr h hi hn x z
      subst ir nr
      have e := f.comm_act i j n h x z
      rw [cone_act] at e
      exact congrArg Prod.fst e)

private theorem fromShiftedIdentityCone_app (r : ℤ) (f : M ⟶ cone (𝟙 (shift N r)))
    (a : A.Obj) (i : ℤ) (x : (M.complex a).X i) :
    (fromShiftedIdentityCone r f).app a i (i+r) rfl x = ((f.app a).f i x).1 := rfl

private theorem fromShiftedIdentityCone_injective (r : ℤ) :
    Function.Injective (fromShiftedIdentityCone (M := M) (N := N) r) := by
  intro f g h
  apply identityCone_hom_ext
  intro a i x
  exact congrArg (fun t : GradedHom M N r => t.app a i (i+r) rfl x) h

private theorem fromShiftedIdentityCone_surjective (r : ℤ) :
    Function.Surjective (fromShiftedIdentityCone (M := M) (N := N) r) := by
  intro g
  let g₀ : GradedHom M (shift N r) 0 :=
    GradedHom.mk (fun a i q h => by
      obtain rfl : i = q := by omega
      exact g.app a i (i+r) rfl) (by
      intro a b i j n ir nr h hi hn x z
      obtain rfl : i = ir := by omega
      obtain rfl : n = nr := by omega
      exact g.comm_act i j n (i+r) (n+r) h rfl rfl x z)
  refine ⟨toIdentityCone g₀, gradedHom_ext_apply ?_⟩
  intro a i q h x
  subst q
  rw [fromShiftedIdentityCone_app]
  rfl

private theorem fromShiftedIdentityCone_comp (r : ℤ) (f : M ⟶ P)
    (g : P ⟶ cone (𝟙 (shift N r))) :
    fromShiftedIdentityCone r (f ≫ g) = restrict f (fromShiftedIdentityCone r g) := by
  apply gradedHom_ext_apply
  intro a i q h x
  subst q
  rw [restrict_app, fromShiftedIdentityCone_app, fromShiftedIdentityCone_app]
  rfl

section Coproduct

variable {I : Type j} {F : I → RightDGModule A} {c : Cofan F}

/-- A strict coproduct has the product universal property on homogeneous maps
in every degree. -/
private theorem gradedHom_coproduct_bijective (hc : IsColimit c) (r : ℤ) :
    Function.Bijective (fun g : GradedHom c.pt N r => fun l => restrict (c.inj l) g) := by
  constructor
  · intro g h he
    obtain ⟨f, rfl⟩ := fromShiftedIdentityCone_surjective r g
    obtain ⟨f', rfl⟩ := fromShiftedIdentityCone_surjective r h
    congr 1
    apply Cofan.IsColimit.hom_ext hc
    intro l
    apply fromShiftedIdentityCone_injective (N := N) r
    rw [fromShiftedIdentityCone_comp, fromShiftedIdentityCone_comp]
    exact congrFun he l
  · intro g
    choose f hf using fun l => fromShiftedIdentityCone_surjective r (g l)
    refine ⟨fromShiftedIdentityCone r (Cofan.IsColimit.desc hc f), funext fun l => ?_⟩
    change restrict (c.inj l) (fromShiftedIdentityCone r (Cofan.IsColimit.desc hc f)) = g l
    rw [← fromShiftedIdentityCone_comp, Cofan.IsColimit.fac, hf l]

/-- Every existing strict coproduct of K-projective modules is K-projective. -/
theorem IsKProjective.coproduct (c : Cofan F) (hc : IsColimit c)
    (hF : ∀ l, (F l).IsKProjective) : IsKProjective c.pt := by
  classical
  intro N hN
  apply (acyclic_iff_boundaries _).2
  intro r z hz
  have cycles (l : I) : (homComplex (F l) N).d (r+1) (r+1+1) (restrict (c.inj l) z) = 0 := by
    rw [← restrict_d, hz, restrict_zero]
  choose g hg using fun l => (acyclic_iff_boundaries _).1 (hF l N hN) r _ (cycles l)
  obtain ⟨b, hb⟩ := (gradedHom_coproduct_bijective hc r).surjective g
  refine ⟨b, (gradedHom_coproduct_bijective hc (r+1)).injective (funext fun l => ?_)⟩
  change restrict (c.inj l) ((homComplex c.pt N).d r (r+1) b) = restrict (c.inj l) z
  have hbl : restrict (c.inj l) b = g l := congrFun hb l
  rw [restrict_d, hbl, hg l]

end Coproduct

end DerivedFormalization.RightDGModule
