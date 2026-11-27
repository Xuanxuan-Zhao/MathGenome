import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.HomComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.Yoneda

open CategoryTheory CochainComplex.HomComplex

universe u v w

namespace DerivedFormalization
namespace RightDGModule

open Specs.DerivedFormalization.DG.Yoneda (liftComplex liftCategory EvaluationLaws)

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}

/-- The module `h_a` represented by `a`. -/
abbrev representable (a : A.Obj) : RightDGModule A :=
  Specs.DerivedFormalization.DG.Yoneda.representable a

variable (a : A.Obj) (M : RightDGModule A)

/-- The homogeneous module map associated to an element of `M(a)`. -/
def yonedaExtend (r : ℤ) (m : (M.complex a).X r) : GradedHom (representable a) M r :=
  GradedHom.mk (fun _ j n h => ModuleCat.ofHom (M.act r j n (by omega) m)) (by
    intro b c i j n ir nr h hi hn x z
    have hir : r+i = ir := by omega
    have hnr : r+i+j = nr := by omega
    subst h hir hnr
    exact (M.act_assoc r i j m x z).symm)

@[simp] theorem yonedaExtend_app (r : ℤ) (m : (M.complex a).X r)
    (b : A.Obj) (j n : ℤ) (h : j+r = n) (x : (A.hom b a).X j) :
    (yonedaExtend a M r m).app b j n h x = M.act r j n (by omega) m x := rfl

/-- Every homogeneous map out of a representable is determined by the identity. -/
theorem yoneda_apply (r : ℤ) (f : GradedHom (representable a) M r)
    (b : A.Obj) (j n : ℤ) (h : j+r = n) (x : (A.hom b a).X j) :
    f.app b j n h x = M.act r j n (by omega) (f.app a 0 r (zero_add r) (A.id a)) x := by
  have e := f.comm_act 0 j j r n (zero_add j) (zero_add r) h (A.id a) x
  change f.app b j n h (A.comp 0 j j (zero_add j) (A.id a) x) = _ at e
  rw [A.toData.id_comp] at e
  exact e

/-- Evaluation at the identity in each degree, in the original module universes. -/
def yonedaEquiv (r : ℤ) :
    GradedHom (representable a) M r ≃ₗ[k] (M.complex a).X r where
  toFun f := f.app a 0 r (zero_add r) (A.id a)
  invFun m := yonedaExtend a M r m
  left_inv f := by
    apply GradedHom.ext
    intro b j n h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (yoneda_apply a M r f b j n h x).symm
  right_inv m := M.act_id a r m
  map_add' f g := by
    change (f.val a + g.val a).v 0 r (zero_add r) (A.id a) = _
    simp only [Cochain.add_v, ModuleCat.hom_add, LinearMap.add_apply]
  map_smul' c f := by
    change (c • f.val a).v 0 r (zero_add r) (A.id a) = _
    simp only [Cochain.smul_v, ModuleCat.hom_smul, LinearMap.smul_apply]
    rfl

/-- The degreewise evaluation equivalences commute with the differentials. -/
theorem yonedaEquiv_comm_d (r : ℤ) (f : GradedHom (representable a) M r) :
    yonedaEquiv a M (r+1) ((homComplex (representable a) M).d r (r+1) f) =
      (M.complex a).d r (r+1) (yonedaEquiv a M r f) := by
  change GradedHom.app ((homComplex (representable a) M).d r (r+1) f)
      a 0 (r+1) (zero_add (r+1)) (A.id a) =
    (M.complex a).d r (r+1) (f.app a 0 r (zero_add r) (A.id a))
  rw [differentialFormula]
  change (M.complex a).d (0+r) (r+1) (f.app a 0 (0+r) rfl (A.id a)) -
    r.negOnePow • f.app a (0+1) (r+1) (by omega) ((A.hom a a).d 0 1 (A.id a)) = _
  rw [A.toData.d_id, map_zero, smul_zero, sub_zero]
  suffices ∀ (q : ℤ) (hq : 0+r = q), q = r →
      (M.complex a).d q (r+1) (f.app a 0 q hq (A.id a)) =
        (M.complex a).d r (r+1) (f.app a 0 r (zero_add r) (A.id a)) from
    this (0+r) rfl (zero_add r)
  intro q hq e
  subst e
  rfl

/-- Enriched Yoneda evaluation at the closed identity of `a`. -/
def yonedaIso : homComplex (representable a) M ≅ liftComplex.{u,v,w} (M.complex a) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun r => ((yonedaEquiv a M r).trans ULift.moduleEquiv.symm).toModuleIso) (by
    intro r s h
    have e : r+1 = s := h
    subst s
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact ULift.ext (yonedaEquiv_comm_d a M r f).symm)

@[simp] theorem yonedaIso_hom_apply (r : ℤ) (f : GradedHom (representable a) M r) :
    ((yonedaIso a M).hom.f r f).down = f.app a 0 r (zero_add r) (A.id a) := rfl

@[simp] theorem yonedaIso_inv_apply (r : ℤ) (m : (M.complex a).X r) :
    (yonedaIso a M).inv.f r (ULift.up m) = yonedaExtend a M r m := rfl

/-- Evaluation commutes with postcomposition by every homogeneous module map. -/
theorem yoneda_natural_module {N : RightDGModule A} (s r n : ℤ) (h : s+r = n)
    (g : GradedHom M N s) (f : GradedHom (representable a) M r) :
    ((yonedaIso a N).hom.f n ((dgCategory A).comp s r n h g f)).down =
      g.app a r n (by omega) (((yonedaIso a M).hom.f r f).down) :=
  compositionFormula s r n h g f a 0 r n (zero_add r) (by omega) (A.id a)

/-- Precomposition by the map represented by `x` corresponds to the right action of `x`. -/
theorem yoneda_natural_object (b : A.Obj) (s r n : ℤ) (h : s+r = n)
    (f : GradedHom (representable b) M s) (x : (A.hom a b).X r) :
    ((yonedaIso a M).hom.f n ((dgCategory A).comp s r n h f
      ((yonedaIso a (representable b)).inv.f r (ULift.up x)))).down =
        M.act s r n h (((yonedaIso b M).hom.f s f).down) x := by
  rw [yoneda_natural_module, yonedaIso_inv_apply, yonedaIso_hom_apply, yonedaExtend_app]
  change f.app a r n (by omega) (A.comp r 0 r (add_zero r) x (A.id a)) = _
  rw [A.toData.comp_id]
  exact yoneda_apply b M s f a r n (by omega) x

private theorem yonedaIso_laws : EvaluationLaws (yonedaIso (A := A)) where
  evaluation := yonedaIso_hom_apply
  inverse a M r j n _ m b x := yonedaExtend_app a M r m b j n _ x
  natural_module a M _ := yoneda_natural_module a M
  natural_object a b M := yoneda_natural_object a M b

/-- Evaluation at the identity gives the enriched Yoneda isomorphism, naturally. -/
theorem enrichedYoneda : Specs.DerivedFormalization.DG.Yoneda.EnrichedYoneda.{u,v,w} :=
  fun {_} _ {_} => ⟨yonedaIso, yonedaIso_laws⟩

/-- The Yoneda dg functor, with the source realized in the common Hom universe. -/
def yoneda (A : DGCategory.{u,v,w} k) : DGFunctor (liftCategory A) (dgCategory A) where
  obj a := representable (A := A) a
  map a b := (yonedaIso (A := A) a (representable (A := A) b)).inv
  map_id a := by
    change yonedaExtend (A := A) a (representable a) 0 (A.id a) =
      (dgCategory A).id (representable (A := A) a)
    apply GradedHom.ext
    intro b j n e
    rw [add_zero] at e
    subst e
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change A.comp 0 j j (zero_add j) (A.id a) x =
      (Cochain.ofHom (𝟙 (A.hom b a))).v j j (add_zero j) x
    rw [A.toData.id_comp, Cochain.ofHom_v]
    rfl
  map_comp := by
    intro a b c i j n h f g
    change yonedaExtend (A := A) a (representable c) n (A.comp i j n h f.down g.down) =
      (dgCategory A).comp i j n h
        (yonedaExtend (A := A) b (representable c) i f.down)
        (yonedaExtend (A := A) a (representable b) j g.down)
    apply GradedHom.ext
    intro d l q e
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [compositionFormula i j n h _ _ d l (j+l) q (by omega) (by omega)]
    subst h
    have eq : i+j+l = q := by omega
    subst eq
    exact A.toData.assoc i j l f.down g.down x

/-- On a homogeneous arrow, the Yoneda functor acts by postcomposition. -/
@[simp] theorem yoneda_map_apply (a b c : A.Obj) (r j n : ℤ) (h : r+j = n)
    (f : (A.hom a b).X r) (g : (A.hom c a).X j) :
    GradedHom.app (((yoneda A).map a b).f r (ULift.up f)) c j n (by omega) g =
      A.comp r j n h f g := rfl

instance yoneda_map_isIso (a b : A.Obj) : IsIso ((yoneda A).map a b) :=
  (yonedaIso (A := A) a (representable (A := A) b)).isIso_inv

/-- The Yoneda dg functor is fully faithful, with postcomposition on morphisms. -/
theorem fullyFaithfulYoneda : Specs.DerivedFormalization.DG.Yoneda.FullyFaithfulYoneda.{u,v,w} := by
  intro k _ A
  exact ⟨yonedaIso, yonedaIso_laws, yoneda A, rfl, fun _ _ => HEq.rfl,
    fun a b => yoneda_map_isIso (A := A) a b⟩

end RightDGModule
end DerivedFormalization
