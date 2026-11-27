import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CoefficientLiftComparison
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.IndexedSums
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.IndexedCellAttachment
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v w j t

namespace DerivedFormalization.DG.IndexedCellAttachment

open Specs.DerivedFormalization.DG.IndexedCellAttachment
open Specs.DerivedFormalization.DG.IndexedSemiFree
open Specs.DerivedFormalization.DG

open private term_hom_ext from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.IndexedSums
open private rawStep rawAct from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.IndexedSums
open private act_id_reindexed from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.SemiFree
open private liftTerm_summand from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.IndexedSums

noncomputable section

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
variable {I : Type j} {P Q R : RightDGModuleModel A}
variable {C : CellFamily P I}

/-- Transport cell data to the larger coefficient universe. -/
abbrev liftFamily := @Specs.DerivedFormalization.DG.IndexedCellAttachment.liftFamily.{u,v,w,j,t}

theorem differentialSquaresToZero : DifferentialSquaresToZero.{u,v,w,j} := by
  intro k _ A P Q I C E a n x
  rw [← ModuleCat.comp_apply, d_comp_d]
  rfl

/-- The original small-index construction has the defining arbitrary-index coordinates. -/
def nativeAttachment {J : Type v} (B : SemiFree.CellFamily P J) :
    Attachment (⟨B.object, B.degree, B.boundary, B.closed⟩ : CellFamily P J) (SemiFree.attach B) where
  inclusion := SemiFree.inclusion B
  coordinates _ _ := LinearEquiv.refl k _
  coordinate_inclusion _ _ _ := rfl
  coordinate_d a n x := by
    change (((SemiFree.attach B).complex a).d n (n+1) x).1 = _ ∧ _
    rw [SemiFree.attachComplex_d]
    exact ⟨rfl, fun i => SemiFree.directSum_d (SemiFree.cells B) a n x.2 i⟩
  coordinate_act _ _ _ _ _ _ := ⟨rfl, fun _ => rfl⟩

theorem nativeComparison : NativeComparison.{u,v,w} := by
  intro k _ A P I C
  exact ⟨nativeAttachment C, rfl, fun _ _ _ => rfl, fun _ => rfl⟩

variable (E : Attachment C Q) (D : Attachment C R)

private def comparisonDegree (a : A.Obj) (n : ℤ) :
    (Q.complex a).X n ≃ₗ[k] (R.complex a).X n :=
  (E.coordinates a n).trans (D.coordinates a n).symm

@[simp] private theorem comparisonDegree_coordinates (a : A.Obj) (n : ℤ)
    (x : (Q.complex a).X n) :
    D.coordinates a n (comparisonDegree E D a n x) = E.coordinates a n x :=
  (D.coordinates a n).apply_symm_apply _

/-- The strict isomorphism that identifies the graded coordinates. -/
def comparisonIso : Q ≅ R :=
  CoefficientLift.isoOfComponents (comparisonDegree E D)
    (fun a n x => by
      apply (D.coordinates a (n+1)).injective
      rw [comparisonDegree_coordinates]
      have hl := E.coordinate_d a n x
      have hr := D.coordinate_d a n (comparisonDegree E D a n x)
      dsimp only at hl hr
      rw [comparisonDegree_coordinates] at hr
      exact Prod.ext (hl.1.trans hr.1.symm) (DFinsupp.ext fun i => (hl.2 i).trans (hr.2 i).symm))
    (fun {a b} m n q h x f => by
      apply (D.coordinates a q).injective
      rw [comparisonDegree_coordinates]
      have hl := E.coordinate_act m n q h x f
      have hr := D.coordinate_act m n q h (comparisonDegree E D b m x) f
      dsimp only at hl hr
      rw [comparisonDegree_coordinates] at hr
      exact Prod.ext (hl.1.trans hr.1.symm) (DFinsupp.ext fun i => (hl.2 i).trans (hr.2 i).symm))

@[simp] theorem comparisonIso_coordinates (a : A.Obj) (n : ℤ) (x : (Q.complex a).X n) :
    D.coordinates a n (((comparisonIso E D).hom.app a).f n x) = E.coordinates a n x :=
  comparisonDegree_coordinates E D a n x

theorem inclusion_comparisonIso : E.inclusion ≫ (comparisonIso E D).hom = D.inclusion := by
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (D.coordinates a n).injective
  change D.coordinates a n (((comparisonIso E D).hom.app a).f n ((E.inclusion.app a).f n x)) = _
  rw [comparisonIso_coordinates, E.coordinate_inclusion, D.coordinate_inclusion]

theorem comparison : Comparison.{u,v,w,j} :=
  fun E D => ⟨comparisonIso E D, inclusion_comparisonIso E D, comparisonIso_coordinates E D⟩

section Construction

variable (C)

private theorem boundaryMap_summand (a : A.Obj) (n : ℤ) (i : I)
    (x : ((cells C i).complex a).X n) :
    boundaryMap C a n (summand (cells C) a n i x) =
      P.act (C.degree i + 1) (n + -C.degree i) (n+1) (by omega) (C.boundary i) x := by
  classical
  exact DirectSum.toModule_lof (R := k)
    (φ := fun i => P.act (C.degree i + 1) (n + -C.degree i) (n+1) (by omega) (C.boundary i)) i x

private theorem boundary_d_at (i : I) (a : A.Obj) (q r p : ℤ)
    (hr : q+1 = r) (hp : C.degree i+1+q = p)
    (x : (A.hom a (C.object i)).X q) :
    (P.complex a).d p (p+1) (P.act (C.degree i+1) q p hp (C.boundary i) x) +
      P.act (C.degree i+1) r (p+1) (by omega) (C.boundary i)
        ((-C.degree i).negOnePow • (A.hom a (C.object i)).d q r x) = 0 := by
  subst r
  rw [P.leibniz, C.closed, map_zero, LinearMap.zero_apply, zero_add]
  simp [Int.negOnePow_succ, Units.smul_def, map_zsmul]

private theorem boundary_act_at (i : I) {a b : A.Obj} (q r t p n : ℤ)
    (ht : q+r = t) (hp : C.degree i+1+q = p) (hn : p+r = n)
    (x : (A.hom b (C.object i)).X q) (f : (A.hom a b).X r) :
    P.act (C.degree i+1) t n (by omega) (C.boundary i) (A.comp q r t ht x f) =
      P.act p r n hn (P.act (C.degree i+1) q p hp (C.boundary i) x) f := by
  subst t p n
  exact (P.act_assoc (C.degree i+1) q r (C.boundary i) x f).symm

variable {S : RightDGModuleModel A} (s : StrictSum (cells C) S)

private def twist (a : A.Obj) (n : ℤ) : (S.complex a).X n →ₗ[k] (P.complex a).X (n+1) :=
  (boundaryMap C a n).comp (s.coordinates a n).toLinearMap

private theorem twist_summand (a : A.Obj) (n : ℤ) (i : I)
    (x : ((cells C i).complex a).X n) :
    twist C s a n (((s.inclusion i).app a).f n x) =
      P.act (C.degree i+1) (n + -C.degree i) (n+1) (by omega) (C.boundary i) x := by
  change boundaryMap C a n (s.coordinates a n (((s.inclusion i).app a).f n x)) = _
  rw [s.coordinate_inclusion, boundaryMap_summand]

private theorem d_twist (a : A.Obj) (n : ℤ) (x : (S.complex a).X n) :
    (P.complex a).d (n+1) (n+1+1) (twist C s a n x) +
      twist C s a (n+1) ((S.complex a).d n (n+1) x) = 0 := by
  let L := ((P.complex a).d (n+1) (n+1+1)).hom.comp (twist C s a n) +
    (twist C s a (n+1)).comp ((S.complex a).d n (n+1)).hom
  have hl : L = 0 := by
    apply term_hom_ext s a n
    intro i y
    change (P.complex a).d (n+1) (n+1+1) (twist C s a n (((s.inclusion i).app a).f n y)) +
      twist C s a (n+1) ((S.complex a).d n (n+1) (((s.inclusion i).app a).f n y)) = 0
    have h := CategoryTheory.congr_fun (((s.inclusion i).app a).comm n (n+1)) y
    change (S.complex a).d n (n+1) (((s.inclusion i).app a).f n y) =
      ((s.inclusion i).app a).f (n+1) (((cells C i).complex a).d n (n+1) y) at h
    rw [h, twist_summand, twist_summand]
    change _ + P.act _ _ _ _ (C.boundary i)
      (((-C.degree i).negOnePow • (A.hom a (C.object i)).d
        (n + -C.degree i) (n+1 + -C.degree i)) y) = 0
    simp only [ModuleCat.hom_smul, LinearMap.smul_apply]
    exact boundary_d_at C i a _ _ _ (by omega) (by omega) y
  exact LinearMap.congr_fun hl x

private theorem twist_act {a b : A.Obj} (m n q : ℤ) (h : m+n = q)
    (x : (S.complex b).X m) (f : (A.hom a b).X n) :
    twist C s a q (S.act m n q h x f) =
      P.act (m+1) n (q+1) (by omega) (twist C s b m x) f := by
  let L := (twist C s a q).comp ((S.act m n q h).flip f)
  let R := ((P.act (m+1) n (q+1) (by omega)).flip f).comp (twist C s b m)
  have hl : L = R := by
    apply term_hom_ext s b m
    intro i y
    change twist C s a q (S.act m n q h (((s.inclusion i).app b).f m y) f) =
      P.act (m+1) n (q+1) (by omega) (twist C s b m (((s.inclusion i).app b).f m y)) f
    rw [← (s.inclusion i).comm_act, twist_summand, twist_summand]
    exact boundary_act_at C i _ _ _ _ _ (by omega) (by omega) (by omega) y f
  exact LinearMap.congr_fun hl x

private abbrev Term (a : A.Obj) (n : ℤ) := (P.complex a).X n × (S.complex a).X n

private def step (a : A.Obj) (n : ℤ) :
    ModuleCat.of k (Term (P := P) (S := S) a n) ⟶ ModuleCat.of k (Term (P := P) (S := S) a (n+1)) :=
  ModuleCat.ofHom
    ((((P.complex a).d n (n+1)).hom.comp (LinearMap.fst k _ _) +
        (twist C s a n).comp (LinearMap.snd k _ _)).prod
      (((S.complex a).d n (n+1)).hom.comp (LinearMap.snd k _ _)))

private theorem d_d_apply (X : ModuleCochain.{u,v} k) (n : ℤ) (x : X.X n) :
    X.d (n+1) (n+1+1) (X.d n (n+1) x) = 0 := by
  rw [← ModuleCat.comp_apply, d_comp_d]
  rfl

@[reducible] private def complex (a : A.Obj) : ModuleCochain.{u,v} k :=
  CochainComplex.of (fun n => ModuleCat.of k (Term (P := P) (S := S) a n)) (step C s a) (by
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · change (P.complex a).d (n+1) (n+1+1)
        ((P.complex a).d n (n+1) x.1 + twist C s a n x.2) +
          twist C s a (n+1) ((S.complex a).d n (n+1) x.2) = 0
      rw [map_add, d_d_apply, zero_add, d_twist]
    · exact d_d_apply (S.complex a) n x.2)

private theorem complex_d (a : A.Obj) (n : ℤ) (x : Term (P := P) (S := S) a n) :
    (complex C s a).d n (n+1) x =
      ((P.complex a).d n (n+1) x.1 + twist C s a n x.2, (S.complex a).d n (n+1) x.2) := by
  change CochainComplex.of.d _ (step C s a) n (n+1) x = _
  rw [CochainComplex.of_d]
  rfl

private def action {a b : A.Obj} (m n q : ℤ) (h : m+n = q) :
    Term (P := P) (S := S) b m →ₗ[k] (A.hom a b).X n →ₗ[k] Term (P := P) (S := S) a q :=
  LinearMap.flip
    { toFun := fun f => (((P.act m n q h).flip f).comp (LinearMap.fst k _ _)).prod
        (((S.act m n q h).flip f).comp (LinearMap.snd k _ _))
      map_add' := by
        intro f g
        apply LinearMap.ext
        intro x
        exact Prod.ext (map_add (P.act m n q h x.1) f g) (map_add (S.act m n q h x.2) f g)
      map_smul' := by
        intro c f
        apply LinearMap.ext
        intro x
        exact Prod.ext (map_smul (P.act m n q h x.1) c f) (map_smul (S.act m n q h x.2) c f) }

/-- The preceding stage and the realized cell sum, with the prescribed differential. -/
@[reducible] def extensionModule : RightDGModuleModel A where
  complex := complex C s
  act := action
  act_id a n x := Prod.ext (P.act_id a n x.1) (S.act_id a n x.2)
  act_assoc m n q x f g := Prod.ext (P.act_assoc m n q x.1 f g) (S.act_assoc m n q x.2 f g)
  leibniz {a b} m n q h x f := by
    change (complex C s a).d q (q+1) (action m n q h x f) =
      action (m+1) n (q+1) _ ((complex C s b).d m (m+1) x) f +
        m.negOnePow • action m (n+1) (q+1) _ x ((A.hom a b).d n (n+1) f)
    rw [complex_d, complex_d]
    apply Prod.ext
    · change (P.complex a).d q (q+1) (P.act m n q h x.1 f) +
        twist C s a q (S.act m n q h x.2 f) =
          P.act (m+1) n (q+1) _ ((P.complex b).d m (m+1) x.1 + twist C s b m x.2) f +
            m.negOnePow • P.act m (n+1) (q+1) _ x.1 ((A.hom a b).d n (n+1) f)
      rw [P.leibniz, twist_act]
      simp only [map_add, LinearMap.add_apply]
      rw [add_right_comm]
    · exact S.leibniz m n q h x.2 f

private def inclusion : P ⟶ extensionModule C s where
  app a := CochainComplex.ofHom (fun n => ModuleCat.ofHom (LinearMap.inl k _ _)) (by
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (complex C s a).d n (n+1) (x, 0) = ((P.complex a).d n (n+1) x, 0)
    rw [complex_d, map_zero, map_zero, add_zero])
  comm_act m n q h x f := by
    change (P.act m n q h x f, 0) = (P.act m n q h x f, S.act m n q h 0 f)
    rw [map_zero, LinearMap.zero_apply]

/-- Form the attachment using any realization of the cell sum. -/
def extension : Attachment C (extensionModule C s) where
  inclusion := inclusion C s
  coordinates a n := (LinearEquiv.refl k _).prodCongr (s.coordinates a n)
  coordinate_inclusion a n x := by
    change (x, s.coordinates a n 0) = (x, 0)
    rw [map_zero]
  coordinate_d a n x := by
    change ((complex C s a).d n (n+1) x).1 = _ ∧ _
    rw [complex_d]
    exact ⟨rfl, s.coordinate_d a n x.2⟩
  coordinate_act m n q h x f := ⟨rfl, s.coordinate_act m n q h x.2 f⟩

end Construction

theorem realization : Realization.{u,v,w,j} := by
  intro k _ A P I C h
  let s := IndexedSums.sumRealization (cells C) h
  exact ⟨extensionModule C s, ⟨extension C s⟩⟩

theorem adequateRealization : AdequateRealization.{u,v,w,j} :=
  fun C => realization (liftFamily.{u,v,w,j,j} C) (fun _ _ => small_self _)

section Quotient

variable {S N : RightDGModuleModel A} (s : StrictSum (cells C) S)

private theorem degree_hom_ext {M N : RightDGModuleModel A} {f g : M ⟶ N}
    (h : ∀ a n x, (f.app a).f n x = (g.app a).f n x) : f = g := by
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  exact LinearMap.ext (h a n)

private def projectDegree (a : A.Obj) (n : ℤ) : (Q.complex a).X n →ₗ[k] (S.complex a).X n :=
  (s.coordinates a n).symm.toLinearMap.comp
    ((LinearMap.snd k _ _).comp (E.coordinates a n).toLinearMap)

private theorem projectDegree_coordinates (a : A.Obj) (n : ℤ) (x : (Q.complex a).X n) :
    s.coordinates a n (projectDegree E s a n x) = (E.coordinates a n x).2 :=
  (s.coordinates a n).apply_symm_apply _

/-- The strict projection to the untwisted direct sum of shifted representables. -/
def projection : Q ⟶ S where
  app a := CochainComplex.ofHom (fun n => ModuleCat.ofHom (projectDegree E s a n)) (by
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply (s.coordinates a (n+1)).injective
    apply DFinsupp.ext
    intro i
    change s.coordinates a (n+1) ((S.complex a).d n (n+1) (projectDegree E s a n x)) i =
      s.coordinates a (n+1) (projectDegree E s a (n+1) ((Q.complex a).d n (n+1) x)) i
    rw [s.coordinate_d, projectDegree_coordinates, projectDegree_coordinates]
    exact ((E.coordinate_d a n x).2 i).symm)
  comm_act {a b} m n q h x f := by
    apply (s.coordinates a q).injective
    apply DFinsupp.ext
    intro i
    change s.coordinates a q (projectDegree E s a q (Q.act m n q h x f)) i =
      s.coordinates a q (S.act m n q h (projectDegree E s b m x) f) i
    rw [s.coordinate_act, projectDegree_coordinates, projectDegree_coordinates]
    exact (E.coordinate_act m n q h x f).2 i

theorem projection_coordinates (a : A.Obj) (n : ℤ) (x : (Q.complex a).X n) :
    s.coordinates a n (((projection E s).app a).f n x) = (E.coordinates a n x).2 :=
  projectDegree_coordinates E s a n x

/-- The degreewise linear section that includes the cell coordinates. -/
def sectionDegree (a : A.Obj) (n : ℤ) : (S.complex a).X n →ₗ[k] (Q.complex a).X n :=
  (E.coordinates a n).symm.toLinearMap.comp
    ((LinearMap.inr k _ _).comp (s.coordinates a n).toLinearMap)

/-- Comparing attachment coordinates also compares the strict quotient maps. -/
theorem projection_comparisonIso {T : RightDGModuleModel A} (r : StrictSum (cells C) T) :
    (comparisonIso E D).hom ≫ projection D r =
      projection E s ≫ (IndexedSums.comparisonIso s r).hom := by
  apply degree_hom_ext
  intro a n x
  apply (r.coordinates a n).injective
  change r.coordinates a n (((projection D r).app a).f n (((comparisonIso E D).hom.app a).f n x)) =
    r.coordinates a n (((IndexedSums.comparisonIso s r).hom.app a).f n (((projection E s).app a).f n x))
  rw [projection_coordinates, comparisonIso_coordinates,
    IndexedSums.comparisonIso_coordinates, projection_coordinates]

private theorem section_coordinates (a : A.Obj) (n : ℤ) (x : (S.complex a).X n) :
    E.coordinates a n (sectionDegree E s a n x) = (0, s.coordinates a n x) :=
  (E.coordinates a n).apply_symm_apply _

theorem sectionDegree_act {a b : A.Obj} (m n q : ℤ) (h : m+n = q)
    (x : (S.complex b).X m) (f : (A.hom a b).X n) :
    sectionDegree E s a q (S.act m n q h x f) = Q.act m n q h (sectionDegree E s b m x) f := by
  apply (E.coordinates a q).injective
  rw [section_coordinates]
  have he := E.coordinate_act m n q h (sectionDegree E s b m x) f
  dsimp only at he
  rw [section_coordinates] at he
  symm
  apply Prod.ext
  · exact he.1.trans (by rw [map_zero, LinearMap.zero_apply])
  · exact DFinsupp.ext fun i => (he.2 i).trans (s.coordinate_act m n q h x f i).symm

@[simp] theorem projection_section (a : A.Obj) (n : ℤ) (x : (S.complex a).X n) :
    ((projection E s).app a).f n (sectionDegree E s a n x) = x := by
  apply (s.coordinates a n).injective
  rw [projection_coordinates, section_coordinates]

theorem inclusion_projection : E.inclusion ≫ projection E s = 0 := by
  apply degree_hom_ext
  intro a n x
  apply (s.coordinates a n).injective
  change s.coordinates a n (((projection E s).app a).f n ((E.inclusion.app a).f n x)) =
    s.coordinates a n 0
  rw [projection_coordinates, E.coordinate_inclusion, map_zero]

private theorem preceding_add_section (a : A.Obj) (n : ℤ) (x : (Q.complex a).X n) :
    (E.inclusion.app a).f n (E.coordinates a n x).1 +
      sectionDegree E s a n (((projection E s).app a).f n x) = x := by
  apply (E.coordinates a n).injective
  rw [map_add, E.coordinate_inclusion, section_coordinates, projection_coordinates]
  exact Prod.ext (add_zero _) (zero_add _)

private theorem factor_degree (g : Q ⟶ N) (hg : E.inclusion ≫ g = 0)
    (a : A.Obj) (n : ℤ) (x : (Q.complex a).X n) :
    (g.app a).f n (sectionDegree E s a n (((projection E s).app a).f n x)) =
      (g.app a).f n x := by
  have h := congrArg (fun f : P ⟶ N => (f.app a).f n (E.coordinates a n x).1) hg
  change (g.app a).f n ((E.inclusion.app a).f n (E.coordinates a n x).1) = 0 at h
  have h' := congrArg ((g.app a).f n) (preceding_add_section E s a n x)
  rwa [map_add, h, zero_add] at h'

private def quotientDesc (g : Q ⟶ N) (hg : E.inclusion ≫ g = 0) : S ⟶ N where
  app a := CochainComplex.ofHom
    (fun n => ModuleCat.ofHom (((g.app a).f n).hom.comp (sectionDegree E s a n))) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      let y := sectionDegree E s a n x
      change (N.complex a).d n (n+1) ((g.app a).f n y) =
        (g.app a).f (n+1) (sectionDegree E s a (n+1) ((S.complex a).d n (n+1) x))
      have hp := CategoryTheory.congr_fun (((projection E s).app a).comm n (n+1)) y
      change (S.complex a).d n (n+1) (((projection E s).app a).f n y) =
        ((projection E s).app a).f (n+1) ((Q.complex a).d n (n+1) y) at hp
      rw [show ((projection E s).app a).f n y = x from projection_section E s a n x] at hp
      rw [hp, factor_degree E s g hg]
      exact CategoryTheory.congr_fun ((g.app a).comm n (n+1)) y)
  comm_act {a b} m n q h x f := by
    let y := sectionDegree E s b m x
    change (g.app a).f q (sectionDegree E s a q (S.act m n q h x f)) =
      N.act m n q h ((g.app b).f m y) f
    have hp := (projection E s).comm_act m n q h y f
    rw [show ((projection E s).app b).f m y = x from projection_section E s b m x] at hp
    rw [← hp, factor_degree E s g hg, g.comm_act]

/-- The projection is a cokernel in the strict category of dg modules. -/
def projectionIsCokernel : IsColimit (CokernelCofork.ofπ (projection E s) (inclusion_projection E s)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun g hg => quotientDesc E s g hg)
    (fun g hg => degree_hom_ext (factor_degree E s g hg))
    (by
      intro N g hg m hm
      apply degree_hom_ext
      intro a n x
      have h := congrArg (fun f : Q ⟶ N => (f.app a).f n (sectionDegree E s a n x)) hm
      change (m.app a).f n (((projection E s).app a).f n (sectionDegree E s a n x)) = _
        at h
      rw [projection_section] at h
      exact h)

theorem termsSmall (E : Attachment C Q) : Specs.DerivedFormalization.DG.IndexedSums.TermsSmall (cells C) := by
  intro a n
  apply small_of_injective (f := fun y : CellTerm C a n => (E.coordinates a n).symm (0, y))
  intro y z h
  exact congrArg Prod.snd ((E.coordinates a n).symm.injective h)

end Quotient

/-- At the native cell sum, the coordinate construction gives the original projection. -/
theorem nativeProjection {J : Type v} (B : SemiFree.CellFamily P J) :
    projection (nativeAttachment B) (IndexedSums.nativeSum (SemiFree.cells B)) =
      SemiFree.projection B := by
  apply degree_hom_ext
  intro a n x
  exact projection_coordinates (nativeAttachment B) (IndexedSums.nativeSum (SemiFree.cells B)) a n x

theorem quotient : Specs.DerivedFormalization.DG.IndexedCellAttachment.Quotient.{u,v,w,j} := by
  intro k _ A P Q I C E
  let hs := termsSmall E
  let s := IndexedSums.sumRealization (cells C) hs
  refine ⟨_, s, projection E s, inclusion_projection E s,
    ⟨IndexedSums.isColimit s⟩, ⟨projectionIsCokernel E s⟩, projection_coordinates E s, ?_⟩
  intro a n
  refine ⟨?_, fun x => ⟨sectionDegree E s a n x, projection_section E s a n x⟩, ?_⟩
  · intro x y h
    exact congrArg Prod.fst ((E.coordinate_inclusion a n x).symm.trans
      ((congrArg (E.coordinates a n) h).trans (E.coordinate_inclusion a n y)))
  · intro x
    constructor
    · intro h
      refine ⟨(E.coordinates a n x).1, (E.coordinates a n).injective ?_⟩
      rw [E.coordinate_inclusion]
      have hp := projection_coordinates E s a n x
      rw [h, map_zero] at hp
      exact Prod.ext rfl hp
    · rintro ⟨y, rfl⟩
      apply (s.coordinates a n).injective
      rw [projection_coordinates, E.coordinate_inclusion, map_zero]

section Generator

variable (i : I)

@[simp] theorem generator_coordinates :
    E.coordinates (C.object i) (C.degree i) (E.generator i) =
      (0, summand (cells C) (C.object i) (C.degree i) i
        (SemiFree.generator (C.object i) (C.degree i))) :=
  (E.coordinates (C.object i) (C.degree i)).apply_symm_apply _

@[simp] theorem comparisonIso_generator :
    ((comparisonIso E D).hom.app (C.object i)).f (C.degree i) (E.generator i) = D.generator i := by
  apply (D.coordinates (C.object i) (C.degree i)).injective
  rw [comparisonIso_coordinates, generator_coordinates, generator_coordinates]

@[simp] theorem generator_d :
    (Q.complex (C.object i)).d (C.degree i) (C.degree i+1) (E.generator i) =
      (E.inclusion.app (C.object i)).f (C.degree i+1) (C.boundary i) := by
  classical
  let a := C.object i
  let n := C.degree i
  let e := SemiFree.generator a n
  apply (E.coordinates a (n+1)).injective
  rw [E.coordinate_inclusion]
  have h := E.coordinate_d a n (E.generator i)
  dsimp only at h
  rw [generator_coordinates] at h
  apply Prod.ext
  · rw [h.1, map_zero, zero_add, boundaryMap_summand]
    exact act_id_reindexed P a (n+1) _ (by dsimp [n]; omega) (C.boundary i)
  · have h₂ : (E.coordinates a (n+1) ((Q.complex a).d n (n+1) (E.generator i))).2 =
        rawStep (cells C) a n (summand (cells C) a n i e) := DFinsupp.ext h.2
    rw [h₂]
    change DirectSum.lmap (fun s => ((cells C s).complex a).d n (n+1) |>.hom)
      (DirectSum.lof k I (fun s => ((cells C s).complex a).X n) i e) = 0
    rw [DirectSum.lmap_lof]
    change summand (cells C) a (n+1) i (((SemiFree.cell a n).complex a).d n (n+1) e) = 0
    rw [RightDGModule.cellGenerator_d, map_zero]

theorem generator_mul (a : A.Obj) (j q : ℤ) (h : C.degree i+j = q)
    (f : (A.hom a (C.object i)).X j) :
    E.coordinates a q (Q.act (C.degree i) j q h (E.generator i) f) =
      (0, summand (cells C) a q i
        (((A.hom a (C.object i)).XIsoOfEq (by omega : j = q + -C.degree i)).hom f)) := by
  classical
  subst q
  let b := C.object i
  let n := C.degree i
  let e := SemiFree.generator b n
  have hc := E.coordinate_act n j (n+j) rfl (E.generator i) f
  dsimp only at hc
  rw [generator_coordinates] at hc
  apply Prod.ext
  · rw [hc.1, map_zero, LinearMap.zero_apply]
  · have h₂ : (E.coordinates a (n+j) (Q.act n j (n+j) rfl (E.generator i) f)).2 =
        rawAct (cells C) n j (n+j) rfl (summand (cells C) b n i e) f := DFinsupp.ext hc.2
    rw [h₂]
    change DirectSum.lmap (fun s => ((cells C s).act n j (n+j) rfl).flip f)
      (DirectSum.lof k I (fun s => ((cells C s).complex b).X n) i e) = _
    rw [DirectSum.lmap_lof]
    change summand (cells C) a (n+j) i ((SemiFree.cell b n).act n j (n+j) rfl e f) = _
    rw [RightDGModule.cellGenerator_mul]

theorem generator_mul_d (a : A.Obj) (j q : ℤ) (h : C.degree i+j = q)
    (f : (A.hom a (C.object i)).X j) :
    (Q.complex a).d q (q+1) (Q.act (C.degree i) j q h (E.generator i) f) =
      (E.inclusion.app a).f (q+1) (P.act (C.degree i+1) j (q+1) (by omega) (C.boundary i) f) +
        (C.degree i).negOnePow • Q.act (C.degree i) (j+1) (q+1) (by omega)
          (E.generator i) ((A.hom a (C.object i)).d j (j+1) f) := by
  rw [Q.leibniz, generator_d, E.inclusion.comm_act]

end Generator

theorem generatorFormula : GeneratorFormula.{u,v,w,j} :=
  fun E i => ⟨generator_d E i, fun a j q h f => ⟨generator_mul E i a j q h f, generator_mul_d E i a j q h f⟩⟩

section CoefficientLift

open DerivedFormalization.DG.CoefficientLift (liftCategory liftModule liftMap)

private def liftCoordinates (a : A.Obj) (n : ℤ) :
    ((liftModule.{u,v,w,t} Q).complex a).X n ≃ₗ[k]
      (((liftModule.{u,v,w,t} P).complex a).X n × CellTerm (liftFamily.{u,v,w,j,t} C) a n) :=
  ULift.moduleEquiv.trans ((E.coordinates a n).trans
    (ULift.moduleEquiv.symm.prodCongr (IndexedSums.liftTerm.{u,v,w,j,t} (cells C) a n)))

private theorem lift_boundary_down (a : A.Obj) (n : ℤ) (y : CellTerm C a n) :
    (boundaryMap (liftFamily.{u,v,w,j,t} C) a n
      (IndexedSums.liftTerm.{u,v,w,j,t} (cells C) a n y)).down =
        boundaryMap C a n y := by
  classical
  let L := ULift.moduleEquiv.toLinearMap.comp
    ((boundaryMap (liftFamily.{u,v,w,j,t} C) a n).comp
      (IndexedSums.liftTerm.{u,v,w,j,t} (cells C) a n).toLinearMap)
  have h : L = boundaryMap C a n := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    change (boundaryMap (liftFamily.{u,v,w,j,t} C) a n
      (IndexedSums.liftTerm.{u,v,w,j,t} (cells C) a n (summand (cells C) a n i x))).down =
        boundaryMap C a n (summand (cells C) a n i x)
    rw [liftTerm_summand]
    change (boundaryMap (liftFamily.{u,v,w,j,t} C) a n
      (summand (cells (liftFamily.{u,v,w,j,t} C)) a n i (ULift.up x))).down =
        boundaryMap C a n (summand (cells C) a n i x)
    exact (congrArg ULift.down (boundaryMap_summand (liftFamily.{u,v,w,j,t} C) a n i
      (ULift.up x))).trans (boundaryMap_summand C a n i x).symm
  exact LinearMap.congr_fun h y

/-- The lifted module retains the coordinate description of the attachment. -/
def liftAttachment : Attachment (liftFamily.{u,v,w,j,t} C) (liftModule.{u,v,w,t} Q) where
  inclusion := liftMap.{u,v,w,t} E.inclusion
  coordinates := liftCoordinates.{u,v,w,j,t} E
  coordinate_inclusion a n x := by
    change (ULift.up (E.coordinates a n ((E.inclusion.app a).f n x.down)).1,
      IndexedSums.liftTerm.{u,v,w,j,t} (cells C) a n
        (E.coordinates a n ((E.inclusion.app a).f n x.down)).2) = (x, 0)
    rw [E.coordinate_inclusion, map_zero]
    rfl
  coordinate_d a n x := by
    constructor
    · apply ULift.ext
      change (E.coordinates a (n+1) ((Q.complex a).d n (n+1) x.down)).1 =
        (P.complex a).d n (n+1) (E.coordinates a n x.down).1 +
          (boundaryMap (liftFamily.{u,v,w,j,t} C) a n
            (IndexedSums.liftTerm.{u,v,w,j,t} (cells C) a n (E.coordinates a n x.down).2)).down
      rw [lift_boundary_down]
      exact (E.coordinate_d a n x.down).1
    · intro i
      apply ULift.ext
      exact (E.coordinate_d a n x.down).2 i
  coordinate_act m n q h x f := by
    constructor
    · apply ULift.ext
      exact (E.coordinate_act m n q h x.down f.down).1
    · intro i
      apply ULift.ext
      exact (E.coordinate_act m n q h x.down f.down).2 i

private theorem lift_complex_XIsoOfEq (X : ModuleCochain.{u,v} k) (m n : ℤ) (h : m = n)
    (x : X.X m) :
    ((Specs.DerivedFormalization.DG.Yoneda.liftComplex.{u,v,t} X).XIsoOfEq h).hom (ULift.up x) =
      ULift.up ((X.XIsoOfEq h).hom x) := by
  subst n
  rfl

private theorem lift_cellGenerator (a : A.Obj) (n : ℤ) :
    SemiFree.generator (A := liftCategory.{u,v,w,t} A) a n =
      ULift.up (SemiFree.generator (A := A) a n) :=
  lift_complex_XIsoOfEq.{u,v,t} (A.hom a a) 0 (n + -n) (by omega) (A.id a)

@[simp] theorem liftAttachment_generator (i : I) :
    ((liftAttachment.{u,v,w,j,t} E).generator i).down = E.generator i := by
  have h : (liftAttachment.{u,v,w,j,t} E).generator i = ULift.up (E.generator i) := by
    apply ((liftAttachment.{u,v,w,j,t} E).coordinates (C.object i) (C.degree i)).injective
    refine (generator_coordinates (liftAttachment.{u,v,w,j,t} E) i).trans ?_
    change (0, summand (cells (liftFamily.{u,v,w,j,t} C)) (C.object i) (C.degree i) i
        (SemiFree.generator (A := liftCategory.{u,v,w,t} A) (C.object i) (C.degree i))) =
      (ULift.up (E.coordinates (C.object i) (C.degree i) (E.generator i)).1,
        IndexedSums.liftTerm.{u,v,w,j,t} (cells C) (C.object i) (C.degree i)
          (E.coordinates (C.object i) (C.degree i) (E.generator i)).2)
    rw [generator_coordinates, liftTerm_summand, lift_cellGenerator]
    rfl
  exact congrArg ULift.down h

theorem liftComparison : LiftComparison.{u,v,w,j,t} := fun E =>
  ⟨liftAttachment.{u,v,w,j,t} E, rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl,
    liftAttachment_generator E⟩

end CoefficientLift

end

end DerivedFormalization.DG.IndexedCellAttachment
