import Specs.LinearAlgebraicGroups.Cohomology.OrderedCechInjectiveRows
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Data.Finset.Max
import Mathlib.Order.Fin.Tuple
import Mathlib.Topology.Sheaves.SheafOfFunctions

open CategoryTheory Opposite TopologicalSpace

universe u v w

noncomputable section

namespace LinearAlgebraicGroups.OrderedCechInjectiveRows

open Specs.OrderedCechInjectiveRows

section LeastVertex

variable {J : Type v} [LinearOrder J] {A : Type w} [AddCommGroup A]

/-- Prepend a vertex strictly below the first vertex of the tuple. -/
private def prepend {n : ℕ} (a : J) (e : Fin (n + 1) ↪o J) (h : a < e 0) :
    Fin (n + 2) ↪o J :=
  OrderEmbedding.ofStrictMono (Fin.cons a e)
    (Fin.strictMono_cons.mpr ⟨fun j => h.trans_le (e.monotone (Fin.zero_le j)), e.strictMono⟩)

private theorem prepend_zero {n : ℕ} {a : J} {e : Fin (n + 1) ↪o J} (h : a < e 0) :
    prepend a e h 0 = a := rfl

private theorem prepend_succ {n : ℕ} {a : J} {e : Fin (n + 1) ↪o J} (h : a < e 0)
    (j : Fin (n + 1)) : prepend a e h j.succ = e j := by
  exact Fin.cons_succ (α := fun _ => J) a (fun k => e k) j

private theorem face_zero_apply {n : ℕ} (e : Fin (n + 2) ↪o J) (j : Fin (n + 1)) :
    face e 0 j = e j.succ := rfl

private theorem face_succ_at_zero {n : ℕ} (e : Fin (n + 2) ↪o J) (i : Fin (n + 1)) :
    face e i.succ 0 = e 0 := by
  change e (i.succ.succAbove 0) = e 0
  rw [Fin.succ_succAbove_zero]

private theorem face_prepend_zero {n : ℕ} {a : J} {e : Fin (n + 1) ↪o J} (h : a < e 0) :
    face (prepend a e h) 0 = e := by
  ext j
  exact prepend_succ h j

private theorem prepend_face_zero {n : ℕ} (e : Fin (n + 2) ↪o J) (h : e 0 < face e 0 0) :
    prepend (e 0) (face e 0) h = e := by
  ext j
  refine Fin.cases rfl (fun k => ?_) j
  rw [prepend_succ, face_zero_apply]

private theorem face_prepend_succ {n : ℕ} {a : J} {e : Fin (n + 2) ↪o J} (h : a < e 0)
    (i : Fin (n + 2)) :
    face (prepend a e h) i.succ =
      prepend a (face e i) (h.trans_le (e.monotone (Fin.zero_le _))) := by
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · rw [face_succ_at_zero, prepend_zero, prepend_zero]
  · change prepend a e h (i.succ.succAbove k.succ) =
      prepend a (face e i) _ k.succ
    rw [Fin.succ_succAbove_succ, prepend_succ, prepend_succ]
    rfl

/-- Contraction of the alternating cochains on an ordered simplex with a least vertex. -/
private theorem exact_of_least (a : J) (ha : ∀ j, a ≤ j) (p : ℕ)
    (c : (Fin (p + 2) ↪o J) → A)
    (hc : ∀ e : Fin (p + 3) ↪o J,
      (∑ i : Fin (p + 3), (-1 : ℤ) ^ (i : ℕ) • c (face e i)) = 0) :
    ∃ b : (Fin (p + 1) ↪o J) → A, ∀ e : Fin (p + 2) ↪o J,
      (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • b (face e i)) = c e := by
  let b : (Fin (p + 1) ↪o J) → A := fun e =>
    if h : a < e 0 then c (prepend a e h) else 0
  refine ⟨b, fun e => ?_⟩
  rcases (ha (e 0)).eq_or_lt with he | he
  · have h₀ : e 0 < face e 0 0 := e.strictMono (Fin.succ_pos 0)
    have htail (i : Fin (p + 1)) : b (face e i.succ) = 0 := by
      have hn : ¬a < face e i.succ 0 := by simp [face_succ_at_zero, he]
      exact dite_eq_right hn
    have hhead : b (face e 0) = c e := by
      subst a
      dsimp only [b]
      rw [dite_eq_left h₀, prepend_face_zero]
    rw [Fin.sum_univ_succ, hhead]
    simp [htail]
  · have hb (i : Fin (p + 2)) :
        b (face e i) = c (face (prepend a e he) i.succ) := by
      have hi : a < face e i 0 := he.trans_le (e.monotone (Fin.zero_le _))
      dsimp only [b]
      rw [dite_eq_left hi, face_prepend_succ]
    have h := hc (prepend a e he)
    rw [Fin.sum_univ_succ, face_prepend_zero] at h
    simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_succ, pow_succ',
      neg_one_mul, neg_smul, Finset.sum_neg_distrib, ← hb, ← sub_eq_add_neg] at h
    exact (sub_eq_zero.mp h).symm

end LeastVertex

section GermFamilies

variable {X : TopCat.{u}} {R : RingSheaf X} (M : SheafOfModules.{u} R)

private abbrev Germ (x : X) : Type u :=
  ↑(TopCat.Presheaf.stalk (X := X) M.val.presheaf x)

/-- Sections are arbitrary families of elements of the stalks over the open. -/
private def germFamiliesPresheaf : X.Presheaf AddCommGrpCat.{u} where
  obj V := AddCommGrpCat.of (∀ x : V.unop, Germ M x.val)
  map f := AddCommGrpCat.ofHom
    { toFun := fun s x => s (f.unop x)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_id V := by ext s x; rfl
  map_comp f g := by ext s x; rfl

private instance germFamiliesModule (V : (Opens X)ᵒᵖ) :
    Module (R.obj.obj V) ((germFamiliesPresheaf M).obj V) :=
  letI (x : V.unop) : Module (R.obj.obj V) (Germ M x.val) :=
    Module.compHom _ (TopCat.Presheaf.germ (X := X) R.obj V.unop x.val x.property).hom
  inferInstanceAs (Module (R.obj.obj V) (∀ x : V.unop, Germ M x.val))

private def germFamiliesModulePresheaf : PresheafOfModules.{u} R.obj :=
  PresheafOfModules.ofPresheaf (germFamiliesPresheaf M) (by
    intro V W f r s
    funext x
    change (TopCat.Presheaf.germ (X := X) R.obj V.unop x.val (f.unop.le x.property)) r • s (f.unop x) =
      (TopCat.Presheaf.germ (X := X) R.obj W.unop x.val x.property) (R.obj.map f r) • s (f.unop x)
    have hg := TopCat.Presheaf.germ_res_apply' (X := X) R.obj f x.val x.property r
    exact congrArg (fun a => a • (show ∀ y : V.unop, Germ M y.val from s) (f.unop x))
      hg.symm)

private def germFamilies : SheafOfModules.{u} R where
  val := germFamiliesModulePresheaf M
  isSheaf := by
    change (germFamiliesPresheaf M).IsSheaf
    apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat.{u})
    exact TopCat.Presheaf.toTypes_isSheaf X (Germ M)

private def germFamiliesEmbedding : M ⟶ germFamilies M :=
  ⟨PresheafOfModules.homMk
    { app := fun V => AddCommGrpCat.ofHom
        { toFun := fun s x => TopCat.Presheaf.germ (X := X) M.val.presheaf V.unop x.val x.property s
          map_zero' := funext fun _ => map_zero _
          map_add' := fun s t => funext fun _ => map_add _ s t }
      naturality := by
        intro V W f
        ext s
        funext x
        exact TopCat.Presheaf.germ_res_apply' (X := X) M.val.presheaf f x.val x.property s }
    (by
      intro V r s
      funext x
      exact M.val.germ_ringCat_smul x.val V.unop x.property r s)⟩

private instance : Mono (germFamiliesEmbedding M) := by
  apply (SheafOfModules.forget R).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro V s t h
  exact TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf R).obj M) V.unop s t
    (fun x hx => congrFun h (⟨x, hx⟩ : V.unop))

end GermFamilies

section PointwiseExactness

variable {X : TopCat.{u}} {R : RingSheaf X} {I : Type v} [LinearOrder I]
  (U : I → Opens X)

private theorem mem_tupleOpen {p : ℕ} {e : Fin (p + 1) ↪o I} {x : X} :
    x ∈ tupleOpen U e ↔ ∀ i, x ∈ U (e i) := by
  rw [← SetLike.mem_coe, tupleOpen, Opens.coe_iInf, Set.mem_iInter]
  rfl

private abbrev PointIndices (x : X) := { i : I // x ∈ U i }

private theorem exists_least_index [Finite I] (hU : (⨆ i, U i) = ⊤) (x : X) :
    ∃ a : PointIndices U x, ∀ j : PointIndices U x, a ≤ j := by
  classical
  let := Fintype.ofFinite I
  let s : Finset I := Finset.univ.filter (fun i => x ∈ U i)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, U i by rw [hU]; trivial)
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  refine ⟨⟨s.min' hs, (Finset.mem_filter.mp (Finset.min'_mem s hs)).2⟩, fun j => ?_⟩
  exact Finset.min'_le s j.val (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.property⟩)

private abbrev forgetPoint {x : X} {p : ℕ} (e : Fin (p + 1) ↪o PointIndices U x) :
    Fin (p + 1) ↪o I :=
  e.trans (OrderEmbedding.subtype _)

private def liftTuple {p : ℕ} (e : Fin (p + 1) ↪o I) (x : tupleOpen U e) :
    Fin (p + 1) ↪o PointIndices U x.val :=
  OrderEmbedding.ofStrictMono (fun i => ⟨e i, (mem_tupleOpen U).mp x.property i⟩) e.strictMono

private def pointOfTuple {x : X} {p : ℕ} (e : Fin (p + 1) ↪o PointIndices U x) :
    tupleOpen U (forgetPoint U e) :=
  ⟨x, (mem_tupleOpen U).mpr fun i => (e i).property⟩

private theorem germFamilies_differential_apply (M : SheafOfModules.{u} R) (p : ℕ)
    (b : Cochains (germFamilies M) U p) (e : Fin (p + 2) ↪o I) (x : tupleOpen U e) :
    differential (germFamilies M) U p b e x =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        b (face e i) ⟨x.val, tupleOpen_le_face U e i x.property⟩ := by
  let summand (i : Fin (p + 2)) (y : tupleOpen U e) : Germ M y.val :=
    (-1 : ℤ) ^ (i : ℕ) • b (face e i) ⟨y.val, tupleOpen_le_face U e i y.property⟩
  change (∑ i, summand i) x = ∑ i, summand i x
  rw [Finset.sum_apply]

/-- Solve the cocycle equation independently at each point of the space. -/
private theorem germFamilies_exact [Finite I] (hU : (⨆ i, U i) = ⊤)
    (M : SheafOfModules.{u} R) (p : ℕ) (c : Cochains (germFamilies M) U (p + 1))
    (hc : differential (germFamilies M) U (p + 1) c = 0) :
    ∃ b : Cochains (germFamilies M) U p, differential (germFamilies M) U p b = c := by
  classical
  let cAt (x : X) (e : Fin (p + 2) ↪o PointIndices U x) : Germ M x :=
    c (forgetPoint U e) (pointOfTuple U e)
  have hAt (x : X) (e : Fin (p + 3) ↪o PointIndices U x) :
      (∑ i : Fin (p + 3), (-1 : ℤ) ^ (i : ℕ) • cAt x (face e i)) = 0 := by
    have h := congrFun (congrFun hc (forgetPoint U e)) (pointOfTuple U e)
    rw [germFamilies_differential_apply] at h
    exact h
  have hLocal (x : X) : ∃ b : (Fin (p + 1) ↪o PointIndices U x) → Germ M x,
      ∀ e : Fin (p + 2) ↪o PointIndices U x,
        (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • b (face e i)) = cAt x e := by
    obtain ⟨a, ha⟩ := exists_least_index U hU x
    exact exact_of_least a ha p (cAt x) (hAt x)
  choose bAt hbAt using hLocal
  let b : Cochains (germFamilies M) U p := fun e x => bAt x.val (liftTuple U e x)
  refine ⟨b, ?_⟩
  funext e x
  rw [germFamilies_differential_apply]
  exact hbAt x.val (liftTuple U e x)

end PointwiseExactness

section Injective

variable {X : TopCat.{u}} {R : RingSheaf X} {I : Type v} [LinearOrder I]
  (U : I → Opens X)

private def mapCochains {M N : SheafOfModules.{u} R} (f : M ⟶ N) (p : ℕ) :
    Cochains M U p →+ Cochains N U p where
  toFun c e := f.val.app (op (tupleOpen U e)) (c e)
  map_zero' := funext fun _ => map_zero _
  map_add' _ _ := funext fun _ => map_add _ _ _

private theorem mapCochains_differential {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    (p : ℕ) (c : Cochains M U p) :
    mapCochains U f (p + 1) (differential M U p c) =
      differential N U p (mapCochains U f p c) := by
  funext e
  change f.val.app (op (tupleOpen U e)) (∑ i : Fin (p + 2),
    (-1 : ℤ) ^ (i : ℕ) • M.val.map (homOfLE (tupleOpen_le_face U e i)).op (c (face e i))) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        N.val.map (homOfLE (tupleOpen_le_face U e i)).op
          (f.val.app (op (tupleOpen U (face e i))) (c (face e i)))
  erw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  erw [map_zsmul]
  congr 1
  exact PresheafOfModules.naturality_apply f.val (homOfLE (tupleOpen_le_face U e i)).op
    (c (face e i))

end Injective

/-- The embedding into the sheaf of all germ families splits for injective coefficients. -/
theorem injective_row_exactness : InjectiveRowExactness.{u, v} := by
  intro X R I _ _ U hU M hM p c hc
  let ι := germFamiliesEmbedding M
  let r := Injective.factorThru (𝟙 M) ι
  have hr : ι ≫ r = 𝟙 M := Injective.comp_factorThru (𝟙 M) ι
  have h : differential (germFamilies M) U (p + 1) (mapCochains U ι (p + 1) c) = 0 := by
    rw [← mapCochains_differential, hc, map_zero]
  obtain ⟨b, hb⟩ := germFamilies_exact U hU M p _ h
  refine ⟨mapCochains U r p b, ?_⟩
  rw [← mapCochains_differential, hb]
  funext e
  change (ι ≫ r).val.app (op (tupleOpen U e)) (c e) = c e
  rw [hr]
  rfl

end LinearAlgebraicGroups.OrderedCechInjectiveRows
