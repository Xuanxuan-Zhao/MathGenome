import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.OrderedCechComparison
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Supported integral tuple chains and their action on Čech cochains. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Opposite TopologicalSpace
open scoped Simplicial
open AdvancedHomologicalAlgebra.Cech AdvancedHomologicalAlgebra.SheafTheory
open AdvancedHomologicalAlgebra.CechSequenceOriginal
open Specs.DerivedFormalization.OrderedCechComparison

namespace DerivedFormalization.OrderedCechComparison

universe u r v w

private abbrev TupleOn {I : Type v} (S : Set I) (p : ℕ) :=
  {t : Fin (p + 1) → I // Set.range t ⊆ S}

private abbrev Chains {I : Type v} (S : Set I) (p : ℕ) := TupleOn S p →₀ ℤ

private def gen {I : Type v} {S : Set I} {p : ℕ} (t : TupleOn S p) : Chains S p :=
  Finsupp.single t 1

private theorem chain_ext {I : Type v} {S : Set I} {p : ℕ} {M : Type*}
    [AddCommGroup M] [Module ℤ M] {f g : Chains S p →ₗ[ℤ] M}
    (h : ∀ t, f (gen t) = g (gen t)) : f = g := by
  apply Finsupp.lhom_ext
  intro t a
  rw [← Finsupp.smul_single_one, f.map_smul, g.map_smul]
  rw [show f (Finsupp.single t 1) = g (Finsupp.single t 1) from h t]

private def weaken {I : Type v} {S T : Set I} (h : S ⊆ T) {p : ℕ} (t : TupleOn S p) :
    TupleOn T p := ⟨t.1, t.2.trans h⟩

private def restrictPositions {I : Type v} {S : Set I} {p q : ℕ}
    (t : TupleOn S q) (f : Fin (p + 1) → Fin (q + 1)) : TupleOn S p :=
  ⟨t.1 ∘ f, fun _ ⟨i, hi⟩ => t.2 ⟨f i, hi⟩⟩

private abbrev Diagram (I : Type v) := Set I ⥤ ModuleCat.{v} ℤ

private abbrev freeTuples (I : Type v) (p : ℕ) : Diagram I where
  obj S := ModuleCat.of ℤ (Chains S p)
  map f := ModuleCat.ofHom (Finsupp.lmapDomain ℤ ℤ (weaken (leOfHom f)))
  map_id S := by
    apply ModuleCat.hom_ext
    apply (chain_ext (S := S) (p := p))
    intro t
    simp [gen, weaken]
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply chain_ext
    intro t
    simp [gen, weaken]

private theorem freeTuples_map_gen {I : Type v} {S T : Set I} (f : S ⟶ T)
    {p : ℕ} (t : TupleOn S p) :
    (freeTuples I p).map f (gen t) = gen (weaken (leOfHom f) t) := by
  change (Finsupp.lmapDomain ℤ ℤ (weaken (leOfHom f))) (Finsupp.single t 1) = _
  simp [gen]

private def ownTuple {I : Type v} {p : ℕ} (t : Fin (p + 1) → I) :
    TupleOn (Set.range t) p := ⟨t, le_rfl⟩

/-- The value on a tuple in its own range determines a map from the free diagram. -/
private def liftGenerators {I : Type v} {p : ℕ} {P : Diagram I}
    (f : ∀ t : Fin (p + 1) → I, P.obj (Set.range t)) : freeTuples I p ⟶ P where
  app S := ModuleCat.ofHom (Finsupp.linearCombination ℤ
    (fun t : TupleOn S p => P.map (homOfLE t.2) (f t.1)))
  naturality S T i := by
    apply ModuleCat.hom_ext
    apply (chain_ext (S := S) (p := p))
    intro t
    change Finsupp.linearCombination ℤ _ ((freeTuples I p).map i (gen t)) =
      P.map i (Finsupp.linearCombination ℤ _ (gen t))
    rw [freeTuples_map_gen]
    simp only [gen, Finsupp.linearCombination_single, one_smul]
    change P.map (homOfLE (t.2.trans (leOfHom i))) (f t.1) =
      P.map i (P.map (homOfLE t.2) (f t.1))
    rw [← ModuleCat.comp_apply, ← P.map_comp]
    rfl

private theorem liftGenerators_gen {I : Type v} {p : ℕ} {P : Diagram I}
    (f : ∀ t : Fin (p + 1) → I, P.obj (Set.range t)) (S : Set I) (t : TupleOn S p) :
    (liftGenerators f).app S (gen t) = P.map (homOfLE t.2) (f t.1) := by
  change Finsupp.linearCombination ℤ _ (Finsupp.single t 1) = _
  rw [Finsupp.linearCombination_single, one_smul]

private theorem diagram_ext {I : Type v} {p : ℕ} {P : Diagram I} {f g : freeTuples I p ⟶ P}
    (h : ∀ t : Fin (p + 1) → I, f.app (Set.range t) (gen (ownTuple t)) =
      g.app (Set.range t) (gen (ownTuple t))) : f = g := by
  apply NatTrans.ext
  funext S
  apply ModuleCat.hom_ext
  apply (chain_ext (S := S) (p := p))
  intro t
  let i : Set.range t.1 ⟶ S := homOfLE t.2
  have apply_naturality (a : freeTuples I p ⟶ P) :
      a.app S (gen t) = P.map i (a.app (Set.range t.1) (gen (ownTuple t.1))) := by
    have ha := congrArg (fun m : (freeTuples I p).obj (Set.range t.1) ⟶ P.obj S =>
      m (gen (ownTuple t.1))) (a.naturality i)
    change a.app S ((freeTuples I p).map i (gen (ownTuple t.1))) = _ at ha
    rw [freeTuples_map_gen] at ha
    exact ha
  rw [apply_naturality, apply_naturality, h]

private def faceMap {I : Type v} {p q : ℕ}
    (i : Fin (p + 1) → Fin (q + 1)) : freeTuples I q ⟶ freeTuples I p :=
  liftGenerators fun t => gen (restrictPositions (ownTuple t) i)

private theorem faceMap_gen {I : Type v} {S : Set I} {p q : ℕ}
    (i : Fin (p + 1) → Fin (q + 1)) (t : TupleOn S q) :
    (faceMap i).app S (gen t) = gen (restrictPositions t i) := by
  rw [faceMap, liftGenerators_gen, freeTuples_map_gen]
  rfl

private def simplices (I : Type v) : SimplicialObject (Diagram I) where
  obj n := freeTuples I n.unop.len
  map f := faceMap f.unop.toOrderHom
  map_id n := by
    apply diagram_ext
    intro t
    rw [faceMap_gen]
    rfl
  map_comp f g := by
    apply diagram_ext
    intro t
    change (faceMap (f ≫ g).unop.toOrderHom).app _ (gen (ownTuple t)) =
      (faceMap g.unop.toOrderHom).app _
        ((faceMap f.unop.toOrderHom).app _ (gen (ownTuple t)))
    rw [faceMap_gen, faceMap_gen, faceMap_gen]
    rfl

private def omissionSign {n : ℕ} (i : Fin n) : ℤ := (-1) ^ i.val

private def boundary {I : Type v} (p : ℕ) : freeTuples I (p + 1) ⟶ freeTuples I p :=
  ∑ i : Fin (p + 2), omissionSign i • faceMap i.succAbove

private theorem boundary_squared {I : Type v} (p : ℕ) :
    boundary (I := I) (p + 1) ≫ boundary p = 0 :=
  AlgebraicTopology.AlternatingFaceMapComplex.d_squared (simplices I) p

private abbrev tupleChains (I : Type v) : ChainComplex (Diagram I) ℕ :=
  ChainComplex.of (freeTuples I) boundary boundary_squared

private theorem boundary_eq {I : Type v} (p : ℕ) :
    (tupleChains I).d (p + 1) p = boundary p :=
  ChainComplex.of_d _ _ p

private theorem boundary_gen {I : Type v} {S : Set I} {p : ℕ} (t : TupleOn S (p + 1)) :
    ((tupleChains I).d (p + 1) p).app S (gen t) =
      ∑ i : Fin (p + 2), omissionSign i • gen (restrictPositions t i.succAbove) := by
  rw [boundary_eq]
  unfold boundary
  simp only [NatTrans.app_sum, NatTrans.app_zsmul, ModuleCat.hom_sum,
    ModuleCat.hom_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_congr rfl fun i _ => congrArg (omissionSign i • ·) (faceMap_gen _ t)


private def permSign {m : ℕ} (σ : Equiv.Perm (Fin m)) : ℤ :=
  ↑(Equiv.Perm.sign σ)

private theorem permSign_mul {m : ℕ} (σ τ : Equiv.Perm (Fin m)) :
    permSign (σ * τ) = permSign σ * permSign τ := by simp [permSign]

private theorem permSign_sq {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    permSign σ * permSign σ = 1 := by
  simp [permSign]

private theorem omissionSign_sq {m : ℕ} (i : Fin m) :
    omissionSign i * omissionSign i = 1 := by
  rw [omissionSign, ← mul_pow]
  simp

/-- The permutation of the complementary positions after deleting position `i`. -/
private def deletePerm {p : ℕ} (σ : Equiv.Perm (Fin (p + 2))) (i : Fin (p + 2)) :
    Equiv.Perm (Fin (p + 1)) :=
  (finSuccAboveEquiv i).trans
    ((σ.subtypeEquiv fun j => (σ.injective.ne_iff (x := j) (y := i)).symm).trans (finSuccAboveEquiv (σ i)).symm)

private theorem deletePerm_apply {p : ℕ} (σ : Equiv.Perm (Fin (p + 2)))
    (i : Fin (p + 2)) (j : Fin (p + 1)) :
    (σ i).succAbove (deletePerm σ i j) = σ (i.succAbove j) := by
  change ((finSuccAboveEquiv (σ i)) (deletePerm σ i j)).val = _
  simp [deletePerm, finSuccAboveEquiv_apply]

private theorem deletePerm_sign {p : ℕ} (σ : Equiv.Perm (Fin (p + 2))) (i : Fin (p + 2)) :
    omissionSign i * permSign (deletePerm σ i) = permSign σ * omissionSign (σ i) := by
  have h : σ * Equiv.Perm.decomposeFin'Symm i 1 =
      Equiv.Perm.decomposeFin'Symm (σ i) (deletePerm σ i) := by
    ext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp
    · simp [deletePerm_apply]
  have h' := congrArg permSign h
  rw [permSign_mul] at h'
  simp [permSign] at h'
  change permSign σ * omissionSign i = omissionSign (σ i) * permSign (deletePerm σ i) at h'
  calc
    omissionSign i * permSign (deletePerm σ i) =
        (omissionSign (σ i) * omissionSign (σ i)) *
          (omissionSign i * permSign (deletePerm σ i)) := by rw [omissionSign_sq, one_mul]
    _ = omissionSign (σ i) *
          (omissionSign i * (omissionSign (σ i) * permSign (deletePerm σ i))) := by ring
    _ = permSign σ * omissionSign (σ i) := by
      rw [← h']
      calc
        _ = (omissionSign i * omissionSign i) * (permSign σ * omissionSign (σ i)) := by ring
        _ = _ := by rw [omissionSign_sq, one_mul]

section Sorting

variable {I : Type v} [LinearOrder I]

private def sortedGen {S : Set I} {p : ℕ} (t : TupleOn S p) : Chains S p :=
  if Function.Injective t.1 then
    permSign (Tuple.sort t.1) • gen (restrictPositions t (Tuple.sort t.1))
  else 0

private def sorting (p : ℕ) : freeTuples I p ⟶ freeTuples I p :=
  liftGenerators (fun t => sortedGen (ownTuple t))

private theorem sorting_gen {S : Set I} {p : ℕ} (t : TupleOn S p) :
    (sorting p).app S (gen t) = sortedGen t := by
  rw [sorting, liftGenerators_gen]
  by_cases h : Function.Injective t.1
  · simp only [sortedGen, ownTuple, h, ↓reduceIte, map_zsmul]
    change permSign (Tuple.sort t.1) •
      ((freeTuples I p).map (homOfLE t.2)) (gen (restrictPositions (ownTuple t.1) (Tuple.sort t.1))) = _
    rw [freeTuples_map_gen]
    rfl
  · simp [sortedGen, ownTuple, h]

private theorem sortedGen_increasing {S : Set I} {p : ℕ} (t : TupleOn S p)
    (h : StrictMono t.1) : sortedGen t = gen t := by
  rw [sortedGen, ite_eq_left h.injective, (Tuple.sort_eq_refl_iff_monotone).2 h.monotone]
  simp [permSign, restrictPositions]

private theorem sortedGen_perm {S : Set I} {p : ℕ} (t : TupleOn S p)
    (σ : Equiv.Perm (Fin (p + 1))) :
    sortedGen (restrictPositions t σ) = permSign σ • sortedGen t := by
  have hs := Tuple.comp_perm_comp_sort_eq_comp_sort (f := t.1) (σ := σ)
  change (t.1 ∘ σ) ∘ Tuple.sort (t.1 ∘ σ) = _ at hs
  by_cases ht : Function.Injective t.1
  · have hperm : σ * Tuple.sort (t.1 ∘ σ) = Tuple.sort t.1 := by
      ext i : 1
      exact ht (congrFun hs i)
    have hsign : permSign (Tuple.sort (t.1 ∘ σ)) = permSign σ * permSign (Tuple.sort t.1) := by
      rw [← hperm, permSign_mul, ← mul_assoc, permSign_sq, one_mul]
    have heq : restrictPositions (restrictPositions t σ) (Tuple.sort (t.1 ∘ σ)) =
        restrictPositions t (Tuple.sort t.1) := Subtype.ext hs
    simp only [sortedGen, restrictPositions, ht, ht.comp σ.injective, ↓reduceIte]
    change permSign (Tuple.sort (t.1 ∘ σ)) •
        gen (restrictPositions (restrictPositions t σ) (Tuple.sort (t.1 ∘ σ))) =
      permSign σ • (permSign (Tuple.sort t.1) • gen (restrictPositions t (Tuple.sort t.1)))
    rw [heq, hsign, mul_smul]
  · have hn : ¬ Function.Injective (t.1 ∘ σ) := fun h =>
      ht (fun x y hxy => by
        obtain ⟨x, rfl⟩ := σ.surjective x
        obtain ⟨y, rfl⟩ := σ.surjective y
        exact congrArg σ (h hxy))
    simp [sortedGen, restrictPositions, ht, hn]

private theorem sortBoundary_perm {S : Set I} {p : ℕ} (t : TupleOn S (p + 1))
    (σ : Equiv.Perm (Fin (p + 2))) :
    (∑ i : Fin (p + 2), omissionSign i • sortedGen (restrictPositions
      (restrictPositions t σ) i.succAbove)) =
    permSign σ • ∑ i : Fin (p + 2), omissionSign i • sortedGen (restrictPositions t i.succAbove) := by
  rw [← Equiv.sum_comp σ (fun i => omissionSign i • sortedGen (restrictPositions t i.succAbove)),
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : restrictPositions (restrictPositions t σ) i.succAbove =
      restrictPositions (restrictPositions t (σ i).succAbove) (deletePerm σ i) :=
    Subtype.ext (funext fun j => congrArg t.1 (deletePerm_apply σ i j).symm)
  rw [h, sortedGen_perm, ← mul_smul, ← mul_smul, deletePerm_sign]

private theorem sortBoundary_repeated {S : Set I} {p : ℕ} (t : TupleOn S (p + 1))
    (ht : ¬ Function.Injective t.1) :
    (∑ i : Fin (p + 2), omissionSign i • sortedGen (restrictPositions t i.succAbove)) = 0 := by
  classical
  rw [Function.Injective] at ht
  push Not at ht
  obtain ⟨i, j, he, hne⟩ := ht
  have hs : restrictPositions t (Equiv.swap i j) = t := by
    apply Subtype.ext
    funext k
    change t.1 (Equiv.swap i j k) = t.1 k
    by_cases hi : k = i
    · subst k; simpa using he.symm
    by_cases hj : k = j
    · subst k; simpa using he
    rw [Equiv.swap_apply_of_ne_of_ne hi hj]
  have h := sortBoundary_perm t (Equiv.swap i j)
  rw [hs, permSign, Equiv.Perm.sign_swap hne, Units.val_neg, Units.val_one, neg_one_zsmul] at h
  ext x
  have hx := congrArg (fun l : Chains S p => l x) h
  change _ = -_ at hx
  simp only [Finsupp.zero_apply]
  omega

private theorem sorting_comm (p : ℕ) :
    sorting (I := I) (p + 1) ≫ (tupleChains I).d (p + 1) p =
      (tupleChains I).d (p + 1) p ≫ sorting p := by
  apply diagram_ext
  intro t
  let a := ownTuple t
  change ((tupleChains I).d (p + 1) p).app _ ((sorting (p + 1)).app _ (gen a)) =
    (sorting p).app _ (((tupleChains I).d (p + 1) p).app _ (gen a))
  rw [sorting_gen, boundary_gen, map_sum]
  simp only [map_zsmul]
  rw [show (∑ i : Fin (p + 2), omissionSign i •
      (sorting p).app (Set.range t) (gen (restrictPositions a i.succAbove))) =
      ∑ i : Fin (p + 2), omissionSign i • sortedGen (restrictPositions a i.succAbove) by
    exact Finset.sum_congr rfl fun i _ => congrArg (omissionSign i • ·) (sorting_gen _)]
  by_cases ht : Function.Injective t
  · let σ := Tuple.sort t
    let b := restrictPositions a σ
    have hb : StrictMono b.1 :=
      (Tuple.monotone_sort t).strictMono_of_injective (ht.comp σ.injective)
    have h : sortedGen a = permSign σ • gen b := ite_eq_left ht
    rw [h, map_zsmul, boundary_gen]
    have hh := sortBoundary_perm a σ
    change (∑ i : Fin (p + 2), omissionSign i • sortedGen (restrictPositions b i.succAbove)) =
      _ at hh
    have hfaces (i : Fin (p + 2)) : sortedGen (restrictPositions b i.succAbove) =
        gen (restrictPositions b i.succAbove) :=
      sortedGen_increasing _ (hb.comp i.strictMono_succAbove)
    rw [show (∑ i : Fin (p + 2), omissionSign i • sortedGen (restrictPositions b i.succAbove)) =
        ∑ i : Fin (p + 2), omissionSign i • gen (restrictPositions b i.succAbove) by simp only [hfaces]]
      at hh
    rw [hh, ← mul_smul, permSign_sq, one_smul]
  · rw [show sortedGen a = 0 from ite_eq_right ht, map_zero]
    exact (sortBoundary_repeated a ht).symm

private def sortingMap : tupleChains I ⟶ tupleChains I :=
  ChainComplex.ofHom (fun p => sorting p) sorting_comm

private theorem sorting_zero : (sortingMap (I := I)).f 0 = 𝟙 _ := by
  apply diagram_ext
  intro t
  change (sorting 0).app _ (gen (ownTuple t)) = gen (ownTuple t)
  rw [sorting_gen]
  exact sortedGen_increasing _ (fun i j h => (not_lt_of_ge (le_of_eq (show j = i from Fin.ext (by omega))) h).elim)

end Sorting

section Contraction

variable {I : Type v}

private def prepend {S : Set I} {p : ℕ} (a : S) (t : TupleOn S p) : TupleOn S (p + 1) :=
  ⟨Fin.cons a.1 t.1, fun _ ⟨j, hj⟩ => by
    subst_vars
    refine Fin.cases a.2 (fun k => ?_) j
    exact t.2 ⟨k, rfl⟩⟩

private def cone {S : Set I} {p : ℕ} (a : S) : Chains S p →ₗ[ℤ] Chains S (p + 1) :=
  Finsupp.lmapDomain ℤ ℤ (prepend a)

private theorem cone_gen {S : Set I} {p : ℕ} (a : S) (t : TupleOn S p) :
    cone a (gen t) = gen (prepend a t) := by simp [cone, gen]

private theorem cone_boundary {S : Set I} (a : S) (p : ℕ) (z : Chains S (p + 1)) :
    ((tupleChains I).d (p + 2) (p + 1)).app S (cone a z) +
      cone a (((tupleChains I).d (p + 1) p).app S z) = z := by
  let d := fun j => ((tupleChains I).d (j + 1) j).app S
  have h : (d (p + 1)).hom.comp (cone a) + (cone a).comp (d p).hom = LinearMap.id := by
    apply (chain_ext (S := S) (p := p + 1))
    intro t
    change d (p + 1) (cone a (gen t)) + cone a (d p (gen t)) = gen t
    dsimp only [d]
    rw [cone_gen, boundary_gen, boundary_gen, Fin.sum_univ_succ]
    simp only [omissionSign, Fin.val_zero, pow_zero, one_zsmul, Fin.val_succ, pow_succ,
      mul_neg, mul_one, neg_smul, map_sum, map_zsmul]
    rw [show restrictPositions (prepend a t) (0 : Fin (p + 3)).succAbove = t from rfl]
    rw [Finset.sum_neg_distrib, add_assoc]
    conv_rhs => rw [← add_zero (gen t)]
    congr 1
    rw [neg_add_eq_zero]
    exact Finset.sum_congr rfl fun i _ => by
      rw [cone_gen]
      congr 2
      apply Subtype.ext
      exact (Fin.cons_comp_succ_succAbove a.1 t.1 i)
  exact LinearMap.congr_fun h z

/-- Fill a supported positive-degree cycle by coning it at the first vertex
of its input tuple. Passing to larger sets commutes with the resulting map. -/
private def fill {p : ℕ} (e : freeTuples I (p + 1) ⟶ freeTuples I (p + 1)) :
    freeTuples I (p + 1) ⟶ freeTuples I (p + 2) :=
  liftGenerators fun t =>
    cone (⟨t 0, Set.mem_range_self 0⟩ : Set.range t) (e.app _ (gen (ownTuple t)))

private theorem fill_boundary {p : ℕ} (e : freeTuples I (p + 1) ⟶ freeTuples I (p + 1))
    (he : e ≫ (tupleChains I).d (p + 1) p = 0) :
    fill e ≫ (tupleChains I).d (p + 2) (p + 1) = e := by
  apply diagram_ext
  intro t
  let a := ownTuple t
  have hz : ((tupleChains I).d (p + 1) p).app (Set.range t)
      (e.app (Set.range t) (gen a)) = 0 := by
    have hh := congrArg (fun f : freeTuples I (p + 1) ⟶ freeTuples I p =>
      (f.app (Set.range t)) (gen a)) he
    change ((tupleChains I).d (p + 1) p).app (Set.range t)
      (e.app (Set.range t) (gen a)) = (0 : Chains (Set.range t) p) at hh
    exact hh
  change ((tupleChains I).d (p + 2) (p + 1)).app _ ((fill e).app _ (gen a)) = _
  rw [fill, liftGenerators_gen]
  change ((tupleChains I).d (p + 2) (p + 1)).app _ ((freeTuples I (p + 2)).map
    (𝟙 (Set.range t)) (cone (⟨t 0, Set.mem_range_self 0⟩ : Set.range t)
      (e.app _ (gen a)))) = _
  rw [((freeTuples I (p + 2)).map_id (Set.range t)), ModuleCat.id_apply]
  simpa only [hz, map_zero, add_zero] using
    cone_boundary (⟨t 0, Set.mem_range_self 0⟩ : Set.range t) p (e.app _ (gen a))

variable [LinearOrder I]

private def sortingHomotopy : Homotopy (𝟙 (tupleChains I)) (sortingMap (I := I)) := by
  refine Homotopy.equivSubZero.symm ?_
  let C := tupleChains I
  let e : C ⟶ C := 𝟙 C - sortingMap
  have e₀ : e.f 0 = 0 := by
    change (𝟙 (freeTuples I 0)) - (sortingMap (I := I)).f 0 = 0
    rw [sorting_zero, sub_self]
  have lift (n : ℕ) (a : C.X n ⟶ C.X (n + 1))
      (h : (e.f (n + 1) - C.d (n + 1) n ≫ a) ≫ C.d (n + 1) n = 0) :
      Σ' b : C.X (n + 1) ⟶ C.X (n + 2),
        e.f (n + 1) = C.d (n + 1) n ≫ a + b ≫ C.d (n + 2) (n + 1) := by
    refine ⟨fill (e.f (n + 1) - C.d (n + 1) n ≫ a), ?_⟩
    rw [fill_boundary _ h]
    abel
  have h₁ := lift 0 0 (by
    rw [Limits.comp_zero, sub_zero, e.comm, e₀, Limits.comp_zero])
  refine Homotopy.mkInductive e 0 (by simpa using e₀) h₁.1 h₁.2 (fun n A => ?_)
  rcases A with ⟨a, b, h⟩
  apply lift (n + 1) b
  rw [Preadditive.sub_comp, Category.assoc, e.comm, h, Preadditive.comp_add,
    ← Category.assoc (C.d (n + 2) (n + 1)) (C.d (n + 1) n), C.d_comp_d,
    Limits.zero_comp, zero_add, sub_self]

end Contraction

section Coefficients

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
  {U : Opens X} {I : Type v} (c : Cover U I) (F : PresheafOfModules.{w} R.obj)

private theorem le_tupleOpen {W : Opens X} {S : Set I}
    (h : ∀ i ∈ S, W ≤ c.opens i) {p : ℕ} (t : TupleOn S p) :
    W ≤ tupleOpen c t.1 := by
  rw [tupleOpen_eq_iInf]
  exact le_iInf fun i => h _ (t.2 (Set.mem_range_self i))

private theorem tupleOpen_le_each {p : ℕ} (t : Fin (p + 1) → I) :
    ∀ i ∈ Set.range t, tupleOpen c t ≤ c.opens i := by
  rintro i ⟨j, rfl⟩
  rw [tupleOpen_eq_iInf]
  exact iInf_le _ j

private def readAt {W : Opens X} (hW : W ≤ U) {S : Set I}
    (hS : ∀ i ∈ S, W ≤ c.opens i) {p : ℕ} (x : Cochains R F c p) :
    Chains S p →ₗ[ℤ] localSections R F U W hW :=
  Finsupp.linearCombination ℤ fun t : TupleOn S p =>
    localRestriction R F U hW (tupleOpen_le c t.1) (le_tupleOpen c hS t) (x t.1)

private theorem readAt_gen {W : Opens X} (hW : W ≤ U) {S : Set I}
    (hS : ∀ i ∈ S, W ≤ c.opens i) {p : ℕ} (x : Cochains R F c p) (t : TupleOn S p) :
    readAt R c F hW hS x (gen t) =
      localRestriction R F U hW (tupleOpen_le c t.1) (le_tupleOpen c hS t) (x t.1) := by
  simp [readAt, gen]

private theorem readAt_restrict {V W : Opens X} (hV : V ≤ U) (hW : W ≤ U) (hWV : W ≤ V)
    {S T : Set I} (hS : ∀ i ∈ S, V ≤ c.opens i) (hT : ∀ i ∈ T, W ≤ c.opens i)
    (hST : S ⟶ T) {p : ℕ} (x : Cochains R F c p) (z : Chains S p) :
    localRestriction R F U hW hV hWV (readAt R c F hV hS x z) =
      readAt R c F hW hT x ((freeTuples I p).map hST z) := by
  let f := (localRestriction R F U hW hV hWV).toAddMonoidHom.toIntLinearMap
  have h : f.comp (readAt R c F hV hS x) =
      (readAt R c F hW hT x).comp ((freeTuples I p).map hST).hom := by
    apply (chain_ext (S := S) (p := p))
    intro t
    change localRestriction R F U hW hV hWV (readAt R c F hV hS x (gen t)) =
      readAt R c F hW hT x ((freeTuples I p).map hST (gen t))
    rw [freeTuples_map_gen, readAt_gen, readAt_gen]
    exact (F.map_comp_apply (homOfLE (le_tupleOpen c hS t)).op (homOfLE hWV).op _).symm
  exact LinearMap.congr_fun h z

/-- A supported tuple chain operation acts contravariantly on cochains.
At an output tuple each chain is evaluated on the intersection of that tuple. -/
private def action {p q : ℕ} (a : freeTuples I q ⟶ freeTuples I p) :
    Cochains R F c p →ₗ[sectionRing R U] Cochains R F c q where
  toFun x t :=
    readAt R c F (tupleOpen_le c t) (tupleOpen_le_each c t) x
      (a.app (Set.range t) (gen (ownTuple t)))
  map_add' x y := by
    funext t
    simp only [readAt, Finsupp.linearCombination_apply, Pi.add_apply,
      map_add, zsmul_add, Finsupp.sum_add]
  map_smul' k x := by
    funext t
    simp only [readAt, Finsupp.linearCombination_apply, Pi.smul_apply,
      LinearMap.map_smul, RingHom.id_apply, Finsupp.sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

private theorem readAt_action {V : Opens X} (hV : V ≤ U)
    {S : Set I} (hS : ∀ i ∈ S, V ≤ c.opens i)
    {p q : ℕ} (a : freeTuples I q ⟶ freeTuples I p) (x : Cochains R F c p) (z : Chains S q) :
    readAt R c F hV hS (action R c F a x) z =
      readAt R c F hV hS x (a.app S z) := by
  have h : readAt R c F hV hS (action R c F a x) =
      (readAt R c F hV hS x).comp (a.app S).hom := by
    apply (chain_ext (S := S) (p := q))
    intro t
    rw [readAt_gen]
    let j : Set.range t.1 ⟶ S := homOfLE t.2
    change localRestriction R F U hV (tupleOpen_le c t.1) (le_tupleOpen c hS t)
        (readAt R c F (tupleOpen_le c t.1) (tupleOpen_le_each c t.1) x
          (a.app (Set.range t.1) (gen (ownTuple t.1)))) = readAt R c F hV hS x (a.app S (gen t))
    rw [readAt_restrict R c F _ _ _ _ _ j]
    have hn := congrArg
      (fun f : (freeTuples I q).obj (Set.range t.1) ⟶ (freeTuples I p).obj S =>
        f (gen (ownTuple t.1))) (a.naturality j)
    change a.app S ((freeTuples I q).map j (gen (ownTuple t.1))) =
      (freeTuples I p).map j (a.app (Set.range t.1) (gen (ownTuple t.1))) at hn
    rw [freeTuples_map_gen] at hn
    rw [← hn]
    rfl
  exact LinearMap.congr_fun h z

private theorem action_comp {p q s : ℕ} (a : freeTuples I s ⟶ freeTuples I q)
    (b : freeTuples I q ⟶ freeTuples I p) :
    action R c F (a ≫ b) = (action R c F a).comp (action R c F b) := by
  ext x t
  exact (readAt_action R c F _ (tupleOpen_le_each c t) b x _).symm

private theorem action_id (p : ℕ) :
    action R c F (𝟙 (freeTuples I p)) = LinearMap.id := by
  ext x t
  change readAt R c F _ (tupleOpen_le_each c t) x (gen (ownTuple t)) = x t
  rw [readAt_gen]
  change F.map (𝟙 (op (tupleOpen c t))) (x t) = x t
  exact congr($(F.presheaf.map_id (op (tupleOpen c t))) (x t))

private theorem action_add {p q : ℕ} (a b : freeTuples I q ⟶ freeTuples I p) :
    action R c F (a + b) = action R c F a + action R c F b := by
  ext x t
  exact map_add (readAt R c F _ (tupleOpen_le_each c t) x) _ _

private theorem action_zero {p q : ℕ} :
    action R c F (0 : freeTuples I q ⟶ freeTuples I p) = 0 := by
  ext x t
  exact map_zero (readAt R c F _ (tupleOpen_le_each c t) x)

private theorem action_boundary (p : ℕ) :
    action R c F ((tupleChains I).d (p + 1) p) = differential R F c p := by
  ext x t
  change readAt R c F _ (tupleOpen_le_each c t) x
    (((tupleChains I).d (p + 1) p).app _ (gen (ownTuple t))) = _
  rw [boundary_gen, map_sum]
  simp only [map_zsmul, differential, LinearMap.sum_apply, Finset.sum_apply,
    LinearMap.smul_apply, Pi.smul_apply]
  exact Finset.sum_congr rfl fun j _ => congrArg (omissionSign j • ·)
    (readAt_gen R c F _ (tupleOpen_le_each c t) x _)

private theorem action_naturality {G : PresheafOfModules.{w} R.obj} (f : F ⟶ G)
    {p q : ℕ} (a : freeTuples I q ⟶ freeTuples I p) :
    (action R c G a).comp (orderedCochainComponent R c f p) =
      (orderedCochainComponent R c f q).comp (action R c F a) := by
  ext x t
  change readAt R c G _ (tupleOpen_le_each c t) (orderedCochainComponent R c f p x) _ =
    f.app (op (tupleOpen c t)) (readAt R c F _ (tupleOpen_le_each c t) x _)
  simp only [readAt, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun j _ => congrArg (_ • ·) ?_
  exact (PresheafOfModules.naturality_apply f
    (homOfLE (le_tupleOpen c (tupleOpen_le_each c t) j)).op (x j.1)).symm

variable [LinearOrder I]

private theorem action_sorting (p : ℕ) :
    action R c F (sorting (I := I) p) =
      (signedExtensionComponent R c F p).comp (projectionComponent R c F p) := by
  ext x t
  change readAt R c F _ (tupleOpen_le_each c t) x
    ((sorting p).app _ (gen (ownTuple t))) = _
  rw [sorting_gen]
  by_cases ht : Function.Injective t
  · simp only [sortedGen, ownTuple, ht, ite_true, map_zsmul, signedExtensionComponent,
      LinearMap.comp_apply, LinearMap.pi_apply, dite_eq_left, LinearMap.smul_apply,
      projectionComponent, LinearMap.proj_apply]
    exact congrArg (permSign (Tuple.sort t) • ·)
      (readAt_gen R c F _ (tupleOpen_le_each c t) x _)
  · simp [sortedGen, ownTuple, ht, signedExtensionComponent]

/-- Extend a cochain by signed permutation, with zero at repeated tuples. -/
def signedExtension : increasingComplex R c F ⟶ orderedCochainComplex R c F :=
  CochainComplex.ofHom (fun p => ModuleCat.ofHom (signedExtensionComponent R c F p)) (by
    intro p
    rw [orderedCochainComplex_d, increasingComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := projectionComponent_surjective R c F p x
    have h := congrArg (action R c F) (sorting_comm (I := I) p)
    rw [action_comp, action_comp, action_boundary, action_sorting, action_sorting] at h
    change differential R F c p (signedExtensionComponent R c F p
        (projectionComponent R c F p y)) =
      signedExtensionComponent R c F (p + 1)
        (increasingDifferential R c F p (projectionComponent R c F p y))
    rw [projection_comm_apply]
    exact (LinearMap.congr_fun h y).symm)

theorem signedExtension_projection :
    signedExtension R c F ≫ projection R c F = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := projectionComponent_surjective R c F p x
  funext t
  change ((signedExtensionComponent R c F p).comp (projectionComponent R c F p)) y t.1 = y t.1
  rw [← action_sorting]
  change readAt R c F (tupleOpen_le c t.1) (tupleOpen_le_each c t.1) y
      ((sorting p).app _ (gen (ownTuple t.1))) = y t.1
  rw [sorting_gen, sortedGen_increasing _ t.2, readAt_gen]
  change F.map (𝟙 (op (tupleOpen c t.1))) (y t.1) = y t.1
  exact congr($(F.presheaf.map_id (op (tupleOpen c t.1))) (y t.1))

variable {F} {G : PresheafOfModules.{w} R.obj}

theorem projection_naturality (f : F ⟶ G) :
    orderedCochainMap R c f ≫ projection R c G =
      projection R c F ≫ increasingMap R c f := by
  apply HomologicalComplex.hom_ext
  intro p
  exact ModuleCat.hom_ext (increasingMap_projection R c f p).symm

theorem signedExtension_naturality (f : F ⟶ G) :
    increasingMap R c f ≫ signedExtension R c G =
      signedExtension R c F ≫ orderedCochainMap R c f := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := projectionComponent_surjective R c F p x
  have h := action_naturality R c F f (sorting (I := I) p)
  rw [action_sorting, action_sorting] at h
  change signedExtensionComponent R c G p
      (increasingMapComponent R c f p (projectionComponent R c F p y)) =
    orderedCochainComponent R c f p
      (signedExtensionComponent R c F p (projectionComponent R c F p y))
  rw [increasingMap_projection_apply]
  exact LinearMap.congr_fun h y

variable (F)

private def cochainHomotopyComponent (p q : ℕ) :
    (orderedCochainComplex R c F).X p ⟶ (orderedCochainComplex R c F).X q :=
  ModuleCat.ofHom (action R c F ((sortingHomotopy (I := I)).hom q p))

/-- The homotopy from the identity to restriction followed by signed extension. -/
def projectionExtensionHomotopy :
    Homotopy (𝟙 _) (projection R c F ≫ signedExtension R c F) where
  hom := cochainHomotopyComponent R c F
  zero p q h := by
    unfold cochainHomotopyComponent
    rw [(sortingHomotopy (I := I)).zero q p h, action_zero]
    rfl
  comm p := by
    let H := sortingHomotopy (I := I)
    have h := H.comm p
    rw [Homotopy.prevD_chainComplex] at h
    rw [dNext_eq _ (show (ComplexShape.up ℕ).Rel p (p + 1) from rfl),
      orderedCochainComplex_d, prevD_nat]
    apply ModuleCat.hom_ext
    cases p with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, zero_add] at h
      have h₀ := congrArg (action R c F (p := 0) (q := 0)) h
      rw [action_add, action_comp, action_boundary] at h₀
      change action R c F (𝟙 (freeTuples I 0)) =
        (action R c F (H.hom 0 1)).comp (differential R F c 0) +
          action R c F (sorting (I := I) 0) at h₀
      rw [action_id, action_sorting] at h₀
      have hd : (orderedCochainComplex R c F).d 0 0 = 0 :=
        (orderedCochainComplex R c F).shape _ _ (by decide)
      simp only [hd, Limits.comp_zero, add_zero]
      exact h₀
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex] at h
      have hn := congrArg (action R c F (p := n + 1) (q := n + 1)) h
      rw [action_add, action_add, action_comp, action_comp, action_boundary, action_boundary] at hn
      change action R c F (𝟙 (freeTuples I (n + 1))) =
        (differential R F c n).comp (action R c F (H.hom n (n + 1))) +
          (action R c F (H.hom (n + 1) (n + 2))).comp (differential R F c (n + 1)) +
          action R c F (sorting (I := I) (n + 1)) at hn
      rw [action_id, action_sorting] at hn
      rw [Nat.add_sub_cancel, orderedCochainComplex_d]
      change LinearMap.id =
        (action R c F (H.hom (n + 1) (n + 2))).comp (differential R F c (n + 1)) +
          (differential R F c n).comp (action R c F (H.hom n (n + 1))) +
          (signedExtensionComponent R c F (n + 1)).comp (projectionComponent R c F (n + 1))
      rw [add_comm (a := (action R c F (H.hom (n + 1) (n + 2))).comp
        (differential R F c (n + 1)))]
      exact hn

variable {F}

theorem projectionExtensionHomotopy_naturality (f : F ⟶ G) (p q : ℕ) :
    (orderedCochainMap R c f).f p ≫ (projectionExtensionHomotopy R c G).hom p q =
      (projectionExtensionHomotopy R c F).hom p q ≫ (orderedCochainMap R c f).f q :=
  ModuleCat.hom_ext (action_naturality R c F f ((sortingHomotopy (I := I)).hom q p))

/-- The all-tuples and increasing-index models are homotopy equivalent over the section ring. -/
def homotopyEquiv : HomotopyEquiv (orderedCochainComplex R c F) (increasingComplex R c F) where
  hom := projection R c F
  inv := signedExtension R c F
  homotopyHomInvId := (projectionExtensionHomotopy R c F).symm
  homotopyInvHomId := Homotopy.ofEq (signedExtension_projection R c F)

end Coefficients

/-- The specified signed deformation retraction, natural in the coefficients. -/
theorem comparison : comparisonType.{u,r,v,w} := by
  intro X R U I _ _ c
  exact ⟨fun F => signedExtension R c F, fun _ _ => rfl,
    fun F => signedExtension_projection R c F,
    fun _ _ f => projection_naturality R c f, fun _ _ f => signedExtension_naturality R c f,
    fun F => projectionExtensionHomotopy R c F,
    fun _ _ f p q => projectionExtensionHomotopy_naturality R c f p q⟩

end DerivedFormalization.OrderedCechComparison
