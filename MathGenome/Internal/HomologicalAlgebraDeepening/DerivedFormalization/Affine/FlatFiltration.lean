import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.FlatFiltration
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.Tensor
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Basis.VectorSpace

open CategoryTheory CategoryTheory.Limits
open scoped Classical DirectSum TensorProduct

universe u v w z

namespace DerivedFormalization.Affine.FlatFiltration

open Specs.DerivedFormalization.Affine.FlatFiltration
open Specs.DerivedFormalization.Affine.Tensor (ModuleTensor term act pure signedBimodule
  regular)
open Specs.DerivedFormalization.DG.HomComplex (gradedHom component)
open Specs.DerivedFormalization.DG.BalancedTensor (Raw Balance rawTmul)
open Tensor

noncomputable section

variable {k : Type u} [Field k] [CharZero k]
variable {A : CommDGAlgebra.{u,v} k}

local notation "d[" M "," n "]" => differential M n
local notation "φ[" f "," n "]" => HomologicalComplex.Hom.f (RightDGModuleHomModel.app f ()) n
local notation "γ[" f "," n "]" => component f () n n (add_zero n)

private theorem acyclic_iso {M N : A.Module} (e : M ≅ N)
    (h : RightDGModule.Acyclic M) : RightDGModule.Acyclic N := by
  intro a n
  have t := (HomologicalComplex.homologyFunctor _ _ n).mapIso
    ((RightDGModuleModel.eval a).mapIso e)
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ n).2
    (((HomologicalComplex.exactAt_iff_isZero_homology _ n).1 (h a n)).of_iso t.symm)

private theorem flat_left {M : A.Module} (h : KFlat M) {E : A.Module}
    (hE : RightDGModule.Acyclic E) : RightDGModule.Acyclic (over M E) :=
  acyclic_iso (swap E M) (h E hE)

private theorem flat_of_left {M : A.Module}
    (h : ∀ E : A.Module, RightDGModule.Acyclic E → RightDGModule.Acyclic (over M E)) :
    KFlat M :=
  fun E hE => acyclic_iso (swap M E) (h E hE)

private theorem chain_comm_at {M N : A.Module} (f : M ⟶ N) (n q : ℤ) (x : term M n) :
    φ[f,q] ((M.complex ()).d n q x) = (N.complex ()).d n q (φ[f,n] x) :=
  (CategoryTheory.congr_fun ((f.app ()).comm n q) x).symm

private theorem chain_comm {M N : A.Module} (f : M ⟶ N) (n : ℤ) (x : term M n) :
    φ[f,n+1] (d[M,n] x) = d[N,n] (φ[f,n] x) :=
  chain_comm_at f n (n+1) x

private theorem cycles_are_boundaries (M : A.Module) :
    RightDGModule.Acyclic M ↔ ∀ (n : ℤ) (x : term M n),
      d[M,n] x = 0 → ∃ y : term M (n-1), (M.complex ()).d (n-1) n y = x := by
  unfold RightDGModule.Acyclic Specs.DerivedFormalization.DG.Module.acyclic
  have exact_at (n : ℤ) :
      (M.complex ()).ExactAt n ↔ ∀ (x : term M n),
        d[M,n] x = 0 → ∃ y : term M (n-1), (M.complex ()).d (n-1) n y = x := by
    rw [HomologicalComplex.exactAt_iff' _ (n-1) n (n+1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff]
    rfl
  constructor
  · intro h n
    exact (exact_at n).1 (h () n)
  · rintro h ⟨⟩ n
    exact (exact_at n).2 (h n)

/-- Tensoring a graded-split short exact sequence preserves its degreewise splitting. -/
def tensorSplit {L M N : A.Module} {f : L ⟶ M} {g : M ⟶ N}
    (S : GradedSplit f g) (E : A.Module) :
    GradedSplit ((extension (𝟙 A) E).map f) ((extension (𝟙 A) E).map g) where
  zero := by
    apply RightDGModuleModel.hom_ext
    rintro ⟨⟩
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply pure_ext
    intro i j hij x y
    have hz : φ[g,i] (φ[f,i] x) = 0 :=
      congrArg (fun t : L ⟶ N => φ[t,i] x) S.zero
    change φ[(extension (𝟙 A) E).map g,n]
      (φ[(extension (𝟙 A) E).map f,n] (pure (𝟙 A) i j n hij x y)) = 0
    rw [map_first_pure, map_first_pure, hz, ← pair_apply]
    simp
  retraction := mapFirstGraded (𝟙 A) E S.retraction
  sectionMap := mapFirstGraded (𝟙 A) E S.sectionMap
  retract := by
    intro n
    refine LinearMap.congr_fun (f := (γ[mapFirstGraded (𝟙 A) E S.retraction,n]).hom.comp
      (φ[(extension (𝟙 A) E).map f,n]).hom) (g := LinearMap.id) ?_
    apply pure_ext
    intro i j h x y
    change γ[mapFirstGraded (𝟙 A) E S.retraction,n]
      (φ[(extension (𝟙 A) E).map f,n] (pure (𝟙 A) i j n h x y)) = _
    rw [map_first_pure, map_first_graded_pure (𝟙 A) E S.retraction i j n i n h
      (add_zero i) (add_zero n), S.retract]
    rfl
  section_id := by
    intro n
    refine LinearMap.congr_fun (f := (φ[(extension (𝟙 A) E).map g,n]).hom.comp
      (γ[mapFirstGraded (𝟙 A) E S.sectionMap,n]).hom) (g := LinearMap.id) ?_
    apply pure_ext
    intro i j h x y
    change φ[(extension (𝟙 A) E).map g,n]
      (γ[mapFirstGraded (𝟙 A) E S.sectionMap,n] (pure (𝟙 A) i j n h x y)) = _
    rw [map_first_graded_pure (𝟙 A) E S.sectionMap i j n i n h
      (add_zero i) (add_zero n), map_first_pure, S.section_id]
    rfl
  decompose := by
    intro n
    refine LinearMap.congr_fun (f :=
      (φ[(extension (𝟙 A) E).map f,n]).hom.comp
        (γ[mapFirstGraded (𝟙 A) E S.retraction,n]).hom +
      (γ[mapFirstGraded (𝟙 A) E S.sectionMap,n]).hom.comp
        (φ[(extension (𝟙 A) E).map g,n]).hom) (g := LinearMap.id) ?_
    apply pure_ext
    intro i j h x y
    change φ[(extension (𝟙 A) E).map f,n]
        (γ[mapFirstGraded (𝟙 A) E S.retraction,n] (pure (𝟙 A) i j n h x y)) +
      γ[mapFirstGraded (𝟙 A) E S.sectionMap,n]
        (φ[(extension (𝟙 A) E).map g,n] (pure (𝟙 A) i j n h x y)) = _
    rw [map_first_graded_pure (𝟙 A) E S.retraction i j n i n h (add_zero i) (add_zero n),
      map_first_pure, map_first_pure,
      map_first_graded_pure (𝟙 A) E S.sectionMap i j n i n h (add_zero i) (add_zero n),
      ← pure_add_left, S.decompose]
    rfl

private theorem split_acyclic {L M N : A.Module} {f : L ⟶ M} {g : M ⟶ N}
    (S : GradedSplit f g) (hL : RightDGModule.Acyclic L) (hN : RightDGModule.Acyclic N) :
    RightDGModule.Acyclic M := by
  let C : ShortComplex (ModuleCochain.{u,v} k) :=
    ShortComplex.mk (f.app ()) (g.app ()) (congrArg (fun t : L ⟶ N => t.app ()) S.zero)
  have hC : C.ShortExact := HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => by
    let D := C.map (HomologicalComplex.eval _ _ n)
    let s : D.Splitting :=
      { r := γ[S.retraction,n]
        s := γ[S.sectionMap,n]
        f_r := ModuleCat.hom_ext (LinearMap.ext (S.retract n))
        s_g := ModuleCat.hom_ext (LinearMap.ext (S.section_id n))
        id := ModuleCat.hom_ext (LinearMap.ext (S.decompose n)) }
    exact s.shortExact
  exact fun a => by
    cases a
    exact hC.acyclic_X₂ (hL ()) (hN ())

theorem kFlat_of_gradedSplit {L M N : A.Module} {f : L ⟶ M} {g : M ⟶ N}
    (S : GradedSplit f g) (hL : KFlat L) (hN : KFlat N) : KFlat M :=
  flat_of_left fun E hE => split_acyclic (tensorSplit S E) (flat_left hL hE) (flat_left hN hE)

/-- The cochain complex in any specified signed tensor model is the balanced tensor
complex, by the degree identifications and the differential formula on pure tensors. -/
private def tensorComplexIso (T : ModuleTensor.{u,v} k)
    (E M : A.Module) (h : T.Formulas (𝟙 A) M) :
    (over E M).complex () ≅ (T.obj (𝟙 A) E M).complex () :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (T.degree (𝟙 A) E M n).toModuleIso) (by
      intro n q hn
      obtain rfl : n+1=q := hn
      apply ModuleCat.hom_ext
      apply pure_ext
      intro i j hij x y
      change d[T.obj (𝟙 A) E M,n] (T.tmul (𝟙 A) i j n hij x y) =
        T.degree (𝟙 A) E M (n+1) (d[over E M,n] (pure (𝟙 A) i j n hij x y))
      rw [h.differential, d_pure, map_add]
      simp only [Units.smul_def, map_zsmul, ModuleTensor.tmul])

theorem model_kFlat_iff (T : ModuleTensor.{u,v} k)
    {M : A.Module} (h : T.Formulas (𝟙 A) M) : T.KFlat M ↔ KFlat M := by
  have transfer {K L : ModuleCochain.{u,v} k} (e : K ≅ L) (hK : K.Acyclic) : L.Acyclic := by
    intro n
    have a := (HomologicalComplex.homologyFunctor _ _ n).mapIso e
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ n).2
      (((HomologicalComplex.exactAt_iff_isZero_homology _ n).1 (hK n)).of_iso a.symm)
  constructor <;> intro hM E hE <;> rintro ⟨⟩
  · exact transfer (tensorComplexIso T E M h).symm (hM E hE ())
  · exact transfer (tensorComplexIso T E M h) (hM E hE ())

theorem gradedSplitFlatness : GradedSplitFlatness.{u,v} := by
  intro k _ _ T A h L M N f g S hL hN
  exact (model_kFlat_iff T (h M)).2 (kFlat_of_gradedSplit S
    ((model_kFlat_iff T (h L)).1 hL) ((model_kFlat_iff T (h N)).1 hN))

section Union

variable {L M N : A.Module} (E : A.Module)

private abbrev raw (M : A.Module) (n : ℤ) :=
  Raw (signedBimodule (𝟙 A) E) M () n

private abbrev balance (M : A.Module) (n : ℤ) :=
  Balance (signedBimodule (𝟙 A) E) M () n

private abbrev rawPure (i j n : ℤ) (h : i+j=n) (x : term M i) (y : term E j) :=
  rawTmul (signedBimodule (𝟙 A) E) M () () i j n h x y

private def rawMap (f : L ⟶ M) (n : ℤ) : raw E L n →ₗ[k] raw E M n :=
  DirectSum.lmap fun p => TensorProduct.map (φ[f,p.2.1.1]).hom LinearMap.id

private theorem rawMap_pure (f : L ⟶ M) (i j n : ℤ) (h : i+j=n)
    (x : term L i) (y : term E j) :
    rawMap E f n (rawPure E i j n h x y) = rawPure E i j n h (φ[f,i] x) y := by
  simp [rawMap, rawTmul]

private theorem raw_ext {n : ℤ} {P : Type*} [AddCommGroup P] [Module k P]
    {f g : raw E M n →ₗ[k] P}
    (h : ∀ i j (e : i+j=n) (x : term M i) (y : term E j),
      f (rawPure E i j n e x y) = g (rawPure E i j n e x y)) : f = g := by
  let : DecidableEq (Specs.DerivedFormalization.Affine.Tensor.dgCat A).Obj := Classical.decEq _
  apply DirectSum.linearMap_ext
  rintro ⟨⟨⟩, ⟨⟨i,j⟩, e⟩⟩
  apply TensorProduct.ext'
  intro x y
  simpa only [LinearMap.comp_apply, rawPure, rawTmul] using h i j e x y

private theorem rawMap_comp (f : L ⟶ M) (g : M ⟶ N) (n : ℤ) :
    rawMap E (f ≫ g) n = (rawMap E g n).comp (rawMap E f n) := by
  apply raw_ext E
  intro i j h x y
  simp only [LinearMap.comp_apply, rawMap_pure]
  rfl

private theorem rawMap_injective (f : L ⟶ M) (n : ℤ)
    (hf : ∀ i, Function.Injective (φ[f,i])) :
    Function.Injective (rawMap E f n) := by
  apply (DirectSum.lmap_injective _).2
  intro p
  let f' := (φ[f,p.2.1.1]).hom
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f'
    (LinearMap.ker_eq_bot.mpr (hf p.2.1.1))
  apply Function.LeftInverse.injective (g := TensorProduct.map g LinearMap.id)
  intro t
  change ((TensorProduct.map g LinearMap.id).comp (TensorProduct.map f' LinearMap.id)) t = t
  rw [← TensorProduct.map_comp, hg, LinearMap.id_comp, TensorProduct.map_id]
  rfl

private theorem rawMap_balance (f : L ⟶ M) (n : ℤ) :
    balance E L n ≤ (balance E M n).comap (rawMap E f n) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨⟩, ⟨⟩, i, l, j, h, x, a, y, rfl⟩
  change rawMap E f n (rawPure E (i+l) j n h (act L i l (i+l) rfl x a) y -
    rawPure E i (l+j) n _ x _) ∈ balance E M n
  rw [map_sub, rawMap_pure, rawMap_pure, f.comm_act]
  exact Submodule.subset_span ⟨(), (), i, l, j, h, φ[f,i] x, a, y, rfl⟩

private theorem rawMap_quot (f : L ⟶ M) (n : ℤ) (x : raw E L n) :
    φ[(extension (𝟙 A) E).map f,n] ((balance E L n).mkQ x) =
      (balance E M n).mkQ (rawMap E f n x) := by
  refine LinearMap.congr_fun (f := (φ[(extension (𝟙 A) E).map f,n]).hom.comp
    (balance E L n).mkQ) (g := (balance E M n).mkQ.comp (rawMap E f n)) ?_ x
  apply raw_ext E
  intro i j h a b
  simp only [LinearMap.comp_apply, rawMap_pure]
  exact map_first_pure (𝟙 A) f i j n h a b

variable {J : Type w} [LinearOrder J] {F : J ⥤ A.Module} (U : Union F M)

private theorem rawInclusion_comp {i j : J} (h : i ≤ j) (n : ℤ) (x : raw E (F.obj i) n) :
    rawMap E (U.incl j) n (rawMap E (F.map (homOfLE h)) n x) =
      rawMap E (U.incl i) n x := by
  change ((rawMap E (U.incl j) n).comp (rawMap E (F.map (homOfLE h)) n)) x = _
  rw [← rawMap_comp, U.comm h]

private theorem raw_lift (n : ℤ) (x : raw E M n) :
    ∃ (j : J) (y : raw E (F.obj j) n), rawMap E (U.incl j) n y = x := by
  let V (j : J) := LinearMap.range (rawMap E (U.incl j) n)
  have hm : Monotone V := by
    intro i j h
    rintro _ ⟨y, rfl⟩
    exact ⟨rawMap E (F.map (homOfLE h)) n y, rawInclusion_comp E U h n y⟩
  let S := ⨆ j, V j
  have hz : S.mkQ = 0 := by
    apply raw_ext E
    intro i j h a b
    obtain ⟨t, y, hy⟩ := U.exhaustive i a
    apply (Submodule.Quotient.mk_eq_zero S).2
    exact le_iSup V t ⟨rawPure E i j n h y b, by rw [rawMap_pure, hy]⟩
  let : Nonempty J := by obtain ⟨j, _, _⟩ := U.exhaustive n 0; exact ⟨j⟩
  exact (Submodule.mem_iSup_of_directed _ hm.directed_le).1
    ((Submodule.Quotient.mk_eq_zero S).1 (LinearMap.congr_fun hz x))

/-- A balancing relation in the union already holds at a stage, since each
generator has a first-factor coefficient in some stage. -/
private theorem balance_lift (n : ℤ) {x : raw E M n} (hx : x ∈ balance E M n) :
    ∃ (j : J) (y : raw E (F.obj j) n),
      y ∈ balance E (F.obj j) n ∧ rawMap E (U.incl j) n y = x := by
  let V (j : J) := (balance E (F.obj j) n).map (rawMap E (U.incl j) n)
  have hm : Monotone V := by
    intro i j h
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨rawMap E (F.map (homOfLE h)) n y, rawMap_balance E _ n hy,
      rawInclusion_comp E U h n y⟩
  have hs : balance E M n ≤ ⨆ j, V j := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨⟩, ⟨⟩, i, l, j, h, a, c, b, rfl⟩
    obtain ⟨t, y, hy⟩ := U.exhaustive i a
    apply le_iSup V t
    refine ⟨_, Submodule.subset_span ⟨(), (), i, l, j, h, y, c, b, rfl⟩, ?_⟩
    change rawMap E (U.incl t) n
      (rawPure E (i+l) j n h (act (F.obj t) i l (i+l) rfl y c) b -
        rawPure E i (l+j) n _ y _) =
      rawPure E (i+l) j n h (act M i l (i+l) rfl a c) b -
        rawPure E i (l+j) n _ a _
    rw [map_sub, rawMap_pure, rawMap_pure, (U.incl t).comm_act, hy]
  let : Nonempty J := by obtain ⟨j, _, _⟩ := U.exhaustive n 0; exact ⟨j⟩
  exact (Submodule.mem_iSup_of_directed _ hm.directed_le).1 (hs hx)

private theorem tensor_lift (n : ℤ) (x : term (over M E) n) :
    ∃ (j : J) (y : term (over (F.obj j) E) n),
      φ[(extension (𝟙 A) E).map (U.incl j),n] y = x := by
  obtain ⟨x, rfl⟩ := (balance E M n).mkQ_surjective x
  obtain ⟨j, y, rfl⟩ := raw_lift E U n x
  exact ⟨j, (balance E (F.obj j) n).mkQ y, rawMap_quot E _ n y⟩

/-- Vanishing in the union tensor is detected at a later stage. The
injectivity used here is on the raw direct sums of tensors over the field. -/
private theorem tensor_eventually_zero {i : J} (n : ℤ) (x : term (over (F.obj i) E) n)
    (hx : φ[(extension (𝟙 A) E).map (U.incl i),n] x = 0) :
    ∃ (j : J) (h : i ≤ j), φ[(extension (𝟙 A) E).map (F.map (homOfLE h)),n] x = 0 := by
  obtain ⟨x, rfl⟩ := (balance E (F.obj i) n).mkQ_surjective x
  rw [rawMap_quot] at hx
  obtain ⟨j, y, hy, he⟩ := balance_lift E U n ((Submodule.Quotient.mk_eq_zero _).1 hx)
  let t := max i j
  have hi : i ≤ t := le_max_left _ _
  have hj : j ≤ t := le_max_right _ _
  have eq : rawMap E (F.map (homOfLE hi)) n x = rawMap E (F.map (homOfLE hj)) n y := by
    apply rawMap_injective E (U.incl t) n (U.injective t)
    rw [rawInclusion_comp E U hi, rawInclusion_comp E U hj, he]
  refine ⟨t, hi, ?_⟩
  rw [rawMap_quot, eq]
  exact (Submodule.Quotient.mk_eq_zero _).2 (rawMap_balance E _ n hy)

private theorem tensorInclusion_comp {i j : J} (h : i ≤ j) (n : ℤ)
    (x : term (over (F.obj i) E) n) :
    φ[(extension (𝟙 A) E).map (U.incl j),n]
        (φ[(extension (𝟙 A) E).map (F.map (homOfLE h)),n] x) =
      φ[(extension (𝟙 A) E).map (U.incl i),n] x := by
  have q := ((extension (𝟙 A) E).map_comp (F.map (homOfLE h)) (U.incl j)).symm
  rw [U.comm h] at q
  exact congrArg (fun t : over (F.obj i) E ⟶ over M E => φ[t,n] x) q

include U in
private theorem union_acyclic (h : ∀ i, RightDGModule.Acyclic (over (F.obj i) E)) :
    RightDGModule.Acyclic (over M E) := by
  apply (cycles_are_boundaries _).2
  intro n x hx
  obtain ⟨i, y, rfl⟩ := tensor_lift E U n x
  rw [← chain_comm] at hx
  obtain ⟨j, hij, hz⟩ := tensor_eventually_zero E U _ _ hx
  rw [chain_comm] at hz
  obtain ⟨z, hz'⟩ := (cycles_are_boundaries _).1 (h j) n _ hz
  refine ⟨φ[(extension (𝟙 A) E).map (U.incl j),n-1] z, ?_⟩
  rw [← chain_comm_at ((extension (𝟙 A) E).map (U.incl j)) (n-1) n z, hz',
    tensorInclusion_comp E U hij]

include U in
theorem kFlat_of_union (h : ∀ i, KFlat (F.obj i)) : KFlat M :=
  flat_of_left fun E hE => union_acyclic E U fun i => flat_left (h i) hE

theorem unionFlatness : UnionFlatness.{u,v,w} := by
  intro k _ _ T A h J _ F M U hF
  exact (model_kFlat_iff T (h M)).2 (kFlat_of_union U fun i =>
    (model_kFlat_iff T (h (F.obj i))).1 (hF i))

end Union

private def unionAtLimit {J : Type w} [LinearOrder J] {F : J ⥤ A.Module} {M : A.Module}
    (U : Union F M) (hF : Continuous F) (j : J) (hj : Order.IsSuccLimit j) :
    Union (earlier F j) (F.obj j) where
  incl i := F.map (homOfLE i.property.le)
  comm {i t} h := by
    change F.map (homOfLE (show i.val ≤ t.val from h)) ≫
      F.map (homOfLE t.property.le) = _
    rw [← F.map_comp]
    rfl
  injective i n := by
    intro x y e
    apply U.injective i.val n
    have he := congrArg (fun t : F.obj i.val ⟶ M => φ[t,n] x) (U.comm i.property.le)
    have he' := congrArg (fun t : F.obj i.val ⟶ M => φ[t,n] y) (U.comm i.property.le)
    exact he.symm.trans ((congrArg (φ[U.incl j,n]) e).trans he')
  exhaustive := hF j hj

theorem filteredFlatness : FilteredFlatness.{u,v,w} := by
  intro k _ _ T A h J _ _ F M U hF hmin hs
  apply unionFlatness T h U
  intro j
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    by_cases hm : IsMin j
    · exact hmin j hm
    by_cases hp : Order.IsSuccPrelimit j
    · exact unionFlatness T h (unionAtLimit U hF j ⟨hm, hp⟩) (fun i => ih i.val i.property)
    · obtain ⟨i, hi⟩ := Order.not_isSuccPrelimit_iff.mp hp
      obtain ⟨Q, p, ⟨S⟩, hQ⟩ := hs i j hi
      exact gradedSplitFlatness T h S (ih i hi.lt) hQ

section Shift

open RightDGModule (GradedHom shift shiftHomologyIso)

variable (M E : A.Module) (s : ℤ)

private def fromShift : gradedHom (shift M s) M s :=
  GradedHom.mk (fun _ _ _ h => eqToHom (congrArg (fun t => term M t) h)) (by
    rintro ⟨⟩ ⟨⟩ i j n ir nr h hi hn x a
    subst ir nr
    rfl)

private def toShift : gradedHom M (shift M s) (-s) :=
  GradedHom.mk (fun _ i q h => eqToHom (congrArg (fun t => term M t)
    (show i=q+s by omega))) (by
    rintro ⟨⟩ ⟨⟩ i j n ir nr h hi hn x a
    obtain rfl : ir+s=i := by omega
    obtain rfl : nr+s=n := by omega
    rfl)

private def shiftForward (n : ℤ) :
    term (over (shift M s) E) n →ₗ[k] term (over M E) (n+s) :=
  (component (mapFirstGraded (𝟙 A) E (fromShift M s)) () n (n+s) rfl).hom

private def shiftBackward (n : ℤ) :
    term (over M E) (n+s) →ₗ[k] term (over (shift M s) E) n :=
  (component (mapFirstGraded (𝟙 A) E (toShift M s)) () (n+s) n (by omega)).hom

private theorem shiftForward_pure (i j n : ℤ) (h : i+j=n)
    (x : term (shift M s) i) (y : term E j) :
    shiftForward M E s n (pure (𝟙 A) i j n h x y) =
      pure (𝟙 A) (i+s) j (n+s) (by omega) x y := by
  exact map_first_graded_pure (𝟙 A) E (fromShift M s) i j n (i+s) (n+s) h rfl rfl x y

private theorem shiftBackward_pure (i j n : ℤ) (h : i+j=n)
    (x : term M (i+s)) (y : term E j) :
    shiftBackward M E s n (pure (𝟙 A) (i+s) j (n+s) (by omega) x y) =
      pure (𝟙 A) (M := shift M s) i j n h x y := by
  exact map_first_graded_pure (𝟙 A) E (toShift M s) (i+s) j (n+s) i n
    (by omega) (by omega) (by omega) x y

private def shiftTensorDegree (n : ℤ) :
    term (over (shift M s) E) n ≃ₗ[k] term (over M E) (n+s) :=
  LinearEquiv.ofLinearMap (shiftForward M E s n) (shiftBackward M E s n)
    (by
      apply pure_ext
      intro i j h x y
      obtain ⟨p, rfl⟩ : ∃ p : ℤ, p+s=i := ⟨i-s, by omega⟩
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [shiftBackward_pure M E s p j n (by omega), shiftForward_pure])
    (by
      apply pure_ext
      intro i j h x y
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [shiftForward_pure, shiftBackward_pure])

private def shiftTensorComplex :
    (over (shift M s) E).complex () ≅ (shift (over M E) s).complex () :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (shiftTensorDegree M E s n).toModuleIso)
    (by
      intro n q hn
      obtain rfl : n+1=q := hn
      apply ModuleCat.hom_ext
      apply pure_ext
      intro i j h x y
      change d[shift (over M E) s,n] (shiftForward M E s n (pure (𝟙 A) i j n h x y)) =
        shiftForward M E s (n+1) (d[over (shift M s) E,n] (pure (𝟙 A) i j n h x y))
      rw [shiftForward_pure, d_pure, map_add]
      simp only [Units.smul_def, map_zsmul]
      rw [shiftForward_pure, shiftForward_pure]
      change (s.negOnePow : ℤ) •
          ((over M E).complex ()).d (n+s) (n+1+s)
            (pure (𝟙 A) (i+s) j (n+s) _ x y) =
        pure (𝟙 A) (i+1+s) j (n+1+s) _
          ((s.negOnePow : ℤ) • (M.complex ()).d (i+s) (i+1+s) x) y +
        (i.negOnePow : ℤ) • pure (𝟙 A) (i+s) (j+1) (n+1+s) _ x (d[E,j] y)
      rw [d_pure_at (𝟙 A) (i+s) j (n+s) (i+1+s) (j+1) (n+1+s)
        (by omega) (by omega) rfl (by omega)]
      simp only [Units.smul_def, smul_add, pure_zsmul_left, smul_smul,
        ← Units.val_mul, ← Int.negOnePow_add]
      rw [show s+(i+s)=i+2*s by omega, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one])

theorem kFlat_shift (hM : KFlat M) : KFlat (shift M s) := by
  apply flat_of_left
  intro E hE
  rintro ⟨⟩ n
  have h := (flat_left hM hE) () (n+s)
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at h ⊢
  let e := (HomologicalComplex.homologyFunctor _ _ n).mapIso (shiftTensorComplex M E s)
  exact h.of_iso (e ≪≫ shiftHomologyIso (over M E) s () n)

theorem shiftFlatness : ShiftFlatness.{u,v} := by
  intro k _ _ T A h M s hM
  exact (model_kFlat_iff T (h _)).2 (kFlat_shift M s ((model_kFlat_iff T (h M)).1 hM))

end Shift

section DirectSum

variable {I : Type z} {P : I → A.Module} {M : A.Module} (S : GradedDirectSum P M)

private abbrev sumTerm (P : I → A.Module) (n : ℤ) :=
  ⨁ i : I, term (P i) n

private abbrev sumInj (P : I → A.Module) (n : ℤ) (i : I) :=
  DirectSum.lof k I (fun j => term (P j) n) i

private abbrev sumComponent (P : I → A.Module) (n : ℤ) (i : I) :=
  DirectSum.component k I (fun j => term (P j) n) i

private def sumEquiv (n : ℤ) : sumTerm P n ≃ₗ[k] term M n :=
  LinearEquiv.ofBijective (DirectSum.toModule k I _ fun i => (φ[S.incl i,n]).hom) (S.bijective n)

private theorem sumEquiv_inj (n : ℤ) (i : I) (x : term (P i) n) :
    sumEquiv S n (sumInj P n i x) = φ[S.incl i,n] x := by
  change (DirectSum.toModule k I (term M n) (fun j => (φ[S.incl j,n]).hom))
    (DirectSum.lof k I (fun j => term (P j) n) i x) = φ[S.incl i,n] x
  rw [DirectSum.toModule_lof]

private theorem sum_ext {n : ℤ} {V : Type*} [AddCommGroup V] [Module k V]
    {f g : term M n →ₗ[k] V}
    (h : ∀ i (x : term (P i) n), f (φ[S.incl i,n] x) = g (φ[S.incl i,n] x)) :
    f = g := by
  have e : f.comp (sumEquiv S n).toLinearMap = g.comp (sumEquiv S n).toLinearMap := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, sumEquiv_inj] using h i x
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := (sumEquiv S n).surjective x
  exact LinearMap.congr_fun e y

private def sumProjection (i : I) (n : ℤ) : term M n →ₗ[k] term (P i) n :=
  (sumComponent P n i).comp (sumEquiv S n).symm.toLinearMap

private theorem sumProjection_inj (i j : I) (n : ℤ) (x : term (P j) n) :
    sumProjection S i n (φ[S.incl j,n] x) = sumComponent P n i (sumInj P n j x) := by
  simp only [sumProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ← sumEquiv_inj S n j x, LinearEquiv.symm_apply_apply]

private def sumProjectionHom (i : I) : M ⟶ P i :=
  homOfDegrees (sumProjection S i)
    (by
      intro n
      refine LinearMap.congr_fun (f := d[P i,n].hom.comp (sumProjection S i n))
        (g := (sumProjection S i (n+1)).comp d[M,n].hom) ?_
      apply sum_ext S
      intro j x
      simp only [LinearMap.comp_apply]
      rw [← chain_comm, sumProjection_inj, sumProjection_inj, DirectSum.component.of,
        DirectSum.component.of]
      by_cases e : j = i
      · subst j
        simp
      · simp [e])
    (by
      intro p q n h x a
      refine LinearMap.congr_fun (f := (sumProjection S i n).comp ((act M p q n h).flip a))
        (g := ((act (P i) p q n h).flip a).comp (sumProjection S i p)) ?_ x
      apply sum_ext S
      intro j y
      simp only [LinearMap.comp_apply, LinearMap.flip_apply]
      rw [← (S.incl j).comm_act, sumProjection_inj, sumProjection_inj,
        DirectSum.component.of, DirectSum.component.of]
      by_cases e : j = i
      · subst j
        simp
      · simp [e, LinearMap.zero_apply])

variable (E : A.Module)

private abbrev tensorInj (i : I) :=
  (extension (𝟙 A) E).map (S.incl i)

private abbrev tensorProjection (i : I) :=
  (extension (𝟙 A) E).map (sumProjectionHom S i)

private def tensorSumMap (n : ℤ) :
    sumTerm (fun i => over (P i) E) n →ₗ[k] term (over M E) n :=
  DirectSum.toModule k I _ fun i => (φ[tensorInj S E i,n]).hom

private theorem tensorSumMap_inj (n : ℤ) (i : I) (x : term (over (P i) E) n) :
    tensorSumMap S E n (sumInj (fun j => over (P j) E) n i x) = φ[tensorInj S E i,n] x := by
  rw [tensorSumMap, sumInj, DirectSum.toModule_lof]

private theorem tensorSumMap_surj (n : ℤ) : Function.Surjective (tensorSumMap S E n) := by
  let V := LinearMap.range (tensorSumMap S E n)
  have hV : V.mkQ = 0 := by
    apply pure_ext
    intro p q hp x y
    have eq : V.mkQ.comp ((pair (𝟙 A) p q n hp (M := M) (N := E)).flip y) = 0 := by
      apply sum_ext S
      intro i xi
      change V.mkQ (pure (𝟙 A) p q n hp (φ[S.incl i,p] xi) y) = 0
      apply (Submodule.Quotient.mk_eq_zero V).2
      refine ⟨sumInj (fun j => over (P j) E) n i (pure (𝟙 A) p q n hp xi y), ?_⟩
      rw [tensorSumMap_inj, tensorInj, map_first_pure]
    exact LinearMap.congr_fun eq x
  intro x
  exact (Submodule.Quotient.mk_eq_zero V).1 (LinearMap.congr_fun hV x)

private theorem tensorProjection_inj (n : ℤ) (i j : I) (x : term (over (P j) E) n) :
    φ[tensorProjection S E i,n] (φ[tensorInj S E j,n] x) =
      sumComponent (fun t => over (P t) E) n i (sumInj (fun t => over (P t) E) n j x) := by
  refine LinearMap.congr_fun
    (f := (φ[tensorProjection S E i,n]).hom.comp (φ[tensorInj S E j,n]).hom)
    (g := (sumComponent (fun t => over (P t) E) n i).comp
      (sumInj (fun t => over (P t) E) n j)) ?_ x
  apply pure_ext
  intro p q h a b
  change φ[(extension (𝟙 A) E).map (sumProjectionHom S i),n]
      (φ[(extension (𝟙 A) E).map (S.incl j),n] (pure (𝟙 A) p q n h a b)) = _
  rw [map_first_pure, map_first_pure]
  change pure (𝟙 A) p q n h (sumProjection S i p (φ[S.incl j,p] a)) b = _
  simp only [LinearMap.comp_apply]
  rw [sumProjection_inj, DirectSum.component.of, DirectSum.component.of]
  by_cases e : j = i
  · subst j
    simp
  · simp [e, ← pair_apply]

private theorem tensorSumMap_component (n : ℤ) (i : I)
    (x : sumTerm (fun j => over (P j) E) n) :
    φ[tensorProjection S E i,n] (tensorSumMap S E n x) = x i := by
  refine LinearMap.congr_fun
    (f := (φ[tensorProjection S E i,n]).hom.comp (tensorSumMap S E n))
    (g := sumComponent (fun j => over (P j) E) n i) ?_ x
  apply DirectSum.linearMap_ext
  intro j
  apply LinearMap.ext
  intro y
  change φ[tensorProjection S E i,n]
      (tensorSumMap S E n (sumInj (fun t => over (P t) E) n j y)) =
    sumComponent (fun t => over (P t) E) n i (sumInj (fun t => over (P t) E) n j y)
  rw [tensorSumMap_inj, tensorProjection_inj]

include S in
private theorem tensorSum_acyclic (hP : ∀ i, RightDGModule.Acyclic (over (P i) E)) :
    RightDGModule.Acyclic (over M E) := by
  apply (cycles_are_boundaries _).2
  intro n x hx
  obtain ⟨y, rfl⟩ := tensorSumMap_surj S E n x
  have hz (i : I) : d[over (P i) E,n] (y i) = 0 := by
    rw [← tensorSumMap_component S E n i y, ← chain_comm, hx, map_zero]
  choose z hz using fun i => (cycles_are_boundaries _).1 (hP i) n (y i) (hz i)
  refine ⟨∑ i ∈ y.support, φ[tensorInj S E i,n-1] (z i), ?_⟩
  have decomp : (∑ i ∈ y.support, φ[tensorInj S E i,n] (y i)) = tensorSumMap S E n y := by
    conv_rhs => rw [← DirectSum.sum_support_of y, map_sum]
    exact Finset.sum_congr rfl fun i _ => (tensorSumMap_inj S E n i (y i)).symm
  rw [map_sum, ← decomp]
  apply Finset.sum_congr rfl
  intro i hi
  exact (chain_comm_at (tensorInj S E i) (n-1) n (z i)).symm.trans
    (congrArg (φ[tensorInj S E i,n]) (hz i))

include S in
theorem kFlat_of_directSum (hP : ∀ i, KFlat (P i)) : KFlat M :=
  flat_of_left fun E hE => tensorSum_acyclic S E fun i => flat_left (hP i) hE

theorem directSumFlatness : DirectSumFlatness.{u,v,z} := by
  intro k _ _ T A h I P M S hP
  exact (model_kFlat_iff T (h M)).2 (kFlat_of_directSum S fun i =>
    (model_kFlat_iff T (h (P i))).1 (hP i))

end DirectSum

theorem semifreeFlatness : SemifreeFlatness.{u,v,w,z} := by
  intro k _ _ T A h J _ _ F M U hF hmin hs
  have shiftedFreeFlat {N : A.Module} (hN : ShiftedFree.{u,v,z} N) : T.KFlat N := by
    obtain ⟨I, s, ⟨S⟩⟩ := hN
    apply directSumFlatness T h S
    intro i
    apply shiftFlatness T h
    exact (model_kFlat_iff T (h (regular A))).2 regular_kFlat
  apply filteredFlatness T h F U hF
  · exact fun i hi => shiftedFreeFlat (hmin i hi)
  · intro i j hij
    obtain ⟨Q, p, hS, hQ⟩ := hs i j hij
    exact ⟨Q, p, hS, shiftedFreeFlat hQ⟩

end

end DerivedFormalization.Affine.FlatFiltration
