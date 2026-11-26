import Specs.LinearAlgebraicGroups.Arithmetic.DiscreteDiagonals
import LinearAlgebraicGroups.Arithmetic.AdelicGroups
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.IsTrivialOn
import Mathlib.Topology.Algebra.Group.Subgroup

noncomputable section

open IsDedekindDomain Topology
open scoped NumberField RestrictedProduct

universe u v

namespace LinearAlgebraicGroups.Arithmetic.DiscreteDiagonals

open GlobalFieldData
open AdelicGroups (Adeles LocalPoints Outside asMatrix integralPoints localPoint localSubgroup)
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.IntegralModels (MatrixRealization RationalPoints)
open Specs.Unipotent (Index)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 50000
set_option maxHeartbeats 900000

@[to_additive]
private theorem subgroup_closedDiscrete_of_isolating_identity {H : Type*}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T1Space H]
    (L : Subgroup H) (U : Set H) (ho : IsOpen U) (h₁ : (1 : H) ∈ U)
    (h : ∀ x ∈ L, x ∈ U → x = 1) :
    IsClosed (L : Set H) ∧ IsDiscrete (L : Set H) := by
  have hopen : IsOpen ({1} : Set L) := by
    rw [isOpen_induced_iff]
    refine ⟨U, ho, ?_⟩
    ext x
    exact ⟨fun hx => Set.mem_singleton_iff.mpr (Subtype.ext (h x x.property hx)),
      fun hx => (Set.mem_singleton_iff.mp hx) ▸ h₁⟩
  have ht : DiscreteTopology L := discreteTopology_iff_isOpen_singleton_one.mpr hopen
  have hd : IsDiscrete (L : Set H) := isDiscrete_iff_discreteTopology.mpr ht
  exact ⟨L.isClosed_of_isDiscrete hd, hd⟩

section Arithmetic

variable {F : Type v} {K : Type u} [Field F] [Field K] [Finite F] [Algebra F K]

private theorem constant_valuation_eq_one (w : FunctionPlace K) {x : K}
    (hx : IsAlgebraic F x) (h0 : x ≠ 0) : w.1.valuation x = 1 := by
  by_contra h
  exact (Valuation.transcendental_of_ne_one F x h0 h) hx

/-- The everywhere integral elements are exactly the relative constants. -/
theorem functionFieldConstants : Specs.DiscreteDiagonals.functionFieldConstants.{u, v} := by
  intro F K _ _ _ _ _t x
  let A := (integralClosure F K).toSubring
  change (∀ w : FunctionPlace K, x ∈ w.1) ↔ IsAlgebraic F x
  constructor
  · intro h
    by_contra hx
    have hxA : x ∉ A := fun hxA => hx (show IsIntegral F x from hxA).isAlgebraic
    obtain ⟨V, _, hV⟩ := A.exists_le_valuationSubring_of_isIntegrallyClosedIn hxA
    exact hV (h ⟨V, fun he => hV (he ▸ ValuationSubring.mem_top x)⟩)
  · intro hx w
    obtain rfl | h0 := eq_or_ne x 0
    · exact w.1.zero_mem
    · exact (w.1.valuation_le_one_iff x).mp (constant_valuation_eq_one w hx h0).le

private theorem number_integral_of_local [NumberField K] (x : K)
    (hx : ∀ w : NumberFinitePlace K, algebraMap K (w.adicCompletion K) x ∈
      w.adicCompletionIntegers K) : IsIntegral ℤ x := by
  obtain ⟨a, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K x
    (fun w => by
      have hh := hx w
      change Valued.v ((x : w.adicCompletion K)) ≤ 1 at hh
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hh
      exact hh)
  exact a.property

end Arithmetic

section ScalarBox

variable {K : Type u} [Field K]

/-- A scalar box around zero is given by open local sets, equal to the local integer rings
at finite places outside a finite set. -/
private theorem exists_isolating_box (D : GlobalFieldData.{u, v} K) :
    ∃ (T : Set D.Place) (U : ∀ w : D.Place, Set (D.Completion w)),
      T.Finite ∧ (∀ w : D.InfinitePlace, Sum.inr w ∈ T) ∧
      (∀ w, IsOpen (U w)) ∧ (∀ w, 0 ∈ U w) ∧
      (∀ w : D.FinitePlace, Sum.inl w ∉ T → U (.inl w) = (D.integers w : Set (D.FiniteCompletion w))) ∧
      (∀ x : K, (∀ w, D.embedding w x ∈ U w) → x = 0) := by
  classical
  cases D with
  | number h =>
    letI := h
    let D : GlobalFieldData.{u, v} K := .number h
    let T : Set D.Place := Set.range (Sum.inr : D.InfinitePlace → D.Place)
    let U (w : D.Place) : Set (D.Completion w) :=
      match w with
      | .inl w => (D.integers w : Set (D.FiniteCompletion w))
      | .inr w => (Metric.ball (0 : w.Completion) 1 : Set w.Completion)
    refine ⟨T, U, Set.finite_range _, fun w => ⟨w, rfl⟩, ?_, ?_, fun _ _ => rfl, ?_⟩
    · rintro (w | w)
      · exact (D.integers_properties w).2.1
      · exact (Metric.isOpen_ball : IsOpen (Metric.ball (0 : w.Completion) 1))
    · rintro (w | w)
      · exact (D.integers w).zero_mem
      · exact (Metric.mem_ball_self zero_lt_one : (0 : w.Completion) ∈ Metric.ball 0 1)
    · intro x hx
      have hInt : IsIntegral ℤ x := number_integral_of_local x (fun w => hx (.inl w))
      have hsmall (w : NumberField.InfinitePlace K) : w x < 1 := by
        have hw : (x : w.Completion) ∈ Metric.ball (0 : w.Completion) 1 := hx (.inr w)
        rw [Metric.mem_ball, dist_zero_right] at hw
        change ‖((WithAbs.equiv w.1).symm x : w.Completion)‖ < 1 at hw
        rw [NumberField.InfinitePlace.Completion.norm_coe] at hw
        exact (WithAbs.equiv w.1).apply_symm_apply x ▸ hw
      by_contra hx0
      let a : 𝓞 K := ⟨x, hInt⟩
      let w : NumberField.InfinitePlace K := Classical.choice inferInstance
      exact (hsmall w).not_ge (NumberField.InfinitePlace.one_le_of_lt_one
        (w := w) (a := a) (by exact fun h' => hx0 (congrArg Subtype.val h')) (fun {z} _ => hsmall z))
  | function F t =>
    let D : GlobalFieldData.{u, v} K := .function F t
    have hn : Nonempty (FunctionPlace K) := by
      by_contra h
      apply t.transcendental
      exact (functionFieldConstants t t.element).mp fun w => (h ⟨w⟩).elim
    let w : FunctionPlace K := Classical.choice hn
    let T : Set D.Place := {Sum.inl w}
    let U (p : D.Place) : Set (D.Completion p) :=
      match p with
      | .inl p => if p = w then {z : p.Completion | Valued.v z < 1} else (p.integers : Set p.Completion)
      | .inr p => p.elim
    refine ⟨T, U, Set.finite_singleton _, (fun w => w.elim), ?_, ?_, ?_, ?_⟩
    · rintro (p | p)
      · change IsOpen (if p = w then {z : p.Completion | Valued.v z < 1} else
            (p.integers : Set p.Completion))
        split_ifs
        · simpa only [Valuation.restrict_lt_one_iff] using
            (Valued.isOpen_ball p.Completion 1)
        · exact (D.integers_properties p).2.1
      · exact p.elim
    · rintro (p | p)
      · change 0 ∈ (if p = w then {z : p.Completion | Valued.v z < 1} else
            (p.integers : Set p.Completion))
        split_ifs <;> simp
      · exact p.elim
    · intro p hp
      have hne : p ≠ w := fun he => hp (he ▸ Set.mem_singleton _)
      change (if p = w then {z : p.Completion | Valued.v z < 1} else
        (p.integers : Set p.Completion)) = (p.integers : Set p.Completion)
      exact ite_eq_right hne
    · intro x hx
      have hstrict : Valued.v (w.embedding x) < 1 := by
        have hw := hx (.inl w)
        change w.embedding x ∈ (if w = w then {z : w.Completion | Valued.v z < 1} else
          (w.integers : Set w.Completion)) at hw
        rw [ite_eq_left rfl] at hw
        exact hw
      have hInt (p : FunctionPlace K) : x ∈ p.1 := by
        apply (p.embedding_mem_integers x).mp
        by_cases hp : p = w
        · subst p
          exact hstrict.le
        · have hp' := hx (.inl p)
          change p.embedding x ∈ (if p = w then {z : p.Completion | Valued.v z < 1} else
            (p.integers : Set p.Completion)) at hp'
          rw [ite_eq_right hp] at hp'
          exact hp'
      by_contra hx0
      have hconstant := (functionFieldConstants t x).mp hInt
      change Valued.v (↑((WithVal.equiv w.1.valuation).symm x) : w.Completion) < 1 at hstrict
      rw [Valued.valuedCompletion_apply] at hstrict
      exact hstrict.not_ge (constant_valuation_eq_one w hconstant hx0).ge

private theorem isOpen_restrictedBox {J : Type*} {R : J → Type*} [∀ j, TopologicalSpace (R j)]
    {A U : ∀ j, Set (R j)} (T : Set J) (hT : T.Finite)
    (ha : ∀ j, IsOpen (A j)) (hu : ∀ j, IsOpen (U j)) (he : ∀ j ∉ T, U j = A j) :
    IsOpen {a : Πʳ j, [R j, A j] | ∀ j, a j ∈ U j} := by
  have eq : {a : Πʳ j, [R j, A j] | ∀ j, a j ∈ U j} =
      (fun a : Πʳ j, [R j, A j] => (a : ∀ j, R j)) ⁻¹' Set.pi T U ∩
      {a : Πʳ j, [R j, A j] | ∀ j ∉ T, a j ∈ A j} := by
    ext a
    constructor
    · intro h
      exact ⟨fun j _ => h j, fun j hj => he j hj ▸ h j⟩
    · rintro ⟨h, h'⟩ j
      by_cases hj : j ∈ T
      · exact h j hj
      · exact (he j hj).symm ▸ h' j hj
  rw [eq]
  exact ((isOpen_set_pi hT (fun j _ => hu j)).preimage RestrictedProduct.continuous_coe).inter
    (RestrictedProduct.isOpen_forall_imp_mem ha)

private theorem isOpen_adeleBox (D : GlobalFieldData.{u, v} K)
    (T : Set D.Place) (U : ∀ w : D.Place, Set (D.Completion w))
    (hT : T.Finite) (ho : ∀ w, IsOpen (U w))
    (he : ∀ w : D.FinitePlace, Sum.inl w ∉ T → U (.inl w) = (D.integers w : Set (D.FiniteCompletion w))) :
    IsOpen {a : D.AdeleRing | ∀ w, D.coordinate w a ∈ U w} := by
  have hfin : IsOpen {a : Πʳ w : D.FinitePlace, [D.FiniteCompletion w, D.integers w] |
      ∀ w, a w ∈ U (.inl w)} :=
    isOpen_restrictedBox (Sum.inl ⁻¹' T) (hT.preimage Sum.inl_injective.injOn)
      (fun w => (D.integers_properties w).2.1) (fun w => ho (.inl w)) he
  cases D with
  | number h =>
    letI := h
    let UI (w : NumberField.InfinitePlace K) : Set w.Completion := U (.inr w)
    have hinf : IsOpen {a : NumberField.InfiniteAdeleRing K | ∀ w, a w ∈ U (.inr w)} := by
      have hpi : IsOpen (Set.pi Set.univ UI) :=
        isOpen_set_pi Set.finite_univ fun w _ => ho (.inr w)
      change IsOpen {a : (w : NumberField.InfinitePlace K) → w.Completion | ∀ w, a w ∈ UI w}
      convert hpi using 1
      ext a
      simp [Set.mem_pi]
    have e : {a : NumberField.AdeleRing (𝓞 K) K | ∀ w, (GlobalFieldData.number h).coordinate w a ∈ U w} =
        {a : NumberField.InfiniteAdeleRing K | ∀ w, a w ∈ U (.inr w)} ×ˢ
          {a : FiniteAdeleRing (𝓞 K) K | ∀ w, a w ∈ U (.inl w)} := by
      ext a
      exact ⟨fun h => ⟨fun w => h (.inr w), fun w => h (.inl w)⟩, fun h w =>
        match w with
        | .inl w => h.2 w
        | .inr w => h.1 w⟩
    exact e ▸ hinf.prod hfin
  | function F t =>
    have e : {a : FunctionAdeleRing K | ∀ w, (GlobalFieldData.function F t).coordinate w a ∈ U w} =
        {a : FunctionAdeleRing K | ∀ w : FunctionPlace K, a w ∈ U (.inl w)} := by
      ext a
      exact ⟨fun h w => h (.inl w), fun h w => match w with
        | .inl w => h w
        | .inr w => w.elim⟩
    exact e ▸ hfin

private theorem adele_coordinate_injective (D : GlobalFieldData.{u, v} K) :
    Function.Injective (fun (a : D.AdeleRing) w => D.coordinate w a) := by
  intro a b hab
  cases D with
  | number h =>
    letI := h
    exact Prod.ext (funext fun w => congrFun hab (.inr w))
      (Subtype.ext (funext fun w => congrFun hab (.inl w)))
  | function F t =>
    exact Subtype.ext (funext fun w => congrFun hab (.inl w))

/-- The range of the canonical ring homomorphism is the scalar diagonal. -/
theorem scalarDiagonalImage_eq_range (D : GlobalFieldData.{u, v} K) :
    Specs.DiscreteDiagonals.scalarDiagonalImage D = Set.range D.diagonal := by
  ext a
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, adele_coordinate_injective D (funext fun w =>
      (D.coordinate_diagonal w x).trans (hx w).symm)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, fun w => D.coordinate_diagonal w x⟩

/-- The additive diagonal is closed and discrete in the full adelic topology. -/
theorem scalarClosedDiscrete : Specs.DiscreteDiagonals.scalarClosedDiscrete.{u, v} := by
  intro K _ D
  letI : T2Space D.AdeleRing := by
    cases D with
    | number h =>
      letI := h
      change T2Space (((w : NumberField.InfinitePlace K) → w.Completion) ×
        (Πʳ w : NumberFinitePlace K, [w.adicCompletion K, w.adicCompletionIntegers K]))
      infer_instance
    | function F t =>
      exact inferInstanceAs (T2Space (FunctionAdeleRing K))
  obtain ⟨T, U, ht, _, ho, h0, he, hiso⟩ := exists_isolating_box D
  rw [scalarDiagonalImage_eq_range D]
  let L := D.diagonal.toAddMonoidHom.range
  change IsClosed (L : Set D.AdeleRing) ∧ IsDiscrete (L : Set D.AdeleRing)
  refine addSubgroup_closedDiscrete_of_isolating_identity L
    {a | ∀ w, D.coordinate w a ∈ U w} (isOpen_adeleBox D T U ht ho he) ?_ ?_
  · change ∀ w, D.coordinate w 0 ∈ U w
    intro w
    have hw := D.coordinate_diagonal w 0
    rw [map_zero, map_zero] at hw
    rw [hw]
    exact h0 w
  · rintro _ ⟨x, rfl⟩ hx
    have hx0 : x = 0 := hiso x fun w => D.coordinate_diagonal w x ▸ hx w
    simp [hx0]

end ScalarBox

section GroupDiagonal

variable {K : Type u} [Field K] {G : AffineAlgebraicGroup K}

/-- The range of the canonical homomorphism at the empty omitted set is the full diagonal. -/
theorem groupDiagonalImage_eq_range (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) :
    Specs.DiscreteDiagonals.groupDiagonalImage D i =
      Set.range (AdelicGroups.diagonal D i ∅) := by
  ext a
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, RestrictedProduct.ext _ _ fun w => (hg w).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, fun _ => rfl⟩

private theorem integral_coordinates (D : GlobalFieldData.{u, v} K)
    (i : MatrixRealization G) (w : D.FinitePlace) (g : LocalPoints D i (.inl w))
    (hg : g ∈ integralPoints D i w) :
    (∀ s t, (asMatrix i (D.Completion (.inl w)) g).val s t ∈ D.integers w) ∧
      (asMatrix i (D.Completion (.inl w)) g)⁻¹.val.det ∈ D.integers w := by
  let M : Matrix.GeneralLinearGroup (Index.{u} i.size) (D.FiniteCompletion w) :=
    asMatrix i (D.Completion (.inl w)) g
  change M ∈ (Matrix.GeneralLinearGroup.map (D.integers w).subtype).range at hg
  change (∀ s t, M.val s t ∈ D.integers w) ∧ M⁻¹.val.det ∈ D.integers w
  obtain ⟨m, hm⟩ := hg
  rw [← hm, ← Matrix.GeneralLinearGroup.map_inv]
  exact ⟨fun s t => (m.val s t).property, by
    change ((D.integers w).subtype.mapMatrix m⁻¹.val).det ∈ D.integers w
    exact (RingHom.map_det (D.integers w).subtype m⁻¹.val) ▸ m⁻¹.val.det.property⟩

/-- The full rational diagonal of an affine algebraic group is closed and discrete. -/
theorem groupClosedDiscrete : Specs.DiscreteDiagonals.groupClosedDiscrete.{u, v} := by
  classical
  intro K _ G D i
  letI (w : Outside D (∅ : Finset D.Place)) : T2Space (LocalPoints D i w.1) :=
    (AdelicGroups.localMatrixEmbedding D i w.1).isEmbedding.t2Space
  letI : T2Space (Adeles D i ∅) := inferInstance
  obtain ⟨T, U, ht, hArch, ho, h0, he, hiso⟩ := exists_isolating_box D
  let m (w : D.Place) := asMatrix i (D.Completion w)
  let E (w : D.Place) : Set (LocalPoints D i w) :=
    {g | (∀ s t, (m w g).val s t - (1 : Matrix (Index.{u} i.size) (Index.{u} i.size) _) s t ∈ U w) ∧
      (m w g)⁻¹.val.det - 1 ∈ U w}
  let V (w : Outside D (∅ : Finset D.Place)) : Set (LocalPoints D i w.1) :=
    if w.1 ∈ T then E w.1 else localSubgroup D i w.1
  have hE (w : D.Place) : IsOpen (E w) := by
    have hc : Continuous (m w) := (AdelicGroups.localMatrixEmbedding D i w).continuous
    have e : E w = (⋂ s, ⋂ t,
        (fun g => (m w g).val s t - (1 : Matrix (Index.{u} i.size) (Index.{u} i.size) _) s t) ⁻¹' U w) ∩
        (fun g => (m w g)⁻¹.val.det - 1) ⁻¹' U w := by
      ext g
      simp [E]
    rw [e]
    refine (isOpen_iInter_of_finite fun s => isOpen_iInter_of_finite fun t =>
      (ho w).preimage
        (((continuous_apply t).comp (Matrix.GeneralLinearGroup.continuous_apply _ hc s)).sub continuous_const)).inter ?_
    refine (ho w).preimage ?_
    have hdet : Continuous (fun g => ((m w g)⁻¹.val : Matrix (Index.{u} i.size) (Index.{u} i.size) _).det) :=
      (continuous_id.matrix_det.comp Units.continuous_val).comp (continuous_inv.comp hc)
    exact hdet.sub continuous_const
  have hV (w : Outside D (∅ : Finset D.Place)) : IsOpen (V w) := by
    dsimp only [V]
    split_ifs
    · exact hE _
    · exact AdelicGroups.localSubgroup_open D i _
  have hbox : IsOpen {a : Adeles D i ∅ | ∀ w, a w ∈ V w} :=
    isOpen_restrictedBox (Subtype.val ⁻¹' T) (ht.preimage Subtype.val_injective.injOn)
      (fun w => AdelicGroups.localSubgroup_open D i w.1) hV (fun w hw => ite_eq_right hw)
  rw [groupDiagonalImage_eq_range D i]
  let d := AdelicGroups.diagonal D i ∅
  change IsClosed (d.range : Set (Adeles D i ∅)) ∧ IsDiscrete (d.range : Set (Adeles D i ∅))
  refine subgroup_closedDiscrete_of_isolating_identity d.range _ hbox ?_ ?_
  · intro w
    change 1 ∈ V w
    dsimp only [V]
    split_ifs
    · change (∀ s t, (m w.1 1).val s t - (1 : Matrix (Index.{u} i.size) (Index.{u} i.size) _) s t ∈ U w.1) ∧
        (m w.1 1)⁻¹.val.det - 1 ∈ U w.1
      simpa only [map_one, inv_one, Matrix.det_one, sub_self, Units.val_one] using
        And.intro (fun _ _ : Index.{u} i.size => h0 w.1) (h0 w.1)
    · exact (localSubgroup D i w.1).one_mem
  · rintro _ ⟨g, rfl⟩ hg
    have hcoord (w : D.Place) : localPoint D i w g ∈ E w := by
      let p : Outside D (∅ : Finset D.Place) := ⟨w, Finset.notMem_empty w⟩
      have hp : localPoint D i w g ∈ V p := hg p
      by_cases hw : w ∈ T
      · change localPoint D i w g ∈ (if w ∈ T then E w else (localSubgroup D i w : Set _)) at hp
        rwa [ite_eq_left hw] at hp
      · cases w with
        | inr w =>
          exact (hw (hArch w)).elim
        | inl w =>
          change localPoint D i (.inl w) g ∈
            (if Sum.inl w ∈ T then E (.inl w) else (integralPoints D i w : Set _)) at hp
          have hi : localPoint D i (.inl w) g ∈ integralPoints D i w := by
            rwa [ite_eq_right hw] at hp
          obtain ⟨hentries, hdet⟩ := integral_coordinates D i w _ hi
          change (∀ s t, (m (.inl w) (localPoint D i (.inl w) g)).val s t -
              (1 : Matrix (Index.{u} i.size) (Index.{u} i.size) _) s t ∈ U (.inl w)) ∧
            (m (.inl w) (localPoint D i (.inl w) g))⁻¹.val.det - 1 ∈ U (.inl w)
          rw [he w hw]
          have hone (s t : Index.{u} i.size) :
              (1 : Matrix (Index.{u} i.size) (Index.{u} i.size) (D.Completion (.inl w))) s t ∈ D.integers w := by
            rw [Matrix.one_apply]
            split_ifs
            · exact (D.integers w).one_mem
            · exact (D.integers w).zero_mem
          exact ⟨fun s t => sub_mem (hentries s t) (hone s t),
            sub_mem hdet (D.integers w).one_mem⟩
    have hm : i.onPoints g = 1 := by
      apply Units.ext
      ext s t
      apply sub_eq_zero.mp
      apply hiso
      intro w
      have hw := (hcoord w).1 s t
      change (asMatrix i (D.Completion w) (localPoint D i w g)).val s t -
        (1 : Matrix (Index.{u} i.size) (Index.{u} i.size) _) s t ∈ U w at hw
      rw [AdelicGroups.localPoint_matrix] at hw
      change (D.embedding w) ((i.onPoints g).val s t -
        (1 : Matrix (Index.{u} i.size) (Index.{u} i.size) K) s t) ∈ U w
      rw [map_sub]
      have he : D.embedding w ((1 : Matrix (Index.{u} i.size) (Index.{u} i.size) K) s t) =
          (1 : Matrix (Index.{u} i.size) (Index.{u} i.size) (D.Completion w)) s t := by
        simp only [Matrix.one_apply]
        split_ifs <;> simp
      rw [he]
      exact hw
    apply RestrictedProduct.ext
    intro w
    apply (AdelicGroups.localMatrixEmbedding D i w.1).injective
    change (m w.1) (localPoint D i w.1 g) = (m w.1) 1
    simp [m, hm]

end GroupDiagonal

end LinearAlgebraicGroups.Arithmetic.DiscreteDiagonals
