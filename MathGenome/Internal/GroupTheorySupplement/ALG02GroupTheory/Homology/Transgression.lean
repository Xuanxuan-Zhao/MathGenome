import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Homology.Transgression
import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Homology.BarProjectionKernel
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Limits Category
open scoped Classical

universe u

namespace ALG02GroupTheory.Transgression

open IntegralBar BarProjectionKernel
open private kernelLinear_ext representative representative_right fiberDifference_one
  fiberDifference_two kernelDOne
  degreeOneCycles_inv_i coordinate translate_coordinate bar_one_identity quotient_conj normalizedLinear_ext
  from MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Homology.BarProjectionKernel

noncomputable section

variable {N E Q N' E' Q' : Type u}
variable [Group N] [Group E] [Group Q] [Group N'] [Group E'] [Group Q']

set_option allowUnsafeReducibility true in
attribute [local reducible] normalizedChains kernelChains ChainComplex.of

private theorem apply_comm {K L : ChainComplex (ModuleCat.{u} Integers.{u}) ℕ}
    (f : K ⟶ L) (i j : ℕ) (x : K.X i) :
    f.f j (K.d i j x) = L.d i j (f.f i x) :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (f.comm i j).symm) x

private theorem apply_boundary_boundary (G : Type u) [Group G]
    (x : NormalizedModule G 3) : barBoundary G 1 (barBoundary G 2 x) = 0 := by
  change (normalizedChains G).d 2 1 ((normalizedChains G).d 3 2 x) = 0
  rw [← ModuleCat.comp_apply, HomologicalComplex.d_comp_d]
  rfl

private theorem filtration_mem (S : GroupExtension N E Q) {p n : ℕ} (t : Fin n → E)
    (h : (Finset.univ.filter (fun j => S.rightHom (t j) ≠ 1)).card ≤ p) :
    normalizedBar n t ∈ barFiltration S p n :=
  Submodule.subset_span ⟨t, h, rfl⟩

private theorem support_card_le {G H : Type u} [Group G] [Group H]
    {m n : ℕ} (v : Fin m → G) (w : Fin n → H) (f : Fin m → Fin n)
    (hf : Function.Injective f) (h : ∀ k, v k ≠ 1 → w (f k) ≠ 1) :
    (Finset.univ.filter (fun k => v k ≠ 1)).card ≤
      (Finset.univ.filter (fun k => w k ≠ 1)).card := by
  apply Finset.card_le_card_of_injOn f _ hf.injOn
  intro k hk
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h k (Finset.mem_filter.mp hk).2⟩

private theorem contraction_support_le (S : GroupExtension N E Q) {n : ℕ}
    (t : Fin (n + 1) → E) (j : Fin (n + 1)) :
    (Finset.univ.filter (fun k => S.rightHom (Fin.contractNth j (· * ·) t k) ≠ 1)).card ≤
      (Finset.univ.filter (fun k => S.rightHom (t k) ≠ 1)).card := by
  induction j using Fin.lastCases with
  | last =>
    apply support_card_le _ _ Fin.castSucc (Fin.castSucc_injective _)
    intro k hk
    rwa [Fin.contractNth_apply_of_lt _ _ _ _ k.isLt] at hk
  | cast i =>
    let j := if S.rightHom (t i.castSucc) = 1 then i.castSucc else i.succ
    apply support_card_le _ _ j.succAbove Fin.succAbove_right_injective
    intro k hk
    rcases lt_trichotomy k.val i.val with hlt | heq | hgt
    · have h : k.castSucc < j := by
        dsimp [j]
        split <;> exact Fin.lt_def.mpr (by simp; omega)
      rwa [j.succAbove_of_castSucc_lt k h, ← Fin.contractNth_apply_of_lt i.castSucc (· * ·) t k hlt]
    · have h : k = i := Fin.ext heq
      subst k
      rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl, map_mul] at hk
      by_cases hi : S.rightHom (t i.castSucc) = 1
      · rw [show j = i.castSucc from ite_eq_left hi, Fin.succAbove_of_le_castSucc _ _ le_rfl]
        simpa [hi] using hk
      · rw [show j = i.succ from ite_eq_right hi, Fin.succAbove_of_castSucc_lt _
          _ (Fin.lt_def.mpr (Nat.lt_succ_self _))]
        exact hi
    · have h : j ≤ k.castSucc := by
        dsimp [j]
        split <;> exact Fin.le_iff_val_le_val.mpr (by simp; omega)
      rwa [j.succAbove_of_le_castSucc k h, ← Fin.contractNth_apply_of_gt i.castSucc (· * ·) t k hgt]

/-- The chain filtration is preserved by faces and by maps of extensions. -/
theorem filtered_bar : Spec.FilteredBar.{u} := by
  constructor
  · intro N E Q _ _ _ S
    refine ⟨?_, ?_, ?_⟩
    · intro n p q hpq
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨t, ht, rfl⟩
      exact filtration_mem S t (ht.trans hpq)
    · intro n
      let V := barFiltration S n n
      have h : V.mkQ = 0 := by
        apply normalizedLinear_ext
        intro t
        apply (Submodule.Quotient.mk_eq_zero V).mpr
        apply filtration_mem
        exact (Finset.card_filter_le _ _).trans_eq (by simp)
      apply top_unique
      intro x _
      exact (Submodule.Quotient.mk_eq_zero V).mp (DFunLike.congr_fun h x)
    · intro p n
      rw [Submodule.map_le_iff_le_comap]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨t, ht, rfl⟩
      change (normalizedChains E).d (n + 1) n (normalizedBar (n + 1) t) ∈ barFiltration S p n
      rw [normalizedChains_d_mk, groupHomology.inhomogeneousChains.d_def]
      unfold bar
      rw [groupHomology.inhomogeneousChains.d_single (A := coefficients E)]
      change (degenerate E n).mkQ (Finsupp.single (fun k => t k.succ) 1 + _) ∈ _
      simp only [map_add, map_sum, map_smul]
      apply Submodule.add_mem
      · apply filtration_mem
        apply le_trans _ ht
        exact support_card_le _ _ Fin.succ (Fin.succ_injective _) (fun _ hk => hk)
      · apply Submodule.sum_mem
        intro j _
        exact Submodule.smul_mem _ _ (filtration_mem S _ ((contraction_support_le S t j).trans ht))
  · intro N E Q N' E' Q' _ _ _ _ _ _ S T f p n
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨t, ht, rfl⟩
    change (normalizedChainsMap f.middle).f n (normalizedBar n t) ∈ barFiltration T p n
    rw [normalizedChainsMap_bar]
    apply filtration_mem
    apply le_trans _ ht
    apply support_card_le _ _ id Function.injective_id
    intro k hk hz
    apply hk
    change T.rightHom (f.middle (t k)) = 1
    rw [show T.rightHom (f.middle (t k)) = f.quotient (S.rightHom (t k)) from
      DFunLike.congr_fun f.right_comm _]
    rw [show S.rightHom (t k) = 1 from hz, map_one]

private theorem filtration_le_kernel (S : GroupExtension N E Q) {p n : ℕ} (hpn : p < n) :
    barFiltration S p n ≤ KernelModule S n := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨t, ht, rfl⟩
  change (normalizedChainsMap S.rightHom).f n (normalizedBar n t) = 0
  rw [normalizedChainsMap_bar]
  apply normalizedBar_eq_zero
  by_contra! h
  have hfilter : (Finset.univ.filter (fun j => S.rightHom (t j) ≠ 1)) = Finset.univ :=
    Finset.filter_true_of_mem (fun j _ => h j)
  rw [hfilter, Finset.card_univ, Fintype.card_fin] at ht
  omega

private theorem bar_mem_zero (S : GroupExtension N E Q) (n : N) :
    normalizedBar 1 ![S.inl n] ∈ barFiltration S 0 1 := by
  apply filtration_mem
  simp [Finset.filter_false]

private theorem bar_mem_one (S : GroupExtension N E Q) (a b : E)
    (h : S.rightHom a = 1 ∨ S.rightHom b = 1) :
    normalizedBar 2 ![a, b] ∈ barFiltration S 1 2 := by
  apply filtration_mem
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, S.rightHom (![a, b] j) = 1 := by
    rcases h with ha | hb
    · exact ⟨0, ha⟩
    · exact ⟨1, hb⟩
  have hlt : (Finset.univ.filter (fun j : Fin 2 => S.rightHom (![a, b] j) ≠ 1)) ⊂
      Finset.univ := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
    intro he
    have hmem : j ∈ Finset.univ.filter (fun j : Fin 2 => S.rightHom (![a, b] j) ≠ 1) :=
      he.symm ▸ Finset.mem_univ j
    exact (Finset.mem_filter.mp hmem).2 hj
  have hc := Finset.card_lt_card hlt
  rw [Finset.card_univ, Fintype.card_fin] at hc
  omega

private theorem kernel_le_by_fibers (S : GroupExtension N E Q) (n : ℕ)
    (W : Submodule Integers.{u} (NormalizedModule E n))
    (h : ∀ (t s : Fin n → E) (e : S.rightHom ∘ t = S.rightHom ∘ s),
      (fiberDifference S t s e).val ∈ W) : KernelModule S n ≤ W := by
  have he : W.mkQ.comp (KernelModule S n).subtype = 0 := by
    apply kernelLinear_ext S n
    intro t
    have hh : S.rightHom ∘ t = S.rightHom ∘ representative S ∘ S.rightHom ∘ t := by
      funext j
      exact (representative_right S (S.rightHom (t j))).symm
    exact (Submodule.Quotient.mk_eq_zero W).mpr (h _ _ hh)
  intro x hx
  exact (Submodule.Quotient.mk_eq_zero W).mp (DFunLike.congr_fun he ⟨x, hx⟩)

/-- A degree-one fiber difference can be corrected by the boundary of a bar with a kernel entry. -/
private theorem kernel_one_le (S : GroupExtension N E Q) :
    KernelModule S 1 ≤ barFiltration S 0 1 ⊔ (barFiltration S 1 2).map (barBoundary E 1) := by
  apply kernel_le_by_fibers S 1
  intro t s he
  rw [fiberDifference_one]
  generalize coordinate S (t 0) * (coordinate S (s 0))⁻¹ = n
  change normalizedBar 1 ![S.inl n * s 0] - normalizedBar 1 ![s 0] ∈
    barFiltration S 0 1 ⊔ (barFiltration S 1 2).map (barBoundary E 1)
  refine Submodule.mem_sup.mpr ⟨normalizedBar 1 ![S.inl n], bar_mem_zero S n,
    -(barBoundary E 1 (normalizedBar 2 ![S.inl n, s 0])), ?_, ?_⟩
  · exact Submodule.neg_mem _ ⟨_, bar_mem_one S _ _ (Or.inl (S.rightHom_inl n)), rfl⟩
  · change _ + -((normalizedChains E).d 2 1 (normalizedBar 2 ![S.inl n, s 0])) = _
    rw [normalizedBar_d_two]
    abel

/-- In degree two, moving a kernel multiplier through an adjacent entry changes the
chain by a boundary and chains of filtration at most one. -/
private theorem kernel_two_le (S : GroupExtension N E Q) :
    KernelModule S 2 ≤ barFiltration S 1 2 ⊔ LinearMap.range (barBoundary E 2) := by
  let W := barFiltration S 1 2 ⊔ LinearMap.range (barBoundary E 2)
  have first (n : N) (a b : E) :
      normalizedBar 2 ![S.inl n * a, b] - normalizedBar 2 ![a, b] ∈ W := by
    refine Submodule.mem_sup.mpr ⟨normalizedBar 2 ![S.inl n, a * b] -
      normalizedBar 2 ![S.inl n, a], Submodule.sub_mem _ (bar_mem_one S _ _
        (Or.inl (S.rightHom_inl n))) (bar_mem_one S _ _ (Or.inl (S.rightHom_inl n))),
      -(barBoundary E 2 (normalizedBar 3 ![S.inl n, a, b])),
      Submodule.neg_mem _ (LinearMap.mem_range_self _ _), ?_⟩
    change _ + -((normalizedChains E).d 3 2 (normalizedBar 3 ![S.inl n, a, b])) = _
    rw [normalizedBar_d_three]
    abel
  have second (m : N) (a b : E) :
      normalizedBar 2 ![a, S.inl m * b] - normalizedBar 2 ![a, b] ∈ W := by
    have ha : S.inl (S.conjAct a m) * a = a * S.inl m := by
      rw [S.inl_conjAct_comm, mul_assoc _ a⁻¹ a, inv_mul_cancel, mul_one]
    have h₁ := first (S.conjAct a m) a b
    rw [ha] at h₁
    have h₂ : normalizedBar 2 ![a, S.inl m * b] - normalizedBar 2 ![a * S.inl m, b] ∈ W := by
      refine Submodule.mem_sup.mpr ⟨normalizedBar 2 ![a, S.inl m] -
        normalizedBar 2 ![S.inl m, b], Submodule.sub_mem _ (bar_mem_one S _ _
          (Or.inr (S.rightHom_inl m))) (bar_mem_one S _ _ (Or.inl (S.rightHom_inl m))),
        barBoundary E 2 (normalizedBar 3 ![a, S.inl m, b]), LinearMap.mem_range_self _ _, ?_⟩
      change _ + (normalizedChains E).d 3 2 (normalizedBar 3 ![a, S.inl m, b]) = _
      rw [normalizedBar_d_three]
      abel
    convert Submodule.add_mem W h₂ h₁ using 1
    abel
  apply kernel_le_by_fibers S 2
  intro t s he
  obtain ⟨n, m, a, b, h', hh⟩ := fiberDifference_two S t s he
  rw [hh]
  change normalizedBar 2 ![S.inl n * a, S.inl m * b] - normalizedBar 2 ![a, b] ∈ W
  convert Submodule.add_mem W (first n a (S.inl m * b)) (second m a b) using 1
  abel

/-- The connecting homology class is represented by the boundary of the chain lift. -/
theorem connecting_on_lift : Spec.ConnectingOnLift.{u} := by
  intro N E Q _ _ _ S hS z hz x hx y hy cy
  exact hS.δ_apply 2 1 rfl z hz x hx y hy 0 ((ComplexShape.down ℕ).next_eq' rfl)


/-- The transported integral map uses the same signed lift formula. -/
theorem integral_lift_formula : Spec.IntegralLiftFormula.{u} := by
  intro N E Q _ _ _ S hS e a z hz ha x hx
  change e (Multiplicative.ofAdd (connecting S hS
    (HomologicalComplex.homologyMap (normalization Q) 2 a))) = _
  rw [ha, connecting_on_lift S hS z hz x hx (liftBoundary S z hz x hx) rfl
    (liftBoundary_isCycle S hS z hz x hx)]

/-- The lifted boundary class is independent of both representative and lift. -/
theorem lift_independence : Spec.LiftIndependence.{u} := by
  intro N E Q _ _ _ S hS z z' hz hz' h x x' hx hx'
  rw [← connecting_on_lift S hS z hz x hx (liftBoundary S z hz x hx) rfl
    (liftBoundary_isCycle S hS z hz x hx),
    ← connecting_on_lift S hS z' hz' x' hx' (liftBoundary S z' hz' x' hx') rfl
    (liftBoundary_isCycle S hS z' hz' x' hx'), h]

private theorem cycleOf_val (K : ChainComplex (ModuleCat.{u} Integers.{u}) ℕ)
    {n : ℕ} (z : K.X (n + 1)) (hz : K.d (n + 1) n z = 0) :
    K.iCycles (n + 1) (cycleOf K z hz) = z :=
  K.i_cyclesMk z n ((ComplexShape.down ℕ).next_eq' rfl) hz

private theorem cycle_val_isCycle (K : ChainComplex (ModuleCat.{u} Integers.{u}) ℕ)
    {n : ℕ} (z : K.cycles (n + 1)) :
    K.d (n + 1) n (K.iCycles (n + 1) z) = 0 := by
  have h := (K.sc (n + 1)).iCycles_g
  change K.iCycles (n + 1) ≫ K.d (n + 1) ((ComplexShape.down ℕ).next (n + 1)) = 0 at h
  rw [(ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)] at h
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) z

private theorem classOf_surjective (K : ChainComplex (ModuleCat.{u} Integers.{u}) ℕ)
    {n : ℕ} (a : K.homology (n + 1)) :
    ∃ (z : K.X (n + 1)) (hz : K.d (n + 1) n z = 0), classOf K z hz = a := by
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ (n + 1))).mp inferInstance a
  refine ⟨K.iCycles (n + 1) z, cycle_val_isCycle K z, ?_⟩
  unfold classOf
  rw [← hz]
  congr 1
  apply (ModuleCat.mono_iff_injective (K.iCycles (n + 1))).mp inferInstance
  exact cycleOf_val K _ _

private theorem classOf_zero_iff (K : ChainComplex (ModuleCat.{u} Integers.{u}) ℕ)
    {n : ℕ} (z : K.X (n + 1)) (hz : K.d (n + 1) n z = 0) :
    classOf K z hz = 0 ↔ ∃ w : K.X (n + 2), K.d (n + 2) (n + 1) w = z := by
  let L := ShortComplex.mk (K.toCycles (n + 2) (n + 1)) (K.homologyπ (n + 1))
    (K.toCycles_comp_homologyπ _ _)
  have hL : L.Exact := L.exact_of_g_is_cokernel
    (K.homologyIsCokernel (i := n + 2) (j := n + 1) ((ComplexShape.down ℕ).prev_eq' rfl))
  have h := hL.moduleCat_range_eq_ker
  change cycleOf K z hz ∈ LinearMap.ker L.g.hom ↔ _
  rw [← h]
  change (∃ w, K.toCycles (n + 2) (n + 1) w = cycleOf K z hz) ↔ _
  have hi (w : K.X (n + 2)) :
      K.iCycles (n + 1) (K.toCycles (n + 2) (n + 1) w) = K.d (n + 2) (n + 1) w :=
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (K.toCycles_i (n + 2) (n + 1))) w
  have hinj := (ModuleCat.mono_iff_injective (K.iCycles (n + 1))).mp inferInstance
  constructor <;> rintro ⟨w, hw⟩ <;> refine ⟨w, ?_⟩
  · rw [← hi, hw, cycleOf_val]
  · apply hinj
    rw [hi, cycleOf_val, hw]

private theorem kernelClass_eq_classOf (S : GroupExtension N E Q)
    (y : KernelModule S 1) (hy : (kernelChains S).d 1 0 y = 0) :
    kernelClass S y = classOf (kernelChains S) y hy := by
  unfold kernelClass degreeOneClassMap classOf
  rw [ModuleCat.comp_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective ((kernelChains S).iCycles 1)).mp inferInstance
  rw [cycleOf_val, ← ModuleCat.comp_apply, degreeOneCycles_inv_i]
  rfl

private theorem source_projects_to_cycle (S : GroupExtension N E Q)
    (x : sourceCycles S) :
    barBoundary Q 1 ((normalizedChainsMap S.rightHom).f 2 x.val) = 0 := by
  rw [← apply_comm (normalizedChainsMap S.rightHom) 2 1]
  exact filtration_le_kernel S (by decide) x.property

private def sourceClass (S : GroupExtension N E Q) :
    sourceCycles S →ₗ[Integers.{u}] (normalizedChains Q).homology 2 :=
  ((normalizedChains Q).liftCycles'
      (ModuleCat.ofHom (((normalizedChainsMap S.rightHom).f 2).hom.comp (sourceCycles S).subtype))
      1 rfl (ModuleCat.hom_ext (LinearMap.ext (source_projects_to_cycle S))) ≫
    (normalizedChains Q).homologyπ 2).hom

private theorem sourceClass_apply (S : GroupExtension N E Q) (x : sourceCycles S) :
    sourceClass S x = classOf (normalizedChains Q) ((normalizedChainsMap S.rightHom).f 2 x.val)
      (source_projects_to_cycle S x) := by
  unfold sourceClass classOf
  change (normalizedChains Q).homologyπ 2 _ = (normalizedChains Q).homologyπ 2 _
  congr 1
  apply (ModuleCat.mono_iff_injective ((normalizedChains Q).iCycles 2)).mp inferInstance
  rw [cycleOf_val]
  have h := (normalizedChains Q).liftCycles_i
    (ModuleCat.ofHom (((normalizedChainsMap S.rightHom).f 2).hom.comp (sourceCycles S).subtype))
    1 ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 2 1 from rfl))
    (ModuleCat.hom_ext (LinearMap.ext (source_projects_to_cycle S)))
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) x

private theorem sourceClass_surjective (S : GroupExtension N E Q) :
    Function.Surjective (sourceClass S) := by
  intro a
  obtain ⟨z, hz, rfl⟩ := classOf_surjective (normalizedChains Q) (n := 1) a
  obtain ⟨x, hx⟩ := projection_surjective S 2 z
  have hk : barBoundary E 1 x ∈ KernelModule S 1 := by
    change (normalizedChainsMap S.rightHom).f 1 ((normalizedChains E).d 2 1 x) = 0
    rw [apply_comm, hx]
    exact hz
  obtain ⟨v, hv, w, hw, h⟩ := Submodule.mem_sup.mp (kernel_one_le S hk)
  obtain ⟨y, hy, rfl⟩ := hw
  have hb : barBoundary E 1 (x - y) = v := by
    rw [map_sub, ← h, add_sub_cancel_right]
  have hx' : (normalizedChainsMap S.rightHom).f 2 (x - y) = z := by
    rw [map_sub, hx, show (normalizedChainsMap S.rightHom).f 2 y = 0 from
      filtration_le_kernel S (by decide) hy, sub_zero]
  have hcy : x - y ∈ sourceCycles S := by
    change barBoundary E 1 (x - y) ∈ barFiltration S 0 1
    rwa [hb]
  refine ⟨⟨x - y, hcy⟩, ?_⟩
  rw [sourceClass_apply]
  unfold classOf
  congr 1
  apply (ModuleCat.mono_iff_injective ((normalizedChains Q).iCycles 2)).mp inferInstance
  rw [cycleOf_val, cycleOf_val]
  exact hx'

private theorem sourceClass_ker (S : GroupExtension N E Q) :
    LinearMap.ker (sourceClass S) = sourceRelations S := by
  ext x
  change sourceClass S x = 0 ↔
    x.val ∈ lowerCycles S ⊔ LinearMap.range (barBoundary E 2)
  rw [sourceClass_apply, classOf_zero_iff]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨w, hw⟩ := projection_surjective S 3 z
    have hk : x.val - barBoundary E 2 w ∈ KernelModule S 2 := by
      change (normalizedChainsMap S.rightHom).f 2 (x.val - (normalizedChains E).d 3 2 w) = 0
      rw [map_sub, apply_comm, hw, hz, sub_self]
    obtain ⟨y, hy, v, hv, he⟩ := Submodule.mem_sup.mp (kernel_two_le S hk)
    obtain ⟨w', rfl⟩ := hv
    have h : y + barBoundary E 2 (w' + w) = x.val := by
      rw [map_add, ← add_assoc, he, sub_add_cancel]
    have hy' : y ∈ sourceCycles S := by
      have hh := congrArg (barBoundary E 1) h
      rw [map_add, apply_boundary_boundary, add_zero] at hh
      change barBoundary E 1 y ∈ barFiltration S 0 1
      rw [hh]
      exact x.property
    exact Submodule.mem_sup.mpr ⟨y, ⟨hy, hy'⟩, _, LinearMap.mem_range_self _ _, h⟩
  · intro hx
    obtain ⟨y, hy, v, hv, he⟩ := Submodule.mem_sup.mp hx
    obtain ⟨w, rfl⟩ := hv
    refine ⟨(normalizedChainsMap S.rightHom).f 3 w, ?_⟩
    rw [← apply_comm (normalizedChainsMap S.rightHom) 3 2]
    have h := congrArg ((normalizedChainsMap S.rightHom).f 2) he
    rw [map_add, show (normalizedChainsMap S.rightHom).f 2 y = 0 from
      filtration_le_kernel S (by decide) hy.1, zero_add] at h
    exact h

private def targetClass (S : GroupExtension N E Q) :
    barFiltration S 0 1 →ₗ[Integers.{u}] (kernelChains S).homology 1 :=
  (kernelClass S).hom.comp (Submodule.inclusion (filtration_le_kernel S (by decide)))

private theorem targetClass_apply (S : GroupExtension N E Q) (x : barFiltration S 0 1)
    (y : KernelModule S 1) (hy : y.val = x.val) (cy : (kernelChains S).d 1 0 y = 0) :
    targetClass S x = classOf (kernelChains S) y cy := by
  unfold targetClass
  rw [LinearMap.comp_apply, ← kernelClass_eq_classOf S]
  congr 1
  exact Subtype.ext hy.symm

private theorem targetClass_surjective (S : GroupExtension N E Q) :
    Function.Surjective (targetClass S) := by
  intro a
  obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective (homologyEquiv S (Multiplicative.ofAdd a))
  have ha := congrArg (fun x => ((homologyEquiv S).symm x).toAdd) hn
  simp only [homologyEquiv_symm_mk S n 1, MulEquiv.symm_apply_apply] at ha
  refine ⟨⟨normalizedBar 1 ![S.inl n], bar_mem_zero S n⟩, ?_⟩
  change kernelClass S (Submodule.inclusion _ _) = a
  change kernelClass S (translateDifference S n 1) = a at ha
  rw [← ha]
  congr 1
  apply Subtype.ext
  change normalizedBar 1 ![S.inl n] = normalizedBar 1 ![S.inl n * 1] - normalizedBar 1 ![(1 : E)]
  rw [mul_one, bar_one_identity, sub_zero]

private theorem kernel_d_val (S : GroupExtension N E Q) (w : KernelModule S 2) :
    ((kernelChains S).d 2 1 w).val = barBoundary E 1 w.val := by
  rw [kernelChains_d]
  rfl

private theorem targetClass_ker (S : GroupExtension N E Q) :
    LinearMap.ker (targetClass S) = targetRelations S := by
  ext x
  let y : KernelModule S 1 := ⟨x.val, filtration_le_kernel S (by decide) x.property⟩
  change targetClass S x = 0 ↔ x.val ∈ (lowerCycles S).map (barBoundary E 1)
  rw [targetClass_apply S x y rfl (by rw [kernelDOne]; rfl), classOf_zero_iff]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨v, hv, z, hz, he⟩ := Submodule.mem_sup.mp (kernel_two_le S w.property)
    obtain ⟨w', rfl⟩ := hz
    have hh := congrArg (barBoundary E 1) he
    rw [map_add, apply_boundary_boundary, add_zero, ← kernel_d_val S w, hw] at hh
    have hc : v ∈ sourceCycles S := by
      change barBoundary E 1 v ∈ barFiltration S 0 1
      rw [hh]
      exact x.property
    exact ⟨v, ⟨hv, hc⟩, hh⟩
  · rintro ⟨v, hv, he⟩
    refine ⟨⟨v, filtration_le_kernel S (by decide) hv.1⟩, ?_⟩
    apply Subtype.ext
    rw [kernel_d_val]
    exact he

private def sourceIdentification (S : GroupExtension N E Q) :
    PageTwoSource S ≃ₗ[Integers.{u}] (normalizedChains Q).homology 2 :=
  (Submodule.quotEquivOfEq _ _ (sourceClass_ker S).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (sourceClass_surjective S))

private def targetIdentification (S : GroupExtension N E Q) :
    PageTwoTarget S ≃ₗ[Integers.{u}] (kernelChains S).homology 1 :=
  (Submodule.quotEquivOfEq _ _ (targetClass_ker S).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (targetClass_surjective S))

/-- The differential on the second page agrees with the normalized connecting map
under the identifications induced by projection and inclusion. -/
theorem filtered_comparison : Spec.FilteredComparison.{u} := by
  intro N E Q _ _ _ S hS
  refine ⟨sourceIdentification S, targetIdentification S,
    fun x _ => sourceClass_apply S x, targetClass_apply S, ?_⟩
  intro a
  obtain ⟨x, rfl⟩ := (sourceRelations S).mkQ_surjective a
  let z : barFiltration S 0 1 := ⟨barBoundary E 1 x.val, x.property⟩
  let y : KernelModule S 1 := ⟨z.val, filtration_le_kernel S (by decide) z.property⟩
  have cy : (kernelChains S).d 1 0 y = 0 := by rw [kernelDOne]; rfl
  change targetClass S z = connecting S hS (sourceClass S x)
  rw [targetClass_apply S z y rfl cy, sourceClass_apply]
  exact (connecting_on_lift S hS _ _ x.val rfl y rfl cy).symm


/-- Compare the filtered bar differential with the integral transgression. -/
theorem integral_filtered_comparison : Spec.IntegralFilteredComparison.{u} := by
  intro N E Q _ _ _ S hS e
  obtain ⟨s, t, hs, ht, hd⟩ := filtered_comparison S hS
  let iso := normalizationHomologyIso Q 2 (by decide)
  have hi (y : (normalizedChains Q).homology 2) :
      HomologicalComplex.homologyMap (normalization Q) 2 (iso.inv y) = y :=
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom iso.inv_hom_id) y
  refine ⟨s.trans (iso.symm.toLinearEquiv), t.toAddEquiv.toMultiplicative.trans e,
    ?_, ?_, ?_⟩
  · intro x hx
    change HomologicalComplex.homologyMap (normalization Q) 2 (iso.inv
      (s ((sourceRelations S).mkQ x))) = _
    rw [hi, hs]
  · intro x y hy cy
    change e (Multiplicative.ofAdd (t ((targetRelations S).mkQ x))) = _
    rw [ht x y hy cy]
  · intro x
    change e (Multiplicative.ofAdd (t (pageTwoDifferential S x))) =
      e (Multiplicative.ofAdd (connecting S hS
        (HomologicalComplex.homologyMap (normalization Q) 2 (iso.inv (s x)))))
    rw [hi, hd]

private def projectionSequenceMap {S : GroupExtension N E Q} {T : GroupExtension N' E' Q'}
    (f : ExtensionHom S T) : projectionSequence S ⟶ projectionSequence T :=
  ShortComplex.homMk (kernelChainsMap f) (normalizedChainsMap f.middle)
    (normalizedChainsMap f.quotient) (by ext n : 1; rfl) (projection_square f)

private theorem normalizedConnecting_natural {S : GroupExtension N E Q}
    {T : GroupExtension N' E' Q'} (f : ExtensionHom S T)
    (hS : (projectionSequence S).ShortExact) (hT : (projectionSequence T).ShortExact)
    (x : (normalizedChains Q).homology 2) :
    connecting T hT (HomologicalComplex.homologyMap (normalizedChainsMap f.quotient) 2 x) =
      HomologicalComplex.homologyMap (kernelChainsMap f) 1 (connecting S hS x) :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (HomologicalComplex.HomologySequence.δ_naturality (projectionSequenceMap f) hS hT
      2 1 rfl).symm) x

/-- Transport the connecting morphism along the homology and kernel identifications. -/
def integralTransgressionFromSequence (S : GroupExtension N E Q)
    (hS : (projectionSequence S).ShortExact)
    (e : Multiplicative ((kernelChains S).homology 1) ≃* KernelQuotient S) :
    Multiplicative (homology Q 2) →* KernelQuotient S :=
  integralConnecting S hS e

/-- The transgression on standard integral homology for a group extension. -/
def integralTransgression (S : GroupExtension N E Q) :
    Multiplicative (homology Q 2) →* KernelQuotient S :=
  integralTransgressionFromSequence S (projection_shortExact S) (homologyEquiv S)

private theorem integralConnecting_natural {S : GroupExtension N E Q}
    {T : GroupExtension N' E' Q'} (f : ExtensionHom S T)
    (hS : (projectionSequence S).ShortExact) (hT : (projectionSequence T).ShortExact)
    (x : homology Q 2) :
    integralConnecting T hT (homologyEquiv T) (Multiplicative.ofAdd (homologyMap f.quotient 2 x)) =
      quotientMap f (integralConnecting S hS (homologyEquiv S) (Multiplicative.ofAdd x)) := by
  have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (normalization_homology_natural f.quotient 2)) x
  change HomologicalComplex.homologyMap (normalizedChainsMap f.quotient) 2
    (HomologicalComplex.homologyMap (normalization Q) 2 x) =
      HomologicalComplex.homologyMap (normalization Q') 2 (homologyMap f.quotient 2 x) at h
  change homologyEquiv T (Multiplicative.ofAdd (connecting T hT
    (HomologicalComplex.homologyMap (normalization Q') 2 (homologyMap f.quotient 2 x)))) =
    quotientMap f (homologyEquiv S (Multiplicative.ofAdd (connecting S hS
      (HomologicalComplex.homologyMap (normalization Q) 2 x))))
  rw [← h, normalizedConnecting_natural f hS hT]
  exact homologyEquiv_natural f (projection_square f) _

/-- The integral transgression commutes with the induced maps of extensions. -/
theorem integralTransgression_natural {S : GroupExtension N E Q} {T : GroupExtension N' E' Q'}
    (f : ExtensionHom S T) (x : homology Q 2) :
    integralTransgression T (Multiplicative.ofAdd (homologyMap f.quotient 2 x)) =
      quotientMap f (integralTransgression S (Multiplicative.ofAdd x)) :=
  integralConnecting_natural f (projection_shortExact S) (projection_shortExact T) x

/-- The integral transgression commutes with all maps of extensions. -/
theorem integral_naturality : Spec.IntegralNaturality.{u} := by
  refine ⟨fun S => homologyEquiv S, ?_, ?_⟩
  · intro N E Q _ _ _ S n y hy cy
    rw [← kernelClass_eq_classOf S y cy]
    have h : y = translateDifference S n 1 := by
      apply Subtype.ext
      change y.val = normalizedBar 1 ![S.inl n * 1] - normalizedBar 1 ![(1 : E)]
      rw [hy, mul_one, bar_one_identity, sub_zero]
    rw [h, homologyEquiv_translate]
  · intro N E Q N' E' Q' _ _ _ _ _ _ S T f hS hT x
    exact integralConnecting_natural f hS hT x

private theorem generatorClass_surjective (G : Type u) [Group G] :
    Function.Surjective (generatorClass (G := G)) := by
  intro x
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective ((h1Equiv G x).toMul)
  refine ⟨g, (h1Equiv G).injective ?_⟩
  rw [h1Equiv_generatorClass]
  exact congrArg Additive.ofMul hg

/-- Inner automorphisms of the kernel act trivially on its first homology. -/
theorem conjugation_factors : Spec.ConjugationFactors.{u} := by
  intro N E Q _ _ _ S a b hab
  have h := translate_coordinate S a b hab
  rw [← h]
  generalize coordinate S a * (coordinate S b)⁻¹ = n
  apply MonoidHom.ext
  intro x
  obtain ⟨m, hm⟩ := generatorClass_surjective N x.toAdd
  have hx : x = Multiplicative.ofAdd (generatorClass m) := congrArg Multiplicative.ofAdd hm.symm
  rw [hx]
  apply Multiplicative.toAdd.injective
  change homologyMap (S.conjAct (S.inl n * b)).toMonoidHom 1 (generatorClass m) =
    homologyMap (S.conjAct b).toMonoidHom 1 (generatorClass m)
  simp only [homologyMap_generatorClass, MulEquiv.coe_toMonoidHom, map_mul, MulAut.mul_apply]
  have he (k : N) : S.conjAct (S.inl n) k = n * k * n⁻¹ := by
    apply S.inl_injective
    rw [S.inl_conjAct_comm, map_mul, map_mul, map_inv]
  rw [he]
  apply (h1Equiv N).injective
  simp only [h1Equiv_generatorClass, map_mul, map_inv]
  congr 1
  rw [mul_comm (Abelianization.of n), mul_assoc, mul_inv_cancel, mul_one]

private def coinvariantProjection (S : GroupExtension N E Q) :
    Multiplicative (homology N 1) →* KernelQuotient S :=
  (Abelianization.lift (QuotientGroup.mk' (pulledBackCommutator S.inl))).comp
    (h1Equiv N).toMultiplicative.toMonoidHom

private theorem coinvariantProjection_generator (S : GroupExtension N E Q) (n : N) :
    coinvariantProjection S (Multiplicative.ofAdd (generatorClass n)) = QuotientGroup.mk n := by
  change Abelianization.lift (QuotientGroup.mk' (pulledBackCommutator S.inl))
    (h1Equiv N (generatorClass n)).toMul = _
  rw [h1Equiv_generatorClass]
  exact Abelianization.lift_apply_of _ _

/-- The target quotient has the universal property of conjugation coinvariants. -/
theorem conjugation_coinvariants : Spec.ConjugationCoinvariants.{u} := by
  intro N E Q _ _ _ S
  refine ⟨coinvariantProjection S, coinvariantProjection_generator S, ?_, ?_⟩
  · intro a
    apply MonoidHom.ext
    intro x
    obtain ⟨n, hn⟩ := generatorClass_surjective N x.toAdd
    have he : x = Multiplicative.ofAdd (generatorClass n) := congrArg Multiplicative.ofAdd hn.symm
    rw [he]
    change coinvariantProjection S (Multiplicative.ofAdd
      (homologyMap (S.conjAct a).toMonoidHom 1 (generatorClass n))) =
      coinvariantProjection S (Multiplicative.ofAdd (generatorClass n))
    rw [homologyMap_generatorClass, coinvariantProjection_generator, coinvariantProjection_generator]
    exact quotient_conj S a n
  · intro A _ f hf
    let k : N →* A := f.comp ((h1Equiv N).toMultiplicative.symm.toMonoidHom.comp Abelianization.of)
    have hk (n : N) : k n = f (Multiplicative.ofAdd (generatorClass n)) := by
      change f (Multiplicative.ofAdd
        ((h1Equiv N).symm (Additive.ofMul (Abelianization.of n)))) = _
      rw [← h1Equiv_generatorClass n, AddEquiv.symm_apply_apply]
    have hinv (a : E) (n : N) : k (S.conjAct a n) = k n := by
      have h := DFunLike.congr_fun (hf a) (Multiplicative.ofAdd (generatorClass n))
      change f (Multiplicative.ofAdd
        (homologyMap (S.conjAct a).toMonoidHom 1 (generatorClass n))) =
        f (Multiplicative.ofAdd (generatorClass n)) at h
      rw [homologyMap_generatorClass, ← hk, ← hk] at h
      exact h
    have kills : pulledBackCommutator S.inl ≤ k.ker := by
      change (⁅(⊤ : Subgroup E), S.inl.range⁆ : Subgroup E).comap S.inl ≤ k.ker
      have h : ⁅(⊤ : Subgroup E), S.inl.range⁆ ≤ k.ker.map S.inl := by
        apply Subgroup.commutator_le.mpr
        rintro a _ _ ⟨n, rfl⟩
        refine ⟨S.conjAct a n * n⁻¹, ?_, ?_⟩
        · change k (S.conjAct a n * n⁻¹) = 1
          rw [map_mul, map_inv, hinv, mul_inv_cancel]
        · rw [map_mul, map_inv, S.inl_conjAct_comm]
          rfl
      intro n hn
      obtain ⟨m, hm, he⟩ := h hn
      exact (S.inl_injective he) ▸ hm
    refine ⟨QuotientGroup.lift _ k kills, ?_, ?_⟩
    · apply MonoidHom.ext
      intro x
      obtain ⟨n, hn⟩ := generatorClass_surjective N x.toAdd
      have he : x = Multiplicative.ofAdd (generatorClass n) := congrArg Multiplicative.ofAdd hn.symm
      rw [he, MonoidHom.comp_apply, coinvariantProjection_generator, QuotientGroup.lift_mk', hk]
    · intro g hg
      apply MonoidHom.ext
      intro x
      refine QuotientGroup.induction_on x fun n => ?_
      rw [QuotientGroup.lift_mk', hk, ← coinvariantProjection_generator S n]
      exact DFunLike.congr_fun hg _

end
end ALG02GroupTheory.Transgression
