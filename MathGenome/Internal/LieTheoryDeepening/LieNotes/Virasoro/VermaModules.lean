import MathGenome.Internal.LieTheoryDeepening.LieNotes.Virasoro.VirasoroCocycle
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Virasoro.VermaModules
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.BorelInduction

/-! Induction and the ordered PBW basis for Virasoro Verma modules. -/

noncomputable section

namespace LieNotes.Virasoro.Verma

open VermaSpec
open RepTheorySurvey.CategoryO.BorelInduction
open UniversalEnvelopingAlgebra (ι)
open scoped TensorProduct

local notation "L" => Vir.L
local notation "C" => Vir.C
local notation "κ" => VirasoroSpec.centralCoefficient

attribute [local instance 100] LieRing.ofAssociativeRing

private def indexEquiv : (ℤ ⊕ Unit) ≃ (ℕ ⊕ (ℕ ⊕ Unit)) where
  toFun
    | .inl (.ofNat n) => .inr (.inl n)
    | .inl (.negSucc n) => .inl n
    | .inr u => .inr (.inr u)
  invFun
    | .inl n => .inl (.negSucc n)
    | .inr (.inl n) => .inl (.ofNat n)
    | .inr (.inr u) => .inr u
  left_inv := by
    rintro (n | u)
    · cases n <;> rfl
    · rfl
  right_inv := by rintro (n | (n | u)) <;> rfl

private def virBasis : Module.Basis (ℕ ⊕ (ℕ ⊕ Unit)) ℂ Vir :=
  (((Witt.basis).prod (Module.Basis.singleton Unit ℂ)).map Vir.coordinates.symm).reindex
    indexEquiv

@[simp] private theorem virBasis_inl (n : ℕ) : virBasis (.inl n) = negativeLetter n := by
  simp [virBasis, indexEquiv, negativeLetter, VirasoroSpec.mode, Vir.coordinates, Witt.L]

@[simp] private theorem virBasis_inr (j : ℕ ⊕ Unit) : virBasis (.inr j) = borelLetter j := by
  cases j with
  | inl n =>
    simp [virBasis, indexEquiv, borelLetter, VirasoroSpec.mode, Vir.coordinates, Witt.L]
  | inr u =>
    simp [virBasis, indexEquiv, borelLetter, VirasoroSpec.central, Vir.coordinates]

private theorem neg_independent : LinearIndependent ℂ negativeLetter := by
  simpa only [Function.comp_def, virBasis_inl] using
    virBasis.linearIndependent.comp Sum.inl Sum.inl_injective

private theorem borel_independent : LinearIndependent ℂ borelLetter := by
  simpa only [Function.comp_def, virBasis_inr] using
    virBasis.linearIndependent.comp Sum.inr Sum.inr_injective

private def spanSubalgebra {I : Type*} (f : I → Vir)
    (closed : ∀ i j, ⁅f i, f j⁆ ∈ Submodule.span ℂ (Set.range f)) : LieSubalgebra ℂ Vir :=
  { Submodule.span ℂ (Set.range f) with
    lie_mem' := by
      intro x y hx hy
      refine Submodule.span_induction (p := fun x _ => ⁅x, y⁆ ∈ _) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨i, rfl⟩
        refine Submodule.span_induction (p := fun y _ => ⁅f i, y⁆ ∈ _) ?_ ?_ ?_ ?_ hy
        · rintro _ ⟨j, rfl⟩
          exact closed i j
        · rw [lie_zero]
          exact Submodule.zero_mem _
        · intro a b _ _ ha hb
          rw [lie_add]
          exact Submodule.add_mem _ ha hb
        · intro a b _ hb
          rw [lie_smul]
          exact Submodule.smul_mem _ a hb
      · rw [zero_lie]
        exact Submodule.zero_mem _
      · intro a b _ _ ha hb
        rw [add_lie]
        exact Submodule.add_mem _ ha hb
      · intro a b _ hb
        rw [smul_lie]
        exact Submodule.smul_mem _ a hb }

private theorem nonnegative_bracket (m n : ℕ) :
    ⁅L (m : ℤ), L (n : ℤ)⁆ = ((m : ℂ) - (n : ℂ)) • L ((m + n : ℕ) : ℤ) := by
  have hk : κ m n = 0 := by
    unfold VirasoroSpec.centralCoefficient
    split
    · have hm : m = 0 := by omega
      simp [hm]
    · rfl
  rw [Vir.lie_L, hk, zero_smul, add_zero, Nat.cast_add]
  push_cast
  rfl

/-- The subalgebra spanned by the central generator and the nonnegative modes. -/
def borel : LieSubalgebra ℂ Vir :=
  spanSubalgebra borelLetter (by
    rintro (m | u) (n | v)
    · change ⁅L (m : ℤ), L (n : ℤ)⁆ ∈ _
      rw [nonnegative_bracket]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self (f := borelLetter) (.inl (m + n))))
    · change ⁅L (m : ℤ), C⁆ ∈ _
      rw [← lie_skew, Vir.lie_C, neg_zero]
      exact Submodule.zero_mem _
    all_goals
      change ⁅C, _⁆ ∈ _
      rw [Vir.lie_C]
      exact Submodule.zero_mem _)

/-- The subalgebra spanned by the negative modes. -/
def negative : LieSubalgebra ℂ Vir :=
  spanSubalgebra negativeLetter (by
    intro m n
    change ⁅L (Int.negSucc m), L (Int.negSucc n)⁆ ∈ _
    have hi : Int.negSucc m + Int.negSucc n = Int.negSucc (m + n + 1) := by omega
    have hk : κ (Int.negSucc m) (Int.negSucc n) = 0 := by
      simp [VirasoroSpec.centralCoefficient, show Int.negSucc m + Int.negSucc n ≠ 0 by omega]
    rw [Vir.lie_L, hi, hk, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self (m + n + 1))))

private theorem borel_mem (i : ℕ ⊕ Unit) : borelLetter i ∈ borel :=
  Submodule.subset_span (Set.mem_range_self i)

private theorem complement : IsCompl negative.toSubmodule borel.toSubmodule := by
  change IsCompl (Submodule.span ℂ (Set.range negativeLetter))
    (Submodule.span ℂ (Set.range borelLetter))
  simpa only [← Set.range_comp, Function.comp_def, virBasis_inl, virBasis_inr] using
    virBasis.linearIndependent.isCompl_span_image virBasis.span_eq
      (Set.isCompl_range_inl_range_inr (α := ℕ) (β := ℕ ⊕ Unit))

private def borelBasis : Module.Basis (ℕ ⊕ Unit) ℂ borel :=
  Module.Basis.span borel_independent

private def negativeBasis : Module.Basis ℕ ℂ negative :=
  Module.Basis.span neg_independent

@[simp] private theorem coe_borelBasis (i : ℕ ⊕ Unit) : (borelBasis i : Vir) = borelLetter i :=
  Module.Basis.coe_span_apply borel_independent i

@[simp] private theorem coe_negativeBasis (i : ℕ) :
    (negativeBasis i : Vir) = negativeLetter i :=
  Module.Basis.coe_span_apply neg_independent i

private def letterValue (c h : ℂ) : ℕ ⊕ Unit → ℂ
  | .inl 0 => h
  | .inl (_ + 1) => 0
  | .inr _ => c

private def functional (c h : ℂ) : borel →ₗ[ℂ] ℂ :=
  borelBasis.constr ℂ (letterValue c h)

@[simp] private theorem functional_basis (c h : ℂ) (i : ℕ ⊕ Unit) :
    functional c h (borelBasis i) = letterValue c h i :=
  borelBasis.constr_basis ℂ _ i

private theorem functional_lie (c h : ℂ) (x y : borel) : functional c h ⁅x, y⁆ = 0 := by
  have hf : (LieModule.toEnd ℂ borel borel).toLinearMap.compr₂ (functional c h) = 0 := by
    apply LinearMap.ext_basis borelBasis borelBasis
    intro i j
    simp only [LinearMap.compr₂_apply, LieHom.coe_toLinearMap, LieModule.toEnd_apply_apply, LinearMap.zero_apply]
    rcases i with (m | u) <;> rcases j with (n | v)
    · have hb : ⁅borelBasis (.inl m), borelBasis (.inl n)⁆ =
          ((m : ℂ) - (n : ℂ)) • borelBasis (.inl (m+n)) := by
        apply Subtype.ext
        change ⁅(borelBasis (.inl m) : Vir), (borelBasis (.inl n) : Vir)⁆ =
          ((m : ℂ) - (n : ℂ)) • (borelBasis (.inl (m+n)) : Vir)
        simp only [coe_borelBasis, borelLetter]
        exact nonnegative_bracket m n
      rw [hb, map_smul, functional_basis]
      cases n with
      | zero => cases m <;> simp [letterValue]
      | succ n => rw [Nat.add_succ]; simp [letterValue]
    · have hz : ⁅borelBasis (.inl m), borelBasis (.inr v)⁆ = 0 := by
        apply Subtype.ext
        change ⁅(borelBasis (.inl m) : Vir), (borelBasis (.inr v) : Vir)⁆ = 0
        rw [coe_borelBasis, coe_borelBasis]
        change ⁅L (m : ℤ), C⁆ = 0
        rw [← lie_skew, Vir.lie_C, neg_zero]
      rw [hz, map_zero]
    · have hz : ⁅borelBasis (.inr u), borelBasis (.inl n)⁆ = 0 := by
        apply Subtype.ext
        change ⁅(borelBasis (.inr u) : Vir), (borelBasis (.inl n) : Vir)⁆ = 0
        simp only [coe_borelBasis]
        change ⁅C, _⁆ = 0
        exact Vir.lie_C _
      rw [hz, map_zero]
    · have hz : ⁅borelBasis (.inr u), borelBasis (.inr v)⁆ = 0 := by
        apply Subtype.ext
        change ⁅(borelBasis (.inr u) : Vir), (borelBasis (.inr v) : Vir)⁆ = 0
        simp only [coe_borelBasis]
        change ⁅C, _⁆ = 0
        exact Vir.lie_C _
      rw [hz, map_zero]
  exact congrArg (fun f : borel →ₗ[ℂ] borel →ₗ[ℂ] ℂ => f x y) hf

private def lieCharacter (c h : ℂ) : borel →ₗ⁅ℂ⁆ ℂ :=
  { functional c h with
    map_lie' := fun {x y} => by
      simp [functional_lie, LieRing.of_associative_ring_bracket, mul_comm] }

/-- The algebra character inducing the highest-weight module. -/
def character (c h : ℂ) : U borel →ₐ[ℂ] ℂ :=
  UniversalEnvelopingAlgebra.lift ℂ (lieCharacter c h)

private theorem character_basis (c h : ℂ) (i : ℕ ⊕ Unit) :
    character c h (ι ℂ (borelBasis i)) = letterValue c h i := by
  rw [character, UniversalEnvelopingAlgebra.lift_ι_apply]
  exact functional_basis c h i

/-- The inducing data of the Virasoro highest-weight construction. -/
def inducingData : VermaSpec.InducingData where
  borel := borel
  span_eq := rfl
  character := character
  character_central c h hm := by
    change character c h (ι ℂ (⟨C, hm⟩ : borel)) = c
    have he : (⟨C, hm⟩ : borel) = borelBasis (.inr ()) := Subtype.ext (by simp only [coe_borelBasis]; rfl)
    rw [he, character_basis]
    rfl
  character_zero c h hm := by
    change character c h (ι ℂ (⟨L 0, hm⟩ : borel)) = h
    have he : (⟨L 0, hm⟩ : borel) = borelBasis (.inl 0) := Subtype.ext (by simp only [coe_borelBasis]; rfl)
    rw [he, character_basis]
    rfl
  character_positive c h j hj hm := by
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = ((n + 1 : ℕ) : ℤ) := ⟨j.toNat - 1, by omega⟩
    change character c h (ι ℂ (⟨L ((n + 1 : ℕ) : ℤ), hm⟩ : borel)) = 0
    have he : (⟨L ((n + 1 : ℕ) : ℤ), hm⟩ : borel) = borelBasis (.inl (n+1)) :=
      Subtype.ext (by simp only [coe_borelBasis]; rfl)
    rw [he, character_basis]
    rfl

/-- The Verma module of central charge `c` and highest weight `h`. -/
abbrev M (c h : ℂ) := inducingData.Verma c h

/-- Its canonical highest-weight vector. -/
abbrev top (c h : ℂ) : M c h := inducingData.top c h

/-- The space of vectors of weight `h + d`. -/
abbrev degree (c h : ℂ) (d : ℤ) := inducingData.degree c h d


abbrev applyWord (c h : ℂ) := inducingData.applyWord c h

@[simp] theorem applyWord_nil (c h : ℂ) : applyWord c h [] = top c h := rfl

@[simp] theorem applyWord_cons (c h : ℂ) (i : ℕ) (w : List ℕ) :
    applyWord c h (i :: w) = ⁅negativeLetter i, applyWord c h w⁆ := rfl

private abbrev characterModule (c h : ℂ) : Module (U borel) ℂ :=
  inducingData.characterModule c h

private theorem character_tower (c h : ℂ) :
    letI := characterModule c h
    IsScalarTower ℂ (U borel) ℂ := by
  let _ := characterModule c h
  apply IsScalarTower.of_algebraMap_smul
  intro a b
  change character c h (algebraMap ℂ (U borel) a) * b = a * b
  rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]

private theorem lie_top_borel (c h : ℂ) (x : borel) :
    ⁅(x : Vir), top c h⁆ = character c h (ι ℂ x) • top c h := by
  let _ := characterModule c h
  change (ι ℂ (x : Vir)) • induceTensor (inclusion borel) 1 (1 : ℂ) =
    character c h (ι ℂ x) • induceTensor (inclusion borel) 1 (1 : ℂ)
  rw [smul_tensor, mul_one, ← inclusion_ι, ← one_mul (inclusion borel (ι ℂ x)), balance_tensor]
  change induceTensor (inclusion borel) 1 (character c h (ι ℂ x) • (1 : ℂ)) = _
  unfold induceTensor
  rw [TensorProduct.tmul_smul, LinearMap.map_smul_of_tower]

theorem highestWeight (c h : ℂ) : IsHighestWeight c h (top c h) := by
  constructor
  · have hm : C ∈ borel := borel_mem (.inr ())
    exact (lie_top_borel c h ⟨C, hm⟩).trans
      (congrArg (· • top c h) (inducingData.character_central c h hm))
  constructor
  · have hm : L 0 ∈ borel := borel_mem (.inl 0)
    exact (lie_top_borel c h ⟨L 0, hm⟩).trans
      (congrArg (· • top c h) (inducingData.character_zero c h hm))
  · intro j hj
    change ⁅L j, top c h⁆ = 0
    have hm : L j ∈ borel := by
      have hn : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg (le_of_lt hj)
      have hm := borel_mem (.inl j.toNat)
      change L (j.toNat : ℤ) ∈ borel at hm
      rwa [hn] at hm
    have hc := inducingData.character_positive c h j hj hm
    change character c h (ι ℂ (⟨L j, hm⟩ : borel)) = 0 at hc
    rw [lie_top_borel c h ⟨L j, hm⟩, hc, zero_smul]

private def pbwEquiv (c h : ℂ) : U negative ≃ₗ[ℂ] M c h :=
  letI := characterModule c h
  letI := character_tower c h
  (TensorProduct.rid ℂ (U negative)).symm.trans (inducedPBWEquiv negative borel complement)

private theorem pbwEquiv_apply (c h : ℂ) (a : U negative) :
    pbwEquiv c h a = (inclusion negative a) • top c h := by
  let _ := characterModule c h
  let _ := character_tower c h
  change inducedPBWEquiv negative borel complement (a ⊗ₜ[ℂ] (1 : ℂ)) = _
  rw [inducedPBWEquiv_tensor]
  symm
  change (inclusion negative a) • induceTensor (inclusion borel) 1 (1 : ℂ) = _
  rw [smul_tensor, mul_one]

/-- The basis of ordered negative-mode words, including the empty word. -/
def basis (c h : ℂ) : Module.Basis Word ℂ (M c h) :=
  (Shared.Lie.PBW.orderedBasis negativeBasis).map (pbwEquiv c h)

private theorem monomial_smul_top (c h : ℂ) (w : List ℕ) :
    inclusion negative (Shared.Lie.PBW.monomial negativeBasis w) • top c h = applyWord c h w := by
  induction w with
  | nil =>
      change inclusion negative 1 • top c h = top c h
      rw [map_one, one_smul]
  | cons i w ih =>
      change inclusion negative (ι ℂ (negativeBasis i) *
        Shared.Lie.PBW.monomial negativeBasis w) • top c h = _
      rw [map_mul, mul_smul, ih, inclusion_ι, coe_negativeBasis]
      rfl

@[simp] theorem basis_apply (c h : ℂ) (w : Word) : basis c h w = applyWord c h w.val := by
  rw [basis, Module.Basis.map_apply, Shared.Lie.PBW.orderedBasis_apply, pbwEquiv_apply]
  exact monomial_smul_top c h w.val

theorem top_ne_zero (c h : ℂ) : top c h ≠ 0 := by
  simpa only [basis_apply, Shared.Lie.PBW.emptyWord, applyWord_nil] using
    (basis c h).ne_zero (Shared.Lie.PBW.emptyWord ℕ)

theorem cyclic (c h : ℂ) : LieSubmodule.lieSpan ℂ Vir {top c h} = ⊤ := by
  apply top_unique
  intro x _
  have hw (w : List ℕ) : applyWord c h w ∈ LieSubmodule.lieSpan ℂ Vir {top c h} := by
    induction w with
    | nil => exact LieSubmodule.subset_lieSpan (Set.mem_singleton _)
    | cons i w ih => exact LieSubmodule.lie_mem _ ih
  have hsub : Submodule.span ℂ (Set.range (basis c h)) ≤
      (LieSubmodule.lieSpan ℂ Vir {top c h}).toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    rw [basis_apply]
    exact hw w.val
  exact hsub ((basis c h).mem_span x)

@[simp] theorem mem_degree {c h : ℂ} {d : ℤ} {x : M c h} :
    x ∈ degree c h d ↔ ⁅L 0, x⁆ = (h + (d : ℂ)) • x :=
  Module.End.mem_eigenspace_iff

private theorem zero_mode_bracket (j : ℤ) : ⁅L 0, L j⁆ = -(j : ℂ) • L j := by
  rw [Vir.lie_L]
  simp [VirasoroSpec.centralCoefficient]

theorem shift (c h : ℂ) (j d : ℤ) (x : M c h) (hx : x ∈ degree c h d) :
    ⁅L j, x⁆ ∈ degree c h (d - j) := by
  rw [mem_degree] at hx ⊢
  rw [leibniz_lie, zero_mode_bracket, smul_lie, hx, lie_smul, ← add_smul, Int.cast_sub]
  congr 1
  ring

private theorem list_weight (c h : ℂ) (w : List ℕ) :
    applyWord c h w ∈ degree c h (((w.map Nat.succ).sum : ℕ) : ℤ) := by
  induction w with
  | nil =>
      simp only [applyWord_nil, List.map_nil, List.sum_nil, Nat.cast_zero, mem_degree,
        Int.cast_zero, add_zero]
      exact (highestWeight c h).2.1
  | cons i w ih =>
      have hs := shift c h (Int.negSucc i) _ (applyWord c h w) ih
      have he : (((w.map Nat.succ).sum : ℕ) : ℤ) - Int.negSucc i =
          ((((i :: w).map Nat.succ).sum : ℕ) : ℤ) := by
        simp only [List.map_cons, List.sum_cons, Nat.cast_add]
        omega
      rw [he] at hs
      exact hs

theorem word_weight (c h : ℂ) (w : Word) :
    applyWord c h w.val ∈ degree c h (wordDegree w) :=
  list_weight c h w.val

theorem degree_span (c h : ℂ) (d : ℤ) : degree c h d =
    Submodule.span ℂ {x | ∃ w : Word, (wordDegree w : ℤ) = d ∧ x = applyWord c h w.val} := by
  let b := basis c h
  have hb (w : Word) : ⁅L 0, b w⁆ = (h + (wordDegree w : ℂ)) • b w := by
    have hw := (mem_degree.mp (word_weight c h w))
    simpa only [Int.cast_natCast, basis_apply, b] using hw
  apply le_antisymm
  · intro x hx
    have hcoord (w : Word) :
        b.coord w ⁅L 0, x⁆ = (h + (wordDegree w : ℂ)) * b.coord w x := by
      have he : (b.coord w).comp (LieModule.toEnd ℂ Vir (M c h) (L 0)) =
          (h + (wordDegree w : ℂ)) • b.coord w := by
        apply b.ext
        intro p
        simp only [LinearMap.comp_apply, LieModule.toEnd_apply_apply, hb, map_smul,
          LinearMap.smul_apply, smul_eq_mul]
        by_cases hp : p = w
        · subst p
          rfl
        · rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne (Ne.symm hp),
            mul_zero, mul_zero]
      exact congrArg (fun f : M c h →ₗ[ℂ] ℂ => f x) he
    have hsupp : ↑(b.repr x).support ⊆ {w : Word | (wordDegree w : ℤ) = d} := by
      intro w hw
      have hn : b.coord w x ≠ 0 := by
        change (b.repr x) w ≠ 0
        exact Finsupp.mem_support_iff.mp hw
      have hc := hcoord w
      rw [mem_degree.mp hx, map_smul, smul_eq_mul] at hc
      have he := mul_right_cancel₀ hn hc
      have he' : ((wordDegree w : ℤ) : ℂ) = (d : ℂ) := by
        rw [Int.cast_natCast]
        exact (add_left_cancel he).symm
      exact_mod_cast he'
    have hxspan := (b.mem_span_image (s := {w : Word | (wordDegree w : ℤ) = d})).2 hsupp
    apply Submodule.span_mono _ hxspan
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w, hw, (basis_apply c h w)⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl, rfl⟩
    exact word_weight c h w

theorem degree_eq_bot_of_neg (c h : ℂ) (d : ℤ) (hd : d < 0) :
    degree c h d = ⊥ := by
  rw [degree_span, ← Submodule.span_empty]
  congr 1
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro y ⟨w, hw, _⟩
  omega

theorem degree_zero (c h : ℂ) :
    degree c h 0 = Submodule.span ℂ {top c h} := by
  rw [degree_span]
  congr 1
  ext x
  constructor
  · rintro ⟨w, hd, rfl⟩
    cases hw : w.val with
    | nil => simp only [applyWord_nil, Set.mem_singleton_iff]
    | cons i l =>
      simp only [wordDegree, hw, List.map_cons, List.sum_cons, Nat.cast_add] at hd
      omega
  · intro hx
    exact ⟨Shared.Lie.PBW.emptyWord ℕ, rfl, Set.mem_singleton_iff.mp hx⟩

theorem kills_below (c h : ℂ) (j d : ℤ) (x : M c h) (hx : x ∈ degree c h d)
    (hd : d - j < 0) : ⁅L j, x⁆ = 0 := by
  have hy := shift c h j d x hx
  rw [degree_eq_bot_of_neg c h (d - j) hd] at hy
  exact (Submodule.mem_bot ℂ).mp hy

theorem central_action (c h : ℂ) (x : M c h) : ⁅C, x⁆ = c • x := by
  have hw (w : List ℕ) : ⁅C, applyWord c h w⁆ = c • applyWord c h w := by
    induction w with
    | nil => exact (highestWeight c h).1
    | cons i w ih =>
      rw [applyWord_cons, leibniz_lie, Vir.lie_C, zero_lie, zero_add, ih, lie_smul]
  have he : LieModule.toEnd ℂ Vir (M c h) C = c • LinearMap.id := by
    apply (basis c h).ext
    intro w
    rw [basis_apply, LieModule.toEnd_apply_apply, LinearMap.smul_apply, LinearMap.id_apply]
    exact hw w.val
  exact congrArg (fun f : Module.End ℂ (M c h) => f x) he

section Universal

variable {X : Type*} [AddCommGroup X] [Module ℂ X] [LieRingModule Vir X] [LieModule ℂ Vir X]

private theorem highestWeight_borel {c h : ℂ} {x : X} (hx : IsHighestWeight c h x)
    (y : borel) : ⁅(y : Vir), x⁆ = functional c h y • x := by
  let F := (LinearMap.applyₗ (R := ℂ) x).comp
    ((LieModule.toEnd ℂ Vir X).toLinearMap.comp borel.incl.toLinearMap)
  let G := (LinearMap.toSpanSingleton ℂ X x).comp (functional c h)
  have he : F = G := by
    apply borelBasis.ext
    intro i
    change ⁅(borelBasis i : Vir), x⁆ = functional c h (borelBasis i) • x
    rw [coe_borelBasis, functional_basis]
    rcases i with (n | u)
    · cases n with
      | zero => exact hx.2.1
      | succ n =>
        change ⁅L (↑(n + 1) : ℤ), x⁆ = (0 : ℂ) • x
        rw [zero_smul]
        exact hx.2.2 _ (by omega)
    · exact hx.1
  exact congrArg (fun f : borel →ₗ[ℂ] X => f y) he

private def envelopingAction (X : Type*) [AddCommGroup X] [Module ℂ X]
    [LieRingModule Vir X] [LieModule ℂ Vir X] : U Vir →ₐ[ℂ] Module.End ℂ X :=
  UniversalEnvelopingAlgebra.lift ℂ (LieModule.toEnd ℂ Vir X)

private theorem highestWeight_enveloping {c h : ℂ} {x : X} (hx : IsHighestWeight c h x)
    (u : U borel) : envelopingAction X (inclusion borel u) x = character c h u • x := by
  let ρ := (envelopingAction X).comp (inclusion borel)
  change ρ u x = character c h u • x
  obtain ⟨a, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ borel) u
  change ρ (UniversalEnvelopingAlgebra.mkAlgHom ℂ borel a) x =
    character c h (UniversalEnvelopingAlgebra.mkAlgHom ℂ borel a) • x
  induction a using TensorAlgebra.induction with
  | algebraMap k =>
    rw [AlgHom.commutes, ρ.commutes, (character c h).commutes, Algebra.algebraMap_self]
    rfl
  | ι y =>
    change envelopingAction X (inclusion borel (ι ℂ y)) x = character c h (ι ℂ y) • x
    rw [inclusion_ι, envelopingAction, character, UniversalEnvelopingAlgebra.lift_ι_apply,
      UniversalEnvelopingAlgebra.lift_ι_apply]
    exact highestWeight_borel hx y
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, ha, hb, add_smul]
  | mul a b ha hb =>
    simp only [map_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul, mul_comm]

theorem universal (c h : ℂ) (x : X) (hx : IsHighestWeight c h x) :
    ∃! f : M c h →ₗ⁅ℂ,Vir⁆ X, f (top c h) = x := by
  let _ := characterModule c h
  let _ := character_tower c h
  let ρ := envelopingAction X
  let _ : Module (U Vir) X := Module.compHom X ρ.toRingHom
  let _ : IsScalarTower ℂ (U Vir) X := IsScalarTower.of_algebraMap_smul fun a z => by
    change ρ (algebraMap ℂ (U Vir) a) z = a • z
    rw [ρ.commutes]
    rfl
  let _ : Module (U borel) X := restrictModule (inclusion borel) X
  let f : ℂ →ₗ[U borel] X :=
    { toFun := fun z => z • x
      map_add' := fun z w => add_smul z w x
      map_smul' := fun u z => by
        change (character c h u * z) • x = ρ (inclusion borel u) (z • x)
        rw [map_smul, highestWeight_enveloping hx, smul_smul, mul_comm] }
  let F : M c h →ₗ[U Vir] X := extend (inclusion borel) f
  let F' : M c h →ₗ⁅ℂ,Vir⁆ X :=
    { F.restrictScalars ℂ with
      map_lie' := fun {y z} => by
        change F ((ι ℂ y) • z) = ⁅y, F z⁆
        rw [map_smul]
        change ρ (ι ℂ y) (F z) = _
        change UniversalEnvelopingAlgebra.lift ℂ (LieModule.toEnd ℂ Vir X) (ι ℂ y) (F z) = _
        rw [UniversalEnvelopingAlgebra.lift_ι_apply]
        rfl }
  have hF : F' (top c h) = x := by
    change extend (inclusion borel) f (induceTensor (inclusion borel) 1 (1 : ℂ)) = x
    rw [extend_tensor, one_smul]
    exact one_smul ℂ x
  refine ⟨F', hF, ?_⟩
  intro G hG
  apply LieModuleHom.coe_injective
  change ((G : M c h →ₗ[ℂ] X) : M c h → X) = ((F' : M c h →ₗ[ℂ] X) : M c h → X)
  congr 1
  apply (basis c h).ext
  intro w
  rw [basis_apply]
  change G (applyWord c h w.val) = F' (applyWord c h w.val)
  generalize w.val = l
  induction l with
  | nil => exact hG.trans hF.symm
  | cons i l ih => rw [applyWord_cons, LieModuleHom.map_lie, LieModuleHom.map_lie, ih]

end Universal

/-- All properties of the construction on the canonical inducing data. -/
theorem modelProperties : VermaSpec.ModelProperties inducingData where
  top_ne_zero := top_ne_zero
  highestWeight := highestWeight
  cyclic := cyclic
  universal := by
    intro c h X _ _ _ _ x hx
    exact universal c h x hx
  central_action := central_action
  orderedBasis := fun c h => ⟨basis c h, basis_apply c h⟩
  word_weight := word_weight
  degree_span := degree_span
  degree_zero := degree_zero
  shift := shift
  kills_below := kills_below

theorem modelExists : VermaSpec.ModelExists :=
  ⟨inferInstanceAs (LieRing Vir), inferInstanceAs (LieAlgebra ℂ Vir),
    rfl, HEq.rfl, fun _ _ => rfl, inducingData, modelProperties⟩

end LieNotes.Virasoro.Verma
