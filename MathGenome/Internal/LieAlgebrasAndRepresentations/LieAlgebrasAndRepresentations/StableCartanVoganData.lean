import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.StableCartanVoganData
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealRootSpace
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SerreRelations
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Reconstruction
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

namespace LieAlgebrasAndRepresentations.StableCartanVoganData

open Specs.LieAlgebrasAndRepresentations.StableCartanVoganData
open Specs.LieAlgebrasAndRepresentations.PolarRealStructures (IsCompact hermitian)
open LieAlgebrasAndRepresentations.RealForms
open LieAlgebrasAndRepresentations.Serre
open scoped ComplexConjugate

universe u v

section Converse

variable {ι : Type v} [DecidableEq ι] {A : Matrix ι ι ℤ}
variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

omit [DecidableEq ι] in
private theorem sign_sq (d : DiagramData A) (i : ι) : d.sign i * d.sign i = 1 := by
  rcases d.sign_cases i with h | h <;> simp [h]

omit [DecidableEq ι] in
private theorem sign_conj (d : DiagramData A) (i : ι) :
    star (d.sign i) = d.sign i := by
  rcases d.sign_cases i with h | h <;> simp [h]

private theorem sign_perm (d : DiagramData A) (i : ι) : d.sign (d.perm i) = d.sign i := by
  by_cases h : d.perm i = i
  · rw [h]
  · rw [d.paired i h, d.paired (d.perm i) (by simpa only [d.involutive i] using Ne.symm h)]

private theorem iterBracket_smul_pair (c q : ℂ) (x y : L) (n : ℕ) :
    iterBracket (c • x) n (q • y) = (c ^ n * q) • iterBracket x n y := by
  induction n with
  | zero => simp [iterBracket]
  | succ n ih =>
    rw [iterBracket, iterBracket, ih, smul_lie, lie_smul, smul_smul, pow_succ']
    rw [mul_assoc]

private theorem diagram_relations (d : DiagramData A) {E F C : ι → L}
    (hr : RelationsHold A E F C) :
    RelationsHold A (fun i => d.sign i • E (d.perm i))
      (fun i => d.sign i • F (d.perm i)) (C ∘ d.perm) := by
  rcases hr with ⟨hh, he, hf, hef, hee, hff⟩
  refine ⟨fun i j => hh _ _, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    simp only [Function.comp_apply, lie_smul, he, d.preserves, smul_comm (d.sign j) (A i j)]
  · intro i j
    simp only [Function.comp_apply, lie_smul, hf, d.preserves, smul_neg,
      smul_comm (d.sign j) (A i j)]
  · intro i j
    simp only [smul_lie, lie_smul, smul_smul, hef]
    by_cases hij : i = j
    · subst j
      simp [sign_sq]
    · simp [hij, show d.perm i ≠ d.perm j from fun h => hij (d.perm.injective h)]
  · intro i j hij
    rw [iterBracket_smul_pair, ← d.preserves i j,
      hee _ _ (fun h => hij (d.perm.injective h)), smul_zero]
  · intro i j hij
    rw [iterBracket_smul_pair, ← d.preserves i j,
      hff _ _ (fun h => hij (d.perm.injective h)), smul_zero]

private theorem presentation_relations (p : Algebra A ≃ₗ⁅ℂ⁆ L)
    (ha : ∀ i j, i ≠ j → A i j ≤ 0) :
    RelationsHold A (fun i => p (e A i)) (fun i => p (f A i)) (fun i => p (h A i)) := by
  rcases relations_spec A ha with ⟨hh, he, hf, hef, hee, hff⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    simpa only [p.map_lie, map_zero] using congrArg p (hh i j)
  · intro i j
    simpa only [p.map_lie, map_zsmul] using congrArg p (he i j)
  · intro i j
    simpa only [p.map_lie, map_neg, map_zsmul] using congrArg p (hf i j)
  · intro i j
    have h := congrArg p (hef i j)
    by_cases hij : i = j
    · rw [ite_eq_left hij] at h ⊢
      simpa only [p.map_lie] using h
    · rw [ite_eq_right hij] at h ⊢
      simpa only [p.map_lie, map_zero] using h
  · intro i j hij
    change iterBracket (p.toLieHom (e A i)) _ (p.toLieHom (e A j)) = 0
    rw [← map_iterBracket, hee i j hij, map_zero]
  · intro i j hij
    change iterBracket (p.toLieHom (f A i)) _ (p.toLieHom (f A j)) = 0
    rw [← map_iterBracket, hff i j hij, map_zero]

theorem realize : realize_type.{u,v} := by
  intro ι _ A ha d L _ _ ω E F C hp hω
  dsimp only
  obtain ⟨p, pe, pf, pc⟩ := hp
  have hr : RelationsHold A E F C := by
    rw [← funext pe, ← funext pf, ← funext pc]
    exact presentation_relations p ha
  have hr' := diagram_relations d hr
  refine ⟨hr', ?_⟩
  let b := (Serre.lift A ha _ _ _ hr').comp p.symm.toLieHom
  have be (i) : b (E i) = d.sign i • E (d.perm i) := by
    rw [← pe i]
    change Serre.lift A ha _ _ _ hr' (p.symm (p (e A i))) = _
    rw [LieEquiv.symm_apply_apply, lift_e]
  have bf (i) : b (F i) = d.sign i • F (d.perm i) := by
    rw [← pf i]
    change Serre.lift A ha _ _ _ hr' (p.symm (p (f A i))) = _
    rw [LieEquiv.symm_apply_apply, lift_f]
  have bc (i) : b (C i) = C (d.perm i) := by
    rw [← pc i]
    change Serre.lift A ha _ _ _ hr' (p.symm (p (h A i))) = _
    rw [LieEquiv.symm_apply_apply, lift_h]
    rfl
  have b2 : (b.comp b).comp p.toLieHom = p.toLieHom := by
    apply Serre.hom_ext A
    · intro i
      change b (b (p (e A i))) = p (e A i)
      rw [pe, be, map_smul, be, d.involutive, sign_perm, smul_smul, sign_sq, one_smul]
    · intro i
      change b (b (p (f A i))) = p (f A i)
      rw [pf, bf, map_smul, bf, d.involutive, sign_perm, smul_smul, sign_sq, one_smul]
    · intro i
      change b (b (p (h A i))) = p (h A i)
      rw [pc, bc, bc, d.involutive]
  have hb : Function.Involutive b := by
    intro x
    obtain ⟨y, rfl⟩ := p.surjective x
    exact LieHom.congr_fun b2 y
  let a := LieEquiv.ofBijective b ⟨hb.injective, hb.surjective⟩
  let K : LieSubalgebra ℂ (Algebra A) :=
    { carrier := {x | ω.map (b (p x)) = b (ω.map (p x))}
      zero_mem' := by simp
      add_mem' := by intro x y hx hy; simp only [Set.mem_ofPred_eq, map_add] at *; rw [hx, hy]
      smul_mem' := by
        intro r x hx
        simp only [Set.mem_ofPred_eq, map_smul, ω.antilinear] at *
        rw [hx]
      lie_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq, LieEquiv.map_lie, LieHom.map_lie] at *
        rw [hx, hy] }
  have hK : K = ⊤ := by
    apply Serre.generators_generate A
    · intro i
      change ω.map (b (p (e A i))) = b (ω.map (p (e A i)))
      rw [pe, be, ω.antilinear, sign_conj d, (hω (d.perm i)).1,
        (hω i).1, map_neg, bf, smul_neg]
    · intro i
      change ω.map (b (p (f A i))) = b (ω.map (p (f A i)))
      rw [pf, bf, ω.antilinear, sign_conj d, (hω (d.perm i)).2.1,
        (hω i).2.1, map_neg, be, smul_neg]
    · intro i
      change ω.map (b (p (h A i))) = b (ω.map (p (h A i)))
      rw [pc, bc, (hω (d.perm i)).2.2, (hω i).2.2, map_neg, bc]
  have hcomm : Intertwines ω ω a := by
    intro x
    obtain ⟨y, rfl⟩ := p.surjective x
    have hm : y ∈ K := by rw [hK]; trivial
    exact hm
  obtain ⟨θ, hθ⟩ := restrict_complex_isomorphism ω ω a hcomm
  refine ⟨a, hcomm, hb, fun i => ⟨be i, bf i, bc i⟩, θ, ?_, fun x => (hθ x).symm⟩
  intro x
  apply Subtype.ext
  rw [hθ, hθ]
  exact hb _

end Converse

section Cartan

open Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature (complexFixed)
open Specs.LieAlgebrasAndRepresentations.SerreRelations (positive simple)
open Complex
open private hermitian_positive killing_conjugation from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

local notation "B" => _root_.killingForm ℂ L

omit [FiniteDimensional ℂ L] in
private theorem killing_bracket (x y z : L) : B ⁅x, y⁆ z = B x ⁅y, z⁆ :=
  LieModule.traceForm_apply_lie_apply ℂ L L x y z

private theorem eq_zero_of_killing_conj (ω : Conjugation L) (hc : IsCompact ω)
    {x : L} (hx : B (ω.map x) x = 0) : x = 0 := by
  by_contra h
  have ht := hermitian_positive ω hc h
  change 0 < (-B (ω.map x) x).re at ht
  simp [hx] at ht

private def centralizer (S : Set L) : LieSubalgebra ℂ L where
  carrier := {x | ∀ y ∈ S, ⁅y, x⁆ = 0}
  zero_mem' := fun y _ => lie_zero y
  add_mem' hx hy := fun z hz => by rw [lie_add, hx z hz, hy z hz, add_zero]
  smul_mem' c _ hx := fun y hy => by rw [lie_smul, hx y hy, smul_zero]
  lie_mem' hx hy := fun z hz => by rw [leibniz_lie, hx z hz, hy z hz, zero_lie, lie_zero, add_zero]

omit [FiniteDimensional ℂ L] in
private theorem mem_centralizer {S : Set L} {x : L} :
    x ∈ centralizer S ↔ ∀ y ∈ S, ⁅y, x⁆ = 0 := Iff.rfl

omit [LieAlgebra ℂ L] [FiniteDimensional ℂ L] in
private theorem lie_flip_zero {x y : L} (h : ⁅x, y⁆ = 0) : ⁅y, x⁆ = 0 := by
  rw [← lie_skew, h, neg_zero]

private theorem exists_compact_abelian (ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L) :
    ∃ S : Submodule ℝ L,
      (∀ x ∈ S, ω.map x = x ∧ a x = x) ∧
      (∀ x ∈ S, ∀ y ∈ S, ⁅x, y⁆ = 0) ∧
      ∀ x, ω.map x = x → a x = x → (∀ y ∈ S, ⁅y, x⁆ = 0) → x ∈ S := by
  let : FiniteDimensional ℝ L := FiniteDimensional.trans ℝ ℂ L
  let P (S : Submodule ℝ L) := (∀ x ∈ S, ω.map x = x ∧ a x = x) ∧
    (∀ x ∈ S, ∀ y ∈ S, ⁅x, y⁆ = 0)
  have hbot : P ⊥ := by
    constructor
    · intro x hx
      rw [(Submodule.mem_bot ℝ).mp hx]
      exact ⟨map_zero _, map_zero _⟩
    · intro x hx y _
      rw [(Submodule.mem_bot ℝ).mp hx, zero_lie]
  obtain ⟨S, hS⟩ := exists_maximal_of_wellFoundedGT P ⟨⊥, hbot⟩
  refine ⟨S, hS.1.1, hS.1.2, ?_⟩
  intro x hωx hax hx
  let U := S ⊔ Submodule.span ℝ {x}
  have hU : P U := by
    constructor
    · intro y hy
      obtain ⟨s, hs, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hw
      obtain ⟨hωs, has⟩ := hS.1.1 s hs
      refine ⟨by rw [map_add, map_smul, hωs, hωx], ?_⟩
      change a (s + (r : ℂ) • x) = s + (r : ℂ) • x
      rw [map_add, map_smul, has, hax]
    · intro y hy z hz
      obtain ⟨s, hs, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨t, ht, v, hv, rfl⟩ := Submodule.mem_sup.mp hz
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hw
      obtain ⟨q, rfl⟩ := Submodule.mem_span_singleton.mp hv
      simp [add_lie, lie_add, smul_lie, lie_smul, hS.1.2 s hs t ht, hx s hs,
        lie_flip_zero (hx t ht)]
  exact hS.2 hU le_sup_left ((le_sup_right : Submodule.span ℝ {x} ≤ U)
    (Submodule.mem_span_singleton_self x))

omit [FiniteDimensional ℂ L] in
private theorem cartan_compl (a : L ≃ₗ⁅ℂ⁆ L) (ha : Function.Involutive a)
    (H : LieSubalgebra ℂ L) (hs : ∀ x ∈ H, a x ∈ H) :
    IsCompl (cartanEigenspace a H 1) (cartanEigenspace a H (-1)) := by
  have mem (r : ℂ) (x : H) : x ∈ cartanEigenspace a H r ↔ a x = r • (x : L) := by
    simp [cartanEigenspace, sub_eq_zero]
    rfl
  refine ⟨Submodule.disjoint_def.mpr ?_, codisjoint_iff.mpr ?_⟩
  · intro x hx hy
    have e := ((mem 1 x).mp hx).symm.trans ((mem (-1) x).mp hy)
    simp only [one_smul, neg_smul] at e
    apply Subtype.ext
    change (x : L) = 0
    linear_combination (norm := module) (1 / 2 : ℂ) • e
  · apply top_unique
    intro x _
    let y : H := ⟨a x, hs x x.property⟩
    let p := (2 : ℂ)⁻¹ • (x + y)
    let q := (2 : ℂ)⁻¹ • (x - y)
    have hp : p ∈ cartanEigenspace a H 1 := (mem _ _).mpr (by
      change a ((2 : ℂ)⁻¹ • ((x : L) + a x)) = _
      change a ((2 : ℂ)⁻¹ • ((x : L) + a x)) = (1 : ℂ) • ((2 : ℂ)⁻¹ • ((x : L) + a x))
      rw [map_smul, map_add, ha (x : L), add_comm (a x) (x : L), one_smul])
    have hq : q ∈ cartanEigenspace a H (-1) := (mem _ _).mpr (by
      change a ((2 : ℂ)⁻¹ • ((x : L) - a x)) = (-1 : ℂ) • ((2 : ℂ)⁻¹ • ((x : L) - a x))
      rw [map_smul, map_sub, ha (x : L)]
      module)
    exact Submodule.mem_sup.mpr ⟨p, hp, q, hq, by dsimp [p, q]; module⟩

omit [FiniteDimensional ℂ L] in
private theorem root_transport (a : L ≃ₗ⁅ℂ⁆ L) (ha : Function.Involutive a)
    (H : LieSubalgebra ℂ L) (hH : ∀ x ∈ H, a x ∈ H)
    (α : Module.Dual ℂ H) {x : L} (hx : x ∈ rootSpace H α) :
    a x ∈ rootSpace H (rootAction a H hH α) := by
  rw [mem_rootSpace] at hx ⊢
  intro y
  have h := congrArg a (hx ⟨a y, hH y y.property⟩)
  change ⁅(y : L), a x⁆ = α ⟨a y, hH y y.property⟩ • a x
  simpa only [LieEquiv.map_lie, map_smul, ha (y : L)] using h

omit [FiniteDimensional ℂ L] in
private theorem rootAction_involutive (a : L ≃ₗ⁅ℂ⁆ L) (ha : Function.Involutive a)
    (H : LieSubalgebra ℂ L) (hH : ∀ x ∈ H, a x ∈ H) :
    Function.Involutive (rootAction a H hH) := by
  intro α
  ext y
  change α (⟨a (a y), _⟩ : H) = α y
  exact congrArg α (Subtype.ext (ha y))

omit [FiniteDimensional ℂ L] in
private theorem rootAction_mem (a : L ≃ₗ⁅ℂ⁆ L) (ha : Function.Involutive a)
    (H : LieSubalgebra ℂ L) (hH : ∀ x ∈ H, a x ∈ H) {α : Module.Dual ℂ H}
    (hα : α ∈ rootSet H) : rootAction a H hH α ∈ rootSet H := by
  refine ⟨?_, ?_⟩
  · intro h
    apply hα.1
    rw [← rootAction_involutive a ha H hH α, h]
    rfl
  · obtain ⟨x, hx, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα.2
    intro h
    have hm := root_transport a ha H hH α hx
    change rootSpace H (rootAction a H hH α) = ⊥ at h
    rw [h, Submodule.mem_bot] at hm
    exact hn (a.injective (hm.trans (map_zero a).symm))

private theorem root_on_imaginary_compact (ω : Conjugation L) (hc : IsCompact ω)
    (H : LieSubalgebra ℂ L) (z : H) (hz : ω.map z = -(z : L))
    (α : Module.Dual ℂ H) (hα : α ∈ rootSet H) : (α z).re = α z := by
  obtain ⟨x, hx, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα.2
  have hex := (mem_rootSpace H α x).mp hx z
  have hne : B (ω.map x) x ≠ 0 := fun h => hn (eq_zero_of_killing_conj ω hc h)
  have hconj : star (α z) * B (ω.map x) x = α z * B (ω.map x) x := by
    calc
      _ = B (ω.map ⁅(z : L), x⁆) x := by rw [hex, ω.antilinear, map_smul]; rfl
      _ = B (ω.map x) ⁅(z : L), x⁆ := by
        rw [LieHom.map_lie, hz, neg_lie, map_neg, LinearMap.neg_apply]
        exact neg_eq_iff_eq_neg.mpr (LieModule.traceForm_apply_lie_apply' ℂ L L _ _ _)
      _ = _ := by rw [hex, map_smul]; rfl
  have he := mul_right_cancel₀ hne hconj
  apply Complex.ext
  · simp
  · have hi := congrArg Complex.im he
    simp only [Complex.star_def, Complex.conj_im] at hi
    simp only [Complex.ofReal_im]
    linarith

theorem stable_order : stable_order_type.{u} := by
  intro L _ _ _ hss ω hc a hcomm ha
  obtain ⟨S, hs, hab, hmax⟩ := exists_compact_abelian ω a
  -- Centralize the maximal abelian subspace of the real fixed algebra.
  let H := centralizer (S : Set L)
  have sle {x : L} (hx : x ∈ S) : x ∈ H :=
    mem_centralizer.mpr fun y hy => hab y hy x hx
  have hstable : ∀ x ∈ H, a x ∈ H := by
    intro x hx
    apply mem_centralizer.mpr
    intro y hy
    rw [← (hs y hy).2, ← LieEquiv.map_lie, (mem_centralizer.mp hx) y hy, map_zero]
  have wstable : ∀ x ∈ H, ω.map x ∈ H := by
    intro x hx
    apply mem_centralizer.mpr
    intro y hy
    rw [← (hs y hy).1, ← LieHom.map_lie, (mem_centralizer.mp hx) y hy, map_zero]
  have split_fixed {x : L} (hx : x ∈ H) (hax : a x = x) :
      ∃ s ∈ S, ∃ t ∈ S, s + I • t = x := by
    obtain ⟨s, t, es, et, est⟩ := fixed_parts_formula ω x
    have eaw : a (ω.map x) = ω.map x := by rw [← hcomm, hax]
    have sh : (s : L) ∈ H := by rw [es]; exact H.smul_mem _ (H.add_mem hx (wstable x hx))
    have th : (t : L) ∈ H := by rw [et]; exact H.smul_mem _ (H.sub_mem hx (wstable x hx))
    have sa : a (s : L) = (s : L) := by rw [es, map_smul, map_add, hax, eaw]
    have ta : a (t : L) = (t : L) := by rw [et, map_smul, map_sub, hax, eaw]
    exact ⟨s, hmax s s.property sa (mem_centralizer.mp sh),
      t, hmax t t.property ta (mem_centralizer.mp th), est⟩
  have fixed_central {x y : L} (hx : x ∈ H) (hax : a x = x) (hy : y ∈ H) : ⁅x, y⁆ = 0 := by
    obtain ⟨s, hs', t, ht', hst⟩ := split_fixed hx hax
    rw [← hst, add_lie, smul_lie, (mem_centralizer.mp hy) s hs',
      (mem_centralizer.mp hy) t ht', smul_zero, add_zero]
  -- The fixed part is central in H. Involution invariance puts every bracket
  -- in this part, and the Killing form then forces that bracket to vanish.
  have habel {x y : L} (hx : x ∈ H) (hy : y ∈ H) : ⁅x, y⁆ = 0 := by
    have sum_central {v w : L} (hv : v ∈ H) (hw : w ∈ H) : ⁅v + a v, w⁆ = 0 :=
      fixed_central (H.add_mem hv (hstable v hv)) (by rw [map_add, ha, add_comm]) hw
    have neq : ⁅a x, a y⁆ = ⁅x, y⁆ := by
      have h₁ := sum_central hx (hstable y hy)
      have h₂ := lie_flip_zero (sum_central hy hx)
      rw [add_lie] at h₁
      rw [lie_add] at h₂
      exact (eq_neg_of_add_eq_zero_right h₁).trans (neg_eq_of_add_eq_zero_left h₂)
    have hb : a ⁅x, y⁆ = ⁅x, y⁆ := (a.map_lie x y).trans neq
    have hbr := H.lie_mem hx hy
    apply eq_zero_of_killing_conj ω hc
    rw [← killing_bracket, fixed_central (wstable _ hbr)
      (by rw [← hcomm, hb]) hx, map_zero, LinearMap.zero_apply]
  have hnormal {x y : L} (hy : y ∈ H) (hb : ⁅x, y⁆ ∈ H) : ⁅x, y⁆ = 0 := by
    have hzero := habel hy (wstable _ hb)
    have hk := LieModule.traceForm_comm ℂ L L (ω.map ⁅x, y⁆) ⁅x, y⁆
    change _root_.killingForm ℂ L (ω.map ⁅x, y⁆) ⁅x, y⁆ =
      _root_.killingForm ℂ L ⁅x, y⁆ (ω.map ⁅x, y⁆) at hk
    rw [killing_bracket, hzero, map_zero] at hk
    exact eq_zero_of_killing_conj ω hc hk
  have hcart : H.IsCartanSubalgebra := by
    have : IsLieAbelian H := ⟨fun x y => Subtype.ext (habel x.property y.property)⟩
    refine ⟨inferInstance, le_antisymm ?_ H.le_normalizer⟩
    intro x hx
    apply mem_centralizer.mpr
    intro y hy
    exact lie_flip_zero (hnormal (sle hy) ((H.mem_normalizer_iff x).mp hx y (sle hy)))
  have hkcart : (fixedCartan a H).IsCartanSubalgebra := by
    let K := fixedCartan a H
    have : IsLieAbelian K := ⟨fun x y => Subtype.ext (Subtype.ext (habel x.property y.property))⟩
    refine ⟨inferInstance, le_antisymm ?_ K.le_normalizer⟩
    intro x hx
    change (x : L) ∈ H
    apply mem_centralizer.mpr
    intro y hy
    let y' : complexFixed a := ⟨y, (hs y hy).2⟩
    have hy' : y' ∈ K := sle hy
    exact lie_flip_zero (hnormal (sle hy) ((K.mem_normalizer_iff x).mp hx y' hy'))
  let := hcart
  have htoral := RealRootSpace.cartan_isMaximalToral hss H
  have root_on_S : ∀ α ∈ rootSet H, ∃ s : S, α ⟨s, sle s.property⟩ ≠ 0 := by
    intro α hα
    by_contra! hz
    obtain ⟨x, hx, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα.2
    have ex := (mem_rootSpace H α x).mp hx
    have xH : x ∈ H := mem_centralizer.mpr fun y hy => by rw [ex ⟨y, sle hy⟩, hz ⟨y, hy⟩, zero_smul]
    apply hα.1
    ext y
    have he : α y • x = 0 := (ex y).symm.trans (habel y.property xH)
    exact (smul_eq_zero.mp he).resolve_right hn
  let hH : StableCartan ω a H :=
    ⟨htoral, hcart, hstable, wstable, hkcart, cartan_compl a ha H hstable, by
      intro α hα
      obtain ⟨s, h⟩ := root_on_S α hα
      exact ⟨⟨s, sle s.property⟩, (hs s s.property).2, h⟩⟩
  let : Finite (rootSet H) := (rootSet_finite H htoral.1).to_subtype
  let j : S →ₗ[ℝ] H :=
    (((I • (LinearMap.id : L →ₗ[ℂ] L)).restrictScalars ℝ).comp S.subtype).codRestrict
      (H.toSubmodule.restrictScalars ℝ) fun t => H.smul_mem I (sle t.property)
  have wj (s : S) : ω.map (j s : L) = -(j s : L) := by
    change ω.map (I • (s : L)) = -(I • (s : L))
    rw [ω.antilinear, (hs s s.property).1, Complex.star_def, conj_I, neg_smul]
  have aj (s : S) : a (j s : L) = (j s : L) := by
    change a (I • (s : L)) = I • (s : L)
    rw [map_smul, (hs s s.property).2]
  let eval (α : rootSet H) : Module.Dual ℝ S :=
    Complex.reLm.comp ((α.val.restrictScalars ℝ).comp j)
  have eval_exists (α : rootSet H) : ∃ s, eval α s ≠ 0 := by
    obtain ⟨s, h⟩ := root_on_S α α.property
    refine ⟨s, ?_⟩
    intro hzero
    have hr := root_on_imaginary_compact ω hc H (j s) (wj s) α α.property
    have e : α.val (j s) = 0 := by
      rw [← hr]
      exact congrArg Complex.ofReal hzero
    change α.val (I • (⟨(s : L), sle s.property⟩ : H)) = 0 at e
    rw [map_smul, smul_eq_mul] at e
    exact h ((mul_eq_zero.mp e).resolve_left I_ne_zero)
  obtain ⟨s, hreg⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists eval eval_exists
  refine ⟨H, hH, j s, aj s, wj s,
    root_on_imaginary_compact ω hc H (j s) (wj s), fun α hα => hreg ⟨α, hα⟩, ?_⟩
  intro α
  have h_eval : evaluation H (j s) (rootAction a H hstable α) = evaluation H (j s) α := by
    change (α (⟨a (j s : L), _⟩ : H)).re = (α (j s)).re
    exact congrArg (fun z => (α z).re) (Subtype.ext (aj s))
  have hroot : rootAction a H hstable α ∈ rootSet H ↔ α ∈ rootSet H := by
    refine ⟨fun h => ?_, rootAction_mem a ha H hstable⟩
    simpa only [rootAction_involutive a ha H hstable α] using rootAction_mem a ha H hstable h
  change (_ ∈ rootSet H ∧ _) ↔ (α ∈ rootSet H ∧ _)
  rw [h_eval, hroot]

end Cartan

section SimpleTriples

open Complex
open Specs.LieAlgebrasAndRepresentations.SerreRelations (positive simple)
open Specs.LieAlgebrasAndRepresentations.RealRootSpace
  (realCartan realRoots rootRestriction extension)
open Specs.LieAlgebrasAndRepresentations.RealRootSpace renaming E → RootDual
open Specs.LieAlgebrasAndRepresentations.SolvableRadical (IsSemisimple_value)
open private hermitian_positive killing_conjugation from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
local notation "B" => _root_.killingForm ℂ L

private theorem root_conjugation (ω : Conjugation L) (hc : IsCompact ω)
    (H : LieSubalgebra ℂ L) (hw : ∀ x ∈ H, ω.map x ∈ H)
    (α : Module.Dual ℂ H) {x : L} (hx : x ∈ rootSpace H α) (hn : x ≠ 0) :
    ω.map x ∈ rootSpace H (-α) := by
  have ex := (mem_rootSpace H α x).mp hx
  have hne : B (ω.map x) x ≠ 0 := fun h => hn (eq_zero_of_killing_conj ω hc h)
  have conj_eval (y z : H) (hz : (z : L) = ω.map y) : star (α y) = -α z := by
    apply mul_right_cancel₀ hne
    calc
      _ = B (ω.map ⁅(y : L), x⁆) x := by rw [ex y, ω.antilinear, map_smul]; rfl
      _ = - B (ω.map x) ⁅(z : L), x⁆ := by
        rw [LieHom.map_lie, ← hz]
        exact LieModule.traceForm_apply_lie_apply' ℂ L L _ _ _
      _ = _ := by rw [ex z, map_smul, smul_eq_mul, neg_mul]
  rw [mem_rootSpace]
  intro y
  let z : H := ⟨ω.map y, hw y y.property⟩
  have h := congrArg ω.map (ex z)
  change ⁅(y : L), ω.map x⁆ = -α y • ω.map x
  rw [LieHom.map_lie, ω.antilinear, conj_eval z y (ω.involutive y).symm] at h
  change ⁅ω.map (ω.map (y : L)), ω.map x⁆ = _ at h
  rw [ω.involutive (y : L)] at h
  exact h

private theorem compact_triple (hss : IsSemisimple_value ℂ L)
    (ω : Conjugation L) (hc : IsCompact ω)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H) (hw : ∀ x ∈ H, ω.map x ∈ H)
    (α : Module.Dual ℂ H) (hα : α ∈ rootSet H) :
    ∃ x : L, x ∈ rootSpace H α ∧ x ≠ 0 ∧
      ⁅x, -ω.map x⁆ = (killingCoroot H α : L) := by
  obtain ⟨x, hx, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα.2
  have hwx := root_conjugation ω hc H hw α hx hn
  let d := RealRootSpace.realization_of_maximalToral hss H hH
  let : NormedAddCommGroup (RootDual H) := d.normedAddCommGroup
  let : InnerProductSpace ℝ (RootDual H) := d.innerProductSpace
  let l := inner ℝ (rootRestriction H α) (rootRestriction H α)
  have hl : (l : ℂ) = rootForm H α α := d.root_form_agrees α hα α hα
  have hl_pos : 0 < l := by
    apply lt_of_le_of_ne real_inner_self_nonneg
    intro h
    apply rootForm_self_ne_zero hss H hH α hα
    have hlz : l = 0 := h.symm
    rw [← hl, hlz, ofReal_zero]
  let k := (hermitian ω x x).re
  have hk : 0 < k := hermitian_positive ω hc hn
  have hkr : (k : ℂ) = B x (-ω.map x) := by
    have hs : B (ω.map x) x = B x (ω.map x) := LieModule.traceForm_comm ℂ L L _ _
    have hconj := killing_conjugation ω (ω.map x) x
    rw [ω.involutive, ← hs] at hconj
    change B (ω.map x) x = star (B (ω.map x) x) at hconj
    have him := congrArg im hconj
    simp only [Complex.star_def, conj_im] at him
    change ((-B (ω.map x) x).re : ℂ) = B x (-ω.map x)
    rw [map_neg, ← hs]
    apply Complex.ext <;> simp
    linarith
  -- Scale the positive root vector by a real number so its opposite remains
  -- the negative of its compact conjugate.
  let c := Real.sqrt (2 / (l * k))
  have hc_pos : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hc_sq : c ^ 2 = 2 / (l * k) := Real.sq_sqrt (by positivity)
  refine ⟨(c : ℂ) • x, Submodule.smul_mem _ _ hx,
    smul_ne_zero (Complex.ofReal_ne_zero.mpr hc_pos.ne') hn, ?_⟩
  rw [ω.antilinear, Complex.star_def, conj_ofReal, ← smul_neg, smul_lie, lie_smul,
    opposite_root_bracket hss H hH α x (-ω.map x) hx (Submodule.neg_mem _ hwx),
    smul_smul, smul_smul]
  change ((c : ℂ) * (c : ℂ) * B x (-ω.map x)) • (tAlpha H α : L) =
    (2 / rootForm H α α) • (tAlpha H α : L)
  rw [← hkr, ← hl]
  congr 1
  have he : c * c * k = 2 / l := by
    rw [← pow_two, hc_sq]
    field_simp
  exact_mod_cast he

private theorem coroot_transport (hss : IsSemisimple_value ℂ L)
    (a : L ≃ₗ⁅ℂ⁆ L) (ha : Function.Involutive a)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    (hs : ∀ x ∈ H, a x ∈ H) (α : Module.Dual ℂ H) :
    a (killingCoroot H α : L) = (killingCoroot H (rootAction a H hs α) : L) := by
  let t : H := ⟨a (tAlpha H α : L), hs _ (tAlpha H α).property⟩
  have ht : t = tAlpha H (rootAction a H hs α) := by
    apply tAlpha_unique hss H hH
    intro y
    change B (a (tAlpha H α : L)) (y : L) = α ⟨a y, hs y y.property⟩
    calc
      _ = B (a (tAlpha H α : L)) (a (a y)) := congrArg _ (ha (y : L)).symm
      _ = B (tAlpha H α : L) (a y) := LieAlgebra.killingForm_of_equiv_apply a _ _
      _ = _ := tAlpha_pairing hss H hH α ⟨a y, hs y y.property⟩
  have ht' : a (tAlpha H α : L) = (tAlpha H (rootAction a H hs α) : L) :=
    congrArg Subtype.val ht
  have hf : rootForm H (rootAction a H hs α) (rootAction a H hs α) = rootForm H α α := by
    rw [rootForm_apply, ← ht']
    exact LieAlgebra.killingForm_of_equiv_apply a _ _
  change a ((2 / rootForm H α α) • (tAlpha H α : L)) =
    (2 / rootForm H (rootAction a H hs α) (rootAction a H hs α)) •
      (tAlpha H (rootAction a H hs α) : L)
  rw [hf, map_smul, ht']

omit [FiniteDimensional ℂ L] in
private theorem simple_action {ω : Conjugation L} {a : L ≃ₗ⁅ℂ⁆ L}
    (ha : Function.Involutive a) {H : LieSubalgebra ℂ L} {hH : StableCartan ω a H} {z : H}
    (hz : PositiveOrder ω a H hH z) :
    ∃ p : simple H (evaluation H z) ≃ simple H (evaluation H z),
      Function.Involutive p ∧ ∀ i, (p i).val = rootAction a H hH.stable i.val := by
  let R := rootAction a H hH.stable
  have hR : Function.Involutive R := rootAction_involutive a ha H hH.stable
  have hAdd (α β : Module.Dual ℂ H) : R (α + β) = R α + R β := rfl
  have hp (i : simple H (evaluation H z)) : R i.val ∈ simple H (evaluation H z) := by
    refine ⟨(hz.preserved _).mpr i.property.1, ?_⟩
    intro α hα β hβ he
    have hh := congrArg R he
    change R (R i.val) = R (α + β) at hh
    have hf : R (R i.val) = i.val := hR i.val
    rw [hf, hAdd] at hh
    exact i.property.2 _ ((hz.preserved _).mpr hα) _ ((hz.preserved _).mpr hβ) hh
  let p (i : simple H (evaluation H z)) : simple H (evaluation H z) := ⟨R i.val, hp i⟩
  have pinv : Function.Involutive p := fun i => Subtype.ext (hR i.val)
  let e := Equiv.ofBijective p ⟨pinv.injective, pinv.surjective⟩
  exact ⟨e, pinv, fun _ => rfl⟩

private theorem eigen_sign_of_root_fixed (hss : IsSemisimple_value ℂ L)
    {a : L ≃ₗ⁅ℂ⁆ L} (ha : Function.Involutive a)
    {H : LieSubalgebra ℂ L} (hH : IsMaximalToral H)
    (hs : ∀ x ∈ H, a x ∈ H) {α : Module.Dual ℂ H} (hα : α ∈ rootSet H)
    (hr : rootAction a H hs α = α) {x : L} (hx : x ∈ rootSpace H α) (hn : x ≠ 0) :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ a x = ε • x := by
  have hax := root_transport a ha H hs α hx
  rw [hr] at hax
  obtain ⟨y, _, hy⟩ := (_root_.finrank_eq_one_iff' (K := ℂ) (V := rootSpace H α)).mp
    (finrank_rootSpace_eq_one hss H hH α hα)
  obtain ⟨k, hk⟩ := hy ⟨x, hx⟩
  obtain ⟨l, hl⟩ := hy ⟨a x, hax⟩
  have hk' : k • (y : L) = x := congrArg Subtype.val hk
  have hl' : l • (y : L) = a x := congrArg Subtype.val hl
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hn ((zero_smul ℂ (y : L)).symm.trans hk').symm
  let ε := l / k
  have he : a x = ε • x := by rw [← hl', ← hk', smul_smul, div_mul_cancel₀ _ hk0]
  have hsquare : ε * ε = 1 := by
    have h := ha x
    rw [he, map_smul, he, smul_smul] at h
    exact smul_left_injective ℂ hn (h.trans (one_smul ℂ x).symm)
  exact ⟨ε, mul_self_eq_one_iff.mp hsquare, he⟩

end SimpleTriples

section Encode

open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)

theorem encode : encode_type.{u} := by
  intro L _ _ _ hss ω hc a hcomm ha
  classical
  obtain ⟨H, hH, z, hz⟩ := stable_order hss ω hc a hcomm ha
  obtain ⟨p, pinv, hp⟩ := simple_action ha hz
  refine ⟨H, hH, z, hz, ?_⟩
  dsimp only
  let φ := evaluation H z
  let J := simple H φ
  let : LinearOrder J := linearOrderOfSTO WellOrderingRel
  let : DecidableEq J := Classical.decEq _
  let C (i : J) := (killingCoroot H i.val : L)
  have hcor (i : J) : a (C i) = C (p i) := by
    change a (killingCoroot H i.val : L) = (killingCoroot H (p i).val : L)
    rw [hp, coroot_transport hss a ha H hH.toral hH.stable]
  have choose_root (i : J) : ∃ x : L, x ∈ rootSpace H i.val ∧ x ≠ 0 ∧
      ⁅x, -ω.map x⁆ = C i :=
    compact_triple hss ω hc H hH.toral hH.compact_stable i.val i.property.1.1
  choose X hX using choose_root
  -- Keep the chosen vector on the smaller vertex of each two-element orbit.
  let E (i : J) := if p i < i then a (X (p i)) else X i
  let F (i : J) := -ω.map (E i)
  have root_back (i : J) : rootAction a H hH.stable (p i).val = i.val :=
    (hp (p i)).symm.trans (congrArg Subtype.val (pinv i))
  have he (i : J) : E i ∈ rootSpace H i.val ∧ E i ≠ 0 ∧ ⁅E i, F i⁆ = C i := by
    change _ ∧ _ ∧ ⁅E i, -ω.map (E i)⁆ = C i
    by_cases hi : p i < i
    · simp only [E, ite_eq_left hi]
      have hm := root_transport a ha H hH.stable (p i).val (hX (p i)).1
      rw [root_back i] at hm
      refine ⟨hm, fun h => (hX (p i)).2.1 (a.injective (h.trans (map_zero a).symm)), ?_⟩
      rw [hcomm, ← map_neg, ← LieEquiv.map_lie, (hX (p i)).2.2, hcor, pinv i]
    · simpa only [E, ite_eq_right hi] using hX i
  have hr (i : J) : E i ∈ rootSpace H i.val ∧ F i ∈ rootSpace H (-i.val) ∧
      E i ≠ 0 ∧ F i ≠ 0 ∧ ⁅E i, F i⁆ = C i := by
    refine ⟨(he i).1, Submodule.neg_mem _ (root_conjugation ω hc H hH.compact_stable i.val
      (he i).1 (he i).2.1), (he i).2.1, ?_, (he i).2.2⟩
    intro hf
    apply (he i).2.1
    apply ω.involutive.injective
    change -ω.map (E i) = 0 at hf
    rw [map_zero]
    exact neg_eq_zero.mp hf
  have hω (i : J) : ω.map (E i) = -F i ∧ ω.map (F i) = -E i ∧ ω.map (C i) = -C i := by
    have h1 : ω.map (E i) = -F i := (neg_neg _).symm
    have h2 : ω.map (F i) = -E i := by
      change ω.map (-ω.map (E i)) = -E i
      rw [map_neg, ω.involutive (E i)]
    refine ⟨h1, h2, ?_⟩
    rw [← (he i).2.2, LieHom.map_lie, h1, h2, neg_lie, lie_neg, neg_neg, ← lie_skew]
  have sign_exists (i : J) : ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ (p i ≠ i → ε = 1) ∧
      a (E i) = ε • E (p i) := by
    by_cases hi : p i = i
    · have hri : rootAction a H hH.stable i.val = i.val :=
        (hp i).symm.trans (congrArg Subtype.val hi)
      obtain ⟨ε, hcases, hε⟩ := eigen_sign_of_root_fixed hss ha hH.toral hH.stable
        i.property.1.1 hri (he i).1 (he i).2.1
      exact ⟨ε, hcases, fun hn => (hn hi).elim, by simpa only [hi] using hε⟩
    · refine ⟨1, Or.inl rfl, fun _ => rfl, ?_⟩
      rw [one_smul]
      rcases lt_or_gt_of_ne hi with hlt | hgt
      · have hn : ¬ p (p i) < p i := by rw [pinv i]; exact not_lt_of_gt hlt
        simp only [E, ite_eq_left hlt, ite_eq_right hn, ha (X (p i))]
      · have hh : p (p i) < p i := by rw [pinv i]; exact hgt
        simp only [E, ite_eq_right (not_lt_of_gt hgt), ite_eq_left hh, pinv i]
  choose ε hε using sign_exists
  obtain ⟨A, g, hA, hg, _⟩ := serre_reconstruction hss H hH.toral φ hz.regular E F hr
  obtain ⟨A', hA_entries, _, hpowers, _⟩ := serre_relations hss H hH.toral φ hz.regular E F hr
  have hoff (i j : J) (hij : i ≠ j) : A i j ≤ 0 := by
    have heq : A i j = A' i j :=
      Int.cast_injective (α := ℂ) ((hA i j).symm.trans (hA_entries i j))
    exact heq ▸ (hpowers i j hij).1
  have hA' (i j : J) : (A i j : ℂ) = j.val (killingCoroot H i.val) := (hA i j).symm
  have hperm (i j : J) : A (p i) (p j) = A i j := by
    apply (Int.cast_injective (α := ℂ))
    rw [hA', hA', hp j]
    change j.val ⟨a (killingCoroot H (p i).val : L), _⟩ = j.val (killingCoroot H i.val)
    exact congrArg j.val (Subtype.ext ((hcor (p i)).trans (congrArg C (pinv i))))
  let d : DiagramData A := ⟨p, pinv, hperm, ε, fun i => (hε i).1, fun i => (hε i).2.1⟩
  have hF (i : J) : a (F i) = ε i • F (p i) := by
    have hs := sign_conj d i
    change star (ε i) = ε i at hs
    change a (-ω.map (E i)) = ε i • (-ω.map (E (p i)))
    rw [map_neg, ← hcomm, (hε i).2.2, ω.antilinear, hs, smul_neg]
  have hP : Presents A E F C := by
    let decEq : DecidableEq J := fun i j => Subtype.instDecidableEq i j
    have hpresentation : @Presents L _ _ J decEq A E F C :=
      ⟨g, fun i => (hg i).1, fun i => (hg i).2.1, fun i => (hg i).2.2⟩
    rwa [Subsingleton.elim decEq (Classical.decEq J)] at hpresentation
  exact ⟨A, d, E, F, hP, hoff, hA', hp, hr, hω,
    fun i => ⟨(hε i).2.2, hF i, hcor i⟩⟩

theorem encode_compact : encode_compact_type.{u} := by
  intro L _ _ _ hss ω hc θ hθ
  obtain ⟨a, ⟨he, hcomm, ha⟩, _⟩ :=
    PolarRealStructures.compact_involution_extension ω θ hθ
  exact ⟨a, he, hcomm, ha, encode hss ω hc a hcomm ha⟩

end Encode

end LieAlgebrasAndRepresentations.StableCartanVoganData
