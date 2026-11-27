import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.SemifreeFlatness
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.SemifreeAlgebras
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.FlatFiltration
import Batteries.Tactic.OpenPrivate

open CategoryTheory
open scoped Classical DirectSum

universe u v

namespace DerivedFormalization.Affine.SemifreeFlatness

open Semifree
open Specs.DerivedFormalization.Affine.Tensor (act term regular restrict)
open Specs.DerivedFormalization.Affine.FlatFiltration (Union GradedSplit GradedDirectSum)
open Specs.DerivedFormalization.DG.ShiftCone (shift)
open Specs.DerivedFormalization.DG.HomComplex (gradedHom)
open Tensor (differential homOfDegrees)
open private mul_one_left_cast homogeneousTerm_cast homogeneousTerm_congr
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.SemifreeAlgebras

noncomputable section

variable {k : Type u} [Field k] [CharZero k]
variable {A P : NonpositiveCDGA.{u,v} k} {f : A ⟶ P} {V : Variables.{v}}

local notation "M" => restrict f (regular P.toCommDGAlgebra)
local notation "B" => A.toCommDGAlgebra
local notation "wt(" m ")" => V.weight (Subtype.val m)

variable (C : Presentation A V f)

/-- The image of a monomial with coefficient one, in its own degree. -/
private def generator (m : V.Monomial) : term M (wt(m)) :=
  C.component _ (homogeneousTerm A V _ m (r := 0) (zero_add _) A.one)

/-- Write the coefficient to the right of the monomial. -/
private def basisMap (m : V.Monomial) (n : ℤ) :
    term (shift (regular B) (-wt(m))) n →ₗ[k] term M n :=
  act M (wt(m)) (n + -wt(m)) n (by omega) (generator C m)

private theorem basisMap_act (m : V.Monomial) (i j n : ℤ) (h : i+j=n)
    (a : term (shift (regular B) (-wt(m))) i) (b : A.complex.X j) :
    basisMap C m n (act (shift (regular B) (-wt(m))) i j n h a b) =
      act M i j n h (basisMap C m i a) b :=
  (Specs.DerivedFormalization.Affine.Tensor.act_assoc_at M
    (wt(m)) (i + -wt(m)) j i (n + -wt(m)) n (by omega) (by omega) h
    (generator C m) a b).symm

private def signOn (s : ℤˣ) (X : ModuleCat.{v} k) : X ≃ₗ[k] X :=
  { toFun x := s • x
    invFun x := s⁻¹ • x
    left_inv x := by dsimp only; rw [smul_smul, inv_mul_cancel, one_smul]
    right_inv x := by dsimp only; rw [smul_smul, mul_inv_cancel, one_smul]
    map_add' := smul_add _
    map_smul' c x := by
      simp only [RingHom.id_apply, Units.smul_def, smul_comm (s : ℤ) c] }

private def rightCoefficient (m : V.Monomial) (n : ℤ) :
    term (shift (regular B) (-wt(m))) n ≃ₗ[k] Coefficient A V n m :=
  (eqToIso (congrArg A.complex.X (show n + -wt(m) = n - wt(m) by omega))).toLinearEquiv.trans
    (signOn ((wt(m)) * (n + -wt(m))).negOnePow _)

private theorem basisMap_eq (m : V.Monomial) (n : ℤ)
    (a : term (shift (regular B) (-wt(m))) n) :
    basisMap C m n a = C.component n (Semifree.term A V n m (rightCoefficient m n a)) := by
  classical
  let j := n + -wt(m)
  have e : wt(m) + j = n := by dsimp [j]; omega
  have h : j + wt(V.constant) = j := by simp
  have hc := C.map_mul (wt(m)) j n e
      (homogeneousTerm A V (wt(m)) m (r := 0) (zero_add _) A.one) (coefficient A V j a)
  change basisMap C m n a = _
  have hb : basisMap C m n a =
      C.component n (polynomialMul A V (wt(m)) j n e
        (homogeneousTerm A V (wt(m)) m (r := 0) (zero_add _) A.one) (coefficient A V j a)) := by
    change P.mul (wt(m)) j n e (generator C m) (f.chainMap.f j a) = _
    rw [hc, C.map_base]
    rfl
  rw [hb]
  apply congrArg (C.component n)
  change polynomialMul A V (wt(m)) j n e
    (homogeneousTerm A V (wt(m)) m (r := 0) (zero_add _) A.one)
    (homogeneousTerm A V j V.constant h a) = _
  rw [polynomialMul_homogeneousTerm, dite_eq_left (show V.Admissible (m.val + V.constant.val) by
    change V.Admissible (m.val + 0)
    simpa using m.prop)]
  rw [mul_one_left_cast, homogeneousTerm_cast (hr := by
    change j + V.weight (m.val + 0) = n
    rw [add_zero]
    omega)]
  rw [homogeneousTerm_congr A V (p := m) (Subtype.ext (add_zero m.val)) _ (by omega)]
  change (wt(m) * j + V.inversions m.val 0).negOnePow • homogeneousTerm A V n m _ a = _
  rw [V.inversions_zero_right, add_zero]
  unfold homogeneousTerm rightCoefficient signOn
  simp only [LinearMap.comp_apply, LinearEquiv.trans_apply, LinearEquiv.coe_mk,
    AddHom.coe_mk, LinearMap.coe_mk, LinearMap.map_smul_of_tower]
  rfl

/-- The coordinates of an element, with coefficients written on the left. -/
private abbrev coords (n : ℤ) := (C.component n).symm

private def supported (S : Set V.Monomial) (n : ℤ) : Submodule k (term M n) where
  carrier := {x | ∀ m ∉ S, coords C n x m = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb m hm
    rw [map_add, DirectSum.add_apply, ha m hm, hb m hm, add_zero]
  smul_mem' := by
    intro c a ha m hm
    rw [map_smul, DirectSum.smul_apply, ha m hm, smul_zero]

private theorem mem_supported {S : Set V.Monomial} {n : ℤ} {x : term M n} :
    x ∈ supported C S n ↔ ∀ m ∉ S, coords C n x m = 0 := Iff.rfl

private theorem supported_mono {S T : Set V.Monomial} (h : S ⊆ T) (n : ℤ) :
    supported C S n ≤ supported C T n :=
  fun _ hx m hm => hx m fun hS => hm (h hS)

private theorem basis_supported {m : V.Monomial} (n : ℤ)
    (a : term (shift (regular B) (-wt(m))) n) {S : Set V.Monomial} (hm : m ∈ S) :
    basisMap C m n a ∈ supported C S n := by
  intro p hp
  rw [basisMap_eq, LinearEquiv.symm_apply_apply]
  exact DFinsupp.single_eq_of_ne (ne_of_mem_of_not_mem hm hp).symm

private theorem induction_supported {S : Set V.Monomial} {n : ℤ} (Q : term M n → Prop)
    (zero : Q 0) (add : ∀ a b, Q a → Q b → Q (a+b))
    (basis : ∀ m ∈ S, ∀ a, Q (basisMap C m n a))
    (x : term M n) (hx : x ∈ supported C S n) : Q x := by
  let p := coords C n x
  have he := congrArg (C.component n) (DirectSum.sum_support_of p)
  rw [map_sum, LinearEquiv.apply_symm_apply] at he
  rw [← he]
  refine Finset.sum_induction _ Q add zero fun m hm => ?_
  have hmS : m ∈ S := by
    by_contra h
    exact (DFinsupp.mem_support_iff.mp hm) (hx m h)
  change Q (C.component n (Semifree.term A V n m (p m)))
  simpa only [basisMap_eq, LinearEquiv.apply_symm_apply] using
    basis m hmS ((rightCoefficient m n).symm (p m))

private theorem act_supported {S : Set V.Monomial} {i j n : ℤ}
    (h : i+j=n) {x : term M i} (hx : x ∈ supported C S i) (a : A.complex.X j) :
    act M i j n h x a ∈ supported C S n := by
  apply induction_supported C (fun x => act M i j n h x a ∈ supported C S n) _ _ _ x hx
  · simp
  · intro x y hx hy
    simpa only [map_add, LinearMap.add_apply] using (supported C S n).add_mem hx hy
  · intro m hm b
    rw [← basisMap_act C]
    exact basis_supported C n _ hm

/-- The degree cutoff uses total cohomological weight, including all monomials
in degree-zero variables at the first nonzero stage. -/
@[reducible] private def cutoff (r : ℕ) : Set V.Monomial :=
  {m | -(r : ℤ) < wt(m)}

private theorem cutoff_mono {r s : ℕ} (h : r ≤ s) :
    cutoff (V := V) r ⊆ cutoff s := by
  intro m hm
  change -(r : ℤ) < wt(m) at hm
  change -(s : ℤ) < wt(m)
  omega

/-- The differential of a monomial generator raises its total weight, since
a positive-degree coefficient in the base must vanish. -/
private theorem generator_d_supported (m : V.Monomial) :
    differential M (wt(m)) (generator C m) ∈ supported C {p | wt(m) < wt(p)} (wt(m)+1) := by
  intro p hp
  have h : 0 < wt(m) + 1 - wt(p) := by
    change ¬ wt(m) < wt(p) at hp
    omega
  exact (A.nonpositive _ h).elim _ _

private theorem differential_basis (m : V.Monomial) (n : ℤ)
    (a : term (shift (regular B) (-wt(m))) n) :
    differential M n (basisMap C m n a) =
      act M (wt(m)+1) (n + -wt(m)) (n+1) (by omega)
        (differential M (wt(m)) (generator C m)) a +
      basisMap C m (n+1) (differential (shift (regular B) (-wt(m))) n a) := by
  have h := (M).leibniz (a := ()) (b := ()) (wt(m)) (n + -wt(m)) n (by omega)
    (generator C m) a
  -- The sign of the shifted differential is the sign of the monomial degree.
  change differential M n (basisMap C m n a) = _ at h
  rw [h]
  congr 1
  change (wt(m)).negOnePow • act M wt(m) (n + -wt(m)+1) (n+1) (by omega) _ _ =
    act M wt(m) (n+1 + -wt(m)) (n+1) (by omega) _
      (((-wt(m)).negOnePow • A.complex.d (n + -wt(m)) (n+1 + -wt(m))) a)
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply, LinearMap.map_smul_of_tower,
    Int.negOnePow_neg]
  congr 1
  let g (q : ℤ) (e : wt(m) + q = n+1) :=
    act M wt(m) q (n+1) e (generator C m) (A.complex.d (n + -wt(m)) q a)
  have eq (q t : ℤ) (hq : wt(m) + q = n+1) (ht : wt(m) + t = n+1)
      (hqt : q = t) : g q hq = g t ht := by subst t; rfl
  exact eq _ _ _ _ (by omega)

private theorem d_supported {r : ℕ} {n : ℤ} {x : term M n}
    (hx : x ∈ supported C (cutoff r) n) :
    differential M n x ∈ supported C (cutoff r) (n+1) := by
  apply induction_supported C (fun x => differential M n x ∈ supported C (cutoff r) (n+1))
    _ _ _ x hx
  · simp
  · intro x y hx hy
    rw [map_add]
    exact (supported C (cutoff r) (n+1)).add_mem hx hy
  · intro m hm a
    rw [differential_basis]
    apply (supported C (cutoff r) (n+1)).add_mem _ (basis_supported C _ _ hm)
    apply act_supported C
    refine supported_mono C (fun p hp => ?_) _ (generator_d_supported C m)
    exact lt_trans (show -(r : ℤ) < wt(m) from hm) (show wt(m) < wt(p) from hp)

/-- Keep precisely the coordinates indexed by a specified set of monomials. -/
private def select (S : Set V.Monomial) (n : ℤ) : term M n →ₗ[k] term M n :=
  (C.component n).toLinearMap.comp
    ((DFinsupp.filterLinearMap k (Coefficient A V n) (· ∈ S)).comp
      (coords C n).toLinearMap)

private theorem coords_select (S : Set V.Monomial) (n : ℤ) (x : term M n) (m : V.Monomial) :
    coords C n (select C S n x) m = if m ∈ S then coords C n x m else 0 := by
  simp only [select, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    DFinsupp.filterLinearMap_apply, DFinsupp.filter_apply]

private theorem select_mem {S : Set V.Monomial} {n : ℤ} (x : term M n) :
    select C S n x ∈ supported C S n := by
  intro m hm
  rw [coords_select, ite_eq_right hm]

private theorem select_eq {S : Set V.Monomial} {n : ℤ} {x : term M n}
    (hx : x ∈ supported C S n) : select C S n x = x := by
  apply (coords C n).injective
  ext m
  by_cases hm : m ∈ S
  · rw [coords_select, ite_eq_left hm]
  · rw [coords_select, ite_eq_right hm, (mem_supported C).mp hx m hm]

private theorem select_zero {S L : Set V.Monomial} (h : Disjoint S L)
    {n : ℤ} {x : term M n} (hx : x ∈ supported C L n) : select C S n x = 0 := by
  apply (coords C n).injective
  ext m
  rw [coords_select, map_zero, DFinsupp.zero_apply]
  by_cases hm : m ∈ S
  · rw [ite_eq_left hm, (mem_supported C).mp hx m fun hl => Set.disjoint_left.mp h hm hl]
  · rw [ite_eq_right hm]

private theorem select_basis (S : Set V.Monomial) (m : V.Monomial) (n : ℤ)
    (a : term (shift (regular B) (-wt(m))) n) :
    select C S n (basisMap C m n a) =
      if m ∈ S then basisMap C m n a else 0 := by
  split_ifs with hm
  · exact select_eq C (basis_supported C n a hm)
  · exact select_zero C (L := {m}) (Set.disjoint_singleton_right.mpr hm)
      (basis_supported C n a rfl)

private theorem select_act (S : Set V.Monomial) (i j n : ℤ) (h : i+j=n)
    (x : term M i) (a : A.complex.X j) :
    select C S n (act M i j n h x a) = act M i j n h (select C S i x) a := by
  apply induction_supported C (S := Set.univ) (fun x =>
    select C S n (act M i j n h x a) = act M i j n h (select C S i x) a) _ _ _ x
    (fun _ hm => (hm trivial).elim)
  · simp only [map_zero, LinearMap.zero_apply]
  · intro x y hx hy
    simp only [map_add, LinearMap.add_apply, hx, hy]
  · intro m _ b
    rw [← basisMap_act, select_basis, select_basis]
    split_ifs with hm
    · exact basisMap_act C m i j n h b a
    · simp only [map_zero, LinearMap.zero_apply]

private theorem select_remainder {S T : Set V.Monomial}
    {n : ℤ} {x : term M n} (hx : x ∈ supported C T n) :
    x - select C S n x ∈ supported C (T \ S) n := by
  intro m hm
  rw [map_sub, DFinsupp.sub_apply, coords_select]
  by_cases hs : m ∈ S
  · rw [ite_eq_left hs, sub_self]
  · rw [ite_eq_right hs, sub_zero, (mem_supported C).mp hx m fun ht => hm ⟨ht, hs⟩]

private theorem differential_sq {n : ℤ} (x : term M n) :
    differential M (n+1) (differential M n x) = 0 :=
  CategoryTheory.congr_fun ((M).complex () |>.d_comp_d n (n+1) (n+1+1)) x

private def project (S : Set V.Monomial) (n : ℤ) :
    term M n →ₗ[k] supported C S n :=
  (select C S n).codRestrict _ (select_mem C)

private def homogeneousAction (S : Set V.Monomial) (i j n : ℤ) (e : i+j=n) :
    supported C S i →ₗ[k] A.complex.X j →ₗ[k] supported C S n :=
  LinearMap.flip
    { toFun a := (((act M i j n e).flip a).comp (supported C S i).subtype).codRestrict _
        fun x => act_supported C e x.property a
      map_add' a b := by ext x; exact map_add (act M i j n e x.val) a b
      map_smul' c a := by ext x; exact map_smul (act M i j n e x.val) c a }

private def selectedStep (S : Set V.Monomial) (n : ℤ) :
    supported C S n →ₗ[k] supported C S (n+1) :=
  (project C S (n+1)).comp ((differential M n).hom.comp (supported C S n).subtype)

@[reducible] private def selectedComplex (S : Set V.Monomial)
    (hs : ∀ n (x : supported C S n), selectedStep C S (n+1) (selectedStep C S n x) = 0) :
    ModuleCochain.{u,v} k :=
  CochainComplex.of (fun n => ModuleCat.of k (supported C S n))
    (fun n => ModuleCat.ofHom (selectedStep C S n)) (fun n =>
      ModuleCat.hom_ext (LinearMap.ext (hs n)))

private theorem selectedComplex_d (S : Set V.Monomial) (hs) (n : ℤ) :
    (selectedComplex C S hs).d n (n+1) = ModuleCat.ofHom (selectedStep C S n) :=
  CochainComplex.of_d (X := fun i => ModuleCat.of k (supported C S i))
    (fun i => ModuleCat.ofHom (selectedStep C S i)) n

@[reducible] private def selectedModule (S : Set V.Monomial)
    (hs : ∀ n (x : supported C S n), selectedStep C S (n+1) (selectedStep C S n x) = 0) :
    (B).Module where
  complex _ := selectedComplex C S hs
  act := homogeneousAction C S
  act_id _ i x := Subtype.ext ((M).act_id () i x.val)
  act_assoc := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩ i j l x a b
    exact Subtype.ext ((M).act_assoc i j l x.val a b)
  leibniz := by
    rintro ⟨⟩ ⟨⟩ i j n h x a
    simp only [CochainComplex.of_d]
    apply Subtype.ext
    change select C S (n+1) (differential M n (act M i j n h x.val a)) =
      act M (i+1) j (n+1) (by omega) (select C S (i+1) (differential M i x.val)) a +
      i.negOnePow • act M i (j+1) (n+1) (by omega) x.val ((B).complex.d j (j+1) a)
    rw [(M).leibniz, map_add, LinearMap.map_smul_of_tower, select_act, select_act,
      select_eq C x.property]

private theorem selectedModule_d (S : Set V.Monomial) (hs) (n : ℤ)
    (x : term (selectedModule C S hs) n) :
    differential (selectedModule C S hs) n x = selectedStep C S n x := by
  change (selectedComplex C S hs).d n (n+1) x = _
  rw [selectedComplex_d]
  rfl

private theorem cutoff_sq (r : ℕ) (n : ℤ) (x : supported C (cutoff r) n) :
    selectedStep C (cutoff r) (n+1) (selectedStep C (cutoff r) n x) = 0 := by
  apply Subtype.ext
  change select C (cutoff r) (n+1+1)
    (differential M (n+1) (select C (cutoff r) (n+1) (differential M n x.val))) = 0
  rw [select_eq C (d_supported C x.property), differential_sq, map_zero]

@[reducible] private def stage (r : ℕ) : (B).Module :=
  selectedModule C (cutoff r) (cutoff_sq C r)

private def stageInclusion {r s : ℕ} (h : r ≤ s) : stage C r ⟶ stage C s :=
  homOfDegrees (fun n => Submodule.inclusion (supported_mono C (cutoff_mono h) n)) (by
    intro n x
    rw [show differential (stage C s) n _ = selectedStep C (cutoff s) n _ from
      selectedModule_d C _ _ _ _, show differential (stage C r) n x = _ from
      selectedModule_d C _ _ _ _]
    apply Subtype.ext
    change select C (cutoff s) (n+1) (differential M n x.val) =
      select C (cutoff r) (n+1) (differential M n x.val)
    rw [select_eq C (d_supported C x.property),
      select_eq C (supported_mono C (cutoff_mono h) _ (d_supported C x.property))]) (by
    intro i j n e x a
    exact Subtype.ext rfl)

private def intoAmbient (r : ℕ) : stage C r ⟶ M :=
  homOfDegrees (fun n => (supported C (cutoff r) n).subtype) (by
    intro n x
    rw [show differential (stage C r) n x = _ from selectedModule_d C _ _ _ _]
    change differential M n x.val = select C (cutoff r) (n+1) (differential M n x.val)
    exact (select_eq C (d_supported C x.property)).symm) (by intro; intros; rfl)

private def stageDiagram : ℕ ⥤ (B).Module where
  obj := stage C
  map e := stageInclusion C (leOfHom e)
  map_id _ := RightDGModuleModel.hom_ext (by
    rintro ⟨⟩
    apply HomologicalComplex.hom_ext
    intro n
    exact ModuleCat.hom_ext (LinearMap.ext fun _ => Subtype.ext rfl))
  map_comp _ _ := RightDGModuleModel.hom_ext (by
    rintro ⟨⟩
    apply HomologicalComplex.hom_ext
    intro n
    exact ModuleCat.hom_ext (LinearMap.ext fun _ => Subtype.ext rfl))

private def stageUnion : Union (stageDiagram C) M where
  incl := intoAmbient C
  comm h := by
    apply RightDGModuleModel.hom_ext
    rintro ⟨⟩
    apply HomologicalComplex.hom_ext
    intro n
    rfl
  injective _ _ := Subtype.val_injective
  exhaustive n x := by
    let p := coords C n x
    let r := (p.support.image (fun m => (-wt(m)).toNat)).sup id + 1
    refine ⟨r, ⟨x, ?_⟩, rfl⟩
    intro m hm
    by_contra hn
    have hle : (-wt(m)).toNat ≤ (p.support.image (fun m => (-wt(m)).toNat)).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem _ (DFinsupp.mem_support_iff.mpr hn))
    change ¬ -(r : ℤ) < wt(m) at hm
    dsimp only [r] at hm
    omega

/-- The monomials whose weight is exactly the negative of the stage index. -/
@[reducible] private def layerSet (r : ℕ) : Set V.Monomial :=
  cutoff (r+1) \ cutoff r

private theorem layer_weight {r : ℕ} {m : V.Monomial}
    (hm : m ∈ layerSet r) : wt(m) = -(r : ℤ) := by
  have h₁ : -((r+1 : ℕ) : ℤ) < wt(m) := hm.1
  have h₂ : ¬ -(r : ℤ) < wt(m) := hm.2
  omega

private theorem cutoff_layer_disjoint (r : ℕ) :
    Disjoint (cutoff (V := V) r) (layerSet r) :=
  Set.disjoint_left.mpr fun _ hm hl => hl.2 hm

private theorem layer_remainder {r : ℕ} {n : ℤ} {x : term M n}
    (hx : x ∈ supported C (cutoff (r+1)) n) :
    x - select C (layerSet r) n x ∈ supported C (cutoff r) n := by
  apply supported_mono C _ _ (select_remainder C (S := layerSet r) hx)
  rintro m ⟨hm, hl⟩
  by_contra hc
  exact hl ⟨hm, hc⟩

private theorem layer_select_d {r : ℕ} {n : ℤ} {x : term M n}
    (hx : x ∈ supported C (cutoff (r+1)) n) :
    select C (layerSet r) (n+1) (differential M n (select C (layerSet r) n x)) =
      select C (layerSet r) (n+1) (differential M n x) := by
  have h := select_zero C (cutoff_layer_disjoint r).symm
    (d_supported C (layer_remainder C hx))
  rw [map_sub, map_sub, sub_eq_zero] at h
  exact h.symm

private theorem layer_sq (r : ℕ) (n : ℤ) (x : supported C (layerSet r) n) :
    selectedStep C (layerSet r) (n+1) (selectedStep C (layerSet r) n x) = 0 := by
  apply Subtype.ext
  change select C (layerSet r) (n+1+1)
    (differential M (n+1) (select C (layerSet r) (n+1) (differential M n x.val))) = 0
  rw [layer_select_d C (d_supported C (supported_mono C (fun _ hm => hm.1) _ x.property)),
    differential_sq, map_zero]

@[reducible] private def layer (r : ℕ) : (B).Module :=
  selectedModule C (layerSet r) (layer_sq C r)

private def layerQuotient (r : ℕ) : stage C (r+1) ⟶ layer C r :=
  homOfDegrees (fun n => (project C (layerSet r) n).comp (supported C (cutoff (r+1)) n).subtype)
    (by
      intro n x
      rw [show differential (layer C r) n _ = _ from selectedModule_d C _ _ _ _,
        show differential (stage C (r+1)) n x = _ from selectedModule_d C _ _ _ _]
      apply Subtype.ext
      change select C (layerSet r) (n+1) (differential M n (select C (layerSet r) n x.val)) =
        select C (layerSet r) (n+1) (select C (cutoff (r+1)) (n+1) (differential M n x.val))
      rw [layer_select_d C x.property, select_eq C (d_supported C x.property)]) (by
      intro i j n e x a
      exact Subtype.ext (select_act C (layerSet r) i j n e x.val a))

private def gradedMapOfDegrees {L N : (B).Module}
    (F : ∀ n, term L n →ₗ[k] term N n)
    (comm : ∀ i j n (h : i+j=n) (x : term L i) (a : (B).complex.X j),
      F n (act L i j n h x a) = act N i j n h (F i x) a) :
    gradedHom L N 0 :=
  RightDGModule.GradedHom.mk (fun a i q h => by
    cases a
    have he : i = q := by omega
    clear h
    subst q
    exact ModuleCat.ofHom (F i)) (by
      rintro ⟨⟩ ⟨⟩ i j n ir nr h hi hn x a
      have ei : i = ir := (add_zero i).symm.trans hi
      have en : n = nr := (add_zero n).symm.trans hn
      cases ei
      cases en
      exact comm i j n h x a)

private def layerSplit (r : ℕ) :
    GradedSplit (stageInclusion C (Nat.le_succ r)) (layerQuotient C r) where
  zero := by
    apply RightDGModuleModel.hom_ext
    rintro ⟨⟩
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subtype.ext (select_zero C (cutoff_layer_disjoint r).symm x.property)
  retraction := gradedMapOfDegrees
    (fun n => (project C (cutoff r) n).comp (supported C (cutoff (r+1)) n).subtype)
    (fun i j n h x a => Subtype.ext (select_act C (cutoff r) i j n h x.val a))
  sectionMap := gradedMapOfDegrees (fun n => Submodule.inclusion
      (supported_mono C (fun m (hm : m ∈ layerSet r) => hm.1) n))
    (fun _ _ _ _ _ _ => Subtype.ext rfl)
  retract n x := Subtype.ext (select_eq C x.property)
  section_id n x := Subtype.ext (select_eq C x.property)
  decompose n y := by
    apply Subtype.ext
    change select C (cutoff r) n y.val + select C (layerSet r) n y.val = y.val
    apply (coords C n).injective
    ext m
    simp only [map_add, DirectSum.add_apply, coords_select]
    by_cases hm : m ∈ cutoff r
    · rw [ite_eq_left hm, ite_eq_right (fun hml => hml.2 hm), add_zero]
    by_cases hs : m ∈ cutoff (r+1)
    · rw [ite_eq_right hm, ite_eq_left (show m ∈ layerSet r from ⟨hs, hm⟩), zero_add]
    · rw [ite_eq_right hm, ite_eq_right (fun hml => hs hml.1), zero_add,
        (mem_supported C).mp y.property m hs]

private def layerInclusion (r : ℕ) (m : layerSet (V := V) r) :
    shift (regular B) (-wt(m.val)) ⟶ layer C r :=
  homOfDegrees (fun n => (basisMap C m.val n).codRestrict _
    (fun a => basis_supported C n a m.property)) (by
      intro n a
      rw [show differential (layer C r) n _ = _ from selectedModule_d C _ _ _ _]
      apply Subtype.ext
      change select C (layerSet r) (n+1) (differential M n (basisMap C m.val n a)) =
        basisMap C m.val (n+1) (differential (shift (regular B) (-wt(m.val))) n a)
      rw [differential_basis, map_add, select_eq C (basis_supported C _ _ m.property)]
      have h : Disjoint (layerSet r) {p | wt(m.val) < wt(p)} := by
        refine Set.disjoint_left.mpr fun p hp hlt => ?_
        have e := layer_weight hp
        have em := layer_weight m.property
        change wt(m.val) < wt(p) at hlt
        omega
      rw [select_zero C h (act_supported C _ (generator_d_supported C m.val) a), zero_add]) (by
      intro i j n h a b
      exact Subtype.ext (basisMap_act C m.val i j n h a b))

private def readLayer (r : ℕ) (n : ℤ) :
    term (layer C r) n →ₗ[k]
      DirectSum (layerSet (V := V) r) (fun m => term (shift (regular B) (-wt(m.val))) n) :=
  (DFinsupp.mapRange.linearMap (fun m : layerSet (V := V) r =>
      (rightCoefficient m.val n).symm.toLinearMap)).comp
    ((DFinsupp.subtypeDomainLinearMap k (Coefficient A V n) (· ∈ layerSet r)).comp
      ((coords C n).toLinearMap.comp (supported C (layerSet r) n).subtype))

private def sumLayer (r : ℕ) (n : ℤ) :
    DirectSum (layerSet (V := V) r) (fun m => term (shift (regular B) (-wt(m.val))) n) →ₗ[k]
      term (layer C r) n :=
  letI : DecidableEq (layerSet (V := V) r) := Classical.decEq _
  DirectSum.toModule k _ _ (fun m => ((layerInclusion C r m).app ()).f n |>.hom)

private theorem readLayer_apply (r : ℕ) (n : ℤ) (x : term (layer C r) n)
    (m : layerSet (V := V) r) :
    readLayer C r n x m = (rightCoefficient m.val n).symm (coords C n x.val m.val) := rfl

private theorem layer_sum_coords (r : ℕ) (n : ℤ)
    (a : DirectSum (layerSet (V := V) r) (fun m => term (shift (regular B) (-wt(m.val))) n))
    (m : layerSet (V := V) r) :
    coords C n (sumLayer C r n a).val m.val = rightCoefficient m.val n (a m) := by
  let _ : DecidableEq (layerSet (V := V) r) := Classical.decEq _
  induction a using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb =>
    rw [map_add]
    change coords C n ((sumLayer C r n a).val + (sumLayer C r n b).val) m.val = _
    rw [map_add, DirectSum.add_apply, ha, hb, DirectSum.add_apply, map_add]
  | of p a =>
    change coords C n (sumLayer C r n (DirectSum.lof k _ _ p a)).val m.val = _
    rw [sumLayer, DirectSum.toModule_lof]
    change coords C n (basisMap C p.val n a) m.val = _
    rw [basisMap_eq, LinearEquiv.symm_apply_apply]
    by_cases h : m = p
    · subst p
      simp [Semifree.term]
    · have hv : m.val ≠ p.val := fun e => h (Subtype.ext e)
      rw [show Semifree.term A V n p.val _ m.val = 0 from DFinsupp.single_eq_of_ne hv,
        DirectSum.of_eq_of_ne _ _ _ h, map_zero]

set_option maxHeartbeats 1000000 in
private theorem sumLayer_bijective (r : ℕ) (n : ℤ) : Function.Bijective (sumLayer C r n) := by
  refine ⟨?_, ?_⟩
  · apply Function.LeftInverse.injective (g := readLayer C r n)
    intro a
    ext m
    rw [readLayer_apply, layer_sum_coords, LinearEquiv.symm_apply_apply]
  · intro x
    refine ⟨readLayer C r n x, ?_⟩
    apply Subtype.ext
    apply (coords C n).injective
    ext m
    by_cases hm : m ∈ layerSet r
    · exact (layer_sum_coords C r n (readLayer C r n x) ⟨m, hm⟩).trans
        ((rightCoefficient m n).apply_symm_apply _)
    · exact (mem_supported C).mp (sumLayer C r n (readLayer C r n x)).property m hm |>.trans
        ((mem_supported C).mp x.property m hm).symm

set_option maxHeartbeats 1000000 in
private def layerDirectSum (r : ℕ) :
    GradedDirectSum (fun m : layerSet (V := V) r => shift (regular B) (-wt(m.val))) (layer C r) where
  incl := layerInclusion C r
  bijective n := by
    simpa only [sumLayer] using sumLayer_bijective C r n


private def initialDirectSum :
    GradedDirectSum (fun _ : PEmpty.{v+1} => regular B) (stage C 0) where
  incl i := i.elim
  bijective n := by
    have h (x : term (stage C 0) n) : x = 0 := by
      apply Subtype.ext
      apply (coords C n).injective
      ext m
      change coords C n x.val m = coords C n (0 : term M n) m
      rw [map_zero, DFinsupp.zero_apply]
      exact x.property m (by
        have h := V.weight_nonpositive m.val
        change ¬ -(0 : ℤ) < wt(m)
        omega)
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun x => ⟨0, (map_zero _).trans (h x).symm⟩⟩

set_option maxHeartbeats 1000000 in
private theorem presentation_kFlat (C : Presentation A V f) : Tensor.KFlat M := by
  apply FlatFiltration.kFlat_of_union (stageUnion C)
  intro r
  change Tensor.KFlat (stage C r)
  induction r with
  | zero => exact FlatFiltration.kFlat_of_directSum (initialDirectSum C) fun i => i.elim
  | succ r ih =>
    exact FlatFiltration.kFlat_of_gradedSplit (layerSplit C r) ih
      (FlatFiltration.kFlat_of_directSum (layerDirectSum C r) fun m =>
        FlatFiltration.kFlat_shift (regular B) (-wt(m.val)) Tensor.regular_kFlat)

theorem semifree_algebra_kFlat :
    Specs.DerivedFormalization.Affine.SemifreeFlatness.SemifreeAlgebraKFlat.{u,v} := by
  intro k _ _ T A P f hT hsf
  obtain ⟨V, ⟨C⟩⟩ := hsf
  exact (FlatFiltration.model_kFlat_iff T hT).2 (presentation_kFlat C.toPresentation)

end

end DerivedFormalization.Affine.SemifreeFlatness
