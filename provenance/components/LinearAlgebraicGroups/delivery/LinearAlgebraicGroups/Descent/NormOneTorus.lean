import Specs.LinearAlgebraicGroups.Descent.NormOneTorus
import LinearAlgebraicGroups.Multiplicative.NormOneTorus
import LinearAlgebraicGroups.Descent.WeilHilbert90
import Mathlib.RingTheory.Complex
import Mathlib.Analysis.Real.Sqrt
import Mathlib.GroupTheory.Index

open CategoryTheory AlgebraicGeometry WithConv
open LinearAlgebraicGroups.WeilRestriction
open LinearAlgebraicGroups.Descent.NonabelianCohomology
open LinearAlgebraicGroups.Specs.NormOneCohomology
open scoped TensorProduct

namespace LinearAlgebraicGroups.Descent.NormOneTorus

universe u v

noncomputable section

set_option linter.style.haveILetI false

section ExactSequence

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
  {M : Type v} [CommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Γ →* MulAut M)

private def cocycleSubgroup : Subgroup (Γ → M) where
  carrier := {a | IsCocycle ρ a}
  one_mem' := (trivial ρ).property
  mul_mem' {a b} ha hb := by
    refine ⟨ha.1.mul hb.1, fun σ τ => ?_⟩
    change a (σ * τ) * b (σ * τ) = (a σ * b σ) * ρ σ (a τ * b τ)
    rw [ha.2, hb.2, map_mul]
    ac_rfl
  inv_mem' {a} ha := by
    refine ⟨ha.1.inv, fun σ τ => ?_⟩
    change (a (σ * τ))⁻¹ = (a σ)⁻¹ * ρ σ (a τ)⁻¹
    rw [ha.2, mul_inv_rev, map_inv, mul_comm]

private def difference (σ : Γ) : M →* M where
  toFun x := x⁻¹ * ρ σ x
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, mul_inv_rev]
    ac_rfl

omit [TopologicalSpace Γ] [TopologicalSpace M] [DiscreteTopology M] in
private theorem difference_cocycle (x : M) (σ τ : Γ) :
    difference ρ (σ * τ) x = difference ρ σ x * ρ σ (difference ρ τ x) := by
  change x⁻¹ * ρ (σ * τ) x = (x⁻¹ * ρ σ x) * ρ σ (x⁻¹ * ρ τ x)
  rw [map_mul ρ, map_mul, map_inv]
  change x⁻¹ * ρ σ (ρ τ x) = (x⁻¹ * ρ σ x) * ((ρ σ x)⁻¹ * ρ σ (ρ τ x))
  simp [mul_assoc]

variable (hρ : ∀ x : M, Continuous fun σ => ρ σ x)

private def coboundary : M →* cocycleSubgroup ρ where
  toFun x := ⟨fun σ => difference ρ σ x, ⟨continuous_const.mul (hρ x),
    difference_cocycle ρ x⟩⟩
  map_one' := Subtype.ext (funext fun σ => (difference ρ σ).map_one)
  map_mul' x y := Subtype.ext (funext fun σ => (difference ρ σ).map_mul x y)

private def h1QuotientEquiv : H1 ρ ≃ cocycleSubgroup ρ ⧸ (coboundary ρ hρ).range := by
  let e : Cocycle ρ ≃ cocycleSubgroup ρ :=
    ⟨fun a => ⟨a.val, a.property⟩, fun a => ⟨a.val, a.property⟩, fun _ => rfl, fun _ => rfl⟩
  refine Quotient.congr e fun a b => ?_
  rw [QuotientGroup.leftRel_apply]
  change (∃ x : M, ∀ σ, b σ = x⁻¹ * a σ * ρ σ x) ↔
    ∃ x : M, coboundary ρ hρ x = (e a)⁻¹ * (e b)
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, Subtype.ext (funext fun σ => ?_)⟩
    change x⁻¹ * ρ σ x = (a σ)⁻¹ * b σ
    rw [hx]
    simp [mul_assoc, mul_left_comm]
  · rintro ⟨x, hx⟩
    refine ⟨x, fun σ => ?_⟩
    have h := congrArg (fun c : cocycleSubgroup ρ => c.val σ) hx
    change x⁻¹ * ρ σ x = (a σ)⁻¹ * b σ at h
    calc
      b σ = a σ * ((a σ)⁻¹ * b σ) := by simp
      _ = x⁻¹ * a σ * ρ σ x := by rw [← h]; ac_rfl

private abbrev h1CommGroup : CommGroup (H1 ρ) :=
  (h1QuotientEquiv ρ hρ).commGroup

private theorem classOf_trivial :
    letI := h1CommGroup ρ hρ
    classOf (trivial ρ) = (1 : H1 ρ) := by
  letI := h1CommGroup ρ hρ
  let e := h1QuotientEquiv ρ hρ
  apply e.injective
  change (QuotientGroup.mk' (coboundary ρ hρ).range) 1 = e (e.symm 1)
  rw [e.apply_symm_apply, map_one]

private theorem classOf_mul (a b c : Cocycle ρ) (h : ∀ σ, c σ = a σ * b σ) :
    letI := h1CommGroup ρ hρ
    classOf c = classOf a * classOf b := by
  letI := h1CommGroup ρ hρ
  let e := h1QuotientEquiv ρ hρ
  apply e.injective
  let q := QuotientGroup.mk' (coboundary ρ hρ).range
  change q ⟨c.val, c.property⟩ = e (e.symm (q ⟨a.val, a.property⟩ * q ⟨b.val, b.property⟩))
  rw [e.apply_symm_apply, ← q.map_mul]
  exact congrArg q (Subtype.ext (funext h))

variable {B A D F : Type v} [CommGroup B] [CommGroup A] [Group D] [CommGroup F]
  [TopologicalSpace B] [DiscreteTopology B]
  (β : Γ →* MulAut B) (α : Γ →* MulAut A)
  (incl : M →* B) (N : B →* A) (i : D →* B) (j : F →* A) (d : D →* F)

/-- The coboundary of a lift identifies the fixed-point norm quotient with H¹. -/
private theorem connectingIso (hβ : ∀ w : B, Continuous fun σ => β σ w)
    (hincl : Function.Injective incl) (hj : Function.Injective j)
    (hincl_eq : ∀ σ x, incl (ρ σ x) = β σ (incl x))
    (hNeq : ∀ σ x, N (β σ x) = α σ (N x))
    (hk : ∀ x, (∃ m, incl m = x) ↔ N x = 1)
    (hfixedB : ∀ x, (∀ σ, β σ x = x) ↔ ∃ y, i y = x)
    (hfixedA : ∀ x, (∀ σ, α σ x = x) ↔ ∃ y, j y = x)
    (hcomm : ∀ y, N (i y) = j (d y))
    (hlift : ∀ x, ∃ w, N w = j x)
    (h90 : ∀ c : Cocycle β, ∃ w, ∀ σ, c σ = difference β σ w) :
    letI := h1CommGroup ρ hρ
    ∃ E : H1 ρ ≃* F ⧸ d.range,
      ∀ (a : F) (w : B), N w = j a →
        ∃ c : Cocycle ρ, (∀ σ, incl (c σ) = difference β σ w) ∧
          E (classOf c) = QuotientGroup.mk a := by
  classical
  letI := h1CommGroup ρ hρ
  let preimage (x : B) : M := if h : ∃ m, incl m = x then h.choose else 1
  have hpre {x : B} (h : N x = 1) : incl (preimage x) = x := by
    unfold preimage
    rw [dite_eq_left ((hk x).mpr h)]
    exact ((hk x).mpr h).choose_spec
  have hdiff σ x : incl (difference ρ σ x) = difference β σ (incl x) := by
    change incl (x⁻¹ * ρ σ x) = (incl x)⁻¹ * β σ (incl x)
    rw [map_mul, map_inv, hincl_eq]
  have fixedDiff {w : B} : (∀ σ, difference β σ w = 1) ↔ ∀ σ, β σ w = w := by
    constructor
    · intro h σ
      exact ((inv_mul_eq_one.mp (h σ))).symm
    · intro h σ
      exact inv_mul_eq_one.mpr (h σ).symm
  have normDiff σ {a : F} {w : B} (hw : N w = j a) : N (difference β σ w) = 1 := by
    change N (w⁻¹ * β σ w) = 1
    rw [map_mul, map_inv, hNeq, hw, (hfixedA _).mpr ⟨a, rfl⟩ σ, inv_mul_cancel]
  let liftCocycle (a : F) (w : B) (hw : N w = j a) : Cocycle ρ :=
    ⟨fun σ => preimage (difference β σ w),
      ⟨by
        have hc : Continuous fun σ => difference β σ w := continuous_const.mul (hβ w)
        exact (continuous_of_discreteTopology (f := preimage)).comp hc, by
        intro σ τ
        change preimage (difference β (σ * τ) w) =
          preimage (difference β σ w) * ρ σ (preimage (difference β τ w))
        apply hincl
        rw [map_mul, hincl_eq, hpre (normDiff (σ * τ) hw), hpre (normDiff σ hw), hpre (normDiff τ hw)]
        exact difference_cocycle β w σ τ⟩⟩
  have hliftCocycle a w hw σ :
      incl (liftCocycle a w hw σ) = difference β σ w := hpre (normDiff σ hw)
  have liftClass a w w' hw hw' :
      classOf (liftCocycle a w hw) = classOf (liftCocycle a w' hw') := by
    obtain ⟨b, hb⟩ := (hk (w' / w)).mpr (by rw [map_div, hw', hw, div_self'])
    apply classOf_eq_iff.mpr
    refine ⟨b, fun σ => hincl ?_⟩
    change incl (liftCocycle a w' hw' σ) =
      incl (b⁻¹ * liftCocycle a w hw σ * ρ σ b)
    rw [show b⁻¹ * liftCocycle a w hw σ * ρ σ b =
      liftCocycle a w hw σ * difference ρ σ b by
        change _ = _ * (b⁻¹ * _)
        ac_rfl, map_mul, hliftCocycle a w' hw', hliftCocycle a w hw, hdiff, hb, map_div]
    rw [mul_comm, div_mul_cancel]
  let δ : F →* H1 ρ :=
    { toFun := fun a => classOf (liftCocycle a (hlift a).choose (hlift a).choose_spec)
      map_one' := by
        have h1 : N (1 : B) = j 1 := by simp
        rw [liftClass 1 _ 1 (hlift 1).choose_spec h1, ← classOf_trivial ρ hρ]
        refine congrArg classOf (Subtype.ext (funext fun σ => hincl ?_))
        change incl (liftCocycle 1 1 h1 σ) = incl 1
        rw [hliftCocycle 1 1 h1, map_one, map_one]
      map_mul' := fun a b => by
        let x := (hlift a).choose
        let y := (hlift b).choose
        have hx : N x = j a := (hlift a).choose_spec
        have hy : N y = j b := (hlift b).choose_spec
        have hxy : N (x * y) = j (a * b) := by rw [map_mul, map_mul, hx, hy]
        rw [liftClass (a * b) _ (x * y) (hlift (a * b)).choose_spec hxy]
        apply classOf_mul ρ hρ
        intro σ
        apply hincl
        change incl (liftCocycle (a * b) (x * y) hxy σ) =
          incl (liftCocycle a x hx σ * liftCocycle b y hy σ)
        rw [map_mul, hliftCocycle (a * b) (x * y) hxy, hliftCocycle a x hx,
          hliftCocycle b y hy, map_mul] }
  have hδ a w hw : δ a = classOf (liftCocycle a w hw) :=
    liftClass a _ w (hlift a).choose_spec hw
  have hker : d.range = δ.ker := by
    ext a
    constructor
    · rintro ⟨y, rfl⟩
      change δ (d y) = 1
      rw [hδ (d y) (i y) (hcomm y), ← classOf_trivial ρ hρ]
      refine congrArg classOf (Subtype.ext (funext fun σ => hincl ?_))
      change incl (liftCocycle (d y) (i y) (hcomm y) σ) = incl 1
      rw [hliftCocycle (d y) (i y) (hcomm y), map_one]
      exact fixedDiff.mpr ((hfixedB _).mpr ⟨y, rfl⟩) σ
    · intro ha
      let w := (hlift a).choose
      have hw : N w = j a := (hlift a).choose_spec
      have ha' : classOf (trivial ρ) = classOf (liftCocycle a w hw) :=
        (classOf_trivial ρ hρ).trans ((hδ a w hw).symm.trans ha).symm
      obtain ⟨b, hb⟩ := classOf_eq_iff.mp ha'
      have hb' σ : difference β σ w = difference β σ (incl b) := by
        rw [← hliftCocycle a w hw, ← hdiff]
        have h := hb σ
        change liftCocycle a w hw σ = b⁻¹ * 1 * ρ σ b at h
        apply congrArg incl
        change liftCocycle a w hw σ = b⁻¹ * ρ σ b
        simpa only [mul_one] using h
      obtain ⟨y, hy⟩ := (hfixedB (w / incl b)).mp (fixedDiff.mp fun σ => by
        rw [map_div, hb', div_self'])
      have hNb : N (incl b) = 1 := (hk _).mp ⟨b, rfl⟩
      have he := congrArg N hy
      rw [hcomm, map_div, hw, hNb, div_one] at he
      exact ⟨y, hj he⟩
  have hsurj : Function.Surjective δ := by
    intro c
    induction c using Quotient.inductionOn with
    | _ c =>
      let cB : Cocycle β := ⟨fun σ => incl (c σ),
        ⟨(continuous_of_discreteTopology (f := incl)).comp c.property.1, fun σ τ => by
          change incl (c (σ * τ)) = incl (c σ) * β σ (incl (c τ))
          rw [c.property.2, map_mul, hincl_eq]⟩⟩
      obtain ⟨w, hw⟩ := h90 cB
      obtain ⟨a, ha⟩ := (hfixedA (N w)).mp fun σ => by
        have hz : N (difference β σ w) = 1 := (hk _).mp ⟨c σ, hw σ⟩
        change N (w⁻¹ * β σ w) = 1 at hz
        rw [map_mul, map_inv, hNeq, inv_mul_eq_one] at hz
        exact hz.symm
      refine ⟨a, (hδ a w ha.symm).trans (congrArg classOf (Subtype.ext (funext fun σ => hincl ?_)))⟩
      rw [hliftCocycle a w ha.symm, ← hw]
  let E := QuotientGroup.liftEquiv d.range hsurj hker
  refine ⟨E.symm, fun a w hw => ⟨liftCocycle a w hw, hliftCocycle a w hw, ?_⟩⟩
  apply E.injective
  rw [E.apply_symm_apply]
  exact (hδ a w hw).symm

end ExactSequence

theorem kernelGeometry : KernelGeometry.{u} :=
  ⟨LinearAlgebraicGroups.NormOneTorus.normKernel,
    LinearAlgebraicGroups.NormOneTorus.kernelSplitting,
    LinearAlgebraicGroups.NormOneTorus.characterAction⟩

section Points

open scoped CategoryTheory.MonObj

variable {k K S : Type u} [Field k] [Field K] [Field S] [Algebra k K] [Algebra k S]
  {W H : AffineAlgebraicGroup k}
  {e : (groupPointsFunctor k).obj W.val ≅ extendedUnits k K}
  {n : W.val ⟶ H.val} (T : Specs.NormOneTorus.KernelModel e n)

local notation "Pts" => NonabelianCohomology.Points

private abbrev weilUnits (e : (groupPointsFunctor k).obj W.val ≅ extendedUnits k K)
    (L : Type u) [Field L] [Algebra k L] :
    WeilPoints (W := W) L ≃* (L ⊗[k] K)ˣ :=
  (e.app (CommAlgCat.of k L)).groupIsoToMulEquiv

private def kernelUnits :
    KernelPoints e T S ≃* Specs.NormOneTorus.normOnePoints k K (CommAlgCat.of k S) :=
  ((hopfSpecPointIso T.coordinate).app (CommAlgCat.of k S)).groupIsoToMulEquiv.symm.trans
    (T.points (CommAlgCat.of k S))

private theorem kernelUnits_val (x : KernelPoints e T S) :
    (kernelUnits T x).val = weilUnits e S (includePoint e T S x) := by
  let p := ((hopfSpecPointIso T.coordinate).app (CommAlgCat.of k S)).groupIsoToMulEquiv
  obtain ⟨f, rfl⟩ := p.surjective x
  change (T.points (CommAlgCat.of k S) (p.symm (p f))).val = _
  rw [p.symm_apply_apply]
  exact T.points_inclusion (CommAlgCat.of k S) f

private theorem includePoint_injective : Function.Injective (includePoint e T S) := by
  intro x y h
  apply (kernelUnits T).injective
  exact Subtype.ext ((kernelUnits_val T x).trans ((congrArg (weilUnits e S) h).trans
    (kernelUnits_val T y).symm))

private theorem includePoint_exact (x : WeilPoints (W := W) S) :
    (∃ y, includePoint e T S y = x) ↔ normOnPoints e S x = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    change Units.map (pointNorm k K (CommAlgCat.of k S)) (weilUnits e S _) = 1
    rw [← kernelUnits_val T]
    exact (kernelUnits T y).property
  · intro hx
    let z : Specs.NormOneTorus.normOnePoints k K (CommAlgCat.of k S) :=
      ⟨weilUnits e S x, hx⟩
    let y := (kernelUnits T).symm z
    refine ⟨y, (weilUnits e S).injective ?_⟩
    rw [← kernelUnits_val T, (kernelUnits T).apply_symm_apply]

private theorem includePoint_equivariant (σ : Gal(S/k)) (x : KernelPoints e T S) :
    includePoint e T S (pointAction k S (specGroup T.coordinate).X σ x) =
      pointAction k S W.val.X σ (includePoint e T S x) :=
  (((groupPointsFunctor k).map T.inclusion).naturality_apply
    (CommAlgCat.ofHom σ.toAlgHom) x).symm

private def unitAction (k S : Type u) [Field k] [Field S] [Algebra k S] :
    Gal(S/k) →* MulAut Sˣ where
  toFun σ := Units.mapEquiv σ.toMulEquiv
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Units.ext
    rfl
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro x
    apply Units.ext
    rfl

private theorem normOnPoints_equivariant [Module.Finite k K] (σ : Gal(S/k))
    (x : WeilPoints (W := W) S) :
    normOnPoints e S (pointAction k S W.val.X σ x) =
      unitAction k S σ (normOnPoints e S x) := by
  have h := e.hom.naturality_apply (CommAlgCat.ofHom σ.toAlgHom) x
  apply Units.ext
  change pointNorm k K (CommAlgCat.of k S) (weilUnits e S (pointAction k S W.val.X σ x)).val =
    σ (pointNorm k K (CommAlgCat.of k S) (weilUnits e S x).val)
  rw [show weilUnits e S (pointAction k S W.val.X σ x) = _ from h]
  exact (normNaturality k K (CommAlgCat.ofHom σ.toAlgHom) _).symm

private theorem fixedUnits [IsGalois k S] (x : Sˣ) :
    (∀ σ, unitAction k S σ x = x) ↔ ∃ y : kˣ, Units.map (algebraMap k S) y = x := by
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed x.val).mpr fun σ =>
      congrArg Units.val (hx σ)
    have ha₀ : a ≠ 0 := by
      intro hz
      exact x.ne_zero (by simpa [hz] using ha.symm)
    exact ⟨Units.mk0 a ha₀, Units.ext ha⟩
  · rintro ⟨y, rfl⟩ σ
    exact Units.ext (σ.commutes y.val)

private theorem pointMap_comp {L R U : Type u} [Field L] [Field R] [Field U]
    [Algebra k L] [Algebra k R] [Algebra k U]
    {X : Over (Spec (CommRingCat.of k))} [GrpObj X]
    (f : L →ₐ[k] R) (g : R →ₐ[k] U) (x : Pts k L X) :
    pointMap k R X g (pointMap k L X f x) = pointMap k L X (g.comp f) x := by
  change (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom g).op ≫
    (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op ≫ x =
      (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (g.comp f)).op ≫ x
  rw [← Category.assoc, ← Functor.map_comp]
  rfl

private theorem fixedPoints [IsGalois k S] {X : Over (Spec (CommRingCat.of k))} [GrpObj X]
    (x : Pts k S X) :
    (∀ σ, pointAction k S X σ x = x) ↔
      ∃ y : Pts k k X, pointMap k k X (Algebra.ofId k S) y = x := by
  let L : FiniteGaloisIntermediateField k S := ⊥
  let f : L →ₐ[k] S := L.toIntermediateField.val
  let b : L ≃ₐ[k] k := IntermediateField.botEquiv k S
  have hker : (restriction L).ker = ⊤ := by
    change (AlgEquiv.restrictNormalHom L.toIntermediateField).ker = _
    rw [L.toIntermediateField.restrictNormalHom_ker]
    exact IntermediateField.fixingSubgroup_bot
  have hbf : f.comp b.symm.toAlgHom = Algebra.ofId k S := by ext
  have hfb : (Algebra.ofId k S).comp b.toAlgHom = f := by
    rw [← hbf, AlgHom.comp_assoc, AlgEquiv.symm_comp, AlgHom.comp_id]
  have he : (∀ σ, pointAction k S X σ x = x) ↔ x ∈ Fixed (pointAction k S X) (restriction L).ker := by
    rw [hker]
    simp [Fixed]
  rw [he, ← finitePoints_iff_fixed L x]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨pointMap k L X b.toAlgHom y, ?_⟩
    rw [pointMap_comp, hfb]
  · rintro ⟨y, rfl⟩
    refine ⟨pointMap k k X b.symm.toAlgHom y, ?_⟩
    rw [pointMap_comp, hbf]

private def rationalWeilUnits :
    Kˣ ≃* WeilPoints (W := W) k :=
  (Units.mapEquiv (Algebra.TensorProduct.lid k K).toMulEquiv).symm.trans (weilUnits e k).symm

private abbrev rationalWeilPoints :
    Kˣ →* WeilPoints (W := W) S :=
  (pointMap k k W.val.X (Algebra.ofId k S)).comp (rationalWeilUnits (e := e)).toMonoidHom

private theorem fixedWeilPoints [IsGalois k S] (x : WeilPoints (W := W) S) :
    (∀ σ, pointAction k S W.val.X σ x = x) ↔
      ∃ y : Kˣ, rationalWeilPoints (e := e) y = x := by
  rw [fixedPoints]
  exact (rationalWeilUnits (e := e)).surjective.exists

private theorem rationalNorm [Module.Finite k K] (x : Kˣ) :
    normOnPoints e S (rationalWeilPoints (e := e) x) =
      Units.map (algebraMap k S).toMonoidHom (fieldNorm (k := k) (K := K) x) := by
  let f := CommAlgCat.ofHom (Algebra.ofId k S)
  let y := rationalWeilUnits (e := e) x
  have he : weilUnits e S (pointMap k k W.val.X f.hom y) =
      (extendedUnits k K).map f (weilUnits e k y) := e.hom.naturality_apply f y
  apply Units.ext
  change pointNorm k K (CommAlgCat.of k S) (weilUnits e S (pointMap k k W.val.X f.hom y)).val =
    algebraMap k S (Algebra.norm k (x : K))
  rw [he]
  refine (normNaturality k K f (weilUnits e k y).val).symm.trans ?_
  apply congrArg (algebraMap k S)
  change Algebra.norm k (weilUnits e k y).val = _
  rw [← Algebra.norm_eq_of_algEquiv (Algebra.TensorProduct.lid k K)]
  exact congrArg (Algebra.norm k)
    (congrArg Units.val ((rationalWeilUnits (e := e)).symm_apply_apply x))

private theorem normOnPoints_surjective
    [Algebra.IsQuadraticExtension k K] [Algebra.IsSeparable k K] [IsSepClosure k S] :
    Function.Surjective (normOnPoints e S) := by
  letI : IsSepClosed S := IsSepClosure.sep_closed k
  let j : K →ₐ[k] S := IsSepClosed.lift
  letI : Algebra K S := j.toRingHom.toAlgebra
  letI : IsScalarTower k K S := IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a =>
    (j.commutes a).symm)
  obtain ⟨σ, hσ, _⟩ := LinearAlgebraicGroups.NormOneTorus.quadraticAutomorphism k K
  obtain ⟨s, _, hn⟩ := LinearAlgebraicGroups.NormOneTorus.quadraticTensorSplitting
    k K σ hσ S
  intro a
  let p : (S × S)ˣ :=
    ⟨(a.val, 1), (a.inv, 1), Prod.ext a.val_inv (one_mul 1), Prod.ext a.inv_val (one_mul 1)⟩
  let x := Units.map s.symm.toMonoidHom p
  refine ⟨(weilUnits e S).symm x, Units.ext ?_⟩
  change Algebra.norm S (weilUnits e S ((weilUnits e S).symm x)).val = _
  rw [(weilUnits e S).apply_symm_apply, hn]
  change (s (s.symm p.val)).1 * (s (s.symm p.val)).2 = a.val
  rw [s.apply_symm_apply]
  exact mul_one _

set_option backward.isDefEq.respectTransparency false in
private theorem continuousPointOrbit [IsGalois k S]
    {X : Over (Spec (CommRingCat.of k))} [GrpObj X] [LocallyOfFiniteType X.hom]
    (x : Pts k S X) :
    letI : TopologicalSpace (Pts k S X) := ⊥
    Continuous (fun σ : Gal(S/k) => pointAction k S X σ x) := by
  letI : TopologicalSpace (Pts k S X) := ⊥
  letI : DiscreteTopology (Pts k S X) := ⟨rfl⟩
  have h := (continuousAction_iff_finiteLevel (ρ := pointAction k S X)).mpr (by
    intro p
    obtain ⟨L, hL⟩ := point_defined_at_finite_level p
    exact ⟨L, (finitePoints_iff_fixed L p).mp hL⟩)
  have hx : Continuous (fun σ : Gal(S/k) => (σ, x)) :=
    continuous_id.prodMk continuous_const
  change Continuous ((fun p : Gal(S/k) × Pts k S X => pointAction k S X p.1 p.2) ∘
    fun σ : Gal(S/k) => (σ, x))
  exact h.comp hx

private abbrev commGroupOfEmbedding {A B : Type u} [Group A] [CommGroup B]
    (f : A →* B) (hf : Function.Injective f) : CommGroup A :=
  { (inferInstance : Group A) with mul_comm := fun x y => hf (by
      rw [map_mul, map_mul, mul_comm]) }

end Points

open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000 in
theorem cohomologyIso : CohomologyIso.{u} := by
  intro k K S _ _ _ _ _ _ _ _ W H e t n _ T
  let M := KernelPoints e T S
  let B := WeilPoints (W := W) S
  let incl := includePoint e T S
  let I := includePoint_injective (S := S) T
  letI : CommGroup B := commGroupOfEmbedding (weilUnits e S).toMonoidHom (weilUnits e S).injective
  letI : CommGroup M := commGroupOfEmbedding incl I
  letI : TopologicalSpace M := ⊥
  letI : TopologicalSpace B := ⊥
  letI : DiscreteTopology M := ⟨rfl⟩
  letI : DiscreteTopology B := ⟨rfl⟩
  let ρ : Gal(S/k) →* MulAut M := pointAction k S (specGroup T.coordinate).X
  let β : Gal(S/k) →* MulAut B := pointAction k S W.val.X
  let j : kˣ →* Sˣ := Units.map (algebraMap k S)
  let N := normOnPoints e S
  let d : Kˣ →* kˣ := fieldNorm
  let i : Kˣ →* B := rationalWeilPoints (e := e)
  haveI : LocallyOfFiniteType W.val.X.hom := W.property.2.1
  haveI : LocallyOfFiniteType (specGroup T.coordinate).X.hom :=
    (hopfSpec_locallyOfFiniteType_iff k T.coordinate).mpr T.finiteType
  have hρ (x : M) : Continuous (fun σ => ρ σ x) := continuousPointOrbit x
  have hβ (x : B) : Continuous (fun σ => β σ x) := continuousPointOrbit x
  have h90 (c : Cocycle β) : ∃ w, ∀ σ, c σ = difference β σ w := by
    have h : classOf c = basepoint β := WeilHilbert90.vanishing k K S W e (classOf c)
    obtain ⟨w, hw⟩ := classOf_eq_iff.mp h.symm
    refine ⟨w, fun σ => ?_⟩
    have hσ := hw σ
    change c σ = w⁻¹ * 1 * β σ w at hσ
    change c σ = w⁻¹ * β σ w
    simpa only [mul_one] using hσ
  have hj : Function.Injective j := Units.map_injective (algebraMap k S).injective
  have hlift (a : kˣ) : ∃ w : B, N w = j a := normOnPoints_surjective (e := e) (j a)
  obtain ⟨E, hE⟩ := connectingIso ρ hρ β (unitAction k S) incl N i j d hβ I hj
    (includePoint_equivariant T) normOnPoints_equivariant (includePoint_exact T)
    fixedWeilPoints fixedUnits rationalNorm hlift h90
  exact ⟨hlift, h1CommGroup ρ hρ, E, (classOf_trivial ρ hρ).symm,
    classOf_mul ρ hρ, hE⟩

theorem complexNormRange : ComplexNormRange := by
  intro a
  constructor
  · rintro ⟨z, rfl⟩
    change 0 < Algebra.norm ℝ z.val
    rw [Algebra.norm_complex_apply, Complex.normSq_pos]
    exact z.ne_zero
  · intro ha
    let z : ℂ := (Real.sqrt a.val : ℝ)
    have hz : Algebra.norm ℝ z = a.val := by
      rw [Algebra.norm_complex_apply]
      change Complex.normSq ((Real.sqrt a.val : ℝ) : ℂ) = a.val
      rw [Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt ha.le]
    have hz₀ : z ≠ 0 := by
      intro h
      rw [h, Algebra.norm_zero] at hz
      exact a.ne_zero hz.symm
    exact ⟨Units.mk0 z hz₀, Units.ext hz⟩

private theorem complexNormIndex : (fieldNorm (k := ℝ) (K := ℂ)).range.index = 2 := by
  let m : ℝˣ := -1
  rw [Subgroup.index_eq_two_iff]
  refine ⟨m, fun a => ?_⟩
  rw [complexNormRange, complexNormRange]
  have hm : (m : ℝ) = -1 := by simp [m]
  rw [Units.val_mul, hm, mul_neg_one, neg_pos]
  rcases lt_or_gt_of_ne a.ne_zero with h | h
  · simp [h, not_lt_of_gt h]
  · simp [h, not_lt_of_gt h]

theorem realCohomology : RealCohomology := by
  intro S _ _ _ W H e t n hn T
  letI : Algebra.IsQuadraticExtension ℝ ℂ := ⟨Complex.finrank_real_complex⟩
  obtain ⟨_, G, E, _⟩ := cohomologyIso ℝ ℂ S W H e t n hn T
  letI := G
  exact (Nat.card_congr E.toEquiv).trans complexNormIndex

end

end LinearAlgebraicGroups.Descent.NormOneTorus
