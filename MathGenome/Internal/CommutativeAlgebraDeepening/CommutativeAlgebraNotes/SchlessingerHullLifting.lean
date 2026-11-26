import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SchlessingerHullLifting
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ConstructSchlessingerCandidate
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.SchlessingerSplitCorrections
import Mathlib.RingTheory.MvPowerSeries.Evaluation
import Batteries.Tactic.OpenPrivate

universe u w

namespace CommutativeAlgebraNotes.SchlessingerHullLifting

open CategoryTheory LocalArtinAlgebra SchlessingerConditionsSpec SchlessingerCandidateSpec
  SchlessingerHullLiftingSpec SchlessingerSplitCorrectionsSpec SchlessingerTangentVectorSpaceSpec
  IsLocalRing
open scoped MvPowerSeries.WithPiTopology

open private ArtinFunctor.onHom_comp ArtinFunctor.onHom_bijective
  from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.SchlessingerTangentVectorSpace
open private ArtinFunctor.splitResidueComparison_bijective
  from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.SchlessingerSplitCorrections

attribute [local instance] extensionKernelFinite

noncomputable section

set_option linter.style.haveILetI false

variable {k : Type u} [Field k] {r : ℕ}
local notation "S" => Series k r
local notation "nS" => maximalIdeal (Series k r)

private theorem series_maximalIdeal :
    nS = Ideal.span (Set.range (MvPowerSeries.X : Fin r → S)) := by
  rw [CompleteRegularPowerSeries.maximalIdeal_eq_span_sup, maximalIdeal_eq_bot,
    Ideal.map_bot, sup_bot_eq]

private theorem variable_mem_maximalIdeal (i : Fin r) : (MvPowerSeries.X i : S) ∈ nS := by
  rw [series_maximalIdeal]
  exact Ideal.subset_span ⟨i, rfl⟩

private theorem maximalIdeal_pow_le_ker {A : LocalArtinAlgebra.{u,u} k}
    (f : S →ₐ[k] A) [IsLocalHom f] {q : ℕ} (hq : maximalIdeal A ^ q = ⊥) :
    nS ^ q ≤ RingHom.ker f.toRingHom := by
  letI : IsLocalHom f.toRingHom := ⟨(inferInstance : IsLocalHom f).map_nonunit⟩
  rw [← Ideal.map_eq_bot_iff_le_ker, Ideal.map_pow]
  exact le_bot_iff.mp ((Ideal.pow_right_mono (map_maximalIdeal_le f.toRingHom) q).trans hq.le)

/-- Into an Artin algebra a local map is determined by a finite polynomial truncation. -/
private theorem series_hom_ext {A : LocalArtinAlgebra.{u,u} k}
    {f g : S →ₐ[k] A} [IsLocalHom f] [IsLocalHom g]
    (hX : ∀ i : Fin r, f (MvPowerSeries.X i) = g (MvPowerSeries.X i)) : f = g := by
  obtain ⟨q, hq⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp inferInstance
  have hq' : maximalIdeal A ^ q = ⊥ := by simpa using hq
  let j : MvPolynomial (Fin r) k →ₐ[k] S := MvPolynomial.coeToMvPowerSeries.algHom k
  have hpoly : f.comp j = g.comp j := MvPolynomial.algHom_ext (fun i => by
    simpa [j] using hX i)
  apply AlgHom.ext
  intro x
  let p := MvPowerSeries.truncTotal q x
  have hp : x - j p ∈ nS ^ q := by
    apply (CompleteRegularPowerSeries.maximalIdealPower k r q _).mpr
    intro d
    by_cases hd : d.degree < q
    · rw [maximalIdeal_eq_bot, ← Ideal.zero_eq_bot, zero_pow (by omega : q - d.degree ≠ 0)]
      simp [p, j, MvPowerSeries.coeff_truncTotal_eq_ite, hd]
    · rw [show q - d.degree = 0 by omega, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
  have hf : f x = f (j p) := by
    have h := RingHom.mem_ker.mp (maximalIdeal_pow_le_ker f hq' hp)
    change f (x - j p) = 0 at h
    rwa [map_sub, sub_eq_zero] at h
  have hg : g x = g (j p) := by
    have h := RingHom.mem_ker.mp (maximalIdeal_pow_le_ker g hq' hp)
    change g (x - j p) = 0 at h
    rwa [map_sub, sub_eq_zero] at h
  exact hf.trans ((congrArg (fun e : MvPolynomial (Fin r) k →ₐ[k] A => e p) hpoly).trans hg.symm)

private theorem exists_series_hom_lift {A B : LocalArtinAlgebra.{u,u} k}
    (g : Hom B A) (hg : Function.Surjective g)
    (f : S →ₐ[k] A) [IsLocalHom f] :
    ∃ b : S →ₐ[k] B, IsLocalHom b ∧ g.val.comp b = f := by
  choose x hx using fun i : Fin r => hg (f (MvPowerSeries.X i))
  have hxmax (i : Fin r) : x i ∈ maximalIdeal B := by
    apply (show ¬ IsUnit (x i) → x i ∈ maximalIdeal B from id)
    intro hu
    have ha : IsUnit (f (MvPowerSeries.X i)) := hx i ▸ hu.map g.val
    exact variable_mem_maximalIdeal i (IsUnit.of_map f _ ha)
  letI : UniformSpace k := ⊥
  letI : UniformSpace B := ⊥
  letI : ContinuousSMul k B := DiscreteTopology.instContinuousSMul k B
  have hxnil (i : Fin r) : IsNilpotent (x i) := by
    obtain ⟨q, hq⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal B).mp inferInstance
    have hm := Ideal.pow_mem_pow (hxmax i) q
    refine ⟨q, ?_⟩
    simpa [hq] using hm
  have heval : MvPowerSeries.HasEval x :=
    ⟨fun i => (hxnil i).isTopologicallyNilpotent, by
      rw [Filter.cofinite_eq_bot]
      exact Filter.tendsto_bot⟩
  let b : S →ₐ[k] B := MvPowerSeries.aeval heval
  have hbX (i : Fin r) : b (MvPowerSeries.X i) = x i := by
    simpa [b, MvPolynomial.aeval_X] using
      MvPowerSeries.aeval_coe (R := k) heval (MvPolynomial.X i)
  have hb : IsLocalHom b := by
    suffices h : nS ≤ (maximalIdeal B).comap b.toRingHom from
      ⟨fun a ha => by
        by_contra hn
        exact h (show a ∈ nS from hn) ha⟩
    rw [series_maximalIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change b (MvPowerSeries.X i) ∈ maximalIdeal B
    rw [hbX]
    exact hxmax i
  letI : IsLocalHom b := hb
  refine ⟨b, hb, ?_⟩
  letI : IsLocalHom (g.val.comp b) := ⟨fun z hz =>
    IsUnit.of_map b z (IsUnit.of_map g.val _ hz)⟩
  apply series_hom_ext
  intro i
  change g (b (MvPowerSeries.X i)) = _
  rw [hbX, hx]

private theorem exists_smul_eq_of_finrank_one {V : Type u} [AddCommGroup V] [Module k V]
    (hd : Module.finrank k V = 1) {x : V} (hx : x ≠ 0) (y : V) :
    ∃ c : k, c • x = y := by
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hd
  have he : e.symm x ≠ 0 := fun h => hx (e.symm.injective (h.trans (map_zero e.symm).symm))
  refine ⟨e.symm y / e.symm x, e.symm.injective ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ he]

private theorem glue {F : ArtinFunctorModel.{u,w} k} (h₁ : H1Model F)
    {C B A : LocalArtinAlgebra.{u,u} k} (f : Hom C A) (g : Hom B A)
    (hg : SmallExtensionModel g) {x : F.toFunctor.obj C} {y : F.toFunctor.obj B}
    (hxy : F.toFunctor.map f x = F.toFunctor.map g y) :
    ∃ z : F.toFunctor.obj (pullback f g), F.toFunctor.map (pullbackFst f g) z = x ∧
      F.toFunctor.map (pullbackSnd f g) z = y := by
  obtain ⟨z, hz⟩ := h₁ f g hg ⟨(x, y), hxy⟩
  exact ⟨z, congrArg (fun v => v.val.1) hz, congrArg (fun v => v.val.2) hz⟩

private theorem exists_stage_lift {F : ArtinFunctorModel.{u,w} k} (T : Tower F r)
    (h₁ : H1Model F) (i : ℕ) {A B : LocalArtinAlgebra.{u,u} k}
    (f : Hom (T.stage i) A) (g : Hom B A) (hg : SmallExtensionModel g)
    (y : F.toFunctor.obj B)
    (hxy : F.toFunctor.map f (T.element i) = F.toFunctor.map g y) :
    ∃ l : Hom (T.stage (i + 1)) B,
      g.comp l = f.comp (artinTransition (seriesResidue k r) (T.decreasing (Nat.le_succ i))) := by
  let P : LocalArtinAlgebra.{u,u} k := pullback f g
  letI : IsLocalRing P := P.localRing
  let p : Hom P (T.stage i) := pullbackFst f g
  let s : Hom P B := pullbackSnd f g
  letI : IsLocalHom s.val := s.property
  let m : S →ₐ[k] T.stage i := Ideal.Quotient.mkₐ k (T.ideal i)
  let tr : Hom (T.stage (i + 1)) (T.stage i) :=
    artinTransition (seriesResidue k r) (T.decreasing (Nat.le_succ i))
  have hm : Function.Surjective m := Ideal.Quotient.mk_surjective
  have hp : Function.Surjective p.val := by
    intro a
    obtain ⟨b, hb⟩ := hg.1 (f a)
    exact ⟨⟨(a, b), hb.symm⟩, rfl⟩
  letI : IsLocalHom m :=
    ⟨(IsLocalHom.of_surjective m.toRingHom hm).map_nonunit⟩
  obtain ⟨ψ, hψ, hpψ⟩ := exists_series_hom_lift p hp m
  letI : IsLocalHom ψ := hψ
  have hpψ' (x : S) : p.val (ψ x) = m x := DFunLike.congr_fun hpψ x
  have hpair (a : P) : f (p.val a) = g (s.val a) := a.property
  suffices hl : ∃ q : Hom (T.stage (i + 1)) P, p.comp q = tr by
    obtain ⟨q, hq⟩ := hl
    refine ⟨s.comp q, Hom.ext fun x => ?_⟩
    change g (s.val (q.val x)) = f (tr.val x)
    exact (hpair (q.val x)).symm.trans (congrArg (fun v : Hom _ _ => f (v x)) hq)
  let K := RingHom.ker ψ.toRingHom
  have hK : K ≤ T.ideal i := by
    intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change m x = 0
    change ψ x = 0 at hx
    rw [← hpψ', hx, map_zero]
  -- Killing the stage ideal gives a section of the pullback projection.
  by_cases hsplit : T.ideal i ≤ K
  · let q₀ : (T.stage i) →ₐ[k] P :=
      Ideal.Quotient.liftₐ (T.ideal i) ψ (fun _ hx => hsplit hx)
    have hq₀ (a : T.stage i) : p.val (q₀ a) = a := by
      obtain ⟨x, rfl⟩ := hm a
      exact hpψ' x
    let q : Hom (T.stage i) P :=
      ⟨q₀, ⟨fun a ha => hq₀ a ▸ ha.map p.val⟩⟩
    exact ⟨q.comp tr, Hom.ext fun a => hq₀ (tr.val a)⟩
  · have hmul : nS * T.ideal i ≤ K := by
      apply Ideal.mul_le.mpr
      intro a ha b hb
      have hamax : ψ a ∈ maximalIdeal P := by
        change ¬ IsUnit (ψ a)
        exact fun hu => ha (IsUnit.of_map ψ _ hu)
      have hb₀ : p.val (ψ b) = 0 := (hpψ' b).trans (Ideal.Quotient.eq_zero_iff_mem.mpr hb)
      have hbker : s.val (ψ b) ∈ ExtensionKernel g := by
        change g (s.val (ψ b)) = 0
        rw [← hpair, hb₀, map_zero]
      change ψ (a * b) = 0
      rw [map_mul]
      apply Subtype.ext
      apply Prod.ext
      · change p.val (ψ a * ψ b) = p.val 0
        rw [map_mul, hb₀, mul_zero, map_zero]
      · change s.val (ψ a * ψ b) = s.val 0
        rw [map_mul, map_zero]
        exact hg.2.2 _ (fun hu => hamax (IsUnit.of_map s.val _ hu)) _ hbker
    obtain ⟨z, hz, hzK⟩ := IsConcreteLE.not_le_iff_exists.mp hsplit
    have hz₁ : p.val (ψ z) = 0 := (hpψ' z).trans (Ideal.Quotient.eq_zero_iff_mem.mpr hz)
    have toKernel (a : P) (ha : p.val a = 0) : s.val a ∈ ExtensionKernel g := by
      change g (s.val a) = 0
      rw [← hpair, ha, map_zero]
    let z₂ : ExtensionKernel g := ⟨s.val (ψ z), toKernel _ hz₁⟩
    have hz₂ : z₂ ≠ 0 := by
      intro he
      apply hzK
      change ψ z = 0
      exact Subtype.ext (Prod.ext hz₁ (congrArg Subtype.val he))
    -- A nonzero image of the stage ideal spans the kernel of the projection.
    have hsurj : Function.Surjective ψ := by
      intro a
      obtain ⟨x, hx⟩ := hm (p.val a)
      let v := a - ψ x
      have hv : p.val v = 0 := by
        change p.val (a - ψ x) = 0
        rw [map_sub, hpψ', hx, sub_self]
      let v₂ : ExtensionKernel g := ⟨s.val v, toKernel v hv⟩
      obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_one hg.2.1 hz₂ v₂
      have hcv : ψ (c • z) = v := by
        rw [map_smul]
        apply Subtype.ext
        apply Prod.ext
        · change p.val (c • ψ z) = p.val v
          rw [map_smul, hz₁, smul_zero, hv]
        · change s.val (c • ψ z) = s.val v
          rw [map_smul]
          exact congrArg Subtype.val hc
      exact ⟨c • z + x, by rw [map_add, hcv]; exact sub_add_cancel _ _⟩
    have hpow : ∃ q : ℕ, nS ^ q ≤ K :=
      ⟨i + 3, by
        rw [show i + 3 = (i + 2) + 1 by omega, pow_succ']
        exact (Ideal.mul_mono le_rfl (T.power i)).trans hmul⟩
    let Q := artinQuotient (seriesResidue k r) K (hK.trans (T.below i)) hpow
    let e : Q ≃ₐ[k] P := Ideal.quotientKerAlgEquivOfSurjective hsurj
    let pK : Hom Q (T.stage i) := artinTransition (seriesResidue k r) hK
    have he (x : S) : e (Ideal.Quotient.mk K x) = ψ x :=
      Ideal.quotientKerAlgEquivOfSurjective_mk hsurj x
    have hpe : p.comp (equivHom e) = pK := by
      apply Hom.ext
      intro a
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := K) a
      change p.val (e (Ideal.Quotient.mk K x)) = m x
      rw [he, hpψ']
    obtain ⟨v, hv, _⟩ := glue h₁ f g hg hxy
    have hleast : T.ideal (i + 1) ≤ K := by
      apply T.least i K hK hpow hmul
      refine ⟨F.toFunctor.map (equivHom e.symm) v, ?_⟩
      change SchlessingerTangentVectorSpaceSpec.onHom F pK
        (SchlessingerTangentVectorSpaceSpec.onHom F (equivHom e.symm) v) = T.element i
      rw [ArtinFunctor.onHom_comp F (equivHom e.symm) pK]
      have hcomp : pK.comp (equivHom e.symm) = p := by
        rw [← hpe]
        exact Hom.ext fun a => congrArg p.val (e.apply_symm_apply a)
      rw [hcomp]
      exact hv
    let qK : Hom (T.stage (i + 1)) Q := artinTransition (seriesResidue k r) hleast
    refine ⟨(equivHom e).comp qK, ?_⟩
    apply Hom.ext
    intro a
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := T.ideal (i + 1)) a
    change p.val (e (Ideal.Quotient.mk K x)) = m x
    rw [he, hpψ']

private theorem tangent_surjective_on_kernel {F : ArtinFunctorModel.{u,w} k}
    {R : CompleteLocalAlgebraModel k} (τ : (representableModel.{u,w} R).toFunctor ⟶ F.toFunctor)
    (ht : Function.Surjective (τ.app (dualModel k)))
    {A B : LocalArtinAlgebra.{u,u} k} {g : Hom B A} (hg : SmallExtensionModel g) :
    Function.Surjective (τ.app (splitModel k (ExtensionKernel g))) := by
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hg.2.1
  let l : Hom (splitModel k k) (splitModel k (ExtensionKernel g)) := splitMap e.toLinearMap
  have hl : Function.Bijective l.val := by
    constructor
    · intro x y h
      apply TrivSqZeroExt.ext
      · simpa only [l, splitMap_fst] using congrArg TrivSqZeroExt.fst h
      · apply e.injective
        exact (splitMap_snd e.toLinearMap x).symm.trans
          ((congrArg TrivSqZeroExt.snd h).trans (splitMap_snd e.toLinearMap y))
    · intro y
      let x : splitModel k k := (y.fst, e.symm y.snd)
      refine ⟨x, TrivSqZeroExt.ext (splitMap_fst e.toLinearMap x) ?_⟩
      exact (splitMap_snd e.toLinearMap x).trans (e.apply_symm_apply y.snd)
  have ht' : Function.Surjective (τ.app (splitModel k k)) := by
    have hall (C : LocalArtinAlgebra.{u,u} k) (hC : C = dualModel k) :
        Function.Surjective (τ.app C) := by
      subst C
      exact ht
    exact hall _ (split_eq_dual k)
  intro θ
  obtain ⟨z, hz⟩ := (ArtinFunctor.onHom_bijective F l hl).surjective θ
  obtain ⟨d, hd⟩ := ht' z
  have hn := ConcreteCategory.congr_hom (τ.naturality l) d
  refine ⟨(representableModel.{u,w} R).toFunctor.map l d, hn.trans ?_⟩
  change F.toFunctor.map l (τ.app (splitModel k k) d) = θ
  rw [hd]
  exact hz

private def completePullbackLift {R : CompleteLocalAlgebraModel k}
    {A B C : LocalArtinAlgebra.{u,u} k} (f : Hom A C) (g : Hom B C)
    (a : CompleteLocalAlgebra.Hom R A) (b : CompleteLocalAlgebra.Hom R B)
    (hab : a.postcomp f = b.postcomp g) : CompleteLocalAlgebra.Hom R (pullback f g) :=
  ⟨(a.val.prod b.val).codRestrict (AlgHom.pullback f.val g.val)
      (fun x => congrArg (fun e : CompleteLocalAlgebra.Hom R C => e x) hab),
    ⟨fun x hx =>
      IsUnit.of_map a.val x (hx.map (pullbackFst f g).val)⟩⟩

/-- The transformation attached to a Schlessinger tower lifts along every
small extension, with the prescribed image in the functor. -/
theorem towerSmooth : TowerSmooth.{u,w} := by
  intro k _ F r T hc τ h₁ h₂ hfactor heval ht A B g hg v
  let R := T.ring hc
  let a : CompleteLocalAlgebra.Hom R A := v.val.1.down
  let y : F.toFunctor.obj B := v.val.2
  have hy : τ.app A (ULift.up a) = F.toFunctor.map g y := v.property
  have evaluate {C : LocalArtinAlgebra.{u,u} k} (i : ℕ) (f : Hom (T.stage i) C)
      (b : CompleteLocalAlgebra.Hom R C) (hb : (T.projection i).postcomp f = b) :
      τ.app C (ULift.up b) = F.toFunctor.map f (T.element i) := by
    rw [← hb]
    exact heval C i f
  have natural {C D : LocalArtinAlgebra.{u,u} k} (l : Hom C D)
      (b : CompleteLocalAlgebra.Hom R C) :
      τ.app D (ULift.up (b.postcomp l)) = F.toFunctor.map l (τ.app C (ULift.up b)) := by
    let d : (representableModel.{u,w} R).toFunctor.obj C := ULift.up b
    have h := ConcreteCategory.congr_hom (τ.naturality l) d
    change τ.app D (ULift.up (b.postcomp l)) = F.toFunctor.map l (τ.app C (ULift.up b)) at h
    exact h
  obtain ⟨i, f, hf⟩ := hfactor A a
  obtain ⟨l, hl⟩ := exists_stage_lift T h₁ i f g hg y ((evaluate i f a hf).symm.trans hy)
  let b : CompleteLocalAlgebra.Hom R B := (T.projection (i + 1)).postcomp l
  have hba : b.postcomp g = a := by
    rw [← hf]
    apply CompleteLocalAlgebra.Hom.ext
    intro x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective (I := T.limitIdeal) x
    exact congrArg (fun e : Hom (T.stage (i + 1)) A => e (Ideal.Quotient.mk (T.ideal (i + 1)) s)) hl
  -- Use a stage through which the ring lift factors to split the new pullback.
  obtain ⟨j, h, hh⟩ := hfactor B b
  let p : CompleteLocalAlgebra.Hom R (T.stage j) := T.projection j
  let f' : Hom (T.stage j) A := g.comp h
  have hf' : p.postcomp f' = a := by
    calc
      p.postcomp f' = (p.postcomp h).postcomp g := rfl
      _ = a := by rw [hh, hba]
  obtain ⟨z, hz₁, hz₂⟩ := glue h₁ f' g hg ((evaluate j f' a hf').symm.trans hy)
  let e := splitPullbackEquiv f' g h hg rfl
  have he := splitPullbackEquiv_formula f' g h hg rfl
  let E := splitModel k (ExtensionKernel g)
  let z' := F.toFunctor.map (equivHom e) z
  have hz' : F.toFunctor.map (splitFst (T.stage j) g) z' = T.element j := by
    change onHom F (splitFst (T.stage j) g) (onHom F (equivHom e) z) = T.element j
    rw [ArtinFunctor.onHom_comp F]
    have he₁ : (splitFst (T.stage j) g).comp (equivHom e) = pullbackFst f' g :=
      Hom.ext fun t => (he.1 t).1
    rw [he₁]
    exact hz₁
  obtain ⟨d, hd⟩ := tangent_surjective_on_kernel τ ht.surjective hg
    (F.toFunctor.map (splitSnd (T.stage j) g) z')
  let δ : CompleteLocalAlgebra.Hom R E := d.down
  let α := residueHomModel (T.stage j)
  let β := residueHomModel E
  have hres : p.postcomp α = δ.postcomp β := by
    exact congrArg ULift.down (Subsingleton.elim
      (α := (representableModel.{u,w} R).toFunctor.obj (fieldModel k))
      (ULift.up (p.postcomp α)) (ULift.up (δ.postcomp β)))
  let q := completePullbackLift α β p δ hres
  have hq₁ : q.postcomp (splitFst (T.stage j) g) = p :=
    CompleteLocalAlgebra.Hom.ext fun _ => rfl
  have hq₂ : q.postcomp (splitSnd (T.stage j) g) = δ :=
    CompleteLocalAlgebra.Hom.ext fun _ => rfl
  have hp : τ.app (T.stage j) (ULift.up p) = T.element j := by
    have hp' : p.postcomp (Hom.id (T.stage j)) = p := CompleteLocalAlgebra.Hom.ext fun _ => rfl
    rw [evaluate j _ p hp']
    exact ConcreteCategory.congr_hom (F.toFunctor.map_id (T.stage j)) (T.element j)
  have hq : τ.app (SplitPullback (T.stage j) g) (ULift.up q) = z' := by
    apply (ArtinFunctor.splitResidueComparison_bijective F h₂ (T.stage j) g hg).injective
    apply Prod.ext
    · change F.toFunctor.map (splitFst (T.stage j) g) (τ.app _ (ULift.up q)) =
        F.toFunctor.map (splitFst (T.stage j) g) z'
      rw [← natural, hq₁, hp, hz']
    · change F.toFunctor.map (splitSnd (T.stage j) g) (τ.app _ (ULift.up q)) =
        F.toFunctor.map (splitSnd (T.stage j) g) z'
      rw [← natural, hq₂]
      exact hd
  let t := q.postcomp (equivHom e.symm)
  let b' := t.postcomp (pullbackSnd f' g)
  have ht₁ : t.postcomp (pullbackFst f' g) = p := by
    rw [← hq₁]
    exact CompleteLocalAlgebra.Hom.ext fun x => (he.2 (q.val x)).1
  have ht₂ : τ.app (pullback f' g) (ULift.up t) = z := by
    rw [natural, hq]
    change onHom F (equivHom e.symm) (onHom F (equivHom e) z) = z
    rw [ArtinFunctor.onHom_comp F]
    have hinv : (equivHom e.symm).comp (equivHom e) = Hom.id (pullback f' g) :=
      Hom.ext e.symm_apply_apply
    rw [hinv]
    exact ConcreteCategory.congr_hom (F.toFunctor.map_id _) z
  refine ⟨ULift.up b', Subtype.ext (Prod.ext ?_ ?_)⟩
  · apply congrArg ULift.up
    change b'.postcomp g = a
    rw [← hf', ← ht₁]
    exact CompleteLocalAlgebra.Hom.ext fun x => (t.val x).property.symm
  · change τ.app B (ULift.up b') = y
    rw [natural, ht₂]
    exact hz₂

end

end CommutativeAlgebraNotes.SchlessingerHullLifting
