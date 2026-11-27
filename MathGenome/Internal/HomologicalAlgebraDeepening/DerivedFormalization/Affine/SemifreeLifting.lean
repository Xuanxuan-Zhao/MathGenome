import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.SemifreeAlgebras
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.SemifreeLifting
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas

open CategoryTheory CategoryTheory.Limits

universe u v

namespace DerivedFormalization.Affine

variable {k : Type u} [Field k] [CharZero k]
variable {A P C D : NonpositiveCDGA.{u,v} k}

omit [CharZero k] in
private theorem comm_apply {X Y : ModuleCochain.{u,v} k}
    (f : X ⟶ Y) (i j : ℤ) (x : X.X i) :
    f.f j (X.d i j x) = Y.d i j (f.f i x) :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (f.comm i j).symm) x

namespace NonpositiveCDGA

/-- Every homogeneous cycle in the kernel of a surjective quasi-isomorphism
has a primitive in the kernel. -/
theorem exists_kernel_primitive (q : C ⟶ D)
    (hs : DegreewiseSurjective q) (hq : IsQuasiIso q)
    (i : ℤ) (z : C.complex.X (i + 1))
    (hz : C.complex.d (i + 1) (i + 1 + 1) z = 0)
    (hqz : q.chainMap.f (i + 1) z = 0) :
    ∃ w : C.complex.X i, C.complex.d i (i + 1) w = z ∧ q.chainMap.f i w = 0 := by
  let p := q.chainMap
  let K := kernel p
  let ι : K ⟶ C.complex := kernel.ι p
  let S := ShortComplex.kernelSequence p
  have : Epi p := HomologicalComplex.epi_of_epi_f p fun j =>
    (ModuleCat.epi_iff_surjective _).2 (hs j)
  have hS : S.ShortExact := by
    refine { exact := ShortComplex.kernelSequence_exact p, mono_f := ?_, epi_g := ?_ }
    · change Mono (kernel.ι p)
      infer_instance
    · change Epi p
      assumption
  have hK : K.Acyclic := hS.acyclic_X₁ hq
  have hExact (j : ℤ) : Function.Exact (ι.f j) (p.f j) := by
    let F := HomologicalComplex.eval (ModuleCat.{v} k) (ComplexShape.up ℤ) j
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).mp
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS j).exact
  have hInjective (j : ℤ) : Function.Injective (ι.f j) :=
    (ModuleCat.mono_iff_injective _).1 (by infer_instance)
  obtain ⟨z', hz'⟩ := (hExact (i + 1) z).1 hqz
  have hdz' : K.d (i + 1) (i + 1 + 1) z' = 0 := hInjective _ (by
    rw [comm_apply ι, hz', hz, map_zero])
  have he := (K.exactAt_iff' i (i + 1) (i + 1 + 1) (by simp) (by simp)).mp (hK (i + 1))
  have he' := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
    (K.sc' i (i + 1) (i + 1 + 1))).mp he
  obtain ⟨w, hw⟩ := (he' z').1 hdz'
  change K.d i (i + 1) w = z' at hw
  refine ⟨ι.f i w, ?_, (hExact i _).2 ⟨w, rfl⟩⟩
  rw [← comm_apply ι, hw, hz']

/-- Lift an element with a prescribed differential by correcting any lift
by a primitive of its error. -/
theorem exists_lift_with_differential (q : C ⟶ D)
    (hs : DegreewiseSurjective q) (hq : IsQuasiIso q)
    (i : ℤ) (b : D.complex.X i) (a : C.complex.X (i + 1))
    (ha : C.complex.d (i + 1) (i + 1 + 1) a = 0)
    (hqa : q.chainMap.f (i + 1) a = D.complex.d i (i + 1) b) :
    ∃ c : C.complex.X i, C.complex.d i (i + 1) c = a ∧ q.chainMap.f i c = b := by
  change ∀ j : ℤ, Function.Surjective (q.chainMap.f j) at hs
  obtain ⟨c, hc⟩ := hs i b
  let z := C.complex.d i (i + 1) c - a
  have hz : C.complex.d (i + 1) (i + 1 + 1) z = 0 := by
    dsimp [z]
    have hdd := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
      (C.complex.d_comp_d i (i + 1) (i + 1 + 1))) c
    change C.complex.d (i + 1) (i + 1 + 1) (C.complex.d i (i + 1) c) = 0 at hdd
    rw [map_sub, hdd, ha, sub_zero]
  have hqz : q.chainMap.f (i + 1) z = 0 := by
    dsimp [z]
    rw [map_sub, comm_apply q.chainMap, hqa, hc, sub_self]
  obtain ⟨w, hw, hqw⟩ := exists_kernel_primitive q hs hq i z hz hqz
  exact ⟨c - w, by rw [map_sub, hw]; exact sub_sub_cancel _ _, by
    rw [map_sub, hqw, sub_zero, hc]⟩

end NonpositiveCDGA

namespace Semifree

noncomputable section

variable {V : Variables.{v}} {aP : A ⟶ P}

/-- The homogeneous generator in the presented algebra. -/
private def generator (E : StagedPresentation A V aP) (x : V.Index) :
    P.complex.X (V.degree x) :=
  E.component _ (variableTerm A V x)

/-- Transport the differential of the presented algebra to its monomials. -/
private def polynomialDifferential (E : StagedPresentation A V aP) (i : ℤ) :
    Polynomial A V i →ₗ[k] Polynomial A V (i + 1) :=
  (E.component (i + 1)).symm.toLinearMap.comp
    ((P.complex.d i (i + 1)).hom.comp (E.component i).toLinearMap)

private def generatorDifferential (E : StagedPresentation A V aP) (x : V.Index) :
    Polynomial A V (V.degree x + 1) :=
  polynomialDifferential E (V.degree x) (variableTerm A V x)

@[simp] private theorem component_polynomialDifferential (E : StagedPresentation A V aP)
    (i : ℤ) (p : Polynomial A V i) :
    E.component (i + 1) (polynomialDifferential E i p) =
      P.complex.d i (i + 1) (E.component i p) :=
  (E.component (i + 1)).apply_symm_apply _

private def presentationDerivation (E : StagedPresentation A V aP) :
    Derivation A V (generatorDifferential E) where
  d := polynomialDifferential E
  leibniz i j n h p r := by
    apply (E.component (n + 1)).injective
    simp only [component_polynomialDifferential, E.map_mul, map_add]
    rw [show E.component (n + 1)
      (i.negOnePow • polynomialMul A V i (j + 1) (n + 1) (by omega) p
        (polynomialDifferential E j r)) =
      i.negOnePow • E.component (n + 1)
        (polynomialMul A V i (j + 1) (n + 1) (by omega) p
          (polynomialDifferential E j r)) from
      LinearMap.map_smul_of_tower (E.component (n + 1)).toLinearMap _ _]
    rw [E.map_mul, component_polynomialDifferential]
    exact P.toDGAlgebra.leibniz (a := ()) (b := ()) (c := ()) i j n h
      (E.component i p) (E.component j r)
  on_base i b := by
    apply (E.component (i + 1)).injective
    rw [component_polynomialDifferential, E.map_base, E.map_base, comm_apply aP.chainMap]
  on_var _ := rfl

private def evaluate (aC : A ⟶ C) (values : ∀ x, C.complex.X (V.degree x)) :
    GradedLift A V C.toCommDGAlgebra (fun i => (aC.chainMap.f i).hom) values :=
  (Classical.choice (gradedUniversalProperty A V C.toCommDGAlgebra
    (fun i => (aC.chainMap.f i).hom) aC.map_one aC.map_mul values)).default

private def presentedMap (E : StagedPresentation A V aP) (f : P ⟶ D) :
    GradedLift A V D.toCommDGAlgebra
      (fun i => ((aP ≫ f).chainMap.f i).hom)
      (fun x => f.chainMap.f (V.degree x) (generator E x)) where
  component i := (f.chainMap.f i).hom.comp (E.component i).toLinearMap
  map_mul i j n h p r := by
    change f.chainMap.f n (E.component n (polynomialMul A V i j n h p r)) = _
    rw [E.map_mul, f.map_mul]
    rfl
  map_base i b := by
    change f.chainMap.f i (E.component i (coefficient A V i b)) =
      f.chainMap.f i (aP.chainMap.f i b)
    rw [E.map_base]
  map_var _ := rfl

/-- Agreement on the generators of a subalgebra implies agreement on its polynomials. -/
private theorem map_evaluation_on {aC : A ⟶ C} {aD : A ⟶ D} (q : C ⟶ D)
    {valuesC : ∀ x, C.complex.X (V.degree x)} {valuesD : ∀ x, D.complex.X (V.degree x)}
    (F : GradedLift A V C.toCommDGAlgebra (fun i => (aC.chainMap.f i).hom) valuesC)
    (G : GradedLift A V D.toCommDGAlgebra (fun i => (aD.chainMap.f i).hom) valuesD)
    (base : aC ≫ q = aD) (S : Set V.Index)
    (vars : ∀ x ∈ S, q.chainMap.f (V.degree x) (valuesC x) = valuesD x) :
    ∀ i (p : Polynomial A V i), UsesOnly A V S p →
      q.chainMap.f i (F.component i p) = G.component i p := by
  apply polynomial_generated_on A V S (fun i p => q.chainMap.f i (F.component i p) = G.component i p)
  · intro i
    simp
  · intro i p r hp hr
    simp only [map_add, hp, hr]
  · intro i s p hp
    simp only [LinearMap.map_smul_of_tower, hp]
  · intro i a
    rw [F.map_base, G.map_base]
    exact DFunLike.congr_fun
      (congrArg (fun m : A ⟶ D => (m.chainMap.f i).hom) base) a
  · intro x hx
    rw [F.map_var, G.map_var]
    exact vars x hx
  · intro i j n h p r hp hr
    rw [F.map_mul, G.map_mul]
    change q.chainMap.f n (C.mul i j n h (F.component i p) (F.component j r)) =
      D.mul i j n h (G.component i p) (G.component j r)
    rw [q.map_mul, hp, hr]

/-- Compatibility with the differential can be checked on the polynomial generators. -/
private theorem evaluation_comm_on (E : StagedPresentation A V aP) {aC : A ⟶ C}
    {values : ∀ x, C.complex.X (V.degree x)}
    (F : GradedLift A V C.toCommDGAlgebra (fun i => (aC.chainMap.f i).hom) values)
    (S : Set V.Index) (vars : ∀ x ∈ S,
      C.complex.d (V.degree x) (V.degree x + 1) (values x) =
        F.component (V.degree x + 1) (generatorDifferential E x)) :
    ∀ i (p : Polynomial A V i), UsesOnly A V S p →
      C.complex.d i (i + 1) (F.component i p) =
        F.component (i + 1) (polynomialDifferential E i p) := by
  let δ := presentationDerivation E
  change ∀ i (p : Polynomial A V i), UsesOnly A V S p →
    C.complex.d i (i + 1) (F.component i p) = F.component (i + 1) (δ.d i p)
  apply polynomial_generated_on A V S
    (fun i p => C.complex.d i (i + 1) (F.component i p) = F.component (i + 1) (δ.d i p))
  · intro i
    simp
  · intro i p r hp hr
    simp only [map_add, hp, hr]
  · intro i s p hp
    simp only [LinearMap.map_smul_of_tower, hp]
  · intro i b
    rw [δ.on_base, F.map_base, F.map_base]
    exact (comm_apply aC.chainMap i (i + 1) b).symm
  · intro x hx
    rw [δ.on_var, F.map_var]
    exact vars x hx
  · intro i j n h p r hp hr
    rw [δ.leibniz, map_add, LinearMap.map_smul_of_tower, F.map_mul, F.map_mul, F.map_mul]
    change C.complex.d n (n + 1) (C.mul i j n h (F.component i p) (F.component j r)) =
      C.mul (i + 1) j (n + 1) (by omega) (F.component (i + 1) (δ.d i p)) (F.component j r) +
        i.negOnePow • C.mul i (j + 1) (n + 1) (by omega)
          (F.component i p) (F.component (j + 1) (δ.d j r))
    rw [C.toDGAlgebra.leibniz (a := ()) (b := ()) (c := ())]
    rw [hp, hr]

/-- Strict lifting from a semifree extension through a degreewise surjective
quasi-isomorphism of nonpositive cdgas under the base. -/
theorem exists_lift_of_surjective_quasiIso :
    Specs.DerivedFormalization.Affine.SemifreeLifting.Lifting.{u,v} := by
  intro k _ _ A P C D aP aC aD f q hSemifree hf hq hs hQuasi
  classical
  obtain ⟨V, ⟨E⟩⟩ := hSemifree
  have hBase : aC ≫ q = aP ≫ f := hq.trans hf.symm

  let before : V.Index → V.Index → Prop := fun y x => E.stages.stage y < E.stages.stage x
  have wf : WellFounded before := InvImage.wf E.stages.stage E.stages.wellFounded
  let extendByZero (x : V.Index)
      (earlier : ∀ y, before y x → C.complex.X (V.degree y)) :
      ∀ y, C.complex.X (V.degree y) :=
    fun y => if h : before y x then earlier y h else 0
  let lifts (x : V.Index) (z : C.complex.X (V.degree x + 1))
      (c : C.complex.X (V.degree x)) : Prop :=
    C.complex.d (V.degree x) (V.degree x + 1) c = z ∧
      q.chainMap.f (V.degree x) c = f.chainMap.f (V.degree x) (generator E x)
  let chooseLift (x : V.Index) (z : C.complex.X (V.degree x + 1)) :
      C.complex.X (V.degree x) :=
    if h : ∃ c, lifts x z c then Classical.choose h else 0
  let step (x : V.Index) (earlier : ∀ y, before y x → C.complex.X (V.degree y)) :
      C.complex.X (V.degree x) :=
    chooseLift x ((evaluate aC (extendByZero x earlier)).component _ (generatorDifferential E x))
  let values : ∀ x, C.complex.X (V.degree x) := wf.fix step
  let F := evaluate aC values
  let G := presentedMap E f

  -- The differential of x depends only on values from earlier stages.
  have hValues : ∀ x, lifts x (F.component _ (generatorDifferential E x)) (values x) := by
    intro x
    refine wf.induction (C := fun y =>
      lifts y (F.component _ (generatorDifferential E y)) (values y)) x ?_
    clear x
    intro x ih
    let i := V.degree x
    let dx := generatorDifferential E x
    let previous := extendByZero x (fun y _ => values y)
    have hEarlier : UsesOnly A V (E.stages.before (E.stages.stage x)) dx := E.earlier x
    have hEval : (evaluate aC previous).component (i + 1) dx = F.component (i + 1) dx := by
      refine map_evaluation_on (𝟙 C) (evaluate aC previous) F (Category.comp_id aC)
        (E.stages.before (E.stages.stage x)) ?_ (i + 1) dx hEarlier
      intro y hy
      change before y x at hy
      change previous y = values y
      dsimp only [previous, extendByZero]
      rw [dite_eq_left hy]
    have hCycle : C.complex.d (i + 1) (i + 1 + 1) (F.component (i + 1) dx) = 0 := by
      rw [evaluation_comm_on E F (E.stages.before (E.stages.stage x))
        (fun y hy => (ih y hy).1) (i + 1) dx hEarlier]
      suffices polynomialDifferential E (i + 1) dx = 0 by rw [this, map_zero]
      apply (E.component (i + 1 + 1)).injective
      rw [component_polynomialDifferential, map_zero]
      change P.complex.d (i + 1) (i + 1 + 1)
        (E.component (i + 1) (polynomialDifferential E i (variableTerm A V x))) = 0
      rw [component_polynomialDifferential]
      exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
        (P.complex.d_comp_d i (i + 1) (i + 1 + 1))) (generator E x)
    have hImage : q.chainMap.f (i + 1) (F.component (i + 1) dx) =
        D.complex.d i (i + 1) (f.chainMap.f i (generator E x)) := by
      rw [map_evaluation_on q F G hBase (E.stages.before (E.stages.stage x))
        (fun y hy => (ih y hy).2) (i + 1) dx hEarlier]
      change f.chainMap.f (i + 1)
        (E.component (i + 1) (polynomialDifferential E i (variableTerm A V x))) = _
      rw [component_polynomialDifferential, comm_apply f.chainMap]
      rfl
    have hExists : ∃ c, lifts x (F.component (i + 1) dx) c :=
      NonpositiveCDGA.exists_lift_with_differential q hs hQuasi i _ _ hCycle hImage
    have hFix : values x = chooseLift x ((evaluate aC previous).component (i + 1) dx) :=
      WellFounded.fix_eq wf step x
    rw [hEval] at hFix
    change lifts x (F.component (i + 1) dx) (values x)
    rw [hFix]
    dsimp only [chooseLift]
    rw [dite_eq_left hExists]
    exact Classical.choose_spec hExists

  have hComm (i : ℤ) (p : Polynomial A V i) :
      C.complex.d i (i + 1) (F.component i p) =
        F.component (i + 1) (polynomialDifferential E i p) :=
    evaluation_comm_on E F Set.univ (fun x _ => (hValues x).1) i p (fun _ _ _ _ => Set.mem_univ _)
  have hImage (i : ℤ) (p : Polynomial A V i) :
      q.chainMap.f i (F.component i p) = f.chainMap.f i (E.component i p) :=
    map_evaluation_on q F G hBase Set.univ (fun x _ => (hValues x).2) i p
      (fun _ _ _ _ => Set.mem_univ _)
  let g : P ⟶ C :=
    { chainMap :=
        { f := fun i => ModuleCat.ofHom ((F.component i).comp (E.component i).symm.toLinearMap)
          comm' := by
            intro i j hij
            change i + 1 = j at hij
            subst j
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro p
            change C.complex.d i (i + 1) (F.component i ((E.component i).symm p)) =
              F.component (i + 1) ((E.component (i + 1)).symm (P.complex.d i (i + 1) p))
            rw [hComm]
            change F.component (i + 1) ((E.component (i + 1)).symm
              (P.complex.d i (i + 1) (E.component i ((E.component i).symm p)))) = _
            rw [LinearEquiv.apply_symm_apply] }
      map_one := by
        change F.component 0 ((E.component 0).symm P.one) = C.one
        rw [← E.map_one, LinearEquiv.symm_apply_apply, F.map_base, aC.map_one]
      map_mul := by
        intro i j n h p r
        change F.component n ((E.component n).symm (P.mul i j n h p r)) =
          C.mul i j n h (F.component i ((E.component i).symm p))
            (F.component j ((E.component j).symm r))
        have hm := E.map_mul i j n h ((E.component i).symm p) ((E.component j).symm r)
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at hm
        rw [← hm, LinearEquiv.symm_apply_apply, F.map_mul] }
  refine ⟨g, ?_, ?_⟩
  · apply CommDGAlgebra.Hom.ext_chainMap
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    change F.component i ((E.component i).symm (aP.chainMap.f i b)) = aC.chainMap.f i b
    rw [← E.map_base, LinearEquiv.symm_apply_apply, F.map_base]
  · apply CommDGAlgebra.Hom.ext_chainMap
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro p
    change q.chainMap.f i (F.component i ((E.component i).symm p)) = f.chainMap.f i p
    rw [hImage, LinearEquiv.apply_symm_apply]

end
end Semifree
end DerivedFormalization.Affine
