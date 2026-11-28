import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.PathResolution
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.EulerExt
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-! The Euler characteristic of the two-term projective resolution. -/

open CategoryTheory CategoryTheory.Abelian

universe u v w d

namespace RepTheorySurvey.Quiver.EulerExt

open RM03 PathResolutionSpec EulerExtSpec
open scoped EulerExtSpec ModuleCat ModuleCat.Algebra DirectSum TensorProduct

noncomputable section

variable {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q]

local notation "A" => PathAlgebra k Q

private theorem right_mul_vertex (i : Q) (p : VertexProjective k i) :
    p.val * PathAlgebra.vertex k i = p.val := by
  obtain ⟨y, hy⟩ := (Forms.mem_projectiveAt k i p.val).mp p.property
  rw [← hy, mul_assoc, PathAlgebra.vertex_idempotent]

private theorem coordinates_vertex_smul (W : QuiverRepresentation.{u, v, w, d} k Q)
    (i : Q) (z : Target W) :
    QuiverModuleEquivalence.coordinates W (PathAlgebra.vertex k i • z) =
      PathOperators.inclusion W i (PathOperators.projection W i
        (QuiverModuleEquivalence.coordinates W z)) :=
  (QuiverModuleEquivalence.coordinates_smul W _ _).trans (PathOperators.action_vertex W i _)

private def vertexEvaluation (V W : QuiverRepresentation.{u, v, w, d} k Q) (i j : Q) :
    (VertexProjective k i ⊗[k] V.vertex j →ₗ[A] Target W) →ₗ[k]
      (V.vertex j →ₗ[k] W.vertex i) where
  toFun f := (PathOperators.projection W i).comp
    ((QuiverModuleEquivalence.coordinates W).toLinearMap.comp
      (TensorProduct.AlgebraTensorModule.curry f (pathVector Quiver.Path.nil)))
  map_add' f g := LinearMap.ext fun x => by
    let project := (PathOperators.projection W i).comp
      (QuiverModuleEquivalence.coordinates W).toLinearMap
    let z : VertexProjective k i ⊗[k] V.vertex j := pathVector Quiver.Path.nil ⊗ₜ[k] x
    change project (f z + g z) = project (f z) + project (g z)
    exact project.map_add _ _
  map_smul' c f := LinearMap.ext fun x => by
    let project := (PathOperators.projection W i).comp
      (QuiverModuleEquivalence.coordinates W).toLinearMap
    let z : VertexProjective k i ⊗[k] V.vertex j := pathVector Quiver.Path.nil ⊗ₜ[k] x
    change project (c • f z) = c • project (f z)
    exact project.map_smul _ _

private theorem vertexEvaluation_apply (V W : QuiverRepresentation.{u, v, w, d} k Q)
    (i j : Q) (f : VertexProjective k i ⊗[k] V.vertex j →ₗ[A] Target W) (x : V.vertex j) :
    vertexEvaluation V W i j f x = PathOperators.projection W i
      (QuiverModuleEquivalence.coordinates W (f (pathVector Quiver.Path.nil ⊗ₜ[k] x))) := rfl

private def extendVertexMap {V W : QuiverRepresentation.{u, v, w, d} k Q} {i j : Q}
    (g : V.vertex j →ₗ[k] W.vertex i) :
    VertexProjective k i ⊗[k] V.vertex j →ₗ[A] Target W :=
  let point := (QuiverModuleEquivalence.coordinates W).symm.toLinearMap.comp
    ((PathOperators.inclusion W i).comp g)
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun p => (p : A) • point
      map_add' p q := add_smul (p : A) (q : A) _
      map_smul' a p := mul_smul a (p : A) _ }

private theorem extendVertexMap_tmul {V W : QuiverRepresentation.{u, v, w, d} k Q} {i j : Q}
    (g : V.vertex j →ₗ[k] W.vertex i) (p : VertexProjective k i) (x : V.vertex j) :
    extendVertexMap (V := V) (W := W) g (p ⊗ₜ[k] x) =
      (p : A) • ((QuiverModuleEquivalence.coordinates W).symm
        (PathOperators.inclusion W i (g x)) : Target W) :=
  TensorProduct.AlgebraTensorModule.lift_tmul _ p x

private def vertexHomEquiv (V W : QuiverRepresentation.{u, v, w, d} k Q) (i j : Q) :
    (VertexProjective k i ⊗[k] V.vertex j →ₗ[A] Target W) ≃ₗ[k]
      (V.vertex j →ₗ[k] W.vertex i) := by
  refine LinearEquiv.ofBijective (vertexEvaluation V W i j) ⟨?_, ?_⟩
  · intro f g h
    apply TensorProduct.AlgebraTensorModule.ext
    intro p x
    let e : VertexProjective k i := pathVector Quiver.Path.nil
    have hgen (q : VertexProjective k i) : (q : A) • e = q :=
      Subtype.ext (right_mul_vertex i q)
    have hfixed (a : VertexProjective k i ⊗[k] V.vertex j →ₗ[A] Target W) :
        PathAlgebra.vertex k i • a (e ⊗ₜ[k] x) = a (e ⊗ₜ[k] x) := by
      rw [← a.map_smul]
      change a ((e : A) • (e ⊗ₜ[k] x)) = _
      rw [PathResolution.tensor_left_action k V i j, hgen]
    have heval := LinearMap.congr_fun h x
    rw [vertexEvaluation_apply, vertexEvaluation_apply] at heval
    change PathOperators.projection W i (QuiverModuleEquivalence.coordinates W (f (e ⊗ₜ[k] x))) =
      PathOperators.projection W i (QuiverModuleEquivalence.coordinates W (g (e ⊗ₜ[k] x))) at heval
    have hvertex : f (e ⊗ₜ[k] x) = g (e ⊗ₜ[k] x) := by
      apply (QuiverModuleEquivalence.coordinates W).injective
      calc
        _ = QuiverModuleEquivalence.coordinates W (PathAlgebra.vertex k i • f (e ⊗ₜ[k] x)) :=
          congrArg (QuiverModuleEquivalence.coordinates W) (hfixed f).symm
        _ = QuiverModuleEquivalence.coordinates W (PathAlgebra.vertex k i • g (e ⊗ₜ[k] x)) := by
          rw [coordinates_vertex_smul, coordinates_vertex_smul, heval]
        _ = _ := congrArg (QuiverModuleEquivalence.coordinates W) (hfixed g)
    rw [← hgen p, ← PathResolution.tensor_left_action k V i j,
      f.map_smul, g.map_smul, hvertex]
  · intro g
    refine ⟨extendVertexMap g, LinearMap.ext fun x => ?_⟩
    rw [vertexEvaluation_apply, extendVertexMap_tmul]
    let z : Target W := (QuiverModuleEquivalence.coordinates W).symm
      (PathOperators.inclusion W i (g x))
    change PathOperators.projection W i (QuiverModuleEquivalence.coordinates W
      (PathAlgebra.vertex k i • z)) = _
    rw [coordinates_vertex_smul W i z]
    simp only [z, LinearEquiv.apply_symm_apply, PathOperators.projection_inclusion]

theorem evaluation_at_vertex : EvaluationAtVertex.{u, v, w, d} := by
  intro k Q _ _ _ V W i j
  exact ⟨vertexHomEquiv V W i j, vertexEvaluation_apply V W i j⟩

private def directSumHomEquiv {ι : Type*} (M : ι → Type*)
    [∀ a, AddCommGroup (M a)] [∀ a, Module A (M a)] (N : ModuleCat.{d} A) :
    ((⨁ a, M a) →ₗ[A] N) ≃ₗ[k] (∀ a, M a →ₗ[A] N) := by
  classical
  refine
    { toFun := fun f a => f.comp (DirectSum.lof A ι M a)
      invFun := DirectSum.toModule A ι N
      left_inv := by
        intro f
        exact LinearMap.ext fun x => (DirectSum.toModule.unique A f x).symm
      right_inv := by
        intro f
        exact funext fun a => LinearMap.ext fun x => DirectSum.toModule_lof A a x
      map_add' := fun _ _ => funext fun _ => LinearMap.ext fun _ => rfl
      map_smul' := fun _ _ => funext fun _ => LinearMap.ext fun _ => rfl }

private def tensorSumHomEquiv {ι : Type*}
    (V W : QuiverRepresentation.{u, v, w, d} k Q) (s t : ι → Q)
    (M : ModuleCat.{d} A) (e : M ≃ₗ[A] ⨁ a, VertexProjective k (t a) ⊗[k] V.vertex (s a)) :
    (M ⟶ Target W) ≃ₗ[k] (∀ a, V.vertex (s a) →ₗ[k] W.vertex (t a)) :=
  (ModuleCat.homLinearEquiv (S := k)).trans
    ((e.congrLeft (Target W) k).trans
      ((directSumHomEquiv (fun a => VertexProjective k (t a) ⊗[k] V.vertex (s a)) (Target W)).trans
        (LinearEquiv.piCongrRight fun a => vertexHomEquiv V W (t a) (s a))))

private theorem tensorSumHom_finite_finrank {ι : Type*} [Fintype ι]
    (V W : FormsSpec.FiniteRepresentation.{u, v, w, d} k Q) (s t : ι → Q)
    (M : ModuleCat.{d} A) (e : M ≃ₗ[A] ⨁ a, VertexProjective k (t a) ⊗[k] QuiverRepresentation.vertex V.obj (s a)) :
    Module.Finite k (M ⟶ Target W.obj) ∧
      Module.finrank k (M ⟶ Target W.obj) =
        ∑ a, Module.finrank k (QuiverRepresentation.vertex V.obj (s a)) * Module.finrank k (QuiverRepresentation.vertex W.obj (t a)) := by
  let (i : Q) : Module.Finite k (QuiverRepresentation.vertex V.obj i) := V.property i
  let (i : Q) : Module.Finite k (QuiverRepresentation.vertex W.obj i) := W.property i
  let equiv := tensorSumHomEquiv V.obj W.obj s t M e
  refine ⟨Module.Finite.equiv equiv.symm, equiv.finrank_eq.trans ?_⟩
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_linearMap]

private abbrev homDifferential {X : ModuleCat.{d} A} (P : ProjectiveResolution X)
    (Y : ModuleCat.{d} A) :
    (P.complex.X 0 ⟶ Y) →ₗ[k] (P.complex.X 1 ⟶ Y) :=
  Linear.leftComp k Y (P.complex.d 1 0)

private def homKernelEquiv {X : ModuleCat.{d} A} (P : ProjectiveResolution X)
    (Y : ModuleCat.{d} A) : (X ⟶ Y) ≃ₗ[k] LinearMap.ker (homDifferential P Y) := by
  let aug : P.complex.X 0 ⟶ X := P.π.f 0
  letI : Epi aug := inferInstanceAs (Epi (P.π.f 0))
  let F := (Linear.leftComp k Y aug).codRestrict (LinearMap.ker (homDifferential P Y)) (fun f => by
    change P.complex.d 1 0 ≫ (aug ≫ f) = 0
    have hz : P.complex.d 1 0 ≫ aug = 0 := P.complex_d_comp_π_f_zero
    rw [← Category.assoc, hz]
    simp)
  refine LinearEquiv.ofBijective F ⟨?_, ?_⟩
  · intro f g h
    exact (cancel_epi aug).mp (congrArg Subtype.val h)
  · intro f
    obtain ⟨g, hg⟩ := P.exact₀.desc' f.val f.property
    exact ⟨g, Subtype.ext hg⟩

private def extOneMap {V W : QuiverRepresentation.{u, v, w, d} k Q} (P : Resolution V) :
    (P.resolution.complex.X 1 ⟶ Target W) →ₗ[k]
      Ext.{max u v w (d + 1)} (Target V) (Target W) 1 := by
  have hd (f : P.resolution.complex.X 1 ⟶ Target W) :
      P.resolution.complex.d 2 1 ≫ f = 0 := (P.higher 0).eq_of_src _ _
  exact
    { toFun := fun f => P.resolution.extMk f 2 rfl (hd f)
      map_add' := fun f g => (P.resolution.add_extMk f g 2 rfl (hd f) (hd g)).symm
      map_smul' := fun c f => (P.resolution.smul_extMk c f 2 rfl (hd f)).symm }

private theorem extOneMap_surjective {V W : QuiverRepresentation.{u, v, w, d} k Q}
    (P : Resolution V) : Function.Surjective (extOneMap (W := W) P) := by
  intro x
  obtain ⟨f, hf, h⟩ := P.resolution.extMk_surjective x 2 rfl
  exact ⟨f, h⟩

private theorem extOneMap_ker {V W : QuiverRepresentation.{u, v, w, d} k Q}
    (P : Resolution V) :
    LinearMap.ker (extOneMap (W := W) P) = LinearMap.range (homDifferential P.resolution (Target W)) := by
  ext f
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  exact P.resolution.extMk_eq_zero_iff f 2 rfl ((P.higher 0).eq_of_src _ _) 0 rfl

private theorem hom_ext_formula_of_resolution [Fintype (Arrow Q)]
    (V W : FormsSpec.FiniteRepresentation.{u, v, w, d} k Q) (P : Resolution V.obj) :
    HomExtFormula V W := by
  obtain ⟨finite₀, rank₀⟩ :=
    tensorSumHom_finite_finrank V W id id (P.resolution.complex.X 0) P.degreeZero
  obtain ⟨finite₁, rank₁⟩ :=
    tensorSumHom_finite_finrank V W (fun a : Arrow Q => a.1) (fun a => a.2.1)
      (P.resolution.complex.X 1) P.degreeOne
  let := finite₀
  let := finite₁
  let D := homDifferential P.resolution (Target W.obj)
  let H := homKernelEquiv P.resolution (Target W.obj)
  let E := extOneMap (W := W.obj) P
  have surj := extOneMap_surjective (W := W.obj) P
  have kerE : LinearMap.ker E = LinearMap.range D := extOneMap_ker P
  refine ⟨Module.Finite.equiv H.symm, Module.Finite.of_surjective E surj, ?_⟩
  have h₀ := D.finrank_range_add_finrank_ker
  change Module.finrank k (LinearMap.range D) + Module.finrank k (LinearMap.ker D) = _ at h₀
  rw [← H.finrank_eq, rank₀] at h₀
  have h₁ := (LinearMap.range D).finrank_quotient_add_finrank
  rw [← kerE, (E.quotKerEquivOfSurjective surj).finrank_eq, kerE, rank₁] at h₁
  have h₀' := congrArg (fun n : ℕ => (n : ℤ)) h₀
  have h₁' := congrArg (fun n : ℕ => (n : ℤ)) h₁
  simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_mul] at h₀' h₁'
  dsimp only [id] at h₀'
  unfold FormsSpec.eulerForm FormsSpec.dimensionVector
  omega

private theorem ext_succ_succ_eq_zero {V W : QuiverRepresentation.{u, v, w, d} k Q}
    (P : Resolution V) (n : ℕ)
    (x : Ext.{max u v w (d + 1)} (Target V) (Target W) (n + 2)) : x = 0 := by
  obtain ⟨f, hf, rfl⟩ := P.resolution.extMk_surjective x (n + 2 + 1) rfl
  have h : f = 0 := (P.higher n).eq_of_src f 0
  subst f
  exact P.resolution.extMk_zero _ rfl

theorem higher_ext_vanishing [Fintype (Arrow Q)] (h : ¬ HasOrientedCycle Q)
    (V W : FormsSpec.FiniteRepresentation.{u, v, w, d} k Q) : HigherExtVanishing V W := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 2 m]
  exact subsingleton_of_forall_eq 0 (ext_succ_succ_eq_zero (PathResolution.resolutionData V.obj h) m)

theorem two_term_projective_resolution : TwoTermProjectiveResolution.{u, v, w, d} := by
  intro k Q _ _ _ _ h V
  let P := PathResolution.resolutionData V.obj h
  exact ⟨⟨P⟩, fun W => ⟨hom_ext_formula_of_resolution V W P, higher_ext_vanishing h V W⟩⟩

end

end RepTheorySurvey.Quiver.EulerExt
