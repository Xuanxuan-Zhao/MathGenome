import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CompactFlagOrbit
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClosedMatrixGroups
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CompactConjugation
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.InnerDerivations
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Module.Submodule.Bilinear
import Mathlib.Topology.Algebra.Group.Pointwise

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace LieAlgebrasAndRepresentations.CompactFlagOrbit

open Specs.LieAlgebrasAndRepresentations
open Specs.LieAlgebrasAndRepresentations.CompactConjugation
open Specs.LieAlgebrasAndRepresentations.CompactFlagOrbit
open ClosedMatrixGroups NormedSpace Topology Filter
open scoped Pointwise ComplexConjugate

section Exponential

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
local instance : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ ℂ F
local instance : NormedAlgebra ℝ (End E) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ (End F) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ (End E) := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℚ (End F) := NormedAlgebra.restrictScalars ℚ ℂ _

private lemma exp_apply_of_intertwining [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (e : E ≃ₗ[ℂ] F) (D : End E) (T : End F)
    (h : ∀ v, e (D v) = T (e v)) (v : E) :
    e (exp D v) = exp T (e v) := by
  let f := e.toContinuousLinearEquiv
  have hf : f.conjContinuousAlgEquiv D = T := by
    ext w
    change e (D (e.symm w)) = T w
    simpa only [e.apply_symm_apply] using h (e.symm w)
  have hexp := NormedSpace.map_exp f.conjContinuousAlgEquiv f.conjContinuousAlgEquiv.continuous D
  rw [hf] at hexp
  have hv := DFunLike.congr_fun hexp (e v)
  change e (exp D (e.symm (e v))) = exp T (e v) at hv
  simpa only [e.symm_apply_apply] using hv

variable [CompleteSpace E] [CompleteSpace F]

private lemma hasDerivAt_exp_apply (X : End E) (v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp (s • X) v) (X (exp (t • X) v)) t := by
  simpa [Function.comp_def] using ((ContinuousLinearMap.apply ℂ E v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const' X t)

private lemma hasDerivAt_exp_apply_bilinear (X : End F) {f : ℝ → F} {f' : F}
    {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s : ℝ => exp (s • X) (f s))
      (exp (t • X) f' + exp (t • X) (X (f t))) t := by
  let ev : End F →L[ℝ] F →L[ℝ] F :=
    ((ContinuousLinearMap.apply ℂ F).flip).bilinearRestrictScalars ℝ
  simpa [ev] using ev.hasDerivAt_of_bilinear
    (fun _ => hasDerivAt_exp_smul_const X t) (fun _ => hf)

/-- An infinitesimal identity for a real bilinear map integrates to
equivariance under the corresponding one-parameter groups. -/
private lemma bilinear_exp_equivariant (B : E →L[ℝ] E →L[ℝ] F) (D : End E) (T : End F)
    (h : ∀ x y, T (B x y) = B x (D y) + B (D x) y) (x y : E) (t : ℝ) :
    B (exp (t • D) x) (exp (t • D) y) = exp (t • T) (B x y) := by
  let f (s : ℝ) := B (exp (s • D) x) (exp (s • D) y)
  have hd (s : ℝ) : HasDerivAt f (T (f s)) s := by
    rw [show T (f s) = _ from h _ _]
    exact B.hasDerivAt_of_bilinear (fun _ => hasDerivAt_exp_apply D x s)
      (fun _ => hasDerivAt_exp_apply D y s)
  let g (s : ℝ) := exp (s • (-T)) (f s)
  have hg (s : ℝ) : HasDerivAt g 0 s := by
    convert hasDerivAt_exp_apply_bilinear (-T) (hd s) using 1
    simp
  have heq : g t = g 0 :=
    is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt) (fun s => (hg s).deriv) t 0
  have hi : exp (t • T) * exp (t • (-T)) = (1 : End F) := by
    rw [smul_neg, ← exp_add_of_commute (Commute.refl (t • T)).neg_right, add_neg_cancel, exp_zero]
  have he := congrArg (fun v => exp (t • T) v) heq
  change (exp (t • T) * exp (t • (-T))) (f t) = _ at he
  rw [hi] at he
  simpa [g, f] using he

private lemma bilinear_differentiated (B : E →L[ℝ] E →L[ℝ] F) (D : End E) (T : End F)
    (h : ∀ (t : ℝ) (x y : E), B (exp (t • D) x) (exp (t • D) y) = exp (t • T) (B x y))
    (x y : E) :
    T (B x y) = B x (D y) + B (D x) y := by
  have h₁ := B.hasDerivAt_of_bilinear (fun _ => hasDerivAt_exp_apply D x 0)
    (fun _ => hasDerivAt_exp_apply D y 0)
  have h₂ := hasDerivAt_exp_apply T (B x y) 0
  rw [show (fun t : ℝ => exp (t • T) (B x y)) =
    (fun t : ℝ => B (exp (t • D) x) (exp (t • D) y)) from funext fun t => (h t x y).symm] at h₂
  simpa using h₂.unique h₁

end Exponential

section Components

variable {A : Type*} [NormedRing A]

attribute [local instance 100] LieRing.ofAssociativeRing

private lemma identityComponent_le (M : Subgroup Aˣ) : identityComponent M ≤ M := by
  rintro _ ⟨g, _, rfl⟩
  exact g.property

private lemma identityComponent_mono {M N : Subgroup Aˣ} (h : M ≤ N) :
    identityComponent M ≤ identityComponent N := by
  rintro _ ⟨g, hg, rfl⟩
  let f : M → N := fun g => ⟨g, h g.property⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have h1 : f 1 = 1 := rfl
  refine ⟨f g, ?_, rfl⟩
  change f g ∈ connectedComponent (1 : N)
  rw [← h1]
  exact hf.mapsTo_connectedComponent (1 : M) hg

private lemma compact_identityComponent (M : Subgroup Aˣ) (hM : IsCompact (M : Set Aˣ)) :
    IsCompact (identityComponent M : Set Aˣ) := by
  let : CompactSpace M := isCompact_iff_compactSpace.mp hM
  exact isClosed_connectedComponent.isCompact.image continuous_subtype_val

variable [NormedAlgebra ℝ A] [CompleteSpace A]

private lemma velocities_mono {M N : Subgroup Aˣ} (h : M ≤ N) : velocities M ⊆ velocities N :=
  fun _ hx t => h (hx t)

private lemma velocities_identityComponent (M : Subgroup Aˣ) :
    velocities (identityComponent M) = velocities M := by
  apply Set.Subset.antisymm (velocities_mono (identityComponent_le M))
  intro X hX t
  let Y : velocities M := ⟨t • X, smul_mem_velocities M hX t⟩
  exact ⟨expIn M Y, expIn_mem_identityComponent M Y, rfl⟩

private lemma identityComponent_eq_closure_exp [FiniteDimensional ℝ A]
    (M : Subgroup Aˣ) (hM : IsClosed (M : Set Aˣ)) :
    identityComponent M = Subgroup.closure (expUnit '' velocities M) := by
  rw [identityComponent, ← exponentialSubgroup_eq_identityComponent M hM, exponentialSubgroup,
    MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨X, rfl⟩, rfl⟩
    exact ⟨X, X.property, rfl⟩
  · rintro ⟨X, hX, rfl⟩
    exact ⟨expIn M ⟨X, hX⟩, ⟨⟨X, hX⟩, rfl⟩, rfl⟩

/-- Infinitesimal directions spanning the ambient Lie algebra give
a product neighborhood in the ambient matrix subgroup. -/
private lemma product_mem_nhds [FiniteDimensional ℝ A]
    (M K T : Subgroup Aˣ) (hM : IsClosed (M : Set Aˣ)) (hK : IsClosed (K : Set Aˣ))
    (hT : IsClosed (T : Set Aˣ)) (hKM : K ≤ M) (hTM : T ≤ M)
    (hsum : ∀ X ∈ velocities M,
      ∃ U ∈ velocities K, ∃ V ∈ velocities T, U + V = X) :
    {g : M | (g : Aˣ) ∈ (K : Set Aˣ) * (T : Set Aˣ)} ∈ 𝓝 (1 : M) := by
  let S := (velocityLieSubalgebra M hM).toSubmodule
  let P := (velocityLieSubalgebra K hK).toSubmodule
  let Q := (velocityLieSubalgebra T hT).toSubmodule
  let a : P × Q →ₗ[ℝ] S := (P.subtype.coprod Q.subtype).codRestrict S fun uv =>
    S.add_mem (velocities_mono hKM uv.1.property) (velocities_mono hTM uv.2.property)
  have ha : Function.Surjective a := by
    intro X
    obtain ⟨U, hU, V, hV, hUV⟩ := hsum X X.property
    exact ⟨(⟨U, hU⟩, ⟨V, hV⟩), Subtype.ext hUV⟩
  obtain ⟨b, hb⟩ := a.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr ha)
  let bL := b.toContinuousLinearMap
  let U : S →L[ℝ] A := P.subtypeL.comp ((ContinuousLinearMap.fst ℝ P Q).comp bL)
  let V : S →L[ℝ] A := Q.subtypeL.comp ((ContinuousLinearMap.snd ℝ P Q).comp bL)
  have hU (x : S) : expUnit (U x) ∈ K := by
    change expUnit ((b x).1 : A) ∈ K
    simpa only [one_smul] using ((b x).1.property : _ ∈ velocities K) (1 : ℝ)
  have hV (x : S) : expUnit (V x) ∈ T := by
    change expUnit ((b x).2 : A) ∈ T
    simpa only [one_smul] using ((b x).2.property : _ ∈ velocities T) (1 : ℝ)
  have hab : U + V = S.subtypeL := by
    ext x
    exact congrArg (fun f : S →ₗ[ℝ] S => (f x : A)) hb
  let F (x : S) : M :=
    ⟨expUnit (U x) * expUnit (V x), M.mul_mem (hKM (hU x)) (hTM (hV x))⟩
  have hF : Continuous F := by
    apply Continuous.subtype_mk
    exact (continuous_expUnit.comp U.continuous).mul (continuous_expUnit.comp V.continuous)
  have hF0 : F 0 = 1 := by
    apply Subtype.ext
    change expUnit (U 0) * expUnit (V 0) = 1
    simp
  let Fval (x : S) : A := exp (U x) * exp (V x)
  have hFval0 : Fval 0 = 1 := by simp [Fval]
  have hdu : HasStrictFDerivAt (fun x : S => exp (U x)) U 0 := by
    have hexp : HasStrictFDerivAt (exp : A → A) (1 : A →L[ℝ] A) (U 0) := by
      simpa only [map_zero] using (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A))
    have he : (1 : A →L[ℝ] A).comp U = U := ContinuousLinearMap.id_comp U
    simpa only [Function.comp_def, he] using hexp.comp 0 U.hasStrictFDerivAt
  have hdv : HasStrictFDerivAt (fun x : S => exp (V x)) V 0 := by
    have hexp : HasStrictFDerivAt (exp : A → A) (1 : A →L[ℝ] A) (V 0) := by
      simpa only [map_zero] using (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A))
    have he : (1 : A →L[ℝ] A).comp V = V := ContinuousLinearMap.id_comp V
    simpa only [Function.comp_def, he] using hexp.comp 0 V.hasStrictFDerivAt
  have hdF : HasStrictFDerivAt Fval S.subtypeL 0 := by
    change HasStrictFDerivAt ((fun x : S => exp (U x)) * (fun x : S => exp (V x))) S.subtypeL 0
    simpa [hab, add_comm] using hdu.mul' hdv
  obtain ⟨C, hC⟩ := S.exists_isCompl
  let p := (S.projectionOnto C hC).toContinuousLinearMap
  have hp (x : S) : p (x : A) = x := Submodule.projectionOnto_apply_left hC x
  have hLog : HasStrictFDerivAt (localLog : A → A) (1 : A →L[ℝ] A) 1 := by
    rw [← hasFDerivAt_localLog_one.fderiv]
    exact analyticAt_localLog_one.hasStrictFDerivAt
  let f (x : S) := p (localLog (Fval x))
  let e := ContinuousLinearEquiv.refl ℝ S
  have hdf : HasStrictFDerivAt f (e : S →L[ℝ] S) 0 := by
    have hLogF := (hFval0 ▸ hLog :
      HasStrictFDerivAt (localLog : A → A) (1 : A →L[ℝ] A) (Fval 0)).comp 0 hdF
    have hcomp := p.hasStrictFDerivAt.comp 0 hLogF
    convert hcomp using 1
    apply ContinuousLinearMap.ext
    intro x
    change x = p (x : A)
    exact (hp x).symm
  have hf0 : f 0 = 0 := by simp [f, hFval0]
  have hLocal : ∀ᶠ g : M in 𝓝 1, expUnit (p (localLog ((g : Aˣ) : A)) : A) = (g : Aˣ) := by
    have hv : Tendsto (fun g : M => (g : Aˣ)) (𝓝 1) (𝓝 1) :=
      continuous_subtype_val.continuousAt
    filter_upwards [eventually_localLog_mem_velocities M hM,
      hv.eventually eventually_expUnit_localLog] with g hg he
    exact (congrArg (fun X : S => expUnit (X : A))
      (hp ⟨localLog ((g : Aˣ) : A), hg⟩)).trans he
  have hFT : Tendsto F (𝓝 0) (𝓝 1) := by
    simpa only [hF0] using (hF.continuousAt (x := (0 : S))).tendsto
  have hfF : ∀ᶠ x in 𝓝 (0 : S), expUnit (f x : A) = (F x : Aˣ) :=
    hFT.eventually hLocal
  let i := hdf.localInverse f e 0
  have hi : ∀ᶠ y in 𝓝 (0 : S), f (i y) = y := by
    simpa only [hf0] using hdf.eventually_right_inverse
  have hit : Tendsto i (𝓝 0) (𝓝 0) := by
    have hi0 : i 0 = 0 := by simpa only [hf0] using hdf.localInverse_apply_image
    have hc : ContinuousAt i 0 := by simpa only [hf0] using hdf.localInverse_continuousAt
    simpa only [hi0] using hc.tendsto
  let l (g : M) := p (localLog ((g : Aˣ) : A))
  have hl : Tendsto l (𝓝 1) (𝓝 0) := by
    have hc : ContinuousAt (fun g : M => ((g : Aˣ) : A)) 1 :=
      (Units.continuous_val.comp continuous_subtype_val).continuousAt
    have hlog : ContinuousAt (localLog : A → A) (((1 : M) : Aˣ) : A) :=
      hasFDerivAt_localLog_one.continuousAt
    have h₁ : ContinuousAt (fun g : M => localLog ((g : Aˣ) : A)) 1 :=
      hlog.comp' (f := fun g : M => ((g : Aˣ) : A)) hc
    have hpl : ContinuousAt l (1 : M) := p.continuous.continuousAt.comp' h₁
    have hl1 : l 1 = 0 := by simp [l]
    simpa only [hl1] using hpl.tendsto
  filter_upwards [hLocal, hl.eventually hi, (hit.comp hl).eventually hfF] with g hg hgi hgF
  refine Set.mem_mul.mpr ⟨expUnit (U (i (l g))), hU _, expUnit (V (i (l g))), hV _, ?_⟩
  change (F (i (l g)) : Aˣ) = (g : Aˣ)
  change expUnit (f (i (l g)) : A) = (F (i (l g)) : Aˣ) at hgF
  rw [← hgF]
  exact (congrArg (fun x : S => expUnit (x : A)) hgi).trans hg

/-- A compact subgroup times a closed subgroup is closed. If the
product contains an identity neighborhood, its translates make it
open as well, so it contains the identity component. -/
private lemma identityComponent_subset_product [FiniteDimensional ℝ A]
    (M K T : Subgroup Aˣ) (hM : IsClosed (M : Set Aˣ)) (hK : IsCompact (K : Set Aˣ))
    (hT : IsClosed (T : Set Aˣ)) (hKM : K ≤ M) (hTM : T ≤ M)
    (hsum : ∀ X ∈ velocities M,
      ∃ U ∈ velocities K, ∃ V ∈ velocities T, U + V = X) :
    (identityComponent M : Set Aˣ) ⊆ (K : Set Aˣ) * (T : Set Aˣ) := by
  let W := (fun g : M => (g : Aˣ)) ⁻¹' ((K : Set Aˣ) * (T : Set Aˣ))
  have hn : W ∈ 𝓝 (1 : M) := product_mem_nhds M K T hM hK.isClosed hT hKM hTM hsum
  have hcl : IsClopen W := by
    refine ⟨(hT.mul_left_of_isCompact hK).preimage continuous_subtype_val, ?_⟩
    refine isOpen_iff_mem_nhds.mpr fun g hg => ?_
    obtain ⟨k, hk, t, ht, hkt⟩ := Set.mem_mul.mp hg
    let k' : M := ⟨k, hKM hk⟩
    let t' : M := ⟨t, hTM ht⟩
    have he : k' * t' = g := Subtype.ext hkt
    let f (x : M) := k'⁻¹ * x * t'⁻¹
    have hf : Continuous f := by
      exact (continuous_const.mul continuous_id).mul continuous_const
    have hfg : f g = 1 := by rw [← he]; simp [f, ← mul_assoc]
    have hft : Tendsto f (𝓝 g) (𝓝 1) := by simpa only [hfg] using (hf.continuousAt (x := g)).tendsto
    filter_upwards [hft.eventually hn] with x hx
    obtain ⟨k₁, hk₁, t₁, ht₁, hkt₁⟩ := Set.mem_mul.mp hx
    refine Set.mem_mul.mpr ⟨k * k₁, K.mul_mem hk hk₁, t₁ * t, T.mul_mem ht₁ ht, ?_⟩
    calc
      (k * k₁) * (t₁ * t) = k * (k₁ * t₁) * t := by simp [mul_assoc]
      _ = k * (k⁻¹ * (x : Aˣ) * t⁻¹) * t := by rw [hkt₁]; rfl
      _ = x := by simp [mul_assoc, ← mul_assoc k k⁻¹]
  have h1 : (1 : M) ∈ W := Set.mem_mul.mpr ⟨1, K.one_mem, 1, T.one_mem, one_mul 1⟩
  rintro g ⟨x, hx, rfl⟩
  exact hcl.connectedComponent_subset h1 hx

end Components

section LieAlgebra

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  [c : InnerProductSpace.Core ℂ L]

attribute [local instance] realLieAlgebra InnerProductSpace.Core.toNormedAddCommGroup
  InnerProductSpace.Core.toNormedSpace

local instance : NormedSpace ℝ L := NormedSpace.restrictScalars ℝ ℂ L
local instance : NormedAlgebra ℝ (End L) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ (End L) := NormedAlgebra.restrictScalars ℚ ℝ _

attribute [local instance 100] LieRing.ofAssociativeRing

private def bracketMap : L →L[ℝ] L →L[ℝ] L :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp (LieAlgebra.ad ℝ L).toLinearMap)

private lemma bracketMap_apply (x y : L) : bracketMap x y = ⁅x, y⁆ := rfl

private def hermitianMap (τ : ConjugateMap L) : L →L[ℝ] L →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun v := LinearMap.toContinuousLinearMap
        { toFun w := hermitian τ v w
          map_add' := map_add (hermitian τ v)
          map_smul' := fun r w => by
            change hermitian τ v ((r : ℂ) • w) = (r : ℂ) • hermitian τ v w
            rw [map_smulₛₗ, Complex.conj_ofReal] }
      map_add' := fun v w => by
        ext x
        exact DFunLike.congr_fun (map_add (hermitian τ) v w) x
      map_smul' := fun r v => by
        ext x
        exact DFunLike.congr_fun (map_smul (hermitian τ) (r : ℂ) v) x }

private lemma hermitianMap_apply (τ : ConjugateMap L) (v w : L) :
    hermitianMap τ v w = hermitian τ v w := rfl

local notation "Aut" => automorphisms (fun v w : L => ⁅v, w⁆)
local notation "AutH" τ => hermitianAutomorphisms (fun v w : L => ⁅v, w⁆)
  (fun v w => hermitian τ v w)

private lemma automorphisms_closed : IsClosed (Aut : Set (End L)ˣ) := by
  have h : (Aut : Set (End L)ˣ) =
      ⋂ (x : L) (y : L), {g | g.val ⁅x, y⁆ = bracketMap (g.val x) (g.val y)} := by
    ext g
    simp [automorphisms, bracketMap_apply]
  rw [h]
  refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq ?_ ?_
  · exact (ContinuousLinearMap.apply ℂ L _).continuous.comp Units.continuous_val
  · exact bracketMap.continuous₂.comp₂
      ((ContinuousLinearMap.apply ℂ L _).continuous.comp Units.continuous_val)
      ((ContinuousLinearMap.apply ℂ L _).continuous.comp Units.continuous_val)

private lemma hermitian_automorphisms_closed (τ : ConjugateMap L) :
    IsClosed (AutH τ : Set (End L)ˣ) := by
  have h : (AutH τ : Set (End L)ˣ) = (Aut : Set (End L)ˣ) ∩
      ⋂ (x : L) (y : L), {g | hermitianMap τ (g.val x) (g.val y) = hermitian τ x y} := by
    ext g
    simp [hermitianAutomorphisms, hermitianMap_apply]
  rw [h]
  refine automorphisms_closed.inter (isClosed_iInter fun x => isClosed_iInter fun y =>
    isClosed_eq ?_ continuous_const)
  exact (hermitianMap τ).continuous₂.comp₂
    ((ContinuousLinearMap.apply ℂ L _).continuous.comp Units.continuous_val)
    ((ContinuousLinearMap.apply ℂ L _).continuous.comp Units.continuous_val)

private lemma mem_velocities_automorphisms (D : End L) :
    D ∈ velocities Aut ↔ ∀ x y : L, D ⁅x, y⁆ = ⁅x, D y⁆ + ⁅D x, y⁆ := by
  constructor
  · intro h x y
    have heq := bilinear_differentiated bracketMap D D
      (fun t v w => by simpa only [bracketMap_apply, coe_expUnit] using (h t v w).symm) x y
    simpa only [bracketMap_apply] using heq
  · intro h t v w
    simpa only [bracketMap_apply, coe_expUnit] using
      (bilinear_exp_equivariant bracketMap D D
        (fun x y => by simpa only [bracketMap_apply] using h x y) v w t).symm

private lemma adjointEnd_apply (z x : L) : adjointEnd z x = ⁅z, x⁆ := rfl

private lemma velocities_automorphisms_eq
    (hss : SolvableRadical.IsSemisimple_value ℂ L) :
    velocities Aut = Set.range (adjointEnd (L := L)) := by
  ext D
  rw [mem_velocities_automorphisms]
  constructor
  · intro h
    let d : LieDerivation ℂ L L :=
      { toLinearMap := D.toLinearMap
        leibniz' := fun x y => by
          change D ⁅x, y⁆ = ⁅x, D y⁆ - ⁅y, D x⁆
          rw [h, sub_eq_add_neg, lie_skew (D x) y] }
    obtain ⟨z, hz⟩ := (adjoint_bijective ℂ L hss).2 d
    exact ⟨z, ContinuousLinearMap.ext fun x => by
      have he : adjoint ℂ L z x = D x :=
        congrArg (fun (D : LieDerivation ℂ L L) => D x) hz
      simpa only [adjointEnd_apply, adjoint_apply] using he⟩
  · rintro ⟨z, rfl⟩ x y
    simpa only [adjointEnd_apply, add_comm] using leibniz_lie z x y

private lemma adjointEnd_injective (hss : SolvableRadical.IsSemisimple_value ℂ L) :
    Function.Injective (adjointEnd (L := L)) := by
  intro x y h
  apply (adjoint_bijective ℂ L hss).1
  ext z
  simpa only [adjointEnd_apply, adjoint_apply] using DFunLike.congr_fun h z

private lemma mem_velocities_hermitian_automorphisms (τ : ConjugateMap L) (D : End L) :
    D ∈ velocities (AutH τ) ↔
      D ∈ velocities Aut ∧ ∀ x y, hermitian τ x (D y) + hermitian τ (D x) y = 0 := by
  constructor
  · intro h
    refine ⟨fun t => (h t).1, fun x y => ?_⟩
    have heq (t : ℝ) (v w : L) :
        hermitianMap τ (exp (t • D) v) (exp (t • D) w) =
          exp (t • (0 : End ℂ)) (hermitianMap τ v w) := by
      simpa only [smul_zero, exp_zero, one_apply_eq_self, hermitianMap_apply, coe_expUnit] using (h t).2 v w
    simpa only [hermitianMap_apply, zero_apply] using
      (bilinear_differentiated (hermitianMap τ) D 0 heq x y).symm
  · rintro ⟨h, hs⟩ t
    refine ⟨h t, fun x y => ?_⟩
    simpa only [smul_zero, exp_zero, one_apply_eq_self, hermitianMap_apply, coe_expUnit] using
      bilinear_exp_equivariant (hermitianMap τ) D 0 (fun v w => (hs v w).symm) x y t

omit [FiniteDimensional ℂ L] c in
private lemma hermitian_apply (τ : ConjugateMap L) (x y : L) :
    hermitian τ x y = -killingForm ℂ L x (τ y) := rfl

private lemma adjoint_hermitian (τ : ConjugateMap L) (hτ : PreservesBracket τ)
    (hττ : Function.Involutive τ) (z x y : L) :
    hermitian τ (adjointEnd z x) y = -hermitian τ x (adjointEnd (τ z) y) := by
  rw [adjointEnd_apply, adjointEnd_apply, hermitian_apply, hermitian_apply, hτ, hττ]
  exact congrArg Neg.neg (LieModule.traceForm_apply_lie_apply' ℂ L L z x (τ y))

private lemma velocities_hermitian_eq
    (hss : SolvableRadical.IsSemisimple_value ℂ L)
    (τ : ConjugateMap L) (hτ : PreservesBracket τ) (hττ : Function.Involutive τ)
    (hp : HermitianPositive τ) :
    velocities (AutH τ) = compactLieAlgebra τ hτ := by
  ext D
  rw [mem_velocities_hermitian_automorphisms, velocities_automorphisms_eq hss]
  constructor
  · rintro ⟨⟨z, rfl⟩, h⟩
    have hz : adjointEnd z = adjointEnd (τ z) := by
      ext y
      apply sub_eq_zero.mp
      let d := adjointEnd z y - adjointEnd (τ z) y
      by_contra hd
      have hn := hp d hd
      specialize h d y
      rw [adjoint_hermitian τ hτ hττ, ← sub_eq_add_neg, ← map_sub] at h
      rw [show hermitian τ d d = 0 from h, Complex.zero_re] at hn
      exact (lt_irrefl _) hn
    exact ⟨⟨z, (adjointEnd_injective hss hz).symm⟩, rfl⟩
  · rintro ⟨z, rfl⟩
    refine ⟨⟨z, rfl⟩, fun x y => ?_⟩
    rw [adjoint_hermitian τ hτ hττ, (mem_fixed τ hτ z).mp z.property, add_neg_cancel]

private lemma hermitian_automorphisms_compact (τ : ConjugateMap L)
    (hc : ∀ x : L, c.inner x x = hermitian τ x x) : IsCompact (AutH τ : Set (End L)ˣ) := by
  let C := Metric.closedBall (0 : End L) 1
  have hC : IsCompact C := isCompact_closedBall _ _
  have hProd : IsCompact (C ×ˢ (MulOpposite.op '' C)) :=
    hC.prod (hC.image MulOpposite.opHomeomorph.continuous)
  have hBound (g : (End L)ˣ) (hg : g ∈ AutH τ) : g.val ∈ C := by
    rw [Metric.mem_closedBall, dist_zero_right]
    apply g.val.opNorm_le_bound zero_le_one
    intro x
    change Real.sqrt (c.inner (g.val x) (g.val x)).re ≤ 1 * Real.sqrt (c.inner x x).re
    have he : hermitian τ (g.val x) (g.val x) = hermitian τ x x := hg.2 x x
    rw [hc, hc, he, one_mul]
  apply (Units.isClosedEmbedding_embedProduct.isCompact_preimage hProd).of_isClosed_subset
    (hermitian_automorphisms_closed τ)
  intro g hg
  exact ⟨hBound g hg, ⟨(g⁻¹).val, hBound g⁻¹ ((AutH τ).inv_mem hg), rfl⟩⟩

private lemma identityComponent_automorphisms_eq_innerGroup
    (hss : SolvableRadical.IsSemisimple_value ℂ L) :
    identityComponent Aut = innerGroup := by
  rw [identityComponent_eq_closure_exp Aut automorphisms_closed, velocities_automorphisms_eq hss]
  exact congrArg Subgroup.closure (Set.range_comp' expUnit adjointEnd).symm

omit [FiniteDimensional ℂ L] in
private lemma lie_mem_borel (H : LieSubalgebra ℂ L) (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ)
    {x y : L} (hx : x ∈ borel H φ) (hy : y ∈ borel H φ) : ⁅x, y⁆ ∈ borel H φ := by
  let W : Option (PositiveRoot H φ) → Submodule ℂ L :=
    fun i => i.elim H.toSubmodule (fun a => RootDecomposition.rootSpace_value H a.val)
  have hW : (⨆ i, W i) = borel H φ := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      cases i with
      | none => exact le_sup_left
      | some a => exact (le_iSup (fun b : PositiveRoot H φ => RootDecomposition.rootSpace_value H b.val) a).trans le_sup_right
    · refine sup_le ?_ (iSup_le fun a => ?_)
      · exact le_iSup W none
      · exact le_iSup W (some a)
  change (LieAlgebra.ad ℂ L x) y ∈ borel H φ
  suffices h : Submodule.map₂ (LieAlgebra.ad ℂ L).toLinearMap (borel H φ) (borel H φ)
      ≤ borel H φ from h (Submodule.apply_mem_map₂ _ hx hy)
  rw [← hW, Submodule.map₂_iSup_left]
  refine iSup_le fun i => ?_
  rw [Submodule.map₂_iSup_right]
  refine iSup_le fun j => ?_
  rw [Submodule.map₂_le]
  intro v hv w hw
  change ⁅v, w⁆ ∈ ⨆ i, W i
  rw [hW]
  cases i <;> cases j
  · exact Submodule.mem_sup_left (H.lie_mem hv hw)
  · rename_i a
    rw [(mem_rootSpace H a.val w).mp hw ⟨v, hv⟩]
    exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem a (Submodule.smul_mem _ _ hw))
  · rename_i a
    rw [← lie_skew v w, (mem_rootSpace H a.val v).mp hv ⟨w, hw⟩]
    exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem a (Submodule.neg_mem _
      (Submodule.smul_mem _ _ hv)))
  · rename_i a b
    have hpos : 0 < φ (a.val + b.val) := by
      rw [map_add]
      exact add_pos a.property.2 b.property.2
    have hn : a.val + b.val ≠ 0 := by
      intro h
      rw [h, map_zero] at hpos
      exact (lt_irrefl _) hpos
    have h := rootSpace_bracket H a.val b.val v w hv hw
    by_cases hroot : a.val + b.val ∈ RootDecomposition.rootSet_value H
    · exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem
        (⟨a.val + b.val, hroot, hpos⟩ : PositiveRoot H φ) h)
    · rw [rootSpace_eq_bot_of_not_mem H _ hn hroot, Submodule.mem_bot] at h
      rw [h]
      exact (borel H φ).zero_mem

private lemma map_eq_of_preserves (B : Submodule ℂ L) (g : (End L)ˣ)
    (hg : ∀ x ∈ B, g.val x ∈ B) : B.map g.val.toLinearMap = B := by
  apply Submodule.eq_of_le_of_finrank_le
  · exact Submodule.map_le_iff_le_comap.mpr hg
  · exact (flagMap B g).finrank_eq.ge

private def stabilizer (B : Submodule ℂ L) : Subgroup (End L)ˣ where
  carrier := {g | ∀ x ∈ B, g.val x ∈ B}
  one_mem' := fun _ h => h
  mul_mem' := fun ha hb x hx => ha _ (hb x hx)
  inv_mem' := by
    intro a ha x hx
    have hm : x ∈ B.map a.val.toLinearMap := by rwa [map_eq_of_preserves B a ha]
    obtain ⟨y, hy, rfl⟩ := hm
    have he : a.inv (a.val y) = y := congrArg (fun f : End L => f y) a.inv_val
    exact he.symm ▸ hy

private lemma stabilizer_closed (B : Submodule ℂ L) :
    IsClosed (stabilizer B : Set (End L)ˣ) := by
  have he : (stabilizer B : Set (End L)ˣ) =
      ⋂ x : B, (fun g : (End L)ˣ => g.val (x : L)) ⁻¹' (B : Set L) := by
    ext g
    rw [Set.mem_iInter]
    exact ⟨fun h x => h x x.property, fun h x hx => h ⟨x, hx⟩⟩
  rw [he]
  exact isClosed_iInter fun x => B.closed_of_finiteDimensional.preimage
    ((ContinuousLinearMap.apply ℂ L _).continuous.comp Units.continuous_val)

private lemma exp_preserves_subspace (B : Submodule ℂ L) (D : End L)
    (hD : ∀ x ∈ B, D x ∈ B) : expUnit D ∈ stabilizer B := by
  let P : Subalgebra ℚ (End L) :=
    { carrier := {F | ∀ x ∈ B, F x ∈ B}
      zero_mem' := fun x _ => by simpa only [zero_apply] using B.zero_mem
      add_mem' := fun h₁ h₂ x hx => B.add_mem (h₁ x hx) (h₂ x hx)
      one_mem' := fun _ hx => hx
      mul_mem' := fun h₁ h₂ x hx => h₁ _ (h₂ x hx)
      algebraMap_mem' := fun r x hx => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact B.smul_mem ((r : ℝ) : ℂ) hx }
  have he : (P : Set (End L)) =
      ⋂ x : B, (fun F : End L => F (x : L)) ⁻¹' (B : Set L) := by
    ext f
    rw [Set.mem_iInter]
    exact ⟨fun h x => h x x.property, fun h x hx => h ⟨x, hx⟩⟩
  have hclosed : IsClosed (P : Set (End L)) := by
    rw [he]
    exact isClosed_iInter fun x => B.closed_of_finiteDimensional.preimage
      (ContinuousLinearMap.apply ℂ L (x : L)).continuous
  exact NormedSpace.exp_mem (R := ℚ) hclosed (show D ∈ P from hD)

private lemma continuous_flagMap (B : Submodule ℂ L) : Continuous (flagMap B) := by
  let b := Module.finBasis ℂ B
  let frame (g : (End L)ˣ) : Frame L (Module.finrank ℂ B) :=
    ⟨fun i => g.val (b i : L), b.linearIndependent.map' (g.val.toLinearMap.comp B.subtype)
      (LinearMap.ker_eq_bot.mpr ((unitEquiv g).injective.comp Subtype.val_injective))⟩
  have hframe : Continuous frame := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i =>
      (ContinuousLinearMap.apply ℂ L (b i : L)).continuous.comp Units.continuous_val
  have hs : Continuous (frameSpan : Frame L (Module.finrank ℂ B) → _) :=
    continuous_coinduced_rng
  have he : flagMap B = frameSpan ∘ frame := by
    funext g
    apply Grassmannian.ext
    change B.map g.val.toLinearMap = Submodule.span ℂ (Set.range (fun i => g.val (b i : L)))
    have hb : Submodule.span ℂ (Set.range fun i => B.subtype (b i)) = B := by
      rw [Set.range_comp' (B.subtype : B → L) (b : _ → B), ← Submodule.map_span, b.span_eq]
      simp
    change B.map g.val.toLinearMap =
      Submodule.span ℂ (Set.range fun i => g.val.toLinearMap (B.subtype (b i)))
    rw [Set.range_comp' (g.val.toLinearMap : L → L), ← Submodule.map_span, hb]
  rw [he]
  exact hs.comp hframe

private lemma flagOrbit_identityComponent_eq
    (hss : SolvableRadical.IsSemisimple_value ℂ L)
    (τ : ConjugateMap L) (hτ : PreservesBracket τ) (hττ : Function.Involutive τ)
    (hp : HermitianPositive τ) (hc : ∀ x : L, c.inner x x = hermitian τ x x)
    (H : LieSubalgebra ℂ L) (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ)
    (hsum : (fixed τ hτ).toSubmodule ⊔ borelReal H φ = ⊤) :
    flagOrbit (borel H φ) (identityComponent (AutH τ)) =
      flagOrbit (borel H φ) (identityComponent Aut) := by
  let B := borel H φ
  let K := identityComponent (AutH τ)
  let T := stabilizer B ⊓ Aut
  have hAutH : (AutH τ) ≤ Aut := fun _ h => h.1
  have hK : IsCompact (K : Set (End L)ˣ) :=
    compact_identityComponent (AutH τ) (hermitian_automorphisms_compact τ hc)
  have hT : IsClosed (T : Set (End L)ˣ) :=
    (stabilizer_closed B).inter automorphisms_closed
  have hvelK : velocities K = compactLieAlgebra τ hτ := by
    rw [velocities_identityComponent, velocities_hermitian_eq hss τ hτ hττ hp]
  have hprod := identityComponent_subset_product Aut K T automorphisms_closed hK hT
    ((identityComponent_le (AutH τ)).trans hAutH) inf_le_right
  have hsub : (identityComponent Aut : Set (End L)ˣ) ⊆ (K : Set (End L)ˣ) * (T : Set (End L)ˣ) := by
    apply hprod
    intro D hD
    rw [velocities_automorphisms_eq hss] at hD
    obtain ⟨z, rfl⟩ := hD
    have hz : z ∈ (fixed τ hτ).toSubmodule ⊔ borelReal H φ := by rw [hsum]; trivial
    obtain ⟨u, hu, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
    refine ⟨adjointEnd u, ?_, adjointEnd b, ?_, ?_⟩
    · rw [hvelK]
      exact ⟨⟨u, hu⟩, rfl⟩
    · intro t
      refine ⟨exp_preserves_subspace B (t • adjointEnd b) (fun x hx => ?_), ?_⟩
      · have hb' : b ∈ B := hb
        change (t : ℂ) • ⁅b, x⁆ ∈ B
        exact B.smul_mem _ (lie_mem_borel H φ hb' hx)
      · have h : adjointEnd b ∈ velocities Aut := by
          rw [velocities_automorphisms_eq hss]
          exact ⟨b, rfl⟩
        exact h t
    · ext x
      exact (add_lie u b x).symm
  apply Set.Subset.antisymm (Set.image_mono (identityComponent_mono hAutH))
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨k, hk, t, ht, rfl⟩ := Set.mem_mul.mp (hsub hg)
  refine ⟨k, hk, Grassmannian.ext ?_⟩
  change B.map k.val.toLinearMap = B.map ((k * t).val.toLinearMap)
  rw [show (k * t).val.toLinearMap = k.val.toLinearMap.comp t.val.toLinearMap from rfl,
    Submodule.map_comp, map_eq_of_preserves B t ht.1]

end LieAlgebra

/-- The identity linear equivalence between the two normed spaces transports
the adjoint exponentials and identifies the generated inner groups. -/
theorem canonical_inner_group :
    Specs.LieAlgebrasAndRepresentations.CompactFlagOrbit.canonicalInnerGroupType.{u} := by
  intro L _ _ _ τ hs hp
  let c := hermitianCore τ hs hp
  let : InnerProductSpace.Core ℂ L := c
  let hermitianNorm := c.toNormedAddCommGroup
  let hermitianSpace := InnerProductSpace.Core.toNormedSpace (𝕜 := ℂ) (F := L)
  let : NormedAlgebra ℝ (End L) := NormedAlgebra.restrictScalars ℝ ℂ _
  have hgen (z : L) : (unitEquiv (expUnit (adjointEnd z))).toLinearMap =
      CartanConjugacy.exponentialOperator z := by
    let D := adjointEnd z
    let coordinateNorm : NormedAddCommGroup L :=
      Specs.LieAlgebrasAndRepresentations.RegularSemisimple.algebraNorm
    let coordinateSpace :=
      NormedSpace.induced ℂ L (Fin (Module.finrank ℂ L) → ℂ) (Module.finBasis ℂ L).equivFun
    let coordinateAd : @End L coordinateNorm coordinateSpace :=
      LinearMap.toContinuousLinearMap (LieAlgebra.ad ℂ L z)
    apply LinearMap.ext
    intro x
    exact @exp_apply_of_intertwining L L hermitianNorm hermitianSpace coordinateNorm
      coordinateSpace _ _ (LinearEquiv.refl ℂ L) D coordinateAd (fun _ => rfl) x
  refine ⟨hgen, ?_⟩
  rw [innerGroup, MonoidHom.map_closure, CartanConjugacy.innerAutomorphisms_value]
  congr 1
  ext e
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, hgen z⟩
  · rintro ⟨z, hz⟩
    refine ⟨expUnit (adjointEnd z), ⟨z, rfl⟩, LinearEquiv.ext fun x => ?_⟩
    exact LinearMap.congr_fun ((hgen z).trans hz.symm) x

/-- The connected compact group and the inner group have the same
orbit of a standard flag satisfying the real sum with the compact form. -/
theorem orbit_comparison :
    Specs.LieAlgebrasAndRepresentations.CompactFlagOrbit.orbitComparisonType.{u} := by
  intro L _ _ _ hss τ hτ hττ hs hp
  let c := hermitianCore τ hs hp
  let : InnerProductSpace.Core ℂ L := c
  let := c.toNormedAddCommGroup
  let := InnerProductSpace.Core.toNormedSpace (𝕜 := ℂ) (F := L)
  let : NormedAlgebra ℝ (End L) := NormedAlgebra.restrictScalars ℝ ℂ _
  let G := identityComponent (automorphisms (fun v w : L => ⁅v, w⁆))
  let K := identityComponent (hermitianAutomorphisms (fun v w : L => ⁅v, w⁆)
    (fun v w => hermitian τ v w))
  change G = innerGroup ∧ IsCompact (K : Set (End L)ˣ) ∧
    velocities K = compactLieAlgebra τ hτ ∧ _
  have hc (x : L) : c.inner x x = hermitian τ x x := rfl
  have hG : G = innerGroup := identityComponent_automorphisms_eq_innerGroup hss
  have hK : IsCompact (K : Set (End L)ˣ) :=
    compact_identityComponent _ (hermitian_automorphisms_compact τ hc)
  have hLie : velocities K = compactLieAlgebra τ hτ :=
    (velocities_identityComponent _).trans (velocities_hermitian_eq hss τ hτ hττ hp)
  refine ⟨hG, hK, hLie, fun H _ φ _ hsum => ?_⟩
  have horbit : flagOrbit (borel H φ) K = flagOrbit (borel H φ) G :=
    flagOrbit_identityComponent_eq hss τ hτ hττ hp hc H φ hsum
  rw [hG] at horbit
  exact ⟨horbit, horbit ▸ hK.image (continuous_flagMap (borel H φ))⟩

/-- The inner orbit of the standard Borel is compact in its complex Grassmannian. -/
theorem compact_flag_orbit :
    Specs.LieAlgebrasAndRepresentations.CompactFlagOrbit.compactFlagOrbitType.{u} := by
  intro L _ _ _ hss H hH
  let : Finite (RootDecomposition.rootSet_value H) := (rootSet_finite H hH.1).to_subtype
  obtain ⟨ψ, hψ⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℝ)
    (fun α : RootDecomposition.rootSet_value H => α.val) (fun α => α.property.1)
  obtain ⟨_, _, _, τ, hτ, _, _, _, _, _, _, hττ, _, _, _, _, _, _, hneg, hs, hp, hsum⟩ :=
    CompactConjugation.construction hss H hH ψ (fun α hα => hψ ⟨α, hα⟩)
  obtain ⟨hG, hK, hLie, horbit⟩ := orbit_comparison hss τ hτ hττ hs hp
  exact ⟨τ, hτ, hττ, hneg, hs, hp, hG, hK, hLie,
    fun φ hφ => ⟨hsum φ hφ, horbit H hH φ hφ (hsum φ hφ)⟩⟩

end LieAlgebrasAndRepresentations.CompactFlagOrbit
