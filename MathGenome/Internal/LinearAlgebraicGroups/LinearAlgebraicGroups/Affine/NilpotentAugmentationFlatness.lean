import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.NilpotentAugmentationFlatness
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
import Mathlib.LinearAlgebra.TensorProduct.Basis

open CategoryTheory Algebra Bialgebra WithConv
open scoped TensorProduct

universe u v

namespace LinearAlgebraicGroups

noncomputable section

section NilpotentIdeal

variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

private lemma eq_bot_of_le_smul_of_nilpotent {I : Ideal R} (hI : IsNilpotent I)
    (P : Submodule R M) (hP : P ≤ I • P) : P = ⊥ := by
  obtain ⟨n, hn⟩ := hI
  have hpow (m : ℕ) : P ≤ I ^ m • P := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', Submodule.mul_smul]
      exact hP.trans (Submodule.smul_mono le_rfl ih)
  simpa [hn] using hpow n

private lemma surjective_of_sup_smul_eq_top {I : Ideal R} (hI : IsNilpotent I)
    (F : M →ₗ[R] N) (hF : LinearMap.range F ⊔ I • (⊤ : Submodule R N) = ⊤) :
    Function.Surjective F := by
  let P := LinearMap.range F
  have hQ : (⊤ : Submodule R (N ⧸ P)) ≤ I • (⊤ : Submodule R (N ⧸ P)) := by
    have h := congrArg (Submodule.map P.mkQ) hF
    change (P ⊔ I • (⊤ : Submodule R N)).map P.mkQ = _ at h
    have hself : P.map P.mkQ = ⊥ := by
      apply eq_bot_iff.mpr
      rintro _ ⟨y, hy, rfl⟩
      simpa using hy
    rw [Submodule.map_sup, hself, bot_sup_eq,
      Submodule.map_smul'', Submodule.map_top, P.range_mkQ] at h
    exact h.ge
  have hz := eq_bot_of_le_smul_of_nilpotent hI (⊤ : Submodule R (N ⧸ P)) hQ
  apply LinearMap.range_eq_top.mp
  have hz' (x : N ⧸ P) : x = 0 := by
    have hx : x ∈ (⊥ : Submodule R (N ⧸ P)) := hz ▸ Submodule.mem_top
    simpa using hx
  exact Submodule.Quotient.subsingleton_iff.mp ⟨fun x y => (hz' x).trans (hz' y).symm⟩

variable (I : Ideal R) (ι : Type*)

private abbrev reduceCoefficients : (ι →₀ R) →ₗ[R] (ι →₀ (R ⧸ I)) :=
  Finsupp.mapRange.linearMap (Algebra.linearMap R (R ⧸ I))

private lemma reduceCoefficients_surjective :
    Function.Surjective (reduceCoefficients I ι) :=
  Finsupp.mapRange_surjective _ (map_zero _) (Ideal.Quotient.mk_surjective (I := I))

private lemma ker_reduceCoefficients :
    LinearMap.ker (reduceCoefficients I ι) = I • (⊤ : Submodule R (ι →₀ R)) := by
  classical
  refine le_antisymm ?_ ?_
  · intro x hx
    have hx' (i : ι) : x i ∈ I := by
      have h := congrArg (fun y : ι →₀ (R ⧸ I) => y i) (LinearMap.mem_ker.mp hx)
      exact Ideal.Quotient.eq_zero_iff_mem.mp h
    rw [← Finsupp.sum_single x]
    apply Submodule.sum_mem
    intro i _
    rw [← Finsupp.smul_single_one]
    exact Submodule.smul_mem_smul (hx' i) (Submodule.mem_top)
  · refine Submodule.smul_le.mpr ?_
    intro a ha x _
    rw [LinearMap.mem_ker, map_smul]
    change (Ideal.Quotient.mk I a) • (reduceCoefficients I ι x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_smul]

/-- Reduction modulo a nilpotent ideal detects invertibility on arbitrary free modules. -/
private lemma injective_of_reduceCoefficients (hI : IsNilpotent I)
    (F : (ι →₀ R) →ₗ[R] (ι →₀ R)) (G : (ι →₀ (R ⧸ I)) →ₗ[R] (ι →₀ (R ⧸ I)))
    (hG : Function.Bijective G)
    (hFG : (reduceCoefficients I ι).comp F = G.comp (reduceCoefficients I ι)) :
    Function.Injective F := by
  let q := reduceCoefficients I ι
  have hq := reduceCoefficients_surjective I ι
  have hk := ker_reduceCoefficients I ι
  change LinearMap.ker q = _ at hk
  have hGt : LinearMap.range (G.comp q) = ⊤ :=
    LinearMap.range_eq_top.mpr (hG.surjective.comp hq)
  have hsurj : Function.Surjective F := by
    apply surjective_of_sup_smul_eq_top hI F
    rw [← hk, ← Submodule.comap_map_eq, ← LinearMap.range_comp, hFG,
      hGt, Submodule.comap_top]
  classical
  let s : (ι →₀ R) →ₗ[R] (ι →₀ R) :=
    (Finsupp.basisSingleOne : Module.Basis ι R (ι →₀ R)).constr R
      (fun i => (hsurj (Finsupp.single i 1)).choose)
  have hs : F.comp s = LinearMap.id := by
    apply (Finsupp.basisSingleOne : Module.Basis ι R (ι →₀ R)).ext
    intro i
    rw [LinearMap.comp_apply]
    dsimp only [s]
    rw [Module.Basis.constr_basis]
    exact (hsurj (Finsupp.single i 1)).choose_spec
  -- Project onto the kernel. Reduction kills the kernel, so applying
  -- this projection shows that the kernel equals its multiple by the ideal.
  let P : (ι →₀ R) →ₗ[R] (ι →₀ R) := LinearMap.id - s.comp F
  have hP : LinearMap.range P ≤ LinearMap.ker F := by
    rintro _ ⟨x, rfl⟩
    have hs' := LinearMap.congr_fun hs (F x)
    change F (s (F x)) = F x at hs'
    simp [P, hs']
  have hK : LinearMap.ker F ≤ LinearMap.ker q := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    apply hG.injective
    have h := LinearMap.congr_fun hFG x
    change q (F x) = G (q x) at h
    simpa [hx] using h.symm
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_of_le_smul_of_nilpotent hI
  intro x hx
  have hx' : x ∈ I • (⊤ : Submodule R (ι →₀ R)) := hk ▸ hK hx
  have hpx : P x = x := by simp [P, LinearMap.mem_ker.mp hx]
  have hm : P x ∈ (I • (⊤ : Submodule R (ι →₀ R))).map P := ⟨x, hx', rfl⟩
  rw [Submodule.map_smul'', Submodule.map_top, hpx] at hm
  exact Submodule.smul_mono le_rfl hP hm

end NilpotentIdeal

section HopfCoaction

open Algebra.TensorProduct

variable {k : Type u} [Field k]
variable {D U V : Type u} [CommRing D] [Bialgebra k D]
    [CommRing U] [Algebra k U] [CommRing V] [Algebra k V]

private lemma convolution_tensor (f : D →ₐ[k] U) (g : D →ₐ[k] V) :
    ofConv (toConv (includeLeft.comp f) * toConv (includeRight.comp g)) =
      (Algebra.TensorProduct.map f g).comp (comulAlgHom k D) := by
  apply AlgHom.ext
  intro x
  change (toConv (includeLeft.comp f) * toConv (includeRight.comp g) :
    WithConv (D →ₐ[k] U ⊗[k] V)) x = _
  rw [AlgHom.convMul_apply, AlgHom.comp_apply, comulAlgHom_apply]
  congr 1
  apply Algebra.TensorProduct.ext'
  intro a b
  simp [tmul_mul_tmul]

variable (C : HopfAlgebraCategory k)

/-- The shear determined by multiplication in the group represented by a Hopf algebra. -/
private def hopfShear : C ⊗[k] C ≃ₐ[C] C ⊗[k] C := by
  let T := C ⊗[k] C
  letI : Group (WithConv (C →ₐ[k] T)) := convolutionGroup C (CommAlgCat.of k T)
  let p : WithConv (C →ₐ[k] T) := toConv includeLeft
  let q : WithConv (C →ₐ[k] T) := toConv includeRight
  let liftRight := liftEquivRight k C C T
  let t := liftRight (p * q).ofConv
  let s := liftRight (p⁻¹ * q).ofConv
  let post (g : T →ₐ[C] T) : WithConv (C →ₐ[k] T) →* WithConv (C →ₐ[k] T) :=
    { toFun := fun x => toConv ((g.restrictScalars k).comp x.ofConv)
      map_one' := by
        apply WithConv.ofConv_injective
        exact AlgHom.ext (fun x => (g.restrictScalars k).commutes _)
      map_mul' := fun x y => WithConv.ofConv_injective
        (AlgHom.comp_convMul_distrib (g.restrictScalars k) x y) }
  have hp (g : T →ₐ[C] T) : post g p = p := by
    apply WithConv.ofConv_injective
    exact AlgHom.ext (fun x => g.commutes x)
  have ht : post t q = p * q := by
    apply WithConv.ofConv_injective
    exact liftRight.symm_apply_apply (p * q).ofConv
  have hs : post s q = p⁻¹ * q := by
    apply WithConv.ofConv_injective
    exact liftRight.symm_apply_apply (p⁻¹ * q).ofConv
  refine AlgEquiv.ofAlgHom t s ?_ ?_
  · apply liftRight.symm.injective
    change (t.restrictScalars k).comp (post s q).ofConv = q.ofConv
    change (post t (post s q)).ofConv = q.ofConv
    rw [hs, map_mul, map_inv, hp, ht, inv_mul_cancel_left]
  · apply liftRight.symm.injective
    change (s.restrictScalars k).comp (post t q).ofConv = q.ofConv
    change (post s (post t q)).ofConv = q.ofConv
    rw [ht, map_mul, hp, hs, mul_inv_cancel_left]

private lemma hopfShear_one_tmul (x : C) :
    hopfShear C (1 ⊗ₜ[k] x) = comulAlgHom k C x := by
  change Algebra.TensorProduct.lift _ _ (fun _ _ => Commute.all ..) (1 ⊗ₜ[k] x) = _
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  have h := convolution_tensor (AlgHom.id k C) (AlgHom.id k C)
  rw [AlgHom.comp_id, AlgHom.comp_id, Algebra.TensorProduct.map_id, AlgHom.id_comp] at h
  exact DFunLike.congr_fun h x

variable {A B : HopfAlgebraCategory k} (f : A ⟶ B)

private abbrev kernelQuotientMap : B →ₐ[k] B ⧸ Specs.kernelIdeal f :=
  Ideal.Quotient.mkₐ k (Specs.kernelIdeal f)

private lemma kernelQuotientMap_comp :
    (kernelQuotientMap f).comp f.hom.toAlgHom =
      (Algebra.ofId k (B ⧸ Specs.kernelIdeal f)).comp (counitAlgHom k A) := by
  apply AlgHom.ext
  intro a
  let ε := counitAlgHom k A
  let q := kernelQuotientMap f
  have hm : a - algebraMap k A (ε a) ∈ Specs.augmentationIdeal A := by
    change ε (a - algebraMap k A (ε a)) = 0
    rw [map_sub, ε.commutes, algebraMap_self, RingHom.id_apply, sub_self]
  have hz : q (f.hom.toAlgHom (a - algebraMap k A (ε a))) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f.hom.toAlgHom hm)
  change q (f.hom.toAlgHom a) = algebraMap k _ (ε a)
  apply sub_eq_zero.mp
  simpa only [map_sub, AlgHom.commutes] using hz

private abbrev kernelCoaction : B →ₐ[k] B ⊗[k] (B ⧸ Specs.kernelIdeal f) :=
  (Algebra.TensorProduct.map (AlgHom.id k B) (kernelQuotientMap f)).comp (comulAlgHom k B)

private lemma kernelCoaction_comp :
    (kernelCoaction f).comp f.hom.toAlgHom = includeLeft.comp f.hom.toAlgHom := by
  change ((Algebra.TensorProduct.map (AlgHom.id k B) (kernelQuotientMap f)).comp
    (comulAlgHom k B)).comp f.hom.toAlgHom = _
  rw [← convolution_tensor (AlgHom.id k B) (kernelQuotientMap f),
    AlgHom.convMul_comp_bialgHom_distrib _ _ f.hom]
  simp only [AlgHom.comp_id, AlgHom.comp_assoc, kernelQuotientMap_comp]
  have h : toConv ((includeRight : B ⧸ Specs.kernelIdeal f →ₐ[k] _).comp
      ((Algebra.ofId k _).comp (counitAlgHom k A))) =
      (1 : WithConv (A →ₐ[k] B ⊗[k] (B ⧸ Specs.kernelIdeal f))) := by
    apply WithConv.ofConv_injective
    exact AlgHom.ext (fun x => (includeRight : B ⧸ Specs.kernelIdeal f →ₐ[k] _).commutes _)
  rw [h]
  exact congrArg WithConv.ofConv
    (mul_one (toConv (includeLeft.comp f.hom.toAlgHom) :
      WithConv (A →ₐ[k] B ⊗[k] (B ⧸ Specs.kernelIdeal f))))

set_option maxHeartbeats 1000000 in
private lemma kernelCoaction_reduce [ (Specs.kernelIdeal f).IsHopfIdeal k] :
    let C := hopfQuotient B (Specs.kernelIdeal f)
    ((Algebra.TensorProduct.map (kernelQuotientMap f) (AlgHom.id k C)).comp
      (kernelCoaction f)) = (comulAlgHom k C).comp (kernelQuotientMap f) := by
  dsimp only
  rw [← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id, AlgHom.id_comp]
  apply AlgHom.ext
  intro x
  exact (Bialgebra.Quotient.comul_mk (R := k) (Specs.kernelIdeal f) x).symm

end HopfCoaction

open Algebra.TensorProduct

set_option maxHeartbeats 2000000 in
theorem nilpotentAugmentationBasis : Specs.NilpotentAugmentationBasis.{u, v} := by
  intro k hk A B hA hB f hf hnil
  let : Algebra A B := f.hom.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower k A B := IsScalarTower.of_algHom f.hom.toAlgHom
  intro ι b e he
  classical
  let I := Specs.kernelIdeal f
  have : I.IsHopfIdeal k := hopfKernelIdeal k f
  let C := hopfQuotient B I
  let q := kernelQuotientMap f
  let δ := kernelCoaction f
  let U : (ι →₀ A) →ₗ[A] B :=
    (Finsupp.basisSingleOne : Module.Basis ι A (ι →₀ A)).constr A e

  -- The lifts span modulo the extended augmentation ideal.
  -- Nilpotence gives surjectivity even when the basis is infinite.
  have hU : Function.Surjective U := by
    apply surjective_of_sup_smul_eq_top hnil
    let P := LinearMap.range U
    have hspan : (P.restrictScalars k).map q.toLinearMap = ⊤ := by
      apply le_antisymm le_top
      rw [← b.span_eq]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      refine ⟨e i, ⟨Finsupp.single i 1, ?_⟩, he i⟩
      exact Module.Basis.constr_basis (Finsupp.basisSingleOne : Module.Basis ι A (ι →₀ A)) A e i
    apply _root_.eq_top_iff.mpr
    intro x _
    obtain ⟨y, hy, hyx⟩ :
        q x ∈ (P.restrictScalars k).map q.toLinearMap := by rw [hspan]; trivial
    refine Submodule.mem_sup.mpr ⟨y, hy, x - y, ?_, by abel⟩
    rw [Ideal.smul_top_eq_map]
    change x - y ∈ I
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (x - y) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hyx.symm

  have hnilI : IsNilpotent I := by
    obtain ⟨n, hn⟩ := hnil
    refine ⟨n, ?_⟩
    change (Ideal.map f.hom.toAlgHom (Specs.augmentationIdeal A)) ^ n = ⊥
    rw [← Ideal.map_pow, hn]
    exact Ideal.map_bot

  -- Reducing the left factor of the coaction gives comultiplication on C.
  -- On the chosen lifts this is the shear applied to the standard base-changed basis.
  let red := Algebra.TensorProduct.map q (AlgHom.id k C)
  let bB := b.baseChange B
  let bC := b.baseChange C
  let qι := reduceCoefficients I ι
  have hcoord (z : B ⊗[k] C) : qι (bB.repr z) = bC.repr (red z) := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      ext i
      change q (bB.repr (x ⊗ₜ[k] y) i) = bC.repr (red (x ⊗ₜ[k] y)) i
      simp only [red, bB, bC, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Module.Basis.baseChange_repr_tmul]
      exact q.toLinearMap.map_smul _ _
    | add x y hx hy => simp only [map_add, hx, hy]

  let F : (ι →₀ B) →ₗ[B] (ι →₀ B) :=
    (Finsupp.basisSingleOne : Module.Basis ι B (ι →₀ B)).constr B
      (fun i => bB.repr (δ (e i)))
  let EC := bC.repr.symm.trans ((hopfShear C).toLinearEquiv.trans bC.repr)
  let G := EC.toLinearMap.restrictScalars B

  have hFG : qι.comp F = G.comp qι := by
    apply (Finsupp.basisSingleOne : Module.Basis ι B (ι →₀ B)).ext
    intro i
    change qι (F (Finsupp.single i 1)) = G (qι (Finsupp.single i 1))
    have hF : F (Finsupp.single i 1) = bB.repr (δ (e i)) :=
      Module.Basis.constr_basis (Finsupp.basisSingleOne : Module.Basis ι B (ι →₀ B)) B _ i
    have hq : qι (Finsupp.single i 1) = Finsupp.single i 1 := by
      simp [qι, reduceCoefficients]
    rw [hF, hcoord, hq]
    change bC.repr (red (δ (e i))) =
      bC.repr (hopfShear C (bC.repr.symm (Finsupp.single i 1)))
    rw [← bC.repr_self i, LinearEquiv.symm_apply_apply]
    change bC.repr (red (δ (e i))) = bC.repr (hopfShear C (b.baseChange C i))
    rw [Module.Basis.baseChange_apply, hopfShear_one_tmul, ← he i]
    exact congrArg bC.repr (DFunLike.congr_fun (kernelCoaction_reduce f) (e i))

  have hF := injective_of_reduceCoefficients I ι hnilI F G EC.bijective hFG
  -- Applying the coaction to a relation over A gives a relation over B
  -- with coefficients mapped along f. Both maps in this coefficient calculation are injective.
  let T := B ⊗[k] C
  let δA : B →ₗ[A] T :=
    { δ.toLinearMap.toAddMonoidHom with
      map_smul' := fun a x => by
        change δ (a • x) = a • (δ x : T)
        rw [Algebra.smul_def a x, Algebra.smul_def a (δ x : T)]
        change δ (f.hom.toAlgHom a * x) =
          (includeLeft : B →ₐ[k] T) (f.hom.toAlgHom a) * δ x
        rw [map_mul]
        exact congrArg (· * δ x) (DFunLike.congr_fun (kernelCoaction_comp f) a) }
  let fι : (ι →₀ A) →ₗ[A] (ι →₀ B) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A B)
  have hfι : Function.Injective fι := Finsupp.mapRange_injective _ (map_zero _) hf
  have hcomp : (bB.repr.toLinearMap.restrictScalars A).comp (δA.comp U) =
      (F.restrictScalars A).comp fι := by
    apply (Finsupp.basisSingleOne : Module.Basis ι A (ι →₀ A)).ext
    intro i
    have h₁ : U (Finsupp.single i 1) = e i :=
      Module.Basis.constr_basis (Finsupp.basisSingleOne : Module.Basis ι A (ι →₀ A)) A e i
    have h₂ : fι (Finsupp.single i 1) = Finsupp.single i 1 := by
      simp [fι]
    change bB.repr (δ (U (Finsupp.single i 1))) = F (fι (Finsupp.single i 1))
    rw [h₁, h₂]
    exact (Module.Basis.constr_basis
      (Finsupp.basisSingleOne : Module.Basis ι B (ι →₀ B)) B
      (fun j => bB.repr (δ (e j))) i).symm
  have hUinj : Function.Injective U := by
    intro x y hxy
    apply hfι
    apply hF
    have h := congrArg (fun z => bB.repr (δA z)) hxy
    change ((bB.repr.toLinearMap.restrictScalars A).comp (δA.comp U)) x =
      ((bB.repr.toLinearMap.restrictScalars A).comp (δA.comp U)) y at h
    rw [hcomp] at h
    exact h
  let equiv := LinearEquiv.ofBijective U ⟨hUinj, hU⟩
  refine ⟨(Finsupp.basisSingleOne : Module.Basis ι A (ι →₀ A)).map equiv, ?_⟩
  intro i
  rw [Module.Basis.map_apply]
  exact Module.Basis.constr_basis (Finsupp.basisSingleOne : Module.Basis ι A (ι →₀ A)) A e i

theorem nilpotentAugmentationFaithfullyFlat : Specs.NilpotentAugmentationFaithfullyFlat.{u} := by
  intro k hk A B hA hB f hf hnil
  let : Algebra A B := f.hom.toAlgHom.toRingHom.toAlgebra
  let C := B ⧸ Specs.kernelIdeal f
  let b := Module.Free.chooseBasis k C
  have hsurj : Function.Surjective (Ideal.Quotient.mk (Specs.kernelIdeal f)) :=
    Ideal.Quotient.mk_surjective
  let e i := (hsurj (b i)).choose
  obtain ⟨b', _⟩ := nilpotentAugmentationBasis k f hf hnil _ b e
    (fun i => (hsurj (b i)).choose_spec)
  have : Module.Free A B := Module.Free.of_basis b'
  have : Nontrivial B :=
    Function.Surjective.nontrivial (f := counitAlgHom k B)
      (fun a => ⟨algebraMap k B a, (counitAlgHom k B).commutes a⟩)
  infer_instance

end

end LinearAlgebraicGroups
