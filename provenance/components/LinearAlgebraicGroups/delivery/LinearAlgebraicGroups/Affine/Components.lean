import Specs.LinearAlgebraicGroups.Affine.Components
import LinearAlgebraicGroups.Affine.GroupSchemes
import LinearAlgebraicGroups.Descent.SemilinearVectorSpaces
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.CategoryTheory.Monoidal.Cartesian.Normal
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.LinearAlgebra.TensorProduct.Basis

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct Topology

universe u

namespace LinearAlgebraicGroups

/-- A Noetherian space has finitely many connected components, because every
irreducible component is contained in a connected component. -/
lemma finiteConnectedComponents (X : Type u) [TopologicalSpace X] [NoetherianSpace X] :
    Finite (ConnectedComponents X) := by
  classical
  let : Finite (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents
  let choosePoint (Z : irreducibleComponents X) : X :=
    Z.property.1.nonempty.some
  have memChoose (Z : irreducibleComponents X) : choosePoint Z ∈ Z.val :=
    Z.property.1.nonempty.some_mem
  refine Finite.of_surjective (fun Z ↦ ConnectedComponents.mk (choosePoint Z)) ?_
  intro C
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  let Z : irreducibleComponents X := ⟨irreducibleComponent x,
    irreducibleComponent_mem_irreducibleComponents x⟩
  exact ⟨Z, ConnectedComponents.coe_eq_coe'.2
    (irreducibleComponent_subset_connectedComponent (memChoose Z))⟩

/-- An étale scheme over a field has the discrete topology, also when the
scheme is only locally of finite type. -/
lemma discreteTopologyOfEtaleOverField {k : Type u} [Field k] {Y : Scheme.{u}}
    (s : Y ⟶ Spec (CommRingCat.of k)) [Etale s] : DiscreteTopology Y := by
  have : IsLocallyArtinian Y := by
    constructor
    intro U
    let f := s.appLE ⊤ U.val (by simp)
    let h := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f).hom
    let : Algebra k Γ(Y, U.val) := h.toAlgebra
    have hf : f.hom.Etale := s.etale_appLE (isAffineOpen_top _) U.property (by simp)
    have hh : h.Etale := RingHom.Etale.respectsIso.2 f.hom
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm hf
    have : Algebra.Etale k Γ(Y, U.val) :=
      RingHom.etale_algebraMap.mp hh
    have : Module.Finite k Γ(Y, U.val) :=
      Algebra.FormallyUnramified.finite_of_free k Γ(Y, U.val)
    exact IsArtinianRing.of_finite k Γ(Y, U.val)
  infer_instance

/-- Étale schemes over a field are separated even when the scheme is not
assumed quasi-compact. The diagonal is open and its target is discrete. -/
lemma separatedOfEtaleOverField {k : Type u} [Field k] {Y : Scheme.{u}}
    (s : Y ⟶ Spec (CommRingCat.of k)) [Etale s] : IsSeparated s := by
  have := discreteTopologyOfEtaleOverField (pullback.snd s s ≫ s)
  refine ⟨⟨?_⟩⟩
  let d := pullback.diagonal s
  exact ⟨d.isOpenEmbedding.isEmbedding, isClosed_discrete _⟩

/-- Purely inseparable scalar extension preserves idempotents, including in
nonreduced algebras. Each idempotent descends because it equals every positive
power of itself. -/
lemma idempotentDescendsPurelyInseparable {k K A : Type u} [Field k] [Field K]
    [Algebra k K] [IsPurelyInseparable k K] [CommRing A] [Algebra k A]
    {e : A ⊗[k] K} (he : IsIdempotentElem e) :
    ∃ e' : A, IsIdempotentElem e' ∧ algebraMap A (A ⊗[k] K) e' = e := by
  obtain ⟨n, hn, e', h⟩ := IsPurelyInseparable.exists_pow_mem_range_tensorProduct e
  rw [he.pow_eq (Nat.ne_of_gt hn)] at h
  refine ⟨e', ?_, h⟩
  apply (Algebra.TensorProduct.includeLeft_injective (S := k) (R := k) (A := A)
    (B := K) (FaithfulSMul.algebraMap_injective k K))
  change algebraMap A (A ⊗[k] K) (e' * e') = algebraMap A (A ⊗[k] K) e'
  rw [map_mul, h, he.eq]

/-- Connected components in a Noetherian space are open and closed. -/
lemma isClopenConnectedComponent (X : Type u) [TopologicalSpace X] [NoetherianSpace X]
    (x : X) : IsClopen (connectedComponent x) := by
  let : Finite (ConnectedComponents X) := finiteConnectedComponents X
  have : T1Space (ConnectedComponents X) := by
    constructor
    intro c
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
    apply ConnectedComponents.isQuotientMap_coe.isClosed_preimage.mp
    rw [connectedComponents_preimage_singleton]
    exact isClosed_connectedComponent
  exact ⟨isClosed_connectedComponent,
    ConnectedComponents.discreteTopology_iff.mp inferInstance x⟩

private lemma coefficient_map {k A B C : Type u} [Field k]
    [CommRing A] [CommRing B] [CommRing C] [Algebra k A] [Algebra k B] [Algebra k C]
    {I : Type u} [DecidableEq I] (b : Module.Basis I k A) (f : B →ₐ[k] C) (x : B ⊗[k] A) (i : I) :
    TensorProduct.equivFinsuppOfBasisRight b (Algebra.TensorProduct.map f (AlgHom.id k A) x) i =
      f (TensorProduct.equivFinsuppOfBasisRight b x i) := by
  induction x with
  | tmul x y =>
      simp [Algebra.smul_def, mul_comm]
  | add x y hx hy => simp [Finsupp.add_apply, hx, hy]

private lemma existsSpecialization {k B : Type u} [Field k] [IsAlgClosed k]
    [CommRing B] [Nontrivial B] [Algebra k B] [Algebra.FiniteType k B] :
    Nonempty (B →ₐ[k] k) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  let := Ideal.Quotient.field m
  have := finite_of_finite_type_of_isJacobsonRing k (B ⧸ m)
  let e := AlgEquiv.ofBijective (Algebra.ofId k (B ⧸ m))
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k))
  exact ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m)⟩

/-- An idempotent over an arbitrary extension of an algebraically closed field
that differs from both zero and one specializes to such an idempotent over the
original field. The inverses of two coefficients keep these inequalities under
specialization. -/
lemma existsNontrivialIdempotentOfScalarExtension {k K A : Type u}
    [Field k] [IsAlgClosed k] [Field K] [Algebra k K] [CommRing A] [Algebra k A]
    {e : K ⊗[k] A} (he : IsIdempotentElem e) (he0 : e ≠ 0) (he1 : e ≠ 1) :
    ∃ x : A, IsIdempotentElem x ∧ x ≠ 0 ∧ x ≠ 1 := by
  classical
  let b := Module.Free.chooseBasis k A
  let c : K ⊗[k] A ≃ₗ[k] _ := TensorProduct.equivFinsuppOfBasisRight b
  let a := c e
  let d := c (1 - e)
  have ha : a ≠ 0 := fun h ↦ he0 (c.injective (h.trans (map_zero c).symm))
  have hd : d ≠ 0 := fun h ↦ he1 (sub_eq_zero.mp
    (c.injective (h.trans (map_zero c).symm))).symm
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra! h
    exact ha (Finsupp.ext h)
  obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
    by_contra! h
    exact hd (Finsupp.ext h)
  let s := insert (a i)⁻¹ (insert (d j)⁻¹ (a.support.image a))
  let B := Algebra.adjoin k (↑s : Set K)
  have : Algebra.FiniteType k B := Algebra.FiniteType.adjoin_of_finite s.finite_toSet
  have : Nontrivial B := ⟨⟨0, 1, fun h ↦ zero_ne_one (congrArg Subtype.val h)⟩⟩
  let v (l : Module.Free.ChooseBasisIndex k A) (hl : l ∈ a.support) : B :=
    ⟨a l, Algebra.subset_adjoin (by
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem a hl)))⟩
  let e' : B ⊗[k] A := ∑ l ∈ a.support.attach, v l.val l.property ⊗ₜ[k] b l.val
  let f := Algebra.TensorProduct.map B.val (AlgHom.id k A)
  have hfe' : f e' = e := by
    simp only [e', map_sum, f, Algebra.TensorProduct.map_tmul, Subalgebra.val_apply,
      v, AlgHom.id_apply]
    rw [Finset.sum_attach (f := fun l ↦ a l ⊗ₜ[k] b l)]
    calc
      _ = c.symm a := (TensorProduct.equivFinsuppOfBasisRight_symm_apply b a).symm
      _ = e := c.symm_apply_apply e
  have hf : Function.Injective f := by
    exact Module.Flat.rTensor_preserves_injective_linearMap B.val.toLinearMap Subtype.val_injective
  have hIdem : IsIdempotentElem e' :=
    hf (by rw [map_mul, hfe', he.eq])
  obtain ⟨sp⟩ := existsSpecialization (k := k) (B := B)
  let g := Algebra.TensorProduct.map sp (AlgHom.id k A)
  have keep (y : B ⊗[k] A) (l : Module.Free.ChooseBasisIndex k A)
      (hy : c (f y) l ≠ 0) (hinv : (c (f y) l)⁻¹ ∈ B) : g y ≠ 0 := by
    let a' := TensorProduct.equivFinsuppOfBasisRight b y l
    let inv : B := ⟨(c (f y) l)⁻¹, hinv⟩
    have hcoe : (a' : K) = c (f y) l := (coefficient_map b B.val y l).symm
    have hmul : a' * inv = 1 := Subtype.ext (by
      change (a' : K) * (c (f y) l)⁻¹ = 1
      rw [hcoe, mul_inv_cancel₀ hy])
    intro hz
    have hzero : sp a' = 0 := by
      rw [← coefficient_map b sp y l]
      change TensorProduct.equivFinsuppOfBasisRight b (g y) l = 0
      simp [hz]
    have h := congrArg sp hmul
    rw [map_mul, hzero, zero_mul, map_one] at h
    exact zero_ne_one h
  have h0 : g e' ≠ 0 := keep e' i (by simpa [hfe'] using hi) (by
    rw [hfe']
    exact Algebra.subset_adjoin (by simp [s, a]))
  have h1 : g (1 - e') ≠ 0 := keep (1 - e') j (by rw [map_sub, map_one, hfe']; exact hj) (by
    rw [map_sub, map_one, hfe']
    exact Algebra.subset_adjoin (by simp [s, d]))
  let l := Algebra.TensorProduct.lid k A
  refine ⟨l (g e'), (hIdem.map g).map l, ?_, ?_⟩
  · intro h
    exact h0 (l.injective (h.trans (map_zero l).symm))
  · intro h
    apply h1
    rw [map_sub, map_one, l.injective (h.trans (map_one l).symm), sub_self]

private lemma preconnectedPrimeSpectrum_iff {A : Type u} [CommRing A] :
    PreconnectedSpace (PrimeSpectrum A) ↔
      ∀ x : A, IsIdempotentElem x → x = 0 ∨ x = 1 := by
  let e := PrimeSpectrum.isIdempotentElemEquivClopens (R := A)
  have bot_val : (e.symm ⊥).val = 0 :=
    congrArg Subtype.val PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot
  have top_val : (e.symm ⊤).val = 1 :=
    congrArg Subtype.val PrimeSpectrum.isIdempotentElemEquivClopens_symm_top
  constructor
  · intro h x hx
    let c : Clopens (PrimeSpectrum A) := e ⟨x, hx⟩
    obtain hc | hc := (isClopen_iff.mp c.isClopen)
    · left
      have hbot : c = ⊥ := SetLike.coe_injective hc
      have := congrArg (fun c ↦ (e.symm c).val) hbot
      simpa only [c, e.symm_apply_apply, bot_val] using this
    · right
      have htop : c = ⊤ := SetLike.coe_injective hc
      have := congrArg (fun c ↦ (e.symm c).val) htop
      simpa only [c, e.symm_apply_apply, top_val] using this
  · intro h
    refine preconnectedSpace_iff_clopen.mpr fun s hs ↦ ?_
    let c : Clopens (PrimeSpectrum A) := ⟨s, hs⟩
    let x := e.symm c
    obtain hx | hx := h x.val x.property
    · left
      have hbot : x = e.symm ⊥ := Subtype.ext (by
        simpa only [bot_val] using hx)
      exact congrArg (fun t : Clopens (PrimeSpectrum A) ↦ (t : Set (PrimeSpectrum A)))
        (e.symm.injective hbot)
    · right
      have htop : x = e.symm ⊤ := Subtype.ext (by
        simpa only [top_val] using hx)
      exact congrArg (fun t : Clopens (PrimeSpectrum A) ↦ (t : Set (PrimeSpectrum A)))
        (e.symm.injective htop)

private lemma connectedPrimeSpectrum_of_injective {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f) [ConnectedSpace (PrimeSpectrum B)] :
    ConnectedSpace (PrimeSpectrum A) := by
  have : Nonempty (PrimeSpectrum A) :=
    (inferInstance : Nonempty (PrimeSpectrum B)).map (PrimeSpectrum.comap f)
  refine { toPreconnectedSpace := preconnectedPrimeSpectrum_iff.mpr (fun x hx ↦ ?_), toNonempty := inferInstance }
  rcases preconnectedPrimeSpectrum_iff.mp (inferInstance : PreconnectedSpace (PrimeSpectrum B))
    (f x) (hx.map f) with h | h
  · exact Or.inl (hf (h.trans (map_zero f).symm))
  · exact Or.inr (hf (h.trans (map_one f).symm))

/-- Over an algebraically closed field, an affine connected scheme stays
connected over every extension field. -/
lemma connectedPrimeSpectrumBaseChangeOfAlgClosed {k K A : Type u}
    [Field k] [IsAlgClosed k] [Field K] [Algebra k K] [CommRing A] [Algebra k A]
    [ConnectedSpace (PrimeSpectrum A)] : ConnectedSpace (PrimeSpectrum (K ⊗[k] A)) := by
  have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  have : Nontrivial (K ⊗[k] A) :=
    (Algebra.TensorProduct.includeRight_injective (A := K) (B := A)
      (algebraMap k K).injective).nontrivial
  refine { toPreconnectedSpace := preconnectedPrimeSpectrum_iff.mpr (fun x hx ↦ ?_), toNonempty := inferInstance }
  by_contra! h
  obtain ⟨y, hy, h0, h1⟩ := existsNontrivialIdempotentOfScalarExtension hx h.1 h.2
  rcases preconnectedPrimeSpectrum_iff.mp (inferInstance : PreconnectedSpace (PrimeSpectrum A))
    y hy with h | h
  · exact h0 h
  · exact h1 h

set_option maxHeartbeats 600000 in
/-- Connectedness after extending to an algebraic closure tests geometric
connectedness for an affine scheme. -/
lemma geometricallyConnectedSpecOfAlgClosure {k A : Type u}
    [Field k] [CommRing A] [Algebra k A] [ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] A))] :
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
  constructor
  apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun Y : Scheme.{u} ↦ ConnectedSpace Y)).mpr
  intro K _ _
  let f : AlgebraicClosure k →ₐ[k] AlgebraicClosure K := IsAlgClosed.lift
  let : Algebra (AlgebraicClosure k) (AlgebraicClosure K) := f.toAlgebra
  let : IsScalarTower k (AlgebraicClosure k) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let e := Algebra.TensorProduct.cancelBaseChange k (AlgebraicClosure k)
    (AlgebraicClosure k) (AlgebraicClosure K) A
  have : ConnectedSpace (PrimeSpectrum ((AlgebraicClosure K) ⊗[AlgebraicClosure k]
      ((AlgebraicClosure k) ⊗[k] A))) :=
    connectedPrimeSpectrumBaseChangeOfAlgClosed
  have : ConnectedSpace (PrimeSpectrum ((AlgebraicClosure K) ⊗[k] A)) :=
    connectedPrimeSpectrum_of_injective e.symm.toRingHom e.symm.injective
  let h : K →ₐ[k] AlgebraicClosure K := IsScalarTower.toAlgHom k K (AlgebraicClosure K)
  let g := Algebra.TensorProduct.map h (AlgHom.id k A)
  have hg : Function.Injective g :=
    Module.Flat.rTensor_preserves_injective_linearMap h.toLinearMap h.injective
  have : ConnectedSpace (PrimeSpectrum (K ⊗[k] A)) :=
    connectedPrimeSpectrum_of_injective g.toRingHom hg
  let E := pullbackSpecIso k K A
  exact ((pullbackSymmetry _ _ ≪≫ E).hom.homeomorph.connectedSpace_iff).mpr
    (inferInstanceAs (ConnectedSpace (PrimeSpectrum (K ⊗[k] A))))

/-- A flat, quasi-compact map with geometrically connected fibers is universal
for factorization through it of maps to separated étale schemes over the base. -/
theorem existsUniqueFactorEtale {X Y E S : Scheme.{u}}
    (q : X ⟶ Y) [Flat q] [QuasiCompact q] [GeometricallyConnected q]
    (s : Y ⟶ S) (e : E ⟶ S) [Etale e] [IsSeparated e]
    (f : X ⟶ E) (hf : f ≫ e = q ≫ s) :
    ∃! g : Y ⟶ E, q ≫ g = f ∧ g ≫ e = s := by
  let a := pullback.fst q q
  let b := pullback.snd q q
  let d := pullback.diagonal e
  let l : pullback q q ⟶ pullback e e := pullback.lift (a ≫ f) (b ≫ f) (by
    change (pullback.fst q q ≫ f) ≫ e = (pullback.snd q q ≫ f) ≫ e
    simp only [Category.assoc, hf, pullback.condition_assoc])
  have hl : Set.range l ⊆ Set.range d := by
    rintro _ ⟨x, rfl⟩
    let z := pullback.diagonal q (a x)
    have hz : a z = a x := by
      change (pullback.diagonal q ≫ a) (a x) = a x
      simp [a]
    have hzd : l z = d (f (a x)) := by
      have w : pullback.diagonal q ≫ l = f ≫ d := by
        apply pullback.hom_ext <;> simp [l, a, b, d]
      exact congrArg (fun m : X ⟶ pullback e e ↦ m (a x)) w
    have hc : IsClopen (l ⁻¹' Set.range d) :=
      ⟨d.isClosedEmbedding.isClosed_range.preimage l.continuous,
        d.isOpenEmbedding.isOpen_range.preimage l.continuous⟩
    have hsub : a ⁻¹' {a x} ⊆ l ⁻¹' Set.range d :=
      (a.isConnected_preimage_singleton (a x)).isPreconnected.subset_isClopen hc
        ⟨z, hz, f (a x), hzd.symm⟩
    exact hsub (show x ∈ a ⁻¹' {a x} from rfl)
  let m := IsOpenImmersion.lift d l hl
  have hm : m ≫ d = l := IsOpenImmersion.lift_fac _ _ _
  have hab : a ≫ f = b ≫ f := by
    have ha : l ≫ pullback.fst e e = m := by rw [← hm]; simp [d]
    have hb : l ≫ pullback.snd e e = m := by rw [← hm]; simp [d]
    simpa [l] using ha.trans hb.symm
  obtain ⟨g, hg⟩ := IsRegularEpi.exists_of_isKernelPair q (IsPullback.of_hasPullback q q) f hab
  refine ⟨g, ⟨hg, ?_⟩, fun n hn ↦ ?_⟩
  · rw [← cancel_epi q, ← Category.assoc, hg, hf]
  · rw [← cancel_epi q, hn.1, hg]

/-- The scalar action on points of any finite group scheme over a field is
continuous when its point set is discrete. -/
theorem componentGaloisOfFinite {k : Type u} [Field k] (Q : Specs.GroupScheme k)
    [IsFinite Q.X.hom] : Specs.ComponentGalois Q := by
  classical
  let K := SeparableClosure k
  let P := Points Q.X (.of k K)
  let : TopologicalSpace P := ⊥
  let act (σ : Gal(K/k)) (p : P) := mapPoints (CommAlgCat.ofHom σ.toAlgHom) p
  let : DiscreteTopology P := ⟨rfl⟩
  change Finite P ∧ Continuous (fun s : Gal(K/k) × P ↦ act s.1 s.2) ∧
    (∀ p, act 1 p = p) ∧ (∀ σ τ p, act (σ * τ) p = act σ (act τ p)) ∧
    ∀ σ p q, act σ (p * q) = act σ p * act σ q
  have hAffine : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  obtain ⟨A, ⟨j⟩⟩ := essImage_algSpec.mpr hAffine
  have hj : IsFinite ((testSpec k).obj A).hom := by
    rw [← Over.w j.hom]
    infer_instance
  have hA : Module.Finite k A.unop := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k A.unop))) at hj
    exact RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp hj)
  let encode : (A.unop →ₐ[k] K) → P := fun p ↦
    (testSpec k).map (CommAlgCat.ofHom p).op ≫ j.hom
  have encode_surj : Function.Surjective encode := by
    intro p
    obtain ⟨a, ha⟩ := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_surjective
      (p ≫ j.inv)
    refine ⟨a.unop.hom, ?_⟩
    change (testSpec k).map a ≫ j.hom = p
    rw [ha]
    simp
  refine ⟨Finite.of_surjective _ encode_surj, continuous_prod_of_discrete_right.mpr ?_,
    ?_, ?_, ?_⟩
  · intro p
    obtain ⟨p, rfl⟩ := encode_surj p
    obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := A.unop)
    let F : IntermediateField k K := IntermediateField.adjoin k (p '' (↑s : Set A.unop))
    have hF : FiniteDimensional k F :=
      IntermediateField.finiteDimensional_adjoin
        (fun x _ ↦ Algebra.IsIntegral.isIntegral x)
    refine continuous_iff_continuousAt.mpr fun σ ↦ ?_
    have hopen : IsOpen ((fun τ : Gal(K/k) ↦ σ⁻¹ * τ) ⁻¹'
        (F.fixingSubgroup : Set Gal(K/k))) :=
      F.fixingSubgroup_isOpen.preimage (continuous_const.mul continuous_id)
    have hmem : σ ∈ (fun τ : Gal(K/k) ↦ σ⁻¹ * τ) ⁻¹'
        (F.fixingSubgroup : Set Gal(K/k)) := by simp
    apply ContinuousAt.congr_of_eventuallyEq
      (f := fun _ : Gal(K/k) ↦ mapPoints (CommAlgCat.ofHom σ.toAlgHom) (encode p))
      continuousAt_const
    filter_upwards [hopen.mem_nhds hmem] with τ hτ
    have hfixed : τ.toAlgHom.comp p = σ.toAlgHom.comp p := by
      apply AlgHom.ext_of_adjoin_eq_top hs
      intro x hx
      have hxF : p x ∈ F := IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
      have h := (F.mem_fixingSubgroup_iff _).mp hτ (p x) hxF
      change σ.symm (τ (p x)) = p x at h
      exact σ.symm.injective (h.trans (σ.symm_apply_apply _).symm)
    change mapPoints (CommAlgCat.ofHom τ.toAlgHom) (encode p) =
      mapPoints (CommAlgCat.ofHom σ.toAlgHom) (encode p)
    have encode_map (ρ : Gal(K/k)) :
        mapPoints (CommAlgCat.ofHom ρ.toAlgHom) (encode p) =
          encode (ρ.toAlgHom.comp p) := by
      change (testSpec k).map (CommAlgCat.ofHom ρ.toAlgHom).op ≫
        (testSpec k).map (CommAlgCat.ofHom p).op ≫ j.hom = _
      rw [← Functor.map_comp_assoc]
      rfl
    rw [encode_map, encode_map, hfixed]
  · intro p
    change (testSpec k).map (𝟙 (op (CommAlgCat.of k K))) ≫ p = p
    simp
  · intro σ τ p
    change (testSpec k).map ((CommAlgCat.ofHom τ.toAlgHom ≫ CommAlgCat.ofHom σ.toAlgHom).op) ≫ p =
      (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op ≫
        (testSpec k).map (CommAlgCat.ofHom τ.toAlgHom).op ≫ p
    simp only [op_comp, Functor.map_comp, Category.assoc]
  · intro σ p q
    exact MonObj.comp_mul _ _ _

private lemma isPullbackWhiskerRight {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (Z : Over S) :
    IsPullback (f ▷ Z).left (fst X Z).left (fst Y Z).left f.left := by
  apply IsPullback.of_right (h₁₂ := (snd Y Z).left) (h₂₂ := Y.hom) (v₁₃ := Z.hom)
  · rw [Over.snd_left, Over.whiskerRight_left_snd, Over.w f]
    exact (IsPullback.of_hasPullback X.hom Z.hom).flip
  · exact Over.whiskerRight_left_fst f
  · exact (IsPullback.of_hasPullback Y.hom Z.hom).flip

private lemma isPullbackWhiskerLeft {S : Scheme.{u}} (Z : Over S) {X Y : Over S} (f : X ⟶ Y) :
    IsPullback (Z ◁ f).left (snd Z X).left (snd Z Y).left f.left := by
  apply IsPullback.of_right (h₁₂ := (fst Z Y).left) (h₂₂ := Y.hom) (v₁₃ := Z.hom)
  · rw [Over.fst_left, Over.whiskerLeft_left_fst, Over.w f]
    exact IsPullback.of_hasPullback Z.hom X.hom
  · exact Over.whiskerLeft_left_snd f
  · exact IsPullback.of_hasPullback Z.hom Y.hom

private lemma tensorHom_property {S : Scheme.{u}} {X Y Z W : Over S} (f : X ⟶ Y) (g : Z ⟶ W)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    (hf : P f.left) (hg : P g.left) : P (f ⊗ₘ g).left := by
  rw [tensorHom_def, Over.comp_left]
  exact P.comp_mem _ _ (P.of_isPullback (isPullbackWhiskerRight f Z).flip hf)
    (P.of_isPullback (isPullbackWhiskerLeft Y g).flip hg)

/-- Products of flat, quasi-compact, universally open maps with geometrically
connected fibers again have those properties. -/
lemma productOfGeometricallyConnectedQuotients {S : Scheme.{u}} {X Y Z W : Over S}
    (f : X ⟶ Y) (g : Z ⟶ W) [Flat f.left] [Flat g.left]
    [QuasiCompact f.left] [QuasiCompact g.left] [UniversallyOpen f.left] [UniversallyOpen g.left]
    [GeometricallyConnected f.left] [GeometricallyConnected g.left] :
    Flat (f ⊗ₘ g).left ∧ QuasiCompact (f ⊗ₘ g).left ∧
      UniversallyOpen (f ⊗ₘ g).left ∧ GeometricallyConnected (f ⊗ₘ g).left := by
  refine ⟨tensorHom_property f g @Flat inferInstance inferInstance,
    tensorHom_property f g @QuasiCompact inferInstance inferInstance,
    tensorHom_property f g @UniversallyOpen inferInstance inferInstance, ?_⟩
  rw [tensorHom_def, Over.comp_left]
  have : GeometricallyConnected (f ▷ Z).left :=
    MorphismProperty.of_isPullback (isPullbackWhiskerRight f Z).flip inferInstance
  have : GeometricallyConnected (Y ◁ g).left :=
    MorphismProperty.of_isPullback (isPullbackWhiskerLeft Y g).flip inferInstance
  have : UniversallyOpen (f ▷ Z).left :=
    MorphismProperty.of_isPullback (isPullbackWhiskerRight f Z).flip inferInstance
  have : UniversallyOpen (Y ◁ g).left :=
    MorphismProperty.of_isPullback (isPullbackWhiskerLeft Y g).flip inferInstance
  exact GeometricallyConnected.comp _ _

section GroupOperations

open scoped CategoryTheory.GrpObj

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]
variable {X Y : C} [GrpObj X] (q : X ⟶ Y)
variable [Epi q] [Epi (q ⊗ₘ q)] [Epi ((q ⊗ₘ q) ⊗ₘ q)]

/-- Group operations descending along an epimorphism and its first two
cartesian powers satisfy the group axioms. -/
@[instance_reducible]
noncomputable def groupObjectOfDescendedOperations (m : Y ⊗ Y ⟶ Y) (v : Y ⟶ Y)
    (hm : (q ⊗ₘ q) ≫ m = μ[X] ≫ q) (hv : q ≫ v = ι[X] ≫ q) : GrpObj Y where
  one := η[X] ≫ q
  mul := m
  inv := v
  one_mul := by
    rw [← cancel_epi (λ_ Y).inv, ← cancel_epi q, leftUnitor_inv_naturality_assoc]
    have h : (𝟙_ C ◁ q) ≫ (η[X] ≫ q) ▷ Y = η[X] ▷ X ≫ (q ⊗ₘ q) := by
      simp only [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom,
        Category.id_comp, Category.comp_id]
    rw [reassoc_of% h, hm]
    simp
  mul_one := by
    rw [← cancel_epi (ρ_ Y).inv, ← cancel_epi q, rightUnitor_inv_naturality_assoc]
    have h : (q ▷ 𝟙_ C) ≫ Y ◁ (η[X] ≫ q) = X ◁ η[X] ≫ (q ⊗ₘ q) := by
      simp only [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom,
        Category.id_comp, Category.comp_id]
    rw [reassoc_of% h, hm]
    simp
  mul_assoc := by
    have hL : ((q ⊗ₘ q) ⊗ₘ q) ≫ m ▷ Y = μ[X] ▷ X ≫ (q ⊗ₘ q) := by
      simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp, hm]
    have hR : (q ⊗ₘ (q ⊗ₘ q)) ≫ Y ◁ m = X ◁ μ[X] ≫ (q ⊗ₘ q) := by
      simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp, hm]
    rw [← cancel_epi ((q ⊗ₘ q) ⊗ₘ q), reassoc_of% hL, hm,
      associator_naturality_assoc, reassoc_of% hR, hm, MonObj.mul_assoc_assoc]
  left_inv := by
    rw [← cancel_epi q, comp_lift_assoc, hv, Category.comp_id]
    have h : lift (ι[X] ≫ q) q = lift ι[X] (𝟙 X) ≫ (q ⊗ₘ q) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [h, Category.assoc, hm]
    simp
  right_inv := by
    rw [← cancel_epi q, comp_lift_assoc, hv, Category.comp_id]
    have h : lift q (ι[X] ≫ q) = lift (𝟙 X) ι[X] ≫ (q ⊗ₘ q) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [h, Category.assoc, hm]
    simp

end GroupOperations

/-- A finite family of elements of a scalar-extended algebra is defined over
a common finite Galois subextension of the given Galois extension. -/
lemma tensorFamilyDefinedOverFiniteGalois {k K A I : Type u} [Field k] [Field K]
    [Algebra k K] [IsGalois k K] [CommRing A] [Algebra k A] [Finite I] (a : I → K ⊗[k] A) :
    ∃ (E : FiniteGaloisIntermediateField k K) (v : I → E ⊗[k] A),
      ∀ i, Algebra.TensorProduct.map E.toIntermediateField.val (AlgHom.id k A) (v i) = a i := by
  classical
  let := Fintype.ofFinite I
  let b := Module.Free.chooseBasis k A
  let c := TensorProduct.equivFinsuppOfBasisRight (M := K) b
  let r (i : I) := c (a i)
  let s : Finset K := Finset.univ.biUnion fun i ↦ (r i).support.image (r i)
  let E := FiniteGaloisIntermediateField.adjoin k (↑s : Set K)
  let w (i : I) (l : (r i).support) : E :=
    ⟨r i l.1, FiniteGaloisIntermediateField.subset_adjoin k _ (by
      change r i l.1 ∈ s
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem (r i) l.2⟩)⟩
  refine ⟨E, fun i ↦ ∑ l ∈ (r i).support.attach, w i l ⊗ₜ[k] b l.1, fun i ↦ ?_⟩
  simp only [map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  change ∑ l ∈ (r i).support.attach, (r i l.1) ⊗ₜ[k] b l.1 = a i
  rw [Finset.sum_attach (f := fun l ↦ r i l ⊗ₜ[k] b l)]
  calc
    _ = c.symm (r i) := (TensorProduct.equivFinsuppOfBasisRight_symm_apply b (r i)).symm
    _ = a i := c.symm_apply_apply _

/-- The full clopen component partition over a separable closure is defined
by idempotents over a single finite Galois extension. -/
lemma componentIdempotentsDefinedOverFiniteGalois {k A : Type u} [Field k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    let K := SeparableClosure k
    let R := K ⊗[k] A
    let I := ConnectedComponents (PrimeSpectrum R)
    ∃ (E : FiniteGaloisIntermediateField k K) (v : I → E ⊗[k] A),
      ∀ i, IsIdempotentElem (v i) ∧
        (PrimeSpectrum.basicOpen
            (Algebra.TensorProduct.map E.toIntermediateField.val (AlgHom.id k A) (v i)) :
          Set (PrimeSpectrum R)) = ConnectedComponents.mk ⁻¹' {i} := by
  classical
  dsimp only
  let K := SeparableClosure k
  let R := K ⊗[k] A
  let I := ConnectedComponents (PrimeSpectrum R)
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  have : Finite I := finiteConnectedComponents (PrimeSpectrum R)
  let U (i : I) : Clopens (PrimeSpectrum R) := ⟨ConnectedComponents.mk ⁻¹' {i}, by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe i
    rw [connectedComponents_preimage_singleton]
    exact isClopenConnectedComponent _ _⟩
  let e (i : I) := (PrimeSpectrum.isIdempotentElemEquivClopens (R := R)).symm (U i)
  obtain ⟨E, v, hv⟩ := tensorFamilyDefinedOverFiniteGalois (fun i ↦ (e i).val)
  let f := Algebra.TensorProduct.map E.toIntermediateField.val (AlgHom.id k A)
  have hf : Function.Injective f :=
    Module.Flat.rTensor_preserves_injective_linearMap E.toIntermediateField.val.toLinearMap
      Subtype.val_injective
  refine ⟨E, v, fun i ↦ ⟨hf (by rw [map_mul, hv i, (e i).property.eq]), ?_⟩⟩
  change (PrimeSpectrum.basicOpen (f (v i)) : Set (PrimeSpectrum R)) = _
  rw [show f (v i) = (e i).val from hv i, PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm]
  rfl

private lemma existsOverFactorEtale {k : Type u} [Field k]
    {X Y E : SchemeOver k} (q : X ⟶ Y) [Flat q.left] [QuasiCompact q.left]
    [GeometricallyConnected q.left] [Etale E.hom] (f : X ⟶ E) :
    ∃ g : Y ⟶ E, q ≫ g = f := by
  have : IsSeparated E.hom := separatedOfEtaleOverField E.hom
  obtain ⟨g, ⟨hfac, hOver⟩, _⟩ := existsUniqueFactorEtale q.left Y.hom E.hom f.left
    (f.w.trans q.w.symm)
  exact ⟨Over.homMk g hOver, Over.OverMorphism.ext hfac⟩

private lemma epiOfFlatGeometricallyConnected {S : Scheme.{u}} {X Y : Over S}
    (q : X ⟶ Y) [Flat q.left] [GeometricallyConnected q.left] : Epi q :=
  (Over.forget S).epi_of_epi_map (Flat.epi_of_flat_of_surjective q.left)

/-- A flat, quasi-compact and universally open quotient with geometrically
connected fibers to an étale scheme inherits the group law from the source. -/
theorem existsComponentGroupStructure {k : Type u} [Field k]
    (G : Specs.GroupScheme k) {Y : SchemeOver k} [Etale Y.hom] (q : G.X ⟶ Y)
    [Flat q.left] [QuasiCompact q.left] [UniversallyOpen q.left]
    [GeometricallyConnected q.left] :
    ∃ S : GrpObj Y, letI := S; IsMonHom q := by
  have h₂ := productOfGeometricallyConnectedQuotients q q
  let q₂ := q ⊗ₘ q
  let _ : Flat q₂.left := h₂.1
  let _ : QuasiCompact q₂.left := h₂.2.1
  let _ : UniversallyOpen q₂.left := h₂.2.2.1
  let _ : GeometricallyConnected q₂.left := h₂.2.2.2
  have h₃ := productOfGeometricallyConnectedQuotients q₂ q
  let _ : Flat (q₂ ⊗ₘ q).left := h₃.1
  let _ : GeometricallyConnected (q₂ ⊗ₘ q).left := h₃.2.2.2
  have : Epi q := epiOfFlatGeometricallyConnected q
  have : Epi q₂ := epiOfFlatGeometricallyConnected q₂
  have : Epi (q₂ ⊗ₘ q) := epiOfFlatGeometricallyConnected (q₂ ⊗ₘ q)
  obtain ⟨m, hm⟩ := existsOverFactorEtale q₂ (μ[G.X] ≫ q)
  obtain ⟨v, hv⟩ := existsOverFactorEtale q (GrpObj.inv (X := G.X) ≫ q)
  let S := groupObjectOfDescendedOperations q m v hm hv
  exact ⟨S, ⟨rfl, hm.symm⟩⟩

/-- The quotient is universal for group homomorphisms to all étale groups. -/
theorem componentGroupUniversal {k : Type u} [Field k] {G Q : Specs.GroupScheme k}
    (q : G ⟶ Q) [Flat q.hom.hom.left] [QuasiCompact q.hom.hom.left]
    [UniversallyOpen q.hom.hom.left] [GeometricallyConnected q.hom.hom.left]
    (E : Specs.GroupScheme k) [Etale E.X.hom] (f : G ⟶ E) :
    ∃! g : Q ⟶ E, q ≫ g = f := by
  obtain ⟨g, hg⟩ := existsOverFactorEtale q.hom.hom f.hom.hom
  have : Epi q.hom.hom := epiOfFlatGeometricallyConnected q.hom.hom
  have h₂ := productOfGeometricallyConnectedQuotients q.hom.hom q.hom.hom
  let _ : Flat (q.hom.hom ⊗ₘ q.hom.hom).left := h₂.1
  let _ : GeometricallyConnected (q.hom.hom ⊗ₘ q.hom.hom).left := h₂.2.2.2
  have : Epi (q.hom.hom ⊗ₘ q.hom.hom) := epiOfFlatGeometricallyConnected _
  have Hone : η[Q.X] ≫ g = η[E.X] := by
    rw [← IsMonHom.one_hom q.hom.hom, Category.assoc, hg, IsMonHom.one_hom]
  have Hmul : μ[Q.X] ≫ g = (g ⊗ₘ g) ≫ μ[E.X] := by
    rw [← cancel_epi (q.hom.hom ⊗ₘ q.hom.hom), ← IsMonHom.mul_hom_assoc, hg, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, hg]
  refine ⟨Grp.homMk'' g Hone Hmul, Grp.hom_ext _ _ hg, fun j hj ↦ ?_⟩
  apply Grp.hom_ext
  rw [← cancel_epi q.hom.hom]
  exact (congrArg (fun h : G ⟶ E ↦ h.hom.hom) hj).trans hg.symm

/-- A rational section of an étale scheme over a field is open and closed. -/
lemma etaleRationalPointImmersions {k : Type u} [Field k] {Y : Scheme.{u}}
    (s : Y ⟶ Spec (CommRingCat.of k)) [Etale s]
    (p : Spec (CommRingCat.of k) ⟶ Y) (hp : p ≫ s = 𝟙 _) :
    IsOpenImmersion p ∧ IsClosedImmersion p := by
  have hclosed : IsClosedImmersion p := isClosedImmersion_of_comp_eq_id s p hp
  have : Etale (p ≫ s) := by rw [hp]; infer_instance
  have : Etale p := Etale.of_comp p s
  exact ⟨IsOpenImmersion.of_flat_of_mono p, hclosed⟩

/-- Pulling back the identity through a geometrically connected quotient to a
finite étale group gives the identity component, with the full fiber scheme. -/
theorem componentQuotientOfKernel {k : Type u} [Field k] {G Q H : Specs.GroupScheme k}
    (q : G ⟶ Q) (i : H ⟶ G) [IsFinite Q.X.hom] [Etale Q.X.hom]
    [LocallyOfFiniteType G.X.hom]
    [Flat q.hom.hom.left] [QuasiCompact q.hom.hom.left]
    [UniversallyOpen q.hom.hom.left] [GeometricallyConnected q.hom.hom.left]
    (h : IsPullback i.hom.hom (toUnit H.X) q.hom.hom η[Q.X]) :
    Specs.ComponentQuotient Q H q i := by
  let S := Spec (CommRingCat.of k)
  have hk : IsPullback i.hom.hom.left H.X.hom q.hom.hom.left η[Q.X].left :=
    h.map (Over.forget S)
  have hη := etaleRationalPointImmersions Q.X.hom η[Q.X].left (by simp)
  have ho : IsOpenImmersion i.hom.hom.left := MorphismProperty.of_isPullback hk.flip hη.1
  have hc : IsClosedImmersion i.hom.hom.left := MorphismProperty.of_isPullback hk.flip hη.2
  have hg : GeometricallyConnected H.X.hom := MorphismProperty.of_isPullback hk inferInstance
  have : LocallyOfFiniteType (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : LocallyOfFiniteType q.hom.hom.left := locallyOfFiniteType_of_comp _ Q.X.hom
  have : IsLocallyNoetherian Q.X.left := LocallyOfFiniteType.isLocallyNoetherian Q.X.hom
  have hn : Specs.IsNormalSubgroup i := by
    have hN := IsMonHom.Normal.of_isPullback_η q.hom.hom h
    obtain ⟨c, hc⟩ := hN.exists_comp_eq_conj
    refine ⟨c, ?_⟩
    simpa [Specs.subgroupConjugation, GrpObj.conj, MonObj.comp_mul, GrpObj.comp_inv] using hc
  have hid : Set.range i.hom.hom.left = connectedComponent (η[G.X].left
      (Classical.choice (inferInstance : Nonempty S))) := by
    let e := Classical.choice (inferInstance : Nonempty S)
    have hpoint : i.hom.hom.left (η[H.X].left e) = η[G.X].left e := by
      have hOne := congrArg (fun f : (𝟙_ (SchemeOver k)) ⟶ G.X ↦ f.left)
        (IsMonHom.one_hom i.hom.hom)
      exact congrArg (fun f : S ⟶ G.X.left ↦ f e) hOne
    have hm : η[G.X].left e ∈ Set.range i.hom.hom.left := ⟨η[H.X].left e, hpoint⟩
    have : ConnectedSpace H.X.left := GeometricallyConnected.connectedSpace_of_subsingleton H.X.hom
    have hcon : _root_.IsConnected (Set.range i.hom.hom.left) := by
      rw [← Set.image_univ]
      exact isConnected_univ.image _ i.hom.hom.left.continuous.continuousOn
    have hcl : IsClopen (Set.range i.hom.hom.left) :=
      ⟨i.hom.hom.left.isClosedEmbedding.isClosed_range,
        i.hom.hom.left.isOpenEmbedding.isOpen_range⟩
    exact (hcon.subset_connectedComponent hm).antisymm
      (isPreconnected_connectedComponent.subset_isClopen hcl ⟨_, mem_connectedComponent, hm⟩)
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ho, hc, hn, hg, hid, hk, fun E _ f ↦ componentGroupUniversal q E f⟩

open scoped CategoryTheory.GrpObj in
/-- The group kernel is the pullback of the identity section in the category
of schemes over the field. -/
lemma existsComponentKernel {k : Type u} [Field k] {G Q : Specs.GroupScheme k}
    (q : G ⟶ Q) : ∃ (H : Specs.GroupScheme k) (i : H ⟶ G),
    IsPullback i.hom.hom (toUnit H.X) q.hom.hom η[Q.X] := by
  let O := Grp.trivial (SchemeOver k)
  let z : O ⟶ Q := 0
  let H := pullback q z
  refine ⟨H, pullback.fst q z, ?_⟩
  have hp := (IsPullback.of_hasPullback q z).map (Grp.forget (SchemeOver k))
  change IsPullback (pullback.fst q z).hom.hom (pullback.snd q z).hom.hom q.hom.hom
    z.hom.hom at hp
  have hs : (pullback.snd q z).hom.hom = toUnit H.X := toUnit_unique _ _
  have hz : z.hom.hom = η[Q.X] := by
    change toUnit (𝟙_ (SchemeOver k)) ≫ η[Q.X] = η[Q.X]
    simp
  rwa [hs, hz] at hp

private lemma baseChangeMapPullback {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X Y : SchemeOver k} (q : X ⟶ Y) :
    IsPullback ((baseChange k K).map q).left (pullback.fst X.hom (fieldSpecMap k K))
      (pullback.fst Y.hom (fieldSpecMap k K)) q.left := by
  let f := fieldSpecMap k K
  change IsPullback ((Over.pullback f).map q).left (pullback.fst X.hom f)
    (pullback.fst Y.hom f) q.left
  apply IsPullback.of_right (h₁₂ := pullback.snd Y.hom f) (h₂₂ := Y.hom) (v₁₃ := f)
  · simp only [Over.pullback_map_left, pullback.lift_snd, Over.w q]
    exact (IsPullback.of_hasPullback X.hom f).flip
  · simp only [Over.pullback_map_left, pullback.lift_fst]
  · exact (IsPullback.of_hasPullback Y.hom f).flip

private lemma baseChangeKernelSquare {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G Q H : Specs.GroupScheme k} (q : G ⟶ Q) (i : H ⟶ G)
    (h : IsPullback i.hom.hom (toUnit H.X) q.hom.hom η[Q.X]) :
    IsPullback ((groupBaseChange k K).map i).hom.hom
      (toUnit ((groupBaseChange k K).obj H).X)
      ((groupBaseChange k K).map q).hom.hom η[((groupBaseChange k K).obj Q).X] := by
  let F := baseChange k K
  let e := Functor.Monoidal.εIso F
  apply (h.map F).of_iso' (Iso.refl _) (Iso.refl _) e (Iso.refl _)
  · simp [F]
  · apply (cancel_mono e.inv).mp
    simp only [Iso.refl_hom, Category.id_comp]
    exact toUnit_unique _ _
  · simp [F]
  · change e.hom ≫ F.map η[Q.X] = (e.hom ≫ F.map η[Q.X]) ≫ 𝟙 _
    simp

/-- The same quotient and kernel diagram satisfy the component conditions
after extension to any field. -/
theorem componentQuotientAfterBaseChange {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G Q H : Specs.GroupScheme k} (q : G ⟶ Q) (i : H ⟶ G)
    [LocallyOfFiniteType G.X.hom]
    [IsFinite Q.X.hom] [Etale Q.X.hom] [Flat q.hom.hom.left] [QuasiCompact q.hom.hom.left]
    [UniversallyOpen q.hom.hom.left] [GeometricallyConnected q.hom.hom.left]
    (h : IsPullback i.hom.hom (toUnit H.X) q.hom.hom η[Q.X]) :
    Specs.ComponentQuotient ((groupBaseChange k K).obj Q) ((groupBaseChange k K).obj H)
      ((groupBaseChange k K).map q) ((groupBaseChange k K).map i) := by
  let Q' := (groupBaseChange k K).obj Q
  let G' := (groupBaseChange k K).obj G
  let q' := (groupBaseChange k K).map q
  have : LocallyOfFiniteType G'.X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom (fieldSpecMap k K))
    infer_instance
  have : IsFinite Q'.X.hom := by
    change IsFinite (pullback.snd Q.X.hom (fieldSpecMap k K))
    infer_instance
  have : Etale Q'.X.hom := by
    change Etale (pullback.snd Q.X.hom (fieldSpecMap k K))
    infer_instance
  have Hq := (baseChangeMapPullback (K := K) q.hom.hom).flip
  have : Flat q'.hom.hom.left :=
    MorphismProperty.of_isPullback Hq (inferInstance : Flat q.hom.hom.left)
  have : QuasiCompact q'.hom.hom.left :=
    MorphismProperty.of_isPullback Hq (inferInstance : QuasiCompact q.hom.hom.left)
  have : UniversallyOpen q'.hom.hom.left :=
    MorphismProperty.of_isPullback Hq (inferInstance : UniversallyOpen q.hom.hom.left)
  have : GeometricallyConnected q'.hom.hom.left :=
    MorphismProperty.of_isPullback Hq (inferInstance : GeometricallyConnected q.hom.hom.left)
  exact componentQuotientOfKernel q' ((groupBaseChange k K).map i) (baseChangeKernelSquare q i h)

private lemma finiteEtalePointEvaluation {k : Type u} [Field k] [IsSepClosed k]
    (Y : SchemeOver k) [IsFinite Y.hom] [Etale Y.hom]
    (x : Spec (CommRingCat.of k)) :
    Function.Bijective (fun p : Points Y (.of k k) ↦ p.left x) := by
  have hAffine : IsAffine Y.left := isAffine_of_isAffineHom Y.hom
  obtain ⟨A, ⟨j⟩⟩ := essImage_algSpec.mpr hAffine
  have he : Etale ((testSpec k).obj A).hom := by rw [← Over.w j.hom]; infer_instance
  have hA : Algebra.Etale k A.unop := by
    change Etale (Spec.map (CommRingCat.ofHom (algebraMap k A.unop))) at he
    rw [HasRingHomProperty.Spec_iff (P := @Etale)] at he
    exact RingHom.etale_algebraMap.mp he
  let encode : (A.unop →ₐ[k] k) → Points Y (.of k k) := fun a ↦
    (testSpec k).map (CommAlgCat.ofHom a).op ≫ j.hom
  have hsurj : Function.Surjective encode := by
    intro p
    obtain ⟨a, ha⟩ := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_surjective
      (p ≫ j.inv)
    refine ⟨a.unop.hom, ?_⟩
    change (testSpec k).map a ≫ j.hom = p
    rw [ha]
    simp
  let j' := j.hom.left.homeomorph
  let c := Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum k A.unop
  have hc (a : A.unop →ₐ[k] k) : (encode a).left x = j' (c a) := by
    change j.hom.left (Spec.map (CommRingCat.ofHom a.toRingHom) x) = j.hom.left (c a)
    apply congrArg j.hom.left
    change PrimeSpectrum.comap a.toRingHom x = c a
    have hx : x = (⊥ : PrimeSpectrum k) := Subsingleton.elim _ _
    apply PrimeSpectrum.ext
    simp [c, hx, RingHom.ker_eq_comap_bot]
    rfl
  refine ⟨?_, ?_⟩
  · intro p p' h
    obtain ⟨a, rfl⟩ := hsurj p
    obtain ⟨a', rfl⟩ := hsurj p'
    change (encode a).left x = (encode a').left x at h
    rw [hc, hc] at h
    exact congrArg encode (c.injective (j'.injective h))
  · intro y
    obtain ⟨a, ha⟩ := (j'.surjective.comp c.surjective) y
    exact ⟨encode a, (hc a).trans ha⟩

private noncomputable def connectedComponentsEquivOfDiscreteTarget
    {X Y : Scheme.{u}} (q : X ⟶ Y) [GeometricallyConnected q] [DiscreteTopology Y] :
    ConnectedComponents X ≃ Y := by
  have fiber (x : X) : q ⁻¹' {q x} = connectedComponent x := by
    refine ((q.isConnected_preimage_singleton (q x)).subset_connectedComponent rfl).antisymm ?_
    exact isPreconnected_connectedComponent.subset_isClopen
      ((isClopen_discrete {q x}).preimage q.continuous) ⟨x, mem_connectedComponent, rfl⟩
  have same (x y : X) : q x = q y ↔ ConnectedComponents.mk x = ConnectedComponents.mk y := by
    rw [ConnectedComponents.coe_eq_coe', ← fiber y]
    rfl
  let f : ConnectedComponents X → Y := Quotient.lift q
    (fun x y h ↦ (same x y).mpr (Quotient.sound h))
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe y
    exact (same x y).mp h
  · intro y
    obtain ⟨x, rfl⟩ := q.surjective y
    exact ⟨ConnectedComponents.mk x, rfl⟩

private lemma galoisBaseChangeNaturality {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X Y : SchemeOver k} (f : X ⟶ Y) (σ : Gal(K/k)) :
    Specs.galoisBaseChangeMap K X σ ≫ ((baseChange k K).map f).left =
      ((baseChange k K).map f).left ≫ Specs.galoisBaseChangeMap K Y σ := by
  apply pullback.hom_ext
  · simp [Specs.galoisBaseChangeMap, Over.pullback_map_left]
  · let fK := ((baseChange k K).map f).left
    let sx := pullback.snd X.hom (fieldSpecMap k K)
    let sy := pullback.snd Y.hom (fieldSpecMap k K)
    let m := Specs.galoisBaseChangeMap K X σ
    let n := Specs.galoisBaseChangeMap K Y σ
    let a : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) :=
      ((testSpec k).map (CommAlgCat.ofHom σ.symm.toAlgHom).op).left
    have hs : fK ≫ sy = sx := pullback.lift_snd _ _ _
    have hm : m ≫ sx = sx ≫ a := pullback.lift_snd _ _ _
    have hn : n ≫ sy = sy ≫ a := pullback.lift_snd _ _ _
    change (m ≫ fK) ≫ sy = (fK ≫ n) ≫ sy
    calc
      _ = m ≫ sx := by simp only [Category.assoc, hs]
      _ = sx ≫ a := hm
      _ = (fK ≫ sy) ≫ a := congrArg (· ≫ a) hs.symm
      _ = _ := by simp only [Category.assoc, hn]

/-- The scalar action on a rational point after base change is obtained by
changing both its domain and its target by the field automorphism. -/
private lemma existsGaloisBaseChangePoint {k K : Type u} [Field k] [Field K] [Algebra k K]
    (Y : SchemeOver k) (σ : Gal(K/k)) (a : Points ((baseChange k K).obj Y) (.of K K))
    (y : Spec (CommRingCat.of K)) :
    ∃ b : Points ((baseChange k K).obj Y) (.of K K),
      b.left y = Specs.galoisBaseChangeMap K Y σ (a.left y) ∧
      baseChangePoint k K Y (.of K K) b =
        mapPoints (CommAlgCat.ofHom σ.toAlgHom) (baseChangePoint k K Y (.of K K) a) := by
  let S := Spec (CommRingCat.of K)
  let F := fieldSpecMap k K
  let r := (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op
  let r' := (testSpec k).map (CommAlgCat.ofHom σ.symm.toAlgHom).op
  let t : S ⟶ S := r.left
  let t' : S ⟶ S := r'.left
  have hinv : CommAlgCat.ofHom σ.symm.toAlgHom ≫ CommAlgCat.ofHom σ.toAlgHom =
      𝟙 (CommAlgCat.of k K) := by
    ext x
    exact σ.apply_symm_apply x
  have hcomp : r ≫ r' = 𝟙 ((testSpec k).obj (op (CommAlgCat.of k K))) := by
    dsimp only [r, r']
    rw [← Functor.map_comp, ← op_comp, hinv, op_id]
    exact (testSpec k).map_id _
  have ht : t ≫ t' = 𝟙 S :=
    congrArg (fun m : Points ((testSpec k).obj (op (CommAlgCat.of k K))) (.of k K) ↦ m.left) hcomp
  let a₀ : S ⟶ pullback Y.hom F := a.left
  let m := Specs.galoisBaseChangeMap K Y σ
  have ha : a₀ ≫ pullback.snd Y.hom F = 𝟙 S := (Over.w a).trans (Spec.map_id _)
  have hb : (t ≫ a₀ ≫ m) ≫ pullback.snd Y.hom F =
      ((testSpec K).obj (op (CommAlgCat.of K K))).hom := by
    calc
      _ = t ≫ (a₀ ≫ pullback.snd Y.hom F) ≫ t' := by
        have hm : m ≫ pullback.snd Y.hom F = pullback.snd Y.hom F ≫ t' :=
          pullback.lift_snd _ _ _
        simp only [Category.assoc, hm]
      _ = 𝟙 S := by simpa only [ha, Category.id_comp] using ht
      _ = _ := (Spec.map_id _).symm
  let b : Points ((baseChange k K).obj Y) (.of K K) := Over.homMk _ hb
  refine ⟨b, ?_, ?_⟩
  · change m (a₀ (t y)) = m (a₀ y)
    rw [Subsingleton.elim (t y) y]
  · apply Over.OverMorphism.ext
    change (t ≫ a₀ ≫ m) ≫ pullback.fst Y.hom F = t ≫ (a₀ ≫ pullback.fst Y.hom F)
    have hm : m ≫ pullback.fst Y.hom F = pullback.fst Y.hom F :=
      pullback.lift_fst _ _ _
    simp only [Category.assoc, hm]

/-- Over a separably closed field, each point of the finite étale quotient
indexes its connected fiber. -/
theorem componentPointsOfQuotient {k : Type u} [Field k]
    {G Q : Specs.GroupScheme k} (q : G ⟶ Q) [IsFinite Q.X.hom] [Etale Q.X.hom]
    [GeometricallyConnected q.hom.hom.left] : Specs.ComponentPoints q := by
  intro K _ _ _
  let E := (groupBaseChange k K).obj Q
  let X := (groupBaseChange k K).obj G
  let p := (groupBaseChange k K).map q
  change ∃ e : ConnectedComponents X.X.left ≃ Points E.X (.of K K), _
  have : IsFinite E.X.hom := by
    change IsFinite (pullback.snd Q.X.hom (fieldSpecMap k K))
    infer_instance
  have : Etale E.X.hom := by
    change Etale (pullback.snd Q.X.hom (fieldSpecMap k K))
    infer_instance
  have : DiscreteTopology E.X.left := discreteTopologyOfEtaleOverField E.X.hom
  have : GeometricallyConnected p.hom.hom.left :=
    MorphismProperty.of_isPullback (baseChangeMapPullback (K := K) q.hom.hom).flip
      (inferInstance : GeometricallyConnected q.hom.hom.left)
  let y := Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of K)))
  let h := Equiv.ofBijective _ (finiteEtalePointEvaluation E.X y)
  let j := connectedComponentsEquivOfDiscreteTarget p.hom.hom.left
  let e := j.trans h.symm
  have he (x : X.X.left) : (e (ConnectedComponents.mk x)).left y = p.hom.hom.left x := by
    change h (h.symm (j (ConnectedComponents.mk x))) = p.hom.hom.left x
    rw [h.apply_symm_apply]
    rfl
  refine ⟨e, he, ?_, ?_, ?_⟩
  · intro c
    let s := (e c).left
    have hs := etaleRationalPointImmersions E.X.hom s (by
      change (e c).left ≫ E.X.hom = _
      rw [Over.w (e c)]
      exact Spec.map_id _)
    let d := p.hom.hom.left
    have pb := IsPullback.of_hasPullback d s
    refine ⟨MorphismProperty.of_isPullback pb.flip hs.1,
      MorphismProperty.of_isPullback pb.flip hs.2, ?_⟩
    change Set.range (pullback.fst d s) = _
    rw [Scheme.Pullback.range_fst]
    ext x
    change d x ∈ Set.range s ↔ ConnectedComponents.mk x = c
    change p.hom.hom.left x ∈ Set.range s ↔ _
    rw [← he x]
    constructor
    · rintro ⟨z, hz⟩
      have hzy := @Subsingleton.elim (Spec (CommRingCat.of K)) inferInstance z y
      rw [hzy] at hz
      exact e.injective (h.injective hz.symm)
    · intro hx
      rw [hx]
      exact ⟨y, rfl⟩
  · intro z
    let f := p.hom.hom
    let f₂ := f ⊗ₘ f
    have : IsFinite (E.X ⊗ E.X).hom := by
      rw [Over.tensorObj_hom]
      infer_instance
    have : Etale (E.X ⊗ E.X).hom := by
      rw [Over.tensorObj_hom]
      infer_instance
    obtain ⟨a, ha⟩ := (finiteEtalePointEvaluation (E.X ⊗ E.X) y).surjective (f₂.left z)
    change a.left y = f₂.left z at ha
    have hfst : a ≫ fst E.X E.X = e (ConnectedComponents.mk ((fst X.X X.X).left z)) := by
      apply h.injective
      calc
        (fst E.X E.X).left (a.left y) = (f₂ ≫ fst E.X E.X).left z :=
          congrArg (fst E.X E.X).left ha
        _ = (fst X.X X.X ≫ f).left z :=
          congrArg (fun g : X.X ⊗ X.X ⟶ E.X ↦ g.left z) (tensorHom_fst f f)
        _ = (e (ConnectedComponents.mk ((fst X.X X.X).left z))).left y := (he _).symm
    have hsnd : a ≫ snd E.X E.X = e (ConnectedComponents.mk ((snd X.X X.X).left z)) := by
      apply h.injective
      calc
        (snd E.X E.X).left (a.left y) = (f₂ ≫ snd E.X E.X).left z :=
          congrArg (snd E.X E.X).left ha
        _ = (snd X.X X.X ≫ f).left z :=
          congrArg (fun g : X.X ⊗ X.X ⟶ E.X ↦ g.left z) (tensorHom_snd f f)
        _ = (e (ConnectedComponents.mk ((snd X.X X.X).left z))).left y := (he _).symm
    have hmul : e (ConnectedComponents.mk (μ[X.X].left z)) = a ≫ μ[E.X] := by
      apply h.injective
      calc
        (e (ConnectedComponents.mk (μ[X.X].left z))).left y = (μ[X.X] ≫ f).left z := he _
        _ = (f₂ ≫ μ[E.X]).left z :=
          congrArg (fun g : X.X ⊗ X.X ⟶ E.X ↦ g.left z) (IsMonHom.mul_hom f)
        _ = μ[E.X].left (a.left y) := congrArg μ[E.X].left ha.symm
    rw [hmul, ← hfst, ← hsnd, ← MonObj.comp_mul, ← MonObj.mul_eq_mul]
  · let a := e.trans (baseChangePointGroupEquiv K Q (.of K K)).toEquiv
    refine ⟨a, fun _ ↦ rfl, ?_⟩
    intro σ x
    obtain ⟨b, hb, hcompare⟩ := existsGaloisBaseChangePoint Q.X σ (e (ConnectedComponents.mk x)) y
    let m : X.X.left ⟶ X.X.left := Specs.galoisBaseChangeMap K G.X σ
    let n : E.X.left ⟶ E.X.left := Specs.galoisBaseChangeMap K Q.X σ
    let f : X.X.left ⟶ E.X.left := p.hom.hom.left
    have hn : m ≫ f = f ≫ n :=
      galoisBaseChangeNaturality q.hom.hom σ
    have hpt : e (ConnectedComponents.mk (m x)) = b := by
      apply h.injective
      change (e (ConnectedComponents.mk (m x))).left y = b.left y
      have h₁ : f (m x) = n (f x) := congrArg (fun g : X.X.left ⟶ E.X.left ↦ g x) hn
      have h₂ : n (f x) = n ((e (ConnectedComponents.mk x)).left y) := congrArg n (he x).symm
      have h₃ : n ((e (ConnectedComponents.mk x)).left y) = b.left y := hb.symm
      exact (he (m x)).trans (h₁.trans (h₂.trans h₃))
    exact (congrArg (baseChangePoint k K Q.X (.of K K)) hpt).trans hcompare

section SubalgebraDescent

open Descent

variable {k K A : Type u} [Field k] [Field K] [Algebra k K]
  [CommRing A] [Algebra k A]

private noncomputable def subalgebraAction (B : Subalgebra K (K ⊗[k] A))
    (h : ∀ g x, x ∈ B → (SemilinearAction.scalarExtension (k := k) (K := K) A).act g x ∈ B) :
    SemilinearAction k K B := by
  let a := SemilinearAction.scalarExtension (k := k) (K := K) A
  refine
    { act := fun g ↦
        { toFun := fun x ↦ ⟨a.act g x, h g _ x.property⟩
          invFun := fun x ↦ ⟨a.act g⁻¹ x, h g⁻¹ _ x.property⟩
          left_inv := fun x ↦ Subtype.ext (by
            change a.act g⁻¹ (a.act g (x : K ⊗[k] A)) = x
            rw [← a.mul_act, inv_mul_cancel, a.one_act])
          right_inv := fun x ↦ Subtype.ext (by
            change a.act g (a.act g⁻¹ (x : K ⊗[k] A)) = x
            rw [← a.mul_act, mul_inv_cancel, a.one_act])
          map_add' := fun x y ↦ Subtype.ext (map_add (a.act g) (x : K ⊗[k] A) (y : K ⊗[k] A)) }
      one_act := fun x ↦ Subtype.ext (a.one_act x)
      mul_act := fun g h x ↦ Subtype.ext (a.mul_act g h x)
      map_smul := fun g r x ↦ Subtype.ext (a.map_smul g r x) }

set_option maxHeartbeats 650000 in
/-- A stable subalgebra of a scalar extension descends by contracting its
underlying algebra to the original field. The comparison is the canonical
scalar-extension map on this subalgebra. -/
theorem subalgebraDescendsOfGalois [FiniteDimensional k K] [IsGalois k K]
    (B : Subalgebra K (K ⊗[k] A))
    (h : ∀ g x, x ∈ B → (SemilinearAction.scalarExtension (k := k) (K := K) A).act g x ∈ B) :
    ∃ (C : Subalgebra k A) (e : (K ⊗[k] C) ≃ₐ[K] B),
      B.val.comp e.toAlgHom = Algebra.TensorProduct.map (AlgHom.id K K) C.val := by
  let f : A →ₐ[k] K ⊗[k] A := Algebra.TensorProduct.includeRight
  let C := (B.restrictScalars k).comap f
  let fC : C →ₐ[k] B :=
    { toFun := fun x ↦ ⟨f x, x.property⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun x y ↦ Subtype.ext (map_mul f (x : A) (y : A))
      map_zero' := Subtype.ext (map_zero f)
      map_add' := fun x y ↦ Subtype.ext (map_add f (x : A) (y : A))
      commutes' := fun r ↦ Subtype.ext (f.commutes r) }
  let ρ := subalgebraAction B h
  let g : C →ₗ[k] ρ.fixed := fC.toLinearMap.codRestrict _ fun x σ ↦ by
    apply Subtype.ext
    change (SemilinearAction.scalarExtension (k := k) (K := K) A).act σ
      ((1 : K) ⊗ₜ[k] (x : A)) = (1 : K) ⊗ₜ[k] (x : A)
    simp
  have hg : Function.Bijective g := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective
      exact congrArg (fun z : ρ.fixed ↦ ((z : B) : K ⊗[k] A)) hxy
    · intro y
      let τ := SemilinearAction.scalarExtension (k := k) (K := K) A
      let z : τ.fixed := ⟨y.val.val, fun σ ↦ congrArg Subtype.val (y.property σ)⟩
      obtain ⟨x, hx⟩ := (SemilinearAction.scalarExtension_bijective (k := k) (K := K) A).2 z
      have hx' : (1 : K) ⊗ₜ[k] x = (y.val : K ⊗[k] A) := congrArg Subtype.val hx
      have hxC : x ∈ C := by
        change (1 : K) ⊗ₜ[k] x ∈ B
        rw [hx']
        exact y.val.property
      exact ⟨⟨x, hxC⟩, Subtype.ext (Subtype.ext hx')⟩
  let e₀ := LinearEquiv.ofBijective g hg
  let e₁ := (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) e₀).trans
    ρ.descentEquiv
  let φ : K ⊗[k] C →ₐ[K] B := AlgHom.liftEquiv k K C B fC
  have hφ : φ.toLinearMap = e₁.toLinearMap := by
    ext x
    rfl
  let e := AlgEquiv.ofBijective φ (by
    change Function.Bijective φ.toLinearMap
    rw [hφ]
    exact e₁.bijective)
  refine ⟨C, e, ?_⟩
  ext x
  change (φ (1 ⊗ₜ[k] x)).val =
    Algebra.TensorProduct.map (AlgHom.id K K) C.val (1 ⊗ₜ[k] x)
  simp [φ, fC, f]

end SubalgebraDescent

/-- Geometric connectedness descends through a surjective base change. A
residue field of a point over each test field gives a connected scheme that
surjects onto the original test fiber. -/
theorem geometricallyConnectedOfSurjectiveBaseChange {X Y S : Scheme.{u}}
    (q : X ⟶ Y) (f : S ⟶ Y) [Surjective f]
    [GeometricallyConnected (pullback.snd q f)] : GeometricallyConnected q := by
  constructor
  apply (geometrically_iff_of_isClosedUnderIsomorphisms
    (P := fun Z : Scheme.{u} ↦ ConnectedSpace Z)).mpr
  intro K _ y
  let U := pullback f y
  have : Nonempty U := (pullback.snd f y).surjective.nonempty
  let x := Classical.choice (inferInstance : Nonempty U)
  let t := U.fromSpecResidueField x
  let tₛ := t ≫ pullback.fst f y
  let tₖ := t ≫ pullback.snd f y
  have ht : tₖ ≫ y = tₛ ≫ f := by
    simp only [tₖ, tₛ, Category.assoc, pullback.condition]
  have : Surjective tₖ :=
    ⟨fun z ↦ ⟨Classical.choice inferInstance, Subsingleton.elim _ z⟩⟩
  let v := pullback.snd q y
  let V := pullback v tₖ
  let a := pullback.fst v tₖ ≫ pullback.fst q y
  let b := pullback.snd v tₖ
  have h : IsPullback a b q (tₛ ≫ f) := by
    rw [← ht]
    exact (IsPullback.of_hasPullback v tₖ).paste_horiz (IsPullback.of_hasPullback q y)
  let l : V ⟶ pullback q f := pullback.lift a (b ≫ tₛ)
    (h.w.trans (Category.assoc b tₛ f).symm)
  have hh : IsPullback l b (pullback.snd q f) tₛ := by
    apply IsPullback.of_right (h₁₂ := pullback.fst q f) (h₂₂ := f) (v₁₃ := q)
    · simpa only [l, pullback.lift_fst] using h
    · simp [l]
    · exact IsPullback.of_hasPullback q f
  have hv : ConnectedSpace V :=
    GeometricallyConnected.geometrically_connectedSpace (f := pullback.snd q f) tₛ l b hh
  exact (pullback.fst v tₖ).surjective.connectedSpace (pullback.fst v tₖ).continuous

/-- The scheme construction gives the component group and identity component
with the universal property and all field comparisons. -/
theorem identityComponentAndQuotientOfSchemeQuotients
    (h : Specs.AffineComponentQuotientsExist.{u}) : Specs.IdentityComponentAndQuotient.{u} := by
  intro k _ G
  have : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  obtain ⟨Y, q, hfin, he, hflat, hqc, hopen, hgeo⟩ :=
    h k G.val.X G.property.1 G.property.2.1
  obtain ⟨s, hs⟩ := existsComponentGroupStructure G.val q
  let Q : Specs.GroupScheme k := @Grp.mk (SchemeOver k) _ _ Y s
  let q' : G.val ⟶ Q := @Grp.homMk _ _ _ _ Q q hs
  have : Flat q'.hom.hom.left := hflat
  have : QuasiCompact q'.hom.hom.left := hqc
  have : UniversallyOpen q'.hom.hom.left := hopen
  have : GeometricallyConnected q'.hom.hom.left := hgeo
  obtain ⟨H, i, hi⟩ := existsComponentKernel q'
  exact ⟨Q, H, q', i, componentQuotientOfKernel q' i hi, componentPointsOfQuotient q',
    componentGaloisOfFinite Q, fun K _ _ ↦ componentQuotientAfterBaseChange (K := K) q' i hi⟩

private lemma idempotentsEqualOfBasicOpens {A : Type u} [CommRing A]
    {a b : A} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (h : (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) = PrimeSpectrum.basicOpen b) :
    a = b := by
  let e := PrimeSpectrum.isIdempotentElemEquivClopens (R := A)
  exact congrArg Subtype.val (e.injective (SetLike.coe_injective h :
    e ⟨a, ha⟩ = e ⟨b, hb⟩))

/-- A finite clopen component partition specified after an injective algebra
map corresponds to a complete orthogonal family before the map. -/
lemma completeIdempotentsOfComponentPartition {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f)
    (v : ConnectedComponents (PrimeSpectrum B) → A)
    [Fintype (ConnectedComponents (PrimeSpectrum B))]
    (hv : ∀ i, IsIdempotentElem (v i) ∧
      (PrimeSpectrum.basicOpen (f (v i)) : Set (PrimeSpectrum B)) =
        ConnectedComponents.mk ⁻¹' {i}) :
    CompleteOrthogonalIdempotents v := by
  classical
  have horth : OrthogonalIdempotents v := by
    refine ⟨fun i ↦ (hv i).1, fun i j hij ↦ hf ?_⟩
    rw [map_mul, map_zero]
    apply idempotentsEqualOfBasicOpens (((hv i).1.map f).mul ((hv j).1.map f)) .zero
    rw [PrimeSpectrum.basicOpen_mul, TopologicalSpace.Opens.coe_inf, (hv i).2, (hv j).2]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      PrimeSpectrum.basicOpen_zero, TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h₁, h₂⟩
    exact hij (h₁.symm.trans h₂)
  refine ⟨horth, hf ?_⟩
  rw [map_one]
  apply idempotentsEqualOfBasicOpens (horth.isIdempotentElem_sum.map f) .one
  ext x
  simp only [PrimeSpectrum.basicOpen_one, TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  let i := ConnectedComponents.mk x
  have hm : x ∈ (PrimeSpectrum.basicOpen (f (v i)) : Set (PrimeSpectrum B)) := by
    rw [(hv i).2]
    rfl
  change f (v i) ∉ x.asIdeal at hm
  change f (∑ j, v j) ∉ x.asIdeal
  intro h
  apply hm
  have hmul := x.asIdeal.mul_mem_left (f (v i)) h
  rwa [← map_mul, horth.mul_sum_of_mem (Finset.mem_univ i)] at hmul

section IdempotentAlgebra

variable {F R I : Type u} [Field F] [CommRing R] [Algebra F R] [Fintype I]
  {v : I → R}

/-- Include the algebra of scalars on the pieces of a finite clopen partition
into the coordinate algebra. -/
private noncomputable def idempotentAlgebraMap (hv : CompleteOrthogonalIdempotents v) :
    (I → F) →ₐ[F] R where
  toFun a := ∑ i, a i • v i
  map_zero' := by simp
  map_one' := by simpa only [Pi.one_apply, one_smul] using hv.complete
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_mul' a b := by
    classical
    simp [Finset.sum_mul, Finset.mul_sum, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
      hv.mul_eq, smul_ite, smul_smul]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [mul_comm (a i) (b i)]
  commutes' a := by
    change ∑ i, a • v i = algebraMap F R a
    rw [← Finset.smul_sum, hv.complete, Algebra.smul_def, mul_one]

@[simp]
private lemma idempotentAlgebraMap_single [DecidableEq I]
    (hv : CompleteOrthogonalIdempotents v) (i : I) :
    idempotentAlgebraMap (F := F) hv (Pi.single i 1) = v i := by
  change ∑ j, Pi.single (M := fun _ ↦ F) i 1 j • v j = v i
  simp [Pi.single_apply]

private lemma idempotentAlgebraMap_injective (hv : CompleteOrthogonalIdempotents v)
    (hne : ∀ i, v i ≠ 0) : Function.Injective (idempotentAlgebraMap (F := F) hv) := by
  classical
  intro a b hab
  ext i
  have h (c : I → F) : v i * idempotentAlgebraMap hv c = c i • v i := by
    change v i * (∑ j, c j • v j) = c i • v i
    simp [Finset.mul_sum, Algebra.mul_smul_comm, hv.mul_eq, smul_ite]
  exact smul_left_injective F (hne i) ((h a).symm.trans ((congrArg (v i * ·) hab).trans (h b)))

end IdempotentAlgebra

section GaloisIdempotents

open Descent

variable {k K A : Type u} [Field k] [Field K] [Algebra k K] [CommRing A] [Algebra k A]

private lemma scalarExtensionAct_eq (σ : Gal(K/k)) (x : K ⊗[k] A) :
    (SemilinearAction.scalarExtension A).act σ x =
      Algebra.TensorProduct.congr σ (AlgEquiv.refl : A ≃ₐ[k] A) x := by
  induction x using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private lemma permutesComponentIdempotents {E : IntermediateField k K}
    [Normal k K] (σ : Gal(E/k))
    (v : ConnectedComponents (PrimeSpectrum (K ⊗[k] A)) → E ⊗[k] A)
    (hv : ∀ i, IsIdempotentElem (v i) ∧
      (PrimeSpectrum.basicOpen (Algebra.TensorProduct.map E.val (AlgHom.id k A) (v i)) :
        Set (PrimeSpectrum (K ⊗[k] A))) = ConnectedComponents.mk ⁻¹' {i}) (i) :
    ∃ j, (SemilinearAction.scalarExtension A).act σ (v i) = v j := by
  let f := Algebra.TensorProduct.map E.val (AlgHom.id k A)
  let g := Algebra.TensorProduct.congr (σ.liftNormal K) (AlgEquiv.refl : A ≃ₐ[k] A)
  let h := (PrimeSpectrum.homeomorphOfRingEquiv g.toRingEquiv).symm
  have hf : Function.Injective f :=
    Module.Flat.rTensor_preserves_injective_linearMap E.val.toLinearMap Subtype.val_injective
  have hcomm (z : E ⊗[k] A) : f ((SemilinearAction.scalarExtension A).act σ z) = g (f z) := by
    rw [scalarExtensionAct_eq]
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      change (E.val (σ x)) ⊗ₜ[k] y = (σ.liftNormal K (E.val x)) ⊗ₜ[k] y
      exact congrArg (· ⊗ₜ[k] y) (σ.liftNormal_commutes K x).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe i
  refine ⟨ConnectedComponents.mk (h.symm x), hf ?_⟩
  rw [hcomm]
  apply idempotentsEqualOfBasicOpens (((hv _).1.map f).map g) ((hv _).1.map f)
  change (PrimeSpectrum.basicOpen (g (f (v (ConnectedComponents.mk x)))) :
    Set (PrimeSpectrum (K ⊗[k] A))) =
    (PrimeSpectrum.basicOpen (f (v (ConnectedComponents.mk (h.symm x)))) :
      Set (PrimeSpectrum (K ⊗[k] A)))
  have hp (z : K ⊗[k] A) : (PrimeSpectrum.basicOpen (g z) : Set (PrimeSpectrum (K ⊗[k] A))) =
      h ⁻¹' (PrimeSpectrum.basicOpen z : Set (PrimeSpectrum (K ⊗[k] A))) := rfl
  rw [hp, (hv _).2, (hv _).2, connectedComponents_preimage_singleton,
    connectedComponents_preimage_singleton]
  have hpre (z : PrimeSpectrum (K ⊗[k] A)) : _root_.IsConnected (h ⁻¹' {z}) :=
    h.isConnected_preimage.mpr isConnected_singleton
  simpa only [h.apply_symm_apply] using
    h.isQuotientMap.isCoinducing.preimage_connectedComponent hpre (h.symm x)

end GaloisIdempotents

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 150000 in
/-- The subalgebra of functions that are scalars on geometric components
descends from a common finite Galois field of definition. -/
private lemma existsComponentAlgebra {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] :
    let K := SeparableClosure k
    let I := ConnectedComponents (PrimeSpectrum (K ⊗[k] A))
    ∃ (C : Subalgebra k A) (e : K ⊗[k] C ≃ₐ[K] (I → K)),
      ∀ i, letI := Classical.decEq I
        (PrimeSpectrum.basicOpen
          (Algebra.TensorProduct.map (AlgHom.id K K) C.val (e.symm (Pi.single i 1))) :
          Set (PrimeSpectrum (K ⊗[k] A))) = ConnectedComponents.mk ⁻¹' {i} := by
  classical
  dsimp only
  let K := SeparableClosure k
  let R := K ⊗[k] A
  let I := ConnectedComponents (PrimeSpectrum R)
  let _ : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  let _ : Finite I := finiteConnectedComponents (PrimeSpectrum R)
  let _ : Fintype I := Fintype.ofFinite I
  obtain ⟨L, v, hv⟩ := componentIdempotentsDefinedOverFiniteGalois (k := k) (A := A)
  let E := L.toIntermediateField
  let f := Algebra.TensorProduct.map E.val (AlgHom.id k A)
  have hf : Function.Injective f :=
    Module.Flat.rTensor_preserves_injective_linearMap E.val.toLinearMap Subtype.val_injective
  have hcomplete := completeIdempotentsOfComponentPartition f.toRingHom hf v hv
  have hne (i : I) : v i ≠ 0 := by
    intro h
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe i
    have hx : x ∈ (PrimeSpectrum.basicOpen (f (v (ConnectedComponents.mk x))) :
        Set (PrimeSpectrum R)) := by
      rw [(hv _).2]
      rfl
    rw [h, map_zero, PrimeSpectrum.basicOpen_zero] at hx
    exact hx
  let j := idempotentAlgebraMap (F := E) hcomplete
  let B := j.range
  have hB (σ : Gal(E/k)) (x : E ⊗[k] A) (hx : x ∈ B) :
      (Descent.SemilinearAction.scalarExtension (k := k) (K := E) A).act σ x ∈ B := by
    obtain ⟨a, rfl⟩ := hx
    let ρ := Descent.SemilinearAction.scalarExtension (k := k) (K := E) A
    change ρ.act σ (∑ i, a i • v i) ∈ B
    rw [map_sum (ρ.act σ)]
    apply B.sum_mem
    intro i _
    obtain ⟨l, hl⟩ := permutesComponentIdempotents σ v hv i
    rw [ρ.map_smul, show ρ.act σ (v i) = v l from hl]
    apply B.smul_mem
    exact ⟨Pi.single l 1, idempotentAlgebraMap_single hcomplete l⟩
  obtain ⟨C, eC, heC⟩ := subalgebraDescendsOfGalois B hB
  let e₀ := AlgEquiv.ofInjective j (idempotentAlgebraMap_injective hcomplete hne)
  let eE := eC.trans e₀.symm
  have heE (a : I → E) : Algebra.TensorProduct.map (AlgHom.id E E) C.val (eE.symm a) = j a := by
    rw [← DFunLike.congr_fun heC]
    change (eC (eC.symm (e₀ a))).val = j a
    rw [eC.apply_symm_apply]
    rfl
  let t := Algebra.TensorProduct.cancelBaseChange k E K K C
  let eK := t.symm.trans ((Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) eE).trans
    (Algebra.TensorProduct.piScalarRight E K K I))
  let w := Algebra.TensorProduct.map E.val (AlgHom.id k C)
  have ht (x : E ⊗[k] C) : t (1 ⊗ₜ[E] x) = w x := by
    induction x using TensorProduct.inductionOn with
    | tmul s c =>
      simp [t, w, Algebra.smul_def]
      rfl
    | add x y hx hy =>
      rw [TensorProduct.tmul_add]
      change t.toRingEquiv.toRingHom (_ + _) = w.toRingHom (x + y)
      rw [t.toRingEquiv.toRingHom.map_add, w.toRingHom.map_add]
      exact congrArg₂ (· + ·) hx hy
  let mK := Algebra.TensorProduct.map (AlgHom.id K K) C.val
  let mE := Algebra.TensorProduct.map (AlgHom.id E E) C.val
  have hw (x : E ⊗[k] C) :
      mK (w x) = f (mE x) := by
    induction x using TensorProduct.inductionOn with
    | tmul s c => rfl
    | add x y hx hy =>
      change mK.toRingHom (w.toRingHom (x + y)) = f.toRingHom (mE.toRingHom (x + y))
      rw [w.toRingHom.map_add, mK.toRingHom.map_add, mE.toRingHom.map_add, f.toRingHom.map_add]
      exact congrArg₂ (· + ·) hx hy
  refine ⟨C, eK, fun i ↦ ?_⟩
  have hs : eK.symm (Pi.single i 1) = w (eE.symm (Pi.single i 1)) := by
    apply eK.injective
    rw [AlgEquiv.apply_symm_apply, ← ht]
    simp only [eK, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply,
      Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
      AlgEquiv.refl_toAlgHom, AlgHom.id_apply]
    ext l
    simp [Pi.single_apply]
  change (PrimeSpectrum.basicOpen (mK (eK.symm (Pi.single i 1))) : Set (PrimeSpectrum R)) = _
  rw [hs, hw, show mE (eE.symm (Pi.single i 1)) = j (Pi.single i 1) from heE _, idempotentAlgebraMap_single]
  exact (hv i).2

local instance : MorphismProperty.RespectsIso @GeometricallyConnected := by
  rw [GeometricallyConnected.eq_geometrically]
  infer_instance

/-- An affine connected scheme over a separably closed field is geometrically
connected, since the algebraic closure is purely inseparable over that field. -/
private lemma geometricallyConnectedOfSepClosed {k : Type u} [Field k] [IsSepClosed k]
    {X : Scheme.{u}} [IsAffine X] (s : X ⟶ Spec (CommRingCat.of k)) [ConnectedSpace X] :
    GeometricallyConnected s := by
  let Y : SchemeOver k := Over.mk s
  have hY : IsAffine Y.left := ‹IsAffine X›
  obtain ⟨A, ⟨j⟩⟩ := essImage_algSpec.mpr hY
  let K := AlgebraicClosure k
  have hc : ConnectedSpace (PrimeSpectrum A.unop) :=
    j.hom.left.homeomorph.connectedSpace_iff.mpr (inferInstance : ConnectedSpace X)
  let e := (PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable k K A.unop).homeomorph _
  let d := PrimeSpectrum.homeomorphOfRingEquiv
    (Algebra.TensorProduct.comm k K A.unop).toRingEquiv
  have : ConnectedSpace (PrimeSpectrum (K ⊗[k] A.unop)) :=
    (d.trans e).connectedSpace_iff.mpr hc
  have h := geometricallyConnectedSpecOfAlgClosure (k := k) (A := A.unop)
  change GeometricallyConnected ((testSpec k).obj A).hom at h
  rw [← Over.w j.hom] at h
  exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected j.hom.left s).mp h

/-- For a split component algebra, the pullbacks along the individual
sections are the clopen components, with their original scheme structures. -/
private lemma geometricallyConnectedOfSplitComponents {k A : Type u} [Field k] [IsSepClosed k]
    [CommRing A] [Algebra k A] [DecidableEq (ConnectedComponents (PrimeSpectrum A))]
    [Finite (ConnectedComponents (PrimeSpectrum A))]
    (f : (ConnectedComponents (PrimeSpectrum A) → k) →ₐ[k] A)
    (h : ∀ i, (PrimeSpectrum.basicOpen (f (Pi.single i 1)) : Set (PrimeSpectrum A)) =
      ConnectedComponents.mk ⁻¹' {i}) :
    GeometricallyConnected (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
  let I := ConnectedComponents (PrimeSpectrum A)
  let q := Spec.map (CommRingCat.ofHom f.toRingHom)
  let p (i : I) := Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : I ↦ k) i))
  have hp (i : I) : Set.range (p i) =
      (PrimeSpectrum.basicOpen (Pi.single (M := fun _ : I ↦ k) i 1) :
        Set (PrimeSpectrum (I → k))) := by
    change Set.range (PrimeSpectrum.comap (Pi.evalRingHom (fun _ : I ↦ k) i)) = _
    rw [← Set.image_univ, ← PrimeSpectrum.comap_evalRingHom_basicOpen]
    simp
  have fibers (i : I) : GeometricallyConnected (pullback.snd q (p i)) := by
    have hr : Set.range (pullback.fst q (p i)) = ConnectedComponents.mk ⁻¹' {i} := by
      rw [Scheme.Pullback.range_fst, hp]
      exact h i
    have hc : _root_.IsConnected (Set.range (pullback.fst q (p i))) := by
      rw [hr]
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe i
      rw [connectedComponents_preimage_singleton]
      exact isConnected_connectedComponent
    have : IsOpenImmersion (p i) := inferInstance
    let e := (pullback.fst q (p i)).isOpenEmbedding.isEmbedding.toHomeomorph
    have : ConnectedSpace ↥(pullback q (p i)) :=
      e.connectedSpace_iff.mpr (isConnected_iff_connectedSpace.mp hc)
    exact geometricallyConnectedOfSepClosed (pullback.snd q (p i))
  constructor
  apply (geometrically_iff_of_isClosedUnderIsomorphisms
    (P := fun Y : Scheme.{u} ↦ ConnectedSpace Y)).mpr
  intro T _ y
  let x : Spec (CommRingCat.of T) := Nonempty.some inferInstance
  obtain ⟨a, ha⟩ := (PrimeSpectrum.sigmaToPi_bijective (fun _ : I ↦ k)).2 (y x)
  let i := a.1
  have hy : Set.range y ⊆ Set.range (p i) := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z x]
    exact ⟨a.2, ha⟩
  have : IsOpenImmersion (p i) := inferInstance
  let t := IsOpenImmersion.lift (p i) y hy
  have ht : t ≫ p i = y := IsOpenImmersion.lift_fac _ _ _
  let v := pullback.snd q (p i)
  have hv := fibers i
  let a := pullback.fst v t ≫ pullback.fst q (p i)
  let b := pullback.snd v t
  have hpb : IsPullback a b q y := by
    rw [← ht]
    exact (IsPullback.of_hasPullback v t).paste_horiz (IsPullback.of_hasPullback q (p i))
  exact hpb.isoPullback.hom.homeomorph.connectedSpace_iff.mp
    (GeometricallyConnected.geometrically_connectedSpace (f := v) t _ _ (.of_hasPullback _ _))

section AffineQuotient

open Algebra.TensorProduct (includeRight)

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

private noncomputable abbrev affineScalarProjection (A : Type u) [CommRing A] [Algebra k A] :
    Spec (CommRingCat.of (K ⊗[k] A)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (R := A) (S := K ⊗[k] A)
    (RingHomClass.toRingHom (includeRight : A →ₐ[k] K ⊗[k] A)))

private lemma affineScalarExtensionSquare (A : Type u) [CommRing A] [Algebra k A] :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[k] A))))
      (affineScalarProjection k K A) (fieldSpecMap k K)
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
  refine (IsPullback.of_hasPullback (fieldSpecMap k K)
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))).of_iso'
      (pullbackSpecIso k K A).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simpa only [Iso.symm_hom, Iso.refl_hom, Category.comp_id] using
      pullbackSpecIso_inv_fst' k K A
  · simpa only [Iso.symm_hom, Iso.refl_hom, Category.comp_id, affineScalarProjection,
      fieldSpecMap] using
      pullbackSpecIso_inv_snd k K A
  · simp
  · simp

private lemma affineMapScalarExtensionPullback {A C : Type u}
    [CommRing A] [Algebra k A] [CommRing C] [Algebra k C] (f : C →ₐ[k] A) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id K K) f).toRingHom))
      (affineScalarProjection k K A) (affineScalarProjection k K C)
      (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
  let m := Algebra.TensorProduct.map (AlgHom.id K K) f
  let q := Spec.map (CommRingCat.ofHom f.toRingHom)
  let qK := Spec.map (CommRingCat.ofHom m.toRingHom)
  let s := Spec.map (CommRingCat.ofHom (algebraMap k C))
  let sK := Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[k] C)))
  have h : q ≫ s = Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
    dsimp only [q, s]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun g : k →+* A ↦ Spec.map (CommRingCat.ofHom g)) f.comp_algebraMap
  have hK : qK ≫ sK = Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[k] A))) := by
    dsimp only [qK, sK]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun g : K →+* K ⊗[k] A ↦ Spec.map (CommRingCat.ofHom g)) m.comp_algebraMap
  change IsPullback qK _ _ q
  apply IsPullback.of_right (h₁₂ := sK) (h₂₂ := s) (v₁₃ := fieldSpecMap k K)
  · rw [hK, h]
    exact affineScalarExtensionSquare k K A
  · dsimp only [qK, q, affineScalarProjection]
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  · exact affineScalarExtensionSquare k K C

end AffineQuotient

/-- An étale target gives an open graph over the base. Thus flatness and
universal openness of the source structure morphism pass to the map. -/
private lemma flatUniversallyOpenOfEtale {X Y S : Scheme.{u}} (q : X ⟶ Y) (s : Y ⟶ S)
    [Etale s] [Flat (q ≫ s)] [UniversallyOpen (q ≫ s)] : Flat q ∧ UniversallyOpen q := by
  let g := pullback.lift (𝟙 X) q (by simp : 𝟙 X ≫ (q ≫ s) = q ≫ s)
  have : IsOpenImmersion g :=
    MorphismProperty.of_isPullback (pullback_lift_diagonal_isPullback q s) inferInstance
  have h : g ≫ pullback.snd (q ≫ s) s = q := pullback.lift_snd _ _ _
  rw [← h]
  exact ⟨inferInstance, inferInstance⟩

set_option maxHeartbeats 700000 in
/-- Finite type affine schemes over a field admit a finite étale target whose
geometric fibers are their connected components. -/
theorem affineComponentQuotientsExist : Specs.AffineComponentQuotientsExist.{u} := by
  classical
  intro k _ X hX htype
  obtain ⟨A₀, ⟨j⟩⟩ := essImage_algSpec.mpr hX
  let A : Type u := A₀.unop
  have h₀ : LocallyOfFiniteType ((testSpec k).obj A₀).hom := by
    rw [← Over.w j.hom]
    infer_instance
  have : Algebra.FiniteType k A := by
    change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k A))) at h₀
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h₀
    exact RingHom.finiteType_algebraMap.mp h₀
  let K := SeparableClosure k
  let I := ConnectedComponents (PrimeSpectrum (K ⊗[k] A))
  let _ : IsNoetherianRing (K ⊗[k] A) := Algebra.FiniteType.isNoetherianRing K (K ⊗[k] A)
  let _ : Finite I := finiteConnectedComponents (PrimeSpectrum (K ⊗[k] A))
  obtain ⟨C, e, he⟩ := existsComponentAlgebra (k := k) (A := A)
  have : Module.Finite K (K ⊗[k] C) := .of_surjective e.symm.toLinearMap e.symm.surjective
  have : Module.Finite k C := .of_finite_tensorProduct_of_faithfullyFlat K
  have : Algebra.Etale K (K ⊗[k] C) := .of_equiv e.symm
  have : Algebra.Etale k C := .of_etale_tensorProduct_of_faithfullyFlat K
  let Y := (testSpec k).obj (op (CommAlgCat.of k C))
  let q₀ := (testSpec k).map (CommAlgCat.ofHom C.val).op
  have hYfin : IsFinite Y.hom := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k C)))
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have hYetale : Etale Y.hom := by
    change Etale (Spec.map (CommRingCat.ofHom (algebraMap k C)))
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  have : Flat (q₀.left ≫ Y.hom) := by
    rw [Over.w q₀]
    change Flat (Spec.map (CommRingCat.ofHom (algebraMap k A)))
    exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : UniversallyOpen (q₀.left ≫ Y.hom) := inferInstance
  obtain ⟨hflat, hopen⟩ := flatUniversallyOpenOfEtale q₀.left Y.hom
  let m := Algebra.TensorProduct.map (AlgHom.id K K) C.val
  let qK := Spec.map (CommRingCat.ofHom m.toRingHom)
  let w₀ := CommRingCat.ofHom (R := I → K) (S := K ⊗[k] C) e.symm.toAlgHom.toRingHom
  let w := Spec.map w₀
  have : IsIso w := by
    have : IsIso w₀ := (ConcreteCategory.isIso_iff_bijective _).mpr e.symm.bijective
    infer_instance
  have hsplit : GeometricallyConnected (qK ≫ w) := by
    dsimp only [qK, w, w₀]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact geometricallyConnectedOfSplitComponents (m.comp e.symm.toAlgHom) he
  have hgeoK : GeometricallyConnected qK :=
    (MorphismProperty.cancel_right_of_respectsIso @GeometricallyConnected qK w).mp hsplit
  let p := affineScalarProjection k K C
  have hfield : Surjective (fieldSpecMap k K) :=
    ⟨fun x ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ x⟩⟩
  have hproj : Surjective p :=
    MorphismProperty.of_isPullback (affineScalarExtensionSquare k K C) hfield
  let qA := Spec.map (CommRingCat.ofHom C.val.toRingHom)
  have hpb : IsPullback (affineScalarProjection k K A) qK qA p :=
    (affineMapScalarExtensionPullback k K C.val).flip
  have hgeoPB : GeometricallyConnected (pullback.snd qA p) := by
    apply (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected hpb.isoPullback.hom _).mp
    rw [hpb.isoPullback_hom_snd]
    exact hgeoK
  have hgeo : GeometricallyConnected q₀.left :=
    @geometricallyConnectedOfSurjectiveBaseChange _ _ _ qA p hproj hgeoPB
  have hqc : QuasiCompact q₀.left := by
    change QuasiCompact (Spec.map (CommRingCat.ofHom C.val.toRingHom))
    infer_instance
  have : IsIso j.inv.left := inferInstance
  let q := j.inv ≫ q₀
  refine ⟨Y, q, hYfin, hYetale, ?_, ?_, ?_, ?_⟩
  · exact MorphismProperty.comp_mem @Flat j.inv.left q₀.left inferInstance hflat
  · exact MorphismProperty.comp_mem @QuasiCompact j.inv.left q₀.left inferInstance hqc
  · exact (MorphismProperty.cancel_left_of_respectsIso @UniversallyOpen j.inv.left q₀.left).mpr hopen
  · exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected j.inv.left q₀.left).mpr hgeo

/-- The identity component and finite étale component group of an affine
algebraic group over any field. -/
theorem identityComponentAndQuotient : Specs.IdentityComponentAndQuotient.{u} :=
  identityComponentAndQuotientOfSchemeQuotients affineComponentQuotientsExist

end LinearAlgebraicGroups
