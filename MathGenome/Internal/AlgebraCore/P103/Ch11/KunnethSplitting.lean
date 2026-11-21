import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.KunnethSplitting
import MathGenome.Internal.AlgebraCore.P103.Ch10.Complexes
import MathGenome.Internal.AlgebraCore.P103.Ch11.FreeComplexReplacement
import MathGenome.Internal.AlgebraCore.P103.Ch11.ArbitraryRankPIDSubmodules
import MathGenome.Internal.AlgebraCore.P103.Ch11.KunnethFreeSplitting
import Mathlib.LinearAlgebra.Prod
import Mathlib.RingTheory.Filtration
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Module.Shrink
import Mathlib.Algebra.Module.ULift

/-!
Comparison and splitting transport for paper.tex 3135–3168.
Free replacements are resized using PID smallness and explicit coordinate
equivalences; zero factors are handled separately. The comparison maps on all
three terms preserve the prescribed sequence arrows and coefficient scalars.
-/
namespace P103.Ch11.KunnethSplitting

universe u a b t a' b' t'
variable {R : Type u} [Ring R]
variable {A : Type a} {B : Type b} {T : Type t}
variable {A' : Type a'} {B' : Type b'} {T' : Type t'}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup T]
variable [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup T']
variable [Module R A] [Module R B] [Module R T]
variable [Module R A'] [Module R B'] [Module R T']

/-- A section transports through the commuting square on the surjections. -/
theorem transport_section
    (eB : B' ≃ₗ[R] B) (eT : T' ≃ₗ[R] T)
    (β : B →ₗ[R] T) (β' : B' →ₗ[R] T')
    (hβ : β.comp eB.toLinearMap = eT.toLinearMap.comp β')
    (s' : T' →ₗ[R] B') (hs' : β'.comp s' = LinearMap.id) :
    β.comp (eB.toLinearMap.comp (s'.comp eT.symm.toLinearMap)) = LinearMap.id := by
  ext t
  change β (eB (s' (eT.symm t))) = t
  have hβ' (b : B') : β (eB b) = eT (β' b) := LinearMap.congr_fun hβ b
  have hs'' (t : T') : β' (s' t) = t := LinearMap.congr_fun hs' t
  rw [hβ', hs'']
  exact eT.apply_symm_apply t

/-- An isomorphism of all three terms transports the whole splitting,
including its prescribed injection and its prescribed surjection. -/
theorem transport_splitting
    (eA : A' ≃ₗ[R] A) (eB : B' ≃ₗ[R] B) (eT : T' ≃ₗ[R] T)
    (α : A →ₗ[R] B) (α' : A' →ₗ[R] B')
    (β : B →ₗ[R] T) (β' : B' →ₗ[R] T')
    (hα : eB.toLinearMap.comp α' = α.comp eA.toLinearMap)
    (hβ : β.comp eB.toLinearMap = eT.toLinearMap.comp β')
    (s' : T' →ₗ[R] B') (hs' : β'.comp s' = LinearMap.id)
    (e' : (A' × T') ≃ₗ[R] B')
    (he' : ∀ a t, e' (a, t) = α' a + s' t)
    (hβe' : ∀ a t, β' (e' (a, t)) = t) :
    ∃ s : T →ₗ[R] B, β.comp s = LinearMap.id ∧
      ∃ e : (A × T) ≃ₗ[R] B,
        (∀ a t, e (a, t) = α a + s t) ∧
        (∀ a t, β (e (a, t)) = t) := by
  let s := eB.toLinearMap.comp (s'.comp eT.symm.toLinearMap)
  let e := ((eA.symm.prodCongr eT.symm).trans e').trans eB
  refine ⟨s, transport_section eB eT β β' hβ s' hs', e, ?_, ?_⟩
  · intro a t
    change eB (e' (eA.symm a, eT.symm t)) = α a + eB (s' (eT.symm t))
    have hα' (a : A') : eB (α' a) = α (eA a) := LinearMap.congr_fun hα a
    rw [he', map_add, hα', eA.apply_symm_apply]
  · intro a t
    change β (eB (e' (eA.symm a, eT.symm t))) = t
    have hβ' (b : B') : β (eB b) = eT (β' b) := LinearMap.congr_fun hβ b
    rw [hβ', hβe']
    exact eT.apply_symm_apply t

/-- The short five lemma, stated for the actual maps of a pair of short
exact sequences. It also applies when source and target live in different
universes. -/
theorem middle_bijective
    (α : A →ₗ[R] B) (β : B →ₗ[R] T)
    (α' : A' →ₗ[R] B') (β' : B' →ₗ[R] T')
    (a : A' →ₗ[R] A) (b : B' →ₗ[R] B) (t : T' →ₗ[R] T)
    (hα : b.comp α' = α.comp a) (hβ : β.comp b = t.comp β')
    (hi : Function.Injective α) (he : Function.Exact α β)
    (he' : Function.Exact α' β') (hs' : Function.Surjective β')
    (ha : Function.Bijective a) (ht : Function.Bijective t) :
    Function.Bijective b := by
  have hαx (x : A') : b (α' x) = α (a x) := LinearMap.congr_fun hα x
  have hβx (x : B') : β (b x) = t (β' x) := LinearMap.congr_fun hβ x
  have hz (x : B') (hb : b x = 0) : x = 0 := by
    have htx : t (β' x) = 0 := by rw [← hβx, hb, map_zero]
    have hxβ : β' x = 0 := ht.1 (by simpa using htx)
    obtain ⟨y, hy⟩ := (he' x).mp hxβ
    have hya : a y = 0 := hi (by rw [← hαx, hy, hb, map_zero])
    have hy0 : y = 0 := ha.1 (by simpa using hya)
    rw [← hy, hy0, map_zero]
  constructor
  · intro x y hxy
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub, hxy, sub_self]
  · intro x
    obtain ⟨z, hz⟩ := ht.2 (β x)
    obtain ⟨y, hy⟩ := hs' z
    have hk : β (x - b y) = 0 := by rw [map_sub, hβx, hy, hz, sub_self]
    obtain ⟨q, hq⟩ := (he (x - b y)).mp hk
    obtain ⟨p, hp⟩ := ha.2 q
    refine ⟨α' p + y, ?_⟩
    rw [map_add, hαx, hp, hq, sub_add_cancel]

/-- Scalar linearity of a transported section follows from the two scalar
comparison squares. -/
theorem transport_section_scalars
    (eB : B' ≃ₗ[R] B) (eT : T' ≃ₗ[R] T)
    (s' : T' →ₗ[R] B')
    (σB : B →ₗ[R] B) (σB' : B' →ₗ[R] B')
    (σT : T →ₗ[R] T) (σT' : T' →ₗ[R] T')
    (hB : σB.comp eB.toLinearMap = eB.toLinearMap.comp σB')
    (hT : σT.comp eT.toLinearMap = eT.toLinearMap.comp σT')
    (hs : σB'.comp s' = s'.comp σT') :
    σB.comp (eB.toLinearMap.comp (s'.comp eT.symm.toLinearMap)) =
      (eB.toLinearMap.comp (s'.comp eT.symm.toLinearMap)).comp σT := by
  ext x
  change σB (eB (s' (eT.symm x))) = eB (s' (eT.symm (σT x)))
  have hb (y : B') : σB (eB y) = eB (σB' y) := LinearMap.congr_fun hB y
  have ht (y : T') : σT (eT y) = eT (σT' y) := LinearMap.congr_fun hT y
  have ht' : σT' (eT.symm x) = eT.symm (σT x) := by
    apply eT.injective
    rw [eT.apply_symm_apply, ← ht, eT.apply_symm_apply]
  have hsx (y : T') : σB' (s' y) = s' (σT' y) := LinearMap.congr_fun hs y
  rw [hb, hsx, ht']

end P103.Ch11.KunnethSplitting

namespace P103.Ch11.KunnethSplitting
open CategoryTheory
open P103.BalancedTensor
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch11.TorBalance P103.Specs.Ch11.KunnethSequence
noncomputable section
universe u v w v' w'
variable {R : Type u} [Ring R]
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Tensoring linear equivalences gives an equivalence of the shared balanced
quotients, without a commutativity assumption on the ring. -/
def tensorEquiv {A : Type v} {A' : Type v'} {B : Type w} {B' : Type w'}
    [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup B']
    [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ A'] [Module R B] [Module R B']
    (a : A ≃ₗ[Rᵐᵒᵖ] A') (b : B ≃ₗ[R] B') :
    Tensor R A B ≃ₗ[ℤ] Tensor R A' B' :=
  LinearEquiv.ofLinearMap (tensorMap a.toLinearMap b.toLinearMap)
    (tensorMap a.symm.toLinearMap b.symm.toLinearMap)
    (by
      apply tensor_hom_ext
      intro x y
      simp only [LinearMap.comp_apply, tensorMap_tmul, LinearMap.id_apply,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply])
    (by
      apply tensor_hom_ext
      intro x y
      simp only [LinearMap.comp_apply, tensorMap_tmul, LinearMap.id_apply,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply])

/-- Every all-model Tor action carries module equivalences to equivalences.
The inverse changes projective model as well as coefficient modules. -/
def torEquiv {n : ℕ} (T : TorMaps.{u,v,w} R n)
    {A A' : ModuleCat.{v} Rᵐᵒᵖ} {B B' : ModuleCat.{w} R}
    (P : ProjectiveChoice Rᵐᵒᵖ A) (Q : ProjectiveChoice Rᵐᵒᵖ A')
    (a : A ≃ₗ[Rᵐᵒᵖ] A') (b : B ≃ₗ[R] B') :
    TorWith P.val B n ≃ₗ[ℤ] TorWith Q.val B' n := by
  let f : A ⟶ A' := ModuleCat.ofHom a.toLinearMap
  let f' : A' ⟶ A := ModuleCat.ofHom a.symm.toLinearMap
  let g : B ⟶ B' := ModuleCat.ofHom b.toLinearMap
  let g' : B' ⟶ B := ModuleCat.ofHom b.symm.toLinearMap
  have hf : f ≫ f' = 𝟙 A := by ext x; exact a.symm_apply_apply x
  have hf' : f' ≫ f = 𝟙 A' := by ext x; exact a.apply_symm_apply x
  have hg : g ≫ g' = 𝟙 B := by ext x; exact b.symm_apply_apply x
  have hg' : g' ≫ g = 𝟙 B' := by ext x; exact b.apply_symm_apply x
  exact LinearEquiv.ofLinearMap (T.map P Q f g) (T.map Q P f' g')
    (by rw [← T.comp, hf', hg', T.id])
    (by rw [← T.comp, hf, hg, T.id])

/-- Quasi-isomorphisms induce the specified equivalence on the tensor
homology diagonal. -/
theorem tensorDiagonalMap_bijective
    {C C' : RightComplex.{u,v} R} {D D' : LeftComplex.{u,w} R}
    (f : C ⟶ C') (g : D ⟶ D') (hf : QuasiIsomorphism f)
    (hg : QuasiIsomorphism g) (n : ℕ) :
    Function.Bijective (tensorDiagonalMap f g n) := by
  have h (i : Diagonal n) : Function.Bijective
      (tensorMap (homologyMap f i.val.1) (homologyMap g i.val.2)) :=
    (tensorEquiv (LinearEquiv.ofBijective _ (hf i.val.1))
      (LinearEquiv.ofBijective _ (hg i.val.2))).bijective
  exact ⟨(DirectSum.lmap_injective _).mpr (fun i => (h i).1),
    (DirectSum.lmap_surjective _).mpr (fun i => (h i).2)⟩

/-- The same conclusion holds for the prescribed Tor map on every pair of
projective model families. -/
theorem torDiagonalMap_bijective
    {C C' : RightComplex.{u,v} R} {D D' : LeftComplex.{u,w} R}
    (f : C ⟶ C') (g : D ⟶ D') (hf : QuasiIsomorphism f)
    (hg : QuasiIsomorphism g) (P : HomologyModels C) (P' : HomologyModels C')
    (T : TorMaps.{u,v,w} R 1) (n : ℕ) :
    Function.Bijective (torDiagonalMap f g P P' T n) := by
  have h (i : TailDiagonal n) : Function.Bijective
      ((T.map (P i.val.1) (P' i.val.1)
        (ModuleCat.ofHom (homologyMap f i.val.1))
        (ModuleCat.ofHom (homologyMap g i.val.2))).toAddMonoidHom.toIntLinearMap) :=
    (torEquiv T
      (B := ModuleCat.of R (Homology D i.val.2))
      (B' := ModuleCat.of R (Homology D' i.val.2)) (P i.val.1) (P' i.val.1)
      (LinearEquiv.ofBijective _ (hf i.val.1))
      (LinearEquiv.ofBijective _ (hg i.val.2))).bijective
  exact ⟨(DirectSum.lmap_injective _).mpr (fun i => (h i).1),
    (DirectSum.lmap_surjective _).mpr (fun i => (h i).2)⟩

/-- The normalized naturality premise and the short five lemma identify all
three terms under quasi-isomorphisms. No independent tensor quasi-isomorphism
certificate is needed for this step. -/
theorem total_homology_bijective_of_normalized_naturality
    (hn : normalized_naturalType.{u,v,w})
    {C C' : RightComplex.{u,v} R} {D D' : LeftComplex.{u,w} R}
    (f : C ⟶ C') (g : D ⟶ D') (hf : QuasiIsomorphism f)
    (hg : QuasiIsomorphism g) (P : HomologyModels C) (P' : HomologyModels C')
    (T : TorMaps.{u,v,w} R 1) (n : ℕ)
    (S : NormalizedDegreeSequence C D P n)
    (S' : NormalizedDegreeSequence C' D' P' n) :
    Function.Bijective (homologyMap (ordinaryTotalMap f g) n) := by
  obtain ⟨hα, hβ⟩ := hn R C C' D D' f g P P' T n S S'
  exact middle_bijective (R := ℤ)
    (A := TensorDiagonal C' D' n) (B := Homology (ordinaryTotal C' D') n)
    (T := TorDiagonal C' D' P' n)
    (A' := TensorDiagonal C D n) (B' := Homology (ordinaryTotal C D) n)
    (T' := TorDiagonal C D P n) S'.α S'.β S.α S.β
    (tensorDiagonalMap f g n)
    (homologyMap (ordinaryTotalMap f g) n).toAddMonoidHom.toIntLinearMap
    (torDiagonalMap f g P P' T n) hα hβ.symm
    S'.injective_α S'.exact S.exact S.surjective_β
    (tensorDiagonalMap_bijective f g hf hg n)
    (torDiagonalMap_bijective f g hf hg P P' T n)

/-- A coefficient-linear section produces the full splitting with both
prescribed arrows. Exactness, rather than any chosen coordinates, proves
bijectivity of the resulting direct-product map. -/
theorem splitsOver_of_scalar_section
    {K : Type u} [CommRing K]
    (C : RightComplex.{u,v} K) (D : LeftComplex.{u,w} K)
    (P : HomologyModels C) (T : TorMaps.{u,v,w} K 1) (n : ℕ)
    (S : DegreeSequence C D P n)
    (s : TorDiagonal C D P n →ₗ[ℤ] Homology (ordinaryTotal C D) n)
    (hs : S.β.comp s = LinearMap.id)
    (hsc : ∀ r, (P103.Specs.Ch11.KunnethFreeSplitting.totalScalar C D n r).comp s =
      s.comp (P103.Specs.Ch11.KunnethFreeSplitting.torScalar C D P T n r)) :
    P103.Specs.Ch11.KunnethSplitting.SplitsOver C D P T n S := by
  let F : (TensorDiagonal C D n × TorDiagonal C D P n) →ₗ[ℤ]
      Homology (ordinaryTotal C D) n :=
    S.α.comp (LinearMap.fst ℤ _ _) + s.comp (LinearMap.snd ℤ _ _)
  have hsx (x : TorDiagonal C D P n) : S.β (s x) = x := LinearMap.congr_fun hs x
  have hβF (a : TensorDiagonal C D n) (t : TorDiagonal C D P n) :
      S.β (F (a,t)) = t := by
    change S.β (S.α a + s t) = t
    rw [map_add, S.exact.apply_apply_eq_zero, hsx, zero_add]
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨a,t⟩ ⟨a',t'⟩ h
      have ht : t = t' := by simpa only [hβF] using congrArg S.β h
      have ha : a = a' := S.injective_α (by
        change S.α a + s t = S.α a' + s t' at h
        rw [ht] at h
        exact add_right_cancel h)
      exact Prod.ext ha ht
    · intro x
      have hk : S.β (x - s (S.β x)) = 0 := by rw [map_sub, hsx, sub_self]
      obtain ⟨a, ha⟩ := (S.exact (x - s (S.β x))).mp hk
      exact ⟨(a, S.β x), by change S.α a + s (S.β x) = x; rw [ha, sub_add_cancel]⟩
  exact ⟨s, hs, hsc, LinearEquiv.ofBijective F hF, fun _ _ => rfl, hβF⟩

/-- The proved both-free retraction gives the full splitting for every
sequence whose actual surjection commutes with coefficients. -/
theorem both_free_splitsOver
    {K : Type u} [CommRing K] [IsDomain K] [IsPrincipalIdealRing K]
    (C : RightComplex.{u,v} K) (D : LeftComplex.{u,w} K)
    (hC : ∀ p, Module.Free Kᵐᵒᵖ (C.X p)) (hD : ∀ q, Module.Free K (D.X q))
    (P : HomologyModels C) (T : TorMaps.{u,v,w} K 1) (n : ℕ)
    (S : DegreeSequence C D P n)
    (hβ : ∀ r, S.β.comp (P103.Specs.Ch11.KunnethFreeSplitting.totalScalar C D n r) =
      (P103.Specs.Ch11.KunnethFreeSplitting.torScalar C D P T n r).comp S.β) :
    P103.Specs.Ch11.KunnethSplitting.SplitsOver C D P T n S := by
  obtain ⟨s, hs, hsc⟩ :=
    P103.Ch11.KunnethFreeSplitting.degreeSequence_scalar_splitting
      P103.Ch11.KunnethSequence.pure_tensor_cycle K C D hC hD P n S T hβ
  exact splitsOver_of_scalar_section C D P T n S s hs hsc

/-- Normalized naturality supplies the scalar compatibility required by the
both-free retraction theorem. -/
theorem both_free_normalized_splitsOver
    (hn : normalized_naturalType.{u,v,w})
    {K : Type u} [CommRing K] [IsDomain K] [IsPrincipalIdealRing K]
    (C : RightComplex.{u,v} K) (D : LeftComplex.{u,w} K)
    (hC : ∀ p, Module.Free Kᵐᵒᵖ (C.X p)) (hD : ∀ q, Module.Free K (D.X q))
    (P : HomologyModels C) (T : TorMaps.{u,v,w} K 1) (n : ℕ)
    (S : NormalizedDegreeSequence C D P n) :
    P103.Specs.Ch11.KunnethSplitting.SplitsOver C D P T n S.toDegreeSequence := by
  apply both_free_splitsOver C D hC hD P T n S.toDegreeSequence
  intro r
  exact (hn K C C D D (𝟙 C)
    (P103.Specs.Ch11.KunnethFreeSplitting.scalarChainMap D r) P P T n S S).2.symm

/-- The second-factor simultaneous family has the same both-free conclusion,
for its own normalized surjection. -/
theorem both_free_left_splitsOver
    {K : Type u} [CommRing K] [IsDomain K] [IsPrincipalIdealRing K]
    (L : LeftSequenceFamily.{u,v,w} K)
    (C : RightComplex.{u,v} K) (D : LeftComplex.{u,w} K)
    (hD : LeftFlatTermsAndBoundaries.{u,v,w} D)
    (hCfree : ∀ p, Module.Free Kᵐᵒᵖ (C.X p))
    (hDfree : ∀ q, Module.Free K (D.X q))
    (P : HomologyModels C) (T : TorMaps.{u,v,w} K 1) (n : ℕ) :
    P103.Specs.Ch11.KunnethSplitting.SplitsOver C D P T n (L.sequence C D hD P n) := by
  apply both_free_splitsOver C D hCfree hDfree P T n (L.sequence C D hD P n)
  intro r
  exact (L.naturality C C D D hD hD (𝟙 C)
    (P103.Specs.Ch11.KunnethFreeSplitting.scalarChainMap D r) P P T n).2.symm

/-- Commuting squares in the two factors induce a commuting square of the
canonical signed totals. The signs and zero extensions stay in the actual
upstream construction. -/
theorem ordinaryTotalMap_square
    {C C' : RightComplex.{u,v} R} {D D' : LeftComplex.{u,w} R}
    (a : C ⟶ C) (a' : C' ⟶ C') (f : C ⟶ C')
    (b : D ⟶ D) (b' : D' ⟶ D') (g : D ⟶ D')
    (hf : a ≫ f = f ≫ a') (hg : b ≫ g = g ≫ b') :
    ordinaryTotalMap a b ≫ ordinaryTotalMap f g =
      ordinaryTotalMap f g ≫ ordinaryTotalMap a' b' := by
  have hf' : HomologicalComplex.extendMap a nonnegativeChainEmbedding ≫
      HomologicalComplex.extendMap f nonnegativeChainEmbedding =
      HomologicalComplex.extendMap f nonnegativeChainEmbedding ≫
      HomologicalComplex.extendMap a' nonnegativeChainEmbedding := by
    rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp, hf]
  have hg' : HomologicalComplex.extendMap b nonnegativeChainEmbedding ≫
      HomologicalComplex.extendMap g nonnegativeChainEmbedding =
      HomologicalComplex.extendMap g nonnegativeChainEmbedding ≫
      HomologicalComplex.extendMap b' nonnegativeChainEmbedding := by
    rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp, hg]
  have H :
      tensorBicomplexMap (HomologicalComplex.extendMap a nonnegativeChainEmbedding)
        (HomologicalComplex.extendMap b nonnegativeChainEmbedding) ≫
      tensorBicomplexMap (HomologicalComplex.extendMap f nonnegativeChainEmbedding)
        (HomologicalComplex.extendMap g nonnegativeChainEmbedding) =
      tensorBicomplexMap (HomologicalComplex.extendMap f nonnegativeChainEmbedding)
        (HomologicalComplex.extendMap g nonnegativeChainEmbedding) ≫
      tensorBicomplexMap (HomologicalComplex.extendMap a' nonnegativeChainEmbedding)
        (HomologicalComplex.extendMap b' nonnegativeChainEmbedding) := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro x y
    exact congrArg₂ (tmul R)
      (congrArg (fun k => (k.f p).hom x) hf')
      (congrArg (fun k => (k.f q).hom y) hg')
  simpa only [ordinaryTotalMap, tensorTotalMap,
    HomologicalComplex₂.total.map_comp, HomologicalComplex.restrictionMap_comp] using
    congrArg (fun φ => HomologicalComplex.restrictionMap
      (HomologicalComplex₂.total.map φ (ComplexShape.down ℤ)) nonnegativeChainEmbedding) H

open P103.Specs.Ch11.KunnethFreeSplitting

/-- Scalar endomorphisms commute with every comparison on total homology. -/
theorem totalScalar_natural
    {K : Type u} [CommRing K]
    {C C' : RightComplex.{u,v} K} {D D' : LeftComplex.{u,w} K}
    (f : C ⟶ C') (g : D ⟶ D') (n : ℕ) (r : K) :
    (totalScalar C' D' n r).comp
        (homologyMap (ordinaryTotalMap f g) n).toAddMonoidHom.toIntLinearMap =
      (homologyMap (ordinaryTotalMap f g) n).toAddMonoidHom.toIntLinearMap.comp
        (totalScalar C D n r) := by
  have hg : scalarChainMap D r ≫ g = g ≫ scalarChainMap D' r := by
    ext q x
    exact (g.f q).hom.map_smul r x
  have h := ordinaryTotalMap_square (𝟙 C) (𝟙 C') f
    (scalarChainMap D r) (scalarChainMap D' r) g (by simp) hg
  apply LinearMap.ext
  intro x
  change homologyMap (ordinaryTotalMap (𝟙 C') (scalarChainMap D' r)) n
      (homologyMap (ordinaryTotalMap f g) n x) =
    homologyMap (ordinaryTotalMap f g) n
      (homologyMap (ordinaryTotalMap (𝟙 C) (scalarChainMap D r)) n x)
  calc
    _ = homologyMap (ordinaryTotalMap f g ≫
        ordinaryTotalMap (𝟙 C') (scalarChainMap D' r)) n x :=
      (congrFun (congrArg DFunLike.coe (P103.Ch10.Complexes.homologyMap_comp _ _ n)) x).symm
    _ = homologyMap (ordinaryTotalMap (𝟙 C) (scalarChainMap D r) ≫
        ordinaryTotalMap f g) n x := congrArg (fun k => homologyMap k n x) h.symm
    _ = _ := congrFun (congrArg DFunLike.coe (P103.Ch10.Complexes.homologyMap_comp _ _ n)) x

set_option maxHeartbeats 3000000 in
/-- Composition on the prescribed Tor diagonals includes every intermediate
projective model family. -/
theorem torDiagonalMap_comp
    {C C' C'' : RightComplex.{u,v} R} {D D' D'' : LeftComplex.{u,w} R}
    (f : C ⟶ C') (f' : C' ⟶ C'') (g : D ⟶ D') (g' : D' ⟶ D'')
    (P : HomologyModels C) (P' : HomologyModels C') (P'' : HomologyModels C'')
    (T : TorMaps.{u,v,w} R 1) (n : ℕ) :
    torDiagonalMap (f ≫ f') (g ≫ g') P P'' T n =
      (torDiagonalMap f' g' P' P'' T n).comp (torDiagonalMap f g P P' T n) := by
  apply LinearMap.ext
  intro x
  apply DFinsupp.ext
  intro i
  have hf : ModuleCat.ofHom (homologyMap (f ≫ f') i.val.1) =
      ModuleCat.ofHom (homologyMap f i.val.1) ≫
        ModuleCat.ofHom (homologyMap f' i.val.1) :=
    ModuleCat.hom_ext (P103.Ch10.Complexes.homologyMap_comp f f' i.val.1)
  have hg : ModuleCat.ofHom (homologyMap (g ≫ g') i.val.2) =
      ModuleCat.ofHom (homologyMap g i.val.2) ≫
        ModuleCat.ofHom (homologyMap g' i.val.2) :=
    ModuleCat.hom_ext (P103.Ch10.Complexes.homologyMap_comp g g' i.val.2)
  change T.map (P i.val.1) (P'' i.val.1)
      (ModuleCat.ofHom (homologyMap (f ≫ f') i.val.1))
      (ModuleCat.ofHom (homologyMap (g ≫ g') i.val.2)) (x i) = _
  rw [hf, hg]
  exact LinearMap.congr_fun (T.comp (P i.val.1) (P' i.val.1) (P'' i.val.1)
    (ModuleCat.ofHom (homologyMap f i.val.1))
    (ModuleCat.ofHom (homologyMap f' i.val.1))
    (ModuleCat.ofHom (homologyMap g i.val.2))
    (ModuleCat.ofHom (homologyMap g' i.val.2))) (x i)

/-- The Tor comparison squares commute with the actual coefficient scalars. -/
theorem torScalar_natural
    {K : Type u} [CommRing K]
    {C C' : RightComplex.{u,v} K} {D D' : LeftComplex.{u,w} K}
    (f : C ⟶ C') (g : D ⟶ D') (P : HomologyModels C) (P' : HomologyModels C')
    (T : TorMaps.{u,v,w} K 1) (n : ℕ) (r : K) :
    (torScalar C' D' P' T n r).comp (torDiagonalMap f g P P' T n) =
      (torDiagonalMap f g P P' T n).comp (torScalar C D P T n r) := by
  have hg : scalarChainMap D r ≫ g = g ≫ scalarChainMap D' r := by
    ext q x
    exact (g.f q).hom.map_smul r x
  dsimp only [torScalar]
  rw [← torDiagonalMap_comp, ← torDiagonalMap_comp]
  simp only [Category.comp_id, Category.id_comp, hg]

/-- A splitting transports along the three actual comparison maps. The outer
maps are isomorphisms because the factor maps are quasi-isomorphisms; the
short five lemma supplies the middle isomorphism. Coefficient naturality
then preserves linearity of the section. -/
theorem splitsOver_of_natural_comparison
    {K : Type u} [CommRing K]
    {C C' : RightComplex.{u,v} K} {D D' : LeftComplex.{u,w} K}
    (f : C ⟶ C') (g : D ⟶ D') (hf : QuasiIsomorphism f)
    (hg : QuasiIsomorphism g) (P : HomologyModels C) (P' : HomologyModels C')
    (T : TorMaps.{u,v,w} K 1) (n : ℕ)
    (S : DegreeSequence C D P n) (S' : DegreeSequence C' D' P' n)
    (hα : (homologyMap (ordinaryTotalMap f g) n).toAddMonoidHom.toIntLinearMap.comp
        S.α = S'.α.comp (tensorDiagonalMap f g n))
    (hβ : (torDiagonalMap f g P P' T n).comp S.β =
      S'.β.comp (homologyMap (ordinaryTotalMap f g) n).toAddMonoidHom.toIntLinearMap)
    (hS : P103.Specs.Ch11.KunnethSplitting.SplitsOver C D P T n S) :
    P103.Specs.Ch11.KunnethSplitting.SplitsOver C' D' P' T n S' := by
  have hB : Function.Bijective (homologyMap (ordinaryTotalMap f g) n) :=
    middle_bijective (R := ℤ)
      (A := TensorDiagonal C' D' n) (B := Homology (ordinaryTotal C' D') n)
      (T := TorDiagonal C' D' P' n)
      (A' := TensorDiagonal C D n) (B' := Homology (ordinaryTotal C D) n)
      (T' := TorDiagonal C D P n) S'.α S'.β S.α S.β
      (tensorDiagonalMap f g n)
      (homologyMap (ordinaryTotalMap f g) n).toAddMonoidHom.toIntLinearMap
      (torDiagonalMap f g P P' T n) hα hβ.symm
      S'.injective_α S'.exact S.exact S.surjective_β
      (tensorDiagonalMap_bijective f g hf hg n)
      (torDiagonalMap_bijective f g hf hg P P' T n)
  let eB : Homology (ordinaryTotal C D) n ≃ₗ[ℤ] Homology (ordinaryTotal C' D') n :=
    LinearEquiv.ofBijective
      (homologyMap (ordinaryTotalMap f g) n).toAddMonoidHom.toIntLinearMap hB
  let eT : TorDiagonal C D P n ≃ₗ[ℤ] TorDiagonal C' D' P' n :=
    LinearEquiv.ofBijective (torDiagonalMap f g P P' T n)
    (torDiagonalMap_bijective f g hf hg P P' T n)
  obtain ⟨s, hs, hsc, _⟩ := hS
  apply splitsOver_of_scalar_section C' D' P' T n S'
    (eB.toLinearMap.comp (s.comp eT.symm.toLinearMap))
  · exact transport_section (R := ℤ)
      (B := Homology (ordinaryTotal C' D') n) (B' := Homology (ordinaryTotal C D) n)
      (T := TorDiagonal C' D' P' n) (T' := TorDiagonal C D P n)
      eB eT S'.β S.β hβ.symm s hs
  · intro r
    exact transport_section_scalars (R := ℤ)
      (B := Homology (ordinaryTotal C' D') n) (B' := Homology (ordinaryTotal C D) n)
      (T := TorDiagonal C' D' P' n) (T' := TorDiagonal C D P n) eB eT s
      (totalScalar C' D' n r) (totalScalar C D n r)
      (torScalar C' D' P' T n r) (torScalar C D P T n r)
      (totalScalar_natural f g n r) (torScalar_natural f g P P' T n r) (hsc r)

/-- Transport through the first-factor normalized family uses precisely its
specified injection and Tor surjection squares. -/
theorem splitsOver_of_normalized_comparison
    (hn : normalized_naturalType.{u,v,w})
    {K : Type u} [CommRing K]
    {C C' : RightComplex.{u,v} K} {D D' : LeftComplex.{u,w} K}
    (f : C ⟶ C') (g : D ⟶ D') (hf : QuasiIsomorphism f)
    (hg : QuasiIsomorphism g) (P : HomologyModels C) (P' : HomologyModels C')
    (T : TorMaps.{u,v,w} K 1) (n : ℕ)
    (S : NormalizedDegreeSequence C D P n) (S' : NormalizedDegreeSequence C' D' P' n)
    (hS : P103.Specs.Ch11.KunnethSplitting.SplitsOver C D P T n S.toDegreeSequence) :
    P103.Specs.Ch11.KunnethSplitting.SplitsOver C' D' P' T n S'.toDegreeSequence := by
  obtain ⟨hα,hβ⟩ := hn K C C' D D' f g P P' T n S S'
  exact splitsOver_of_natural_comparison f g hf hg P P' T n
    S.toDegreeSequence S'.toDegreeSequence hα hβ hS

/-- The identical transport argument applies to the second-factor family,
so its signed opposite-ring normalization is preserved. -/
theorem splitsOver_of_left_comparison
    {K : Type u} [CommRing K] (L : LeftSequenceFamily.{u,v,w} K)
    {C C' : RightComplex.{u,v} K} {D D' : LeftComplex.{u,w} K}
    (hD : LeftFlatTermsAndBoundaries.{u,v,w} D)
    (hD' : LeftFlatTermsAndBoundaries.{u,v,w} D')
    (f : C ⟶ C') (g : D ⟶ D') (hf : QuasiIsomorphism f)
    (hg : QuasiIsomorphism g) (P : HomologyModels C) (P' : HomologyModels C')
    (T : TorMaps.{u,v,w} K 1) (n : ℕ)
    (hS : P103.Specs.Ch11.KunnethSplitting.SplitsOver C D P T n
      (L.sequence C D hD P n)) :
    P103.Specs.Ch11.KunnethSplitting.SplitsOver C' D' P' T n
      (L.sequence C' D' hD' P' n) := by
  obtain ⟨hα,hβ⟩ := L.naturality C C' D D' hD hD' f g P P' T n
  exact splitsOver_of_natural_comparison f g hf hg P P' T n
    (L.sequence C D hD P n) (L.sequence C' D' hD' P' n) hα hβ hS

/-- All terms and boundaries of a degreewise free PID complex are flat,
without restricting the cardinality of any basis. -/
theorem right_free_flatTermsAndBoundaries
    {K : Type u} [CommRing K] [IsDomain K] [IsPrincipalIdealRing K]
    (C : RightComplex.{u,v} K) (hC : ∀ p, Module.Free Kᵐᵒᵖ (C.X p)) :
    P103.Specs.Ch11.UniversalCoefficientsHomology.FlatTermsAndBoundaries.{u,v,w} C := by
  exact P103.Ch11.KunnethFreeSplitting.free_flat_terms_boundaries C hC

/-- The second-factor version uses the genuine left-module tensor flatness. -/
theorem left_free_flatTermsAndBoundaries
    {K : Type u} [CommRing K] [IsDomain K] [IsPrincipalIdealRing K]
    (D : LeftComplex.{u,w} K) (hD : ∀ q, Module.Free K (D.X q)) :
    LeftFlatTermsAndBoundaries.{u,v,w} D := by
  constructor
  · intro q
    letI := hD q
    exact P103.Ch02.FlatnessTests.projective_flat K (D.X q) inferInstance
  · intro q
    letI := hD q
    letI : Module.Free K (boundaries D q) :=
      P103.Ch11.ArbitraryRankPIDSubmodules.free_submodule K (D.X q) (boundaries D q)
    exact P103.Ch02.FlatnessTests.projective_flat K (boundaries D q) inferInstance

/-- Choose genuine projective models for all homology modules of a replacement.
These are existing proved projective resolutions, not assumed certificates. -/
def chooseHomologyModels (C : RightComplex.{u,v} R) : HomologyModels C := fun p =>
  let h := P103.Ch10.ProjectiveResolutions.exists_projective_resolution Rᵐᵒᵖ (Homology C p)
  ⟨h.choose, h.choose_spec⟩

/-- The identity comparison induces identity homology maps. -/
theorem quasiIsomorphism_identity
    {S : Type*} [Ring S] (C : ChainComplex (ModuleCat.{v} S) ℕ) :
    QuasiIsomorphism (𝟙 C) := by
  intro n
  have h : homologyMap (𝟙 C) n = LinearMap.id := P103.Ch10.Complexes.homologyMap_id C n
  rw [h]
  exact Function.bijective_id

open P103.Specs.Ch11.KunnethSplitting

theorem extend_subsingleton {R : Type u} [Ring R]
    (D : ChainComplex (ModuleCat.{w} R) ℕ)
    (hD : ∀ q, Subsingleton (D.X q)) (q : ℤ) :
    Subsingleton ((extendNonnegativeChain D).X q) := by
  by_cases hq : 0 ≤ q
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    letI := hD q
    exact ModuleCat.subsingleton_of_isZero
      ((ModuleCat.isZero_of_subsingleton (D.X q)).of_iso
        (D.extendXIso nonnegativeChainEmbedding (i := q) rfl))
  · exact ModuleCat.subsingleton_of_isZero
      (D.isZero_extend_X nonnegativeChainEmbedding q (by
        intro i h
        change (i : ℤ) = q at h
        omega))

theorem total_subsingleton_right {R : Type u} [Ring R]
    (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (hD : ∀ q, Subsingleton (D.X q)) (n : ℕ) :
    Subsingleton ((ordinaryTotal C D).X n) := by
  let K := tensorBicomplex (extendNonnegativeChain C) (extendNonnegativeChain D)
  have hK (i : {i : ℤ × ℤ // i.1 + i.2 = (n : ℤ)}) :
      Subsingleton ((K.X i.val.1).X i.val.2) := by
    letI := extend_subsingleton D hD i.val.2
    change Subsingleton (Tensor R _ _)
    infer_instance
  letI := hK
  exact (P103.Specs.Ch10.TotalComplexAssembly.totalTermEquiv K n).injective.subsingleton

theorem total_subsingleton_left {R : Type u} [Ring R]
    (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (hC : ∀ p, Subsingleton (C.X p)) (n : ℕ) :
    Subsingleton ((ordinaryTotal C D).X n) := by
  let K := tensorBicomplex (extendNonnegativeChain C) (extendNonnegativeChain D)
  have hK (i : {i : ℤ × ℤ // i.1 + i.2 = (n : ℤ)}) :
      Subsingleton ((K.X i.val.1).X i.val.2) := by
    letI := extend_subsingleton C hC i.val.1
    change Subsingleton (Tensor R _ _)
    infer_instance
  letI := hK
  exact (P103.Specs.Ch10.TotalComplexAssembly.totalTermEquiv K n).injective.subsingleton

theorem zero_splitsOver {R : Type u} [CommRing R]
    (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (P : HomologyModels C) (T : TorMaps.{u,v,w} R 1) (n : ℕ)
    (S : DegreeSequence C D P n)
    [Subsingleton ((ordinaryTotal C D).X n)] : SplitsOver C D P T n S := by
  letI : Subsingleton (Homology (ordinaryTotal C D) n) := inferInstance
  letI : Subsingleton (TensorDiagonal C D n) := S.injective_α.subsingleton
  letI : Subsingleton (TorDiagonal C D P n) := S.surjective_β.subsingleton
  refine ⟨0, ?_, ?_, LinearEquiv.ofSubsingleton (R := ℤ) _ _, ?_, ?_⟩
  · exact Subsingleton.elim _ _
  · intro r; exact Subsingleton.elim _ _
  · intro a t; exact Subsingleton.elim _ _
  · intro a t; exact Subsingleton.elim _ _

section UniverseControl
variable {K : Type u} [CommRing K] [IsDomain K] [IsPrincipalIdealRing K]

/-- Adic digits compress a PID into countably many residue classes. -/
theorem small_of_small_quotient (I : Ideal K) (hI : I ≠ ⊤)
    [Small.{v} (K ⧸ I)] : Small.{v} K := by
  classical
  let a := Submodule.IsPrincipal.generator I
  let q : K → K ⧸ I := Ideal.Quotient.mk I
  let rep : K ⧸ I → K := Quotient.out
  have hdiv (r : K) : ∃ z : K, r = rep (q r) + a * z := by
    have hm : r - rep (q r) ∈ I := Ideal.Quotient.eq.mp (by
      exact (Ideal.Quotient.mk_out (q r)).symm)
    obtain ⟨z, hz⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator I).mp hm
    refine ⟨z, ?_⟩
    change r - rep (q r) = z * a at hz
    calc
      r = rep (q r) + (r - rep (q r)) := by ring
      _ = rep (q r) + a * z := by rw [hz, mul_comm z a]
  let δ : K → K := fun r => (hdiv r).choose
  have hδ (r : K) : r = rep (q r) + a * δ r := (hdiv r).choose_spec
  let digits : K → ℕ → K ⧸ I := fun r n => q (δ^[n] r)
  apply small_of_injective (f := digits)
  intro r s hrs
  have heq (n : ℕ) : r - s = a ^ n * (δ^[n] r - δ^[n] s) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hq : q (δ^[n] r) = q (δ^[n] s) := congrFun hrs n
      have hnext : δ^[n] r - δ^[n] s =
          a * (δ (δ^[n] r) - δ (δ^[n] s)) := by
        calc
          _ = (rep (q (δ^[n] r)) + a * δ (δ^[n] r)) -
            (rep (q (δ^[n] s)) + a * δ (δ^[n] s)) := by
              rw [← hδ (δ^[n] r), ← hδ (δ^[n] s)]
          _ = _ := by rw [hq]; ring
      rw [ih, hnext, pow_succ, Function.iterate_succ_apply',
        Function.iterate_succ_apply']
      ring
  have hm : r - s ∈ ⨅ n : ℕ, I ^ n := by
    apply Ideal.mem_iInf.mpr
    intro n
    rw [← Ideal.span_singleton_generator I, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    exact ⟨δ^[n] r - δ^[n] s, heq n⟩
  rw [Ideal.iInf_pow_eq_bot_of_isDomain I hI] at hm
  exact sub_eq_zero.mp hm

/-- Every nonzero module over a PID controls the universe of the ring. -/
theorem small_of_nontrivial_module (M : Type v) [AddCommGroup M] [Module K M]
    [Nontrivial M] : Small.{v} K := by
  classical
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  let f : K →ₗ[K] M := LinearMap.toSpanSingleton K M x
  let I : Ideal K := LinearMap.ker f
  have hI : I ≠ ⊤ := by
    intro h
    have : (1 : K) ∈ I := h ▸ Submodule.mem_top
    have : f 1 = 0 := this
    exact hx (by simpa [f] using this)
  letI : Small.{v} (K ⧸ I) := small_of_injective
    (f := fun z : K ⧸ I => ((LinearMap.quotKerEquivRange f z) : M))
    (Subtype.val_injective.comp (LinearMap.quotKerEquivRange f).injective)
  exact small_of_small_quotient I hI


theorem small_or_zero_right (C : RightComplex.{u,v} K) :
    Small.{v} K ∨ ∀ p, Subsingleton (C.X p) := by
  classical
  by_cases h : Small.{v} K
  · exact Or.inl h
  · refine Or.inr (fun p => ?_)
    rcases subsingleton_or_nontrivial (C.X p) with hs | hn
    · exact hs
    · letI := hn
      letI : IsPrincipalIdealRing Kᵐᵒᵖ := IsPrincipalIdealRing.of_surjective
        (RingEquiv.toOpposite K).toRingHom (RingEquiv.toOpposite K).surjective
      letI : Small.{v} Kᵐᵒᵖ := small_of_nontrivial_module (K := Kᵐᵒᵖ) (C.X p)
      exact (h (small_of_injective (f := MulOpposite.op) MulOpposite.op_injective)).elim

theorem small_or_zero_left (D : LeftComplex.{u,w} K) :
    Small.{w} K ∨ ∀ q, Subsingleton (D.X q) := by
  classical
  by_cases h : Small.{w} K
  · exact Or.inl h
  · refine Or.inr (fun q => ?_)
    rcases subsingleton_or_nontrivial (D.X q) with hs | hn
    · exact hs
    · letI := hn
      exact (h (small_of_nontrivial_module (K := K) (D.X q))).elim

end UniverseControl

namespace SmallReplacement
universe r s t z
variable {S : Type r} [Ring S]


def cyclesEquiv (C : ChainComplex (ModuleCat.{s} S) ℕ)
    (D : ChainComplex (ModuleCat.{t} S) ℕ)
    (e : ∀ n, C.X n ≃ₗ[S] D.X n)
    (h : ∀ i j x, e j ((C.d i j).hom x) = (D.d i j).hom (e i x))
    (n : ℕ) : cycles C n ≃ₗ[S] cycles D n where
  toFun z := ⟨e n z.val, by
    change (D.d n _).hom (e n z.val) = 0
    rw [← h, show (C.d n _).hom z.val = 0 from z.property, map_zero]⟩
  invFun z := ⟨(e n).symm z.val, by
    change (C.d n _).hom ((e n).symm z.val) = 0
    apply (e _).injective
    rw [h, LinearEquiv.apply_symm_apply, show (D.d n _).hom z.val = 0 from z.property,
      map_zero]⟩
  left_inv z := by apply Subtype.ext; exact (e n).symm_apply_apply z.val
  right_inv z := by apply Subtype.ext; exact (e n).apply_symm_apply z.val
  map_add' _ _ := by apply Subtype.ext; exact map_add _ _ _
  map_smul' _ _ := by apply Subtype.ext; exact map_smul _ _ _

theorem cycleBoundaries_map (C : ChainComplex (ModuleCat.{s} S) ℕ)
    (D : ChainComplex (ModuleCat.{t} S) ℕ)
    (e : ∀ n, C.X n ≃ₗ[S] D.X n)
    (h : ∀ i j x, e j ((C.d i j).hom x) = (D.d i j).hom (e i x))
    (n : ℕ) : (cycleBoundaries C n).map (cyclesEquiv C D e h n).toLinearMap =
      cycleBoundaries D n := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x, hx⟩ := hz
    refine ⟨e _ x, ?_⟩
    change (D.d _ n).hom (e _ x) = e n z.val
    rw [← h, hx]
    rfl
  · intro hy
    obtain ⟨x, hx⟩ := hy
    refine ⟨(cyclesEquiv C D e h n).symm y, ?_, by simp⟩
    refine ⟨(e _).symm x, ?_⟩
    change (C.d _ n).hom ((e _).symm x) = (e n).symm y.val
    apply (e n).injective
    rw [h, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hx]
    rfl

def homologyEquiv (C : ChainComplex (ModuleCat.{s} S) ℕ)
    (D : ChainComplex (ModuleCat.{t} S) ℕ)
    (e : ∀ n, C.X n ≃ₗ[S] D.X n)
    (h : ∀ i j x, e j ((C.d i j).hom x) = (D.d i j).hom (e i x))
    (n : ℕ) : Homology C n ≃ₗ[S] Homology D n :=
  Submodule.Quotient.equiv _ _ (cyclesEquiv C D e h n) (cycleBoundaries_map C D e h n)

@[simp] theorem homologyEquiv_class (C : ChainComplex (ModuleCat.{s} S) ℕ)
    (D : ChainComplex (ModuleCat.{t} S) ℕ)
    (e : ∀ n, C.X n ≃ₗ[S] D.X n)
    (h : ∀ i j x, e j ((C.d i j).hom x) = (D.d i j).hom (e i x))
    (n : ℕ) (z : cycles C n) :
    homologyEquiv C D e h n (homologyClass C n z) =
      homologyClass D n (cyclesEquiv C D e h n z) := rfl

theorem quasi_of_pointwise_equiv
    {C D : ChainComplex (ModuleCat.{s} S) ℕ}
    {C' D' : ChainComplex (ModuleCat.{t} S) ℕ}
    (f : C ⟶ D) (g : C' ⟶ D')
    (a : ∀ n, C.X n ≃ₗ[S] C'.X n) (b : ∀ n, D.X n ≃ₗ[S] D'.X n)
    (ha : ∀ i j x, a j ((C.d i j).hom x) = (C'.d i j).hom (a i x))
    (hb : ∀ i j x, b j ((D.d i j).hom x) = (D'.d i j).hom (b i x))
    (hf : ∀ n x, b n ((f.f n).hom x) = (g.f n).hom (a n x))
    (hg : QuasiIsomorphism g) : QuasiIsomorphism f := by
  intro n
  let aH := homologyEquiv C C' a ha n
  let bH := homologyEquiv D D' b hb n
  have hs (x : Homology C n) : bH (homologyMap f n x) = homologyMap g n (aH x) := by
    obtain ⟨z, rfl⟩ := (cycleBoundaries C n).mkQ_surjective x
    change homologyClass D' n (cyclesEquiv D D' b hb n (cyclesMap f n z)) =
      homologyClass D' n (cyclesMap g n (cyclesEquiv C C' a ha n z))
    congr 1
    apply Subtype.ext
    exact hf n z.val
  constructor
  · intro x y hxy
    apply aH.injective
    apply (hg n).1
    rw [← hs, ← hs, hxy]
  · intro y
    obtain ⟨x, hx⟩ := (hg n).2 (bH y)
    refine ⟨aH.symm x, bH.injective ?_⟩
    rw [hs, LinearEquiv.apply_symm_apply, hx]

def transportComplex (C : ChainComplex (ModuleCat.{t} S) ℕ)
    (X : ℕ → ModuleCat.{s} S) (e : ∀ n, X n ≃ₗ[S] C.X n) :
    ChainComplex (ModuleCat.{s} S) ℕ where
  X := X
  d i j := ModuleCat.ofHom ((e j).symm.toLinearMap.comp ((C.d i j).hom.comp (e i).toLinearMap))
  shape i j h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (e j).symm ((C.d i j).hom (e i x)) = 0
    rw [C.shape i j h]
    simp
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (e k).symm ((C.d j k).hom (e j ((e j).symm ((C.d i j).hom (e i x))))) = 0
    rw [LinearEquiv.apply_symm_apply]
    have h := congrArg (fun f => f.hom (e i x)) (C.d_comp_d i j k)
    change (C.d j k).hom ((C.d i j).hom (e i x)) = 0 at h
    rw [h, map_zero]

theorem transportComplex_comm (C : ChainComplex (ModuleCat.{t} S) ℕ)
    (X : ℕ → ModuleCat.{s} S) (e : ∀ n, X n ≃ₗ[S] C.X n) (i j : ℕ) (x : X i) :
    e j (((transportComplex C X e).d i j).hom x) = (C.d i j).hom (e i x) :=
  (e j).apply_symm_apply _

def transferMap
    {C D : ChainComplex (ModuleCat.{s} S) ℕ}
    {C' D' : ChainComplex (ModuleCat.{t} S) ℕ}
    (g : C' ⟶ D')
    (a : ∀ n, C.X n ≃ₗ[S] C'.X n) (b : ∀ n, D.X n ≃ₗ[S] D'.X n)
    (ha : ∀ i j x, a j ((C.d i j).hom x) = (C'.d i j).hom (a i x))
    (hb : ∀ i j x, b j ((D.d i j).hom x) = (D'.d i j).hom (b i x)) : C ⟶ D where
  f n := ModuleCat.ofHom ((b n).symm.toLinearMap.comp (((g.f n).hom).comp (a n).toLinearMap))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (D.d i j).hom ((b i).symm ((g.f i).hom (a i x))) =
      (b j).symm ((g.f j).hom (a j ((C.d i j).hom x)))
    apply (b j).injective
    rw [hb, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, ha]
    exact congrArg (fun f => f.hom (a i x)) (g.comm i j)

theorem transferMap_quasi
    {C D : ChainComplex (ModuleCat.{s} S) ℕ}
    {C' D' : ChainComplex (ModuleCat.{t} S) ℕ}
    (g : C' ⟶ D')
    (a : ∀ n, C.X n ≃ₗ[S] C'.X n) (b : ∀ n, D.X n ≃ₗ[S] D'.X n)
    (ha : ∀ i j x, a j ((C.d i j).hom x) = (C'.d i j).hom (a i x))
    (hb : ∀ i j x, b j ((D.d i j).hom x) = (D'.d i j).hom (b i x))
    (hg : QuasiIsomorphism g) : QuasiIsomorphism (transferMap g a b ha hb) := by
  apply quasi_of_pointwise_equiv _ g a b ha hb _ hg
  intro n x
  exact (b n).apply_symm_apply _

open P103.Ch11.FreeComplexReplacement

private instance finsuppSmall {α : Type*} [Small.{s} α] [Small.{s} S] :
    Small.{s} (α →₀ S) :=
  small_of_injective (f := fun x : α →₀ S => (x : α → S)) DFunLike.coe_injective

theorem replacement_small (D : ChainComplex (ModuleCat.{max r s} S) ℕ)
    [Small.{s} S] [∀ n, Small.{s} (D.X n)] (n : ℕ) :
    Small.{s} ((replacementComplex D).X n) := by
  change Small.{s} ((stages D n).X)
  induction n with
  | zero =>
    change Small.{s} (D.X 0 →₀ S)
    infer_instance
  | succ n ih =>
    letI : Small.{s} ((stages D n).X) := ih
    change Small.{s} (matching D (stages D n) →₀ S)
    infer_instance

theorem exists_free_replacement_small [Small.{s} S]
    (D : ChainComplex (ModuleCat.{s} S) ℕ) :
    ∃ (Q : ChainComplex (ModuleCat.{s} S) ℕ) (f : Q ⟶ D),
      (∀ n, Module.Free S (Q.X n)) ∧ QuasiIsomorphism f := by
  let D' : ChainComplex (ModuleCat.{max r s} S) ℕ :=
    transportComplex D (fun n => ModuleCat.of S (ULift.{r} (D.X n)))
      (fun _ => ULift.moduleEquiv)
  let b : ∀ n, D.X n ≃ₗ[S] D'.X n := fun n => ULift.moduleEquiv.symm
  have hb : ∀ i j x, b j ((D.d i j).hom x) = (D'.d i j).hom (b i x) := by
    intro i j x
    rfl
  letI (n : ℕ) : Small.{s} (D'.X n) :=
    small_of_injective (f := (b n).symm) (b n).symm.injective
  let Q' := replacementComplex D'
  letI (n : ℕ) : Small.{s} (Q'.X n) := replacement_small D' n
  let X : ℕ → ModuleCat.{s} S := fun n => ModuleCat.of S (Shrink.{s} (Q'.X n))
  let a : ∀ n, X n ≃ₗ[S] Q'.X n := fun n => Shrink.linearEquiv S (Q'.X n)
  let Q := transportComplex Q' X a
  have ha : ∀ i j x, a j ((Q.d i j).hom x) = (Q'.d i j).hom (a i x) :=
    transportComplex_comm Q' X a
  refine ⟨Q, transferMap (replacementMap D') a b ha hb, ?_, ?_⟩
  · intro n
    haveI := replacement_free D' n
    exact Module.Free.of_equiv (a n).symm
  · exact transferMap_quasi (C := Q) (D := D) (C' := Q') (D' := D')
      (replacementMap D') a b ha hb (replacement_quasiIsomorphism D')

end SmallReplacement

/-- Transfer of the both-free splitting through replacements in the original
module universes. The zero-complex cases remove any size restriction on the ring. -/
theorem one_free_normalized_splitsOver
    (hr : right_sequenceType.{u,v,w})
    (hn : normalized_naturalType.{u,v,w})
    {K : Type u} [CommRing K] [IsDomain K] [IsPrincipalIdealRing K]
    (C : RightComplex.{u,v} K) (D : LeftComplex.{u,w} K)
    (hfree : P103.Specs.Ch11.KunnethSplitting.OneFree C D)
    (P : HomologyModels C) (T : TorMaps.{u,v,w} K 1) (n : ℕ)
    (S : NormalizedDegreeSequence C D P n) :
    P103.Specs.Ch11.KunnethSplitting.SplitsOver C D P T n S.toDegreeSequence := by
  rcases small_or_zero_right C with hsmallC | hzeroC
  · letI := hsmallC
    letI : Small.{v} Kᵐᵒᵖ :=
      small_of_injective (f := MulOpposite.unop) MulOpposite.unop_injective
    rcases small_or_zero_left D with hsmallD | hzeroD
    · letI := hsmallD
      rcases hfree with hC | hD
      · obtain ⟨Q, f, hQfree, hQiso⟩ := SmallReplacement.exists_free_replacement_small D
        obtain ⟨N⟩ := hr K C (right_free_flatTermsAndBoundaries C hC) Q P n
        have hN := both_free_normalized_splitsOver hn C Q hC hQfree P T n N
        exact splitsOver_of_normalized_comparison hn (𝟙 C) f
          (quasiIsomorphism_identity C) hQiso P P T n N S hN
      · obtain ⟨Q, f, hQfree, hQiso⟩ := SmallReplacement.exists_free_replacement_small C
        let P' := chooseHomologyModels Q
        obtain ⟨N⟩ := hr K Q (right_free_flatTermsAndBoundaries Q hQfree) D P' n
        have hN := both_free_normalized_splitsOver hn Q D hQfree hD P' T n N
        exact splitsOver_of_normalized_comparison hn f (𝟙 D)
          hQiso (quasiIsomorphism_identity D) P' P T n N S hN
    · letI := total_subsingleton_right C D hzeroD n
      exact zero_splitsOver C D P T n S.toDegreeSequence
  · letI := total_subsingleton_left C D hzeroC n
    exact zero_splitsOver C D P T n S.toDegreeSequence

/-- The same transfer preserves the actual second-factor family's arrows,
including its prescribed opposite-ring normalization and coefficient scalars. -/
theorem one_free_left_splitsOver
    {K : Type u} [CommRing K] [IsDomain K] [IsPrincipalIdealRing K]
    (L : LeftSequenceFamily.{u,v,w} K)
    (C : RightComplex.{u,v} K) (D : LeftComplex.{u,w} K)
    (hD : LeftFlatTermsAndBoundaries.{u,v,w} D)
    (hfree : P103.Specs.Ch11.KunnethSplitting.OneFree C D)
    (P : HomologyModels C) (T : TorMaps.{u,v,w} K 1) (n : ℕ) :
    P103.Specs.Ch11.KunnethSplitting.SplitsOver C D P T n (L.sequence C D hD P n) := by
  rcases small_or_zero_right C with hsmallC | hzeroC
  · letI := hsmallC
    letI : Small.{v} Kᵐᵒᵖ :=
      small_of_injective (f := MulOpposite.unop) MulOpposite.unop_injective
    rcases small_or_zero_left D with hsmallD | hzeroD
    · letI := hsmallD
      rcases hfree with hCfree | hDfree
      · obtain ⟨Q, f, hQfree, hQiso⟩ := SmallReplacement.exists_free_replacement_small D
        have hQflat : LeftFlatTermsAndBoundaries.{u,v,w} Q :=
          left_free_flatTermsAndBoundaries Q hQfree
        have hN := both_free_left_splitsOver L C Q hQflat hCfree hQfree P T n
        exact splitsOver_of_left_comparison L hQflat hD (𝟙 C) f
          (quasiIsomorphism_identity C) hQiso P P T n hN
      · obtain ⟨Q, f, hQfree, hQiso⟩ := SmallReplacement.exists_free_replacement_small C
        let P' := chooseHomologyModels Q
        have hN := both_free_left_splitsOver L Q D hD hQfree hDfree P' T n
        exact splitsOver_of_left_comparison L hD hD f (𝟙 D)
          hQiso (quasiIsomorphism_identity D) P' P T n hN
    · letI := total_subsingleton_right C D hzeroD n
      exact zero_splitsOver C D P T n (L.sequence C D hD P n)
  · letI := total_subsingleton_left C D hzeroC n
    exact zero_splitsOver C D P T n (L.sequence C D hD P n)

/-- The full first-factor Künneth sequence splits over a PID whenever either
complex is degreewise free, with arbitrary rank and the prescribed maps. -/
theorem right_splitting :
    P103.Specs.Ch11.KunnethSplitting.right_splittingType.{u,v,w} := by
  refine ⟨P103.Ch11.KunnethSequence.right_sequence,
    P103.Ch11.KunnethSequence.normalized_natural,
    P103.Ch11.KunnethSequence.scalar_compatibility, ?_⟩
  intro K _ _ _ C D _hflat hfree P T n S
  exact one_free_normalized_splitsOver P103.Ch11.KunnethSequence.right_sequence
    P103.Ch11.KunnethSequence.normalized_natural C D hfree P T n S

/-- The same one-free splitting for the natural second-factor sequence,
retaining its signed opposite-ring normalization and coefficient action. -/
theorem left_splitting :
    P103.Specs.Ch11.KunnethSplitting.left_splittingType.{u,v,w} := by
  refine ⟨P103.Ch11.KunnethSequence.left_natural_sequence,
    P103.Ch11.KunnethSequence.scalar_compatibility, ?_⟩
  intro K _ _ _ L C D hD hfree P T n
  exact one_free_left_splitsOver L C D hD hfree P T n

end
end P103.Ch11.KunnethSplitting
