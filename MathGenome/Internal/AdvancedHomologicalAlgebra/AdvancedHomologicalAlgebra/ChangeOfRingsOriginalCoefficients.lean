import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ChangeOfRingsOriginalCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ChangeOfRingsTor
import MathGenome.Internal.AlgebraCore.P103.Ch10.Comparison
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.AlgebraCore.P103.Ch10.ProjectiveResolutions

noncomputable section

open CategoryTheory
open P103.Specs.Ch10 P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.BalancedTensor

namespace AdvancedHomologicalAlgebra.ChangeOfRingsOriginalCoefficients

universe u v w x y z i

namespace TermIso

variable {R : Type u} [Ring R] {I : Type i} {c : ComplexShape I}
variable {C : HomologicalComplex (ModuleCat.{v} R) c}
variable {D : HomologicalComplex (ModuleCat.{w} R) c}

def homology (e : TermIso C D) (n : I) : Homology C n ≃ₗ[R] Homology D n where
  __ := e.hom.homologyMap n
  invFun := e.symm.hom.homologyMap n
  left_inv := by
    intro z
    obtain ⟨a, rfl⟩ := (cycleBoundaries C n).mkQ_surjective z
    change homologyClass C n _ = homologyClass C n a
    congr 1
    exact Subtype.ext ((e.app n).symm_apply_apply a.val)
  right_inv := by
    intro z
    obtain ⟨a, rfl⟩ := (cycleBoundaries D n).mkQ_surjective z
    change homologyClass D n _ = homologyClass D n a
    congr 1
    exact Subtype.ext ((e.app n).apply_symm_apply a.val)

theorem homology_class (e : TermIso C D) (n : I) (a : Complexes.cycles C n) :
    e.homology n (homologyClass C n a) = homologyClass D n (e.hom.cyclesMap n a) := rfl

end TermIso

section Lifting

variable {R : Type u} [Ring R]
variable {A : Type v} [AddCommGroup A] [Module R A]

private theorem exact_conjugate
    {A₀ : Type*} {A₁ : Type*} {A₂ : Type*}
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
    [Module R A₀] [Module R A₁] [Module R A₂]
    {B₀ : Type*} {B₁ : Type*} {B₂ : Type*}
    [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    [Module R B₀] [Module R B₁] [Module R B₂]
    (a : A₀ ≃ₗ[R] B₀) (b : A₁ ≃ₗ[R] B₁) (c : A₂ ≃ₗ[R] B₂)
    (f : A₀ →ₗ[R] A₁) (g : A₁ →ₗ[R] A₂)
    (h : LinearMap.range f = LinearMap.ker g) :
    LinearMap.range (b.toLinearMap.comp (f.comp a.symm.toLinearMap)) =
      LinearMap.ker (c.toLinearMap.comp (g.comp b.symm.toLinearMap)) := by
  ext z
  obtain ⟨z, rfl⟩ := b.surjective z
  simp only [LinearMap.mem_range, LinearMap.mem_ker, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, EmbeddingLike.map_eq_zero_iff]
  change (∃ y, b (f (a.symm y)) = b z) ↔ g z = 0
  rw [← LinearMap.mem_ker, ← h, LinearMap.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨a.symm y, b.injective hy⟩
  · rintro ⟨y, rfl⟩
    exact ⟨a y, by rw [a.symm_apply_apply]⟩

/-- Lift the terms and transport the augmentation along a specified equivalence.
The target can also be a Tor module that is already in the large universe. -/
def liftResolutionAlong {B : Type (max w z)} [AddCommGroup B] [Module R B]
    (P : AugmentedResolution.{u,v,w} R A) (e : A ≃ₗ[R] B) : LeftResolution R B where
  complex := liftComplex.{u,w,max u z,0} P.complex
  ε := e.toLinearMap.comp (P.ε.comp ULift.moduleEquiv.toLinearMap)
  surjective b := by
    obtain ⟨a, rfl⟩ := e.surjective b
    obtain ⟨p, hp⟩ := P.surjective a
    exact ⟨ULift.up p, congrArg e hp⟩
  exact_zero := exact_conjugate (carrierUp R (P.complex.X 1))
    (carrierUp R (P.complex.X 0)) e _ _ P.exact_zero
  exact_succ n := exact_conjugate (carrierUp R (P.complex.X (n + 2)))
    (carrierUp R (P.complex.X (n + 1))) (carrierUp R (P.complex.X n))
    _ _ (P.exact_succ n)

theorem liftResolutionAlong_projective {B : Type (max w z)} [AddCommGroup B] [Module R B]
    (P : AugmentedResolution.{u,v,w} R A) (e : A ≃ₗ[R] B) :
    (liftResolutionAlong.{u,v,w,z} P e).IsProjective := by
  intro n
  change Module.Projective R (ULift.{max u z} (P.complex.X n))
  let := P.projective n
  infer_instance

/-- Every original independently sized module admits an augmented projective resolution. -/
theorem resolution_existence : ResolutionExistenceType.{u,v,z} := by
  intro R _ A _ _
  obtain ⟨P, hP⟩ := P103.Ch10.ProjectiveResolutions.exists_projective_resolution R (ULift.{z} A)
  let e : ULift.{z} A ≃ₗ[R] A := ULift.moduleEquiv
  exact ⟨{ complex := P.complex
           ε := e.toLinearMap.comp P.ε
           surjective := e.surjective.comp P.surjective
           exact_zero := by
             rw [P.exact_zero]
             ext a
             change P.ε a = 0 ↔ (P.ε a).down = 0
             exact ⟨fun h => congrArg ULift.down h, fun h => ULift.ext h⟩
           exact_succ := P.exact_succ
           projective := hP }⟩

/-- The exact carrier lift preserves the augmentation and termwise projectivity. -/
theorem resolution_lift : ResolutionLiftType.{u,v,w,z} := by
  intro R _ A _ _ P
  let e := carrierUp.{u,v,max u w z} R A
  exact ⟨⟨liftResolutionAlong.{u,v,w,max u v z} P e, rfl, fun _ => rfl,
    liftResolutionAlong_projective P e⟩⟩

end Lifting

section Tensor

variable {R : Type u} [Ring R] {A : Type v} {B : Type w} {A' : Type x} {B' : Type y}
variable [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup A'] [Module Rᵐᵒᵖ A']
variable [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']

/-- Simultaneous scalar-preserving carrier equivalences on two tensor factors. -/
def tensorEquiv (a : A ≃ₗ[Rᵐᵒᵖ] A') (b : B ≃ₗ[R] B') :
    Tensor R A B ≃ₗ[ℤ] Tensor R A' B' where
  __ := tensorMap a.toLinearMap b.toLinearMap
  invFun := tensorMap a.symm.toLinearMap b.symm.toLinearMap
  left_inv := by
    intro t
    have h := tensor_hom_ext
      ((tensorMap a.symm.toLinearMap b.symm.toLinearMap).comp
        (tensorMap a.toLinearMap b.toLinearMap))
      LinearMap.id (fun x y => by
        change tmul R (a.symm (a x)) (b.symm (b y)) = tmul R x y
        rw [a.symm_apply_apply, b.symm_apply_apply])
    exact LinearMap.congr_fun h t
  right_inv := by
    intro t
    have h := tensor_hom_ext
      ((tensorMap a.toLinearMap b.toLinearMap).comp
        (tensorMap a.symm.toLinearMap b.symm.toLinearMap))
      LinearMap.id (fun x y => by
        change tmul R (a (a.symm x)) (b (b.symm y)) = tmul R x y
        rw [a.apply_symm_apply, b.apply_symm_apply])
    exact LinearMap.congr_fun h t

theorem tensor_equiv : TensorEquivType.{u,v,w,x,y} := by
  intro R _ A B A' B' _ _ _ _ _ _ _ _ a b
  exact ⟨tensorEquiv a b, fun _ _ => rfl, fun _ _ => rfl⟩

end Tensor

section Comparison

variable {R : Type u} [Ring R] {I : Type i} {c : ComplexShape I}
variable {C : HomologicalComplex (ModuleCat.{v} R) c}
variable {D : HomologicalComplex (ModuleCat.{w} R) c}
variable {C' D' : HomologicalComplex (ModuleCat.{x} R) c}

/-- Conjugate a map into a common module category using the term equivalences. -/
def conjugateChainMap (e : TermIso C C') (e' : TermIso D D')
    (l : TermMap C D) : C' ⟶ D' :=
  TermMap.toHom (TermMap.comp e'.hom (TermMap.comp l e.symm.hom))

theorem conjugateChainMap_apply (e : TermIso C C') (e' : TermIso D D')
    (l : TermMap C D) (n : I) (a : C.X n) :
    ((conjugateChainMap e e' l).f n).hom (e.app n a) = e'.app n (l.app n a) := by
  change e'.app n (l.app n ((e.app n).symm (e.app n a))) = _
  rw [LinearEquiv.symm_apply_apply]

end Comparison

section AugmentedMaps

variable {R : Type u} [Ring R] {A : Type v} {B : Type w}
variable [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

theorem AugmentedResolution.exists_lift
    (P : AugmentedResolution.{u,v,x} R A) (Q : AugmentedResolution.{u,w,y} R B)
    (f : A →ₗ[R] B) :
    ∃ l : TermMap P.complex Q.complex, P.Lifts Q f l := by
  let a := carrierUp.{u,v,max u w x y} R A
  let b := carrierUp.{u,w,max u v x y} R B
  let L := liftResolutionAlong.{u,v,x,max u v w y} P a
  let L' := liftResolutionAlong.{u,w,y,max u v w x} Q b
  obtain ⟨l, hl⟩ := P103.Ch10.Comparison.chain_exists R _ _ L L'
    (liftResolutionAlong_projective P a) (conjugate f a b)
  let e : TermIso P.complex L.complex := liftComplexIso P.complex
  let e' : TermIso Q.complex L'.complex := liftComplexIso Q.complex
  refine ⟨TermMap.comp e'.symm.hom (TermMap.comp (TermMap.ofHom l) e.hom), ?_⟩
  intro p
  exact congrArg ULift.down (LinearMap.congr_fun hl (ULift.up p))

end AugmentedMaps



section TensorComplex

variable {R : Type u} [Ring R] {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable {C : ChainComplex (ModuleCat.{x} Rᵐᵒᵖ) ℕ}
variable {D : ChainComplex (ModuleCat.{y} Rᵐᵒᵖ) ℕ}

/-- The quotient Tor comparison comes from a term equivalence on the original
balanced tensor complexes. -/
def tensorComplexIso (e : TermIso C D) (b : M ≃ₗ[R] N) :
    TermIso (tensorComplex C M) (tensorComplex D N) where
  app n := tensorEquiv (e.app n) b
  comm m n := by
    have h : ((tensorComplex D N).d m n).hom.comp (tensorEquiv (e.app m) b).toLinearMap =
        (tensorEquiv (e.app n) b).toLinearMap.comp ((tensorComplex C M).d m n).hom := by
      apply tensor_hom_ext
      intro a t
      change tmul R ((D.d m n).hom (e.app m a)) (b t) =
        tmul R (e.app n ((C.d m n).hom a)) (b t)
      rw [e.comm]
    exact LinearMap.congr_fun h

end TensorComplex

section Total

open P103.Specs.Ch11.TorBalance
open private ordinaryTotalChainMap ordinaryTotalChainMap_inclusion ordinaryTotalLinear_ext
  from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.TorBalance

variable {R : Type u} [Ring R]
variable {C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ}
variable {D : ChainComplex (ModuleCat.{w} R) ℕ}
variable {C' : ChainComplex (ModuleCat.{x} Rᵐᵒᵖ) ℕ}
variable {D' : ChainComplex (ModuleCat.{y} R) ℕ}

private theorem totalInverse
    (a : TermIso C C') (b : TermIso D D') (n : ℕ) :
    ((ordinaryTotalChainMap a.symm.hom b.symm.hom).app n).comp
      ((ordinaryTotalChainMap a.hom b.hom).app n) = LinearMap.id := by
  apply ordinaryTotalLinear_ext C D n
  intro i j h x y
  simp only [LinearMap.comp_apply, ordinaryTotalChainMap_inclusion, LinearMap.id_apply]
  change ordinaryInclusion C D i j n h
      (tmul R ((a.app i).symm (a.app i x)) ((b.app j).symm (b.app j y))) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

/-- On the signed total, the tensor comparison is computed summand by summand. -/
def signedTotalIso (a : TermIso C C') (b : TermIso D D') :
    TermIso (ordinaryTotal C D) (ordinaryTotal C' D') where
  app n := LinearEquiv.ofLinearMap ((ordinaryTotalChainMap a.hom b.hom).app n)
    ((ordinaryTotalChainMap a.symm.hom b.symm.hom).app n)
    (totalInverse a.symm b.symm n) (totalInverse a b n)
  comm m n := TermMap.comm_apply (ordinaryTotalChainMap a.hom b.hom) m n

theorem signedTotalIso_on_tensor (a : TermIso C C') (b : TermIso D D')
    (i j n : ℕ) (h : i + j = n) (x : C.X i) (y : D.X j) :
    (signedTotalIso a b).app n (ordinaryInclusion C D i j n h (tmul R x y)) =
      ordinaryInclusion C' D' i j n h (tmul R (a.app i x) (b.app j y)) :=
  ordinaryTotalChainMap_inclusion a.hom b.hom i j n h x y

theorem signedTotalIso_row (a : TermIso C C') (b : TermIso D D')
    (p : ℤ) (n : ℕ) :
    (rowPiece C D p n).map ((signedTotalIso a b).app n).toLinearMap = rowPiece C' D' p n := by
  classical
  rw [rowPiece, rowPiece, Submodule.map_iSup]
  congr 1
  funext k
  let e := tensorEquiv (a.app k.1.1) (b.app k.1.2)
  have h : ((signedTotalIso a b).app n).toLinearMap.comp
      (ordinaryInclusion C D k.1.1 k.1.2 n k.2.1) =
      (ordinaryInclusion C' D' k.1.1 k.1.2 n k.2.1).comp e.toLinearMap := by
    apply LinearMap.toAddMonoidHom_injective
    apply P103.BalancedTensor.hom_ext
    intro x y
    exact signedTotalIso_on_tensor a b _ _ _ _ x y
  rw [← LinearMap.range_comp, h, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr e.surjective, Submodule.map_top]

theorem total_transport : TotalTransportType.{u,v,w,x,y} :=
  fun _ _ _ _ _ _ a b => ⟨signedTotalIso a b, signedTotalIso_on_tensor a b,
    signedTotalIso_row a b⟩

end Total


section InnerTor

open ChangeOfRingsTor

variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)
variable {C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ}
variable {D : ChainComplex (ModuleCat.{x} Rᵐᵒᵖ) ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- The heterogeneous original map retains the action on the unchanged
S-factor in Pᵢ ⊗ᵣ S. -/
def extensionChainMap (l : TermMap C D) :
    TermMap (extensionComplexData f C).complex (extensionComplexData f D).complex where
  app n := extensionMap f (C.X n) (l.app n)
  comm m n := by
    ext t
    change extensionMap f (D.X m) (D.d m n).hom (extensionMap f (C.X m) (l.app m) t) =
      extensionMap f (C.X n) (l.app n) (extensionMap f (C.X m) (C.d m n).hom t)
    induction t using P103.BalancedTensor.induction_on with
    | h0 => simp only [map_zero]
    | ht x s =>
      change tmul R ((D.d m n).hom (l.app m x)) s =
        tmul R (l.app n ((C.d m n).hom x)) s
      rw [TermMap.comm_apply]
    | ha t z ht hz => simp only [map_add, ht, hz]

private theorem extensionInverse (e : TermIso C D) (n : ℕ) :
    ((extensionChainMap f e.symm.hom).app n).comp
      ((extensionChainMap f e.hom).app n) = LinearMap.id := by
  ext t
  change extensionMap f (D.X n) (e.app n).symm.toLinearMap
    (extensionMap f (C.X n) (e.app n).toLinearMap t) = t
  induction t using P103.BalancedTensor.induction_on with
  | h0 => simp only [map_zero]
  | ht x s =>
    change tmul R ((e.app n).symm (e.app n x)) s = tmul R x s
    rw [LinearEquiv.symm_apply_apply]
  | ha t z ht hz => simp only [map_add, ht, hz]

def extensionChainIso (e : TermIso C D) :
    TermIso (extensionComplexData f C).complex (extensionComplexData f D).complex where
  app n := LinearEquiv.ofLinearMap ((extensionChainMap f e.hom).app n)
    ((extensionChainMap f e.symm.hom).app n) (extensionInverse f e.symm n)
    (extensionInverse f e n)
  comm m n := TermMap.comm_apply (extensionChainMap f e.hom) m n

def innerQuotient (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ) : InnerQuotient f C where
  model := innerHomologyData f C
  action := innerTorModule f C
  linear q := (innerTorEquiv f C q).map_smul

set_option backward.isDefEq.respectTransparency false in
theorem innerQuotientMap_class (l : TermMap C D) (q : ℕ)
    (z : cycles (tensorComplex C (Restricted f S)) q) :
    ∃ t : cycles (tensorComplex D (Restricted f S)) q,
      t.val = tensorMap (l.app q) LinearMap.id z.val ∧
      (innerTorEquiv f D q)
        ((extensionChainMap f l).homologyMap q
          ((innerTorEquiv f C q).symm (homologyClass _ q z))) = homologyClass _ q t := by
  let a := (extensionCyclesEquiv f C q).symm z
  have ha : (innerTorEquiv f C q).symm (homologyClass _ q z) =
      homologyClass _ q a := by
    apply (innerTorEquiv f C q).injective
    rw [LinearEquiv.apply_symm_apply]
    change homologyClass _ q z = homologyClass _ q ((extensionCyclesEquiv f C q) a)
    rw [LinearEquiv.apply_symm_apply]
  rw [ha]
  let w := (extensionChainMap f l).cyclesMap q a
  refine ⟨extensionCyclesEquiv f D q w, ?_, rfl⟩
  exact extensionMap_eq f (C.X q) (l.app q) z.val

def innerTransport (e : TermIso C D) :
    InnerTransport f e (innerQuotient f C) (innerQuotient f D) where
  terms := extensionChainIso f e
  pure_tensor _ _ _ := rfl
  quotient q := (innerTorEquiv f C q).symm.trans
    (((extensionChainIso f e).homology q).trans (innerTorEquiv f D q))
  quotient_class q z := innerQuotientMap_class f e.hom q z

theorem inner_transport : InnerTransportType.{u,v,w,x} :=
  fun _ _ _ _ f C D e => ⟨innerQuotient f C, innerQuotient f D, ⟨innerTransport f e⟩⟩

end InnerTor


section HomologySquares

universe v' w'
variable {R : Type u} [Ring R] {I : Type i} {c : ComplexShape I}
variable {C : HomologicalComplex (ModuleCat.{v} R) c}
variable {D : HomologicalComplex (ModuleCat.{w} R) c}
variable {C' : HomologicalComplex (ModuleCat.{v'} R) c}
variable {D' : HomologicalComplex (ModuleCat.{w'} R) c}

theorem TermIso.homology_natural (e : TermIso C C') (e' : TermIso D D')
    (l : TermMap C D) (l' : TermMap C' D')
    (h : ∀ n a, l'.app n (e.app n a) = e'.app n (l.app n a)) (n : I)
    (a : Homology C n) :
    l'.homologyMap n (e.homology n a) = e'.homology n (l.homologyMap n a) := by
  obtain ⟨a, rfl⟩ := (cycleBoundaries C n).mkQ_surjective a
  exact congrArg (homologyClass D' n) (Subtype.ext (h n a.val))

theorem TermMap.homology_fromHom
    {D : HomologicalComplex (ModuleCat.{v} R) c} (l : C ⟶ D) (n : I) :
    (TermMap.ofHom l).homologyMap n = homologyMap l n := rfl

/-- Normalization on cycles determines the induced map on the entire quotient. -/
theorem TermIso.homology_unique (e : TermIso C D) (n : I)
    (h : Homology C n → Homology D n)
    (hh : ∀ z : cycles C n, ∃ t : cycles D n,
      t.val = e.app n z.val ∧ h (homologyClass C n z) = homologyClass D n t)
    (x : Homology C n) : h x = e.homology n x := by
  refine Quotient.inductionOn x ?_
  intro z
  obtain ⟨t, ht, hz⟩ := hh z
  exact hz.trans (congrArg (homologyClass D n) (Subtype.ext ht))

end HomologySquares

section TensorSquare

universe v' w' x' y'
variable {R : Type u} [Ring R]
variable {M : Type v} {N : Type w} {M' : Type v'} {N' : Type w'}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
variable {C : ChainComplex (ModuleCat.{x} Rᵐᵒᵖ) ℕ}
variable {D : ChainComplex (ModuleCat.{y} Rᵐᵒᵖ) ℕ}
variable {C' : ChainComplex (ModuleCat.{x'} Rᵐᵒᵖ) ℕ}
variable {D' : ChainComplex (ModuleCat.{y'} Rᵐᵒᵖ) ℕ}

theorem tensorComplexIso_natural (e : TermIso C C') (e' : TermIso D D')
    (b : M ≃ₗ[R] M') (b' : N ≃ₗ[R] N')
    (l : TermMap C D) (l' : TermMap C' D')
    (g : M →ₗ[R] N) (g' : M' →ₗ[R] N')
    (hl : ∀ n a, l'.app n (e.app n a) = e'.app n (l.app n a))
    (hg : ∀ t, g' (b t) = b' (g t)) (n : ℕ)
    (a : Homology (tensorComplex C M) n) :
    (TorBalance.tensorLinearChainMap l' g').homologyMap n
        ((tensorComplexIso e b).homology n a) =
      (tensorComplexIso e' b').homology n
        ((TorBalance.tensorLinearChainMap l g).homologyMap n a) := by
  apply TermIso.homology_natural _ _ _ _ _ n a
  intro k
  have h :
      ((TorBalance.tensorLinearChainMap l' g').app k).comp
          ((tensorComplexIso e b).app k).toLinearMap =
        ((tensorComplexIso e' b').app k).toLinearMap.comp
          ((TorBalance.tensorLinearChainMap l g).app k) := by
    apply tensor_hom_ext
    intro x t
    change tmul R (l'.app k (e.app k x)) (g' (b t)) =
      tmul R (e'.app k (l.app k x)) (b' (g t))
    rw [hl, hg]
  exact LinearMap.congr_fun h

end TensorSquare


section TargetTransport

open ChangeOfRingsTor P103.Specs.Ch11.TorBalance
universe a b c d
variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)
variable {A : Type a} {M : Type b} {A' : Type c} {M' : Type (max u v d)}
variable [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup M] [Module S M]
variable [AddCommGroup A'] [Module Rᵐᵒᵖ A'] [AddCommGroup M'] [Module S M']
variable {P : AugmentedResolution.{u,a,w} Rᵐᵒᵖ A} {Q : AugmentedResolution.{v,b,x} S M}
variable {P' : LeftResolution Rᵐᵒᵖ A'} {Q' : LeftResolution S M'}

set_option maxHeartbeats 900000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pull the canonical ambient total augmentation back to the original complexes.
Its degree-zero formula is the original augmentation, including on pure tensors. -/
def targetTransport (e : TermIso P.complex P'.complex)
    (e' : TermIso Q.complex Q'.complex) (m : M ≃ₗ[S] M')
    (ε : ∀ y, Q'.ε (e'.app 0 y) = m (Q.ε y))
    (T : TargetComparisonData.{u,v,c,d} f A' M' P' Q') :
    TargetTransport f (P := P) (Q := Q) e e' m T := by
  let er := restrictChainIso f e'
  let et := signedTotalIso e er
  let ec := tensorComplexIso e (restrictEquiv f m)
  let α := TermMap.comp ec.symm.hom (TermMap.comp (TermMap.ofHom T.augmentation) et.hom)
  have hα (n : ℕ) (z) : (T.augmentation.f n).hom (et.app n z) =
      ec.app n (α.app n z) :=
    ((ec.app n).apply_symm_apply _).symm
  refine {
    total := ⟨et, signedTotalIso_on_tensor e er, signedTotalIso_row e er⟩
    tensor := ec
    tensor_formula := fun _ _ _ => rfl
    augmentation := α
    augmentation_zero := ?_
    augmentation_positive := ?_
    augmentation_square := hα
    quasi := ?_
    quotient := ec.homology
    quotient_class := fun n z => ⟨ec.hom.cyclesMap n z, rfl, rfl⟩ }
  · intro n x y
    apply (ec.app n).injective
    rw [← hα, signedTotalIso_on_tensor e er]
    exact (T.zero n (e.app n x) (Restricted.of f (Q'.complex.X 0) (e'.app 0 y))).trans
      (congrArg (fun z : M' => tmul R (e.app n x) (Restricted.of f M' z)) (ε y))
  · intro i j n h hj
    apply LinearMap.toAddMonoidHom_injective
    apply P103.BalancedTensor.hom_ext
    intro x y
    change α.app n (ordinaryInclusion _ _ i j n h (tmul R x y)) = 0
    apply (ec.app n).injective
    rw [← hα, signedTotalIso_on_tensor e er, map_zero]
    exact LinearMap.congr_fun (T.positive i j n h hj) _
  · intro n
    let O := ordinaryTotal P.complex (restrictionComplex f (ComplexShape.down ℕ) Q.complex)
    have square (z : Homology O n) :
        (ec.homology n) (α.homologyMap n z) =
          homologyMap T.augmentation n ((et.homology n) z) := by
      refine Quotient.inductionOn z ?_
      intro a
      exact congrArg (homologyClass (tensorComplex P'.complex (Restricted f M')) n)
        (Subtype.ext (hα n a.val).symm)
    have bij : Function.Bijective (α.homologyMap n) := by
      refine ⟨?_, ?_⟩
      · intro a b h
        apply (et.homology n).injective
        apply (T.quasi n).injective
        rw [← square a, ← square b, h]
      · intro b
        obtain ⟨a, ha⟩ := ((T.quasi n).surjective.comp (et.homology n).surjective)
          (ec.homology n b)
        exact ⟨a, (ec.homology n).injective ((square a).trans ha)⟩
    exact ⟨AddEquiv.ofBijective (α.homologyMap n) bij,
      fun z => ⟨α.cyclesMap n z, rfl, rfl⟩⟩

end TargetTransport


section OriginalSequence

open ChangeOfRingsTor
universe a b
variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)
variable {A : Type a} {M : Type b}
variable [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup M] [Module S M]
variable (P : AugmentedResolution.{u,a,w} Rᵐᵒᵖ A)
variable (Q : AugmentedResolution.{v,b,x} S M)

def ambientPair : AmbientPair.{u,v,w,x,z,a,b} f P Q := by
  let e := carrierUp.{u,a,max u v b w x z} Rᵐᵒᵖ A
  let e' := carrierUp.{v,b,max u v a w x z} S M
  let PR := liftResolutionAlong.{u,a,w,max u v a b x z} P e
  let QR := liftResolutionAlong.{v,b,x,max u v a b w z} Q e'
  exact {
    pair := {
      right := PR
      left := QR
      right_projective := liftResolutionAlong_projective P e
      left_projective := liftResolutionAlong_projective Q e'
      total := tensor_total_exists R PR.complex (restrictionResolution f _ QR).complex }
    rightTerm := liftComplexIso P.complex
    leftTerm := liftComplexIso Q.complex
    rightComplex := rfl
    leftComplex := rfl
    rightUp := fun _ _ => rfl
    leftUp := fun _ _ => rfl
    rightAugmentation := fun _ => rfl
    leftAugmentation := fun _ => rfl }

variable {P Q}

def outerTransport (L : AmbientPair.{u,v,w,x,max y z,a,b} f P Q) (q : ℕ)
    [Module Sᵐᵒᵖ (resolutionTor P (Restricted f S) q)]
    [Module Sᵐᵒᵖ (TorWith L.pair.right (Restricted f S) q)]
    (e : resolutionTor P (Restricted f S) q ≃ₗ[Sᵐᵒᵖ] TorWith L.pair.right (Restricted f S) q)
    (U : AugmentedResolution.{v,max w v,y} Sᵐᵒᵖ (resolutionTor P (Restricted f S) q)) :
    OuterTransport.{u,v,w,x,y,z,a,b} f L q e U := by
  let V := liftResolutionAlong.{v,max v w,y,max u v a b w x z} U e
  let t : TermIso U.complex V.complex := liftComplexIso U.complex
  let c := tensorComplexIso t (carrierUp.{v,b,max u v a w x y z} S M)
  exact {
    ambient := V
    projective := liftResolutionAlong_projective U e
    terms := t
    complex_eq := rfl
    on_terms := fun _ _ => rfl
    aug := fun _ => rfl
    tensor := c
    pure_tensor := fun _ _ _ => rfl
    quotient := c.homology
    quotient_class := fun p z => ⟨c.hom.cyclesMap p z, rfl, rfl⟩ }


set_option maxHeartbeats 900000 in
set_option backward.isDefEq.respectTransparency false in
/-- Apply the ambient sequence to the specified lifts and transport its Tor
coordinates through the comparisons on the original tensor complexes. -/
def originalSequence :
    OriginalSequenceData.{u,v,w,x,y,z,a,b} f (P := P) (Q := Q)
      (changeOfRingsSystem.{u,v,max u v a b w x y z,max u v a b w x y z} f) := by
  let L := ambientPair.{u,v,w,x,max y z,a,b} f P Q
  let E := innerTransport f L.rightTerm
  refine {
    lift := L
    originalInner := innerQuotient f P.complex
    inner := E
    target := targetTransport f L.rightTerm L.leftTerm (carrierUp _ _) L.leftAugmentation
      (canonicalTargetComparison f L.pair)
    outer := ?_ }
  intro q U
  letI : Module Sᵐᵒᵖ (resolutionTor P (Restricted f S) q) := innerTorModule f P.complex q
  letI : Module Sᵐᵒᵖ (TorWith L.pair.right (Restricted f S) q) :=
    innerTorModule f L.pair.right.complex q
  exact outerTransport.{u,v,w,x,y,z,a,b} f L q (E.quotient q) U

namespace OriginalSequenceData
variable {T : NaturalSystem.{u,v,max u v a b w x y z,max u v a b w x y z} f}
variable (V : OriginalSequenceData.{u,v,w,x,y,z,a,b} f (P := P) (Q := Q) T)

theorem originalLimit : OriginalLimitData f V := by
  let E := V.pages f
  refine ⟨?_, ?_, ?_⟩
  · intro p n
    exact (Subobject.mapIsoToOrderIso (V.targetIso f n)).monotone
      (chainTargetPiece_increasing E.filtration p (n : ℤ))
  · intro n
    obtain ⟨lo, hi, hlo, hhi⟩ := chainTargetPiece_finite E.filtration E.convergence (n : ℤ)
    refine ⟨lo, hi, ?_, ?_⟩
    · intro p hp
      change (Subobject.mapIsoToOrderIso (V.targetIso f n)) (chainTargetPiece E.filtration p n) = ⊥
      rw [hlo p hp, OrderIso.map_bot]
    · intro p hp
      change (Subobject.mapIsoToOrderIso (V.targetIso f n)) (chainTargetPiece E.filtration p n) = ⊤
      rw [hhi p hp, OrderIso.map_top]
  · intro n r p hr hs
    exact ⟨mappedChainPageLimitIso E.filtration E.pages (n : ℤ) (V.targetIso f n)
      E.convergence r hr p hs⟩

end OriginalSequenceData

theorem original_sequence : OriginalSequenceType.{u,v,w,x,y,z,a,b} := by
  intro R S _ _ f A M _ _ _ _ P Q
  let V := originalSequence.{u,v,w,x,y,z,a,b} f (P := P) (Q := Q)
  exact ⟨_, V, V.originalLimit f⟩

set_option maxHeartbeats 1000000 in
/-- The ambient target identification is induced by the very augmentation
used to define the augmentation on the original signed total. -/
theorem originalSequence_target_normalized (n : ℕ) :
    let V := originalSequence.{u,v,w,x,y,z,a,b} f (P := P) (Q := Q)
    (V.pages f).targetIso n = (V.pages f).augmentation.cochainHomologyIso n := by
  rfl

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The abutment sends every lifted total cycle to its original augmentation class. -/
theorem target_representatives : TargetRepresentativesType.{u,v,w,x,y,z,a,b} := by
  intro R S _ _ f A M _ _ _ _ P Q T V n z
  let E := V.pages f
  let a := V.target.total.iso.hom.cyclesMap n z
  let t := V.target.augmentation.cyclesMap n z
  obtain ⟨z', hz', hclass⟩ := negativeExtensionQuotientIso_inv_class E.totalRegrading.iso n a
  obtain ⟨t', ht', hquotient⟩ := V.target.quotient_class n t
  have haug : cyclesMap E.augmentation.augmentation n a = t' :=
    Subtype.ext ((V.target.augmentation_square n z.val).trans ht'.symm)
  let e := negativeExtensionQuotientIso E.totalRegrading.iso n
  have hclass' : e.hom.hom (explicitClass _ _ z') = homologyClass _ n a := by
    rw [← hclass]
    exact e.toLinearEquiv.apply_symm_apply _
  refine ⟨z', t, hz', rfl, ?_⟩
  change ULift.up ((V.target.quotient n).symm (homologyMap E.augmentation.augmentation n
    (e.hom.hom (explicitClass _ _ z')))) = ULift.up (homologyClass _ n t)
  rw [hclass']
  change ULift.up ((V.target.quotient n).symm
    (homologyClass _ n (cyclesMap E.augmentation.augmentation n a))) = _
  rw [haug, ← hquotient, LinearEquiv.symm_apply_apply]

end OriginalSequence


section InnerMap

open ChangeOfRingsTor

variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)
variable {C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ}
variable {D : ChainComplex (ModuleCat.{x} Rᵐᵒᵖ) ℕ}

def innerQuotientMap (l : TermMap C D) (q : ℕ) :
    letI := innerTorModule f C q
    letI := innerTorModule f D q
    Homology (tensorComplex C (Restricted f S)) q →ₗ[Sᵐᵒᵖ]
      Homology (tensorComplex D (Restricted f S)) q := by
  letI := innerTorModule f C q
  letI := innerTorModule f D q
  exact (innerTorEquiv f D q).toLinearMap.comp
    (((extensionChainMap f l).homologyMap q).comp (innerTorEquiv f C q).symm.toLinearMap)

theorem innerQuotientMap_eq (l : TermMap C D) (q : ℕ)
    (a : Homology (tensorComplex C (Restricted f S)) q) :
    innerQuotientMap f l q a =
      (TorBalance.tensorLinearChainMap l
       (LinearMap.id : Restricted f S →ₗ[R] Restricted f S)).homologyMap q a := by
  refine Quotient.inductionOn a ?_
  intro z
  obtain ⟨t, ht, hz⟩ := innerQuotientMap_class f l q z
  refine hz.trans (congrArg (homologyClass (tensorComplex D (Restricted f S)) q) ?_)
  exact Subtype.ext ht

theorem innerTransport_eq (e : TermIso C D) (q : ℕ)
    (a : Homology (tensorComplex C (Restricted f S)) q) :
    (innerTransport f e).quotient q a =
      (tensorComplexIso e (LinearEquiv.refl R (Restricted f S))).homology q a := by
  refine Quotient.inductionOn a ?_
  intro z
  obtain ⟨t, ht, hz⟩ := (innerTransport f e).quotient_class q z
  refine hz.trans (congrArg (homologyClass (tensorComplex D (Restricted f S)) q) ?_)
  exact Subtype.ext ht

end InnerMap

section SameUniverse

variable {R : Type u} [Ring R] {M : Type v} {N : Type v}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable {C D : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ}

theorem tensorLinearChainMap_fromHom (l : C ⟶ D) (g : M →ₗ[R] N) :
    TorBalance.tensorLinearChainMap (TermMap.ofHom l) g =
      TermMap.ofHom (tensorFirstMap l M ≫ tensorSecondMap D g) := by
  apply TorBalance.LinearChainMap.eq_of_app_eq
  funext n
  apply tensor_hom_ext
  intro x y
  rfl

end SameUniverse


section LiftSquares

universe a b a' b'
variable {R : Type u} [Ring R] {A : Type a} {B : Type b} {A' : Type a'} {B' : Type b'}
variable [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
variable [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
variable {P : AugmentedResolution.{u,a,w} R A} {Q : AugmentedResolution.{u,b,x} R B}
variable {P' : AugmentedResolution.{u,a',y} R A'} {Q' : AugmentedResolution.{u,b',y} R B'}

/-- Conjugation preserves the defining square of an augmented comparison lift. -/
theorem augmented_conjugate
    (e : TermIso P.complex P'.complex) (e' : TermIso Q.complex Q'.complex)
    (a : A ≃ₗ[R] A') (b : B ≃ₗ[R] B')
    (hP : ∀ x, P'.ε (e.app 0 x) = a (P.ε x))
    (hQ : ∀ x, Q'.ε (e'.app 0 x) = b (Q.ε x))
    (l : TermMap P.complex Q.complex) (g : A →ₗ[R] B) (h : P.Lifts Q g l)
    (g' : A' →ₗ[R] B') (hg : ∀ x, g' (a x) = b (g x)) :
    P'.Lifts Q' g' (TermMap.ofHom (conjugateChainMap e e' l)) := by
  intro x
  obtain ⟨x, rfl⟩ := (e.app 0).surjective x
  change Q'.ε (((conjugateChainMap e e' l).f 0).hom (e.app 0 x)) =
      g' (P'.ε (e.app 0 x))
  rw [conjugateChainMap_apply, hP, hQ, hg, h x]

end LiftSquares


section Naturality

open ChangeOfRingsTor P103.Specs.Ch11.TorBalance
open private ordinaryTotalChainMap ordinaryTotalChainMap_inclusion ordinaryTotalLinear_ext
  from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.TorBalance

universe a b a' b' w' x' y'

variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)
variable {A : ModuleCat.{a} Rᵐᵒᵖ} {M : ModuleCat.{b} S}
variable {A' : ModuleCat.{a'} Rᵐᵒᵖ} {M' : ModuleCat.{b'} S}
variable {P : AugmentedResolution.{u,a,w} Rᵐᵒᵖ A} {Q : AugmentedResolution.{v,b,x} S M}
variable {P' : AugmentedResolution.{u,a',w'} Rᵐᵒᵖ A'}
variable {Q' : AugmentedResolution.{v,b',x'} S M'}
variable {T : NaturalSystem.{u,v,max u v a b w x y a' b' w' x' y' z,
  max u v a b w x y a' b' w' x' y' z} f}
variable (V : OriginalSequenceData.{u,v,w,x,y,max a' b' w' x' y' z,a,b} f (P := P) (Q := Q) T)
variable (V' : OriginalSequenceData.{u,v,w',x',y',max a b w x y z,a',b'} f (P := P') (Q := Q') T)

set_option maxHeartbeats 3000000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The maps on the original target are induced by the original augmented
total maps, and are compatible with the ambient page comparison. -/
def targetNaturality
    (g : A →ₗ[Rᵐᵒᵖ] A') (h : M →ₗ[S] M')
    (l : TermMap P.complex P'.complex) (m : TermMap Q.complex Q'.complex)
    (hl : P.Lifts P' g l) (hm : Q.Lifts Q' h m) :
    TargetNaturality.{u,v,w,x,y,z,a,b,a',b',w',x',y'} f V V' g h l m := by
  let g' := ambientRightMap.{u,v,w,x,y,z,a,b,a',b',w',x',y'} g
  let h' := ambientLeftMap.{u,v,w,x,y,z,a,b,a',b',w',x',y'} h
  let L := conjugateChainMap V.lift.rightTerm V'.lift.rightTerm l
  let N := conjugateChainMap V.lift.leftTerm V'.lift.leftTerm m
  let Nᵣ := ((restrictionFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).map N
  have hL : ChainLift V.lift.pair.right V'.lift.pair.right g'.hom L := by
    apply LinearMap.ext
    exact augmented_conjugate
      (P' := AugmentedResolution.ofP103 V.lift.pair.right V.lift.pair.right_projective)
      (Q' := AugmentedResolution.ofP103 V'.lift.pair.right V'.lift.pair.right_projective)
      V.lift.rightTerm V'.lift.rightTerm (carrierUp _ _) (carrierUp _ _)
      V.lift.rightAugmentation V'.lift.rightAugmentation l g hl g'.hom (fun _ => rfl)
  have hN : ChainLift V.lift.pair.left V'.lift.pair.left h'.hom N := by
    apply LinearMap.ext
    exact augmented_conjugate
      (P' := AugmentedResolution.ofP103 V.lift.pair.left V.lift.pair.left_projective)
      (Q' := AugmentedResolution.ofP103 V'.lift.pair.left V'.lift.pair.left_projective)
      V.lift.leftTerm V'.lift.leftTerm (carrierUp _ _) (carrierUp _ _)
      V.lift.leftAugmentation V'.lift.leftAugmentation m h hm h'.hom (fun _ => rfl)
  let F := ordinaryTotalChainMap l (restrictChainMap f m)
  let K := TorBalance.tensorLinearChainMap l (restrictLinear f h)
  have hq (n : ℕ) (z : resolutionTor P (Restricted f M) n) :
      (T.targetMap V.lift.pair V'.lift.pair g' h' n).hom (V.target.quotient n z) = V'.target.quotient n (K.homologyMap n z) := by
    rw [T.targetMap_eq V.lift.pair V'.lift.pair g' h' n L hL]
    rw [← TermMap.homology_fromHom, ← tensorLinearChainMap_fromHom]
    have hq₁ (z) : V.target.quotient n z = V.target.tensor.homology n z := by
      refine Quotient.inductionOn z ?_
      intro t
      obtain ⟨s, hs, ht⟩ := V.target.quotient_class n t
      exact ht.trans (congrArg (homologyClass _ n) (Subtype.ext hs))
    have hq₂ (z) : V'.target.quotient n z = V'.target.tensor.homology n z := by
      refine Quotient.inductionOn z ?_
      intro t
      obtain ⟨s, hs, ht⟩ := V'.target.quotient_class n t
      exact ht.trans (congrArg (homologyClass _ n) (Subtype.ext hs))
    rw [hq₁, hq₂]
    apply TermIso.homology_natural
    intro k
    have ht :
        ((TorBalance.tensorLinearChainMap (TermMap.ofHom L)
          (Restricted.map f h'.hom)).app k).comp (V.target.tensor.app k).toLinearMap =
        (V'.target.tensor.app k).toLinearMap.comp (K.app k) := by
      apply LinearMap.toAddMonoidHom_injective
      apply P103.BalancedTensor.hom_ext
      intro a b
      change tensorMap (L.f k).hom (Restricted.map f h'.hom)
          (V.target.tensor.app k (tmul R a b)) =
        V'.target.tensor.app k (tmul R (l.app k a) ((restrictLinear f h) b))
      rw [V.target.tensor_formula, V'.target.tensor_formula]
      let b' := Restricted.of f (ULift.{max u v a' w' x' y' a b w x y z} M')
        (ULift.up (h (Restricted.val f M b)))
      change tmul R ((L.f k).hom (V.lift.rightTerm.app k a)) b' =
        tmul R (V'.lift.rightTerm.app k (l.app k a)) b' 
      rw [conjugateChainMap_apply]
    exact LinearMap.congr_fun ht
  have square (n : ℕ) :
      HomologicalComplex.homologyMap (T.lifted V.lift.pair V'.lift.pair L N).hom (-(n : ℤ)) ≫
        (V'.targetIso f n).hom =
      (V.targetIso f n).hom ≫ ambientTargetMap.{u,v,w,x,y,z,a,b,a',b',w',x',y'} f n (K.homologyMap n) := by
    let ea := (V.target.quotient n).symm.trans (carrierUp.{0,max b w,max u v a b w x y a' b' w' x' y' z} ℤ _)
    let eb := (V'.target.quotient n).symm.trans (carrierUp.{0,max b' w',max u v a b w x y a' b' w' x' y' z} ℤ _)
    let Amap := T.targetMap V.lift.pair V'.lift.pair g' h' n
    let Bmap := ambientTargetMap.{u,v,w,x,y,z,a,b,a',b',w',x',y'} f n (K.homologyMap n)
    have hconj : Amap ≫ eb.toModuleIso.hom = ea.toModuleIso.hom ≫ Bmap := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro t
      obtain ⟨z, rfl⟩ := (V.target.quotient n).surjective t
      change ULift.up ((V'.target.quotient n).symm (Amap.hom (V.target.quotient n z))) =
        ULift.up (K.homologyMap n ((V.target.quotient n).symm (V.target.quotient n z)))
      rw [hq n, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    change _ ≫ ((V'.pages f).targetIso n).hom ≫ eb.toModuleIso.hom =
      (((V.pages f).targetIso n).hom ≫ ea.toModuleIso.hom) ≫ Bmap
    rw [← Category.assoc, T.target_naturality _ _ g' h' L N hL hN,
      Category.assoc, hconj, ← Category.assoc]
  refine {
    ambientRight := L
    ambientLeft := N
    termwise_right := conjugateChainMap_apply _ _ l
    termwise_left := conjugateChainMap_apply _ _ m
    aug_right := hL
    aug_left := hN
    page := T.map_eq _ _ g' h' L N hL hN
    originalTotal := F
    total_formula := ordinaryTotalChainMap_inclusion l (restrictChainMap f m)
    total_square := ?_
    originalTarget := K
    target_formula := fun _ => rfl
    augmentation_square := ?_
    targetMap := K.homologyMap
    target_class := K.homologyMap_induces
    quotient_square := hq
    target_square := square
    filtration := ?_ }
  · intro n
    have ht :
        (V'.target.total.iso.app n).toLinearMap.comp (F.app n) =
          ((ordinaryTotalMap L Nᵣ).f n).hom.comp
            (V.target.total.iso.app n).toLinearMap := by
      apply ordinaryTotalLinear_ext P.complex (restrictionComplex f (ComplexShape.down ℕ) Q.complex) n
      intro i j d a b
      change V'.target.total.iso.app n
          ((ordinaryTotalChainMap l (restrictChainMap f m)).app n
            (ordinaryInclusion _ _ i j n d (tmul R a b))) =
        ((ordinaryTotalMap L Nᵣ).f n).hom
          (V.target.total.iso.app n (ordinaryInclusion _ _ i j n d (tmul R a b)))
      rw [ordinaryTotalChainMap_inclusion]
      rw [V.target.total.on_tensor i j n d a b]
      rw [V'.target.total.on_tensor i j n d (l.app i a) ((restrictChainMap f m).app j b)]
      rw [P103.Ch11.TorBalance.ordinaryTotalMap_inclusion L Nᵣ]
      have hx := conjugateChainMap_apply V.lift.rightTerm V'.lift.rightTerm l i a
      have hy := conjugateChainMap_apply V.lift.leftTerm V'.lift.leftTerm m j
        (Restricted.val f (Q.complex.X j) b)
      exact congrArg (ordinaryInclusion _ _ i j n d)
        (congrArg₂ (tmul R) hx.symm hy.symm)
    exact LinearMap.congr_fun ht
  · intro n
    have ht :
        (V'.target.augmentation.app n).comp (F.app n) =
          (K.app n).comp (V.target.augmentation.app n) := by
      apply ordinaryTotalLinear_ext P.complex (restrictionComplex f (ComplexShape.down ℕ) Q.complex) n
      intro i j d a b
      dsimp only [F, LinearMap.comp_apply]
      rw [ordinaryTotalChainMap_inclusion]
      by_cases hj : j = 0
      · subst j
        have hd : i = n := by omega
        subst i
        let b₀ := Restricted.val f (Q.complex.X 0) b
        exact (V'.target.augmentation_zero n (l.app n a) (m.app 0 b₀)).trans
          ((congrArg (fun z => tmul R (l.app n a) (Restricted.of f M' z)) (hm b₀)).trans
            (congrArg (K.app n) (V.target.augmentation_zero n a b₀)).symm)
      · have ha := LinearMap.congr_fun (V.target.augmentation_positive i j n d hj) (tmul R a b)
        have hb := LinearMap.congr_fun (V'.target.augmentation_positive i j n d hj)
          (tmul R (l.app i a) ((restrictChainMap f m).app j b))
        change V.target.augmentation.app n (ordinaryInclusion _ _ i j n d (tmul R a b)) = 0 at ha
        change V'.target.augmentation.app n
          (ordinaryInclusion _ _ i j n d (tmul R (l.app i a) ((restrictChainMap f m).app j b))) = 0 at hb
        rw [ha, hb, map_zero]
    exact LinearMap.congr_fun ht
  · intro p n
    exact ⟨transportedCohomologyStepMap (T.lifted _ _ L N) (-(n : ℤ))
      (V.targetIso f n) (V'.targetIso f n) (-p),
      transportedCohomologyStepMap_arrow (T.lifted _ _ L N) (-(n : ℤ))
        (V.targetIso f n) (V'.targetIso f n) _ (square n) (-p)⟩


set_option maxHeartbeats 1000000 in
theorem target_naturality : TargetNaturalityType.{u,v,w,x,y,z,a,b,a',b',w',x',y'} := by
  intro R S _ _ f A M A' M' P Q P' Q'
  let VP := originalSequence.{u,v,w,x,y,max a' b' w' x' y' z,a,b} f (P := P) (Q := Q)
  let VQ := originalSequence.{u,v,w',x',y',max a b w x y z,a',b'} f (P := P') (Q := Q')
  refine ⟨_, VP, VQ, VP.originalLimit f, VQ.originalLimit f, ?_⟩
  intro g h l m hl hm
  exact ⟨targetNaturality.{u,v,w,x,y,z,a,b,a',b',w',x',y'} f VP VQ g h l m hl hm⟩


variable {V V'}
variable {g : A →ₗ[Rᵐᵒᵖ] A'} {h : M →ₗ[S] M'}
variable {l : TermMap P.complex P'.complex} {m : TermMap Q.complex Q'.complex}

set_option maxHeartbeats 6500000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem second_naturality
    (N : TargetNaturality.{u,v,w,x,y,z,a,b,a',b',w',x',y'} f V V' g h l m) :
    SecondNaturality f N := by
  let g' := ambientRightMap.{u,v,w,x,y,z,a,b,a',b',w',x',y'} g
  let h' := ambientLeftMap.{u,v,w,x,y,z,a,b,a',b',w',x',y'} h
  intro q
  letI : Module Sᵐᵒᵖ (resolutionTor P (Restricted f S) q) := V.originalInner.action q
  letI : Module Sᵐᵒᵖ (resolutionTor P' (Restricted f S) q) := V'.originalInner.action q
  letI : Module Sᵐᵒᵖ (TorWith V.lift.pair.right (Restricted f S) q) := (V.pages f).innerModule q
  letI : Module Sᵐᵒᵖ (TorWith V'.lift.pair.right (Restricted f S) q) := (V'.pages f).innerModule q
  let e := V.inner.quotient q
  let e' := V'.inner.quotient q
  let J := T.innerMap V.lift.pair V'.lift.pair g' q
  let j := e'.symm.toLinearMap.comp (J.comp e.toLinearMap)
  have hj (z) : J (e z) = e' (j z) := (e'.apply_symm_apply _).symm
  let idS : Restricted f S →ₗ[R] Restricted f S := LinearMap.id
  let I := TorBalance.tensorLinearChainMap l idS
  have innerRepr (z : Homology (tensorComplex P.complex (Restricted f S)) q) :
      j z = I.homologyMap q z := by
    apply e'.injective
    rw [← hj]
    rw [T.innerMap_eq V.lift.pair V'.lift.pair g' q N.ambientRight N.aug_right]
    rw [← TermMap.homology_fromHom]
    have hL : (TermMap.ofHom (tensorFirstMap N.ambientRight (Restricted f S))) =
        TorBalance.tensorLinearChainMap (TermMap.ofHom N.ambientRight) idS := by
      apply TorBalance.LinearChainMap.eq_of_app_eq
      funext n
      rfl
    rw [hL]
    let et := tensorComplexIso V.lift.rightTerm (LinearEquiv.refl R (Restricted f S))
    let et' := tensorComplexIso V'.lift.rightTerm (LinearEquiv.refl R (Restricted f S))
    have he (z) : e z = et.homology q z := by
      refine Quotient.inductionOn z ?_
      intro x
      obtain ⟨t, ht, hx⟩ := V.inner.quotient_class q x
      exact hx.trans (congrArg (homologyClass _ q) (Subtype.ext ht))
    have he' (z) : e' z = et'.homology q z := by
      refine Quotient.inductionOn z ?_
      intro x
      obtain ⟨t, ht, hx⟩ := V'.inner.quotient_class q x
      exact hx.trans (congrArg (homologyClass _ q) (Subtype.ext ht))
    rw [he, he']
    exact tensorComplexIso_natural V.lift.rightTerm V'.lift.rightTerm
      (LinearEquiv.refl R (Restricted f S)) (LinearEquiv.refl R (Restricted f S))
      l (TermMap.ofHom N.ambientRight) idS idS N.termwise_right (fun _ => rfl) q z
  refine ⟨j, ⟨I, fun _ => rfl, ?_⟩, ?_⟩
  · intro z
    exact ⟨I.cyclesMap q z, rfl, innerRepr (homologyClass _ q z)⟩
  · intro U U' k hk
    let O := V.outer q U
    let O' := V'.outer q U'
    let l' := conjugateChainMap O.terms O'.terms k
    have hl' : ChainLift O.ambient O'.ambient J l' := by
      apply LinearMap.ext
      exact augmented_conjugate
        (P' := AugmentedResolution.ofP103 O.ambient O.projective)
        (Q' := AugmentedResolution.ofP103 O'.ambient O'.projective)
        O.terms O'.terms e e' O.aug O'.aug k j hk J hj
    let F := TorBalance.tensorLinearChainMap k h
    refine ⟨F, F.homologyMap, fun _ => rfl, F.homologyMap_induces, ?_⟩
    intro p z
    let e₂ := (V.pages f).secondIso p q O.ambient O.projective
    let e₂' := (V'.pages f).secondIso p q O'.ambient O'.projective
    let t := T.map V.lift.pair V'.lift.pair g' h' 2 p (p+q)
    have ha := DFunLike.congr_fun
      (congrArg ModuleCat.Hom.hom
        (T.second_naturality V.lift.pair V'.lift.pair g' h' p q
          O.ambient O'.ambient O.projective O'.projective l' hl')) z
    apply (O'.quotient p).injective
    change (O'.quotient p) ((O'.quotient p).symm (e₂'.hom.hom (t.hom z))) =
      (O'.quotient p) (F.homologyMap p ((O.quotient p).symm (e₂.hom.hom z)))
    rw [LinearEquiv.apply_symm_apply]
    change e₂'.hom.hom (t.hom z) =
      (O'.quotient p) (F.homologyMap p ((O.quotient p).symm (e₂.hom.hom z)))
    let M₁ := ULift.{max u v a w x y a' b' w' x' y' z} M
    let φ := tensorFirstMap l' M₁ ≫ tensorSecondMap O'.ambient.complex h'.hom
    let F₁ := TorBalance.tensorLinearChainMap (TermMap.ofHom l') h'.hom
    have hφ : F₁.homologyMap p = homologyMap φ p := by
      dsimp only [F₁, φ]
      rw [tensorLinearChainMap_fromHom, TermMap.homology_fromHom]
    have ha' : e₂'.hom.hom (t.hom z) = homologyMap φ p (e₂.hom.hom z) := ha
    let z₀ := (O.quotient p).symm (e₂.hom.hom z)
    have hz : e₂.hom.hom z = O.quotient p z₀ :=
      ((O.quotient p).apply_symm_apply _).symm
    calc
      _ = F₁.homologyMap p (O.quotient p z₀) :=
        ha'.trans ((LinearMap.congr_fun hφ (e₂.hom.hom z)).symm.trans
          (congrArg (F₁.homologyMap p) hz))
      _ = (O'.quotient p) (F.homologyMap p z₀) := ?_
    rw [TermIso.homology_unique O.tensor p _ (O.quotient_class p),
      TermIso.homology_unique O'.tensor p _ (O'.quotient_class p)]
    apply TermIso.homology_natural
    intro n
    have hQ :
        ((TorBalance.tensorLinearChainMap (TermMap.ofHom l') h'.hom).app n).comp
          (O.tensor.app n).toLinearMap =
        (O'.tensor.app n).toLinearMap.comp (F.app n) := by
      apply tensor_hom_ext
      intro x b
      change tensorMap (l'.f n).hom h'.hom (O.tensor.app n (tmul S x b)) =
        O'.tensor.app n (tmul S (k.app n x) (h b))
      rw [O.pure_tensor, O'.pure_tensor]
      change tmul S ((l'.f n).hom (O.terms.app n x)) (ULift.up (h b)) =
        tmul S (O'.terms.app n (k.app n x)) (ULift.up (h b))
      rw [conjugateChainMap_apply]
    exact LinearMap.congr_fun hQ

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency false in
theorem originalTargetLaws
    (N : TargetNaturality.{u,v,w,x,y,z,a,b,a',b',w',x',y'} f V V' g h l m) :
    OriginalTargetLaws f N := by
  constructor
  · intro p n
    rintro _ ⟨z, hz, rfl⟩
    change ULift.up z ∈ LinearMap.range (V.targetPiece f p n).arrow.hom at hz
    change ULift.up (N.targetMap n z) ∈ LinearMap.range (V'.targetPiece f p n).arrow.hom
    obtain ⟨t, ht⟩ := hz
    obtain ⟨k, hk⟩ := N.filtration p n
    refine ⟨k.hom t, ?_⟩
    have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hk) t
    let F := ambientTargetMap.{u,v,w,x,y,z,a,b,a',b',w',x',y'} f n (N.targetMap n)
    change (V'.targetPiece f p n).arrow.hom (k.hom t) =
      F.hom ((V.targetPiece f p n).arrow.hom t) at h
    exact h.trans (congrArg F.hom ht)
  · intro l' m' N'
    constructor
    · intro n
      apply LinearMap.ext
      intro z
      apply (V'.target.quotient n).injective
      exact (N.quotient_square n z).symm.trans (N'.quotient_square n z)
    · intro r p n hr
      exact (N.page r p n hr).symm.trans (N'.page r p n hr)

set_option maxHeartbeats 1500000 in
theorem naturality : FullNaturalityType.{u,v,w,x,y,z,a,b,a',b',w',x',y'} := by
  intro R S _ _ f A M A' M' P Q P' Q'
  let VP := originalSequence.{u,v,w,x,y,max a' b' w' x' y' z,a,b} f (P := P) (Q := Q)
  let VQ := originalSequence.{u,v,w',x',y',max a b w x y z,a',b'} f (P := P') (Q := Q')
  refine ⟨_, VP, VQ, VP.originalLimit f, VQ.originalLimit f, ?_⟩
  intro g h
  refine ⟨P.exists_lift P' g, Q.exists_lift Q' h, ?_⟩
  intro l m hl hm
  let N := targetNaturality.{u,v,w,x,y,z,a,b,a',b',w',x',y'} f VP VQ g h l m hl hm
  exact ⟨N, second_naturality f N, originalTargetLaws f N⟩

end Naturality


section SubmoduleTransport

variable {G : Type w} [AddCommGroup G] {H : ModuleCat.{x} ℤ}

private def stepEquiv (e : G ≃ₗ[ℤ] H) (S : Subobject H) :
    (S : ModuleCat ℤ) ≃ₗ[ℤ] (LinearMap.range S.arrow.hom).comap e.toLinearMap :=
  LinearEquiv.ofBijective
    ((e.symm.toLinearMap.comp S.arrow.hom).codRestrict
      ((LinearMap.range S.arrow.hom).comap e.toLinearMap) (by
        intro t
        change ∃ z, S.arrow.hom z = e (e.symm (S.arrow.hom t))
        exact ⟨t, (e.apply_symm_apply _).symm⟩)) (by
    constructor
    · intro a b ha
      exact ((ModuleCat.mono_iff_injective S.arrow).1 inferInstance)
        (e.symm.injective (congrArg Subtype.val ha))
    · intro b
      obtain ⟨a, ha⟩ := b.property
      exact ⟨a, Subtype.ext (e.symm_apply_eq.mpr ha)⟩)

private theorem stepEquiv_range (e : G ≃ₗ[ℤ] H) {S T : Subobject H} (h : S ≤ T) :
    (LinearMap.range (Subobject.ofLE S T h).hom).map (stepEquiv e T).toLinearMap =
      ((LinearMap.range S.arrow.hom).comap e.toLinearMap).comap
        ((LinearMap.range T.arrow.hom).comap e.toLinearMap).subtype := by
  ext z
  have hs (x : (S : ModuleCat ℤ)) :
      T.arrow.hom ((Subobject.ofLE S T h).hom x) = S.arrow.hom x :=
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (Subobject.ofLE_arrow h)) x
  constructor
  · rintro ⟨a, ⟨b, rfl⟩, rfl⟩
    refine ⟨b, ?_⟩
    change S.arrow.hom b = e (e.symm (T.arrow.hom ((Subobject.ofLE S T h).hom b)))
    rw [LinearEquiv.apply_symm_apply, hs]
  · rintro ⟨b, hb⟩
    refine ⟨(Subobject.ofLE S T h).hom b, ⟨b, rfl⟩, ?_⟩
    apply Subtype.ext
    change e.symm (T.arrow.hom ((Subobject.ofLE S T h).hom b)) = z.val
    exact e.symm_apply_eq.mpr ((hs b).trans hb)

private def originalStepQuotient (e : G ≃ₗ[ℤ] H) {S T : Subobject H} (h : S ≤ T) :
    ↥(Limits.cokernel (Subobject.ofLE S T h)) ≃ₗ[ℤ]
      ((LinearMap.range T.arrow.hom).comap e.toLinearMap) ⧸
        (((LinearMap.range S.arrow.hom).comap e.toLinearMap).comap
          ((LinearMap.range T.arrow.hom).comap e.toLinearMap).subtype) :=
  (ModuleCat.cokernelIsoRangeQuotient (Subobject.ofLE S T h)).toLinearEquiv.trans
    (Submodule.Quotient.equiv _ _ (stepEquiv e T) (stepEquiv_range e h))

end SubmoduleTransport

section UnliftedFiltration

open ChangeOfRingsTor
universe a b

variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)
variable {A : Type a} {M : Type b}
variable [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup M] [Module S M]
variable {P : AugmentedResolution.{u,a,w} Rᵐᵒᵖ A}
variable {Q : AugmentedResolution.{v,b,x} S M}
variable {T : NaturalSystem.{u,v,max u v a b w x y z,max u v a b w x y z} f}
variable (V : OriginalSequenceData.{u,v,w,x,y,z,a,b} f (P := P) (Q := Q) T)

namespace OriginalSequenceData

theorem targetSubmodule_increasing (p : ℤ) (n : ℕ) :
    V.targetSubmodule f (p-1) n ≤ V.targetSubmodule f p n :=
  (targetSubmoduleOrder.{u,v,w,x,y,z,a,b} (P := P) (M := M) f n).monotone ((V.originalLimit f).increasing p n)

theorem targetSubmodule_finite (n : ℕ) :
    ∃ a b : ℤ, (∀ p, p ≤ a → V.targetSubmodule f p n = ⊥) ∧
      (∀ p, b ≤ p → V.targetSubmodule f p n = ⊤) := by
  obtain ⟨a,b,ha,hb⟩ := (V.originalLimit f).finite n
  refine ⟨a,b,?_,?_⟩
  · intro p hp
    change (targetSubmoduleOrder.{u,v,w,x,y,z,a,b} (P := P) (M := M) f n) (V.targetPiece f p n) = ⊥
    rw [ha p hp, OrderIso.map_bot]
  · intro p hp
    change (targetSubmoduleOrder.{u,v,w,x,y,z,a,b} (P := P) (M := M) f n) (V.targetPiece f p n) = ⊤
    rw [hb p hp, OrderIso.map_top]

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
def targetGradedEquiv (n : ℕ) (r p : ℤ) (hr : 0 ≤ r)
    (hs : FiniteFiltrationConvergence.Stabilized (V.pages f).filtration r (-p) (-(n : ℤ))) :
    ↥(chainPage (V := ModuleCat.{max u v a b w x y z} ℤ)
      (V.pages f).filtration (V.pages f).pages r p (n : ℤ)) ≃ₗ[ℤ]
    V.targetSubmodule f p n ⧸
      ((V.targetSubmodule f (p-1) n).comap (V.targetSubmodule f p n).subtype) := by
  let E := V.pages f
  let e := mappedChainPageLimitIso E.filtration E.pages (n : ℤ) (V.targetIso f n)
    E.convergence r hr p hs
  let g := originalStepQuotient
    (carrierUp.{0,max w b,max u v a b w x y z} ℤ (resolutionTor P (Restricted f M) n))
    ((V.originalLimit f).increasing p n)
  exact e.toLinearEquiv.trans g

end OriginalSequenceData
theorem unlifted_limit : UnliftedLimitType.{u,v,w,x,y,z,a,b} := by
  intro R S _ _ f A M _ _ _ _ P Q T V
  exact ⟨V.targetSubmodule_increasing f, V.targetSubmodule_finite f,
    fun n r p hr hs => ⟨V.targetGradedEquiv f n r p hr hs⟩⟩

end UnliftedFiltration


section RowFiltration

open CategoryTheory.Limits DoubleTotalization FiniteDiagonalFiltrations

private theorem range_bicone {ι : Type i} {A : ι → ModuleCat.{w} ℤ}
    (b : Bicone A) (h : b.IsBilimit) {H : ModuleCat.{w} ℤ} (j : b.pt ⟶ H) :
    LinearMap.range j.hom = ⨆ s, LinearMap.range (b.ι s ≫ j).hom := by
  let U := ⨆ s, LinearMap.range (b.ι s ≫ j).hom
  letI : Module ℤ U := U.module
  let u (s : ι) : A s ⟶ ModuleCat.of ℤ U := ModuleCat.ofHom
    ((b.ι s ≫ j).hom.codRestrict U fun x =>
      le_iSup (fun i => LinearMap.range (b.ι i ≫ j).hom) s
        (LinearMap.mem_range_self _ x))
  let k := h.isColimit.desc (Cofan.mk (ModuleCat.of ℤ U) u)
  have hk : k ≫ ModuleCat.ofHom U.subtype = j := by
    apply h.isColimit.hom_ext
    rintro ⟨s⟩
    change b.ι s ≫ (k ≫ ModuleCat.ofHom U.subtype) = b.ι s ≫ j
    rw [← Category.assoc, show b.ι s ≫ k = u s from h.isColimit.fac _ ⟨s⟩]
    rfl
  refine le_antisymm ?_ ?_
  · conv_lhs => rw [← hk, ModuleCat.hom_comp]
    rintro _ ⟨x, rfl⟩
    exact (k.hom x).property
  · exact iSup_le fun s => LinearMap.range_comp_le_range (b.ι s).hom j.hom

/-- The row filtration formula agrees with the supremum of the ranges
of the actual diagonal summand inclusions. -/
theorem rowFiltration_range {K : Bicomplex (ModuleCat.{w} ℤ)}
    [K.HasTotal (ComplexShape.up ℤ)] {F : Filtration (sumTotal K)}
    (h : HasFiltrationFormula K Prod.snd F) (p n : ℤ) :
    (ModuleCat.subobjectModule _) (F.piece p n) =
      ⨆ s : {i : Diagonal n // p ≤ i.val.2},
        LinearMap.range (sumInjection K s.val.val.1 s.val.val.2 n s.val.property).hom := by
  obtain ⟨b, hb, j, hj, he, hι⟩ := h p n
  let e := Subobject.underlyingIso j
  have he' : LinearMap.range (Subobject.mk j).arrow.hom = LinearMap.range j.hom := by
    have hc (t : b.pt) : (Subobject.mk j).arrow.hom (e.inv.hom t) = j.hom t := by
      simpa only [e, ModuleCat.hom_comp, LinearMap.comp_apply] using
        (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (Subobject.underlyingIso_arrow j)) t)
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨e.hom.hom t, ?_⟩
      rw [← hc]
      exact congrArg ((Subobject.mk j).arrow.hom) (e.toLinearEquiv.symm_apply_apply t)
    · rintro ⟨t, rfl⟩
      exact ⟨e.inv.hom t, hc t⟩
  rw [← he]
  change LinearMap.range (Subobject.mk j).arrow.hom = _
  rw [he', range_bicone b hb j]
  simp only [hι]

section Regrading
open ChangeOfRingsTor P103.Specs.Ch11.TorBalance

set_option maxHeartbeats 1200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [Ring R]
variable (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
variable (D : ChainComplex (ModuleCat.{w} R) ℕ)
variable [(tensorCochainBicomplex C D).HasTotal (ComplexShape.up ℤ)]

private theorem regradedSummand_range (e : TotalRegrading C D)
    (i j n : ℕ) (h : i+j=n)
    (p q : ℤ) (hp : -p = i) (hq : -q = j) :
    (LinearMap.range (sumInjection (tensorCochainBicomplex C D) p q (-(n : ℤ))
      (by omega)).hom).map ((e.iso.hom.f (-(n : ℤ))) ≫
        ((ordinaryTotal C D).extendXIso negativeChainEmbedding (i := n) rfl).hom).hom =
    LinearMap.range (ordinaryInclusion C D i j n h) := by
  have hp' : p = -(i : ℤ) := by omega
  have hq' : q = -(j : ℤ) := by omega
  subst p q
  let a := (C.extendXIso nonnegativeChainEmbedding (i := i) (i' := -(-(i : ℤ)))
    (by change (i : ℤ) = -(-(i : ℤ)); omega)).symm.toLinearEquiv
  let b := (D.extendXIso nonnegativeChainEmbedding (i := j) (i' := -(-(j : ℤ)))
    (by change (j : ℤ) = -(-(j : ℤ)); omega)).symm.toLinearEquiv
  have hs : Function.Surjective (tensorSummand C D i j) := (tensorEquiv a b).surjective
  let k := (ordinaryTotal C D).extendXIso negativeChainEmbedding (i := n) rfl
  let inc := sumInjection (tensorCochainBicomplex C D) (-(i : ℤ)) (-(j : ℤ)) (-(n : ℤ))
    (by omega)
  let F := ((e.iso.hom.f (-(n : ℤ))) ≫ k.hom).hom.comp inc.hom
  have hf : F.comp (tensorSummand C D i j) = ordinaryInclusion C D i j n h := by
    apply LinearMap.ext
    intro z
    change k.hom.hom ((e.iso.hom.f (-(n : ℤ))).hom (inc.hom (tensorSummand C D i j z))) = _
    rw [e.on_summands i j n h z]
    exact k.toLinearEquiv.apply_symm_apply _
  rw [← LinearMap.range_comp]
  change LinearMap.range F = _
  rw [← hf, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hs)]

private theorem compareRow (B : TensorPagesData C D) (e : TotalRegrading C D) (p : ℤ) (n : ℕ) :
    ((ModuleCat.subobjectModule _) (B.filtration.piece (-p) (-(n : ℤ)))).map
      ((e.iso.hom.f (-(n : ℤ))) ≫
        ((ordinaryTotal C D).extendXIso negativeChainEmbedding (i := n) rfl).hom).hom =
      rowPiece C D p n := by
  let F := ((e.iso.hom.f (-(n : ℤ))) ≫
    ((ordinaryTotal C D).extendXIso negativeChainEmbedding (i := n) rfl).hom).hom
  change ((ModuleCat.subobjectModule _) (B.filtration.piece (-p) (-(n : ℤ)))).map F = _
  rw [rowFiltration_range B.formula, Submodule.map_iSup]
  apply le_antisymm
  · apply iSup_le
    intro s
    let i := s.val.val.1
    let j := s.val.val.2
    by_cases hz : 0 < i ∨ 0 < j
    · have z := tensorCochainBicomplex_upper C D i j hz
      have hzero : sumInjection (tensorCochainBicomplex C D) i j (-(n : ℤ)) s.val.property = 0 :=
        z.eq_of_src _ _
      change (LinearMap.range (sumInjection (tensorCochainBicomplex C D) i j (-(n : ℤ))
        s.val.property).hom).map _ ≤ _
      rw [hzero, ModuleCat.hom_zero, LinearMap.range_zero, Submodule.map_bot]
      exact bot_le
    · obtain ⟨i', hi⟩ := Int.eq_ofNat_of_zero_le (a := -i) (by omega)
      obtain ⟨j', hj⟩ := Int.eq_ofNat_of_zero_le (a := -j) (by omega)
      have hd : i' + j' = n := by
        have h := s.val.property
        change i + j = -(n : ℤ) at h
        omega
      have ht : (j' : ℤ) ≤ p := by
        have h := s.property
        change -p ≤ j at h
        omega
      have hs := regradedSummand_range C D e i' j' n hd i j hi hj
      change (LinearMap.range (sumInjection (tensorCochainBicomplex C D) i j (-(n : ℤ))
        s.val.property).hom).map F ≤ _
      rw [hs]
      let t : {ij : ℕ × ℕ // ij.1+ij.2=n ∧ (ij.2 : ℤ) ≤ p} := ⟨(i',j'),hd,ht⟩
      exact le_iSup (fun k : {ij : ℕ × ℕ // ij.1+ij.2=n ∧ (ij.2 : ℤ) ≤ p} =>
        LinearMap.range (ordinaryInclusion C D k.val.1 k.val.2 n k.property.1)) t
  · apply iSup_le
    intro s
    let i := s.val.1
    let j := s.val.2
    let t : {k : Diagonal (-(n : ℤ)) // -p ≤ k.val.2} :=
      ⟨⟨(-(i : ℤ), -(j : ℤ)), by have h := s.property.1; omega⟩,
        by change -p ≤ -(j : ℤ); have h := s.property.2; omega⟩
    exact (regradedSummand_range C D e i j n s.property.1 (-(i : ℤ)) (-(j : ℤ))
      (Int.neg_neg _) (Int.neg_neg _)).ge.trans (le_iSup (fun s : {i : Diagonal (-(n : ℤ)) // -p ≤ i.val.2} =>
        (LinearMap.range (sumInjection (tensorCochainBicomplex C D) s.val.val.1 s.val.val.2
          (-(n : ℤ)) s.val.property).hom).map F) t)


end Regrading

theorem row_filtration_regrade : RegradedRowsType.{u,v,w} := by
  intro R _ C D _ B
  exact ⟨⟨ChangeOfRingsTor.ordinaryTotalRegrading C D⟩, compareRow C D B⟩

end RowFiltration

section Composition

open ChangeOfRingsTor
universe a b c a' b' c'

namespace CoefficientCoordinates

variable {R : Type u} [Ring R] {X Y Z : ModuleCat.{w} R}

@[simp] theorem map_id (E : CoefficientCoordinates.{u,w,a} X) :
    E.map E LinearMap.id = 𝟙 X := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  change E.equiv (E.equiv.symm b) = b
  exact E.equiv.apply_symm_apply b

theorem map_comp (E : CoefficientCoordinates.{u,w,a} X) (F : CoefficientCoordinates.{u,w,b} Y)
    (G : CoefficientCoordinates.{u,w,c} Z) (g : E.original →ₗ[R] F.original)
    (h : F.original →ₗ[R] G.original) :
    E.map G (h.comp g) = E.map F g ≫ F.map G h := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  change G.equiv (h (g (E.equiv.symm b))) =
    G.equiv (h (F.equiv.symm (F.equiv (g (E.equiv.symm b)))))
  rw [LinearEquiv.symm_apply_apply]

end CoefficientCoordinates

set_option maxHeartbeats 2000000 in
theorem coordinate_functoriality : CoordinateFunctorialityType.{u,v,w,x,a,b,c,a',b',c'} := by
  intro R S _ _ f T A B C M N L P Q U a₁ a₂ a₃ b₁ b₂ b₃ g g' h h'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r p n hr
    rw [CoefficientCoordinates.map_id, CoefficientCoordinates.map_id]
    exact T.map_id P r p n hr
  · intro r p n hr
    rw [CoefficientCoordinates.map_comp, CoefficientCoordinates.map_comp]
    exact T.map_comp P Q U _ _ _ _ r p n hr
  · intro n
    rw [CoefficientCoordinates.map_id, CoefficientCoordinates.map_id]
    exact T.targetMap_id P n
  · intro n
    rw [CoefficientCoordinates.map_comp, CoefficientCoordinates.map_comp]
    exact T.targetMap_comp P Q U _ _ _ _ n
  · exact T.differential_naturality P Q _ _

end Composition


section ResolutionChange

open ChangeOfRingsTor
universe a b w' x' y'

set_option maxHeartbeats 3500000 in
set_option backward.isDefEq.respectTransparency false in
theorem resolution_change : ResolutionChangeType.{u,v,w,x,y,z,a,b,w',x',y'} := by
  intro R S _ _ f A M P Q P' Q' T V V'
  constructor
  · intro r p n hr
    exact ⟨T.comparison V.lift.pair V'.lift.pair r p n hr, rfl⟩
  · intro n
    let k := T.targetComparison V.lift.pair V'.lift.pair n
    let e := (V.target.quotient n).trans (k.toLinearEquiv.trans (V'.target.quotient n).symm)
    refine ⟨e, ?_, ?_⟩
    · intro z
      change V'.target.quotient n
          ((V'.target.quotient n).symm (k.hom.hom (V.target.quotient n z))) =
        k.hom.hom (V.target.quotient n z)
      exact (V'.target.quotient n).apply_symm_apply _
    · intro p
      obtain ⟨l, hl⟩ := P.exists_lift P' LinearMap.id
      obtain ⟨m, hm⟩ := Q.exists_lift Q' LinearMap.id
      obtain ⟨l', hl'⟩ := P'.exists_lift P LinearMap.id
      obtain ⟨m', hm'⟩ := Q'.exists_lift Q LinearMap.id
      let N := targetNaturality.{u,v,w,x,y,z,a,b,a,b,w',x',y'}
        f V V' LinearMap.id LinearMap.id l m hl hm
      let N' := targetNaturality.{u,v,w',x',y',z,a,b,a,b,w,x,y}
        f V' V LinearMap.id LinearMap.id l' m' hl' hm'
      have hN : e.toLinearMap = N.targetMap n := by
        apply LinearMap.ext
        intro z
        apply (V'.target.quotient n).injective
        change V'.target.quotient n ((V'.target.quotient n).symm
          (k.hom.hom (V.target.quotient n z))) =
          V'.target.quotient n (N.targetMap n z)
        rw [LinearEquiv.apply_symm_apply]
        exact N.quotient_square n z
      have hN' : e.symm.toLinearMap = N'.targetMap n := by
        apply LinearMap.ext
        intro z
        apply (V.target.quotient n).injective
        change V.target.quotient n ((V.target.quotient n).symm
          (k.inv.hom (V'.target.quotient n z))) =
          V.target.quotient n (N'.targetMap n z)
        rw [LinearEquiv.apply_symm_apply]
        exact N'.quotient_square n z
      refine le_antisymm ?_ ?_
      · rw [hN]
        exact (originalTargetLaws f N).1 p n
      · apply (Submodule.orderIsoMapComap e).symm_apply_le.mp
        rw [Submodule.orderIsoMapComap_symm_apply, Submodule.comap_equiv_eq_map_symm, hN']
        exact (originalTargetLaws f N').1 p n

end ResolutionChange

end AdvancedHomologicalAlgebra.ChangeOfRingsOriginalCoefficients
