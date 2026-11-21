import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.KunnethFreeSplitting
import MathGenome.Internal.AlgebraCore.P103.Ch11.ArbitraryRankPIDSubmodules
import MathGenome.Internal.AlgebraCore.P103.Ch11.TorBalance
import MathGenome.Internal.AlgebraCore.P103.Ch01.SplitSequences
import MathGenome.Internal.AlgebraCore.P103.Ch02.FlatnessTests
import Mathlib.Algebra.Module.Projective

import MathGenome.Internal.AlgebraCore.P103.Ch11.KunnethSequence
namespace P103.Ch11.KunnethFreeSplitting
open CategoryTheory
open P103.BalancedTensor
open P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.KunnethSequence P103.Specs.Ch11.TorBalance
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch11.KunnethFreeSplitting
open P103.Specs.Ch10.TotalComplexAssembly
noncomputable section
universe u v w
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Projections
variable {S : Type u} [Ring S]
  (C : ChainComplex (ModuleCat.{v} S) ℕ)

/-- A projective differential image makes the actual cycle inclusion split. -/
theorem exists_cycle_retraction
    (h : ∀ n, Module.Projective S (LinearMap.range
      (C.d n ((ComplexShape.down ℕ).next n)).hom)) (n : ℕ) :
    ∃ r : C.X n →ₗ[S] cycles C n,
      r.comp (cycles C n).subtype = LinearMap.id := by
  let d := (C.d n ((ComplexShape.down ℕ).next n)).hom
  letI := h n
  obtain ⟨s, hs⟩ := d.rangeRestrict.exists_rightInverse_of_surjective d.range_rangeRestrict
  let t : C.X n →ₗ[S] C.X n := LinearMap.id - s.comp d.rangeRestrict
  have ht : ∀ x, t x ∈ cycles C n := by
    intro x
    change d (x - s (d.rangeRestrict x)) = 0
    have he := congrArg Subtype.val (LinearMap.congr_fun hs (d.rangeRestrict x))
    change d (s (d.rangeRestrict x)) = d x at he
    simp [he]
  refine ⟨t.codRestrict (cycles C n) ht, ?_⟩
  ext z
  have hz : d z.val = 0 := z.property
  have hz' : d.rangeRestrict z.val = 0 := Subtype.ext hz
  change z.val - s (d.rangeRestrict z.val) = z.val
  simp [hz']

/-- Chosen projections give maps to quotient homology on entire chain terms. -/
def termHomologyMap (r : ∀ n, C.X n →ₗ[S] cycles C n) (n : ℕ) :
    C.X n →ₗ[S] Homology C n := (homologyClass C n).comp (r n)

theorem termHomologyMap_cycle
    (r : ∀ n, C.X n →ₗ[S] cycles C n)
    (hr : ∀ n, (r n).comp (cycles C n).subtype = LinearMap.id)
    (n : ℕ) (z : cycles C n) :
    termHomologyMap C r n z.val = homologyClass C n z := by
  have hz := LinearMap.congr_fun (hr n) z
  exact congrArg (homologyClass C n) hz

theorem termHomologyMap_d
    (r : ∀ n, C.X n →ₗ[S] cycles C n)
    (hr : ∀ n, (r n).comp (cycles C n).subtype = LinearMap.id)
    (i j : ℕ) (x : C.X i) :
    termHomologyMap C r j ((C.d i j).hom x) = 0 := by
  by_cases hij : (ComplexShape.down ℕ).Rel i j
  · have hi : i = j + 1 := by simpa [ComplexShape.down_Rel] using hij.symm
    subst i
    have hb : (C.d (j+1) j).hom x ∈ boundaries C j := by
      change ∃ y, (C.d ((ComplexShape.down ℕ).prev j) j).hom y = _
      rw [ChainComplex.prev]
      exact ⟨x, rfl⟩
    let z : cycles C j := ⟨_, boundaryInclusion C j hb⟩
    rw [show (C.d (j+1) j).hom x = z.val from rfl,
      termHomologyMap_cycle C r hr j z]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hb
  · rw [C.shape i j hij]
    exact map_zero _

end Projections

section TensorProjections
variable {R : Type u} [Ring R]
  (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
  (rC : ∀ p, C.X p →ₗ[Rᵐᵒᵖ] cycles C p)
  (rD : ∀ q, D.X q →ₗ[R] cycles D q)

private instance finiteDiagonal (n : ℕ) : Finite (Diagonal n) := by
  apply Finite.of_injective
    (fun i : Diagonal n =>
      ((⟨i.val.1, by have := i.property; omega⟩ : Fin (n+1)),
       (⟨i.val.2, by have := i.property; omega⟩ : Fin (n+1))))
  intro i j h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun k : Fin (n+1) × Fin (n+1) => k.1.val) h
  · exact congrArg (fun k : Fin (n+1) × Fin (n+1) => k.2.val) h

/-- Extend a chosen map on ordinary terms to the retained integer term. -/
def extendedTermMap {S : Type u} [Ring S]
    (E : ChainComplex (ModuleCat.{v} S) ℕ)
    (r : ∀ p, E.X p →ₗ[S] cycles E p) (p : ℕ) :
    (extendNonnegativeChain E).X (p : ℤ) →ₗ[S] Homology E p :=
  (termHomologyMap E r p).comp
    (E.extendXIso nonnegativeChainEmbedding (i := p) rfl).hom.hom

/-- A single tensor coordinate, followed by the two quotient homology maps. -/
def tensorCoordinate (n : ℕ) (i : Diagonal n) :
    (ordinaryTotal C D).X n →ₗ[ℤ] TensorTerm C D i.val :=
  (tensorMap (extendedTermMap C rC i.val.1) (extendedTermMap D rD i.val.2)).comp
    (totalProjection (tensorBicomplex (extendNonnegativeChain C)
      (extendNonnegativeChain D)) i.val.1 i.val.2 n
      (by have := i.property; exact_mod_cast this)).hom

/-- The finite diagonal sum of the tensor coordinates. -/
def tensorTermRetraction (n : ℕ) :
    (ordinaryTotal C D).X n →ₗ[ℤ] TensorDiagonal C D n := by
  classical
  letI := Fintype.ofFinite (Diagonal n)
  exact ∑ i : Diagonal n,
    (DirectSum.lof ℤ _ (fun i : Diagonal n => TensorTerm C D i.val) i).comp
      (tensorCoordinate C D rC rD n i)

theorem extendedTermMap_d {S : Type u} [Ring S]
    (E : ChainComplex (ModuleCat.{v} S) ℕ)
    (r : ∀ p, E.X p →ₗ[S] cycles E p)
    (hr : ∀ p, (r p).comp (cycles E p).subtype = LinearMap.id)
    (i j : ℕ) (x : (extendNonnegativeChain E).X (i : ℤ)) :
    extendedTermMap E r j (((extendNonnegativeChain E).d i j).hom x) = 0 := by
  change termHomologyMap E r j
    ((E.extendXIso nonnegativeChainEmbedding (i := j) rfl).hom.hom _) = 0
  rw [P103.Ch11.TorBalance.extendNonnegativeChain_d_coordinate]
  exact termHomologyMap_d E r hr i j _

theorem tensorCoordinate_inclusion_self (n : ℕ) (i : Diagonal n)
    (a : C.X i.val.1) (b : D.X i.val.2) :
    tensorCoordinate C D rC rD n i
      (ordinaryInclusion C D i.val.1 i.val.2 n i.property (tmul R a b)) =
    tmul R (termHomologyMap C rC i.val.1 a) (termHomologyMap D rD i.val.2 b) := by
  let K := tensorBicomplex (extendNonnegativeChain C) (extendNonnegativeChain D)
  have he := congrArg (fun f => f.hom
    (tmul R ((C.extendXIso nonnegativeChainEmbedding (i := i.val.1) rfl).inv.hom a)
      ((D.extendXIso nonnegativeChainEmbedding (i := i.val.2) rfl).inv.hom b)))
    (P103.Ch10.TotalComplexAssembly.totalInclusion_projection_self K
      i.val.1 i.val.2 n (by exact_mod_cast i.property))
  calc
    _ = tensorMap (extendedTermMap C rC i.val.1) (extendedTermMap D rD i.val.2)
        (tmul R ((C.extendXIso nonnegativeChainEmbedding (i := i.val.1) rfl).inv.hom a)
          ((D.extendXIso nonnegativeChainEmbedding (i := i.val.2) rfl).inv.hom b)) :=
      congrArg (tensorMap (extendedTermMap C rC i.val.1) (extendedTermMap D rD i.val.2)) he
    _ = _ := by
      change tmul R (termHomologyMap C rC i.val.1
        ((C.extendXIso nonnegativeChainEmbedding (i := i.val.1) rfl).hom.hom
          ((C.extendXIso nonnegativeChainEmbedding (i := i.val.1) rfl).inv.hom a)))
        (termHomologyMap D rD i.val.2
        ((D.extendXIso nonnegativeChainEmbedding (i := i.val.2) rfl).hom.hom
          ((D.extendXIso nonnegativeChainEmbedding (i := i.val.2) rfl).inv.hom b))) = _
      apply congrArg₂ (tmul R)
      · exact congrArg (termHomologyMap C rC i.val.1)
          (congrArg (fun f => f.hom a)
            (C.extendXIso nonnegativeChainEmbedding (i := i.val.1) rfl).inv_hom_id)
      · exact congrArg (termHomologyMap D rD i.val.2)
          (congrArg (fun f => f.hom b)
            (D.extendXIso nonnegativeChainEmbedding (i := i.val.2) rfl).inv_hom_id)

theorem tensorCoordinate_inclusion_ne (n : ℕ) (i j : Diagonal n) (hij : i ≠ j)
    (a : C.X j.val.1) (b : D.X j.val.2) :
    tensorCoordinate C D rC rD n i
      (ordinaryInclusion C D j.val.1 j.val.2 n j.property (tmul R a b)) = 0 := by
  let K := tensorBicomplex (extendNonnegativeChain C) (extendNonnegativeChain D)
  have hne : (j.val.1 : ℤ) ≠ i.val.1 ∨ (j.val.2 : ℤ) ≠ i.val.2 := by
    by_contra h
    push_neg at h
    apply hij
    apply Subtype.ext
    apply Prod.ext <;> omega
  have he := congrArg (fun f => f.hom
    (tmul R ((C.extendXIso nonnegativeChainEmbedding (i := j.val.1) rfl).inv.hom a)
      ((D.extendXIso nonnegativeChainEmbedding (i := j.val.2) rfl).inv.hom b)))
    (P103.Ch10.TotalComplexAssembly.totalInclusion_projection_ne K
      j.val.1 j.val.2 i.val.1 i.val.2 n
      (by exact_mod_cast j.property) (by exact_mod_cast i.property) hne)
  rw [P103.Ch11.TorBalance.ordinaryInclusion_tmul]
  change tensorMap _ _ ((totalProjection K _ _ _ _).hom
    ((totalInclusion K _ _ _ _).hom _)) = 0
  change (totalProjection K _ _ _ _).hom ((totalInclusion K _ _ _ _).hom _) = 0 at he
  rw [he, map_zero]

theorem tensorTermRetraction_inclusion (n : ℕ) (i : Diagonal n)
    (a : C.X i.val.1) (b : D.X i.val.2) :
    tensorTermRetraction C D rC rD n
      (ordinaryInclusion C D i.val.1 i.val.2 n i.property (tmul R a b)) =
    DirectSum.lof ℤ _ (fun i : Diagonal n => TensorTerm C D i.val) i
      (tmul R (termHomologyMap C rC i.val.1 a) (termHomologyMap D rD i.val.2 b)) := by
  classical
  letI := Fintype.ofFinite (Diagonal n)
  rw [tensorTermRetraction, LinearMap.sum_apply, Finset.sum_eq_single i]
  · rw [LinearMap.comp_apply, tensorCoordinate_inclusion_self]
  · intro j _ hji
    simp only [LinearMap.comp_apply, tensorCoordinate_inclusion_ne C D rC rD n j i hji,
      map_zero]
  · simp

theorem tensorCoordinate_d
    (hC : ∀ p, (rC p).comp (cycles C p).subtype = LinearMap.id)
    (hD : ∀ q, (rD q).comp (cycles D q).subtype = LinearMap.id)
    (n : ℕ) (i : Diagonal n) (x : (ordinaryTotal C D).X (n+1)) :
    tensorCoordinate C D rC rD n i (((ordinaryTotal C D).d (n+1) n).hom x) = 0 := by
  let K := tensorBicomplex (extendNonnegativeChain C) (extendNonnegativeChain D)
  let f := tensorMap (extendedTermMap C rC i.val.1) (extendedTermMap D rD i.val.2)
  have hhorizontal : ∀ y, f (((K.d ((i.val.1 : ℤ)+1) i.val.1).f i.val.2).hom y) = 0 := by
    have hh : f.comp ((K.d ((i.val.1 : ℤ)+1) i.val.1).f i.val.2).hom = 0 := by
      apply tensor_hom_ext
      intro a b
      change tmul R (extendedTermMap C rC i.val.1
        (((extendNonnegativeChain C).d ((i.val.1 : ℤ)+1) i.val.1).hom a))
        (extendedTermMap D rD i.val.2 b) = 0
      have hz : ∀ a, extendedTermMap C rC i.val.1
          (((extendNonnegativeChain C).d ((i.val.1 : ℤ)+1) i.val.1).hom a) = 0 := by
        have hz := extendedTermMap_d C rC hC (i.val.1+1) i.val.1
        rw [Nat.cast_add, Nat.cast_one] at hz
        exact hz
      rw [hz, zero_tmul]
    exact LinearMap.congr_fun hh
  have hvertical : ∀ y, f (((K.X i.val.1).d ((i.val.2 : ℤ)+1) i.val.2).hom y) = 0 := by
    have hh : f.comp ((K.X i.val.1).d ((i.val.2 : ℤ)+1) i.val.2).hom = 0 := by
      apply tensor_hom_ext
      intro a b
      change tmul R (extendedTermMap C rC i.val.1 a)
        (extendedTermMap D rD i.val.2
          (((extendNonnegativeChain D).d ((i.val.2 : ℤ)+1) i.val.2).hom b)) = 0
      have hz : ∀ b, extendedTermMap D rD i.val.2
          (((extendNonnegativeChain D).d ((i.val.2 : ℤ)+1) i.val.2).hom b) = 0 := by
        have hz := extendedTermMap_d D rD hD (i.val.2+1) i.val.2
        rw [Nat.cast_add, Nat.cast_one] at hz
        exact hz
      rw [hz, tmul_zero]
    exact LinearMap.congr_fun hh
  let y : (total K).X ((n+1 : ℕ) : ℤ) := x
  have he0 := P103.Ch10.TotalComplexAssembly.chain_totalProjection_d K
    i.val.1 i.val.2 ((n+1 : ℕ) : ℤ) (by have := i.property; omega)
  have he : (total K).d ((n+1 : ℕ) : ℤ) n ≫
      totalProjection K i.val.1 i.val.2 n (by exact_mod_cast i.property) =
      totalProjection K ((i.val.1 : ℤ)+1) i.val.2 ((n+1 : ℕ) : ℤ)
        (by have := i.property; omega) ≫ (K.d ((i.val.1 : ℤ)+1) i.val.1).f i.val.2 +
      (i.val.1 : ℤ).negOnePow •
        (totalProjection K i.val.1 ((i.val.2 : ℤ)+1) ((n+1 : ℕ) : ℤ)
        (by have := i.property; omega) ≫ (K.X i.val.1).d ((i.val.2 : ℤ)+1) i.val.2) := by
    convert he0 using 1 <;> congr 2 <;> first | exact proof_irrel_heq _ _ | omega
  have hx := congrArg (fun k => f (k.hom y)) he
  have hh : f ((totalProjection K ((i.val.1 : ℤ)+1) i.val.2 ((n+1 : ℕ) : ℤ)
        (by have := i.property; omega) ≫ (K.d ((i.val.1 : ℤ)+1) i.val.1).f i.val.2 +
      (i.val.1 : ℤ).negOnePow •
        (totalProjection K i.val.1 ((i.val.2 : ℤ)+1) ((n+1 : ℕ) : ℤ)
        (by have := i.property; omega) ≫ (K.X i.val.1).d ((i.val.2 : ℤ)+1) i.val.2)).hom y) = 0 := by
    change f (_ + (i.val.1 : ℤ).negOnePow • _) = 0
    rw [map_add, map_zsmul_unit]
    change f (((K.d ((i.val.1 : ℤ)+1) i.val.1).f i.val.2).hom _) +
      (i.val.1 : ℤ).negOnePow • f (((K.X i.val.1).d ((i.val.2 : ℤ)+1) i.val.2).hom _) = 0
    rw [hhorizontal, hvertical, smul_zero, add_zero]
  exact hx.trans hh

theorem tensorTermRetraction_d
    (hC : ∀ p, (rC p).comp (cycles C p).subtype = LinearMap.id)
    (hD : ∀ q, (rD q).comp (cycles D q).subtype = LinearMap.id)
    (n : ℕ) (x : (ordinaryTotal C D).X (n+1)) :
    tensorTermRetraction C D rC rD n (((ordinaryTotal C D).d (n+1) n).hom x) = 0 := by
  classical
  rw [tensorTermRetraction, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [LinearMap.comp_apply, tensorCoordinate_d C D rC rD hC hD, map_zero]

/-- The diagonal map kills all boundaries, so descends to actual quotient homology. -/
def homologyRetraction
    (hC : ∀ p, (rC p).comp (cycles C p).subtype = LinearMap.id)
    (hD : ∀ q, (rD q).comp (cycles D q).subtype = LinearMap.id)
    (n : ℕ) : Homology (ordinaryTotal C D) n →ₗ[ℤ] TensorDiagonal C D n :=
  by
    let f : cycles (ordinaryTotal C D) n →+ TensorDiagonal C D n :=
      (tensorTermRetraction C D rC rD n).toAddMonoidHom.comp
        (cycles (ordinaryTotal C D) n).subtype.toAddMonoidHom
    let g := QuotientAddGroup.lift (cycleBoundaries (ordinaryTotal C D) n).toAddSubgroup f (by
      intro z hz
      obtain ⟨x, hx⟩ := hz
      change tensorTermRetraction C D rC rD n z.val = 0
      change ((ordinaryTotal C D).d ((ComplexShape.down ℕ).prev n) n).hom x = z.val at hx
      rw [← hx]
      have hd : ∀ y : (ordinaryTotal C D).X ((ComplexShape.down ℕ).prev n),
          tensorTermRetraction C D rC rD n
            (((ordinaryTotal C D).d ((ComplexShape.down ℕ).prev n) n).hom y) = 0 := by
        rw [ChainComplex.prev]
        exact tensorTermRetraction_d C D rC rD hC hD n
      exact hd x)
    let h : Homology (ordinaryTotal C D) n →+ TensorDiagonal C D n :=
      { toFun := fun z => g z
        map_zero' := g.map_zero
        map_add' := g.map_add }
    exact h.toIntLinearMap

theorem homologyRetraction_class
    (hC : ∀ p, (rC p).comp (cycles C p).subtype = LinearMap.id)
    (hD : ∀ q, (rD q).comp (cycles D q).subtype = LinearMap.id)
    (n : ℕ) (z : cycles (ordinaryTotal C D) n) :
    homologyRetraction C D rC rD hC hD n (homologyClass _ n z) =
      tensorTermRetraction C D rC rD n z.val := rfl

/-- The prescribed cycle formula alone identifies the retraction on α. -/
theorem homologyRetraction_alpha
    (hcycle : pure_tensor_cycleType.{u,v,w})
    (hC : ∀ p, (rC p).comp (cycles C p).subtype = LinearMap.id)
    (hD : ∀ q, (rD q).comp (cycles D q).subtype = LinearMap.id)
    (n : ℕ) (α : TensorDiagonal C D n →ₗ[ℤ] Homology (ordinaryTotal C D) n)
    (hα : AlphaFormula C D n α) :
    (homologyRetraction C D rC rD hC hD n).comp α = LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro t
  have he : ∀ t : TensorTerm C D i.val,
      homologyRetraction C D rC rD hC hD n
        (α (DirectSum.lof ℤ _ (fun i : Diagonal n => TensorTerm C D i.val) i t)) =
        DirectSum.lof ℤ _ (fun i : Diagonal n => TensorTerm C D i.val) i t := by
    intro t
    induction t using P103.BalancedTensor.induction_on with
    | h0 => simp
    | ha a b ha hb => simpa only [map_add, ha, hb]
    | ht a b =>
      obtain ⟨c, rfl⟩ := (cycleBoundaries C i.val.1).mkQ_surjective a
      obtain ⟨x, rfl⟩ := (cycleBoundaries D i.val.2).mkQ_surjective b
      let z : cycles (ordinaryTotal C D) n :=
        ⟨ordinaryInclusion C D i.val.1 i.val.2 n i.property (tmul R c.val x.val),
          hcycle R C D i.val.1 i.val.2 n i.property c x⟩
      change homologyRetraction C D rC rD hC hD n
        (α (DirectSum.lof ℤ _ (fun i : Diagonal n => TensorTerm C D i.val) i
          (tmul R (homologyClass C i.val.1 c) (homologyClass D i.val.2 x)))) = _
      rw [hα i c x z rfl, homologyRetraction_class]
      change tensorTermRetraction C D rC rD n
        (ordinaryInclusion C D i.val.1 i.val.2 n i.property (tmul R c.val x.val)) = _
      rw [tensorTermRetraction_inclusion, termHomologyMap_cycle C rC hC,
        termHomologyMap_cycle D rD hD]
      rfl
  exact he t


end TensorProjections

section Scalars
variable {R : Type u} [CommRing R]

theorem homologyMap_scalar (D : LeftComplex.{u,w} R) (n : ℕ) (r : R) :
    homologyMap (scalarChainMap D r) n = r • LinearMap.id := by
  apply LinearMap.ext
  intro y
  obtain ⟨z, rfl⟩ := (cycleBoundaries D n).mkQ_surjective y
  change homologyClass D n (r • z) = r • homologyClass D n z
  exact (homologyClass D n).map_smul r z

variable (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
  (rC : ∀ p, C.X p →ₗ[Rᵐᵒᵖ] cycles C p)
  (rD : ∀ q, D.X q →ₗ[R] cycles D q)

theorem tensorTermRetraction_scalar (n : ℕ) (r : R) :
    (tensorTermRetraction C D rC rD n).comp
        ((ordinaryTotalMap (𝟙 C) (scalarChainMap D r)).f n).hom =
      (tensorDiagonalMap (𝟙 C) (scalarChainMap D r) n).comp
        (tensorTermRetraction C D rC rD n) := by
  classical
  have he : (ModuleCat.ofHom ((tensorTermRetraction C D rC rD n).comp
        ((ordinaryTotalMap (𝟙 C) (scalarChainMap D r)).f n).hom) :
        (ordinaryTotal C D).X n ⟶ ModuleCat.of ℤ (TensorDiagonal C D n)) =
      ModuleCat.ofHom ((tensorDiagonalMap (𝟙 C) (scalarChainMap D r) n).comp
        (tensorTermRetraction C D rC rD n)) := by
    apply P103.Ch11.TorBalance.ordinaryTotal_hom_ext C D n
    intro p q hpq a b
    change tensorTermRetraction C D rC rD n
      (((ordinaryTotalMap (𝟙 C) (scalarChainMap D r)).f n).hom
        (ordinaryInclusion C D p q n hpq (tmul R a b))) = _
    rw [P103.Ch11.TorBalance.ordinaryTotalMap_inclusion]
    let i : Diagonal n := ⟨(p,q),hpq⟩
    change tensorTermRetraction C D rC rD n
      (ordinaryInclusion C D i.val.1 i.val.2 n i.property (tmul R a (r • b))) =
      tensorDiagonalMap (𝟙 C) (scalarChainMap D r) n
        (tensorTermRetraction C D rC rD n
          (ordinaryInclusion C D i.val.1 i.val.2 n i.property (tmul R a b)))
    rw [tensorTermRetraction_inclusion, tensorTermRetraction_inclusion]
    simp only [tensorDiagonalMap, DirectSum.lmap_lof, tensorMap_tmul]
    have hid : homologyMap (𝟙 C) i.val.1 = LinearMap.id :=
      P103.Ch10.Complexes.homologyMap_id C i.val.1
    rw [hid, homologyMap_scalar D i.val.2 r]
    change DirectSum.lof ℤ _ (fun i : Diagonal n => TensorTerm C D i.val) i
      (tmul R (termHomologyMap C rC p a) (termHomologyMap D rD q (r • b))) =
      DirectSum.lof ℤ _ (fun i : Diagonal n => TensorTerm C D i.val) i
      (tmul R (termHomologyMap C rC p a) (r • termHomologyMap D rD q b))
    rw [map_smul]
  exact congrArg ModuleCat.Hom.hom he

theorem homologyRetraction_scalar
    (hC : ∀ p, (rC p).comp (cycles C p).subtype = LinearMap.id)
    (hD : ∀ q, (rD q).comp (cycles D q).subtype = LinearMap.id)
    (n : ℕ) (r : R) :
    (homologyRetraction C D rC rD hC hD n).comp (totalScalar C D n r) =
      (tensorDiagonalMap (𝟙 C) (scalarChainMap D r) n).comp
        (homologyRetraction C D rC rD hC hD n) := by
  apply LinearMap.ext
  intro y
  refine Quotient.inductionOn y ?_
  intro z
  change tensorTermRetraction C D rC rD n
    (((ordinaryTotalMap (𝟙 C) (scalarChainMap D r)).f n).hom z.val) =
      tensorDiagonalMap (𝟙 C) (scalarChainMap D r) n
        (tensorTermRetraction C D rC rD n z.val)
  exact LinearMap.congr_fun (tensorTermRetraction_scalar C D rC rD n r) z.val

end Scalars

section PID
variable {S : Type u} [CommRing S] [IsDomain S] [IsPrincipalIdealRing S]

/-- The arbitrary-rank PID theorem supplies all the chosen cycle projections. -/
theorem free_cycle_retractions (C : ChainComplex (ModuleCat.{v} S) ℕ)
    (hC : ∀ p, Module.Free S (C.X p)) :
    ∃ r : ∀ p, C.X p →ₗ[S] cycles C p,
      ∀ p, (r p).comp (cycles C p).subtype = LinearMap.id := by
  have hP : ∀ n, Module.Projective S
      (LinearMap.range (C.d n ((ComplexShape.down ℕ).next n)).hom) := by
    intro n
    letI := hC ((ComplexShape.down ℕ).next n)
    letI := P103.Ch11.ArbitraryRankPIDSubmodules.free_submodule S
      (C.X ((ComplexShape.down ℕ).next n))
      (LinearMap.range (C.d n ((ComplexShape.down ℕ).next n)).hom)
    infer_instance
  choose r hr using exists_cycle_retraction C hP
  exact ⟨r, hr⟩

end PID

/-- Arbitrary-rank free terms and their PID submodules are genuinely flat
in the test universe of the second complex. -/
theorem free_flat_terms_boundaries {R : Type u}
    [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (C : RightComplex.{u,v} R) (hC : ∀ p, Module.Free Rᵐᵒᵖ (C.X p)) :
    P103.Specs.Ch11.UniversalCoefficientsHomology.FlatTermsAndBoundaries.{u,v,w} C := by
  letI : IsPrincipalIdealRing Rᵐᵒᵖ := IsPrincipalIdealRing.of_surjective
    (RingEquiv.toOpposite R).toRingHom (RingEquiv.toOpposite R).surjective
  constructor
  · intro p
    letI := hC p
    exact (P103.Ch02.FlatnessTests.rightFlat_iff_opposite R (C.X p)).mpr
      (P103.Ch02.FlatnessTests.projective_flat Rᵐᵒᵖ (C.X p) inferInstance)
  · intro p
    letI := hC p
    letI := P103.Ch11.ArbitraryRankPIDSubmodules.free_submodule Rᵐᵒᵖ
      (C.X p) (boundaries C p)
    exact (P103.Ch02.FlatnessTests.rightFlat_iff_opposite R (boundaries C p)).mpr
      (P103.Ch02.FlatnessTests.projective_flat Rᵐᵒᵖ (boundaries C p) inferInstance)

/-- The retraction splits every sequence with the prescribed cycle formula. -/
theorem degreeSequence_splitting (hcycle : pure_tensor_cycleType.{u,v,w}) :
    ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
      (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R),
      (∀ p, Module.Free Rᵐᵒᵖ (C.X p)) → (∀ q, Module.Free R (D.X q)) →
      ∀ (P : HomologyModels C) (n : ℕ) (S : DegreeSequence C D P n), Splits S := by
  intro R _ _ _ C D hC hD P n S
  letI : IsPrincipalIdealRing Rᵐᵒᵖ := IsPrincipalIdealRing.of_surjective
    (RingEquiv.toOpposite R).toRingHom (RingEquiv.toOpposite R).surjective
  obtain ⟨rC, hrC⟩ := free_cycle_retractions C hC
  obtain ⟨rD, hrD⟩ := free_cycle_retractions D hD
  have hr := homologyRetraction_alpha C D rC rD hcycle hrC hrD n S.α S.α_formula
  obtain ⟨s, hs⟩ := (P103.Ch01.SplitSequences.section_iff_retraction ℤ
    (TensorDiagonal C D n) (Homology (ordinaryTotal C D) n) (TorDiagonal C D P n)
    S.α S.β S.injective_α S.surjective_β S.exact).mpr
      ⟨homologyRetraction C D rC rD hrC hrD n, hr⟩
  let e := P103.Ch01.SplitSequences.splitting ℤ
    (TensorDiagonal C D n) (Homology (ordinaryTotal C D) n) (TorDiagonal C D P n)
    S.α S.β S.injective_α S.exact s hs
  refine ⟨s, hs, e, ?_, ?_⟩
  · intro a t
    rfl
  · intro a t
    change S.β (S.α a + s t) = t
    have ha : S.β (S.α a) = 0 := (S.exact _).mpr ⟨a, rfl⟩
    rw [map_add, ha, zero_add]
    exact LinearMap.congr_fun hs t

/-- The section is scalar compatible whenever the supplied last arrow is.
This generic lemma is applied below with compatibility proved by naturality. -/
theorem degreeSequence_scalar_splitting (hcycle : pure_tensor_cycleType.{u,v,w}) :
    ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
      (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R),
      (∀ p, Module.Free Rᵐᵒᵖ (C.X p)) → (∀ q, Module.Free R (D.X q)) →
      ∀ (P : HomologyModels C) (n : ℕ) (S : DegreeSequence C D P n)
        (T : TorMaps.{u,v,w} R 1),
      (∀ r, S.β.comp (totalScalar C D n r) = (torScalar C D P T n r).comp S.β) →
      ScalarSplits S T := by
  intro R _ _ _ C D hC hD P n S T hβscalar
  letI : IsPrincipalIdealRing Rᵐᵒᵖ := IsPrincipalIdealRing.of_surjective
    (RingEquiv.toOpposite R).toRingHom (RingEquiv.toOpposite R).surjective
  obtain ⟨rC, hrC⟩ := free_cycle_retractions C hC
  obtain ⟨rD, hrD⟩ := free_cycle_retractions D hD
  let ρ := homologyRetraction C D rC rD hrC hrD n
  have hi : ∀ a, ρ (S.α a) = a :=
    LinearMap.congr_fun (homologyRetraction_alpha C D rC rD hcycle hrC hrD n S.α S.α_formula)
  have hβ0 : ∀ a, S.β (S.α a) = 0 := fun a => (S.exact _).mpr ⟨a, rfl⟩
  obtain ⟨s0, hs0, _⟩ :=
    degreeSequence_splitting hcycle R C D hC hD P n S
  let s := s0 - S.α.comp (ρ.comp s0)
  have hs : ∀ t, S.β (s t) = t := by
    intro t
    change S.β (s0 t - S.α (ρ (s0 t))) = t
    rw [map_sub, hβ0, sub_zero]
    exact LinearMap.congr_fun hs0 t
  have hρs : ∀ t, ρ (s t) = 0 := by
    intro t
    change ρ (s0 t - S.α (ρ (s0 t))) = 0
    rw [map_sub, hi, sub_self]
  have hjoint : ∀ z, S.β z = 0 → ρ z = 0 → z = 0 := by
    intro z hz hρz
    obtain ⟨a, ha⟩ := (S.exact z).mp hz
    have haz := congrArg ρ ha
    rw [hi, hρz] at haz
    rw [← ha, haz, map_zero]
  refine ⟨s, ?_, ?_⟩
  · apply LinearMap.ext
    intro t
    exact hs t
  · intro r
    have hβr : ∀ z, S.β (totalScalar C D n r z) = torScalar C D P T n r (S.β z) :=
      LinearMap.congr_fun (hβscalar r)
    have hρr : ∀ z, ρ (totalScalar C D n r z) =
        tensorDiagonalMap (𝟙 C) (scalarChainMap D r) n (ρ z) :=
      LinearMap.congr_fun (homologyRetraction_scalar C D rC rD hrC hrD n r)
    apply LinearMap.ext
    intro t
    change totalScalar C D n r (s t) = s (torScalar C D P T n r t)
    apply sub_eq_zero.mp
    apply hjoint
    · rw [map_sub, hβr, hs, hs, sub_self]
    · rw [map_sub, hρr, hρs, hρs, map_zero, sub_self]

/-- Conditional derivation under the ten complete upstream propositions,
in the exact contract order. The original closed target is left to the owner. -/
theorem splitting_conditional :
    alpha_naturalType.{u,v,w} →
    cycles_flatType.{u,v,w} →
    left_natural_sequenceType.{u,v,w} →
    left_sequenceType.{u,v,w} →
    normalized_naturalType.{u,v,w} →
    pure_tensor_cycleType.{u,v,w} →
    pure_tensor_naturalType.{u,v,w} →
    right_sequenceType.{u,v,w} →
    scalar_compatibilityType.{u,v,w} →
    tor_diagonal_zeroType.{u,v,w} →
    P103.Specs.Ch11.KunnethFreeSplitting.splittingType.{u,v,w} := by
  intro _halpha _hcycles _hleftnatural _hleft _hnatural hcycle _hpure hright _hscalar _hzero
  intro R _ _ _ C D hC hD P n
  exact ⟨hright R C (free_flat_terms_boundaries C hC) D P n,
    degreeSequence_splitting hcycle R C D hC hD P n⟩

/-- Naturality supplies scalar compatibility of the actual normalized last
arrow, so no extra scalar certificate is a premise of the splitting result. -/
theorem scalar_splitting_conditional :
    alpha_naturalType.{u,v,w} →
    cycles_flatType.{u,v,w} →
    left_natural_sequenceType.{u,v,w} →
    left_sequenceType.{u,v,w} →
    normalized_naturalType.{u,v,w} →
    pure_tensor_cycleType.{u,v,w} →
    pure_tensor_naturalType.{u,v,w} →
    right_sequenceType.{u,v,w} →
    scalar_compatibilityType.{u,v,w} →
    tor_diagonal_zeroType.{u,v,w} →
    scalar_splittingType.{u,v,w} := by
  intro _halpha _hcycles _hleftnatural _hleft hnatural hcycle _hpure hright _hscalar _hzero
  intro R _ _ _ C D hC hD P n T
  refine ⟨hright R C (free_flat_terms_boundaries C hC) D P n, ?_⟩
  intro S
  apply degreeSequence_scalar_splitting hcycle R C D hC hD P n S.toDegreeSequence T
  intro r
  exact (hnatural R C C D D (𝟙 C) (scalarChainMap D r) P P T n S S).2.symm

end
end P103.Ch11.KunnethFreeSplitting

universe v8_closure_a92ee8e5d11f7f0a_u0 v8_closure_a92ee8e5d11f7f0a_u1 v8_closure_a92ee8e5d11f7f0a_u2
theorem _root_.«P103».«Ch11».«KunnethFreeSplitting».«scalar_splitting» : _root_.«P103».«Specs».«Ch11».«KunnethFreeSplitting».«scalar_splittingType».{v8_closure_a92ee8e5d11f7f0a_u0, v8_closure_a92ee8e5d11f7f0a_u1, v8_closure_a92ee8e5d11f7f0a_u2} :=
  @_root_.«P103».«Ch11».«KunnethFreeSplitting».«scalar_splitting_conditional».{v8_closure_a92ee8e5d11f7f0a_u0, v8_closure_a92ee8e5d11f7f0a_u1, v8_closure_a92ee8e5d11f7f0a_u2} (@_root_.«P103».«Ch11».«KunnethSequence».«alpha_natural».{v8_closure_a92ee8e5d11f7f0a_u0, v8_closure_a92ee8e5d11f7f0a_u1, v8_closure_a92ee8e5d11f7f0a_u2}) (@_root_.«P103».«Ch11».«KunnethSequence».«cycles_flat».{v8_closure_a92ee8e5d11f7f0a_u0, v8_closure_a92ee8e5d11f7f0a_u1, v8_closure_a92ee8e5d11f7f0a_u2}) (@_root_.«P103».«Ch11».«KunnethSequence».«left_natural_sequence».{v8_closure_a92ee8e5d11f7f0a_u0, v8_closure_a92ee8e5d11f7f0a_u1, v8_closure_a92ee8e5d11f7f0a_u2}) (@_root_.«P103».«Ch11».«KunnethSequence».«left_sequence».{v8_closure_a92ee8e5d11f7f0a_u0, v8_closure_a92ee8e5d11f7f0a_u1, v8_closure_a92ee8e5d11f7f0a_u2}) (@_root_.«P103».«Ch11».«KunnethSequence».«normalized_natural».{v8_closure_a92ee8e5d11f7f0a_u0, v8_closure_a92ee8e5d11f7f0a_u1, v8_closure_a92ee8e5d11f7f0a_u2}) (@_root_.«P103».«Ch11».«KunnethSequence».«pure_tensor_cycle».{v8_closure_a92ee8e5d11f7f0a_u0, v8_closure_a92ee8e5d11f7f0a_u1, v8_closure_a92ee8e5d11f7f0a_u2}) (@_root_.«P103».«Ch11».«KunnethSequence».«pure_tensor_natural».{v8_closure_a92ee8e5d11f7f0a_u0, v8_closure_a92ee8e5d11f7f0a_u1, v8_closure_a92ee8e5d11f7f0a_u2}) (@_root_.«P103».«Ch11».«KunnethSequence».«right_sequence».{v8_closure_a92ee8e5d11f7f0a_u0, v8_closure_a92ee8e5d11f7f0a_u1, v8_closure_a92ee8e5d11f7f0a_u2}) (@_root_.«P103».«Ch11».«KunnethSequence».«scalar_compatibility».{v8_closure_a92ee8e5d11f7f0a_u0, v8_closure_a92ee8e5d11f7f0a_u1, v8_closure_a92ee8e5d11f7f0a_u2}) (@_root_.«P103».«Ch11».«KunnethSequence».«tor_diagonal_zero».{v8_closure_a92ee8e5d11f7f0a_u0, v8_closure_a92ee8e5d11f7f0a_u1, v8_closure_a92ee8e5d11f7f0a_u2})
theorem _root_.«P103».«Ch11».«KunnethFreeSplitting».«splitting» : _root_.«P103».«Specs».«Ch11».«KunnethFreeSplitting».«splittingType».{v8_closure_a92ee8e5d11f7f0a_u0, v8_closure_a92ee8e5d11f7f0a_u1, v8_closure_a92ee8e5d11f7f0a_u2} :=
  @_root_.«P103».«Ch11».«KunnethFreeSplitting».«splitting_conditional».{v8_closure_a92ee8e5d11f7f0a_u0, v8_closure_a92ee8e5d11f7f0a_u1, v8_closure_a92ee8e5d11f7f0a_u2} (@_root_.«P103».«Ch11».«KunnethSequence».«alpha_natural».{v8_closure_a92ee8e5d11f7f0a_u0, v8_closure_a92ee8e5d11f7f0a_u1, v8_closure_a92ee8e5d11f7f0a_u2}) (@_root_.«P103».«Ch11».«KunnethSequence».«cycles_flat».{v8_closure_a92ee8e5d11f7f0a_u0, v8_closure_a92ee8e5d11f7f0a_u1, v8_closure_a92ee8e5d11f7f0a_u2}) (@_root_.«P103».«Ch11».«KunnethSequence».«left_natural_sequence».{v8_closure_a92ee8e5d11f7f0a_u0, v8_closure_a92ee8e5d11f7f0a_u1, v8_closure_a92ee8e5d11f7f0a_u2}) (@_root_.«P103».«Ch11».«KunnethSequence».«left_sequence».{v8_closure_a92ee8e5d11f7f0a_u0, v8_closure_a92ee8e5d11f7f0a_u1, v8_closure_a92ee8e5d11f7f0a_u2}) (@_root_.«P103».«Ch11».«KunnethSequence».«normalized_natural».{v8_closure_a92ee8e5d11f7f0a_u0, v8_closure_a92ee8e5d11f7f0a_u1, v8_closure_a92ee8e5d11f7f0a_u2}) (@_root_.«P103».«Ch11».«KunnethSequence».«pure_tensor_cycle».{v8_closure_a92ee8e5d11f7f0a_u0, v8_closure_a92ee8e5d11f7f0a_u1, v8_closure_a92ee8e5d11f7f0a_u2}) (@_root_.«P103».«Ch11».«KunnethSequence».«pure_tensor_natural».{v8_closure_a92ee8e5d11f7f0a_u0, v8_closure_a92ee8e5d11f7f0a_u1, v8_closure_a92ee8e5d11f7f0a_u2}) (@_root_.«P103».«Ch11».«KunnethSequence».«right_sequence».{v8_closure_a92ee8e5d11f7f0a_u0, v8_closure_a92ee8e5d11f7f0a_u1, v8_closure_a92ee8e5d11f7f0a_u2}) (@_root_.«P103».«Ch11».«KunnethSequence».«scalar_compatibility».{v8_closure_a92ee8e5d11f7f0a_u0, v8_closure_a92ee8e5d11f7f0a_u1, v8_closure_a92ee8e5d11f7f0a_u2}) (@_root_.«P103».«Ch11».«KunnethSequence».«tor_diagonal_zero».{v8_closure_a92ee8e5d11f7f0a_u0, v8_closure_a92ee8e5d11f7f0a_u1, v8_closure_a92ee8e5d11f7f0a_u2})
