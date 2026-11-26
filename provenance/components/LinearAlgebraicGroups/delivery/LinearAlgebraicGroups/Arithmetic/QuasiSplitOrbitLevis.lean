import Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis
import LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
import LinearAlgebraicGroups.Arithmetic.UnitaryRankOne
import LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitTorusProduct
import LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitDerivedRoots
import LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitPinnedModels
import LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitAmbientWords
import LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import LinearAlgebraicGroups.Descent.AdjointBorelCohomology
import LinearAlgebraicGroups.RootData.SpecialLinearDatum
import LinearAlgebraicGroups.Flag.StandardParabolics
import LinearAlgebraicGroups.Relative.Parabolics
import LinearAlgebraicGroups.Reductive.CentralDerived
import LinearAlgebraicGroups.Multiplicative.CharacterDescent
import LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory
open Module
open HopfAlgebra Coalgebra
open scoped BigOperators CategoryTheory.MonObj TensorProduct LinearAlgebraicGroups.Descent

universe u v w

namespace LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis

open Specs.QuasiSplitOrbitLevis

set_option linter.style.haveILetI false

noncomputable section


open LieAlgebrasAndRepresentations
open Specs.AbsoluteDynkinTypes (PreservesCartan D4Cartan E6Reflection)
open LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
  (cartanPermutationTransport typeAPermutations typeBCPermutations typeDPermutations
    d4Permutations exceptionalPermutations)
open private d4_entry from LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
open LinearAlgebraicGroups.Classification.SimplyConnectedLattice (latticeCriterion)
open Specs.SimplyConnectedLattice (corootLatticeOf)
open RootData (integralCartan)

private theorem typeA_adjacent_rev {n : ℕ} (j : Fin n) (hne : j ≠ j.rev)
    (hadj : CartanMatrix.A n j j.rev ≠ 0 ∨ CartanMatrix.A n j.rev j ≠ 0) :
    0 < n / 2 ∧ n = 2 * (n / 2) ∧
      ((j.val = n / 2 - 1 ∧ j.rev.val = n / 2) ∨
        (j.rev.val = n / 2 - 1 ∧ j.val = n / 2)) := by
  simp only [CartanMatrix.A, Matrix.of_apply, ite_eq_right hne, ite_eq_right (Ne.symm hne)] at hadj
  have h : j.val + 1 = j.rev.val ∨ j.rev.val + 1 = j.val := by
    by_contra! hn
    simp only [ite_eq_right (not_or.mpr hn), ite_eq_right (not_or.mpr (And.symm hn)), ne_self_iff_false, or_self] at hadj
  have hs := Fin.val_rev j
  have hj := j.isLt
  have hj' := j.rev.isLt
  omega

private theorem orthogonalMovedVertex (t : FiniteDynkinType)
    (hn : ∀ m h, t ≠ .A m h) :
    ∀ (σ : Equiv.Perm (Fin t.rank)), PreservesCartan t.cartan t.cartan σ →
      ∀ j, j ≠ σ j → t.cartan j (σ j) = 0 ∧ t.cartan (σ j) j = 0 := by
  cases t with
  | A n h => exact (hn n h rfl).elim
  | B n h =>
      intro σ hσ j hj
      exact (hj (congrFun (congrArg Equiv.toFun (((typeBCPermutations n h σ).2).mp hσ)) j).symm).elim
  | C n h =>
      intro σ hσ j hj
      exact (hj (congrFun (congrArg Equiv.toFun (((typeBCPermutations n h σ).1).mp hσ)) j).symm).elim
  | D n h =>
      intro σ hσ j hj
      rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | h5
      · change Equiv.Perm (Fin 4) at σ
        change Fin 4 at j
        have hfix : σ (1 : Fin 4) = 1 := (d4Permutations σ).mp hσ
        have hleft : j ≠ 1 := by
          intro he
          apply hj
          exact he.trans (hfix.symm.trans (congrArg (fun x : Fin 4 => σ x) he.symm))
        have hright : σ j ≠ 1 := fun he => hleft (σ.injective (he.trans hfix.symm))
        change CartanMatrix.D 4 j (σ j) = 0 ∧ CartanMatrix.D 4 (σ j) j = 0
        have hne : j ≠ σ j := hj
        simp [d4_entry, hne, Ne.symm hne, hleft, hright]
      · change Equiv.Perm (Fin n) at σ
        change Fin n at j
        change CartanMatrix.D n j (σ j) = 0 ∧ CartanMatrix.D n (σ j) j = 0
        rcases (typeDPermutations n h5 σ).mp hσ with rfl | hs
        · exact (hj rfl).elim
        let a : Fin n := ⟨n - 2, by omega⟩
        let b : Fin n := ⟨n - 1, by omega⟩
        change σ = Equiv.swap a b at hs
        have hab : a ≠ b := by
          intro he
          have hval := congrArg Fin.val he
          dsimp [a, b] at hval
          omega
        have hz : CartanMatrix.D n a b = 0 ∧ CartanMatrix.D n b a = 0 := by
          simp only [CartanMatrix.D, Matrix.of_apply, ite_eq_right hab, ite_eq_right (Ne.symm hab)]
          have ha : a.val = n - 2 := rfl
          have hb : b.val = n - 1 := rfl
          constructor <;> split_ifs <;> omega
        by_cases ja : j = a
        · subst j
          simpa only [hs, Equiv.swap_apply_left] using hz
        by_cases jb : j = b
        · subst j
          simpa only [hs, Equiv.swap_apply_right] using And.symm hz
        exact (hj ((congrFun (congrArg Equiv.toFun hs) j).trans (Equiv.swap_apply_of_ne_of_ne ja jb)).symm).elim
  | E6 =>
      intro σ hσ j hj
      rcases exceptionalPermutations.1 σ |>.mp hσ with rfl | rfl
      · exact (hj rfl).elim
      · exact (show ∀ i : Fin 6, i ≠ E6Reflection i →
            CartanMatrix.E 6 i (E6Reflection i) = 0 ∧
              CartanMatrix.E 6 (E6Reflection i) i = 0 by decide +kernel) j hj
  | E7 =>
      intro σ hσ j hj
      rw [(exceptionalPermutations.2.1 σ).mp hσ] at hj
      exact (hj rfl).elim
  | E8 =>
      intro σ hσ j hj
      rw [(exceptionalPermutations.2.2.1 σ).mp hσ] at hj
      exact (hj rfl).elim
  | F4 =>
      intro σ hσ j hj
      rw [(exceptionalPermutations.2.2.2.1 σ).mp hσ] at hj
      exact (hj rfl).elim
  | G2 =>
      intro σ hσ j hj
      rw [(exceptionalPermutations.2.2.2.2 σ).mp hσ] at hj
      exact (hj rfl).elim

private theorem orbitPermutation {Γ : Type u} {I : Type v} [Group Γ]
    (ρ : Γ →* Equiv.Perm I) {i x y : I} (hx : x ∈ diagramOrbit ρ i)
    (hy : y ∈ diagramOrbit ρ i) :
    ∃ g, ρ g x = y := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  refine ⟨b * a⁻¹, ?_⟩
  rw [map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply]

theorem cartanOrbitShapes : CartanOrbitShapes.{u,v} := by
  classical
  intro Γ I _ A t ht ρ hρ i
  obtain ⟨e, he⟩ := ht
  by_cases ho : ∀ x ∈ diagramOrbit ρ i, ∀ y ∈ diagramOrbit ρ i, x ≠ y →
      A x y = 0 ∧ A y x = 0
  · exact Or.inl ho
  push Not at ho
  obtain ⟨x, hx, y, hy, hxy, hadj⟩ := ho
  obtain ⟨g, hg⟩ := orbitPermutation ρ hx hy
  let σ : Equiv.Perm (Fin t.rank) := (e.symm.trans (ρ g)).trans e
  have hσ : PreservesCartan t.cartan t.cartan σ :=
    (cartanPermutationTransport he (ρ g)).mp (hρ g)
  have hσx : σ (e x) = e y := by simp [σ, hg]
  have hne : e x ≠ σ (e x) := by simpa [hσx] using hxy
  have htype : ∃ n hn, t = .A n hn := by
    by_contra! ht
    obtain ⟨h₁, h₂⟩ := orthogonalMovedVertex t ht σ hσ (e x) hne
    rw [hσx] at h₁ h₂
    exact hadj (he x y |>.trans h₁) (he y x |>.trans h₂)
  obtain ⟨n, hn, rfl⟩ := htype
  change I ≃ Fin n at e
  change Equiv.Perm (Fin n) at σ
  have hrev : σ = Fin.revPerm := by
    rcases (typeAPermutations n σ).mp hσ with h | h
    · exact (hne (congrFun (congrArg Equiv.toFun h) (e x)).symm).elim
    · exact h
  have hyrev : e y = (e x).rev := hσx.symm.trans (congrFun (congrArg Equiv.toFun hrev) (e x))
  have hnonzero : CartanMatrix.A n (e x) (e y) ≠ 0 ∨ CartanMatrix.A n (e y) (e x) ≠ 0 := by
    by_contra! h
    exact hadj (he x y |>.trans h.1) (he y x |>.trans h.2)
  have hxrev : e x ≠ (e x).rev := by simpa only [← hyrev] using e.injective.ne hxy
  rw [hyrev] at hnonzero
  obtain ⟨hhalf, hsize, hmiddle⟩ := typeA_adjacent_rev (e x) hxrev hnonzero
  have horbit : e '' diagramOrbit ρ i = {e x, e y} := by
    ext q
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨a, ha⟩ := orbitPermutation ρ hx hj
      let π := (e.symm.trans (ρ a)).trans e
      have hπ : PreservesCartan (CartanMatrix.A n) (CartanMatrix.A n) π :=
        (cartanPermutationTransport he (ρ a)).mp (hρ a)
      have hcalc : π (e x) = e j := by simp [π, ha]
      rcases (typeAPermutations n π).mp hπ with h | h
      · exact Or.inl (hcalc.symm.trans (congrFun (congrArg Equiv.toFun h) (e x)))
      · exact Or.inr ((hcalc.symm.trans (congrFun (congrArg Equiv.toFun h) (e x))).trans hyrev.symm)
    · rintro (rfl | rfl)
      · exact ⟨x, hx, rfl⟩
      · exact ⟨y, hy, rfl⟩
  let r := n / 2
  change n = 2 * r at hsize
  refine Or.inr ⟨r, hhalf, e.trans (finCongr hsize), ?_, ?_⟩
  · intro a b
    refine (he a b).trans ?_
    change CartanMatrix.A n (e a) (e b) =
      CartanMatrix.A (2 * r) (finCongr hsize (e a)) (finCongr hsize (e b))
    simp only [CartanMatrix.A, Matrix.of_apply, (finCongr hsize).apply_eq_iff_eq,
      finCongr_apply_coe, Int.reduceNeg]
    try rfl
  · change ((finCongr hsize) ∘ e) '' diagramOrbit ρ i = _
    calc
      _ = (finCongr hsize) '' (e '' diagramOrbit ρ i) :=
        (Set.image_image _ _ _).symm
      _ = _ := ?_
    rw [horbit]
    simp only [Set.image_insert_eq, Set.image_singleton]
    change ((e x).val = r - 1 ∧ (e x).rev.val = r) ∨
      ((e x).rev.val = r - 1 ∧ (e x).val = r) at hmiddle
    rw [← hyrev] at hmiddle
    rcases hmiddle with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · rw [show finCongr hsize (e x) = ⟨r - 1, by omega⟩ from Fin.ext hl,
          show finCongr hsize (e y) = ⟨r, by omega⟩ from Fin.ext hr]
    · rw [show finCongr hsize (e y) = ⟨r - 1, by omega⟩ from Fin.ext hl,
          show finCongr hsize (e x) = ⟨r, by omega⟩ from Fin.ext hr]
      ext z
      simp [or_comm]

theorem attachedOrbitShapes : AttachedOrbitShapes.{u,v} := by
  intro k _ P D h Γ _ ω i
  letI := D.comm
  obtain ⟨_, _, _, _, _, t, e, he, _, _⟩ := h
  apply cartanOrbitShapes _ t ⟨e, he⟩ _ _ i
  intro g a b
  exact ((ω g).asIso.hom.val.toHom.pairing (i := b.val) (j := a.val)).symm

theorem attachedCorootBasis : AttachedCorootBasis.{u} := by
  intro k _ P D hG hsc
  letI := D.comm
  have h := (latticeCriterion P.G hG P.T P.split P.maximal D.datum).mp hsc
  have hspan : Submodule.span ℤ (Set.range fun i : D.base.support => D.datum.rootDatum.coroot i.val) = ⊤ := by
    change Submodule.span ℤ (Set.range fun i : (↑D.base.support : Set _) =>
      D.datum.rootDatum.coroot i.val) = ⊤
    rw [← Set.image_eq_range, D.base.span_int_coroot_support]
    exact h
  refine ⟨Basis.mk D.base.linearIndepOn_coroot hspan.ge, fun i => ?_⟩
  exact Basis.mk_apply _ _ i

theorem integralPointsOfBasisSpan : IntegralPointsOfBasisSpan.{u,v} := by
  intro I Y _ b s y
  rw [← Finsupp.supported_eq_span_single, Finsupp.mem_supported', b.mem_span_image]
  simp only [Finsupp.mapRange_apply, Int.cast_eq_zero]
  simp [Set.subset_def, not_imp_comm]

theorem quadraticTensorSplitting : QuadraticTensorSplitting.{u,v} := by
  intro F E _ _ _ _ _
  let σ := Specs.UnitaryRankOne.quadraticConjugation F E
  obtain ⟨a, ha⟩ : ∃ a : E, σ a ≠ a := by
    by_contra! h
    exact Specs.UnitaryRankOne.quadraticConjugation_ne_one F E (AlgEquiv.ext h)
  let f : E ⊗[F] E →ₐ[E] E × E :=
    Algebra.TensorProduct.lift (Algebra.ofId E (E × E))
      ((AlgHom.id F E).prod σ.toAlgHom) (fun _ _ => Commute.all _ _)
  have hf (x y : E) : f (x ⊗ₜ[F] y) = (x * y, x * σ y) := rfl
  have hos : ∃ z, f z = (0, 1) := by
    let d := σ a - a
    have hd : d ≠ 0 := sub_ne_zero.mpr ha
    refine ⟨(d⁻¹ ⊗ₜ[F] a) - ((d⁻¹ * a) ⊗ₜ[F] 1), ?_⟩
    rw [map_sub, hf, hf]
    apply Prod.ext
    · simp
    · change d⁻¹ * σ a - (d⁻¹ * a) * σ 1 = 1
      rw [map_one, mul_one, ← mul_sub, inv_mul_cancel₀ hd]
  obtain ⟨z, hz⟩ := hos
  have hsurj : Function.Surjective f := by
    rintro ⟨x, y⟩
    refine ⟨(x ⊗ₜ[F] 1) + ((y - x) ⊗ₜ[F] 1) * z, ?_⟩
    rw [map_add, map_mul, hf, hf, hz]
    apply Prod.ext <;> simp
  have hdeg := Algebra.IsQuadraticExtension.finrank_eq_two F E
  let : FiniteDimensional F E := .of_finrank_pos (hdeg ▸ Nat.zero_lt_succ _)
  have hdim : Module.finrank E (E ⊗[F] E) = Module.finrank E (E × E) := by
    rw [Module.finrank_baseChange, Module.finrank_prod, Module.finrank_self, hdeg]
  have hinj : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
  exact ⟨AlgEquiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩


theorem unitaryScalarSplitting : UnitaryScalarSplitting.{u,v} := by
  intro F E _ _ _ _ _ R _ _ _ _
  obtain ⟨e, he⟩ := quadraticTensorSplitting F E
  let f : R ⊗[F] E ≃ₐ[R] R × R :=
    (Algebra.TensorProduct.cancelBaseChange F E R R E).symm.trans
      ((Algebra.TensorProduct.congr (.refl : R ≃ₐ[R] R) e).trans
        ((Algebra.TensorProduct.prodRight E R R E E).trans
          ((Algebra.TensorProduct.rid E R R).prodCongr (Algebra.TensorProduct.rid E R R))))
  have hf (x : R) (y : E) : f (x ⊗ₜ[F] y) =
      (x * algebraMap E R y,
        x * algebraMap E R (Specs.UnitaryRankOne.quadraticConjugation F E y)) := by
    dsimp only [f, AlgEquiv.trans_apply]
    rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul, Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.map_tmul]
    change ((Algebra.TensorProduct.rid E R R).prodCongr (Algebra.TensorProduct.rid E R R))
      ((Algebra.TensorProduct.prodRight E R R E E) (x ⊗ₜ[E] e (1 ⊗ₜ[F] y))) = _
    rw [he, Algebra.TensorProduct.prodRight_tmul]
    ext <;> simp [Algebra.smul_def, mul_comm]
  refine ⟨f, hf, fun z => ?_⟩
  let σ := Specs.UnitaryRankOne.quadraticConjugation F E
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      rw [quadraticTensorInvolution, Algebra.TensorProduct.congr_apply,
        Algebra.TensorProduct.map_tmul]
      change f (x ⊗ₜ[F] σ y) = (f (x ⊗ₜ[F] y)).swap
      rw [hf, hf, Prod.swap_prod_mk]
      have hσ : σ (σ y) = y := by
        have hd := Algebra.IsQuadraticExtension.finrank_eq_two F E
        let : FiniteDimensional F E := .of_finrank_pos (hd ▸ Nat.zero_lt_succ 1)
        have hc : Nat.card (E ≃ₐ[F] E) = 2 := (IsGalois.card_aut_eq_finrank F E).trans hd
        have h := pow_card_eq_one' (x := σ)
        rw [hc, pow_two] at h
        exact DFunLike.congr_fun h y
      simp only [← show σ = Specs.UnitaryRankOne.quadraticConjugation F E from rfl, hσ]
  | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy]
      rfl

section UnitaryModel

open Matrix

open Matrix.SpecialLinearGroup in
private def hyperbolicDual {R : Type v} [CommRing R] : SL₃ R →* SL₃ R where
  toFun := hyperbolicInverseTranspose
  map_one' := by
    apply Subtype.ext
    simp [hyperbolicInverseTranspose, Matrix.submatrix_one_equiv]
  map_mul' a b := by
    apply Subtype.ext
    change ((a * b)⁻¹).val.transpose.submatrix Fin.revPerm Fin.revPerm =
      (a⁻¹).val.transpose.submatrix Fin.revPerm Fin.revPerm *
      (b⁻¹).val.transpose.submatrix Fin.revPerm Fin.revPerm
    rw [_root_.mul_inv_rev, coe_mul, Matrix.transpose_mul, Matrix.submatrix_mul_equiv]

private theorem hyperbolicDual_involutive {R : Type v} [CommRing R] (g : SL₃ R) :
    hyperbolicDual (hyperbolicDual g) = g := by
  have hi : (hyperbolicDual g)⁻¹ = hyperbolicDual g⁻¹ := (map_inv _ _).symm
  apply Subtype.ext
  change ((hyperbolicDual g)⁻¹).val.transpose.submatrix Fin.revPerm Fin.revPerm = g.val
  rw [hi]
  ext i j
  change ((g⁻¹)⁻¹).val (Fin.rev (Fin.rev i)) (Fin.rev (Fin.rev j)) = g.val i j
  rw [inv_inv, Fin.rev_rev, Fin.rev_rev]

open Matrix.SpecialLinearGroup in
private theorem hyperbolicDual_map {R S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (g : SL₃ R) :
    hyperbolicDual (SpecialLinearGroup.map f g) = SpecialLinearGroup.map f (hyperbolicDual g) := by
  apply Subtype.ext
  change ((SpecialLinearGroup.map f g)⁻¹).val.transpose.submatrix Fin.revPerm Fin.revPerm =
    f.mapMatrix ((g⁻¹).val.transpose.submatrix Fin.revPerm Fin.revPerm)
  rw [← map_inv]
  rfl

open Matrix.SpecialLinearGroup in
private def slProduct (R : Type v) [CommRing R] : SL₃ (R × R) ≃* SL₃ R × SL₃ R :=
  MulEquiv.ofBijective ((SpecialLinearGroup.map (RingHom.fst R R)).prod (SpecialLinearGroup.map (RingHom.snd R R))) (by
    constructor
    · intro a b h
      apply Subtype.ext
      ext1 i j
      exact Prod.ext (congrArg (fun g : SL₃ R × SL₃ R => g.1.val i j) h)
        (congrArg (fun g : SL₃ R × SL₃ R => g.2.val i j) h)
    · rintro ⟨a, b⟩
      let A : Matrix (Fin 3) (Fin 3) (R × R) := fun i j => (a.val i j, b.val i j)
      have ha : (RingHom.fst R R).mapMatrix A = a.val := rfl
      have hb : (RingHom.snd R R).mapMatrix A = b.val := rfl
      have hA : A.det = 1 := by
        apply Prod.ext
        · change (RingHom.fst R R) A.det = 1
          rw [RingHom.map_det, ha, a.property]
        · change (RingHom.snd R R) A.det = 1
          rw [RingHom.map_det, hb, b.property]
      exact ⟨⟨A, hA⟩, Prod.ext (Subtype.ext ha) (Subtype.ext hb)⟩)

open Matrix.SpecialLinearGroup in
private def slRingEquiv {A B : Type v} [CommRing A] [CommRing B] (e : A ≃+* B) :
    SL₃ A ≃* SL₃ B where
  toFun := SpecialLinearGroup.map e.toRingHom
  invFun := SpecialLinearGroup.map e.symm.toRingHom
  left_inv g := by ext i j; exact e.symm_apply_apply _
  right_inv g := by ext i j; exact e.apply_symm_apply _
  map_mul' := map_mul (SpecialLinearGroup.map e.toRingHom)

open Matrix.SpecialLinearGroup in
theorem splitUnitaryPoints : SplitUnitaryPoints.{u,v} := by
  intro F E _ _ _ _ _ R _ _ _ _ e he
  let σ := quadraticTensorInvolution F E R
  let τ : SL₃ (R ⊗[F] E) →* SL₃ (R ⊗[F] E) :=
    hyperbolicDual.comp (map σ.toRingEquiv.toRingHom)
  let t := (slRingEquiv e.toRingEquiv).trans (slProduct R)
  let U := τ.eqLocus (MonoidHom.id _)
  have first_eq (g : SL₃ (R ⊗[F] E)) : (t g).1 =
      SpecialLinearGroup.map ((RingHom.fst R R).comp e.toRingEquiv.toRingHom) g := by
    ext i j
    rfl
  have second_eq (g : SL₃ (R ⊗[F] E)) : (t g).2 =
      SpecialLinearGroup.map ((RingHom.snd R R).comp e.toRingEquiv.toRingHom) g := by
    ext i j
    rfl
  have act (g : SL₃ (R ⊗[F] E)) :
      t (τ g) = (hyperbolicDual (t g).2, hyperbolicDual (t g).1) := by
    have h₁ : SpecialLinearGroup.map ((RingHom.fst R R).comp e.toRingEquiv.toRingHom)
        (map σ.toRingEquiv.toRingHom g) =
        SpecialLinearGroup.map ((RingHom.snd R R).comp e.toRingEquiv.toRingHom) g := by
      ext i j
      exact congrArg Prod.fst (he (g.val i j))
    have h₂ : SpecialLinearGroup.map ((RingHom.snd R R).comp e.toRingEquiv.toRingHom)
        (map σ.toRingEquiv.toRingHom g) =
        SpecialLinearGroup.map ((RingHom.fst R R).comp e.toRingEquiv.toRingHom) g := by
      ext i j
      exact congrArg Prod.snd (he (g.val i j))
    apply Prod.ext
    · simp only [first_eq, second_eq]
      change SpecialLinearGroup.map ((RingHom.fst R R).comp e.toRingEquiv.toRingHom)
        (hyperbolicDual (map σ.toRingEquiv.toRingHom g)) =
        hyperbolicDual (SpecialLinearGroup.map ((RingHom.snd R R).comp e.toRingEquiv.toRingHom) g)
      rw [← hyperbolicDual_map, h₁]
    · simp only [first_eq, second_eq, ]
      change SpecialLinearGroup.map ((RingHom.snd R R).comp e.toRingEquiv.toRingHom)
        (hyperbolicDual (map σ.toRingEquiv.toRingHom g)) =
        hyperbolicDual (SpecialLinearGroup.map ((RingHom.fst R R).comp e.toRingEquiv.toRingHom) g)
      rw [← hyperbolicDual_map, h₂]
  let p : U →* SL₃ R := (MonoidHom.fst _ _).comp (t.toMonoidHom.comp U.subtype)
  have second (g : U) : hyperbolicDual (t g.val).1 = (t g.val).2 := by
    have hg : τ g.val = g.val := g.prop
    exact congrArg Prod.snd ((act g.val).symm.trans (congrArg t hg))
  have hp : Function.Bijective p := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply t.injective
      exact Prod.ext h (((second x).symm.trans (congrArg hyperbolicDual h)).trans (second y))
    · intro g
      let b := t.symm (g, hyperbolicDual g)
      have hb : t b = (g, hyperbolicDual g) := t.apply_symm_apply _
      have hbU : b ∈ U := by
        change τ b = b
        apply t.injective
        rw [act, hb, hyperbolicDual_involutive]
      exact ⟨⟨b, hbU⟩, congrArg Prod.fst hb⟩
  refine ⟨U, fun _ => Iff.rfl, MulEquiv.ofBijective p hp, ?_, ?_⟩
  · exact fun g => first_eq g.val
  · intro g
    rw [← second_eq]
    exact second g


open Specs.SpecialLinearDatum (coordinatePairUnits)

variable {R : Type u} [CommRing R]

private theorem matrixSimpleCoroot_inv (i : Fin 2) (t : Rˣ) :
    (matrixSimpleCoroot i t)⁻¹ = matrixSimpleCoroot i t⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change Matrix.diagonal _ * Matrix.diagonal _ = (1 : Matrix (Fin 3) (Fin 3) R)
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  by_cases hj : j = i.castSucc
  · simp [coordinatePairUnits, hj]
  by_cases hk : j = i.succ
  · have hs : i.succ ≠ i.castSucc := ((Fin.castSucc_lt_succ_iff).2 (le_refl i)).ne'
    simp [coordinatePairUnits, hk, hs]
  · simp [coordinatePairUnits, hj, hk]

private theorem matrixSimpleCoroot_map (σ : R ≃+* R) (i : Fin 2) (t : Rˣ) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (matrixSimpleCoroot i t) =
      matrixSimpleCoroot i (Units.map σ.toRingHom.toMonoidHom t) := by
  apply Subtype.ext
  change (Matrix.diagonal _).map σ = Matrix.diagonal _
  rw [Matrix.diagonal_map σ.map_zero]
  congr 1
  funext j
  by_cases hj : j = i.castSucc
  · simp [coordinatePairUnits, hj]
  by_cases hk : j = i.succ
  · have hs : i.succ ≠ i.castSucc := ((Fin.castSucc_lt_succ_iff).2 (le_refl i)).ne'
    simp [coordinatePairUnits, hk, hs, ← map_inv]
  · simp [coordinatePairUnits, hj, hk]

theorem unitaryCorootInterchange : UnitaryCorootInterchange.{u} := by
  intro R _ σ i t
  rw [unitaryDescentOperator, matrixSimpleCoroot_map]
  generalize Units.map σ.toRingHom.toMonoidHom t = s
  apply Subtype.ext
  change ((matrixSimpleCoroot i s)⁻¹).val.transpose.submatrix
    Fin.revPerm Fin.revPerm = _
  rw [matrixSimpleCoroot_inv]
  change (Matrix.diagonal _).transpose.submatrix Fin.revPerm Fin.revPerm =
    Matrix.diagonal _
  rw [Matrix.diagonal_transpose, Matrix.submatrix_diagonal_equiv]
  congr 1
  funext j
  fin_cases i <;> fin_cases j <;> simp [coordinatePairUnits]

open Matrix.SpecialLinearGroup in
private theorem mapTransvection {R : Type u} [CommRing R] (σ : R ≃+* R)
    {i j : Fin 3} (h : i ≠ j) (t : R) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (transvection h t) =
      transvection h (σ t) := by
  apply Subtype.ext
  change ((1 : Matrix (Fin 3) (Fin 3) R) + Matrix.single i j t).map σ =
    (1 : Matrix (Fin 3) (Fin 3) R) + Matrix.single i j (σ t)
  ext r s
  simp only [Matrix.map_apply, Matrix.add_apply, map_add]
  congr 1
  · by_cases h : r = s <;> simp [Matrix.one_apply, h]
  · by_cases h' : i = r ∧ j = s <;> simp [h']

open Matrix.SpecialLinearGroup in
theorem unitaryPinningInterchange : UnitaryPinningInterchange.{u} := by
  intro R _ σ t
  dsimp only
  constructor <;> rw [unitaryDescentOperator, mapTransvection] <;>
    apply Subtype.ext <;>
    simp only [hyperbolicInverseTranspose, transvection_inv, transvection_coe, map_neg, neg_neg]
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

end UnitaryModel

section RankOneWords

open LinearAlgebraicGroups.Arithmetic.UnitaryRankOne
open Specs.UnitaryRankOne

theorem splitWordsTransfer : SplitWordsTransfer.{u,v} := by
  intro E _ A _ H f hU hV
  have hw (t : Eˣ) : f (splitWord t) ∈ H := by
    rw [splitWord, map_mul, map_mul]
    exact H.mul_mem (H.mul_mem (hU _) (hV _)) (hU _)
  refine ⟨?_, hw 1⟩
  rintro g ⟨t, ht⟩
  have he : g = splitWord t * splitWord (-1) :=
    Subtype.ext (ht.trans (splitRankOneWords.1 t).2.symm)
  rw [he, map_mul]
  exact H.mul_mem (hw _) (hw _)

theorem unitaryWordsTransfer : UnitaryWordsTransfer.{u,v,w} := by
  intro F E _ _ _ _ _ _ A _ M H f
  dsimp only
  intro hM hsub
  let σ := quadraticConjugation F E
  let V := unitaryRadicalGenerators σ 1
  obtain ⟨hUpper, hLower, _, _⟩ := admissibleCoordinates (F := F) (E := E) (1 : Fˣ)
  simp only [Units.val_one, map_one] at hUpper hLower
  let P := (H.comap f).map M.subtype
  have hP : Subgroup.closure V ≤ P := by
    apply (Subgroup.closure_le P).mpr
    intro x hx
    have hm : x ∈ M := by
      apply (hM x).mpr
      obtain ⟨a, b, hab, h | h⟩ := hx
      · rw [h, upper]
        exact (hUpper _ _ _).mpr ⟨rfl, hab⟩
      · rw [h, lower]
        exact (hLower _ _ _).mpr ⟨rfl, hab⟩
    exact ⟨⟨x, hm⟩, hsub ⟨x, hm⟩ hx, rfl⟩
  obtain ⟨hdiag, hwords, hweyl, _⟩ :=
    unitaryTorusAndWeylWords (F := F) (E := E) (1 : Fˣ)
  refine ⟨?_, ?_⟩
  · intro g hg
    obtain ⟨d, hd⟩ := hg
    have hpres := (hM g.val).mp g.prop
    have hdet := g.val.prop
    rw [hd] at hpres hdet
    obtain ⟨s, hs⟩ := (hdiag d).mp ⟨hdet, by simpa using hpres⟩
    obtain ⟨x, hx, hxval⟩ := (hwords s).1
    have he : x = g.val := Subtype.ext (hxval.trans (hs.symm.trans hd.symm))
    obtain ⟨y, hy, hyval⟩ := hP (by simpa using hx)
    have hgy : g = y := (Subtype.ext (hyval.trans he)).symm
    rw [hgy]
    exact hy
  · obtain ⟨x, hx, hxval⟩ := hweyl
    obtain ⟨y, hy, hyval⟩ := hP (by simpa using hx)
    exact ⟨y, congrArg Subtype.val hyval |>.trans hxval, hy⟩

theorem splitWeylCorootAction : SplitWeylCorootAction.{u} := by
  intro R _ t
  have h := (splitRankOneWords.1 (1 : Rˣ)).2
  have hi : splitWord (-1 : Rˣ) = (splitWord 1)⁻¹ := by
    symm
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    change (splitWord (1 : Rˣ) * splitWord (-1)).val = (1 : Matrix (Fin 2) (Fin 2) R)
    rw [h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [← hi]
  change (splitWord (1 : Rˣ)).val * (splitWord t * splitWord (-1)).val *
    (splitWord (-1 : Rˣ)).val = _
  rw [(splitRankOneWords.1 (1 : Rˣ)).1, (splitRankOneWords.1 (-1 : Rˣ)).1,
    (splitRankOneWords.1 t).2, Matrix.diagonal_vec2, Matrix.diagonal_vec2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem unitaryWeylCorootAction : UnitaryWeylCorootAction.{u} := by
  intro E _ w hw i t
  have hsq : w * w = 1 := by
    apply Subtype.ext
    change w.val * w.val = 1
    rw [hw]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [unitaryWeyl, Matrix.mul_apply, Fin.sum_univ_three]
  have hi : w⁻¹ = w := inv_eq_of_mul_eq_one_left hsq
  rw [hi]
  apply Subtype.ext
  change w.val * (matrixSimpleCoroot i t).val * w.val = _
  rw [hw]
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [unitaryWeyl, matrixSimpleCoroot, Specs.SpecialLinearDatum.coordinatePairUnits,
      Matrix.mul_apply, Matrix.vecMul_diagonal, Fin.sum_univ_three, Fin.rev]

end RankOneWords

section OrbitField

theorem orbitFieldDegree : OrbitFieldDegree.{u,v} := by
  intro F K _ _ _ _ _ I ρ i
  letI := MulAction.compHom I ρ
  change Module.finrank F (IntermediateField.fixedField (MulAction.stabilizer Gal(K/F) i)) =
    (diagramOrbit ρ i).ncard ∧ Algebra.IsSeparable F (orbitField ρ i)
  refine ⟨?_, inferInstance⟩
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, IntermediateField.fixingSubgroup_fixedField,
    Subgroup.index_eq_card, ← Nat.card_coe_set_eq]
  exact (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer Gal(K/F) i)).symm

private theorem tensorProductOfEmbeddings {F K L J : Type u} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] [FiniteDimensional F L] [Fintype J]
    (emb : J → (L →ₐ[F] K)) (hemb : Function.Injective emb)
    (hdeg : Module.finrank F L = Fintype.card J) :
    ∃ e : K ⊗[F] L ≃ₐ[K] (J → K),
      ∀ (x : K) (y : L) (j : J), e (x ⊗ₜ[F] y) j = x * emb j y := by
  classical
  let f : K ⊗[F] L →ₐ[K] (J → K) := Algebra.TensorProduct.lift (Algebra.ofId K (J → K))
    (AlgHom.pi emb) (fun _ _ => Commute.all _ _)
  have hf (x : K) (y : L) (j : J) : f (x ⊗ₜ[F] y) j = x * emb j y := rfl
  have separate (j l : J) (hjl : j ≠ l) : ∃ z, f z j = 1 ∧ f z l = 0 := by
    obtain ⟨y, hy⟩ : ∃ y : L, emb j y ≠ emb l y := by
      by_contra! h
      exact hjl (hemb (AlgHom.ext h))
    let d := emb j y - emb l y
    refine ⟨(d⁻¹ ⊗ₜ[F] y) - ((d⁻¹ * emb l y) ⊗ₜ[F] 1), ?_, ?_⟩
    · simp only [map_sub, Pi.sub_apply, hf, map_one, mul_one, ← mul_sub]
      exact inv_mul_cancel₀ (sub_ne_zero.mpr hy)
    · simp only [map_sub, Pi.sub_apply, hf, map_one, mul_one, sub_self]
  have singleton (j : J) : ∃ z, f z = Pi.single j 1 := by
    have h (l : {l : J // j ≠ l}) := separate j l l.property
    choose z hz using h
    refine ⟨∏ l, z l, ?_⟩
    funext l
    rw [map_prod]
    change (Pi.evalRingHom (fun _ : J => K) l) (∏ q, f (z q)) =
      (Pi.single j (1 : K) : J → K) l
    rw [map_prod]
    by_cases hl : l = j
    · subst l
      simp only [Pi.single_eq_same]
      exact Finset.prod_eq_one fun q _ => (hz q).1
    · rw [Pi.single_eq_of_ne hl]
      exact Finset.prod_eq_zero (Finset.mem_univ (⟨l, Ne.symm hl⟩ : {q : J // j ≠ q}))
        (hz ⟨l, Ne.symm hl⟩).2
  choose z hz using singleton
  have hsurj : Function.Surjective f := by
    intro a
    refine ⟨∑ j, (a j ⊗ₜ[F] (1 : L)) * z j, ?_⟩
    funext l
    rw [map_sum, Fintype.sum_apply, Finset.sum_eq_single l]
    · simp [hf, hz]
    · intro j _ hj
      simp [hf, hz, Pi.single_eq_of_ne hj.symm]
    · simp
  have hdim : Module.finrank K (K ⊗[F] L) = Module.finrank K (J → K) := by
    rw [Module.finrank_baseChange, Module.finrank_pi, hdeg]
  have hinj : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
  exact ⟨AlgEquiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

theorem orbitScalarSplitting : OrbitScalarSplitting.{u} := by
  classical
  intro F K _ _ _ _ _ I ρ i
  let L := orbitField ρ i
  let J := diagramOrbit ρ i
  letI := MulAction.compHom I ρ
  let H := MulAction.stabilizer Gal(K/F) i
  let j₀ (g : Gal(K/F)) : J := ⟨ρ g i, ⟨g, rfl⟩⟩
  have hs (j : J) : ∃ g, j₀ g = j := by
    obtain ⟨g, hg⟩ := j.property
    exact ⟨g, Subtype.ext hg⟩
  letI : Finite J := Finite.of_surjective j₀ hs
  letI : Fintype J := Fintype.ofFinite J
  have hH : L.fixingSubgroup = H := IntermediateField.fixingSubgroup_fixedField H
  have hfix (g : Gal(K/F)) : (∀ y : L, g y.val = y.val) ↔ g ∈ H := by
    rw [← hH, IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun h y hy => h ⟨y, hy⟩, fun h y => h y.val y.property⟩
  have same (g h : Gal(K/F)) : (∀ y : L, g y.val = h y.val) ↔ j₀ g = j₀ h := by
    calc
      (∀ y : L, g y.val = h y.val) ↔ (∀ y : L, (h⁻¹ * g) y.val = y.val) := by
        constructor
        · intro eq y
          simp only [AlgEquiv.mul_apply, eq y]
          exact h.symm_apply_apply _
        · intro eq y
          have hh := congrArg h (eq y)
          change h (h.symm (g y.val)) = h y.val at hh
          simpa only [AlgEquiv.apply_symm_apply] using hh
      _ ↔ h⁻¹ * g ∈ H := hfix _
      _ ↔ j₀ g = j₀ h := by
        change ρ (h⁻¹ * g) i = i ↔ j₀ g = j₀ h
        rw [map_mul, map_inv, Equiv.Perm.mul_apply]
        change (ρ h).symm (ρ g i) = i ↔ j₀ g = j₀ h
        rw [(ρ h).symm_apply_eq]
        exact ⟨fun e => Subtype.ext e, fun e => congrArg Subtype.val e⟩
  let rep (j : J) := (hs j).choose
  have hrep (j : J) : j₀ (rep j) = j := (hs j).choose_spec
  let emb (j : J) : L →ₐ[F] K := (rep j).toAlgHom.comp L.val
  have hemb (g : Gal(K/F)) (y : L) : emb (j₀ g) y = g y.val :=
    (same (rep (j₀ g)) g).2 (hrep (j₀ g)) y
  have hinj : Function.Injective emb := by
    intro j l h
    rw [← hrep j, ← hrep l]
    exact (same (rep j) (rep l)).mp (fun y => DFunLike.congr_fun h y)
  have hdeg : Module.finrank F L = Fintype.card J := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact (orbitFieldDegree ρ i).1
  obtain ⟨e, he⟩ := tensorProductOfEmbeddings emb hinj hdeg
  refine ⟨emb, e, hemb, he, ?_⟩
  intro g z j
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      rw [Algebra.TensorProduct.map_tmul, he, he, map_mul]
      obtain ⟨h, rfl⟩ := hs j
      have htr : orbitTranslate ρ i g⁻¹ (j₀ h) = j₀ (g⁻¹ * h) := by
        apply Subtype.ext
        exact (congrArg (fun p : Equiv.Perm I => p i) (map_mul ρ g⁻¹ h)).symm
      rw [htr, hemb, hemb]
      change g x * h y.val = g x * g (g.symm (h y.val))
      rw [AlgEquiv.apply_symm_apply]
  | add z w hz hw => simp only [map_add, Pi.add_apply, hz, hw]

theorem orbitScalarSplittingOverAlgebras : OrbitScalarSplittingOverAlgebras.{u,v} := by
  classical
  intro F K _ _ _ _ _ I ρ i
  let L := orbitField ρ i
  let J := diagramOrbit ρ i
  letI : Finite J := Finite.of_surjective (Set.rangeFactorization (fun g => ρ g i))
    Set.rangeFactorization_surjective
  letI : Fintype J := Fintype.ofFinite J
  obtain ⟨emb, e, hemb, he, _⟩ := orbitScalarSplitting ρ i
  refine ⟨emb, hemb, fun R _ _ _ _ => ?_⟩
  let f : R ⊗[F] L ≃ₐ[R] (J → R) :=
    (Algebra.TensorProduct.cancelBaseChange F K R R L).symm.trans
      ((Algebra.TensorProduct.congr (.refl : R ≃ₐ[R] R) e).trans
        ((Algebra.TensorProduct.piRight K R R (fun _ : J => K)).trans
          (AlgEquiv.piCongrRight (fun _ => Algebra.TensorProduct.rid K R R))))
  refine ⟨f, fun x y j => ?_⟩
  dsimp only [f, AlgEquiv.trans_apply]
  rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  change Algebra.TensorProduct.rid K R R
    (Algebra.TensorProduct.piRight K R R (fun _ : J => K) (x ⊗ₜ[K] e (1 ⊗ₜ[F] y)) j) = _
  simp only [Algebra.TensorProduct.piRight_tmul, he, one_mul]
  simp [Algebra.smul_def, mul_comm]

end OrbitField

section LatticeDecomposition

theorem basisPartitionProduct : BasisPartitionProduct.{u,v,w} := by
  classical
  intro I J _ Y _ b p
  dsimp only
  let L := fun j : J => Submodule.span ℤ (b '' {i | p i = j})
  let f : (∀ j, L j) →ₗ[ℤ] Y :=
    { toFun := fun x => ∑ j, (x j).val
      map_add' := fun x y => by
        change (∑ j, ((x j).val + (y j).val)) = _
        rw [Finset.sum_add_distrib]
      map_smul' := fun r x => by
        change (∑ j, r • (x j).val) = r • (∑ j, (x j).val)
        rw [Finset.smul_sum] }
  have outside (j : J) (x : L j) (i : I) (hi : p i ≠ j) : b.repr x.val i = 0 := by
    have h := (b.mem_span_image).mp x.prop
    by_contra hn
    exact hi (h (Finsupp.mem_support_iff.mpr hn))
  have component (x : ∀ j, L j) (i : I) :
      b.repr (f x) i = b.repr (x (p i)).val i := by
    change b.repr (∑ j, (x j).val) i = _
    rw [map_sum, Finsupp.finsetSum_apply]
    exact Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) (fun j _ h => outside j (x j) i h.symm)
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      funext j
      apply Subtype.ext
      apply b.repr.injective
      ext i
      by_cases hi : p i = j
      · subst j
        rw [← component, ← component, h]
      · rw [outside _ _ _ hi, outside _ _ _ hi]
    · intro y
      let z : ∀ j, L j := fun j => ⟨b.repr.symm ((b.repr y).filter (fun i => p i = j)), by
        apply (b.mem_span_image).mpr
        rw [LinearEquiv.apply_symm_apply]
        intro i hi
        by_contra hn
        exact (Finsupp.mem_support_iff.mp hi) (Finsupp.filter_apply_neg _ _ hn)⟩
      refine ⟨z, b.repr.injective ?_⟩
      ext i
      rw [component]
      change b.repr (b.repr.symm ((b.repr y).filter (fun j => p j = p i))) i = _
      rw [LinearEquiv.apply_symm_apply]
      exact Finsupp.filter_apply_pos (fun j => p j = p i) _ (show p i = p i from rfl)
  exact ⟨LinearEquiv.ofBijective f hf, fun _ => rfl⟩

end LatticeDecomposition

section InvariantFace

open Specs.Pinning (SplitBorelPair AttachedDatum)
open Specs.AbstractPairing (Root)
open Specs.CharacterDescent (Cocharacter)
open Specs.CharacterPairing (pairing)
open LinearAlgebraicGroups.Flag.StandardParabolicLevi (exists_face_cocharacter)

set_option backward.isDefEq.respectTransparency false in
private theorem pairing_action {k : Type u} [Field k] {P : SplitBorelPair k} (D : AttachedDatum P)
    (a : Aut D.toBased) (i : Root P.T) (y : D.toBased.Y) :
    letI := D.comm
    pairing P.T.group ((a.asIso.hom.val.indexEquiv i).val) (cocharacterAction D a y).toMul =
      pairing P.T.group i.val y.toMul := by
  letI := D.comm
  rw [← D.datum.pairing_eq, ← D.datum.pairing_eq, ← D.datum.root_eq, ← D.datum.root_eq]
  let e := a.asIso.hom.val
  change D.toBased.datum.toLinearMap
    (D.toBased.datum.root (e.indexEquiv i)) (e.coweightEquiv.symm y) =
    D.toBased.datum.toLinearMap (D.toBased.datum.root i) y
  rw [← e.toHom.root_weightMap_apply]
  exact (e.toLinearMap_weightEquiv _ _).trans (congrArg _ (e.coweightEquiv.apply_symm_apply y))

set_option backward.isDefEq.respectTransparency false in
theorem invariantFaceCocharacter : InvariantFaceCocharacter.{u,v} := by
  classical
  intro k _ P D Γ _ _ ω I
  letI := D.comm
  intro hI hstable
  letI : Fintype Γ := Fintype.ofFinite Γ
  obtain ⟨c, hc⟩ := exists_face_cocharacter (D := D.datum) D.base I hI
  let ρ := (cocharacterAction D).comp ω
  let c₀ : D.toBased.Y := Additive.ofMul c
  let y : D.toBased.Y := ∑ g : Γ, ρ g c₀
  have hfix (g : Γ) : ρ g y = y := by
    dsimp only [y]
    rw [map_sum]
    have h (h : Γ) : ρ g (ρ h c₀) = ρ (g * h) c₀ := by rw [map_mul]; rfl
    simp only [h]
    exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)
  have pair_sum (i : Root P.T) : pairing P.T.group i.val y.toMul =
      ∑ g : Γ, pairing P.T.group i.val (ρ g c₀).toMul := by
    rw [← D.datum.pairing_eq, ← D.datum.root_eq]
    change D.datum.rootDatum.toLinearMap (D.datum.rootDatum.root i) y = _
    rw [show y = ∑ g : Γ, ρ g c₀ from rfl, map_sum]
    apply Finset.sum_congr rfl
    intro g _
    exact (congrArg (fun x => D.datum.rootDatum.toLinearMap x (ρ g c₀)) (D.datum.root_eq i)).trans
      (D.datum.pairing_eq i.val (ρ g c₀).toMul)
  have term (g : Γ) (i : Root P.T) :
      pairing P.T.group i.val (ρ g c₀).toMul =
        pairing P.T.group ((ω g).asIso.hom.val.indexEquiv.symm i).val c := by
    have h := pairing_action D (ω g) ((ω g).asIso.hom.val.indexEquiv.symm i) c₀
    rw [Equiv.apply_symm_apply] at h
    exact h
  refine ⟨y.toMul, ⟨?_, ?_⟩, hfix⟩
  · intro i hi
    rw [pair_sum]
    apply Finset.sum_eq_zero
    intro g _
    rw [term]
    apply hc.1
    exact (hstable g _).mp (by simpa only [Equiv.apply_symm_apply] using hi)
  · intro i hi
    rw [pair_sum]
    apply Finset.sum_pos
    · intro g _
      rw [term]
      apply hc.2
      let e := (ω g).asIso.hom.val.indexEquiv
      have hs : e '' (D.toBased.base.support : Set _) = D.toBased.base.support :=
        (ω g).asIso.hom.property
      have hm : (i : D.toBased.I) ∈ e '' (D.toBased.base.support : Set _) :=
        Eq.mpr (congrArg (fun S : Set D.toBased.I => i ∈ S) hs) hi.1
      obtain ⟨j, hj, he⟩ := hm
      have hji : j = e.symm i := (e.eq_symm_apply).mpr he
      refine ⟨?_, ?_⟩
      · exact hji ▸ hj
      · intro hin
        exact hi.2 (by simpa only [Equiv.apply_symm_apply] using (hstable g _).mpr hin)
    · exact Finset.univ_nonempty

theorem orbitRootStability : OrbitRootStability.{u,v} := by
  intro k _ P D Γ _ ω i
  letI := D.comm
  let ρ := (simplePermutation D).comp ω
  have perm (g : Γ) (j : D.toBased.base.support) :
      (ρ g j).val = (ω g).asIso.hom.val.indexEquiv j.val := rfl
  have orbit (g : Γ) : (ρ g i).val ∈ orbitRootSet D ω i := ⟨ρ g i, ⟨g, rfl⟩, rfl⟩
  constructor
  · rintro _ ⟨j, _, rfl⟩
    exact j.property
  · intro g α
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, ht⟩
      have h : (ρ (g⁻¹ * t) i).val = α := by
        apply (ω g).asIso.hom.val.indexEquiv.injective
        rw [← perm, ← Equiv.Perm.mul_apply, ← map_mul, ← mul_assoc, mul_inv_cancel, one_mul]
        exact ht
      exact h ▸ orbit (g⁻¹ * t)
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      have h : (ω g).asIso.hom.val.indexEquiv (ρ t i).val = (ρ (g * t) i).val :=
        (perm g (ρ t i)).symm.trans
          (congrArg (fun p : Equiv.Perm D.toBased.base.support => (p i).val) (map_mul ρ g t).symm)
      exact (congrArg (fun r : Root P.T => r ∈ orbitRootSet D ω i) h).mpr (orbit (g * t))

theorem attachedCorootPermutation : AttachedCorootPermutation.{u} := by
  intro k _ P D a i
  letI := D.comm
  let e := a.asIso.hom.val
  change e.coweightEquiv.symm (D.toBased.datum.coroot i.val) =
    D.toBased.datum.coroot (e.indexEquiv i.val)
  apply e.coweightEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  have h := e.toHom.coroot_coweightMap_apply _ _ (e.indexEquiv i.val)
  rw [Equiv.symm_apply_apply] at h
  exact h.symm

end InvariantFace

section RationalFace

open CategoryTheory.Limits
open Specs.CharacterDescent (Cocharacter)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private cocharacter_ext_units from LinearAlgebraicGroups.RootData.RankOneFlag
open private multiplicativeBaseChange multiplicativeBaseChange_unit twistedBaseChange twistMorphism
  twistCocharacter descendInvariantCocharacter from LinearAlgebraicGroups.Relative.RationalCocharacter

private theorem preservesUnits_unique {F K : Type u} [Field F] [Field K] [Algebra F K]
    (e : MultiplicativeComparison F K) (he : PreservesUnits e) :
    e = multiplicativeBaseChange F K := by
  apply Iso.ext
  apply cocharacter_ext_units
  intro R t
  apply (baseChangePoints F K _ R).1
  exact (he R t).trans (multiplicativeBaseChange_unit K R t).symm

set_option backward.isDefEq.respectTransparency false in
/-- Averaging on the integral lattice gives a rational cocharacter cutting
out the specified face in the actual scalar-extended torus. -/
theorem rationalFaceCocharacter : RationalFaceCocharacter.{u} := by
  intro F K _ _ _ _ _ G T B S D e ω he hω I
  letI := D.comm
  intro hI hstable
  have heq := preservesUnits_unique e he
  subst e
  obtain ⟨c, hc, hfix⟩ := invariantFaceCocharacter S.pair D ω I hI hstable
  let T₀ := closedSubgroupAlgebraicGroup T
  let a := multiplicativeBaseChange F K
  let M := specGroup (groupAlgebra F IntegerCharacters)
  let f := a.inv ≫ c
  have hinv (σ : Gal(K/F)) : twistCocharacter σ c = c := by
    have h := hω σ⁻¹ (Additive.ofMul c)
    rw [hfix σ⁻¹, inv_inv] at h
    change fieldConjugation σ M ≫ f.hom.hom.left =
      f.hom.hom.left ≫ fieldConjugation σ T.group at h
    have htwist : twistMorphism σ f = f := by
      apply Grp.hom_ext
      apply Over.OverMorphism.ext
      let x := twistedBaseChange σ M
      change x.inv.hom.hom.left ≫ f.hom.hom.left ≫ fieldConjugation σ T.group = _
      rw [← h, ← Category.assoc]
      have hid := congrArg (fun p => p.hom.hom.left) x.inv_hom_id
      change x.inv.hom.hom.left ≫ fieldConjugation σ M = 𝟙 _ at hid
      rw [hid, Category.id_comp]
    change a.hom ≫ twistMorphism σ f = c
    rw [htwist]
    exact a.hom_inv_id_assoc c
  obtain ⟨d, hd⟩ := descendInvariantCocharacter T₀ c hinv
  refine ⟨d, ?_⟩
  change a.hom ≫ (groupBaseChange F K).map d = c at hd
  change Specs.StandardParabolicLevi.HasFace D.base I (a.hom ≫ (groupBaseChange F K).map d)
  rw [hd]
  exact hc

end RationalFace

section SplitLevi

open Specs.Pinning (IsSimple)
open Specs.BorelsAndChambers (positiveRoots subgroupRoots)
open Specs.CharacterDescent (Cocharacter)
open Specs.CharacterPairing (pairing)
open Specs.SimpleRoots (evaluate)
open Specs.StandardParabolicLevi (HasFace leviRoots parabolicWeylGroup)
open LinearAlgebraicGroups.Flag.StandardParabolicLevi (exists_face_cocharacter face_weyl_group)

open private common_kernel_for_face face_parabolic face_common_kernel_centralizer face_levi_roots
  from LinearAlgebraicGroups.Flag.StandardParabolicLevi
open private connected_of_geometricallyConnected torus_subgroupOf_centralizer
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private restrictSubgroup from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private maximal_torus_in_intermediate_group from LinearAlgebraicGroups.RootData.RankOneFlag

private theorem regularForAttachedBase {k : Type u} [Field k]
    (P : Specs.Pinning.SplitBorelPair k) (D : Specs.Pinning.AttachedDatum P) :
    letI := D.comm
    ∃ c : Cocharacter P.T.group, Specs.BorelsAndChambers.IsRegular P.T c ∧
      positiveRoots P.T c = subgroupRoots P.T P.B ∧
      Specs.SimpleRoots.IsBaseFor D.datum.rootDatum (evaluate D.datum c) D.base := by
  classical
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.freeCharacters
  letI := D.datum.finiteCharacters
  letI := D.datum.reduced
  obtain ⟨c, _, hreg, _, hc⟩ :=
    (RootData.BorelsAndChambers.borelsThroughT P.G P.reductive P.T P.split P.maximal).1
      P.B P.borel P.containsTorus
  let f := evaluate D.datum c
  have hf (i : Specs.AbstractPairing.Root P.T) :
      f (D.datum.rootDatum.root i) = pairing P.T.group i.val c := by
    change D.datum.rootDatum.toLinearMap
      (D.datum.rootDatum.root i) (Additive.ofMul c) = _
    rw [D.datum.root_eq, D.datum.pairing_eq]
  have hpos : Specs.SimpleRoots.positive D.datum.rootDatum f = subgroupRoots P.T P.B := by
    rw [hc]
    ext i
    change 0 < f (D.datum.rootDatum.root i) ↔ 0 < pairing P.T.group i.val c
    rw [hf]
  obtain ⟨b, hb⟩ := RootData.SimpleRoots.baseFor D.datum.rootDatum f (fun i => hf i ▸ hreg i)
  have hs : b.support = D.base.support := by
    ext i
    rw [hb.simple_iff, D.simple_iff, hpos]
    unfold IsSimple
    simp only [D.datum.root_eq]
    rfl
  have support_injective : Function.Injective
      (RootPairing.Base.support (P := D.datum.rootDatum)) := by
    intro b₁ b₂ hn
    cases b₁
    cases b₂
    cases hn
    rfl
  have he : b = D.base := support_injective hs
  exact ⟨c, hreg, hc.symm, he ▸ hb⟩

private theorem splitLeviForFace {k : Type u} [Field k] (P : Specs.Pinning.SplitBorelPair k)
    (D : Specs.Pinning.AttachedDatum P) (I : Set (Specs.AbstractPairing.Root P.T))
    (lam : Cocharacter P.T.group) (L : CocharacterDynamics.LimitDecomposition (lam ≫ P.T.inclusion))
    (hlam : letI := D.comm; HasFace D.base I lam) : IsSplitStandardLevi D I L := by
  letI := D.comm
  obtain ⟨c, _, hc, hb⟩ := regularForAttachedBase P D
  obtain ⟨S, hS, d, hd⟩ := common_kernel_for_face P.split hlam
  letI := P.reductive.1
  letI := connected_of_geometricallyConnected P.reductive.2.1
  obtain ⟨hpar, hB⟩ := face_parabolic P.reductive P.split P.maximal P.borel
    P.containsTorus hc hb hlam L
  obtain ⟨hcentral, hred⟩ := face_common_kernel_centralizer P.reductive P.split P.maximal hc hb hlam S hS d hd L
  obtain ⟨j, hj⟩ := torus_subgroupOf_centralizer P.split lam L
  let Tₗ := restrictSubgroup P.T L.centralizer j hj
  let e : P.T.group ≅ Tₗ.group := Iso.refl _
  have hi : e.hom ≫ Tₗ.inclusion ≫ L.centralizer.inclusion = P.T.inclusion :=
    (Category.id_comp _).trans hj
  exact ⟨Tₗ, e, S, hS, hcentral, hpar, hB, hred, hi,
    maximal_torus_in_intermediate_group hj P.maximal, P.split,
    face_levi_roots P.split hc hb hlam L Tₗ e hi⟩

theorem splitStandardLevi : SplitStandardLevi.{u} := by
  intro k _ P D
  letI := D.comm
  intro I hI
  obtain ⟨c, hc⟩ := exists_face_cocharacter (D := D.datum) D.base I hI
  letI := P.reductive.1
  letI := connected_of_geometricallyConnected P.reductive.2.1
  obtain ⟨L, _⟩ := CocharacterDynamics.cocharacterDynamics P.G (c ≫ P.T.inclusion)
  exact ⟨c, L, hc, splitLeviForFace P D I c L hc⟩

private theorem coweight_difference_mem_span {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (Q : RootDatum J X Y) (I : Set J) (w : Q.weylGroup)
    (hw : w ∈ Subgroup.closure (RootPairing.weylGroup.ofIdx Q '' I)) :
    ∀ y : Y, w.val.coweightEquiv y - y ∈ Submodule.span ℤ (Q.coroot '' I) := by
  let L := Submodule.span ℤ (Q.coroot '' I)
  refine Subgroup.closure_induction
    (p := fun v _ => ∀ y : Y, v.val.coweightEquiv y - y ∈ L) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨i, hi, rfl⟩ y
    change (RootPairing.Equiv.reflection Q i).coweightEquiv y - y ∈ L
    rw [RootPairing.Equiv.reflection_coweightEquiv, RootPairing.coreflection_apply]
    have h := L.neg_mem (L.smul_mem (Q.root' i y) (Submodule.subset_span ⟨i, hi, rfl⟩))
    convert h using 1
    abel
  · intro y
    change y - y ∈ L
    simp
  · intro x z _ _ hx hz y
    change z.val.coweightEquiv (x.val.coweightEquiv y) - y ∈ L
    convert L.add_mem (hz (x.val.coweightEquiv y)) (hx y) using 1
    abel
  · intro x _ hx y
    change x.val.coweightEquiv.symm y - y ∈ L
    have h := hx (x.val.coweightEquiv.symm y)
    rw [LinearEquiv.apply_symm_apply] at h
    simpa only [neg_sub] using L.neg_mem h

set_option backward.isDefEq.respectTransparency false in
theorem faceCorootSpan : FaceCorootSpan.{u} := by
  classical
  intro k _ P D hG hsc
  letI := D.comm
  intro I hI
  let Q := D.datum.rootDatum
  let L := Submodule.span ℤ (Q.coroot '' I)
  obtain ⟨b, hb⟩ := attachedCorootBasis P D hG hsc
  let J : Set D.base.support := {i | i.val ∈ I}
  have he : b '' J = Q.coroot '' I := by
    ext y
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i.val, hi, (hb i).symm⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hI hi⟩, hi, hb _⟩
  have saturated (y : D.toBased.Y) (n : ℕ) (hn : n ≠ 0) (hy : n • y ∈ L) : y ∈ L := by
    change n • y ∈ Submodule.span ℤ (Q.coroot '' I) at hy
    change y ∈ Submodule.span ℤ (Q.coroot '' I)
    rw [← he, b.mem_span_image] at hy ⊢
    intro i hi
    apply hy
    apply Finsupp.mem_support_iff.mpr
    have hval : b.repr (n • y) i = (n : ℤ) * b.repr y i := by
      rw [map_nsmul]
      rfl
    rw [hval]
    exact mul_ne_zero (by exact_mod_cast hn) (Finsupp.mem_support_iff.mp hi)
  refine ⟨le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_mono ?_), saturated⟩
  · rintro _ ⟨α, hα, rfl⟩
    obtain ⟨lam, hlam⟩ := exists_face_cocharacter (D := D.datum) D.base I hI
    obtain ⟨c, hreg, _, hc⟩ := regularForAttachedBase P D
    let f := evaluate D.datum lam
    have hz : f (Q.root α) = 0 := by
      apply LinearMap.mem_ker.mp
      exact (Submodule.span_le.mpr (by
        rintro _ ⟨i, hi, rfl⟩
        apply LinearMap.mem_ker.mpr
        change D.datum.rootDatum.toLinearMap (D.datum.rootDatum.root i) (Additive.ofMul lam) = 0
        rw [D.datum.root_eq, D.datum.pairing_eq]
        exact hlam.1 i hi)) hα
    have hw : RootPairing.weylGroup.ofIdx Q α ∈ parabolicWeylGroup D.datum I := by
      apply (face_weyl_group hreg hc hlam _).mp
      ext x
      change f (Q.reflection α x) = f x
      rw [RootPairing.reflection_apply, map_sub, map_zsmul, hz, smul_zero, sub_zero]
    have hd := coweight_difference_mem_span Q I _ hw (Q.coroot α)
    change (RootPairing.Equiv.reflection Q α).coweightEquiv (Q.coroot α) - Q.coroot α ∈ L at hd
    rw [RootPairing.Equiv.reflection_coweightEquiv, RootPairing.coreflection_apply_self] at hd
    exact saturated (Q.coroot α) 2 (by decide) (by
      simpa only [neg_sub, sub_neg_eq_add, two_nsmul] using L.neg_mem hd)
  · rintro _ ⟨α, hα, rfl⟩
    exact ⟨α, Submodule.subset_span ⟨α, hα, rfl⟩, rfl⟩

end SplitLevi

section DerivedCoroots

open CategoryTheory.Limits
open Specs.AbstractPairing (Root)
open Specs.CharacterDescent (Cocharacter)
open Specs.Pinning (SplitBorelPair AttachedDatum)
open Specs.RootGroups (rootPoint rankOneWord)
open Specs.SchemeDerivedGroup (IsCommutative)
open Specs.StandardParabolicLevi (leviRoots)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition unitPoint cocharacterPoint)
open private cocharacter_ext_units from LinearAlgebraicGroups.RootData.RankOneFlag
open private contractingKilled postMul postInv from LinearAlgebraicGroups.Reductive.CentralDerived
open private attachedCoroot_pushforward from LinearAlgebraicGroups.Classification.CentralIsogenies

set_option backward.isDefEq.respectTransparency false in
private theorem rootPoint_comp_of_zero {k : Type u} [Field k] {A : Specs.RootGroups.AdditiveLine k}
    {G Q : Specs.GroupScheme k} {x : A.group ⟶ G} {q : G ⟶ Q} (h : x ≫ q = 0)
    (R : TestAlgebra k) (b : R) : rootPoint x R b ≫ q.hom.hom = 1 := by
  unfold rootPoint
  rw [Category.assoc, ← Grp.comp_hom_hom, h]
  exact MonObj.comp_one _

set_option backward.isDefEq.respectTransparency false in
theorem attachedCorootToCommutative : AttachedCorootToCommutative.{u} := by
  intro k _ G Q T α c h q hq
  obtain ⟨C, _, _, _, D, E, _, _, _, _, A, p, n, _, _, _, _, r, rfl⟩ := h
  let C₀ := closedSubgroupAlgebraicGroup C.subgroup
  have hp := contractingKilled (G := C₀) (Q := Q) (C.subgroup.inclusion ≫ q) hq D
  have hn := contractingKilled (G := C₀) (Q := Q) (C.subgroup.inclusion ≫ q) hq E
  let xp := p.root.hom ≫ D.contracting.inclusion ≫ C.subgroup.inclusion
  let xn := n.root.hom ≫ E.contracting.inclusion ≫ C.subgroup.inclusion
  have hxp : xp ≫ q = 0 := by
    dsimp only [xp]
    rw [Category.assoc, Category.assoc, hp, comp_zero]
  have hxn : xn ≫ q = 0 := by
    dsimp only [xn]
    rw [Category.assoc, Category.assoc, hn, comp_zero]
  apply cocharacter_ext_units
  intro R t
  have hw (s : Rˣ) : rankOneWord xp xn R s ≫ q.hom.hom = 1 := by
    let f := IsMonHom.monoidHom q.hom.hom ((testSpec k).obj (Opposite.op R))
    change f (rootPoint xp R (↑s : R) * rootPoint xn R (-(↑s⁻¹ : R)) * rootPoint xp R (↑s : R)) = 1
    rw [map_mul, map_mul]
    change ((rootPoint xp R (↑s : R) ≫ q.hom.hom) *
      (rootPoint xn R (-(↑s⁻¹ : R)) ≫ q.hom.hom)) * (rootPoint xp R (↑s : R) ≫ q.hom.hom) = 1
    rw [rootPoint_comp_of_zero hxp, rootPoint_comp_of_zero hxn, mul_one, mul_one]
  change (cocharacterPoint r.coroot R t ≫ T.inclusion.hom.hom) ≫ q.hom.hom =
    unitPoint R t ≫ (1 : _ ⟶ Q.val.X)
  rw [r.coroot_word R t, postMul, postInv, hw, hw, inv_one, mul_one, MonObj.comp_one]

private theorem corootUnderTorusIso {k : Type u} [Field k] (G H : AffineAlgebraicGroup k)
    (hH : Specs.GeometricRadicals.IsReductive H) (T : ClosedSubgroup G.val) (U : ClosedSubgroup H.val)
    (hU : Specs.GeometricRadicals.IsSplitTorus U.group) (hmax : Specs.RankOneFlag.IsGeometricallyMaximal U)
    (f : G.val ⟶ H.val) (e : T.group ≅ U.group) (he : e.hom ≫ U.inclusion = T.inclusion ≫ f)
    (α : Root U) (hβ : e.hom ≫ α.val ∈ Specs.CharacterPairing.absoluteRoots T)
    (c : Cocharacter T.group) (d : Cocharacter U.group)
    (hc : Specs.AbstractPairing.IsAttachedCoroot T ⟨_, hβ⟩ c)
    (hd : Specs.AbstractPairing.IsAttachedCoroot U α d) : c ≫ e.hom = d := by
  haveI : IsIso e.hom.hom.hom.left :=
    (Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))).map_isIso e.hom
  have hRest : Specs.CentralIsogenies.IsTorusRestriction f e.hom :=
    ⟨he, inferInstance, inferInstance⟩
  exact attachedCoroot_pushforward G H hH T U hU hmax f e.hom hRest α.val α.property hβ c d hc hd

set_option backward.isDefEq.respectTransparency false in
private theorem subsystemCorootToCommutative {k : Type u} [Field k] {P : SplitBorelPair k}
    (D : AttachedDatum P) (I : Set (Root P.T)) (c : Cocharacter P.T.group)
    (L : LimitDecomposition (c ≫ P.T.inclusion)) (hL : IsSplitStandardLevi D I L)
    (Q : AffineAlgebraicGroup k) (q : L.centralizer.group ⟶ Q.val) (hq : IsCommutative Q.val)
    (α : Root P.T) (hα : letI := D.comm; α ∈ leviRoots D.datum I) :
    letI := D.comm
    ∃ d : Cocharacter L.centralizer.group,
      d ≫ L.centralizer.inclusion = (D.datum.rootDatum.coroot α).toMul ≫ P.T.inclusion ∧
      d ≫ q = 0 := by
  letI := D.comm
  obtain ⟨Tₗ, e, _, _, _, _, _, hred, hi, hmax, hs, hroot⟩ := hL
  let Gₗ := closedSubgroupAlgebraicGroup L.centralizer
  obtain ⟨hComm, ⟨A⟩⟩ := RootData.AbstractPairing.abstractPairing Gₗ hred Tₗ hs hmax
  letI := hComm
  have hβ : e.inv ≫ α.val ∈ Specs.CharacterPairing.absoluteRoots Tₗ := by
    rw [hroot]
    exact ⟨α, hα, rfl⟩
  let β : Root (G := Gₗ) Tₗ := ⟨_, hβ⟩
  let d : Cocharacter Tₗ.group := (A.rootDatum.coroot β).toMul
  have hinc : e.inv ≫ P.T.inclusion = Tₗ.inclusion ≫ L.centralizer.inclusion :=
    (congrArg (e.inv ≫ ·) hi.symm).trans (e.inv_hom_id_assoc _)
  have hd : d ≫ e.inv = (D.datum.rootDatum.coroot α).toMul :=
    corootUnderTorusIso Gₗ P.G P.reductive Tₗ P.T P.split P.maximal
      L.centralizer.inclusion e.symm hinc α hβ d _ (A.attached β) (D.datum.attached α)
  refine ⟨d ≫ Tₗ.inclusion, ?_, ?_⟩
  · rw [Category.assoc, ← hinc, ← Category.assoc, hd]
  · exact (Category.assoc _ _ _).trans
      (attachedCorootToCommutative Gₗ Q Tₗ β d (A.attached β) q hq)

end DerivedCoroots

section RationalLevi

open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private cocharacterCentralizerReductive from LinearAlgebraicGroups.Relative.RationalCocharacter

theorem derivedLeviFromRationalCocharacter : DerivedLeviFromRationalCocharacter.{u} := by
  intro F _ G T hG hT hmax c
  obtain ⟨D⟩ := CocharacterDynamics.existsLimitDecomposition G (c ≫ T.inclusion)
  have hred := cocharacterCentralizerReductive G hG T hT hmax c D
  let L := closedSubgroupAlgebraicGroup D.centralizer
  obtain ⟨H, hH⟩ := SchemeDerivedGroup.derivedSubgroupExists L
  exact ⟨D, H, hred, hH, Reductive.CentralDerived.derivedSemisimple L hred H hH⟩

open private extendSubgroup limits_subgroups_extend subgroupOf_of_extend subgroupIso_of_same same_subgroup_symm
  from LinearAlgebraicGroups.RootData.RankOneFlag
open private subgroupOf_trans from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private limitIsParabolic from LinearAlgebraicGroups.Relative.MaximalSplitTori
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private factor_group_through_subgroup from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private torus_commutative from LinearAlgebraicGroups.Reductive.TorusFreeUnipotent

private theorem castLimitSubgroups {F : Type u} [Field F] {G : Specs.GroupScheme F}
    {c d : Specs.CharacterDescent.Cocharacter G} (h : c = d)
    (L : CocharacterDynamics.LimitDecomposition c) :
    (h ▸ L : CocharacterDynamics.LimitDecomposition d).parabolic = L.parabolic ∧
    (h ▸ L : CocharacterDynamics.LimitDecomposition d).centralizer = L.centralizer := by
  subst d
  exact ⟨rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
theorem rationalFaceDerivedLevi : RationalFaceDerivedLevi.{u} := by
  intro F K _ _ _ _ _ G T B S D e ω hG hT hmax he hω I
  letI := D.comm
  intro hI hstable
  obtain ⟨c, hc⟩ := rationalFaceCocharacter G T B S D e ω he hω I hI hstable
  obtain ⟨L, H, hL, hH, hHss⟩ := derivedLeviFromRationalCocharacter G T hG hT hmax c
  let E := groupBaseChange F K
  let cK := e.hom ≫ E.map c
  let cG := c ≫ T.inclusion
  obtain ⟨Lk⟩ := CocharacterDynamics.existsLimitDecomposition S.pair.G (cK ≫ S.pair.T.inclusion)
  have hLevi := splitLeviForFace S.pair D I cK Lk hc
  have hcomp : cK ≫ S.pair.T.inclusion = e.hom ≫ E.map cG := by
    change (e.hom ≫ E.map c) ≫ E.map T.inclusion = e.hom ≫ E.map (c ≫ T.inclusion)
    rw [E.map_comp, Category.assoc]
  have hbase : Specs.RankOneFlag.SameSubgroup Lk.parabolic
      (extendSubgroup K L.parabolic) ∧
      Specs.RankOneFlag.SameSubgroup Lk.centralizer
        (extendSubgroup K L.centralizer) := by
    obtain ⟨hp, _, hz⟩ := limits_subgroups_extend G L e he (hcomp ▸ Lk)
    obtain ⟨ep, ez⟩ := castLimitSubgroups hcomp Lk
    exact ⟨ep ▸ hp, ez ▸ hz⟩
  have hB : Specs.SchemeDerivedGroup.IsSubgroupOf B L.parabolic := by
    obtain ⟨_, _, _, _, _, _, hb, _⟩ := hLevi
    exact subgroupOf_of_extend (subgroupOf_trans hb hbase.1.1)
  obtain ⟨j, hj⟩ := subgroupIso_of_same (same_subgroup_symm hbase.2)
  change j.hom ≫ Lk.centralizer.inclusion = E.map L.centralizer.inclusion at hj
  obtain ⟨hClosed, hDerived, _⟩ := Reductive.DerivedSubgroup.derivedSubgroupBaseChange K
    (closedSubgroupAlgebraicGroup L.centralizer) H hH hL.1 hL.2.1
  refine ⟨c, hc, L, H, Lk, limitIsParabolic G hG cG L, hB, hL, hH, hHss,
    hLevi, j, hj, hClosed, hDerived, ?_⟩
  let Gₗ := closedSubgroupAlgebraicGroup L.centralizer
  let Gₖ := Specs.Unipotent.baseChangedAlgebraicGroup K Gₗ
  have hRed := (Reductive.RadicalBaseChange.reductiveFieldExtension (K := K) Gₗ hL.1 hL.2.1).mpr hL
  let Hₖ := Specs.GeometricRadicals.baseChangedSubgroup K H hClosed
  obtain ⟨Q, q, hker, _, hQ⟩ := Reductive.CentralDerived.derivedTorusQuotient Gₖ hRed Hₖ hDerived
  letI := torus_commutative Q hQ
  intro α hα
  obtain ⟨d, hd, hq⟩ := subsystemCorootToCommutative D I cK Lk hLevi Q (j.inv ≫ q)
    (fun _ _ _ => mul_comm _ _) α hα
  let dₖ := d ≫ j.inv
  have hdₖ : dₖ ≫ q = 0 := (Category.assoc _ _ _).trans hq
  obtain ⟨s, hs⟩ := (schemeKernel_sections hker dₖ.hom.hom).mpr
    (congrArg (fun f => f.hom.hom) hdₖ)
  obtain ⟨a, ha⟩ := factor_group_through_subgroup Hₖ dₖ s hs
  refine ⟨a, ?_⟩
  change a ≫ E.map (H.inclusion ≫ L.centralizer.inclusion) = _
  rw [E.map_comp, ← Category.assoc, show a ≫ E.map H.inclusion = dₖ from ha]
  rw [← hj, Category.assoc, j.inv_hom_id_assoc]
  exact hd

end RationalLevi

section CorootSaturation

open CategoryTheory.Limits
open Specs.CharacterDescent (Cocharacter)
open Specs.DiagonalizableGroups (diagonalGroup groupAlgebra IntegerCharacters)
open Specs.SimplyConnectedLattice (corootLattice)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private cocharacterSum cocharacterSum_finiteQuotient
  from LinearAlgebraicGroups.Classification.IntegralRealization
open private cocharacterImageIsTorus from LinearAlgebraicGroups.Relative.RationalCocharacter
open private torus_of_iso from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private groupPresentation schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private trivialOfFiniteSmoothConnected postMul from LinearAlgebraicGroups.Reductive.CentralDerived
open private torus_smooth cancel_groupHom_of_flat_of_surjective
  from LinearAlgebraicGroups.Reductive.CentralFrobeniusDescent
open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies
open private centralizes_iff mono_over from LinearAlgebraicGroups.Affine.Stabilizers
open private factor_group_through_subgroup from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private pairing_eq_iff isTorus_of_split from LinearAlgebraicGroups.RootData.CharacterPairing
open private powerMorphism_zero from LinearAlgebraicGroups.Flag.StandardParabolicLevi
open private torus_commutative from LinearAlgebraicGroups.Reductive.TorusFreeUnipotent

set_option backward.isDefEq.respectTransparency false in
private theorem cocharacter_to_finite_group {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (h : IsFinite G.val.X.hom) (c : Cocharacter G.val) : c = 0 := by
  obtain ⟨S, p, ht, hp, _, _⟩ := cocharacterImageIsTorus G c
  let A := closedSubgroupAlgebraicGroup S
  obtain ⟨B, _, ⟨e⟩⟩ := groupPresentation A
  have hc := ((SmoothnessAndIsogenies.smoothConnectedMultiplicativeType B).mp
    ((CharacterDescent.torusOnSchemes B).mpr (torus_of_iso e.symm ht))).2.2
  let U := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  have hconn : ConnectedSpace A.val.X.left :=
    (U.mapIso e).hom.homeomorph.connectedSpace_iff.mp hc
  have hf : IsFinite A.val.X.hom := by
    letI := h
    letI := S.isClosedImmersion
    change IsFinite S.group.X.hom
    rw [← S.inclusion.hom.hom.w]
    infer_instance
  obtain ⟨z⟩ := trivialOfFiniteSmoothConnected A (torus_smooth A ht) hconn hf
  have hzero : IsZero S.group := (Grp.isZero_trivial _).of_iso z
  rw [← hp, hzero.eq_zero_of_src S.inclusion, comp_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem cocharacter_in_central_derived_is_trivial {k : Type u} [Field k]
    {G : AffineAlgebraicGroup k} (H : ClosedSubgroup G.val)
    (hH : Specs.GeometricRadicals.IsSemisimple (closedSubgroupAlgebraicGroup H))
    (c : Cocharacter H.group) (hc : Centralizes (𝟙 G.val) (c ≫ H.inclusion).hom.hom) :
    c = 0 := by
  let A := closedSubgroupAlgebraicGroup H
  have hr := reductive_of_semisimple A hH
  obtain ⟨Z, hZ, _⟩ := Reductive.CentralDerived.centralTorusExists A hr
  have hz := (Reductive.CentralDerived.semisimpleIffFiniteCentre A hr Z hZ).mp hH
  have hh : Centralizes (𝟙 H.group) c.hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro X f x
    letI := mono_over H.inclusion.hom.hom H.isClosedImmersion
    have h := ((centralizes_iff _ _).mp hc X f (x ≫ H.inclusion.hom.hom)).eq
    apply (cancel_mono H.inclusion.hom.hom).mp
    simpa only [Grp.comp_hom_hom, Grp.id_hom_hom, Category.comp_id,
      Category.assoc, postMul] using h
  obtain ⟨s, hs⟩ := (hZ _ _).mp hh
  obtain ⟨cZ, hcZ⟩ := factor_group_through_subgroup Z c s hs
  rw [← hcZ, cocharacter_to_finite_group (closedSubgroupAlgebraicGroup Z) hz cZ, zero_comp]

private def cocharacterPushforward {k : Type u} [Field k] {S T : Specs.GroupScheme k}
    [IsCommMonObj S.X] [IsCommMonObj T.X] (f : S ⟶ T) :
    Additive (Cocharacter S) →ₗ[ℤ] Additive (Cocharacter T) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun c => Additive.ofMul (c.toMul ≫ f)
      map_zero' := congrArg Additive.ofMul (show (0 : Cocharacter S) ≫ f = 0 from zero_comp)
      map_add' := fun _ _ => Grp.hom_ext _ _ (MonObj.mul_comp _ _ _) }

set_option backward.isDefEq.respectTransparency false in
private theorem cocharacter_eq_zero_of_nsmul_eq_zero {k : Type u} [Field k]
    {T : Specs.GroupScheme k} [IsCommMonObj T.X] (c : Cocharacter T) {n : ℕ} (hn : n ≠ 0)
    (h : n • Additive.ofMul c = 0) : c = 0 := by
  let X := IntegerCharacters.{u}
  letI : Group.FG X := Group.fg_of_surjective (f := (MulEquiv.ulift.symm : Multiplicative ℤ ≃* X).toMonoidHom)
    MulEquiv.ulift.symm.surjective
  let M := diagonalGroup k X
  letI : IsCommMonObj M.val.X := Specs.CharacterDescent.groupAlgebraSpectrumIsCommMonObj
  let e : X ≃* (Fin 1 → X) := (MulEquiv.funUnique (Fin 1) X).symm
  let a : (groupAlgebra k X) ≅ groupAlgebra k (Fin 1 → X) :=
    CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv k k e)
  obtain ⟨b⟩ := CharacterDescent.standardSplitTorus (k := k) 1
  have hM : Specs.GeometricRadicals.IsTorus M.val :=
    isTorus_of_split ⟨1, ⟨(hopfSpec (CommRingCat.of k)).mapIso a.symm.op ≪≫ b⟩⟩
  let p := CentralFrobeniusDescent.powerHom M.val n
  obtain ⟨hf, hs⟩ := CentralFrobeniusDescent.torus_power_flat_surjective M hM n hn
  letI : Flat p.hom.hom.left := hf
  letI : Surjective p.hom.hom.left := hs
  have hp : p ≫ c = c ^ n := by
    apply Grp.hom_ext
    change (CentralFrobeniusDescent.powerHom M.val n).hom.hom ≫ c.hom.hom = (c ^ n).hom.hom
    simp only [CentralFrobeniusDescent.powerHom, Grp.Hom.hom_pow, Mon.Hom.hom_pow, Grp.id_hom_hom]
    rw [MonObj.pow_comp, Category.id_comp]
  apply cancel_groupHom_of_flat_of_surjective p
  rw [hp, comp_zero]
  exact congrArg Additive.toMul h

set_option backward.isDefEq.respectTransparency false in
theorem splitDerivedCocharacterSaturation : SplitDerivedCocharacterSaturation.{u} := by
  classical
  intro k _ P D H hH c
  letI := D.comm
  obtain ⟨Q, q, hker, _, ht⟩ := Reductive.CentralDerived.derivedTorusQuotient P.G P.reductive H hH
  have hHss := Reductive.CentralDerived.derivedSemisimple P.G P.reductive H hH
  letI := torus_commutative Q ht
  let F := cocharacterPushforward (P.T.inclusion ≫ q)
  have hspan : corootLattice D ≤ F.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨α, rfl⟩
    apply LinearMap.mem_ker.mpr
    exact congrArg Additive.ofMul (attachedCorootToCommutative P.G Q P.T α _ (D.datum.attached α) q
      (fun _ _ _ => mul_comm _ _))
  have factors (x : Cocharacter P.T.group) :
      (∃ d : Cocharacter H.group, d ≫ H.inclusion = x ≫ P.T.inclusion) ↔
        F (Additive.ofMul x) = 0 := by
    constructor
    · rintro ⟨d, hd⟩
      have hp := (schemeKernel_sections hker (x ≫ P.T.inclusion).hom.hom).mp
        ⟨d.hom.hom, congrArg (fun f => f.hom.hom) hd⟩
      have hzero : (x ≫ P.T.inclusion) ≫ q = 0 := Grp.hom_ext _ _ hp
      exact congrArg Additive.ofMul ((Category.assoc _ _ _).symm.trans hzero)
    · intro hx
      obtain ⟨s, hs⟩ := (schemeKernel_sections hker (x ≫ P.T.inclusion).hom.hom).mpr
        (congrArg (fun f => f.hom.hom) (show (x ≫ P.T.inclusion) ≫ q = 0 from
          (Category.assoc _ _ _).trans (congrArg Additive.toMul hx)))
      exact factor_group_through_subgroup H (x ≫ P.T.inclusion) s hs
  rw [factors]
  refine ⟨?_, ?_⟩
  · intro hc
    let r := (cocharacterSum D.toBased).range
    letI : Finite (D.toBased.Y ⧸ r) := cocharacterSum_finiteQuotient D.toBased
    let n := Nat.card (D.toBased.Y ⧸ r)
    have hn : n ≠ 0 := Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
    obtain ⟨⟨x, z⟩, hxz⟩ : n • Additive.ofMul c ∈ r :=
      AddSubgroup.nsmul_index_mem r.toAddSubgroup (Additive.ofMul c)
    let x₀ : Additive (Cocharacter P.T.group) := x.val
    let z₀ : Additive (Cocharacter P.T.group) := z.val
    have hx₀ : x₀ ∈ corootLattice D := x.property
    change x₀ + z₀ = n • Additive.ofMul c at hxz
    have hqz : F z₀ = 0 := by
      have h := congrArg F hxz
      simp only [map_add, map_nsmul, hc, smul_zero, LinearMap.mem_ker.mp (hspan hx₀), zero_add] at h
      exact h
    obtain ⟨d, hd⟩ := (factors z₀.toMul).mpr hqz
    obtain ⟨_, _, _, _, _, hcent⟩ := RootData.SchemeCentre.schemeCentre P.G P.reductive P.T P.split P.maximal
    let R := CommAlgCat.of k (MonoidAlgebra k IntegerCharacters)
    have hz : Centralizes (𝟙 P.G.val) (z₀.toMul ≫ P.T.inclusion).hom.hom := by
      apply (hcent R z₀.toMul.hom.hom).mpr
      intro α hα
      have h0 := LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp z.property ⟨α, hα⟩)
      change D.datum.rootDatum.toLinearMap (D.datum.rootDatum.root ⟨α, hα⟩) z₀ = 0 at h0
      rw [D.datum.root_eq] at h0
      have hEq := (pairing_eq_iff α z₀.toMul 0).mpr ((D.datum.pairing_eq α z₀.toMul).symm.trans h0)
      rw [powerMorphism_zero] at hEq
      exact congrArg (fun f => f.hom.hom) hEq
    have hd0 : d = 0 := cocharacter_in_central_derived_is_trivial H hHss d (hd.symm ▸ hz)
    have hz0 : z₀ = 0 := by
      letI : Mono P.T.inclusion :=
        (Grp.forget (SchemeOver k) ⋙ Over.forget _).mono_of_mono_map
          (show Mono P.T.inclusion.hom.hom.left from letI := P.T.isClosedImmersion; inferInstance)
      have h : z₀.toMul ≫ P.T.inclusion = (0 : Cocharacter P.T.group) ≫ P.T.inclusion := by
        rw [← hd, hd0, zero_comp, zero_comp]
      exact congrArg Additive.ofMul ((cancel_mono P.T.inclusion).mp h)
    rw [hz0, add_zero] at hxz
    exact ⟨n, hn, hxz ▸ hx₀⟩
  · rintro ⟨n, hn, hx⟩
    have hh := LinearMap.mem_ker.mp (hspan hx)
    rw [map_nsmul] at hh
    exact congrArg Additive.ofMul (cocharacter_eq_zero_of_nsmul_eq_zero _ hn hh)

end CorootSaturation

section LeviCocharacters

open Specs.AbstractPairing (Root)
open Specs.CharacterDescent (Cocharacter)
open Specs.SimplyConnectedLattice (corootLattice)
open Specs.StandardParabolicLevi (leviRoots)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private splitBorelPair from LinearAlgebraicGroups.Classification.SimplyConnectedLattice

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
theorem splitLeviCocharacterSpan : SplitLeviCocharacterSpan.{u} := by
  intro k _ P D hG hsc
  letI := D.comm
  intro I hI c L hL H hH y
  obtain ⟨Tₗ, e, _, _, _, _, _, hred, hi, hmax, hs, hroot⟩ := hL
  let Gₗ := closedSubgroupAlgebraicGroup L.centralizer
  let Pₗ := splitBorelPair Gₗ hred Tₗ hs hmax
  let A := Classification.Pinning.attachedDatum Pₗ
  letI : IsCommMonObj Pₗ.T.group.X := A.comm
  letI : IsCommMonObj Tₗ.group.X := A.comm
  let A₀ : Specs.AbstractPairing.Datum (G := Gₗ) Tₗ := A.datum
  let B : Submodule ℤ (Additive (Cocharacter Tₗ.group)) := corootLattice A
  let y₀ : Additive (Cocharacter P.T.group) := y
  let F := cocharacterPushforward e.inv
  have hF : Function.Injective F := by
    intro x z h
    exact congrArg Additive.ofMul ((cancel_mono e.inv).mp (congrArg Additive.toMul h))
  have hinc : e.inv ≫ P.T.inclusion = Tₗ.inclusion ≫ L.centralizer.inclusion :=
    (congrArg (e.inv ≫ ·) hi.symm).trans (e.inv_hom_id_assoc _)
  have hsets : F '' Set.range A₀.rootDatum.coroot = D.datum.rootDatum.coroot '' leviRoots D.datum I := by
    have comparison (α : Root P.T) (hα : α ∈ leviRoots D.datum I) :
        ∃ β : Root (G := Gₗ) Tₗ, β.val = e.inv ≫ α.val ∧
          F (A₀.rootDatum.coroot β) = D.datum.rootDatum.coroot α := by
      have hb : e.inv ≫ α.val ∈ Specs.CharacterPairing.absoluteRoots Tₗ :=
        hroot.symm ▸ Set.mem_image_of_mem _ hα
      let β : Root (G := Gₗ) Tₗ := ⟨_, hb⟩
      exact ⟨β, rfl, congrArg Additive.ofMul
        (corootUnderTorusIso Gₗ P.G P.reductive Tₗ P.T P.split P.maximal
          L.centralizer.inclusion e.symm hinc α hb _ _ (A₀.attached β) (D.datum.attached α))⟩
    ext z
    constructor
    · rintro ⟨_, ⟨β, rfl⟩, rfl⟩
      obtain ⟨α, ha, hv⟩ := (congrArg (fun S => β.val ∈ S) hroot).mp β.property
      obtain ⟨β', hv', hc⟩ := comparison α ha
      have he : β' = β := Subtype.ext (hv'.trans hv)
      exact ⟨α, ha, he ▸ hc.symm⟩
    · rintro ⟨α, ha, rfl⟩
      obtain ⟨β, _, he⟩ := comparison α ha
      exact ⟨_, ⟨β, rfl⟩, he⟩
  have hmap : B.map F = Submodule.span ℤ (D.datum.rootDatum.coroot '' leviRoots D.datum I) := by
    have hCorootLattice : B = Submodule.span ℤ (Set.range A₀.rootDatum.coroot) := rfl
    rw [hCorootLattice, Submodule.map_span, hsets]
  obtain ⟨hspan, saturated⟩ := faceCorootSpan P D hG hsc I hI
  have hmap' : B.map F = Submodule.span ℤ (D.datum.rootDatum.coroot '' I) :=
    hmap.trans hspan
  let d : Cocharacter Tₗ.group := y₀.toMul ≫ e.hom
  have hd : d ≫ Tₗ.inclusion ≫ L.centralizer.inclusion = y₀.toMul ≫ P.T.inclusion :=
    (Category.assoc _ _ _).trans (congrArg (y₀.toMul ≫ ·) hi)
  have hFd : F (Additive.ofMul d) = y₀ := by
    change Additive.ofMul ((y₀.toMul ≫ e.hom) ≫ e.inv) = y₀
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
    rfl
  have hsat := splitDerivedCocharacterSaturation Pₗ A H hH d
  constructor
  · rintro ⟨x, hx⟩
    letI : Mono L.centralizer.inclusion :=
      (Grp.forget (SchemeOver k) ⋙ Over.forget _).mono_of_mono_map
        (show Mono L.centralizer.inclusion.hom.hom.left from letI := L.centralizer.isClosedImmersion; inferInstance)
    have hf : x ≫ H.inclusion = d ≫ Tₗ.inclusion :=
      (cancel_mono L.centralizer.inclusion).mp ((Category.assoc _ _ _).trans
        (hx.trans (hd.symm.trans (Category.assoc _ _ _).symm)))
    obtain ⟨n, hn, hx⟩ := hsat.mp ⟨x, hf⟩
    have hm : F (n • Additive.ofMul d) ∈ B.map F := Submodule.mem_map_of_mem (f := F) hx
    rw [map_nsmul, hFd, hmap'] at hm
    exact saturated y₀ n hn hm
  · intro hy
    have hy' : y₀ ∈ B.map F := hmap'.symm ▸ hy
    obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp hy'
    have he : z = Additive.ofMul d := hF (hzy.trans hFd.symm)
    obtain ⟨x, hx⟩ := hsat.mpr ⟨1, one_ne_zero, by simpa only [one_nsmul] using he ▸ hz⟩
    exact ⟨x, (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ L.centralizer.inclusion) hx).trans
      ((Category.assoc _ _ _).trans hd))⟩

end LeviCocharacters

section DerivedLeviTorus

open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Opposite

set_option backward.isDefEq.respectTransparency false

open _root_.LinearAlgebraicGroups.Specs
open Specs.GeometricRadicals (IsTorus IsReductive IsSplitTorus IsMaximalTorus GeometricGroup baseChangedSubgroup)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.SchemeDerivedGroup (IsDerivedSubgroup)
open Specs.RankOneFlag (IsGeometricallyMaximal)

open private factor_group_through_subgroup from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private centralizes_iff mono_over from LinearAlgebraicGroups.Affine.Stabilizers
open private comp_conjugate conjugationIso conjugate exists_maximal_torus_over
    transportSubgroup maximal_of_square
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private torus_commutative from LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private isSplitTorus_of_isAlgClosed from LinearAlgebraicGroups.Reductive.NontrivialRationalTorus
open private geometricallyMaximal_of_maximal_split from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private rational_maximal_exists torus_descends_from_algebraic_closure
  from LinearAlgebraicGroups.Reductive.MaximalToriExist
open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies

variable {k : Type u} [Field k]

private theorem closedSubgroup_mono {G : GroupScheme k} (H : ClosedSubgroup G) :
    Mono H.inclusion :=
  Functor.mono_of_mono_map (Grp.forget (SchemeOver k)) (by
    change Mono H.inclusion.hom.hom
    exact mono_over _ H.isClosedImmersion)

private theorem conjugationRestrictsToNormal {G : GroupScheme k} (H : ClosedSubgroup G)
    (hH : IsNormalSubgroup H.inclusion) (g : 𝟙_ (SchemeOver k) ⟶ G.X) :
    ∃ e : H.group ≅ H.group, e.hom ≫ H.inclusion = H.inclusion ≫ (conjugationIso g).hom := by
  let e := conjugationIso g
  have fac (a : 𝟙_ (SchemeOver k) ⟶ G.X) :
      ∃ f : H.group ⟶ H.group, f ≫ H.inclusion = H.inclusion ≫ (conjugationIso a).hom := by
    obtain ⟨c, hc⟩ := hH
    let p := lift ((toUnit H.group.X) ≫ a) (𝟙 H.group.X)
    apply factor_group_through_subgroup H _ (p ≫ c)
    rw [Category.assoc, hc]
    change p ≫ subgroupConjugation H.inclusion =
      H.inclusion.hom.hom ≫ conjugate a (𝟙 G.X)
    rw [comp_conjugate, Category.comp_id]
    simp only [p, subgroupConjugation, MonObj.comp_mul, GrpObj.comp_inv,
      lift_fst, lift_snd_assoc]
    rfl
  obtain ⟨f, hf⟩ := fac g
  obtain ⟨r, hr⟩ := fac g⁻¹
  have hi : (conjugationIso g⁻¹).hom = e.inv := by
    apply Grp.hom_ext
    rfl
  rw [hi] at hr
  letI := closedSubgroup_mono H
  refine ⟨⟨f, r, ?_, ?_⟩, hf⟩
  · apply (cancel_mono H.inclusion).mp
    rw [Category.assoc, hr, ← Category.assoc, hf, Category.assoc, e.hom_inv_id,
      Category.comp_id, Category.id_comp]
  · apply (cancel_mono H.inclusion).mp
    rw [Category.assoc, hf, ← Category.assoc, hr, Category.assoc, e.inv_hom_id,
      Category.comp_id, Category.id_comp]

private theorem normalTorusInMaximal [IsAlgClosed k]
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (H T : ClosedSubgroup G.val) (hH : IsNormalSubgroup H.inclusion)
    (hT : IsMaximalTorus T) :
    ∃ V : ClosedSubgroup H.group, IsMaximalTorus V ∧
      Specs.SchemeDerivedGroup.IsSubgroupOf (subgroupOfSubgroup H V) T := by
  obtain ⟨U, hU⟩ := rational_maximal_exists (closedSubgroupAlgebraicGroup H)
  obtain ⟨A, hA, j, hj⟩ := exists_maximal_torus_over G (subgroupOfSubgroup H U) hU.1
  haveI := hG.2.1
  have hc := GeometricallyConnected.connectedSpace_of_subsingleton (f := G.val.X.hom)
  obtain ⟨g, e, he⟩ := MaximalToriConjugate.maximalToriConjugate G hG.1 hc A T hA hT
  obtain ⟨d, hd⟩ := conjugationRestrictsToNormal H hH g
  let V := transportSubgroup d U
  refine ⟨V, maximal_of_square d U V (Iso.refl _) (Category.id_comp _) hU, j ≫ e.hom, ?_⟩
  rw [Category.assoc]
  have he' : e.hom ≫ T.inclusion = A.inclusion ≫ (conjugationIso g).hom := by
    apply Grp.hom_ext
    change (e.hom ≫ T.inclusion).hom.hom = A.inclusion.hom.hom ≫ conjugate g (𝟙 G.val.X)
    rw [comp_conjugate, Category.comp_id]
    exact he
  change j ≫ e.hom ≫ T.inclusion = (U.inclusion ≫ d.hom) ≫ H.inclusion
  rw [he', ← Category.assoc, hj, Category.assoc, hd]
  rfl

private theorem geometricNormalTorusIntersection [IsAlgClosed k]
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (H T : ClosedSubgroup G.val) (hH : IsNormalSubgroup H.inclusion)
    (hHr : IsReductive (closedSubgroupAlgebraicGroup H))
    (hT : IsMaximalTorus T)
    (V : ClosedSubgroup H.group) (i : V.group ⟶ T.group)
    (hp : IsPullback i V.inclusion T.inclusion H.inclusion) :
    IsMaximalTorus V := by
  obtain ⟨U, hU, j, hj⟩ := normalTorusInMaximal G hG H T hH hT
  let v : U.group ⟶ V.group := hp.lift j U.inclusion hj
  have hvi : v ≫ i = j := hp.lift_fst _ _ _
  have hv : v ≫ V.inclusion = U.inclusion := hp.lift_snd _ _ _
  let HR := closedSubgroupAlgebraicGroup H
  have hgeom := geometricallyMaximal_of_maximal_split HR U hU (isSplitTorus_of_isAlgClosed (G := HR) U hU.1)
  have hcent := Reductive.TorusCentralizer.maximalTorusCentralizer HR hHr U hU.1 hgeom
  let w := V.inclusion
  letI : IsCommMonObj T.group.X := torus_commutative (closedSubgroupAlgebraicGroup T) hT.1
  haveI : Mono H.inclusion.hom.hom := mono_over _ H.isClosedImmersion
  have hcomm : Centralizes U.inclusion w.hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro Y a b
    apply Commute.of_map (f := IsMonHom.monoidHom H.inclusion.hom.hom Y)
      (fun _ _ h => (cancel_mono H.inclusion.hom.hom).mp h)
    change Commute ((a ≫ w.hom.hom) ≫ H.inclusion.hom.hom)
      ((b ≫ U.inclusion.hom.hom) ≫ H.inclusion.hom.hom)
    have hp' := congrArg (fun f => f.hom.hom) hp.w
    have hj' := congrArg (fun f => f.hom.hom) hj
    change i.hom.hom ≫ T.inclusion.hom.hom = w.hom.hom ≫ H.inclusion.hom.hom at hp'
    change j.hom.hom ≫ T.inclusion.hom.hom = U.inclusion.hom.hom ≫ H.inclusion.hom.hom at hj'
    have ha : (a ≫ w.hom.hom) ≫ H.inclusion.hom.hom =
        (a ≫ i.hom.hom) ≫ T.inclusion.hom.hom := by rw [Category.assoc, ← hp', ← Category.assoc]
    have hb : (b ≫ U.inclusion.hom.hom) ≫ H.inclusion.hom.hom =
        (b ≫ j.hom.hom) ≫ T.inclusion.hom.hom := by rw [Category.assoc, ← hj', ← Category.assoc]
    rw [ha, hb]
    exact (show Commute (a ≫ i.hom.hom) (b ≫ j.hom.hom) from mul_comm _ _).map
      (IsMonHom.monoidHom T.inclusion.hom.hom Y)
  obtain ⟨c, hc⟩ := (hcent _ _).mp hcomm
  obtain ⟨s, hs⟩ := factor_group_through_subgroup U w c hc
  letI := closedSubgroup_mono U
  letI := closedSubgroup_mono V
  let e : U.group ≅ V.group := ⟨v, s,
    (cancel_mono U.inclusion).mp (by rw [Category.assoc, hs, hv, Category.id_comp]),
    (cancel_mono V.inclusion).mp (by rw [Category.assoc, hv, hs, Category.id_comp])⟩
  exact maximal_of_square (Iso.refl _) U V e (hv.trans (Category.comp_id _).symm) hU

open Specs.CharacterDescent (StandardLattice)
open Specs.DiagonalizableGroups (groupAlgebra)
open private splitPresentation latticeCoordinates from LinearAlgebraicGroups.RootData.CharacterPairing
open private torus_of_iso from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private groupPresentation from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private noFiniteOrderOfConnectedSplit latticeEquivOfBasis reducedOfSmoothHopf
  from LinearAlgebraicGroups.Multiplicative.SmoothnessAndIsogenies

private theorem splitOfClosedTorus (V : AffineAlgebraicGroup k) (hV : IsTorus V.val)
    {T : GroupScheme k} (hT : IsSplitTorus T) (f : V.val ⟶ T)
    (hf : IsClosedImmersion f.hom.hom.left) :
    IsSplitTorus V.val := by
  obtain ⟨n, ⟨e⟩⟩ := splitPresentation hT
  obtain ⟨B, _, ⟨d⟩⟩ := groupPresentation V
  let M := StandardLattice.{u} n
  let ff := hopfSpec.fullyFaithful (R := CommRingCat.of k)
  let a : groupAlgebra k M ⟶ B := (ff.preimage (d.hom ≫ f ≫ e.inv)).unop
  have ha : specGroupMap a = d.hom ≫ f ≫ e.inv := ff.map_preimage _
  have hsa : Function.Surjective a.hom := by
    apply (hopfMapClosedImmersion k a).mp
    rw [ha]
    let F := Grp.forget (SchemeOver k) ⋙ Over.forget _
    haveI : IsIso (F.map d.hom) := F.map_isIso d.hom
    haveI : IsIso (F.map e.inv) := F.map_isIso e.inv
    change IsClosedImmersion ((F.map d.hom) ≫ (F.map f) ≫ (F.map e.inv))
    letI : IsClosedImmersion (F.map f) := hf
    infer_instance
  obtain ⟨N, ⟨v, _⟩, _⟩ := (DiagonalizableGroups.hopfQuotientClassification k M a).mp hsa
  let C := groupAlgebra k (M ⧸ N)
  let j : C ≅ B := CommHopfAlgCat.isoMk v
  let i := (hopfSpec (CommRingCat.of k)).mapIso j.symm.op ≪≫ d
  have htor := (LinearAlgebraicGroups.GeometricRadicals.torusCoordinateComparison C).mp
    (torus_of_iso i.symm hV)
  obtain ⟨_, hSmooth, hConn⟩ :=
    (SmoothnessAndIsogenies.smoothConnectedMultiplicativeType C).mp htor
  letI : _root_.IsReduced (MonoidAlgebra k (M ⧸ N)) := reducedOfSmoothHopf C hSmooth
  letI : ConnectedSpace (PrimeSpectrum (MonoidAlgebra k (M ⧸ N))) := hConn
  letI : Module.Finite ℤ (Additive M) := Module.Finite.equiv (latticeCoordinates n).symm
  letI : Group.FG M := GroupFG.iff_add_fg.mpr (Module.Finite.iff_addGroup_fg.mp inferInstance)
  letI : Module.Finite ℤ (Additive (M ⧸ N)) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  letI : Module.IsTorsionFree ℤ (Additive (M ⧸ N)) := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro x m hm
    by_cases hx : x = 0
    · exact Or.inl hx
    right
    have hd : (orderOf m.toMul : ℤ) ∣ x := orderOf_dvd_iff_zpow_eq_one.mpr hm
    have hn : 0 < orderOf m.toMul := by
      by_contra! h
      exact hx (by simpa [Nat.eq_zero_of_le_zero h] using hd)
    exact noFiniteOrderOfConnectedSplit (k := k) m.toMul hn
  obtain ⟨r, b⟩ := Module.basisOfFiniteTypeTorsionFree'
    (R := ℤ) (M := Additive (M ⧸ N))
  let w := CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv k k (latticeEquivOfBasis b))
  obtain ⟨t⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) r
  exact ⟨r, ⟨i.symm ≪≫ (hopfSpec (CommRingCat.of k)).mapIso w.symm.op ≪≫ t⟩⟩

/-- The pullback with the derived inclusion is already a maximal torus,
including as a scheme in positive characteristic. -/
theorem derivedMaximalTorusIntersection : DerivedMaximalTorusIntersection.{u} := by
  intro k _ G hG T hT H hH
  let P := pullback T.inclusion H.inclusion
  let i : P ⟶ T.group := pullback.fst _ _
  let j : P ⟶ H.group := pullback.snd _ _
  have hp : IsPullback i j T.inclusion H.inclusion := IsPullback.of_hasPullback _ _
  have hp' := hp.map (Grp.forget (SchemeOver k) ⋙ Over.forget _)
  have hi : IsClosedImmersion i.hom.hom.left := MorphismProperty.of_isPullback hp'.flip H.isClosedImmersion
  have hj : IsClosedImmersion j.hom.hom.left := MorphismProperty.of_isPullback hp' T.isClosedImmersion
  let V : ClosedSubgroup H.group := ⟨P, j, hj⟩
  let Vg := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup H) V
  let K := AlgebraicClosure k
  let E := groupBaseChange k K
  obtain ⟨hTK, hmTK⟩ := hT
  have hHK : IsClosedImmersion (E.map H.inclusion).hom.hom.left :=
    baseChangeClosedSubgroup k K H.inclusion H.isClosedImmersion
  have hVK : IsClosedImmersion (E.map V.inclusion).hom.hom.left :=
    baseChangeClosedSubgroup k K V.inclusion V.isClosedImmersion
  let TK := baseChangedSubgroup K T hTK
  let HK := baseChangedSubgroup K H hHK
  let VK := baseChangedSubgroup K V hVK
  have hGk : IsReductive (GeometricGroup G) :=
    (Reductive.RadicalBaseChange.reductiveFieldExtension (K := K) G hG.1 hG.2.1).mpr hG
  have hHr := reductive_of_semisimple (closedSubgroupAlgebraicGroup H)
    (Reductive.CentralDerived.derivedSemisimple G hG H hH)
  have hHKr : IsReductive (closedSubgroupAlgebraicGroup (G := GeometricGroup G) HK) :=
    (Reductive.RadicalBaseChange.reductiveFieldExtension (K := K)
      (closedSubgroupAlgebraicGroup H) hHr.1 hHr.2.1).mpr hHr
  have hmax : IsMaximalTorus VK :=
    geometricNormalTorusIntersection (GeometricGroup G) hGk HK TK
      (baseChangeNormalSubgroup k K H.inclusion hH.1) hHKr hmTK VK (E.map i)
      (baseChangeSubgroupPullback k K hp)
  have htor : IsTorus V.group := torus_descends_from_algebraic_closure Vg hmax.1
  exact ⟨V, i, hp, hi, htor, ⟨hVK, hmax⟩, fun hs => splitOfClosedTorus Vg htor hs i hi⟩

open CocharacterDynamics (LimitDecomposition)
open Specs.CharacterDescent (Cocharacter)
open private factor_closed from LinearAlgebraicGroups.Reductive.GeometricRadicals
open private torus_after_algClosed_extension from LinearAlgebraicGroups.Reductive.MaximalToriExist
open private groupBaseChangeTowerIso from LinearAlgebraicGroups.Relative.RationalCocharacter
open private maximal_torus_in_intermediate_group from LinearAlgebraicGroups.RootData.RankOneFlag

set_option maxHeartbeats 650000 in
private theorem maximalTorusInLevi (G : AffineAlgebraicGroup k)
    (T : ClosedSubgroup G.val) (hT : IsTorus T.group) (hTm : IsGeometricallyMaximal T)
    (c : Cocharacter T.group) (L : LimitDecomposition (c ≫ T.inclusion)) :
    ∃ A : ClosedSubgroup L.centralizer.group,
      ∃ e : T.group ≅ A.group,
        e.hom ≫ A.inclusion ≫ L.centralizer.inclusion = T.inclusion ∧
        IsGeometricallyMaximal A := by
  letI : IsCommMonObj T.group.X := torus_commutative (closedSubgroupAlgebraicGroup T) hT
  have hcomm : Centralizes (c ≫ T.inclusion) T.inclusion.hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro Y a b
    change Commute (a ≫ T.inclusion.hom.hom)
      (b ≫ c.hom.hom ≫ T.inclusion.hom.hom)
    exact (show Commute a (b ≫ c.hom.hom) from mul_comm _ _).map
      (IsMonHom.monoidHom T.inclusion.hom.hom Y)
  obtain ⟨f, hf⟩ := (L.centralizer_points _ _).mp hcomm
  obtain ⟨j, hj⟩ := factor_group_through_subgroup L.centralizer T.inclusion f hf
  have hjc : IsClosedImmersion j.hom.hom.left := factor_closed (H := T) hj
  let A : ClosedSubgroup L.centralizer.group := ⟨T.group, j, hjc⟩
  refine ⟨A, Iso.refl _, (Category.id_comp _).trans hj, ?_⟩
  exact maximal_torus_in_intermediate_group hj hTm

private theorem baseChangeOfTorus (K : Type u) [Field K] [Algebra k K]
    (U : AffineAlgebraicGroup k) (hU : IsTorus U.val) :
    IsTorus ((groupBaseChange k K).obj U.val) := by
  let E := AlgebraicClosure K
  let UK := Specs.Unipotent.baseChangedAlgebraicGroup K U
  apply torus_descends_from_algebraic_closure UK
  exact torus_of_iso ((groupBaseChangeTowerIso (k := k) (K := K) (L := E)).app U.val).symm
    (torus_after_algClosed_extension E U hU)

theorem rationalDerivedLeviTorus : RationalDerivedLeviTorus.{u} := by
  intro k _ G T hT hTm c L hL H hH
  obtain ⟨A, e, he, hA⟩ := maximalTorusInLevi G T hT hTm c L
  let R := closedSubgroupAlgebraicGroup L.centralizer
  obtain ⟨V, j, hpb, hj, hV, hmaxV, _⟩ := derivedMaximalTorusIntersection R hL A hA H hH
  let a : V.group ⟶ T.group := j ≫ e.inv
  letI := closedSubgroup_mono L.centralizer
  let LS := L.centralizer.inclusion
  have he' : e.inv ≫ T.inclusion = A.inclusion ≫ LS :=
    (congrArg (e.inv ≫ ·) he.symm).trans (e.inv_hom_id_assoc _)
  have hp' : IsPullback e.inv A.inclusion T.inclusion LS :=
    IsPullback.of_horiz_isIso_mono ⟨he'⟩
  have hpb' : IsPullback a V.inclusion T.inclusion (H.inclusion ≫ LS) := hpb.paste_horiz hp'
  have ha : IsClosedImmersion a.hom.hom.left := by
    have := hj
    let U := Grp.forget (SchemeOver k) ⋙ Over.forget _
    haveI : IsIso (U.map e.inv) := U.map_isIso e.inv
    exact inferInstanceAs (IsClosedImmersion (j.hom.hom.left ≫ (U.map e.inv)))
  refine ⟨V, a, hpb', ha, hV, hmaxV, ?_⟩
  intro K _ _ ht
  let V' := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup (G := R) H) V
  let VK := Specs.Unipotent.baseChangedAlgebraicGroup K V'
  have hVK : IsTorus VK.val := baseChangeOfTorus K V' hV
  exact splitOfClosedTorus VK hVK ht ((groupBaseChange k K).map a)
    (baseChangeClosedSubgroup k K a ha)

end DerivedLeviTorus

section DerivedCocharacterIntersection

open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

open _root_.LinearAlgebraicGroups.Specs
open Specs.SchemeDerivedGroup (IsDerivedSubgroup FactorsThrough commutatorMap)
open Specs.GeometricRadicals (baseChangedSubgroup)
open Specs.CharacterDescent (Cocharacter)
open CocharacterDynamics (LimitDecomposition)
open Specs.AbstractPairing (Root)
open Specs.Pinning (SplitBorelPair AttachedDatum)
open Specs.GeometricRadicals (IsSemisimple)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open private transportSubgroup transport_normal from LinearAlgebraicGroups.Reductive.RadicalBaseChange

variable {k : Type u} [Field k]

private theorem commutatorMap_comp {G H : GroupScheme k} (e : G ⟶ H) :
    (e.hom.hom ⊗ₘ e.hom.hom) ≫ commutatorMap (𝟙 H) (𝟙 H) =
      commutatorMap (𝟙 G) (𝟙 G) ≫ e.hom.hom := by
  simp [commutatorMap, MonObj.comp_mul, GrpObj.comp_inv, MonObj.mul_comp, GrpObj.inv_comp]

private theorem commutatorFactorsThroughIso {G H : GroupScheme k} (e : G ≅ H)
    (D : ClosedSubgroup G) (hD : FactorsThrough D (commutatorMap (𝟙 G) (𝟙 G))) :
    FactorsThrough (transportSubgroup e D) (commutatorMap (𝟙 H) (𝟙 H)) := by
  obtain ⟨t, ht⟩ := hD
  change t ≫ D.inclusion.hom.hom = commutatorMap (𝟙 G) (𝟙 G) at ht
  refine ⟨(e.inv.hom.hom ⊗ₘ e.inv.hom.hom) ≫ t, ?_⟩
  change ((e.inv.hom.hom ⊗ₘ e.inv.hom.hom) ≫ t) ≫
    (D.inclusion.hom.hom ≫ e.hom.hom.hom) = _
  rw [Category.assoc, ← Category.assoc t, ht, ← Category.assoc, commutatorMap_comp]
  change commutatorMap (𝟙 H) (𝟙 H) ≫ (e.inv ≫ e.hom).hom.hom = _
  rw [e.inv_hom_id]
  exact Category.comp_id _

private theorem derivedSubgroupOfIso {G H : GroupScheme k} (e : G ≅ H)
    (D : ClosedSubgroup G) (hD : IsDerivedSubgroup D) :
    IsDerivedSubgroup (transportSubgroup e D) := by
  refine ⟨transport_normal e D hD.1, commutatorFactorsThroughIso e D hD.2.1, ?_⟩
  intro N hN hcommN
  obtain ⟨j, hj⟩ := hD.2.2 (transportSubgroup e.symm N) (transport_normal e.symm N hN)
    (commutatorFactorsThroughIso e.symm N hcommN)
  refine ⟨j, ?_⟩
  have hh : j ≫ N.inclusion ≫ e.inv = D.inclusion := hj
  change j ≫ N.inclusion = D.inclusion ≫ e.hom
  calc
    j ≫ N.inclusion = (j ≫ N.inclusion ≫ e.inv) ≫ e.hom := by simp only
      [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = D.inclusion ≫ e.hom := congrArg (· ≫ e.hom) hh

private theorem cocharacterFactorsThroughIntersection {G T H V : GroupScheme k}
    (t : T ⟶ G) (h : H ⟶ G) (i : V ⟶ T) (j : V ⟶ H) (hp : IsPullback i j t h)
    (y : Cocharacter T) :
    (∃ z : Cocharacter V, z ≫ i = y) ↔ (∃ z : Cocharacter H, z ≫ h = y ≫ t) := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z ≫ j, ?_⟩
    rw [Category.assoc, ← hp.w, ← Category.assoc, hz]
  · rintro ⟨z, hz⟩
    exact ⟨hp.lift y z hz.symm, hp.lift_fst _ _ _⟩

set_option maxHeartbeats 650000 in
private theorem cocharacterSpanForDerivedIntersection {P : SplitBorelPair k} (D : AttachedDatum P)
    (hG : IsSemisimple P.G) (hsc : GeometricallySimplyConnected P.G)
    (I : Set (Root P.T)) (hI : letI := D.comm; I ⊆ D.base.support)
    (c : Cocharacter P.T.group) (L : LimitDecomposition (c ≫ P.T.inclusion))
    (hL : IsSplitStandardLevi D I L)
    {M V : GroupScheme k} (H : ClosedSubgroup M) (hH : IsDerivedSubgroup H)
    (e : M ≅ L.centralizer.group) (i : V ⟶ P.T.group) (j : V ⟶ H.group)
    (hp : IsPullback i j P.T.inclusion (H.inclusion ≫ e.hom ≫ L.centralizer.inclusion)) :
    letI := D.comm
    ∀ y : D.toBased.Y, (∃ z : Cocharacter V, z ≫ i = y.toMul) ↔
      y ∈ Submodule.span ℤ (D.datum.rootDatum.coroot '' I) := by
  let := D.comm
  intro y
  let H' := transportSubgroup e H
  have hH' : IsDerivedSubgroup H' := derivedSubgroupOfIso e H hH
  change IsPullback i j P.T.inclusion (H.inclusion ≫ e.hom ≫ L.centralizer.inclusion) at hp
  rw [← Category.assoc] at hp
  have hp' : IsPullback i j P.T.inclusion (H'.inclusion ≫ L.centralizer.inclusion) := hp
  exact (cocharacterFactorsThroughIntersection _ _ _ _ hp' y.toMul).trans
    (splitLeviCocharacterSpan P D hG hsc I hI c L hL H' hH' y)

set_option maxHeartbeats 650000 in
theorem rationalFaceDerivedTorus : RationalFaceDerivedTorus.{u} := by
  intro F K _ _ _ _ _ G T B S D e ω hG hT hmax hss hsc he hω I
  let := D.comm
  intro hI hstable
  obtain ⟨c, hc, L, H, Lk, hP, hB, hL, hH, hHss, hLk, j, hj, hHc, hDk, _⟩ :=
    rationalFaceDerivedLevi G T B S D e ω hG hT hmax he hω I hI hstable
  obtain ⟨V, i, hp, hi, htor, hmaxV, hs⟩ := rationalDerivedLeviTorus G T hT hmax c L hL H hH
  refine ⟨c, hc, L, H, hP, hB, hL, hH, hHss, V, i, hp, hi, htor, hmaxV, hs K S.split, ?_⟩
  let E := groupBaseChange F K
  let Hk := baseChangedSubgroup K H hHc
  have hpK0 := baseChangeSubgroupPullback F K hp
  have hj' : E.map (H.inclusion ≫ L.centralizer.inclusion) =
      Hk.inclusion ≫ j.hom ≫ Lk.centralizer.inclusion := by
    change E.map (H.inclusion ≫ L.centralizer.inclusion) =
      E.map H.inclusion ≫ j.hom ≫ Lk.centralizer.inclusion
    rw [E.map_comp, hj]
  rw [hj'] at hpK0
  exact cocharacterSpanForDerivedIntersection D hss hsc I hI
    (e.hom ≫ E.map c) Lk hLk Hk hDk j (E.map i) (E.map V.inclusion) hpK0

end DerivedCocharacterIntersection

section TorusDescent

open Specs.CharacterDescent (GeometricCharacters IsDiagonalizable)
open LinearAlgebraicGroups.CharacterDescent (scalarExtensionDatum)
open private descendEquivariantHopfMap from LinearAlgebraicGroups.Multiplicative.CharacterDescent

theorem descentOnGeometricCharacters : DescentOnGeometricCharacters.{u} := by
  intro k K _ _ _ _ A B f hA hf
  let A' := extendedHopf K A
  let B' := extendedHopf K B
  let Φ := (scalarExtensionDatum K A).action
  let Ψ := (scalarExtensionDatum K B).action
  have span_top : Submodule.span K (Set.range (GroupLike.val (R := K) (A := A'))) = ⊤ := by
    obtain ⟨M, ⟨e⟩⟩ := hA
    letI : Group.FG M.obj := M.property
    let er := CommHopfAlgCat.ofIso e
    letI : Algebra.FiniteType K A' := Algebra.FiniteType.equiv
      (inferInstanceAs (Algebra.FiniteType K (MonoidAlgebra K M.obj))) er.toAlgEquiv
    exact (DiagonalizableGroups.groupLikeSpanning K A').mpr
      ⟨M.obj, inferInstance, inferInstance, ⟨er⟩⟩
  apply descendEquivariantHopfMap K f
  intro g x
  have hx : x ∈ Submodule.span K (Set.range (GroupLike.val (R := K) (A := A'))) := by
    rw [span_top]
    exact Submodule.mem_top
  change f.hom (Φ.act g x) = Ψ.act g (f.hom x)
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨x, rfl⟩ := hx
      exact hf g x
  | zero => simp
  | add x y _ _ ihx ihy => simp only [map_add, ihx, ihy]
  | smul r x hx ih =>
      rw [Φ.map_smul, map_smul]
      rw [map_smul, Ψ.map_smul]
      exact congrArg (g r • ·) ih

open Specs.DiagonalizableGroups (groupAlgebra)
open Specs.CharacterDescent (StandardLattice)
open private orbitWeilProduct from LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private splitPresentation latticeCoordinates from LinearAlgebraicGroups.RootData.CharacterPairing
open private extendedGroupIso from LinearAlgebraicGroups.Affine.ClosedSubgroups

theorem permutationTorusProduct : PermutationTorusProduct.{u} := by
  intro F K _ _ _ _ _ I _ ρ T hs b
  apply orbitWeilProduct b
  obtain ⟨r, ⟨d⟩⟩ := splitPresentation hs
  let M := StandardLattice.{u} r
  letI : Module.Finite ℤ (Additive M) := Module.Finite.equiv (latticeCoordinates r).symm
  letI : Group.FG M := GroupFG.iff_add_fg.mpr (Module.Finite.iff_addGroup_fg.mp inferInstance)
  let A := Specs.AdjointCocharacters.coordinateHopf T
  let e := extendedGroupIso K A ≪≫
    (groupBaseChange F K).mapIso (Specs.AdjointCocharacters.coordinateHopfIso T)
  let f : specGroup (groupAlgebra K M) ≅ specGroup (extendedHopf K A) := d ≪≫ e.symm
  exact ⟨⟨CommGrpCat.of M, inferInstance⟩, ⟨((hopfSpec.fullyFaithful (R := CommRingCat.of K)).preimageIso f).unop.symm⟩⟩

end TorusDescent

section MatrixDatum

open Specs.SpecialLinearDatum

theorem attachedMatrixCoroots : AttachedMatrixCoroots.{u} := by
  intro k _ r S s
  obtain ⟨T, L, M, B, D, hD, hpin, hsc⟩ :=
    RootData.SpecialLinearDatum.matrixPinnedDatum k r S s
  letI := D.comm
  refine ⟨T, L, M, B, D, hD, hpin, hsc, ?_, ?_⟩
  · intro i
    exact (hD.2 _).mpr ⟨i, rfl, rfl⟩
  · intro i R t
    dsimp only
    have h := hD.1 (adjacentRootIndex i)
    have hc := L.cocharacterPoint_eq (Specs.SpecialLinearDatum.coroot (r + 1) i.castSucc i.succ) R t
    change L.cocharacters (D.datum.rootDatum.coroot (M.indices (adjacentRootIndex i))) =
      Specs.SpecialLinearDatum.coroot (r + 1) i.castSucc i.succ at h
    rw [← h, LinearEquiv.symm_apply_apply] at hc
    rw [hc, h]
    congr 1
    funext j
    have hne : i.castSucc ≠ i.succ := ((Fin.castSucc_lt_succ_iff).mpr le_rfl).ne
    by_cases h₁ : j.down = i.castSucc
    · simp [Specs.SpecialLinearDatum.coroot, coordinate, coordinatePairUnits, h₁, hne.symm]
    by_cases h₂ : j.down = i.succ
    · simp [Specs.SpecialLinearDatum.coroot, coordinate, coordinatePairUnits, h₂, hne.symm]
    · simp [Specs.SpecialLinearDatum.coroot, coordinate, coordinatePairUnits, h₁, h₂]

end MatrixDatum

section HermitianModel

open Matrix

theorem unitaryScalarSplittingNaturality : UnitaryScalarSplittingNaturality.{u,v} := by
  intro F E _ _ _ _ _ R S _ _ _ _ _ _ _ _ f eR eS
  dsimp only
  intro hR hS z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      rw [Algebra.TensorProduct.map_tmul, hS, hR]
      simp
  | add a b ha hb =>
      rw [map_add, map_add, ha, hb, map_add]
      exact Prod.ext (map_add f _ _).symm (map_add f _ _).symm

private theorem reverseEntries_eq {E : Type u} [CommRing E] (A : Matrix (Fin 3) (Fin 3) E) :
    A.submatrix Fin.revPerm Fin.revPerm =
      hyperbolicGram E * A * hyperbolicGram E := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three,
      hyperbolicGram]

theorem hyperbolicFixedEquation : HyperbolicFixedEquation.{u} := by
  intro E _ σ g
  let J := hyperbolicGram E
  let b := Matrix.SpecialLinearGroup.map σ.toRingHom g
  let B := b.val.transpose
  let C := (b⁻¹).val.transpose
  have hBC : B * C = 1 := by
    change b.val.transpose * (b⁻¹).val.transpose = 1
    rw [← Matrix.transpose_mul]
    change ((b⁻¹ * b).val).transpose = 1
    rw [inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]
  have hCB : C * B = 1 := by
    change (b⁻¹).val.transpose * b.val.transpose = 1
    rw [← Matrix.transpose_mul]
    change ((b * b⁻¹).val).transpose = 1
    rw [mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]
  have hJ : J * J = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [J, Matrix.mul_apply, Fin.sum_univ_three, hyperbolicGram]
  change unitaryDescentOperator σ g = g ↔ B * J * g.val = J
  have hformula : (unitaryDescentOperator σ g).val = J * C * J :=
    reverseEntries_eq _
  constructor
  · intro hg
    have hg' : J * C * J = g.val := hformula.symm.trans (congrArg Subtype.val hg)
    calc
      B * J * g.val = B * J * (J * C * J) := congrArg (B * J * ·) hg'.symm
      _ = (B * (J * J) * C) * J := by simp [mul_assoc]
      _ = J := by simp [hJ, hBC]
  · intro hg
    apply Subtype.ext
    rw [hformula]
    calc
      J * C * J = J * C * (B * J * g.val) := congrArg (J * C * ·) hg.symm
      _ = (J * (C * B) * J) * g.val := by simp [mul_assoc]
      _ = g.val := by simp [hCB, hJ]

theorem unitaryDescentFixedPoints : UnitaryDescentFixedPoints.{u,v} := by
  intro F E _ _ _ σ g
  exact hyperbolicFixedEquation σ.toRingEquiv g

end HermitianModel

section UnitaryScheme

open CategoryTheory.Limits
open Matrix
open Specs.AdjointRepresentation (GroupPoints)
open LinearAlgebraicGroups.WeilRestriction (extendScalars)

private def reindexSpecialLinear {I J R : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [CommRing R] (e : I ≃ J) :
    Matrix.SpecialLinearGroup I R ≃* Matrix.SpecialLinearGroup J R where
  toFun g := ⟨g.val.submatrix e.symm e.symm,
    by rw [Matrix.det_submatrix_equiv_self, g.property]⟩
  invFun g := ⟨g.val.submatrix e e, by rw [Matrix.det_submatrix_equiv_self, g.property]⟩
  left_inv g := by
    apply Subtype.ext
    ext i j
    simp [Matrix.submatrix_apply]
  right_inv g := by
    apply Subtype.ext
    ext i j
    simp [Matrix.submatrix_apply]
  map_mul' g h := by
    apply Subtype.ext
    change (g.val * h.val).submatrix e.symm e.symm =
      g.val.submatrix e.symm e.symm * h.val.submatrix e.symm e.symm
    rw [Matrix.submatrix_mul_equiv]

private def specialLinearThreePointIso (E : Type u) [Field E] :
    (groupPointsFunctor E).obj (StandardGroups.specialLinearGroup E (ULift.{u} (Fin 3))).val ≅
      specialLinearThreePoints E :=
  StandardGroups.specialLinearGroupPointsIso E (ULift.{u} (Fin 3)) ≪≫
    NatIso.ofComponents (fun R => MulEquiv.toGrpIso (reindexSpecialLinear (R := R) Equiv.ulift)) (by
      intro R S f
      apply GrpCat.ext
      intro g
      apply Subtype.ext
      rfl)

set_option backward.isDefEq.respectTransparency false in
private def unitaryMatrixOperator (F E : Type u) [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] :
    let A := extendScalars F E ⋙ specialLinearThreePoints E
    A ⟶ A where
  app R := GrpCat.ofHom (hyperbolicDual.comp (Matrix.SpecialLinearGroup.map
    (quadraticTensorInvolution F E R).toRingEquiv.toRingHom))
  naturality {R S} f := by
    apply GrpCat.ext
    intro g
    let φ : R ⊗[F] E →+* S ⊗[F] E :=
      (Algebra.TensorProduct.map f.hom (AlgHom.id F E)).toRingHom
    let σ₁ := (quadraticTensorInvolution F E R).toRingEquiv
    let σ₂ := (quadraticTensorInvolution F E S).toRingEquiv
    change hyperbolicDual (Matrix.SpecialLinearGroup.map σ₂.toRingHom
      (Matrix.SpecialLinearGroup.map φ g)) = Matrix.SpecialLinearGroup.map φ
        (hyperbolicDual (Matrix.SpecialLinearGroup.map σ₁.toRingHom g))
    rw [← hyperbolicDual_map]
    congr 1
    apply Subtype.ext
    ext i j
    change σ₂ (φ (g.val i j)) = φ (σ₁ (g.val i j))
    generalize g.val i j = z
    induction z using TensorProduct.inductionOn with
    | tmul x y => rfl
    | add x y hx hy => simp only [map_add, hx, hy]

set_option backward.isDefEq.respectTransparency false in
private theorem equalizerClosedSubgroup {k : Type u} [Field k] (A : AffineAlgebraicGroup k)
    (f g : A.val ⟶ A.val) :
    ∃ S : ClosedSubgroup A.val,
      RepresentsSubgroup S (fun _ x => x ≫ f.hom.hom = x ≫ g.hom.hom) := by
  let G := Grp.forget (SchemeOver k)
  let e := PreservesEqualizer.iso G f g
  let i := equalizer.ι f g
  have hi : e.inv ≫ i.hom.hom = equalizer.ι (G.map f) (G.map g) :=
    PreservesEqualizer.iso_inv_ι G f g
  have hi' : i.hom.hom = e.hom ≫ equalizer.ι (G.map f) (G.map g) := by
    rw [← hi, e.hom_inv_id_assoc]
  have hc : IsClosedImmersion i.hom.hom.left := by
    letI := A.property.1
    letI : IsAffineHom A.val.X.hom := inferInstance
    letI : IsSeparated (G.obj A.val).hom := inferInstanceAs (IsSeparated A.val.X.hom)
    letI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
    letI : IsClosedImmersion (equalizer.ι (G.map f) (G.map g)).left :=
      isClosedImmersion_equalizer_ι_left (G.map f) (G.map g)
    rw [hi', Over.comp_left]
    exact IsClosedImmersion.comp _ _
  refine ⟨⟨equalizer f g, i, hc⟩, fun X x => ?_⟩
  change x ≫ f.hom.hom = x ≫ g.hom.hom ↔ ∃ s, s ≫ i.hom.hom = x
  constructor
  · intro h
    refine ⟨equalizer.lift x h ≫ e.inv, ?_⟩
    rw [Category.assoc, hi]
    exact equalizer.lift_ι _ _
  · rintro ⟨s, rfl⟩
    have h := congrArg G.map (equalizer.condition f g)
    simp only [Functor.map_comp] at h
    change i.hom.hom ≫ f.hom.hom = i.hom.hom ≫ g.hom.hom at h
    simpa only [Category.assoc] using congrArg (s ≫ ·) h

set_option backward.isDefEq.respectTransparency false in
theorem hyperbolicUnitaryModel : HyperbolicUnitaryModel.{u} := by
  intro F E _ _ _ _ _
  letI : FiniteDimensional F E := .of_finrank_pos
    (Algebra.IsQuadraticExtension.finrank_eq_two F E ▸ Nat.zero_lt_succ 1)
  let A := StandardGroups.specialLinearGroup E (ULift.{u} (Fin 3))
  let W := LinearAlgebraicGroups.WeilRestriction.groupRepresentation F E A
  let m := W.2 ≪≫ Functor.isoWhiskerLeft (extendScalars F E) (specialLinearThreePointIso E)
  let d := unitaryMatrixOperator F E
  obtain ⟨s, hs⟩ := (groupHomComparison F W.1.val W.1.val W.1.property.1).2
    (m.hom ≫ d ≫ m.inv)
  have hmatrix (R : TestAlgebra F) (x : GroupPoints W.1.val R) :
      m.hom.app R (x ≫ s.hom.hom) =
        unitaryDescentOperator (quadraticTensorInvolution F E R).toRingEquiv (m.hom.app R x) := by
    have he := congrArg (fun n => n.app R x) hs
    change x ≫ s.hom.hom = m.inv.app R (d.app R (m.hom.app R x)) at he
    rw [he]
    exact GrpCat.hom_inv_apply (m.app R) _
  obtain ⟨U, hU⟩ := equalizerClosedSubgroup W.1 s (𝟙 W.1.val)
  have hinj (R : TestAlgebra F) :
      Function.Injective (fun x : GroupPoints W.1.val R => m.hom.app R x) :=
    Function.LeftInverse.injective (GrpCat.inv_hom_apply (m.app R))
  refine ⟨W.1, U, m, fun R g => ?_⟩
  dsimp only
  let x : GroupPoints W.1.val R := m.inv.app R g
  have hx : m.hom.app R x = g := GrpCat.hom_inv_apply (m.app R) g
  rw [← hx]
  rw [← hyperbolicFixedEquation, ← hmatrix]
  constructor
  · intro h
    have he : x ≫ s.hom.hom = x ≫ (𝟙 W.1.val : W.1.val ⟶ W.1.val).hom.hom := by
      rw [Grp.id_hom_hom, Category.comp_id]
      exact hinj R h
    obtain ⟨y, hy⟩ := (hU _ _).mp he
    exact ⟨y, congrArg (fun z => m.hom.app R z) hy⟩
  · rintro ⟨y, hy⟩
    have he := hinj R hy
    have h := (hU _ x).mpr ⟨y, he⟩
    rw [Grp.id_hom_hom, Category.comp_id] at h
    exact congrArg (fun z => m.hom.app R z) h

private theorem unitaryFirstProjection_tmul {F E : Type u} [Field F] [Field E] [Algebra F E]
    (R : TestAlgebra E) (x : (restrictTestAlgebra F E).obj R) (y : E) :
    unitaryFirstProjection (F := F) R (x ⊗ₜ[F] y) = x * algebraMap E R y := rfl

private theorem unitaryFirstProjection_natural {F E : Type u} [Field F] [Field E] [Algebra F E]
    {R S : TestAlgebra E} (a : R ⟶ S) :
    (unitaryFirstProjection (F := F) S).comp
        (Algebra.TensorProduct.map ((restrictTestAlgebra F E).map a).hom (AlgHom.id F E)).toRingHom =
      a.hom.toRingHom.comp (unitaryFirstProjection (F := F) R) := by
  apply RingHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      change unitaryFirstProjection (F := F) S (a.hom x ⊗ₜ[F] y) =
        a.hom (unitaryFirstProjection (F := F) R (x ⊗ₜ[F] y))
      rw [unitaryFirstProjection_tmul, unitaryFirstProjection_tmul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

section SplitUnitaryScheme

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
  {W : AffineAlgebraicGroup F} (U : ClosedSubgroup W.val)
  (m : (groupPointsFunctor F).obj W.val ≅ extendScalars F E ⋙ specialLinearThreePoints E)

private def unitaryBaseChangeMatrix (R : TestAlgebra E) :
    GroupPoints ((groupBaseChange F E).obj U.group) R →* SL₃ (((restrictTestAlgebra F E).obj R) ⊗[F] E) :=
  let R₀ := (restrictTestAlgebra F E).obj R
  (m.hom.app R₀).hom.comp ((((groupPointsFunctor F).map U.inclusion).app R₀).hom.comp
    (baseChangePointGroupEquiv E U.group R).toMonoidHom)

set_option backward.isDefEq.respectTransparency false in
private def unitarySplitPointMap : (groupPointsFunctor E).obj ((groupBaseChange F E).obj U.group) ⟶
    specialLinearThreePoints E where
  app R := GrpCat.ofHom ((Matrix.SpecialLinearGroup.map (unitaryFirstProjection (F := F) R)).comp
    (unitaryBaseChangeMatrix U m R))
  naturality {R S} a := by
    apply GrpCat.ext
    intro x
    let R₀ := (restrictTestAlgebra F E).obj R
    let S₀ := (restrictTestAlgebra F E).obj S
    let f := (restrictTestAlgebra F E).map a
    let φ := (Algebra.TensorProduct.map f.hom (AlgHom.id F E)).toRingHom
    let b := baseChangePoint F E U.group.X R x ≫ U.inclusion.hom.hom
    let z := m.hom.app R₀ b
    have h := baseChangePointsNaturality F E U.group.X a x
    have hz := m.hom.naturality_apply f b
    change m.hom.app S₀ (mapPoints f b) = Matrix.SpecialLinearGroup.map φ z at hz
    change Matrix.SpecialLinearGroup.map (unitaryFirstProjection (F := F) S)
      (m.hom.app S₀ (baseChangePoint F E U.group.X S (mapPoints a x) ≫ U.inclusion.hom.hom)) =
      Matrix.SpecialLinearGroup.map a.hom.toRingHom
        (Matrix.SpecialLinearGroup.map (unitaryFirstProjection (F := F) R) z)
    rw [h]
    change Matrix.SpecialLinearGroup.map (unitaryFirstProjection (F := F) S)
      (m.hom.app S₀ (mapPoints f b)) = _
    rw [hz]
    apply Subtype.ext
    ext i j
    exact DFunLike.congr_fun (unitaryFirstProjection_natural (F := F) a) (z.val i j)

set_option backward.isDefEq.respectTransparency false in
private theorem unitarySplitPointMap_bijective (h : RepresentsHyperbolicUnitary (E := E) U m)
    (R : TestAlgebra E) : Function.Bijective ((unitarySplitPointMap U m).app R) := by
  let R₀ := (restrictTestAlgebra F E).obj R
  letI : Algebra E R₀ := inferInstanceAs (Algebra E R)
  letI : IsScalarTower F E R₀ := IsScalarTower.of_algebraMap_eq' rfl
  let σ := (quadraticTensorInvolution F E R₀).toRingEquiv
  obtain ⟨a, ha, hswap⟩ := unitaryScalarSplitting F E R₀
  obtain ⟨M, hM, f, hf, _⟩ := splitUnitaryPoints F E R₀ a hswap
  have hfst : (RingHom.fst R₀ R₀).comp a.toRingEquiv.toRingHom = unitaryFirstProjection (F := F) R := by
    apply RingHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
        change (a (x ⊗ₜ[F] y)).1 = unitaryFirstProjection (F := F) R (x ⊗ₜ[F] y)
        rw [ha, unitaryFirstProjection_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  let b := baseChangePointGroupEquiv E U.group R
  let q := unitaryBaseChangeMatrix U m R
  let j (x : GroupPoints ((groupBaseChange F E).obj U.group) R) : M :=
    ⟨q x, (hM _).mpr ((hyperbolicFixedEquation σ _).mpr ((h R₀ _).mpr ⟨b x, rfl⟩))⟩
  have hj : Function.Bijective j := by
    constructor
    · intro x y hxy
      have he : q x = q y := congrArg Subtype.val hxy
      letI := U.isClosedImmersion
      letI : Mono U.inclusion.hom.hom := Over.mono_of_mono_left _
      have hi : Function.Injective (fun p : GroupPoints W.val R₀ => m.hom.app R₀ p) :=
        Function.LeftInverse.injective (GrpCat.inv_hom_apply (m.app R₀))
      apply b.injective
      exact (cancel_mono U.inclusion.hom.hom).mp (hi he)
    · intro g
      obtain ⟨p, hp⟩ := (h R₀ g.val).mp
        ((hyperbolicFixedEquation σ _).mp ((hM _).mp g.property))
      obtain ⟨x, hx⟩ := b.surjective p
      refine ⟨x, Subtype.ext ?_⟩
      change m.hom.app R₀ (b x ≫ U.inclusion.hom.hom) = g.val
      rw [hx]
      exact hp
  have hu : ⇑((unitarySplitPointMap U m).app R) = f ∘ j := by
    funext x
    change Matrix.SpecialLinearGroup.map (unitaryFirstProjection (F := F) R) (q x) = f (j x)
    rw [hf, hfst]
  rw [hu]
  exact f.bijective.comp hj

end SplitUnitaryScheme

set_option backward.isDefEq.respectTransparency false in
theorem hyperbolicUnitaryBaseChange : HyperbolicUnitaryBaseChange.{u} := by
  intro F E _ _ _ _ _ W U m hm A a
  let X := (groupBaseChange F E).obj U.group
  let W₀ := Specs.Unipotent.closedSubgroupAlgebraicGroup U
  have hX : IsAffine X.X.left := (Specs.Unipotent.baseChangedAlgebraicGroup E W₀).property.1
  let P := groupPointsFunctor E
  let q := unitarySplitPointMap U m
  let i : P.obj X ≅ specialLinearThreePoints E := NatIso.ofComponents
    (fun R => MulEquiv.toGrpIso (MulEquiv.ofBijective (q.app R).hom (unitarySplitPointMap_bijective U m hm R)))
    (fun f => q.naturality f)
  let j := i ≪≫ a.symm
  obtain ⟨f, hf⟩ := (groupHomComparison E X A.val hX).2 j.hom
  obtain ⟨g, hg⟩ := (groupHomComparison E A.val X A.property.1).2 j.inv
  change P.map f = j.hom at hf
  change P.map g = j.inv at hg
  have hi : f ≫ g = 𝟙 X := by
    apply (groupHomComparison E X X hX).1
    change P.map (f ≫ g) = P.map (𝟙 X)
    rw [Functor.map_comp, hf, hg, Iso.hom_inv_id]
    exact (P.map_id X).symm
  have hj : g ≫ f = 𝟙 A.val := by
    apply (groupHomComparison E A.val A.val A.property.1).1
    change P.map (g ≫ f) = P.map (𝟙 A.val)
    rw [Functor.map_comp, hg, hf, Iso.inv_hom_id]
    exact (P.map_id A.val).symm
  refine ⟨⟨f, g, hi, hj⟩, fun R x => ?_⟩
  change a.hom.app R ((P.map f).app R x) = q.app R x
  rw [hf]
  exact GrpCat.hom_inv_apply (a.app R) (q.app R x)

set_option backward.isDefEq.respectTransparency false in
theorem hyperbolicUnitaryRationalPoints : HyperbolicUnitaryRationalPoints.{u} := by
  intro F E _ _ _ _ _ W U m hm
  let R := CommAlgCat.of F F
  let ψ := Algebra.TensorProduct.lid F E
  let σ := Specs.UnitaryRankOne.quadraticConjugation F E
  let τ := (quadraticTensorInvolution F E F).toRingEquiv
  let e := slRingEquiv ψ.toRingEquiv
  have hσ (z : F ⊗[F] E) : ψ (τ z) = σ (ψ z) := by
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
        change ψ ((quadraticTensorInvolution F E F) (a ⊗ₜ[F] b)) = σ (ψ (a ⊗ₜ[F] b))
        rw [quadraticTensorInvolution, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
        change ψ (a ⊗ₜ[F] σ b) = σ (ψ (a ⊗ₜ[F] b))
        simp only [ψ, Algebra.TensorProduct.lid_tmul, Algebra.smul_def, map_mul, σ.commutes]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hcomm (g : SL₃ (F ⊗[F] E)) :
      e (unitaryDescentOperator τ g) = unitaryDescentOperator σ.toRingEquiv (e g) := by
    change Matrix.SpecialLinearGroup.map ψ.toRingEquiv.toRingHom
      (hyperbolicDual (Matrix.SpecialLinearGroup.map τ.toRingHom g)) =
      hyperbolicDual (Matrix.SpecialLinearGroup.map σ.toRingEquiv.toRingHom
        (Matrix.SpecialLinearGroup.map ψ.toRingEquiv.toRingHom g))
    rw [← hyperbolicDual_map]
    congr 1
    apply Subtype.ext
    ext i j
    exact hσ (g.val i j)
  let f : GroupPoints U.group R →* SL₃ E := e.toMonoidHom.comp
    ((m.hom.app R).hom.comp (((groupPointsFunctor F).map U.inclusion).app R).hom)
  have hf : Function.Injective f := by
    intro a b hab
    letI := U.isClosedImmersion
    letI : Mono U.inclusion.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono U.inclusion.hom.hom).mp
    exact Function.LeftInverse.injective (GrpCat.inv_hom_apply (m.app R)) (e.injective hab)
  refine ⟨f.range, MonoidHom.ofInjective hf, ?_, fun _ => rfl⟩
  intro g
  constructor
  · rintro ⟨p, rfl⟩
    let a : SL₃ (F ⊗[F] E) := m.hom.app R (p ≫ U.inclusion.hom.hom)
    have hfix := (hyperbolicFixedEquation τ a).mpr ((hm R a).mpr ⟨p, rfl⟩)
    exact (unitaryDescentFixedPoints σ (e a)).mp ((hcomm a).symm.trans (congrArg e hfix))
  · intro hg
    let a := e.symm g
    have hfix : unitaryDescentOperator τ a = a := by
      apply e.injective
      rw [hcomm, e.apply_symm_apply]
      exact (unitaryDescentFixedPoints σ g).mpr hg
    obtain ⟨p, hp⟩ := (hm R a).mp ((hyperbolicFixedEquation τ a).mp hfix)
    refine ⟨p, ?_⟩
    exact (congrArg e hp).trans (e.apply_symm_apply g)

end UnitaryScheme

section OrbitAssembly

open CategoryTheory.Limits
open Specs.AbstractPairing (Root)
open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricRadicals (IsReductive IsSemisimple IsSplitTorus IsTorus baseChangedSubgroup)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.Pinning (AttachedDatum)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private maximal_of_square from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private isTorus_of_split from LinearAlgebraicGroups.RootData.CharacterPairing
open private cocharacter_ext_units from LinearAlgebraicGroups.RootData.RankOneFlag

private theorem geometricallyMaximalOfIso {k : Type u} [Field k]
    {G H : GroupScheme k} (g : G ≅ H) (S : ClosedSubgroup G) (T : ClosedSubgroup H)
    (f : S.group ≅ T.group) (hf : f.hom ≫ T.inclusion = S.inclusion ≫ g.hom)
    (hS : IsGeometricallyMaximal S) : IsGeometricallyMaximal T := by
  let E := AlgebraicClosure k
  let C := groupBaseChange k E
  obtain ⟨hc, hm⟩ := hS
  let hc' := baseChangeClosedSubgroup k E T.inclusion T.isClosedImmersion
  refine ⟨hc', maximal_of_square (C.mapIso g)
    (baseChangedSubgroup E S hc) (baseChangedSubgroup E T hc') (C.mapIso f) ?_ hm⟩
  change C.map f.hom ≫ C.map T.inclusion = C.map S.inclusion ≫ C.map g.hom
  rw [← C.map_comp, hf, C.map_comp]

private theorem sameIntersectionIso {k : Type u} [Field k] {G T H : GroupScheme k}
    {t : T ⟶ G} {h : H ⟶ G} {S₁ S₂ : ClosedSubgroup H}
    {i₁ : S₁.group ⟶ T} {i₂ : S₂.group ⟶ T}
    (p₁ : IsPullback i₁ S₁.inclusion t h) (p₂ : IsPullback i₂ S₂.inclusion t h) :
    ∃ f : S₁.group ≅ S₂.group, f.hom ≫ S₂.inclusion = S₁.inclusion := by
  let f := p₂.lift i₁ S₁.inclusion p₁.w
  let g := p₁.lift i₂ S₂.inclusion p₂.w
  have hf : f ≫ S₂.inclusion = S₁.inclusion := p₂.lift_snd _ _ _
  have hg : g ≫ S₁.inclusion = S₂.inclusion := p₁.lift_snd _ _ _
  letI := closedSubgroup_mono S₁
  letI := closedSubgroup_mono S₂
  refine ⟨⟨f, g, (cancel_mono S₁.inclusion).mp ?_, (cancel_mono S₂.inclusion).mp ?_⟩, hf⟩
  · rw [Category.assoc, hg, hf, Category.id_comp]
  · rw [Category.assoc, hf, hg, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
theorem rationalStandardFaceExists : RationalStandardFaceExists.{u} := by
  intro F K _ _ _ _ _ G T B P D e ω hG hT hmax hss hsc he hω I
  letI := D.comm
  intro hI hstable
  obtain ⟨c, hc, L, H, Lk, hP, hB, hL, hH, hHss, hLk, j, hj, hHc, hDk, _⟩ :=
    rationalFaceDerivedLevi G T B P D e ω hG hT hmax he hω I hI hstable
  obtain ⟨V, i, hp, hi, htor, hmaxV, hs⟩ := rationalDerivedLeviTorus G T hT hmax c L hL H hH
  let C := groupBaseChange F K
  let Hk := baseChangedSubgroup K H hHc
  let H' := subgroupAlongIso j Hk
  have hH' : Specs.SchemeDerivedGroup.IsDerivedSubgroup H' := derivedSubgroupOfIso j Hk hDk
  have hiK : IsClosedImmersion (C.map V.inclusion).hom.hom.left :=
    baseChangeClosedSubgroup F K V.inclusion V.isClosedImmersion
  let Vk := baseChangedSubgroup K V hiK
  have hpK := baseChangeSubgroupPullback F K hp
  have hj' : C.map (H.inclusion ≫ L.centralizer.inclusion) =
      H'.inclusion ≫ Lk.centralizer.inclusion := by
    change C.map (H.inclusion ≫ L.centralizer.inclusion) =
      (C.map H.inclusion ≫ j.hom) ≫ Lk.centralizer.inclusion
    rw [Category.assoc, hj, C.map_comp]
  rw [hj'] at hpK
  have hpk₀ : IsPullback (C.map i) (C.map V.inclusion) P.pair.T.inclusion
      ((C.map H.inclusion ≫ j.hom) ≫ Lk.centralizer.inclusion) := hpK
  have himage := cocharacterSpanForDerivedIntersection D hss hsc I hI
    (e.hom ≫ C.map c) Lk hLk Hk hDk j (C.map i) (C.map V.inclusion)
    (by rw [← Category.assoc]; exact hpk₀)
  obtain ⟨_, hsaturated⟩ := faceCorootSpan P.pair D hss hsc I hI
  have hsat (y : D.toBased.Y) :
      y ∈ Submodule.span ℤ (D.datum.rootDatum.coroot '' I) ↔
        ∃ n : ℕ, n ≠ 0 ∧ n • y ∈ Submodule.span ℤ (D.datum.rootDatum.coroot '' I) := by
    exact ⟨fun hy => ⟨1, one_ne_zero, by simpa only [one_smul] using hy⟩,
      fun ⟨n, hn, hy⟩ => hsaturated y n hn hy⟩
  obtain ⟨Tₗ, t, J, hJ, hcentral, _, _, hred, ht, hTm, _, hroots⟩ := hLk
  obtain ⟨W, w, hw, _, _, hW, _⟩ := rationalDerivedLeviTorus P.pair.G P.pair.T
    (isTorus_of_split P.split) P.maximal (e.hom ≫ C.map c) Lk hred H' hH'
  have hpk : IsPullback (C.map i) Vk.inclusion P.pair.T.inclusion
      (H'.inclusion ≫ Lk.centralizer.inclusion) := hpK
  obtain ⟨f, hf⟩ := sameIntersectionIso (S₁ := W) (S₂ := Vk) hw hpk
  have hmaxK : IsGeometricallyMaximal Vk :=
    geometricallyMaximalOfIso (Iso.refl _) W Vk f (by simpa only [Iso.refl_hom, Category.comp_id] using hf) hW
  refine ⟨{ simple := hI
            scalar := e
            cocharacter := c
            limit := L
            parabolic := hP
            containsBorel := hB
            reductive := hL
            derived := H
            isDerived := hH
            semisimple := hHss
            torus := V
            torusMap := i
            torusClosed := hi
            intersection := hp
            isTorus := htor
            maximal := hmaxV
            splitClosed := hiK
            splitMaximal := hmaxK
            splitTorus := hs K P.split
            integralImage := himage
            saturatedImage := fun y => (himage y).trans (hsat y)
            hasFace := hc
            splitLimit := Lk
            comparison := j
            comparisonSquare := hj
            kernelTorus := J
            kernel := hJ
            splitCentralizer := hcentral
            splitReductive := hred
            splitLeviTorus := Tₗ
            splitLeviTorusIso := t
            splitLeviTorusSquare := ht
            splitLeviTorusMaximal := hTm
            splitLeviRoots := hroots
            splitDerivedClosed := hHc
            splitIsDerived := hH'
            splitIntersection := hpk }, rfl⟩

open QuasiSplitOrbitTorusProduct
  (cocharacterCoefficientAction orbitTorusProductOnCocharacters)
open Specs.QuasiSplitOrbitTorusProduct
  (CocharacterTransport cocharacterPushforward OrbitTorusDecomposition)

private theorem orbitRoots_eq_fiber {F K : Type u} [Field F] [Field K] [Algebra F K]
    {G : AffineAlgebraicGroup F} {T B : ClosedSubgroup G.val}
    {P : SplitPairOver (K := K) G T B}
    (D : AttachedDatum P.pair) (ω : Gal(K/F) →* Aut D.toBased) :
    letI := D.comm
    let ρ : Gal(K/F) →* Equiv.Perm D.base.support := (simplePermutation D).comp ω
    letI : MulAction Gal(K/F) D.base.support := MulAction.compHom D.base.support ρ
    let q := Quotient.mk (MulAction.orbitRel Gal(K/F) D.base.support)
    ∀ i : D.base.support, Subtype.val '' {j | q j = q i} = orbitRootSet D ω i := by
  letI := D.comm
  let ρ : Gal(K/F) →* Equiv.Perm D.base.support := (simplePermutation D).comp ω
  letI : MulAction Gal(K/F) D.base.support := MulAction.compHom D.base.support ρ
  let q := Quotient.mk (MulAction.orbitRel Gal(K/F) D.base.support)
  change ∀ i : D.base.support, Subtype.val '' {j | q j = q i} = Subtype.val '' diagramOrbit ρ i
  intro i
  congr 1
  ext j
  exact Quotient.eq.trans MulAction.orbitRel_apply

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
theorem rationalOrbitTorusProduct : RationalOrbitTorusProduct.{u} := by
  intro F K _ _ _ _ _ G T B P D e ω hG hT hmax hss hsc he hω
  letI := D.comm
  letI : Finite (Root P.pair.T) := D.datum.finiteRoots
  letI : Fintype D.base.support := Fintype.ofFinite _
  let ρ : Gal(K/F) →* Equiv.Perm D.base.support := (simplePermutation D).comp ω
  letI : MulAction Gal(K/F) D.base.support := MulAction.compHom D.base.support ρ
  let O := MulAction.orbitRel.Quotient Gal(K/F) D.base.support
  let q : D.base.support → O := Quotient.mk (MulAction.orbitRel Gal(K/F) D.base.support)
  let I (o : O) : Set (Root P.pair.T) := Subtype.val '' {i | q i = o}
  have existsFace (o : O) : ∃ L : RationalStandardFace D (I o), L.scalar = e := by
    obtain ⟨i, rfl⟩ := Quotient.exists_rep o
    have hI : I (q i) = orbitRootSet D ω i := orbitRoots_eq_fiber D ω i
    rw [hI]
    obtain ⟨hs, hstable⟩ := orbitRootStability D ω i
    exact rationalStandardFaceExists G T B P D e ω hG hT hmax hss hsc he hω _ hs hstable
  choose L hL using existsFace
  obtain ⟨b, hb⟩ := attachedCorootBasis P.pair D hss hsc
  let A := closedSubgroupAlgebraicGroup T
  have hA : IsSplitTorus ((groupBaseChange F K).obj A.val) := P.split
  obtain ⟨hcomm, hdecomp⟩ := orbitTorusProductOnCocharacters (K := K) ρ A hA
  letI : IsCommMonObj ((groupBaseChange F K).obj T.group).X := hcomm
  obtain ⟨m, hm, htransport, _⟩ := cocharacterCoefficientAction (F := F) (K := K)
  have hme : m = e := by
    apply Iso.ext
    apply cocharacter_ext_units
    intro R t
    apply (baseChangePoints F K _ R).1
    exact (hm R t).trans (he R t).symm
  have hperm (σ : Gal(K/F)) (i : D.base.support) :
      CocharacterTransport T.group σ (b i).toMul (b (ρ σ i)).toMul := by
    apply (htransport T.group σ _ _).mpr
    rw [hme, hb i, hb (ρ σ i)]
    have h := hω σ⁻¹ (D.datum.rootDatum.coroot (ρ σ i).val)
    dsimp only at h
    rw [attachedCorootPermutation D (ω σ⁻¹) (ρ σ i), inv_inv] at h
    change fieldConjugation σ _ ≫
        (e.inv ≫ (D.datum.rootDatum.coroot (ρ σ⁻¹ (ρ σ i)).val).toMul).hom.hom.left =
      (e.inv ≫ (D.datum.rootDatum.coroot (ρ σ i).val).toMul).hom.hom.left ≫
        fieldConjugation σ T.group at h
    rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one, Equiv.Perm.one_apply] at h
    exact h
  let S (o : O) := (L o).embeddedTorus D
  obtain ⟨hcommS, hprod⟩ := hdecomp b hperm S (fun o => (L o).isTorus)
  have hspan (o : O) :
      letI := hcommS o
      let j := Specs.QuasiSplitOrbitTorusProduct.cocharacterPushforward (K := K) (S o).inclusion
      Function.Injective j ∧ LinearMap.range j = Submodule.span ℤ (b '' {i | q i = o}) := by
    dsimp only
    letI := hcommS o
    let j := Specs.QuasiSplitOrbitTorusProduct.cocharacterPushforward (K := K) (S o).inclusion
    have hmono := closedSubgroup_mono (baseChangedSubgroup K (S o)
      (baseChangeClosedSubgroup F K (S o).inclusion (S o).isClosedImmersion))
    letI : Mono ((groupBaseChange F K).map (S o).inclusion) := hmono
    have hset :
        D.datum.rootDatum.coroot '' I o = b '' {i | q i = o} := by
      rw [Set.image_image]
      congr 1
      funext i
      exact (hb i).symm
    refine ⟨fun x y h => Additive.toMul.injective ((cancel_mono
      ((groupBaseChange F K).map (S o).inclusion)).mp (congrArg Additive.toMul h)), ?_⟩
    ext y
    change (∃ x, j x = y) ↔ y ∈ Submodule.span ℤ (b '' {i | q i = o})
    rw [← hset, ← (L o).integralImage y]
    exact ⟨fun ⟨x, hx⟩ => ⟨x.toMul, congrArg Additive.toMul hx⟩,
      fun ⟨x, hx⟩ => ⟨Additive.ofMul x, Additive.toMul.injective hx⟩⟩
  obtain ⟨_, c, _, hdec⟩ := hprod hspan
  dsimp only
  exact ⟨L, b.map c, c, fun i => congrArg c (hb i), hL, hdec⟩

open Specs.QuasiSplitOrbitDerivedRoots (ActualPinnedAction coefficientAction comparedAction
  diagramRoot diagramSimple pinnedRootMap)
open Specs.Pinning (PinnedGroup SimpleRoot Pinning)
open Specs.RootGroups (AdditiveLine)
open Specs.OrderedRootProducts (RootSubgroupFamily)

private theorem comparedAction_refl {F K : Type u} [Field F] [Field K] [Algebra F K]
    (σ : Gal(K/F)) (X : GroupScheme F) :
    comparedAction σ (Iso.refl ((groupBaseChange F K).obj X)) = fieldConjugation σ X := by
  change (𝟙 _) ≫ coefficientAction σ X ≫ (𝟙 _) = _
  rw [Category.comp_id, Category.id_comp]
  rfl

private theorem diagramCoroot {F K : Type u} [Field F] [Field K] [Algebra F K]
    {G : AffineAlgebraicGroup F} {T B : ClosedSubgroup G.val} {P : SplitPairOver (K := K) G T B}
    (D : AttachedDatum P.pair) (ω : Gal(K/F) →* Aut D.toBased)
    (σ : Gal(K/F)) (α : Root P.pair.T) :
    letI := D.comm
    cocharacterAction D (ω σ) (D.datum.rootDatum.coroot α) =
      D.datum.rootDatum.coroot (diagramRoot ω σ α) := by
  letI := D.comm
  let f := (ω σ).asIso.hom.val
  change f.coweightEquiv.symm (D.toBased.datum.coroot α) =
    D.toBased.datum.coroot (f.indexEquiv α)
  apply f.coweightEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  have h := f.toHom.coroot_coweightMap_apply _ _ (f.indexEquiv α)
  change f.coweightEquiv (D.toBased.datum.coroot (f.indexEquiv α)) =
    D.toBased.datum.coroot (f.indexEquiv.symm (f.indexEquiv α)) at h
  exact (h.trans (congrArg D.toBased.datum.coroot (f.indexEquiv.symm_apply_apply α))).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
theorem rationalFacePinning : RationalFacePinning.{u} := by
  intro F K _ _ _ _ _ G T B N P D pair hG hT hmax A₀ A U p a ω I L hA hstable
  letI := D.comm
  let Q : PinnedGroup A := ⟨P.pair, U, p⟩
  let R := L.rationalFace D pair hG hT hmax
  let m := L.scalar
  have act : ActualPinnedAction R A₀ A a m.symm Q.roots Q.pin ω := by
    refine ⟨hstable, ?_, ?_, ?_⟩
    · intro σ α
      change comparedAction σ⁻¹ (Iso.refl ((groupBaseChange F K).obj T.group)) ≫
        (diagramRoot ω σ α).val.hom.hom.left =
        α.val.hom.hom.left ≫ comparedAction σ⁻¹ m.symm
      rw [comparedAction_refl]
      exact hA.characters σ α
    · intro σ α
      rw [show R.ambientTorusComparison = Iso.refl _ from rfl, comparedAction_refl]
      have h := hA.cocharacters σ (D.datum.rootDatum.coroot α)
      dsimp only at h
      rw [diagramCoroot D ω σ α] at h
      change fieldConjugation σ⁻¹ _ ≫
          (m.inv.hom.hom.left ≫ (D.datum.rootDatum.coroot (diagramRoot ω σ α)).toMul.hom.hom.left) =
        (m.inv.hom.hom.left ≫ (D.datum.rootDatum.coroot α).toMul.hom.hom.left) ≫
          fieldConjugation σ⁻¹ T.group at h
      have hm := congrArg (fun f => f.hom.hom.left) m.hom_inv_id
      change m.hom.hom.hom.left ≫ m.inv.hom.hom.left = 𝟙 _ at hm
      change (m.hom.hom.hom.left ≫ fieldConjugation σ⁻¹ _ ≫ m.inv.hom.hom.left) ≫
          (D.datum.rootDatum.coroot (diagramRoot ω σ α)).toMul.hom.hom.left =
        (D.datum.rootDatum.coroot α).toMul.hom.hom.left ≫ fieldConjugation σ⁻¹ T.group
      rw [Category.assoc, Category.assoc, h]
      simp only [Category.assoc, reassoc_of% hm]
    · intro σ α
      dsimp only
      rw [show R.groupComparison = Iso.refl _ from rfl, comparedAction_refl]
      exact hA.pinning σ α
  obtain ⟨h, Bp, Bn, E, En, β, hop, hsc, hs, hroot, V, p', hp, ha⟩ :=
    QuasiSplitOrbitDerivedRoots.rationalDerivedRootComparison Q D I (L.splitFace D) R a m.symm ω act
  exact ⟨⟨h, Bp, Bn, E, En, β, hop, hsc, hs, hroot, V, p', hp, ha⟩⟩

open Specs.QuasiSplitOrbitAmbientWords (BorelRadical OrbitLevi SplitRadical SplitOrbit)
open _root_.LinearAlgebraicGroups.Specs (IsSchemeKernel)
open Specs.GeometricRadicals (IsUnipotentRadical)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.GeometricBorelConjugacy (IsKBorel)
open Specs.Unipotent (IsFppfGroupQuotient)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.StandardParabolicLevi (leviRoots)
open Specs.RootGroups (IsRootSubgroup)
open Specs.CharacterPairing (pairing)
open private isTorus_iff_coordinates from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private torus_multiplicativeType from LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private liftToSchemeKernel from LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel
open private reductive_of_semisimple sameSubgroupIso
  from LinearAlgebraicGroups.Classification.CentralIsogenies
open private compared_borel_ascent attachedBase_regular opposite_roots_of_pullback
  oppositeRoot oppositeRoot_character face_root_pairing
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitDerivedRoots
open private smooth_baseChangedGroup connected_baseChangedGroup radical_of_torus_kernel
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private baseChangeKernelSquare from LinearAlgebraicGroups.Affine.Components
open private exists_weylIdentification from LinearAlgebraicGroups.Classification.TransportedRootCoordinates
open private subgroupOf_trans from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

set_option backward.isDefEq.respectTransparency false in
private theorem borelRadicalAndQuotient {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    (hG : IsReductive G) (T B : ClosedSubgroup G.val) (hTmax : IsGeometricallyMaximal T)
    (hB : Specs.GeometricBorelConjugacy.IsKBorel B) (t : T.group ⟶ B.group)
    (ht : t ≫ B.inclusion = T.inclusion) :
    ∃ (U : ClosedSubgroup B.group) (q : B.group ⟶ T.group),
      IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U ∧ IsSchemeKernel q U ∧
      t ≫ q = 𝟙 T.group := by
  have hclosed : IsClosedImmersion t.hom.hom.left := by
    letI := B.isClosedImmersion
    have hh : t.hom.hom.left ≫ B.inclusion.hom.hom.left = T.inclusion.hom.hom.left :=
      congrArg (fun f => f.hom.hom.left) ht
    haveI : IsClosedImmersion (t.hom.hom.left ≫ B.inclusion.hom.hom.left) := hh ▸ T.isClosedImmersion
    exact IsClosedImmersion.of_comp_isClosedImmersion _ B.inclusion.hom.hom.left
  let V : ClosedSubgroup B.group := ⟨T.group, t, hclosed⟩
  have hmax : IsGeometricallyMaximal (subgroupOfSubgroup B V) := by
    refine geometricallyMaximalOfIso (Iso.refl _) T (subgroupOfSubgroup B V) (Iso.refl _) ?_ hTmax
    change (𝟙 _) ≫ (t ≫ B.inclusion) = T.inclusion ≫ (𝟙 _)
    rw [Category.id_comp, Category.comp_id, ht]
  obtain ⟨U, q, hu, _, hq, hs⟩ := Descent.AdjointBorelCohomology.borelTorusQuotient
    G B hG hB V hmax
  exact ⟨U, q, hu, hq.1, hs⟩

set_option backward.isDefEq.respectTransparency false in
private theorem inducedRadicalInclusion {k : Type u} [Field k]
    {G H : AffineAlgebraicGroup k} {A : ClosedSubgroup G.val} {B : ClosedSubgroup H.val}
    {T : ClosedSubgroup G.val} (hG : IsReductive G) (hT : IsTorus T.group)
    (hmax : IsGeometricallyMaximal T) (hA : Specs.GeometricBorelConjugacy.IsKBorel A)
    (t : T.group ⟶ A.group) (ht : t ≫ A.inclusion = T.inclusion)
    (e : H.val ⟶ G.val) (f : B.group ⟶ A.group) (hf : f ≫ A.inclusion = B.inclusion ≫ e)
    (P : ClosedSubgroup A.group) (hP : IsUnipotentRadical (closedSubgroupAlgebraicGroup A) P)
    (U : ClosedSubgroup B.group) (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U) :
    ∃ j : U.group ⟶ P.group,
      j ≫ P.inclusion ≫ A.inclusion = U.inclusion ≫ B.inclusion ≫ e := by
  obtain ⟨V, q, hV, hq, _⟩ := borelRadicalAndQuotient hG T A hmax hA t ht
  let Q := closedSubgroupAlgebraicGroup T
  have hz : (U.inclusion ≫ f) ≫ q = 0 :=
    LinearAlgebraicGroups.Unipotent.homFromUnipotentToMultiplicativeType
      (closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup B) U)
      Q _ hU.2.1 (torus_multiplicativeType ((isTorus_iff_coordinates Q).mp hT))
  obtain ⟨v, hv⟩ := liftToSchemeKernel hq (U.inclusion ≫ f) hz
  obtain ⟨i, hi, _⟩ := LinearAlgebraicGroups.GeometricRadicals.radicalUnique
    (closedSubgroupAlgebraicGroup A) Specs.Unipotent.IsUnipotent hV hP
  refine ⟨v ≫ i.hom, ?_⟩
  rw [Category.assoc, ← Category.assoc i.hom, hi, ← Category.assoc v, hv, Category.assoc, hf]

set_option backward.isDefEq.respectTransparency false in
private theorem extendBorelRadical {F K : Type u} [Field F] [Field K] [Algebra F K]
    {G : AffineAlgebraicGroup F} (hG : IsReductive G) (T : ClosedSubgroup G.val)
    (hmax : IsGeometricallyMaximal T)
    (hsplit : IsSplitTorus ((groupBaseChange F K).obj T.group)) (B : BorelRadical G)
    (t : T.group ⟶ B.borel.group) (ht : t ≫ B.borel.inclusion = T.inclusion) :
    Nonempty (SplitRadical K B) := by
  let C := groupBaseChange F K
  have hBc := baseChangeClosedSubgroup F K B.borel.inclusion B.borel.isClosedImmersion
  have hUc := baseChangeClosedSubgroup F K B.radical.inclusion B.radical.isClosedImmersion
  let Bk := baseChangedSubgroup K B.borel hBc
  let U := B.radical
  let Uk := baseChangedSubgroup K U hUc
  have hBk : IsKBorel Bk := compared_borel_ascent (H := Specs.Unipotent.baseChangedAlgebraicGroup K G)
    hG B.borel Bk (Iso.refl _) (Iso.refl _) (by
      change (𝟙 _) ≫ C.map B.borel.inclusion = C.map B.borel.inclusion ≫ (𝟙 _)
      rw [Category.id_comp, Category.comp_id]) B.isBorel
  obtain ⟨V, q, hV, hq, _⟩ := borelRadicalAndQuotient hG T B.borel hmax B.isBorel t ht
  obtain ⟨i, hi, _⟩ := LinearAlgebraicGroups.GeometricRadicals.radicalUnique
    (closedSubgroupAlgebraicGroup B.borel) Specs.Unipotent.IsUnipotent hV B.isRadical
  let H := Grp.forget (SchemeOver F)
  have hk : IsSchemeKernel q U := hq.of_iso (H.mapIso i) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      change V.inclusion.hom.hom ≫ (𝟙 _) = i.hom.hom.hom ≫ U.inclusion.hom.hom
      rw [Category.comp_id]
      exact (congrArg (fun f : V.group ⟶ B.borel.group => f.hom.hom) hi).symm)
    (by subsingleton) (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
  have hbase : IsSchemeKernel (C.map q) Uk := baseChangeKernelSquare q U.inclusion hk
  let G₁ := closedSubgroupAlgebraicGroup (G := Specs.Unipotent.baseChangedAlgebraicGroup K G) Bk
  let T₁ := Specs.Unipotent.baseChangedAlgebraicGroup K (closedSubgroupAlgebraicGroup T)
  let V₁ := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup B.borel) U
  have hu₁ : Specs.Unipotent.IsUnipotent (closedSubgroupAlgebraicGroup (G := G₁) Uk) :=
    (LinearAlgebraicGroups.Unipotent.unipotenceFieldExtension V₁).mpr B.isRadical.2.1
  exact ⟨⟨hBc, hUc, hBk, radical_of_torus_kernel (A := G₁) (L := T₁) Uk (C.map q)
    hbase hsplit (smooth_baseChangedGroup B.isRadical.1.1)
    (connected_baseChangedGroup V₁ B.isRadical.1.2.1) hu₁⟩⟩

private theorem rootSubgroupIso {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    {T V W : ClosedSubgroup G.val} (hG : IsReductive G) (hT : IsSplitTorus T.group)
    (hm : IsGeometricallyMaximal T) (α : Root T)
    (hV : IsRootSubgroup T V α.val) (hW : IsRootSubgroup T W α.val) :
    ∃ e : V.group ≅ W.group, e.hom ≫ W.inclusion = V.inclusion := by
  obtain ⟨U, _, _, _, _, h⟩ := (RootData.RootGroups.rootSubgroups G hG T hT hm).2
    α.val α.property |>.2.2
  exact sameSubgroupIso ⟨subgroupOf_trans (h V hV).2 (h W hW).1,
    subgroupOf_trans (h W hW).2 (h V hV).1⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3000000 in
theorem rationalFaceAmbientRadicals : RationalFaceAmbientRadicals.{u} := by
  intro F K _ _ _ G T B P D pair hG hT hmax A₀ A U p a ω I L d
  let R := L.rationalFace D pair hG hT hmax
  let H := R.group
  let E : H.val ⟶ G.val := R.inclusion
  let C := groupBaseChange F K
  let N (s : Bool) : ClosedSubgroup H.val :=
    if s then d.positive.rational else d.negative.rational
  have hN (s : Bool) : Specs.GeometricBorelConjugacy.IsKBorel (N s) := by
    cases s
    · exact d.negative.isKBorel
    · exact d.positive.isKBorel
  let inN (s : Bool) : (N s).group ⟶ (B s).borel.group := by
    cases s
    · exact d.negative.toAmbient
    · exact d.positive.toAmbient
  have hpN (s : Bool) : IsPullback (inN s) (N s).inclusion (B s).borel.inclusion E := by
    cases s
    · exact d.negative.intersection
    · exact d.positive.intersection
  have hH : IsReductive H := reductive_of_semisimple H L.semisimple
  obtain ⟨ip, in', hop, hpos⟩ := d.opposite
  have hneg : in' ≫ d.negative.rational.inclusion = L.torus.inclusion := hop.w.symm.trans hpos
  have rad (s : Bool) :
      ∃ U : ClosedSubgroup (N s).group, IsUnipotentRadical
        (closedSubgroupAlgebraicGroup (N s)) U := by
    cases s
    · obtain ⟨U, _, hu, _⟩ := borelRadicalAndQuotient hH L.torus d.negative.rational
        L.maximal d.negative.isKBorel in' hneg
      exact ⟨U, hu⟩
    · obtain ⟨U, _, hu, _⟩ := borelRadicalAndQuotient hH L.torus d.positive.rational
        L.maximal d.positive.isKBorel ip hpos
      exact ⟨U, hu⟩
  choose V hV using rad
  let hPair (s : Bool) : BorelRadical H := ⟨N s, hN s, V s, hV s⟩
  let t (s : Bool) : T.group ⟶ (B s).borel.group := by
    cases s
    · exact pair.toNegative
    · exact pair.toPositive
  have ht (s : Bool) : t s ≫ (B s).borel.inclusion = T.inclusion := by
    cases s
    · exact pair.intersection.w.symm.trans pair.positiveSquare
    · exact pair.positiveSquare
  let tH (s : Bool) : L.torus.group ⟶ (N s).group := by
    cases s
    · exact in'
    · exact ip
  have htH (s : Bool) : tH s ≫ (N s).inclusion = L.torus.inclusion := by
    cases s
    · exact hneg
    · exact hpos
  let O : OrbitLevi F :=
    { G := G
      reductive := hG
      T := T
      maximal := hmax
      B := B
      ambientTorus := fun s => ⟨t s, ht s⟩
      L := L.limit.centralizer
      deriv := L.derived
      isDerived := L.isDerived
      S := L.torus
      torusMap := L.torusMap
      intersection := L.intersection.map (Grp.forget (SchemeOver F))
      Hpair := hPair
      induced := by
        intro s Y g
        have pb : IsPullback (inN s).hom.hom (N s).inclusion.hom.hom
            (B s).borel.inclusion.hom.hom E.hom.hom :=
          (hpN s).map (Grp.forget (SchemeOver F))
        change (∃ x, x ≫ (N s).inclusion.hom.hom = g) ↔
          ∃ y, y ≫ (B s).borel.inclusion.hom.hom = g ≫ E.hom.hom
        exact ⟨fun ⟨x, hx⟩ => ⟨x ≫ (inN s).hom.hom,
          by rw [Category.assoc, pb.w, ← Category.assoc, hx]⟩,
          fun ⟨y, hy⟩ => ⟨pb.lift y g hy, pb.lift_snd _ _ _⟩⟩ }
  refine ⟨O, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, ?_, ?_⟩
  · intro s
    obtain ⟨j, hj⟩ := inducedRadicalInclusion hG hT hmax (B s).isBorel (t s) (ht s)
      E (inN s) (hpN s).w (B s).radical (B s).isRadical (V s) (hV s)
    refine ⟨j, ?_⟩
    change j ≫ ((B s).radical.inclusion ≫ (B s).borel.inclusion) =
      ((V s).inclusion ≫ (N s).inclusion) ≫ E
    simpa only [Category.assoc] using hj
  let ambient (s : Bool) :=
    (extendBorelRadical (K := K) hG T hmax P.split (B s) (t s) (ht s)).some
  let derived (s : Bool) :=
    (extendBorelRadical (K := K) hH L.torus L.maximal L.splitTorus (hPair s) (tH s) (htH s)).some
  letI := D.comm
  let Epos := d.posDatum
  letI := Epos.comm
  obtain ⟨c, hc, hpositive, hb⟩ := attachedBase_regular D
  let f := Specs.SimpleRoots.evaluate D.datum c
  have hval (α : Root P.pair.T) : f (D.datum.rootDatum.root α) = pairing _ α.val c :=
    (congrArg (fun x => D.datum.rootDatum.toLinearMap x (Additive.ofMul c))
      (D.datum.root_eq α)).trans (D.datum.pairing_eq _ _)
  have hf : Specs.SimpleRoots.positive D.datum.rootDatum f = subgroupRoots P.pair.T (ambient true).borel := by
    ext α
    change 0 < f (D.datum.rootDatum.root α) ↔ α ∈ subgroupRoots P.pair.T P.pair.B
    rw [hval, ← hpositive]
    rfl
  have hneg' : {i | f (D.datum.rootDatum.root i) < 0} =
      subgroupRoots P.pair.T (ambient false).borel := by
    have hp := baseChangeSubgroupPullback F K pair.intersection
    have hsquare : C.map pair.toPositive ≫ (ambient true).borel.inclusion =
        P.pair.T.inclusion := by
      change C.map pair.toPositive ≫ C.map (B true).borel.inclusion = C.map T.inclusion
      rw [← C.map_comp, pair.positiveSquare]
    have hsign := opposite_roots_of_pullback D (ambient false).borel
      (ambient false).isBorel hp hsquare
    ext α
    change f (D.datum.rootDatum.root α) < 0 ↔ α ∈ subgroupRoots P.pair.T (ambient false).borel
    have hp : Specs.SimpleRoots.positive D.datum.rootDatum f = subgroupRoots P.pair.T P.pair.B := hf
    rw [hsign, ← hp]
    change f (D.datum.rootDatum.root α) < 0 ↔
      0 < f (D.datum.rootDatum.root (oppositeRoot D α))
    have hχ : D.datum.rootDatum.root (oppositeRoot D α) =
        - D.datum.rootDatum.root α := by
      rw [D.datum.root_eq, D.datum.root_eq, oppositeRoot_character]
      rfl
    rw [hχ, map_neg, neg_pos]
  obtain ⟨W⟩ := exists_weylIdentification P.pair D
  have he : C.map E = (L.splitFace D).inclusion := by
    change C.map (L.derived.inclusion ≫ L.limit.centralizer.inclusion) =
      (C.map L.derived.inclusion ≫ L.comparison.hom) ≫ L.splitLimit.centralizer.inclusion
    rw [C.map_comp, Category.assoc, L.comparisonSquare]
  have hcor (i : I) : ∃ c : Cocharacter ((groupBaseChange F K).obj O.S.group),
      c ≫ C.map O.torusMap = (D.datum.rootDatum.coroot i.val).toMul :=
    (L.integralImage _).mpr (Submodule.subset_span ⟨i, i.property, rfl⟩)
  choose coroot hcoroot using hcor
  have hRed : IsReductive (Specs.Unipotent.baseChangedAlgebraicGroup K H) := d.reductive
  let S : SplitOrbit O K :=
    { reductive := P.reductive
      hReductive := hRed
      tClosed := P.torusClosed
      sClosed := L.splitClosed
      tSplit := P.split
      sSplit := L.splitTorus
      tMax := P.maximal
      sMax := L.splitMaximal
      ambient := ambient
      derived := derived
      tInBorel := fun s => ⟨C.map (t s), by
        change C.map (t s) ≫ C.map (B s).borel.inclusion = C.map T.inclusion
        rw [← C.map_comp, ht s]⟩
      sInBorel := fun s => ⟨C.map (tH s), by
        change C.map (tH s) ≫ C.map (N s).inclusion = C.map L.torus.inclusion
        rw [← C.map_comp, htH s]⟩
      comm := D.comm
      D := D.datum
      W := W
      positive := f
      base := D.base
      based := hb
      positive_eq := hf
      negative_eq := hneg'
      face := I
      isFace := L.simple
      rootGroups := U
      derivedRootGroups := d.rootGroups
      rootIndex := d.roots.symm
      rootSigns := by
        intro s r
        let α := d.roots.symm r
        have hα : (d.roots α).val = (L.splitFace D).toAmbientTorus ≫ α.val.val := (d.rootComparison α).1
        have hβ : (L.splitFace D).toAmbientTorus ≫ α.val.val ∈
            Specs.CharacterPairing.absoluteRoots (L.splitFace D).torus :=
          hα ▸ (d.roots α).property
        have hp := baseChangeSubgroupPullback F K (hpN s)
        rw [he] at hp
        have hS := QuasiSplitOrbitDerivedRoots.faceBorelRoots D I (L.splitFace D)
          (ambient s).borel (derived s).borel (C.map (inN s)) hp α.val α.property hβ
        have hEq : (⟨_, hβ⟩ : Root (G := (L.splitFace D).group) (L.splitFace D).torus) = r :=
          (Subtype.ext hα.symm : ⟨_, hβ⟩ = d.roots α).trans (d.roots.apply_symm_apply r)
        change r ∈ subgroupRoots (L.splitFace D).torus (derived s).borel ↔
          α.val ∈ subgroupRoots P.pair.T (ambient s).borel
        exact hEq ▸ hS
      rootMatch := by
        intro r
        let α := d.roots.symm r
        obtain ⟨Z, hz, z, hZ⟩ := (d.rootComparison α).2.2.2.2 (U α.val).val (U α.val).property
        have hEq : d.roots α = r := d.roots.apply_symm_apply r
        have hz' : IsRootSubgroup (L.splitFace D).torus Z r.val := hEq ▸ hz
        obtain ⟨j, hj⟩ := rootSubgroupIso d.reductive L.splitTorus L.splitMaximal r
          (d.rootGroups r).property hz'
        refine ⟨j ≪≫ z, ?_⟩
        change (j.hom ≫ z.hom) ≫ (U α.val).val.inclusion =
          (d.rootGroups r).val.inclusion ≫ C.map E
        rw [he, Category.assoc, hZ, ← Category.assoc j.hom, hj]
      corootLift := coroot
      corootMatch := hcoroot }
  exact ⟨S, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem rationalFaceCartanComparison : RationalFaceCartanComparison.{u} := by
  intro F K _ _ _ G T B N P D pair hG hT hmax A₀ A U p a ω I L d
  letI := D.comm
  letI := d.posDatum.comm
  let E := d.posDatum
  let lift (i : I) : ↥(leviRoots D.datum I) :=
    ⟨i.val, Submodule.subset_span ⟨i.val, i.property, rfl⟩⟩
  let f (i : I) : E.base.support :=
    ⟨d.roots (lift i), (d.rootComparison (lift i)).2.2.1.mpr i.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      have e : lift i = lift j := d.roots.injective (congrArg Subtype.val h)
      exact Subtype.ext (congrArg (fun r : ↥(leviRoots D.datum I) => r.val) e)
    · intro j
      obtain ⟨α, hα⟩ := d.roots.surjective j.val
      have h : α.val ∈ I := (d.rootComparison α).2.2.1.mp (hα.symm ▸ j.property)
      exact ⟨⟨α.val, h⟩, Subtype.ext hα⟩
  refine ⟨Equiv.ofBijective f hf, ?_, ?_⟩
  · intro i α h
    exact congrArg d.roots (Subtype.ext h)
  · intro i j
    let t := (E.datum.rootDatum.coroot (d.roots (lift j))).toMul
    calc
      E.datum.rootDatum.toLinearMap (E.datum.rootDatum.root (d.roots (lift i)))
          (Additive.ofMul t) =
          Specs.CharacterPairing.pairing (L.splitFace D).torus.group (d.roots (lift i)).val t :=
        (congrArg (fun x => E.datum.rootDatum.toLinearMap x (Additive.ofMul t))
          (E.datum.root_eq (d.roots (lift i)))).trans (E.datum.pairing_eq _ _)
      _ = Specs.CharacterPairing.pairing (L.splitFace D).torus.group
          ((L.splitFace D).toAmbientTorus ≫ i.val.val) t :=
        congrArg (fun χ => Specs.CharacterPairing.pairing _ χ t) (d.rootComparison (lift i)).1
      _ = D.datum.rootDatum.pairing i.val j.val :=
        (face_root_pairing (L.splitFace D) i.val j.val t (d.rootComparison (lift j)).2.1).symm

open Specs.AbsoluteDynkinTypes (IsAbsolutelyAlmostSimple)
open Specs.GeometricRadicals (GeometricGroup)
open Specs.SimplyConnectedLattice (corootLattice)
open Specs.Pinning (BasedRootDatum BasedIso SplitBorelPair)
open RootData (integralCartan)
open LinearAlgebraicGroups.Classification.IntegralRealization (integralRealization)
open LinearAlgebraicGroups.Classification.SimplyConnectedLattice (latticeCriterion splitCover)
open LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
  (nonemptySimpleRoots disconnectedPartition geometricProductOfBlocks noGeometricProduct)
open private classifyDatum from LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
open private basedIso_base_iff pinnedLift from LinearAlgebraicGroups.Classification.PinnedEquivalence
open private fibreTowerIso realization_corootSpan of_fullCorootLattice
  torusIso_of_isIso centralIsogeny_baseChange centralIsogeny_postIso isIso_of_scalarExtension
  from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private groupBaseChangeTowerIso from LinearAlgebraicGroups.Relative.RationalCocharacter

private def simpleSupportEquiv {D E : BasedRootDatum.{u}} (f : BasedIso D E) :
    D.base.support ≃ E.base.support :=
  f.val.indexEquiv.subtypeEquiv (basedIso_base_iff f)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2500000 in
theorem absoluteClassificationOfSplitPair : AbsoluteClassificationOfSplitPair.{u} := by
  classical
  intro F K _ _ _ _ G T B P D hG hsc
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.freeCharacters
  letI := D.datum.finiteCharacters
  letI := D.datum.freeCocharacters
  letI := D.datum.finiteCocharacters
  letI := D.datum.reduced
  let E := AlgebraicClosure F
  let i : K →ₐ[F] E := IsAlgClosed.lift
  letI : Algebra K E := i.toAlgebra
  letI : IsScalarTower F K E := IsScalarTower.of_algebraMap_eq' i.comp_algebraMap.symm
  let j : (groupBaseChange K E).obj P.pair.G.val ≅ (GeometricGroup G).val :=
    (groupBaseChangeTowerIso (k := F) (K := K) (L := E)).app G.val
  have hss : IsSemisimple P.pair.G :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := K) G hG.1.1 hG.1.2.1).mpr hG.1
  have hY : corootLattice D = ⊤ := by
    obtain ⟨Q, D', f, t, hs, _, hf, ht, _, b, hb⟩ :=
      splitCover P.pair.G hss P.pair.T P.split P.maximal D.datum
    letI := D'.comm
    have hs' : IsSemisimple (Specs.Unipotent.baseChangedAlgebraicGroup E Q.G) :=
      (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := E) Q.G hs.1 hs.2.1).mpr hs
    letI : IsIso ((groupBaseChange K E).map f ≫ j.hom) := hsc _ hs' _
      (centralIsogeny_postIso j (centralIsogeny_baseChange E Q f hf))
    letI : IsIso f := isIso_of_scalarExtension E f (IsIso.of_isIso_comp_right _ j.hom)
    letI : IsIso t := torusIso_of_isIso Q P.pair f t ht
    apply top_unique
    intro y _
    have hy := (b (Additive.ofMul (y.toMul ≫ inv t))).property
    rw [hb, Category.assoc, IsIso.inv_hom_id, Category.comp_id] at hy
    exact hy
  refine ⟨hss, (latticeCriterion P.pair.G hss P.pair.T P.split P.maximal D.datum).mpr hY, ?_⟩
  obtain ⟨W⟩ := exists_weylIdentification P.pair D
  apply classifyDatum D W hY
  obtain ⟨M⟩ := integralRealization D.toBased
  obtain ⟨Ak, Mk, ek, _, _, _, _, _, _⟩ := M.fieldFibre K
  obtain ⟨Uk, ⟨pk⟩⟩ := Classification.Pinning.pinningsExist Ak P.pair
  let Qk : PinnedGroup Ak := ⟨P.pair, Uk, pk⟩
  let gk : D.toBased ⟶ Mk.attached.toBased := Mk.datumIso
  obtain ⟨qk, _⟩ := pinnedLift Mk.pinned Qk Mk.attached D (asIso gk).inv
  obtain ⟨Ae, Me, ee, _, _, _, _, _, _⟩ := M.fieldFibre E
  let P' := Me.pinned.pair
  let E' := Me.attached
  letI := E'.comm
  let kIso : P'.G.val ≅ (GeometricGroup G).val :=
    ee.symm ≪≫ (fibreTowerIso K E).app M.group ≪≫
      (groupBaseChange K E).mapIso (ek ≪≫ qk.group) ≪≫ j
  have hY' : corootLattice E' = ⊤ := realization_corootSpan Me hY
  have hn' : ¬ IsZero P'.G.val := fun h => hG.2.1 (h.of_iso kIso.symm)
  let v : D.base.support ≃ E'.base.support := simpleSupportEquiv Me.datumIso
  have hv (x y : D.base.support) :
      integralCartan D.datum.rootDatum D.base x y =
        integralCartan E'.datum.rootDatum E'.base (v x) (v y) :=
    (Me.datumIso.val.toHom.pairing (i := y.val) (j := x.val)).symm
  have hn : Nonempty D.base.support := (nonemptySimpleRoots P' E' hY' hn').map v.symm
  by_contra hc
  obtain ⟨S, ⟨x, hx⟩, ⟨y, hy⟩, hS⟩ := disconnectedPartition D.datum.rootDatum D.base hn hc
  have hy' : v y ∉ v '' S := by
    rintro ⟨z, hz, he⟩
    exact hy (v.injective he ▸ hz)
  have hCross : ∀ a ∈ v '' S, ∀ b ∉ v '' S,
      integralCartan E'.datum.rootDatum E'.base a b = 0 ∧
        integralCartan E'.datum.rootDatum E'.base b a = 0 := by
    rintro a ⟨a', ha, rfl⟩ b hb
    obtain ⟨b', rfl⟩ := v.surjective b
    obtain ⟨h₁, h₂⟩ := hS a' ha b' (fun h => hb ⟨b', h, rfl⟩)
    exact ⟨(hv a' b').symm.trans h₁, (hv b' a').symm.trans h₂⟩
  obtain ⟨H, J, hH, hJ, hnH, hnJ, ⟨g⟩⟩ :=
    geometricProductOfBlocks P' E' hY' (v '' S) ⟨v x, ⟨x, hx, rfl⟩⟩ ⟨v y, hy'⟩ hCross
  exact (noGeometricProduct G hG H J hH hJ hnH hnJ).false (kIso.symm ≪≫ g)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
theorem rationalOrbitLeviStructure : RationalOrbitLeviStructure.{u} := by
  intro F K _ _ _ _ _ G T B P D pair hG hT hmax habs hsc A₀ A U p a m ω hm hA
  letI := D.comm
  letI := D.datum.finiteRoots
  let ρ : Gal(K/F) →* Equiv.Perm D.base.support := (simplePermutation D).comp ω
  letI : MulAction Gal(K/F) D.base.support := MulAction.compHom D.base.support ρ
  let O := MulAction.orbitRel.Quotient Gal(K/F) D.base.support
  let q : D.base.support → O := Quotient.mk (MulAction.orbitRel Gal(K/F) D.base.support)
  let I (o : O) : Set (Root P.pair.T) := Subtype.val '' {i | q i = o}
  obtain ⟨hs, hscK, hclass⟩ := absoluteClassificationOfSplitPair P D habs hsc
  obtain ⟨L, b, c, hb, hL, hprod⟩ := rationalOrbitTorusProduct G T (B true).borel P D m ω hG hT hmax
    hs hscK hm hA.cocharacters
  let L' (o : O) : RationalStandardFace D (I o) := L o
  have hshape (i : D.base.support) : OrbitShape (integralCartan D.datum.rootDatum D.base) ρ i :=
    attachedOrbitShapes D hclass ω i
  dsimp only
  refine ⟨L', b, c, hb, hL, hprod, hshape, fun o => ?_⟩
  have hstable : ∀ (σ : Gal(K/F)) (α : Root P.pair.T), diagramRoot ω σ α ∈ I o ↔ α ∈ I o := by
    obtain ⟨i, hi⟩ := Quotient.exists_rep o
    have hI : I o = orbitRootSet D ω i := by
      change q i = o at hi
      rw [← hi]
      exact orbitRoots_eq_fiber D ω i
    rw [hI]
    exact (orbitRootStability D ω i).2
  have hA' : IsAmbientPinnedAction D p a (L' o).scalar ω := (hL o).symm ▸ hA
  obtain ⟨d⟩ := rationalFacePinning D pair hG hT hmax U p a ω (I o) (L' o) hA' hstable
  exact ⟨d, rationalFaceAmbientRadicals B D pair hG hT hmax d⟩

open Specs.AdjointCocharacters (coordinateHopf coordinateHopfIso coordinateHopfMap)
open Specs.AutomorphismSequence (forgetPinning)
open Specs.AdjointBorelCohomology (PinnedTwist)
open private scalarExtensionComparison scalarExtensionComparison_coefficients coefficientRingMap
  coefficientRingMap_apply from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitTorusProduct
open private extendedCoordinateIso_natural from LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private extendedSpecIso_hom_fst extendedGroupIso specGroupMap_comp
  from LinearAlgebraicGroups.Affine.ClosedSubgroups

section PinnedComparisons

local notation "coord" => Specs.AdjointCocharacters.coordinateHopf
local notation "coordMap" => Specs.AdjointCocharacters.coordinateHopfMap

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

private def comparisonCoordinateIso {X Y : AffineAlgebraicGroup F}
    (g : (groupBaseChange F K).obj X.val ≅ (groupBaseChange F K).obj Y.val) :
    extendedHopf K (coord Y) ≅ extendedHopf K (coord X) :=
  ((hopfSpec.fullyFaithful (R := CommRingCat.of K)).preimageIso
    ((scalarExtensionComparison (K := K) X).val ≪≫ g ≪≫
      (scalarExtensionComparison (K := K) Y).val.symm)).unop

set_option backward.isDefEq.respectTransparency false in
private theorem comparisonCoordinateIso_comm {X Y : AffineAlgebraicGroup F}
    (g : (groupBaseChange F K).obj X.val ≅ (groupBaseChange F K).obj Y.val) :
    specGroupMap (comparisonCoordinateIso g).hom ≫ (scalarExtensionComparison (K := K) Y).val.hom =
      (scalarExtensionComparison (K := K) X).val.hom ≫ g.hom := by
  let a := (scalarExtensionComparison (K := K) X).val
  let b := (scalarExtensionComparison (K := K) Y).val
  have h : specGroupMap (comparisonCoordinateIso g).hom = (a ≪≫ g ≪≫ b.symm).hom :=
    (hopfSpec.fullyFaithful (R := CommRingCat.of K)).map_preimage ((a ≪≫ g ≪≫ b.symm).hom)
  change specGroupMap (comparisonCoordinateIso g).hom ≫ b.hom = a.hom ≫ g.hom
  rw [h, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, b.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem comparisonCoordinateIso_naturality {X Y U V : AffineAlgebraicGroup F}
    (i : X.val ⟶ U.val) (j : Y.val ⟶ V.val)
    (g : (groupBaseChange F K).obj X.val ≅ (groupBaseChange F K).obj Y.val)
    (h : (groupBaseChange F K).obj U.val ≅ (groupBaseChange F K).obj V.val)
    (sq : g.hom ≫ (groupBaseChange F K).map j = (groupBaseChange F K).map i ≫ h.hom) :
    (comparisonCoordinateIso h).hom ≫ extendedHopfMap K (coordMap i) =
      extendedHopfMap K (coordMap j) ≫ (comparisonCoordinateIso g).hom := by
  let C := groupBaseChange F K
  let a (Z : AffineAlgebraicGroup F) := (scalarExtensionComparison (K := K) Z).val
  have nat {Z W : AffineAlgebraicGroup F} (f : Z.val ⟶ W.val) :
      specGroupMap (extendedHopfMap K (coordMap f)) ≫ (a W).hom =
        (a Z).hom ≫ C.map f := extendedCoordinateIso_natural f
  apply Quiver.Hom.op_inj
  apply (hopfSpec.fullyFaithful (R := CommRingCat.of K)).map_injective
  change specGroupMap ((comparisonCoordinateIso h).hom ≫ extendedHopfMap K (coordMap i)) =
    specGroupMap (extendedHopfMap K (coordMap j) ≫ (comparisonCoordinateIso g).hom)
  rw [specGroupMap_comp, specGroupMap_comp]
  apply (cancel_mono (a V).hom).mp
  rw [Category.assoc, comparisonCoordinateIso_comm, ← Category.assoc, nat,
    Category.assoc, ← sq, ← Category.assoc, ← comparisonCoordinateIso_comm g,
    Category.assoc, ← nat j]
  exact (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
private theorem comparisonCoordinateIso_coefficients {X Y : AffineAlgebraicGroup F}
    (g : (groupBaseChange F K).obj X.val ≅ (groupBaseChange F K).obj Y.val)
    (σ : Gal(K/F)) (b : Y.val ⟶ Y.val)
    (h : coefficientAction σ X.val ≫ g.hom.hom.hom.left =
      g.hom.hom.hom.left ≫ ((groupBaseChange F K).map b).hom.hom.left ≫ coefficientAction σ Y.val)
    (x : extendedHopf K (coord Y)) :
    (Descent.SemilinearAction.scalarExtension (K := K) (coord X)).act σ
        ((comparisonCoordinateIso g).hom.hom x) =
      (comparisonCoordinateIso g).hom.hom ((extendedHopfMap K (coordMap b)).hom
        ((Descent.SemilinearAction.scalarExtension (K := K) (coord Y)).act σ x)) := by
  let C := groupBaseChange F K
  let a (Z : AffineAlgebraicGroup F) := (scalarExtensionComparison (K := K) Z).val
  let ux := (a X).hom.hom.hom.left
  let uy := (a Y).hom.hom.hom.left
  let F₀ := Grp.forget (SchemeOver K) ⋙ Over.forget (Spec (CommRingCat.of K))
  let c (Z : AffineAlgebraicGroup F) :=
    CommRingCat.ofHom (coefficientRingMap σ (coord Z)).toRingHom
  let s := CommRingCat.ofHom (comparisonCoordinateIso g).hom.hom.toAlgHom.toRingHom
  let r := CommRingCat.ofHom (extendedHopfMap K (coordMap b)).hom.toAlgHom.toRingHom
  have ht : Spec.map s ≫ uy = ux ≫ g.hom.hom.hom.left :=
    (congrArg F₀.map (comparisonCoordinateIso_comm g))
  have hb : Spec.map r ≫ uy = uy ≫ (C.map b).hom.hom.left :=
    (congrArg F₀.map (extendedCoordinateIso_natural (K := K) b))
  have hc (Z : AffineAlgebraicGroup F) :
      (a Z).hom.hom.hom.left ≫ coefficientAction σ Z.val =
        Spec.map (c Z) ≫ (a Z).hom.hom.hom.left :=
    scalarExtensionComparison_coefficients (scalarExtensionComparison (K := K) Z) σ
  haveI : IsIso uy := F₀.map_isIso (a Y).hom
  have hs : Spec.map (c X) ≫ Spec.map s = Spec.map s ≫ Spec.map r ≫ Spec.map (c Y) := by
    apply (cancel_mono uy).mp
    calc
      (Spec.map (c X) ≫ Spec.map s) ≫ uy =
          ux ≫ coefficientAction σ X.val ≫ g.hom.hom.hom.left := by
        rw [Category.assoc, ht, ← Category.assoc, ← hc X, Category.assoc]
      _ = ux ≫ g.hom.hom.hom.left ≫ (C.map b).hom.hom.left ≫ coefficientAction σ Y.val :=
        congrArg (ux ≫ ·) h
      _ = (Spec.map s ≫ Spec.map r ≫ Spec.map (c Y)) ≫ uy := by
        simp only [Category.assoc]
        rw [← hc Y, ← Category.assoc (Spec.map r), hb, Category.assoc,
          ← Category.assoc (Spec.map s), ht, Category.assoc]
  have hr : s ≫ c X = (c Y ≫ r) ≫ s := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec.map_comp]
    exact hs
  have hval := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hr) x
  change coefficientRingMap σ (coord X) ((comparisonCoordinateIso g).hom.hom x) =
    (comparisonCoordinateIso g).hom.hom ((extendedHopfMap K (coordMap b)).hom
      (coefficientRingMap σ (coord Y) x)) at hval
  simpa only [coefficientRingMap_apply] using hval

set_option backward.isDefEq.respectTransparency false in
private theorem scalarExtensionIso_unique
    (a : ∀ U : HopfAlgebraCategory F, specGroup (extendedHopf K U) ≅
      (groupBaseChange F K).obj (specGroup U))
    (ha : Descent.Forms.IsScalarExtensionComparison a) (U : HopfAlgebraCategory F) :
    a U = extendedGroupIso K U := by
  apply Iso.ext
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (ha U).trans (extendedSpecIso_hom_fst K U).symm
  · exact (Over.w (a U).hom.hom.hom).trans (Over.w (extendedGroupIso K U).hom.hom.hom).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2500000 in
theorem pinnedTwistFromSchemeComparison : PinnedTwistFromSchemeComparison.{u} := by
  intro F K _ _ _ A₀ P₀ D₀ l H B S ω
  dsimp only
  intro g b t hb ht hcoeff
  let B' := closedSubgroupAlgebraicGroup B
  let S' := closedSubgroupAlgebraicGroup S
  let B₀ := closedSubgroupAlgebraicGroup P₀.pair.B
  let S₀ := closedSubgroupAlgebraicGroup P₀.pair.T
  let d : PinnedTwist (P := P₀) K D₀ l B S :=
    { outer := ω
      groupIso := comparisonCoordinateIso (X := H) (Y := P₀.pair.G) g
      borelIso := comparisonCoordinateIso (X := B') (Y := B₀) b
      torusIso := comparisonCoordinateIso (X := S') (Y := S₀) t
      borelComm := comparisonCoordinateIso_naturality (X := B') (Y := B₀)
        (U := H) (V := P₀.pair.G) B.inclusion P₀.pair.B.inclusion b g hb
      torusComm := comparisonCoordinateIso_naturality (X := S') (Y := S₀)
        (U := H) (V := P₀.pair.G) S.inclusion P₀.pair.T.inclusion t g ht
      twistedAction := fun σ x =>
        comparisonCoordinateIso_coefficients (X := H) (Y := P₀.pair.G) g σ _ (hcoeff σ) x }
  refine ⟨d, rfl, fun a ha => ?_⟩
  rw [scalarExtensionIso_unique a ha (coord H),
    scalarExtensionIso_unique a ha (coord P₀.pair.G)]
  apply Iso.ext
  have hc := comparisonCoordinateIso_comm (X := H) (Y := P₀.pair.G) g
  change (((scalarExtensionComparison (K := K) H).val.inv ≫
    specGroupMap (comparisonCoordinateIso (X := H) (Y := P₀.pair.G) g).hom) ≫
      (scalarExtensionComparison (K := K) P₀.pair.G).val.hom) =
      g.hom
  rw [Category.assoc, hc, Iso.inv_hom_id_assoc]

end PinnedComparisons

open Specs.IntegralSemisimpleModel (fibre forgetFibrePoint)
open Specs.RootGroups (rootPoint)
open Classification.IntegralSemisimpleModel (forgetFibrePoint_bijective)
open private exists_additiveFibreIso forgetFibrePoint_comp
  from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private rootMorphism_ext from LinearAlgebraicGroups.Classification.TransportedRootCoordinates
open private rootPoint_comp from LinearAlgebraicGroups.RootData.RootGroups

section IntegralMarks

open Opposite CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterPairing (characterValue pairing)
open Specs.RationalRealization (Realization)
open CocharacterDynamics (cocharacterPoint unitPoint)
open Specs.IntegralSemisimpleModel (Integers IntegralGroup splitTorus TorusValues torusPoint)
open private characterValue_eq_unit characterUnit from LinearAlgebraicGroups.RootData.RootGroups
open private unitEquiv from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

attribute [local instance] Specs.IntegralSemisimpleModel.integerAlgebra

section
variable {F K : Type u} [Field F] [Field K] [Algebra F K]
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

private abbrev integerSpecMap (k : Type u) [Field k] :
    Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of Integers.{u}) :=
  letI := Specs.IntegralSemisimpleModel.integerAlgebra (k := k)
  Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} k))

private theorem integerSpecMap_tower :
    fieldSpecMap F K ≫ integerSpecMap F = integerSpecMap K := by
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact map_intCast (algebraMap F K) x.down

private def integralFibreTowerComparison (X : Over (Spec (CommRingCat.of Integers.{u}))) :
    ((Over.pullback (integerSpecMap F) ⋙ baseChange F K).obj X).left ≅
      ((Over.pullback (integerSpecMap K)).obj X).left :=
  pullbackLeftPullbackSndIso X.hom (integerSpecMap F) (fieldSpecMap F K) ≪≫
    pullback.congrHom rfl (integerSpecMap_tower (F := F) (K := K))

private theorem integralFibreTowerComparison_fst (X : Over (Spec (CommRingCat.of Integers.{u}))) :
    (integralFibreTowerComparison (F := F) (K := K) X).hom ≫
      pullback.fst X.hom (integerSpecMap K) =
      pullback.fst ((Over.pullback (integerSpecMap F)).obj X).hom (fieldSpecMap F K) ≫
        pullback.fst X.hom (integerSpecMap F) := by
  simp [integralFibreTowerComparison, pullback.congrHom, baseChange]

private theorem integralFibreTowerComparison_snd (X : Over (Spec (CommRingCat.of Integers.{u}))) :
    (integralFibreTowerComparison (F := F) (K := K) X).hom ≫
      ((Over.pullback (integerSpecMap K)).obj X).hom =
        ((Over.pullback (integerSpecMap F) ⋙ baseChange F K).obj X).hom := by
  simp [integralFibreTowerComparison, pullback.congrHom, baseChange]

private def integralFibreTower :
    fibre F ⋙ groupBaseChange F K ≅ fibre K :=
  Functor.mapGrpCompIso.symm ≪≫ Functor.mapGrpNatIso
    (NatIso.ofComponents (fun X ↦ Over.isoMk (integralFibreTowerComparison X)
      (integralFibreTowerComparison_snd X)) (by
      intro X Y a
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · change (((Over.pullback (integerSpecMap F) ⋙ baseChange F K).map a).left ≫
            (integralFibreTowerComparison (F := F) (K := K) Y).hom) ≫ pullback.fst _ _ =
          ((integralFibreTowerComparison (F := F) (K := K) X).hom ≫
            ((Over.pullback (integerSpecMap K)).map a).left) ≫ pullback.fst _ _
        simp only [Category.assoc, integralFibreTowerComparison_fst, Functor.comp_map,
          Over.pullback_map_left, pullback.lift_fst_assoc, pullback.lift_fst]
        rw [← Category.assoc (integralFibreTowerComparison (F := F) (K := K) X).hom,
          integralFibreTowerComparison_fst, Category.assoc]
      · exact (Over.w _).trans (Over.w _).symm))

private theorem forgetIntegralFibreTower (G : IntegralGroup.{u}) (R : TestAlgebra K)
    (p : GroupPoints ((fibre F ⋙ groupBaseChange F K).obj G) R) :
    forgetFibrePoint G R (p ≫ ((integralFibreTower (F := F) (K := K)).app G).hom.hom.hom) =
      forgetFibrePoint G ((restrictTestAlgebra F K).obj R)
        (baseChangePoint F K ((fibre F).obj G).X R p) := by
  apply Over.OverMorphism.ext
  change (p.left ≫ (integralFibreTowerComparison (F := F) (K := K) G.X).hom) ≫
      pullback.fst G.X.hom (integerSpecMap K) =
    (p.left ≫ pullback.fst ((fibre F).obj G).X.hom (fieldSpecMap F K)) ≫
      pullback.fst G.X.hom (integerSpecMap F)
  rw [Category.assoc, integralFibreTowerComparison_fst, Category.assoc]
  rfl

private theorem integralCocharacter_point {k : Type u} [Field k] {A : AdditiveLine k}
    {D : BasedRootDatum.{u}} (P : Realization D A)
    (t : (fibre k).obj (splitTorus D) ≅ P.pinned.pair.T.group)
    (h : ∀ (R : TestAlgebra k) (s : GroupPoints ((fibre k).obj (splitTorus D)) R)
          (v : TorusValues D (CommAlgCat.of Integers.{u} R)),
        forgetFibrePoint (splitTorus D) R s = torusPoint D (CommAlgCat.of Integers.{u} R) v →
        ∀ x : D.X, characterValue (Additive.toMul (P.datumIso.val.weightEquiv x)) R
          (s ≫ t.hom.hom.hom) = (v (Multiplicative.ofAdd x) : R))
    (y : D.Y) (R : TestAlgebra k) (v : Rˣ) :
    letI := P.attached.comm
    forgetFibrePoint (splitTorus D) R
      (cocharacterPoint (P.datumIso.val.coweightEquiv.symm y).toMul R v ≫ t.inv.hom.hom) =
        torusPoint D (CommAlgCat.of Integers.{u} R)
          (Specs.IntegralSemisimpleModel.cocharacter D y (CommAlgCat.of Integers.{u} R) v) := by
  letI := P.attached.comm
  let q := Specs.IntegralSemisimpleModel.cocharacter D y (CommAlgCat.of Integers.{u} R) v
  obtain ⟨s, hs⟩ := (forgetFibrePoint_bijective (splitTorus D) R).2
    (torusPoint D (CommAlgCat.of Integers.{u} R) q)
  let c : Cocharacter P.pinned.pair.T.group := (P.datumIso.val.coweightEquiv.symm y).toMul
  have hc : s ≫ t.hom.hom.hom = cocharacterPoint c R v := by
    apply Classification.PinnedUniqueness.charactersSeparatePoints P.pinned.pair.split R
    intro χ
    obtain ⟨x, hx⟩ := P.datumIso.val.weightEquiv.surjective (Additive.ofMul χ)
    have hχ : (P.datumIso.val.weightEquiv x).toMul = χ := congrArg Additive.toMul hx
    have he : pairing P.pinned.pair.T.group χ c = D.datum.toLinearMap x y := by
      rw [← hχ, ← P.attached.datum.pairing_eq]
      change P.attached.datum.rootDatum.toLinearMap (P.datumIso.val.weightEquiv x)
        (P.datumIso.val.coweightEquiv.symm y) = D.datum.toLinearMap x y
      have hp := DFunLike.congr_fun (P.datumIso.val.toHom.weight_coweight_transpose_apply
        D.datum P.attached.toBased.datum (P.datumIso.val.coweightEquiv.symm y)) x
      have hy := P.datumIso.val.coweightEquiv.apply_symm_apply y
      change P.attached.datum.rootDatum.toLinearMap (P.datumIso.val.weightEquiv x)
          (P.datumIso.val.coweightEquiv.symm y) =
        D.datum.toLinearMap x (P.datumIso.val.coweightEquiv (P.datumIso.val.coweightEquiv.symm y)) at hp
      exact hp.trans (congrArg (D.datum.toLinearMap x) hy)
    apply (unitEquiv R).injective
    apply Units.ext
    change (characterUnit χ R (s ≫ t.hom.hom.hom) : R) =
      (characterUnit χ R (cocharacterPoint c R v) : R)
    rw [← characterValue_eq_unit, ← characterValue_eq_unit,
      (RootData.CharacterPairing.characterPairingComposition _ χ c).2 R v, he, ← hχ]
    exact h R s q hs x
  have hc' := congrArg (fun z : GroupPoints P.pinned.pair.T.group R => z ≫ t.inv.hom.hom) hc
  have hn : t.hom.hom.hom ≫ t.inv.hom.hom = 𝟙 ((fibre k).obj (splitTorus D)).X :=
    (congrArg (fun f : (fibre k).obj (splitTorus D) ⟶ (fibre k).obj (splitTorus D) =>
      f.hom.hom) t.hom_inv_id)
  change forgetFibrePoint (splitTorus D) R (cocharacterPoint c R v ≫ t.inv.hom.hom) = _
  rw [← hc']
  simpa only [Category.assoc, hn, Category.comp_id] using hs

set_option maxHeartbeats 1900000 in
private theorem compareCocharactersOfFibrePoints
    (X : IntegralGroup.{u}) {S₀ : GroupScheme F} {S : GroupScheme K}
    (t₀ : (fibre F).obj X ≅ S₀) (t : (fibre K).obj X ≅ S)
    (c₀ : Cocharacter S₀) (c : Cocharacter S)
    (m : MultiplicativeComparison F K) (hm : PreservesUnits m)
    (same : ∀ (R : TestAlgebra K) (v : Rˣ),
      let R₀ := (restrictTestAlgebra F K).obj R
      forgetFibrePoint X R (cocharacterPoint c R v ≫ t.inv.hom.hom) =
        forgetFibrePoint X R₀ (cocharacterPoint c₀ R₀ v ≫ t₀.inv.hom.hom)) :
    c ≫ (t.symm ≪≫ ((integralFibreTower (F := F) (K := K)).app X).symm ≪≫
      (groupBaseChange F K).mapIso t₀).hom = m.hom ≫ (groupBaseChange F K).map c₀ := by
  let C := groupBaseChange F K
  let s := (integralFibreTower (F := F) (K := K)).app X
  apply cocharacter_ext_units
  intro R v
  let R₀ := (restrictTestAlgebra F K).obj R
  let b := cocharacterPoint c R v ≫ t.inv.hom.hom
  let b' := b ≫ s.inv.hom.hom
  have hb' : baseChangePoint F K ((fibre F).obj X).X R b' =
      cocharacterPoint c₀ R₀ v ≫ t₀.inv.hom.hom := by
    apply (forgetFibrePoint_bijective X R₀).1
    rw [← forgetIntegralFibreTower X R b']
    change forgetFibrePoint X R ((b ≫ s.inv.hom.hom) ≫ s.hom.hom.hom) = _
    have hc : s.inv.hom.hom ≫ s.hom.hom.hom = 𝟙 _ :=
      (congrArg (fun f : (fibre K).obj X ⟶ (fibre K).obj X => f.hom.hom) s.inv_hom_id)
    rw [Category.assoc, hc, Category.comp_id]
    exact same R v
  apply (baseChangePoints F K S₀.X R).1
  change baseChangePoint F K S₀.X R
      (b' ≫ (C.map t₀.hom).hom.hom) =
      baseChangePoint F K S₀.X R
        ((unitPoint R v ≫ m.hom.hom.hom) ≫ (C.map c₀).hom.hom)
  have hl := baseChangePointsSchemeNaturality F K t₀.hom.hom.hom R b'
  have hr := baseChangePointsSchemeNaturality F K c₀.hom.hom R (unitPoint R v ≫ m.hom.hom.hom)
  rw [hb'] at hl
  rw [hm R v] at hr
  refine hl.trans (Eq.trans ?_ hr.symm)
  have hc : t₀.inv.hom.hom ≫ t₀.hom.hom.hom = 𝟙 _ :=
    (congrArg (fun f : S₀ ⟶ S₀ => f.hom.hom) t₀.inv_hom_id)
  rw [Category.assoc, hc, Category.comp_id]
  rfl


set_option maxHeartbeats 2300000 in
private theorem compareIntegralCocharacters {D : BasedRootDatum.{u}}
    {A₀ : AdditiveLine F} {A : AdditiveLine K}
    (P₀ : Realization D A₀) (P : Realization D A)
    (t₀ : (fibre F).obj (splitTorus D) ≅ P₀.pinned.pair.T.group)
    (t : (fibre K).obj (splitTorus D) ≅ P.pinned.pair.T.group)
    (h₀ : ∀ (R : TestAlgebra F) (s : GroupPoints ((fibre F).obj (splitTorus D)) R)
          (v : TorusValues D (CommAlgCat.of Integers.{u} R)),
        forgetFibrePoint (splitTorus D) R s = torusPoint D (CommAlgCat.of Integers.{u} R) v →
        ∀ x : D.X, characterValue (Additive.toMul (P₀.datumIso.val.weightEquiv x)) R
          (s ≫ t₀.hom.hom.hom) = (v (Multiplicative.ofAdd x) : R))
    (h : ∀ (R : TestAlgebra K) (s : GroupPoints ((fibre K).obj (splitTorus D)) R)
          (v : TorusValues D (CommAlgCat.of Integers.{u} R)),
        forgetFibrePoint (splitTorus D) R s = torusPoint D (CommAlgCat.of Integers.{u} R) v →
        ∀ x : D.X, characterValue (Additive.toMul (P.datumIso.val.weightEquiv x)) R
          (s ≫ t.hom.hom.hom) = (v (Multiplicative.ofAdd x) : R))
    (m : MultiplicativeComparison F K) (hm : PreservesUnits m) :
    letI := P₀.attached.comm
    letI := P.attached.comm
    ∀ y : D.Y,
      (P.datumIso.val.coweightEquiv.symm y).toMul ≫
        (t.symm ≪≫ ((integralFibreTower (F := F) (K := K)).app (splitTorus D)).symm ≪≫
          (groupBaseChange F K).mapIso t₀).hom =
      m.hom ≫ (groupBaseChange F K).map (P₀.datumIso.val.coweightEquiv.symm y).toMul := by
  letI := P₀.attached.comm
  letI := P.attached.comm
  intro y
  apply compareCocharactersOfFibrePoints _ t₀ t _ _ m hm
  intro R v
  dsimp only
  rw [integralCocharacter_point P t h y R v,
    integralCocharacter_point P₀ t₀ h₀ y ((restrictTestAlgebra F K).obj R) v]

end

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
theorem integralFibreRootMaps : IntegralFibreRootMaps.{u} := by
  intro D M k _
  obtain ⟨A, R, g, t, x, ht, hx, hT, hX⟩ := M.fieldFibre k
  obtain ⟨a, ha⟩ := exists_additiveFibreIso M.line A
  refine ⟨A, R, g, t, a, x, ht, hx, hT, fun i => ?_⟩
  let u := (x i).val.hom ≫ (R.pinned.roots (R.datumIso.val.indexEquiv i)).val.inclusion
  have heq : u ≫ g.inv = a.hom ≫ (fibre k).map (M.root i) := by
    apply rootMorphism_ext
    intro L z
    apply (forgetFibrePoint_bijective M.group L).1
    rw [rootPoint_comp a.hom ((fibre k).map (M.root i)) L z,
      forgetFibrePoint_comp (M.root i) L, ha L z]
    exact hX i L z
  calc
    u = (u ≫ g.inv) ≫ g.hom := by rw [Category.assoc, g.inv_hom_id, Category.comp_id]
    _ = _ := by rw [heq, Category.assoc]

open Specs.OrderedRootProducts (rootProduct)
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open private factor_group_through_subgroup
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private productFactors radicalProduct existsEnumeration rootInRadical
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitAmbientWords
open private base_isPos_iff_subgroupRoots basedIso_pos_iff pushKBorel
  from LinearAlgebraicGroups.Classification.PinnedEquivalence
open private subgroup_baseChange_iff from LinearAlgebraicGroups.Reductive.RadicalBaseChange

set_option backward.isDefEq.respectTransparency false in
private theorem borelFactorsThrough {k : Type u} [Field k] (P : SplitBorelPair k)
    [Finite (Root P.T)] (U : RootSubgroupFamily P.T) {G : GroupScheme k}
    (g : P.G.val ⟶ G) (S : ClosedSubgroup G)
    (c : P.T.group ⟶ S.group) (hc : c ≫ S.inclusion = P.T.inclusion ≫ g)
    (hU : ∀ i ∈ subgroupRoots P.T P.B, ∃ j : (U i).val.group ⟶ S.group,
      j ≫ S.inclusion = (U i).val.inclusion ≫ g) :
    ∃ b : P.B.group ⟶ S.group, b ≫ S.inclusion = P.B.inclusion ≫ g := by
  obtain ⟨t, ht⟩ := P.containsTorus
  obtain ⟨R, q, hR, hq, hqt⟩ :=
    borelRadicalAndQuotient P.reductive P.T P.B P.maximal P.borel t ht
  let B : BorelRadical P.G := ⟨P.B, P.borel, R, hR⟩
  obtain ⟨l, hl⟩ := existsEnumeration (subgroupRoots P.T P.B)
  obtain ⟨e, he⟩ := radicalProduct P.reductive P.split P.maximal B ⟨t, ht⟩ U l hl
  obtain ⟨p, hp⟩ := productFactors U g S.inclusion l (fun i hi => hU i (hl.2 i |>.mp hi))
  let b := P.B.inclusion ≫ g
  have hRad : (e.inv ≫ p) ≫ S.inclusion.hom.hom = R.inclusion.hom.hom ≫ b.hom.hom := by
    rw [Category.assoc, hp, ← he]
    change e.inv ≫ e.hom ≫ R.inclusion.hom.hom ≫ b.hom.hom = _
    rw [e.inv_hom_id_assoc]
  let s : P.B.group.X ⟶ P.B.group.X := q.hom.hom ≫ t.hom.hom
  let d : P.B.group.X ⟶ P.B.group.X := s⁻¹ * 𝟙 _
  have hq' : d ≫ q.hom.hom = 1 := by
    have h := congrArg (fun f : P.T.group ⟶ P.T.group => f.hom.hom) hqt
    change t.hom.hom ≫ q.hom.hom = 𝟙 _ at h
    simp only [d, MonObj.mul_comp, GrpObj.inv_comp, Category.id_comp, s, Category.assoc,
      h, Category.comp_id, inv_mul_cancel]
  obtain ⟨x, hx⟩ := (schemeKernel_sections hq d).mpr hq'
  change x ≫ R.inclusion.hom.hom = d at hx
  have hpT : (q.hom.hom ≫ c.hom.hom) ≫ S.inclusion.hom.hom = s ≫ b.hom.hom := by
    have ht' : c.hom.hom ≫ S.inclusion.hom.hom = t.hom.hom ≫ b.hom.hom := by
      rw [← Grp.comp_hom_hom, hc]
      exact congrArg (fun f : P.T.group ⟶ G => f.hom.hom)
        (show P.T.inclusion ≫ g = t ≫ b from by rw [← ht, Category.assoc])
    simp only [s, Category.assoc, ht']
  have hprod : ((q.hom.hom ≫ c.hom.hom) * (x ≫ e.inv ≫ p)) ≫ S.inclusion.hom.hom =
      b.hom.hom := by
    rw [MonObj.mul_comp, hpT, Category.assoc x, hRad, ← Category.assoc x, hx,
      ← MonObj.mul_comp]
    simp only [d, mul_inv_cancel_left, Category.id_comp]
  exact factor_group_through_subgroup S b _ hprod

set_option backward.isDefEq.respectTransparency false in
private theorem borelIsoOfInclusion {k : Type u} [Field k] {G : GroupScheme k}
    {B C : ClosedSubgroup G} (hB : IsKBorel B) (hC : IsKBorel C) (hle : IsSubgroupOf B C) :
    ∃ b : B.group ≅ C.group, b.hom ≫ C.inclusion = B.inclusion := by
  let E := AlgebraicClosure k
  obtain ⟨b, hB⟩ := hB
  obtain ⟨c, hC⟩ := hC
  have hle' : IsSubgroupOf (baseChangedSubgroup E B b) (baseChangedSubgroup E C c) :=
    (subgroup_baseChange_iff (K := E) B C).mpr hle
  have hge := hB.2 (baseChangedSubgroup E C c) hC.1 hle'
  exact sameSubgroupIso ⟨hle, (subgroup_baseChange_iff (K := E) C B).mp hge⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4400000 in
theorem integralSplitComparison : IntegralSplitComparison.{u} := by
  intro F K _ _ _ D
  obtain ⟨M⟩ := integralRealization D
  obtain ⟨A₀, R₀, g₀, t₀, a₀, x₀, ht₀, pin₀, hT₀, hx₀⟩ := integralFibreRootMaps D M F
  obtain ⟨A, R, g, t, a, x, ht, pin, hTK, hx⟩ := integralFibreRootMaps D M K
  let C := groupBaseChange F K
  let s := (integralFibreTower (F := F) (K := K)).symm
  let g' := g.symm ≪≫ s.app M.group ≪≫ C.mapIso g₀
  let t' := t.symm ≪≫ s.app _ ≪≫ C.mapIso t₀
  let a' := a ≪≫ s.app M.line.group ≪≫ (C.mapIso a₀).symm
  have htorus : R.pinned.pair.T.inclusion ≫ g'.hom =
      t'.hom ≫ C.map R₀.pinned.pair.T.inclusion := by
    have left₀ := s.hom.naturality M.torus
    change (fibre K).map M.torus ≫ (s.app M.group).hom =
      (s.app _).hom ≫ C.map ((fibre F).map M.torus) at left₀
    have ht' : R.pinned.pair.T.inclusion ≫ g.inv = t.inv ≫ (fibre K).map M.torus := by
      rw [← cancel_epi t.hom, t.hom_inv_id_assoc, ← Category.assoc, ← ht, Category.assoc,
        g.hom_inv_id, Category.comp_id]
    change R.pinned.pair.T.inclusion ≫ g.inv ≫ (s.app M.group).hom ≫ C.map g₀.hom =
      (t.inv ≫ (s.app _).hom ≫ C.map t₀.hom) ≫ C.map R₀.pinned.pair.T.inclusion
    rw [← Category.assoc R.pinned.pair.T.inclusion, ht']
    simp only [Category.assoc, reassoc_of% left₀, ← C.map_comp]
    rw [ht₀]
    rfl
  let xK (i : D.I) := (x i).val.hom ≫ (R.pinned.roots (R.datumIso.val.indexEquiv i)).val.inclusion
  let xF (i : D.I) := (x₀ i).val.hom ≫ (R₀.pinned.roots (R₀.datumIso.val.indexEquiv i)).val.inclusion
  have mark (i : D.I) : xK i ≫ g'.hom = a'.hom ≫ C.map (xF i) := by
    have h := s.hom.naturality (M.root i)
    change (fibre K).map (M.root i) ≫ (s.app M.group).hom =
      (s.app M.line.group).hom ≫ C.map ((fibre F).map (M.root i)) at h
    change xK i ≫ g.inv ≫ (s.app M.group).hom ≫ C.map g₀.hom =
      (a.hom ≫ (s.app M.line.group).hom ≫ C.map a₀.inv) ≫ C.map (xF i)
    rw [show xK i = _ from hx i, show xF i = _ from hx₀ i]
    have ha : C.map a₀.inv ≫ C.map a₀.hom = 𝟙 _ := by
      rw [← C.map_comp, a₀.inv_hom_id, C.map_id]
    simp only [Category.assoc, g.hom_inv_id_assoc, reassoc_of% h, C.map_comp, reassoc_of% ha]
  let P₀ := R₀.pinned.pair
  let P := R.pinned.pair
  let B := baseChangedSubgroup K P₀.B (baseChangeClosedSubgroup F K P₀.B.inclusion P₀.B.isClosedImmersion)
  obtain ⟨j, hj⟩ := P₀.containsTorus
  have hT : (t'.hom ≫ C.map j) ≫ B.inclusion = P.T.inclusion ≫ g'.hom := by
    change (t'.hom ≫ C.map j) ≫ C.map P₀.B.inclusion = P.T.inclusion ≫ g'.hom
    rw [Category.assoc, ← C.map_comp, hj, ← htorus]
  have hB : IsKBorel B :=
    compared_borel_ascent (H := Specs.Unipotent.baseChangedAlgebraicGroup K P₀.G)
      P₀.reductive P₀.B B (Iso.refl _) (Iso.refl _) (by
        change (𝟙 _) ≫ C.map P₀.B.inclusion = C.map P₀.B.inclusion ≫ (𝟙 _)
        rw [Category.id_comp, Category.comp_id]) P₀.borel
  obtain ⟨V, _, hV, _, _⟩ :=
    borelRadicalAndQuotient P₀.reductive P₀.T P₀.B P₀.maximal P₀.borel j hj
  let B₀ : BorelRadical P₀.G := ⟨P₀.B, P₀.borel, V, hV⟩
  letI := R.attached.comm
  letI := R₀.attached.comm
  letI := R.attached.datum.finiteRoots
  letI := R₀.attached.datum.finiteRoots
  have rootMark : ∀ b ∈ subgroupRoots P.T P.B,
      ∃ f : (R.pinned.roots b).val.group ⟶ B.group,
        f ≫ B.inclusion = (R.pinned.roots b).val.inclusion ≫ g'.hom := by
    intro b hb
    obtain ⟨i, rfl⟩ := R.datumIso.val.indexEquiv.surjective b
    have pos {k : Type u} [Field k] (P : SplitBorelPair k) (D : AttachedDatum P)
        (α : Root P.T) : letI := D.comm; D.base.IsPos α ↔ α ∈ subgroupRoots P.T P.B := by
      obtain ⟨_, _, _, hBorels, _⟩ :=
        RootData.BorelPositivity.borelPositivity P.G P.reductive P.T P.split P.maximal
      exact base_isPos_iff_subgroupRoots D (hBorels.1 P.B P.borel P.containsTorus) α
    have hi : D.base.IsPos i :=
      (basedIso_pos_iff R.datumIso i).mpr ((pos P R.attached _).mpr hb)
    have hf : R₀.datumIso.val.indexEquiv i ∈ subgroupRoots P₀.T P₀.B :=
      (pos P₀ R₀.attached _).mp ((basedIso_pos_iff R₀.datumIso i).mp hi)
    obtain ⟨y, hy⟩ := rootInRadical P₀.reductive P₀.split P₀.maximal B₀
      P₀.containsTorus R₀.pinned.roots _ hf
    let z := y ≫ V.inclusion
    have hz : z ≫ P₀.B.inclusion = (R₀.pinned.roots (R₀.datumIso.val.indexEquiv i)).val.inclusion := by
      rw [Category.assoc]
      exact hy
    let f := (x i).val.inv ≫ a'.hom ≫ C.map ((x₀ i).val.hom ≫ z)
    refine ⟨f, ?_⟩
    change ((x i).val.inv ≫ a'.hom ≫ C.map ((x₀ i).val.hom ≫ z)) ≫ C.map P₀.B.inclusion = _
    simp only [Category.assoc, ← C.map_comp, hz, ← mark i, xK, xF, Iso.inv_hom_id_assoc]
  obtain ⟨b, hb⟩ := borelFactorsThrough P R.pinned.roots g'.hom B _ hT rootMark
  let B' := subgroupAlongIso g' P.B
  have hB' : IsKBorel B' := pushKBorel g' P.borel
  obtain ⟨j', hj'⟩ := borelIsoOfInclusion hB' hB ⟨b, hb⟩
  refine ⟨A₀, A, R₀, R, g', t', a', j', htorus, hj'.symm, ?_, ?_⟩
  · intro i
    have eq₁ : xK i.val = R.rootMap i := by
      exact congrArg (fun z => z.val.hom ≫
        (R.pinned.roots (R.datumIso.val.indexEquiv i.val)).val.inclusion) (pin i)
    have eq₂ : xF i.val = R₀.rootMap i := by
      exact congrArg (fun z => z.val.hom ≫
        (R₀.pinned.roots (R₀.datumIso.val.indexEquiv i.val)).val.inclusion) (pin₀ i)
    simpa only [eq₁, eq₂] using mark i.val
  · intro m hm y
    exact compareIntegralCocharacters R₀ R t₀ t hT₀ hTK m hm y

end IntegralMarks

open Specs.AbsoluteDynkinTypes (PreservesCartan)
open RootData.AbsoluteDynkinTypes (cartanDeterminesBasedDatum)

theorem cartanActionLift : CartanActionLift.{u} := by
  classical
  intro Γ _ D hD ρ hρ
  have hex g := (cartanDeterminesBasedDatum D D hD hD (ρ g)).mp (hρ g)
  choose f hf using fun g => (hex g).exists
  let lift (g : Γ) : Aut D := Aut.of (asIso (f g : D ⟶ D))
  have eqLift g (b : D ⟶ D)
      (hb : ∀ i : D.base.support, b.val.indexEquiv i.val = (ρ g i).val) :
      f g = b := (hex g).unique (hf g) hb
  let θ : Γ →* Aut D :=
    { toFun := lift
      map_one' := by
        apply Aut.ext
        apply Iso.ext
        change f 1 = 𝟙 D
        apply eqLift
        intro i
        rw [map_one]
        rfl
      map_mul' := by
        intro g h
        apply Aut.ext
        apply Iso.ext
        refine eqLift (g * h) (lift g * lift h).asIso.hom (fun i => ?_)
        change (f g).val.indexEquiv ((f h).val.indexEquiv i.val) = (ρ (g * h) i).val
        rw [hf h i, hf g (ρ h i), map_mul, Equiv.Perm.mul_apply] }
  exact ⟨θ, hf⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1300000 in
theorem rationalFaceDiagram : RationalFaceDiagram.{u} := by
  intro F K _ _ _ G T B N P D pair hG hT hmax A₀ A U p a ω I L d hs
  letI := D.comm
  let E := d.posDatum
  letI := E.comm
  obtain ⟨v, hv, hCartan⟩ := rationalFaceCartanComparison D d
  let r : Gal(K/F) →* Equiv.Perm I :=
    { toFun := fun σ => (ω σ).asIso.hom.val.indexEquiv.subtypeEquiv (fun i => (hs σ i).symm)
      map_one' := by
        ext i
        simp only [map_one]
        rfl
      map_mul' := by
        intro σ τ
        ext i
        simp only [map_mul]
        rfl }
  let ρ : Gal(K/F) →* Equiv.Perm E.base.support := v.permCongrHom.toMonoidHom.comp r
  have hρ (σ : Gal(K/F)) :
      PreservesCartan (integralCartan E.datum.rootDatum E.base)
        (integralCartan E.datum.rootDatum E.base) (ρ σ) := by
    intro x y
    obtain ⟨i, rfl⟩ := v.surjective x
    obtain ⟨j, rfl⟩ := v.surjective y
    have h (i : I) : ρ σ (v i) = v (r σ i) := by
      change v (r σ (v.symm (v i))) = v (r σ i)
      rw [v.symm_apply_apply]
    rw [h i, h j]
    change E.datum.rootDatum.pairing (v j).val (v i).val =
      E.datum.rootDatum.pairing (v (r σ j)).val (v (r σ i)).val
    rw [hCartan, hCartan]
    exact ((ω σ).asIso.hom.val.toHom.pairing (i := j.val) (j := i.val)).symm
  have hsc := QuasiSplitOrbitDerivedRoots.splitDerivedSimplyConnected D I (L.splitFace D) L.integralImage
  let H := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup L.limit.centralizer) L.derived
  have hsem : IsSemisimple (L.splitFace D).group :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := K) H L.semisimple.1 L.semisimple.2.1).mpr L.semisimple
  letI : IsCommMonObj (L.splitFace D).torus.group.X := E.comm
  have hY : corootLattice E = ⊤ :=
    (latticeCriterion (L.splitFace D).group hsem (L.splitFace D).torus
      L.splitTorus L.splitMaximal E.datum).mp hsc
  obtain ⟨θ, hθ⟩ := cartanActionLift E.toBased hY ρ hρ
  refine ⟨v, θ, hv, hCartan, ?_⟩
  intro σ i
  rw [hθ σ (v i)]
  change (v (r σ (v.symm (v i)))).val = (v (r σ i)).val
  rw [v.symm_apply_apply]

open Specs.AbsoluteDynkinTypes (ClassifiedDatum)

set_option backward.isDefEq.respectTransparency false in
theorem orbitFaceCartan : OrbitFaceCartan.{u} := by
  classical
  intro k _ P D hD Γ _ ω i
  letI := D.comm
  let ρ := (simplePermutation D).comp ω
  let I := orbitRootSet D ω i
  let J := diagramOrbit ρ i
  let f (x : J) : I := ⟨x.val.val, ⟨x.val, x.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      exact Subtype.ext (Subtype.ext (congrArg (fun y : I => y.val) h))
    · rintro ⟨a, ⟨x, hx, rfl⟩⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  let v := Equiv.ofBijective f hf
  have hcase := attachedOrbitShapes D hD ω i
  rcases hcase with ho | ⟨n, hn, e, he, eq⟩
  · left
    intro a b h
    obtain ⟨a', rfl⟩ := v.surjective a
    obtain ⟨b', rfl⟩ := v.surjective b
    have hn : a'.val ≠ b'.val := fun h' => h (congrArg v (Subtype.ext h'))
    exact (ho a'.val a'.property b'.val b'.property hn).2
  let l : Fin (2 * n) := ⟨n - 1, by omega⟩
  let r : Fin (2 * n) := ⟨n, by omega⟩
  have hne : l ≠ r := fun h => by have := congrArg Fin.val h; dsimp [l, r] at this; omega
  have hset : e '' J = {l, r} := eq
  let τ : J ≃ ↥({l, r} : Set (Fin (2 * n))) :=
    e.subtypeEquiv (fun x => by rw [← hset, Set.mem_image]; exact ⟨fun h => ⟨x, h, rfl⟩,
      fun ⟨y, hy, hyx⟩ => e.injective hyx ▸ hy⟩)
  let g (b : Fin 2) : ↥({l, r} : Set (Fin (2 * n))) :=
    if b = 0 then ⟨l, Set.mem_insert _ _⟩ else ⟨r, Set.mem_insert_of_mem _ rfl⟩
  have hg : Function.Bijective g := by
    constructor
    · intro a b h
      fin_cases a <;> fin_cases b
      · rfl
      · exact (hne (congrArg Subtype.val h)).elim
      · exact (hne (congrArg Subtype.val h).symm).elim
      · rfl
    · rintro ⟨y, hy⟩
      rcases Set.mem_insert_iff.mp hy with hl | hr
      · exact ⟨0, Subtype.ext hl.symm⟩
      · exact ⟨1, Subtype.ext (Set.mem_singleton_iff.mp hr).symm⟩
  let j := (Equiv.ofBijective g hg).trans (τ.symm.trans v)
  right
  refine ⟨j, fun a b => ?_⟩
  let a' := τ.symm (g a)
  let b' := τ.symm (g b)
  have ha : e a'.val = (g a).val := congrArg Subtype.val (τ.apply_symm_apply (g a))
  have hb : e b'.val = (g b).val := congrArg Subtype.val (τ.apply_symm_apply (g b))
  change integralCartan D.datum.rootDatum D.base b'.val a'.val = _
  rw [he, ha, hb]
  have hv : l.val + 1 = r.val := by dsimp [l, r]; omega
  have hlr : CartanMatrix.A (2 * n) l r = -1 := by
    simp [CartanMatrix.A, hne, hv]
  have hrl : CartanMatrix.A (2 * n) r l = -1 := by
    simp [CartanMatrix.A, hne.symm, hv]
  fin_cases a <;> fin_cases b
  · exact congrFun (CartanMatrix.A_diag (2 * n)) l
  · exact hrl
  · exact hlr
  · exact congrFun (CartanMatrix.A_diag (2 * n)) r

section FaceNormalizer

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Specs.QuasiSplitOrbitAmbientWords (RationalPoints extendPoint onPoints onRational groundPointIso
  IsFaceLongest)
open Specs.QuasiSplitOrbitDerivedRoots (SplitFace)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Specs.AdjointRepresentation (GroupPoints)
open CocharacterDynamics (factorsThroughClosed_iff cocharacterPoint mapPoints_unitPoint unitPoint)
open private face_cocharacter_decomposition multiplicativeLine_split
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitDerivedRoots
open private mono_over centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private factor_group_through_subgroup
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private conjugates_of_normalizes normalizes_inv normalizes_iff_sections
  from LinearAlgebraicGroups.RootData.BorelNormalizer
open private conjugatesSubgroups_square from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private torus_smooth from LinearAlgebraicGroups.Reductive.CentralFrobeniusDescent
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private normalizes_of_conjugates_self conjugate conjugationIso comp_conjugate
  rationalConstant conjugate_comp from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private unitPointHom_apply unitEquiv unitEquiv_unitPoint
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private isTorus_of_split from LinearAlgebraicGroups.RootData.CharacterPairing
open private extendPoint_natural normalizes_of_extended longest_of_simple_images
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitAmbientWords
open private face_stabilizes_cocharacter from LinearAlgebraicGroups.Flag.StandardParabolicLevi

section
variable {k : Type u} [Field k]
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

private theorem subgroup_eq_top_of_cocharacters {T : GroupScheme k} (hT : IsSplitTorus T)
    (R : TestAlgebra k) (Q : Subgroup (GroupPoints T R))
    (h : ∀ (c : Cocharacter T) (t : Rˣ), cocharacterPoint c R t ∈ Q) :
    Q = ⊤ := by
  classical
  obtain ⟨hcomm, _⟩ := RootData.CharacterPairing.perfectCharacterPairing T hT
  letI := hcomm
  obtain ⟨n, ⟨Tiso⟩⟩ := hT
  let I := ULift.{u} (Fin n)
  let M := specGroup (groupAlgebra k IntegerCharacters)
  let e := (groupPointsFunctor k).mapIso Tiso ≪≫
    (LinearAlgebraicGroups.StandardGroups.multiplicativePowerGroupPointsIso k I)
  let f (j : I) : (groupPointsFunctor k).obj M ⟶ Specs.StandardGroups.multiplicativePowerPoints k I :=
    { app := fun S => GrpCat.ofHom ((MonoidHom.mulSingle (fun _ : I => Sˣ) j).comp (unitEquiv S).toMonoidHom)
      naturality := by
        intro S S' a
        apply GrpCat.ext
        intro x
        obtain ⟨v, rfl⟩ := (unitEquiv S).symm.surjective x
        have hx := mapPoints_unitPoint a v
        change Pi.mulSingle j (unitEquiv S' (mapPoints a ((unitEquiv S).symm v))) =
          (fun i => Units.map a.hom.toMonoidHom ((Pi.mulSingle j (unitEquiv S ((unitEquiv S).symm v)) : I → Sˣ) i))
        rw [show (unitEquiv S).symm v = unitPoint S v from unitPointHom_apply S v, hx,
          unitEquiv_unitPoint, unitEquiv_unitPoint]
        funext i
        by_cases hij : i = j
        · subst i
          simp
        · simp [Pi.mulSingle_eq_of_ne hij] }
  have hM : IsAffine M.X.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (MonoidAlgebra k IntegerCharacters))))
  obtain ⟨c, hc⟩ : ∃ c : I → Cocharacter T,
      ∀ j, (groupPointsFunctor k).map (c j) = f j ≫ e.inv := by
    choose c hc using fun j => (groupHomComparison k M T hM).2 (f j ≫ e.inv)
    exact ⟨c, hc⟩
  let eR := (e.app R).groupIsoToMulEquiv
  have hm (j : I) (v : Rˣ) : eR (cocharacterPoint (c j) R v) = Pi.mulSingle j v := by
    apply eR.symm.injective
    rw [MulEquiv.symm_apply_apply]
    have hj := congrArg (fun a => a.app R (unitPoint R v)) (hc j)
    change cocharacterPoint (c j) R v =
      eR.symm (Pi.mulSingle j (unitEquiv R (unitPoint R v))) at hj
    rw [unitEquiv_unitPoint] at hj
    exact hj
  apply top_unique
  intro x _
  have hsingle (j : I) :
      Pi.mulSingle j (eR x j) ∈ Q.map eR.toMonoidHom :=
    ⟨cocharacterPoint (c j) R (eR x j), h (c j) _, hm j _⟩
  have hx : eR x ∈ Q.map eR.toMonoidHom := by
    rw [← Finset.univ_prod_mulSingle (eR x)]
    exact Subgroup.prod_mem (Q.map eR.toMonoidHom) (t := Finset.univ)
      (f := fun j : I => (Pi.mulSingle j (eR x j) : I → Rˣ)) (fun j _ => hsingle j)
  obtain ⟨y, hy, e⟩ := hx
  exact eR.injective e ▸ hy

/-- A map from a reduced scheme factors through a closed immersion if its
pullback along a surjective map factors through it. -/
private theorem closedFactorOfSurjective {V X Y Z : SchemeOver k}
    (g : X ⟶ Y) (i : Z ⟶ Y) (p : V ⟶ X) (z : V ⟶ Z)
    (hi : IsClosedImmersion i.left) (hp : Surjective p.left) (hX : IsReduced X.left)
    (h : p ≫ g = z ≫ i) : ∃ a : X ⟶ Z, a ≫ i = g := by
  let q := pullback.fst g.left i.left
  let r := pullback.snd g.left i.left
  have hh : p.left ≫ g.left = z.left ≫ i.left := congrArg Over.Hom.left h
  let v := pullback.lift p.left z.left hh
  letI : IsClosedImmersion q := MorphismProperty.pullback_fst _ _ hi
  have hv : v ≫ q = p.left := pullback.lift_fst _ _ _
  haveI : Surjective (v ≫ q) := hv.symm ▸ hp
  haveI : Surjective q := Surjective.of_comp v q
  haveI : IsIso q := isIso_of_isClosedImmersion_of_surjective q
  have h' : (inv q ≫ r) ≫ i.left = g.left := by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  have hc : (inv q ≫ r) ≫ Z.hom = X.hom := by
    rw [← Over.w i, ← Category.assoc, h', Over.w g]
  exact ⟨Over.homMk _ hc, Over.OverMorphism.ext h'⟩

set_option maxHeartbeats 2500000 in
private theorem faceTorusFactors {P : SplitBorelPair k} (D : AttachedDatum P) (I : Set (Root P.T))
    (S : SplitFace D I)
    (hSpan : letI := D.comm
      ∀ y : D.toBased.Y, (∃ c : Cocharacter S.torus.group, c ≫ S.toAmbientTorus = y.toMul) ↔
        y ∈ Submodule.span ℤ (D.datum.rootDatum.coroot '' I))
    (f : P.T.group ⟶ P.G.val)
    (hT : ∃ a : S.torus.group ⟶ P.T.group, S.toAmbientTorus ≫ f = a ≫ P.T.inclusion)
    (hZ : S.kernelTorus.inclusion ≫ f = S.kernelTorus.inclusion ≫ P.T.inclusion) :
    ∃ a : P.T.group ⟶ P.T.group, a ≫ P.T.inclusion = f := by
  letI := D.comm
  let t := P.T.inclusion
  obtain ⟨j, hj⟩ := hT
  letI : Group.FG IntegerCharacters := Group.fg_of_surjective
    (f := (MulEquiv.ulift.symm : Multiplicative ℤ ≃* IntegerCharacters).toMonoidHom)
    MulEquiv.ulift.symm.surjective
  let M := Specs.DiagonalizableGroups.diagonalGroup k IntegerCharacters
  letI : IsCommMonObj M.val.X := Specs.CharacterDescent.groupAlgebraSpectrumIsCommMonObj
  have hM : GeometricRadicals.IsTorus M.val := isTorus_of_split multiplicativeLine_split
  haveI : Smooth M.val.X.hom := torus_smooth M hM
  have hMred : IsReduced M.val.X.left := isReduced_of_smooth_over_field M.val.X.hom
  have hfactor (c : Cocharacter P.T.group) :
      ∃ d : M.val.X ⟶ P.T.group.X, d ≫ t.hom.hom = (c ≫ f).hom.hom := by
    obtain ⟨n, d, z, hn, hdz⟩ := face_cocharacter_decomposition S hSpan c
    let pow := CentralFrobeniusDescent.powerHom M.val n
    have hpow := (CentralFrobeniusDescent.torus_power_flat_surjective M hM n (Nat.ne_of_gt hn)).2
    have hp : pow ≫ c = c ^ n := by
      apply Grp.hom_ext
      change (CentralFrobeniusDescent.powerHom M.val n).hom.hom ≫ c.hom.hom = (c ^ n).hom.hom
      simp only [CentralFrobeniusDescent.powerHom, Grp.Hom.hom_pow, Mon.Hom.hom_pow, Grp.id_hom_hom]
      rw [MonObj.pow_comp, Category.id_comp]
    let s : M.val.X ⟶ P.T.group.X := (d ≫ j).hom.hom * (z ≫ S.kernelTorus.inclusion).hom.hom
    have heq : pow.hom.hom ≫ (c ≫ f).hom.hom = s ≫ t.hom.hom := by
      change ((pow ≫ c) ≫ f).hom.hom = _
      rw [hp, hdz]
      change ((d ≫ S.toAmbientTorus).hom.hom * (z ≫ S.kernelTorus.inclusion).hom.hom) ≫ f.hom.hom =
        s ≫ t.hom.hom
      have hd : (d ≫ S.toAmbientTorus) ≫ f = (d ≫ j) ≫ t := by
        rw [Category.assoc, hj, Category.assoc]
      have hz : (z ≫ S.kernelTorus.inclusion) ≫ f = (z ≫ S.kernelTorus.inclusion) ≫ t := by
        rw [Category.assoc, hZ, Category.assoc]
      simp only [s, MonObj.mul_comp, ← Grp.comp_hom_hom, hd, hz]
    exact closedFactorOfSurjective (c ≫ f).hom.hom t.hom.hom pow.hom.hom s
      P.T.isClosedImmersion hpow hMred heq
  obtain ⟨a, ha⟩ := (factorsThroughClosed_iff t.hom.hom P.T.isClosedImmersion f.hom.hom).mpr (by
    intro R r
    let S₀ := (onPoints t R).range.comap (onPoints f R)
    have htop : S₀ = ⊤ := subgroup_eq_top_of_cocharacters P.split R S₀ (fun c s => by
      obtain ⟨d, hd⟩ := hfactor c
      exact ⟨unitPoint R s ≫ d, by
        change (unitPoint R s ≫ d) ≫ t.hom.hom =
          (unitPoint R s ≫ c.hom.hom) ≫ f.hom.hom
        rw [Category.assoc, hd, Grp.comp_hom_hom, Category.assoc]⟩)
    have hr : r ∈ S₀ := htop.symm ▸ (Subgroup.mem_top r)
    exact hr)
  exact factor_group_through_subgroup P.T f a ha

private theorem faceNormalizer {P : SplitBorelPair k} (D : AttachedDatum P) (I : Set (Root P.T))
    (S : SplitFace D I)
    (hSpan : letI := D.comm
      ∀ y : D.toBased.Y, (∃ c : Cocharacter S.torus.group, c ≫ S.toAmbientTorus = y.toMul) ↔
        y ∈ Submodule.span ℤ (D.datum.rootDatum.coroot '' I))
    (x : 𝟙_ (SchemeOver k) ⟶ S.group.val.X)
    (hx : Normalizes S.torus.inclusion x)
    (centralizer : Centralizes (S.kernelTorus.inclusion ≫ P.T.inclusion) (x ≫ S.inclusion.hom.hom)) :
    Normalizes P.T.inclusion (x ≫ S.inclusion.hom.hom) := by
  letI := D.comm
  let g := x ≫ S.inclusion.hom.hom
  have hT (y : 𝟙_ (SchemeOver k) ⟶ S.group.val.X) (hy : Normalizes S.torus.inclusion y) :
      ∃ j : S.torus.group ⟶ P.T.group,
        S.toAmbientTorus ≫ (P.T.inclusion ≫ (conjugationIso (y ≫ S.inclusion.hom.hom)).hom) =
          j ≫ P.T.inclusion := by
    obtain ⟨e, he⟩ := conjugates_of_normalizes S.torus hy
    have eq := conjugatesSubgroups_square y e he
    refine ⟨e.hom ≫ S.toAmbientTorus, ?_⟩
    have hs := S.intersection.w
    change S.toAmbientTorus ≫ P.T.inclusion = S.torus.inclusion ≫ S.inclusion at hs
    have hn : S.inclusion ≫ (conjugationIso (y ≫ S.inclusion.hom.hom)).hom =
        (conjugationIso y).hom ≫ S.inclusion := by
      apply Grp.hom_ext
      change S.inclusion.hom.hom ≫ conjugate (y ≫ S.inclusion.hom.hom) (𝟙 _) =
        conjugate y (𝟙 _) ≫ S.inclusion.hom.hom
      rw [comp_conjugate, conjugate_comp, Category.id_comp, Category.comp_id]
    rw [← Category.assoc, hs, Category.assoc, hn, ← Category.assoc, eq, Category.assoc,
      ← hs, Category.assoc]
  have hZ (y : 𝟙_ (SchemeOver k) ⟶ P.G.val.X)
      (hy : Centralizes (S.kernelTorus.inclusion ≫ P.T.inclusion) y) :
      S.kernelTorus.inclusion ≫ (P.T.inclusion ≫ (conjugationIso y).hom) =
        S.kernelTorus.inclusion ≫ P.T.inclusion := by
    apply Grp.hom_ext
    rw [← Category.assoc, Grp.comp_hom_hom]
    change (S.kernelTorus.inclusion ≫ P.T.inclusion).hom.hom ≫ conjugate y (𝟙 _) =
      (S.kernelTorus.inclusion ≫ P.T.inclusion).hom.hom
    rw [comp_conjugate, Category.comp_id]
    have h := (centralizes_iff _ _).mp hy S.kernelTorus.group.X (toUnit _) (𝟙 _)
    simpa only [conjugate, rationalConstant, Category.id_comp] using (mul_inv_eq_iff_eq_mul.mpr h.eq)
  have hZ' : Centralizes (S.kernelTorus.inclusion ≫ P.T.inclusion) g⁻¹ := by
    apply (centralizes_iff _ _).mpr
    intro Y y z
    rw [GrpObj.comp_inv]
    exact ((centralizes_iff _ _).mp centralizer Y y z).inv_left
  obtain ⟨a, ha⟩ := faceTorusFactors D I S hSpan _ (hT x hx) (hZ g centralizer)
  obtain ⟨b, hb⟩ := faceTorusFactors D I S hSpan _ (by
    have h := hT x⁻¹ (normalizes_inv S.torus hx)
    rw [GrpObj.inv_comp] at h
    exact h) (hZ g⁻¹ hZ')
  letI : Mono P.T.inclusion := (Grp.forget (SchemeOver k)).mono_of_mono_map
    (mono_over P.T.inclusion.hom.hom P.T.isClosedImmersion)
  have hinv : (conjugationIso g).hom ≫ (conjugationIso g⁻¹).hom = 𝟙 _ :=
    (conjugationIso g).hom_inv_id
  have hinv' : (conjugationIso g⁻¹).hom ≫ (conjugationIso g).hom = 𝟙 _ :=
    (conjugationIso g).inv_hom_id
  have heq : a ≫ b = 𝟙 _ := by
    apply (cancel_mono P.T.inclusion).mp
    rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc, hinv, Category.comp_id, Category.id_comp]
  have heq' : b ≫ a = 𝟙 _ := by
    apply (cancel_mono P.T.inclusion).mp
    rw [Category.assoc, ha, ← Category.assoc, hb, Category.assoc, hinv', Category.comp_id, Category.id_comp]
  apply normalizes_of_conjugates_self P.T
  refine ⟨⟨a,b,heq,heq'⟩, ?_⟩
  change (a ≫ P.T.inclusion).hom.hom = conjugate g P.T.inclusion.hom.hom
  rw [ha]
  change P.T.inclusion.hom.hom ≫ conjugate g (𝟙 _) = _
  rw [comp_conjugate, Category.comp_id]

end

/-- Scheme normalization is unchanged by a change of presentation of a point's domain. -/
private theorem normalizes_precomp_iso {k : Type u} [Field k]
    {G : GroupScheme k} (T : ClosedSubgroup G)
    {X Y : SchemeOver k} (e : X ≅ Y) (g : Y ⟶ G.X) :
    Normalizes T.inclusion (e.hom ≫ g) ↔ Normalizes T.inclusion g := by
  rw [normalizes_iff_sections, normalizes_iff_sections]
  constructor
  · intro h R t u
    specialize h R (t ≫ e.inv) u
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h
  · intro h R t u
    simpa only [Category.assoc] using h R (t ≫ e.hom) u

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1800000 in
/-- The normalizer of the derived face torus maps to the normalizer of the
full ambient torus. The condition can be checked on the given split face. -/
theorem rationalFaceNormalizerTransfer : RationalFaceNormalizerTransfer.{u} := by
  intro F K _ _ _ G T B P D I L x hx
  let C := groupBaseChange F K
  let S := L.splitFace D
  let e := groundPointIso K
  let y := extendPoint (K := K) L.derived.group x
  let z : 𝟙_ (SchemeOver K) ⟶ S.group.val.X := e.hom ≫ y
  have he : C.map (L.derived.inclusion ≫ L.limit.centralizer.inclusion) = S.inclusion := by
    change C.map (L.derived.inclusion ≫ L.limit.centralizer.inclusion) =
      (C.map L.derived.inclusion ≫ L.comparison.hom) ≫ L.splitLimit.centralizer.inclusion
    rw [C.map_comp, Category.assoc, L.comparisonSquare]
  have hz : Normalizes S.torus.inclusion z :=
    (normalizes_precomp_iso S.torus e y).mpr hx
  have hc : Centralizes (S.kernelTorus.inclusion ≫ P.pair.T.inclusion) (z ≫ S.inclusion.hom.hom) :=
    (S.centralizer _ _).mpr ⟨z ≫ S.derived.inclusion.hom.hom, Category.assoc _ _ _⟩
  have hg := faceNormalizer D I S L.integralImage z hz hc
  apply normalizes_of_extended (K := K)
  rw [extendPoint_natural, he]
  have hg' := (normalizes_precomp_iso P.pair.T e (onRational S.inclusion y)).mp (by
    change Normalizes P.pair.T.inclusion (e.hom ≫ y ≫ S.inclusion.hom.hom)
    simpa only [z, Category.assoc] using hg)
  exact hg'

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1100000 in
theorem longestFaceLabelFromCoroots : LongestFaceLabelFromCoroots.{u} := by
  intro F K _ _ _ O A
  letI := A.comm
  let P := A.rootDatum
  intro c lam hc hb hf w hw π he
  have hm := (face_stabilizes_cocharacter hc hb hf A.W w).mp hw
  apply longest_of_simple_images A w hm
  intro i
  refine ⟨π i, ?_⟩
  let e := w.val
  let j := e.indexEquiv i.val
  let r := P.reflectionPerm (π i).val (π i).val
  have h1 : e.coweightEquiv (P.coroot j) = P.coroot i.val := by
    have h := e.toHom.coroot_coweightMap_apply P P j
    change e.coweightEquiv (P.coroot j) = P.coroot (e.indexEquiv.symm j) at h
    simpa only [j, e.indexEquiv.symm_apply_apply] using h
  have h2 : P.coroot j = P.coroot r := by
    change P.coroot j = P.coroot (P.reflectionPerm (π i).val (π i).val)
    rw [show P.coroot j = e.coweightEquiv.symm (P.coroot i.val) from
      (e.coweightEquiv.symm_apply_eq.mpr h1.symm).symm, he i,
      RootPairing.coroot_reflectionPerm, RootPairing.coreflection_apply_self]
  have h3 : e.weightEquiv (P.root i.val) = P.root j :=
    e.toHom.root_weightMap_apply P P i.val
  rw [h3, P.coroot.injective h2]
  change P.root (P.reflectionPerm (π i).val (π i).val) = _
  rw [RootPairing.root_reflectionPerm,
    RootPairing.reflection_apply_self]

end FaceNormalizer

end OrbitAssembly

section PinnedComparisonRigidity

open _root_.LinearAlgebraicGroups.Specs
open Opposite
open CategoryTheory.Limits
open Specs.Pinning (PinnedGroup PinnedIso AttachedDatum SimpleRoot BasedIso transportCharacter)
open Specs.RootGroups (AdditiveLine rootPoint)
open Specs.QuasiSplitOrbitDerivedRoots (pinnedRootMap coefficientAction comparedAction)
open Specs.CharacterDescent (Cocharacter Character)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.PinnedUniqueness (scalarGroupPoints)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterPairing (pairing)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open LinearAlgebraicGroups.Classification.Pinning (inducedBasedIso)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open private twistMorphism twistedBaseChange twistedBaseChange_inv
  from LinearAlgebraicGroups.Relative.RationalCocharacter
open private fieldConjugation_fst fieldConjugation_snd
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitTorusProduct
open private coefficientAction_naturality
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitDerivedRoots
open private rootPoint_comp from LinearAlgebraicGroups.RootData.RootGroups
open private coroot_transport rootEquiv from LinearAlgebraicGroups.Classification.Pinning
open private pinnedLifts from LinearAlgebraicGroups.Descent.AutomorphismSequence

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option linter.style.haveILetI false

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

private abbrev schemeHom {k : Type u} [Field k] {X Y : GroupScheme k} (f : X ⟶ Y) :=
  f.hom.hom.left

private theorem twistMorphism_square (σ : Gal(K/F)) {X Y : GroupScheme F}
    (f : (groupBaseChange F K).obj X ⟶ (groupBaseChange F K).obj Y) :
    schemeHom (twistMorphism σ f) =
      coefficientAction σ⁻¹ X ≫ schemeHom f ≫ coefficientAction σ Y := by
  change (twistedBaseChange σ X).inv.hom.hom.left ≫ _ ≫ _ = _
  rw [twistedBaseChange_inv]
  rfl

private theorem coefficientAction_inv_hom (σ : Gal(K/F)) (X : GroupScheme F) :
    coefficientAction σ⁻¹ X ≫ coefficientAction σ X = 𝟙 _ := by
  let Z := ((groupBaseChange F K).obj X).X.left
  let e := (Grp.forget (SchemeOver K) ⋙ Over.forget _).mapIso (twistedBaseChange σ X)
  have h : e.inv ≫ e.hom = 𝟙 _ := e.inv_hom_id
  change (twistedBaseChange σ X).inv.hom.hom.left ≫ (twistedBaseChange σ X).hom.hom.hom.left =
    𝟙 Z at h
  rw [twistedBaseChange_inv] at h
  exact h

private theorem coefficientAction_hom_inv (σ : Gal(K/F)) (X : GroupScheme F) :
    coefficientAction σ X ≫ coefficientAction σ⁻¹ X = 𝟙 _ := by
  simpa only [inv_inv] using coefficientAction_inv_hom σ⁻¹ X

private theorem twist_eq_iff (σ : Gal(K/F)) {X Y : GroupScheme F}
    (f g : (groupBaseChange F K).obj X ⟶ (groupBaseChange F K).obj Y) :
    twistMorphism σ f = g ↔
      schemeHom f ≫ coefficientAction σ Y = coefficientAction σ X ≫ schemeHom g := by
  constructor
  · intro h
    have h' := congrArg (fun r => coefficientAction σ X ≫ schemeHom r) h
    rw [twistMorphism_square, ← Category.assoc, coefficientAction_hom_inv, Category.id_comp] at h'
    exact h'
  · intro h
    apply Grp.hom_ext
    apply Over.OverMorphism.ext
    change schemeHom (twistMorphism σ f) = schemeHom g
    rw [twistMorphism_square, h, ← Category.assoc, coefficientAction_inv_hom, Category.id_comp]

private theorem twistMorphism_comp (σ : Gal(K/F)) {X Y Z : GroupScheme F}
    (f : (groupBaseChange F K).obj X ⟶ (groupBaseChange F K).obj Y)
    (g : (groupBaseChange F K).obj Y ⟶ (groupBaseChange F K).obj Z) :
    twistMorphism σ (f ≫ g) = twistMorphism σ f ≫ twistMorphism σ g := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  change schemeHom (twistMorphism σ (f ≫ g)) =
    schemeHom (twistMorphism σ f) ≫ schemeHom (twistMorphism σ g)
  rw [twistMorphism_square, twistMorphism_square, twistMorphism_square]
  change coefficientAction σ⁻¹ X ≫ (schemeHom f ≫ schemeHom g) ≫ coefficientAction σ Z =
    (coefficientAction σ⁻¹ X ≫ schemeHom f ≫ coefficientAction σ Y) ≫
      coefficientAction σ⁻¹ Y ≫ schemeHom g ≫ coefficientAction σ Z
  simp only [Category.assoc, reassoc_of% (coefficientAction_hom_inv σ Y)]

private theorem twistMorphism_ground (σ : Gal(K/F)) {X Y : GroupScheme F} (f : X ⟶ Y) :
    twistMorphism σ ((groupBaseChange F K).map f) = (groupBaseChange F K).map f := by
  apply (twist_eq_iff σ _ _).mpr
  exact (coefficientAction_naturality σ f).symm

private theorem postcomp_torus_ext {k : Type u} [Field k] {S T : GroupScheme k}
    (hS : IsSplitTorus S) (hT : IsSplitTorus T)
    {f g : S ⟶ T} (same : ∀ c : Cocharacter S, c ≫ f = c ≫ g) : f = g := by
  obtain ⟨hcomm, _, _, _, _, P, hperf, hpair⟩ :=
    RootData.CharacterPairing.perfectCharacterPairing S hS
  letI := hcomm
  letI := hperf
  have hchar (χ : Character T) : f ≫ χ = g ≫ χ := by
    apply Additive.ofMul.injective
    apply P.toPerfPair.injective
    ext y
    change P (Additive.ofMul (f ≫ χ)) y = P (Additive.ofMul (g ≫ χ)) y
    change P _ (Additive.ofMul y.toMul) = P _ (Additive.ofMul y.toMul)
    rw [hpair, hpair]
    unfold pairing Specs.CharacterDescent.compositionPairing
    rw [← Category.assoc, ← Category.assoc, same y.toMul]
  have hAff : IsAffine S.X.left := by
    obtain ⟨r, ⟨e⟩⟩ := hS
    letI := (Specs.StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin r))).property.1
    letI : IsIso e.hom.hom.hom.left :=
      (Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))).map_isIso e.hom
    exact IsAffine.of_isIso e.hom.hom.hom.left
  apply (groupHomComparison k S T hAff).1
  ext R x
  apply Classification.PinnedUniqueness.charactersSeparatePoints hT R
  intro χ
  change (x ≫ f.hom.hom) ≫ χ.hom.hom = (x ≫ g.hom.hom) ≫ χ.hom.hom
  simp only [Category.assoc, ← Grp.comp_hom_hom, hchar]

private theorem pinnedRootMaps_ext {k : Type u} [Field k] {A : AdditiveLine k}
    (P : PinnedGroup A) {G : GroupScheme k} (f g : P.pair.G.val ≅ G)
    (hT : P.pair.T.inclusion ≫ f.hom = P.pair.T.inclusion ≫ g.hom)
    (hp : ∀ i, pinnedRootMap P.pin i ≫ f.hom = pinnedRootMap P.pin i ≫ g.hom) :
    f.hom = g.hom := by
  let R := CommAlgCat.of k k
  let d := f.hom ≫ g.inv
  let h := (groupPointsFunctor k).map d
  let n := Functor.whiskerLeft (Under.forget R) h
  have hT' : P.pair.T.inclusion ≫ d = P.pair.T.inclusion := by
    rw [← Category.assoc, hT, Category.assoc, g.hom_inv_id, Category.comp_id]
  have hP' (i : SimpleRoot P.pair) : pinnedRootMap P.pin i ≫ d = pinnedRootMap P.pin i := by
    rw [← Category.assoc, hp, Category.assoc, g.hom_inv_id, Category.comp_id]
  have e : n = 𝟙 _ := Classification.PinnedUniqueness.scalarRigidity P R n
    (by
      intro U t
      change (t ≫ P.pair.T.inclusion.hom.hom) ≫ d.hom.hom = t ≫ P.pair.T.inclusion.hom.hom
      rw [Category.assoc, ← Grp.comp_hom_hom, hT'])
    (by
      intro U α a
      change rootPoint (pinnedRootMap P.pin α) U.right a ≫ d.hom.hom =
        rootPoint (pinnedRootMap P.pin α) U.right a
      rw [← rootPoint_comp, hP'])
  have hd : d = 𝟙 _ := by
    apply (groupHomComparison k _ _ P.pair.G.property.1).1
    ext S x
    let u : R ⟶ S := CommAlgCat.ofHom (Algebra.ofId k S)
    have E := congrArg (fun v : scalarGroupPoints R P.pair.G.val ⟶ _ =>
      (v.app (Under.mk u)).hom x) e
    change x ≫ d.hom.hom = x at E
    change x ≫ d.hom.hom = x ≫ ((𝟙 P.pair.G.val) : P.pair.G.val ⟶ P.pair.G.val).hom.hom
    simpa only [Grp.id_hom_hom, Category.comp_id] using E
  apply (cancel_mono g.inv).mp
  rw [g.hom_inv_id]
  exact hd

private theorem pinnedRootMap_transport {k : Type u} [Field k] {A : AdditiveLine k}
    {P Q : PinnedGroup A} (f : PinnedIso P Q) (i : SimpleRoot P.pair) (j : SimpleRoot Q.pair)
    (h : transportCharacter f.torus i.val.val = j.val.val) :
    pinnedRootMap P.pin i ≫ f.group.hom = pinnedRootMap Q.pin j := by
  have he : (transportCharacter f.torus i.val.val, pinnedRootMap P.pin i ≫ f.group.hom) ∈
      Specs.Pinning.pinGraph Q := by
    rw [← f.pin_comm]
    exact ⟨_, ⟨i, rfl⟩, rfl⟩
  obtain ⟨j', hj'⟩ := he
  have e : j' = j := Subtype.ext (Subtype.ext ((congrArg Prod.fst hj').trans h))
  subst j'
  exact (congrArg Prod.snd hj').symm

end PinnedComparisonRigidity

section PinnedCoefficientCompatibility

open _root_.LinearAlgebraicGroups.Specs
open Opposite
open CategoryTheory.Limits
open Specs.Pinning (PinnedGroup PinnedIso AttachedDatum SimpleRoot BasedIso transportCharacter)
open Specs.RootGroups (AdditiveLine rootPoint)
open Specs.QuasiSplitOrbitDerivedRoots (pinnedRootMap coefficientAction comparedAction)
open Specs.CharacterDescent (Cocharacter Character)
open Specs.QuasiSplitOrbitLevis (MultiplicativeComparison)
open Specs.RootGroups (HasScalarAction)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open LinearAlgebraicGroups.Classification.Pinning (inducedBasedIso)
open private twistMorphism from LinearAlgebraicGroups.Relative.RationalCocharacter
open private coefficientAction_naturality from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitDerivedRoots
open private rootPoint_comp rootPoint_eq from LinearAlgebraicGroups.RootData.RootGroups
open private additiveIso_linear coroot_transport rootEquiv from LinearAlgebraicGroups.Classification.Pinning
open private pinnedLifts from LinearAlgebraicGroups.Descent.AutomorphismSequence

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.style.haveILetI false

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

private theorem scalarAction_reparametrize {k : Type u} [Field k] {A A' : AdditiveLine k}
    {G : GroupScheme k} {T : ClosedSubgroup G} {χ : Character T.group}
    (e : A'.group ≅ A.group) (x : A.group ⟶ G) (hx : HasScalarAction T χ x) :
    HasScalarAction T χ (e.hom ≫ x) := by
  obtain ⟨c, hc⟩ := additiveIso_linear A' A e
  intro R t a
  have h (b : R) : rootPoint (e.hom ≫ x) R b =
      rootPoint x R (algebraMap k R (c : k) * b) := by
    rw [rootPoint_comp, hc, rootPoint_eq]
  let g : AdjointRepresentation.GroupPoints G R := t ≫ T.inclusion.hom.hom
  change g * rootPoint (e.hom ≫ x) R a * g⁻¹ =
    rootPoint (e.hom ≫ x) R (Specs.CharacterPairing.characterValue χ R t * a)
  rw [h, h]
  rw [hx R t (algebraMap k R (c : k) * a)]
  congr 1
  ring

private def reparametrizePin {k : Type u} [Field k] {A A' : AdditiveLine k}
    (P : PinnedGroup A) (e : A'.group ≅ A.group) : PinnedGroup A' where
  pair := P.pair
  roots := P.roots
  pin i := ⟨e ≪≫ (P.pin i).val, by
    change HasScalarAction P.pair.T i.val.val
      ((e.hom ≫ (P.pin i).val.hom) ≫ (P.roots i.val).val.inclusion)
    rw [Category.assoc]
    exact scalarAction_reparametrize e _ (P.pin i).property⟩

private theorem reparametrizeRootMap {k : Type u} [Field k] {A A' : AdditiveLine k}
    (P : PinnedGroup A) (e : A'.group ≅ A.group) (i : SimpleRoot P.pair) :
    pinnedRootMap (reparametrizePin P e).pin i = e.hom ≫ pinnedRootMap P.pin i :=
  Category.assoc _ _ _

private theorem liftOfAttachedDatum {k : Type u} [Field k] {A : AdditiveLine k}
    (P : PinnedGroup A) (D : AttachedDatum P.pair) :
    ∃ l : Aut D.toBased ≃* Aut P, ∀ d : Aut D.toBased,
      inducedBasedIso (l d).asIso.hom D D = d.asIso.hom := by
  obtain ⟨E, l, h⟩ := pinnedLifts P
  let e : D.toBased ≅ E.toBased := asIso (inducedBasedIso (PinnedIso.refl P) D E)
  let v := Aut.autMulEquivOfIso e
  refine ⟨v.trans l, fun d => ?_⟩
  let f := (l (v d)).asIso.hom
  have he (x : D.toBased.X) :
      e.hom.val.weightEquiv x = (Additive.ofMul x.toMul : E.toBased.X) := by
    change Additive.ofMul ((𝟙 P.pair.T.group) ≫ x.toMul) = Additive.ofMul x.toMul
    exact congrArg Additive.ofMul (Category.id_comp _)
  have hei (x : E.toBased.X) :
      e.inv.val.weightEquiv x = (Additive.ofMul x.toMul : D.toBased.X) := by
    have hh := congrArg (fun b : E.toBased ⟶ E.toBased => b.val.weightEquiv x) e.inv_hom_id
    change e.hom.val.weightEquiv (e.inv.val.weightEquiv x) = x at hh
    exact Additive.ofMul.injective ((he (e.inv.val.weightEquiv x)).symm.trans hh) |> congrArg Additive.ofMul
  apply Subtype.ext
  apply RootPairing.Equiv.weightHom_injective D.toBased.datum
  ext z
  let χ : Character P.pair.T.group := z.toMul
  change Additive.ofMul (transportCharacter f.torus χ) = d.asIso.hom.val.weightEquiv z
  have hd := (h (v d)).1 χ
  change e.hom.val.weightEquiv (d.asIso.hom.val.weightEquiv
      (e.inv.val.weightEquiv (Additive.ofMul χ))) =
        Additive.ofMul (transportCharacter f.torus χ) at hd
  exact hd.symm.trans (by
    have hi := congrArg d.asIso.hom.val.weightEquiv (hei (Additive.ofMul χ))
    exact (congrArg e.hom.val.weightEquiv hi).trans (he (d.asIso.hom.val.weightEquiv z)))

/-- Galois equivariance follows from the effect on the actual coroot basis
and on the labelled simple root morphisms. -/
private theorem pinnedComparisonEquivariant {A : AdditiveLine K} {A₀ : AdditiveLine F}
    (Q : PinnedGroup A) (D : AttachedDatum Q.pair) (P : PinnedGroup A₀)
    {H S N : GroupScheme F}
    (h : (groupBaseChange F K).obj H ≅ Q.pair.G.val)
    (s : (groupBaseChange F K).obj S ≅ Q.pair.T.group)
    (i : S ⟶ H)
    (hs : (groupBaseChange F K).map i ≫ h.hom = s.hom ≫ Q.pair.T.inclusion)
    (e : MultiplicativeComparison F K)
    (a : (groupBaseChange F K).obj N ≅ A.group)
    (g : (groupBaseChange F K).obj H ≅ (groupBaseChange F K).obj P.pair.G.val)
    (t : (groupBaseChange F K).obj S ≅ (groupBaseChange F K).obj P.pair.T.group)
    (ht : (groupBaseChange F K).map i ≫ g.hom = t.hom ≫ (groupBaseChange F K).map P.pair.T.inclusion)
    (σ : Gal(K/F)) (f : PinnedIso P P) (π : Equiv.Perm (SimpleRoot Q.pair))
    (hcomm : IsCommMonObj ((groupBaseChange F K).obj P.pair.T.group).X)
    (hsp : IsSplitTorus ((groupBaseChange F K).obj P.pair.T.group))
    (basis : letI := D.comm; Module.Basis (SimpleRoot Q.pair) ℤ
      (Additive (Cocharacter Q.pair.T.group)))
    (hb : letI := D.comm; ∀ j, basis j = Additive.ofMul (simpleCorootOfAttachedDatum Q D j))
    (hcor : ∀ j, twistMorphism σ (e.inv ≫ simpleCorootOfAttachedDatum Q D (π j) ≫ s.inv) =
      e.inv ≫ simpleCorootOfAttachedDatum Q D j ≫ s.inv)
    (hp : ∀ j, twistMorphism σ (a.hom ≫ pinnedRootMap Q.pin (π j) ≫ h.inv) =
      a.hom ≫ pinnedRootMap Q.pin j ≫ h.inv)
    (hcor₀ : ∀ j, ∃ y : Cocharacter P.pair.T.group,
      e.inv ≫ simpleCorootOfAttachedDatum Q D (π j) ≫ s.inv ≫ t.hom = (groupBaseChange F K).map y)
    (hp₀ : ∀ j, ∃ x : N ⟶ P.pair.G.val,
      a.hom ≫ pinnedRootMap Q.pin (π j) ≫ h.inv ≫ g.hom = (groupBaseChange F K).map x)
    (hcor_f : ∀ j,
      simpleCorootOfAttachedDatum Q D j ≫ s.inv ≫ t.hom ≫ (groupBaseChange F K).map f.torus.hom =
        simpleCorootOfAttachedDatum Q D (π j) ≫ s.inv ≫ t.hom)
    (hp_f : ∀ j,
      pinnedRootMap Q.pin j ≫ h.inv ≫ g.hom ≫ (groupBaseChange F K).map f.group.hom =
        pinnedRootMap Q.pin (π j) ≫ h.inv ≫ g.hom) :
    coefficientAction σ H ≫ schemeHom g.hom =
      schemeHom g.hom ≫ schemeHom ((groupBaseChange F K).map f.group.inv) ≫
        coefficientAction σ P.pair.G.val := by
  letI := D.comm
  letI := hcomm
  let C := groupBaseChange F K
  have ht' : twistMorphism σ t.hom = t.hom ≫ C.map f.torus.hom := by
    apply (cancel_epi s.inv).1
    apply postcomp_torus_ext Q.pair.split hsp
    let c (j : SimpleRoot Q.pair) := simpleCorootOfAttachedDatum Q D j
    have hsame (j : SimpleRoot Q.pair) :
        c j ≫ s.inv ≫ twistMorphism σ t.hom =
          c j ≫ s.inv ≫ t.hom ≫ C.map f.torus.hom := by
      obtain ⟨y, hy⟩ := hcor₀ j
      have hc : (e.inv ≫ c j ≫ s.inv) ≫ twistMorphism σ t.hom = C.map y := by
        rw [← hcor j, ← twistMorphism_comp, Category.assoc, Category.assoc, hy, twistMorphism_ground]
      apply (cancel_epi e.inv).mp
      simp only [Category.assoc] at hc
      change e.inv ≫ c j ≫ s.inv ≫ twistMorphism σ t.hom =
        e.inv ≫ (c j ≫ s.inv ≫ t.hom ≫ C.map f.torus.hom)
      exact hc.trans (((congrArg (e.inv ≫ ·) (hcor_f j)).trans hy).symm)
    let a' := s.inv ≫ twistMorphism σ t.hom
    let b' := s.inv ≫ t.hom ≫ C.map f.torus.hom
    let post (f : Q.pair.T.group ⟶ C.obj P.pair.T.group) :
        Additive (Cocharacter Q.pair.T.group) →ₗ[ℤ]
          Additive (Cocharacter (C.obj P.pair.T.group)) :=
      AddMonoidHom.toIntLinearMap
        { toFun := fun y => Additive.ofMul (y.toMul ≫ f)
          map_zero' := congrArg Additive.ofMul (show (0 : Cocharacter Q.pair.T.group) ≫ f = 0 from zero_comp)
          map_add' := fun _ _ => Grp.hom_ext _ _ (MonObj.mul_comp _ _ _) }
    have hlinear : post a' = post b' := by
      apply basis.ext
      intro j
      rw [hb]
      exact congrArg Additive.ofMul (hsame j)
    intro y
    exact Additive.ofMul.injective (DFunLike.congr_fun hlinear (Additive.ofMul y))
  have hg' : twistMorphism σ g.hom = g.hom ≫ C.map f.group.hom := by
    haveI : IsIso (twistMorphism σ g.hom) := by
      unfold twistMorphism
      infer_instance
    let u := h.symm ≪≫ asIso (twistMorphism σ g.hom)
    let v := h.symm ≪≫ g ≪≫ C.mapIso f.group
    have htu : Q.pair.T.inclusion ≫ h.inv = s.inv ≫ C.map i := by
      apply (cancel_epi s.hom).mp
      simp only [Iso.hom_inv_id_assoc]
      rw [← Category.assoc, ← hs, Category.assoc, h.hom_inv_id, Category.comp_id]
    have h1 : Q.pair.T.inclusion ≫ u.hom = Q.pair.T.inclusion ≫ v.hom := by
      change Q.pair.T.inclusion ≫ h.inv ≫ twistMorphism σ g.hom =
        Q.pair.T.inclusion ≫ h.inv ≫ g.hom ≫ C.map f.group.hom
      rw [← Category.assoc Q.pair.T.inclusion, ← Category.assoc Q.pair.T.inclusion, htu]
      have h' : C.map i ≫ twistMorphism σ g.hom =
          (t.hom ≫ C.map f.torus.hom) ≫ C.map P.pair.T.inclusion := by
        calc
          _ = twistMorphism σ (C.map i ≫ g.hom) := by
            rw [twistMorphism_comp, twistMorphism_ground]
          _ = _ := by
            rw [ht, twistMorphism_comp, twistMorphism_ground, ht']
      have h'' : (t.hom ≫ C.map f.torus.hom) ≫ C.map P.pair.T.inclusion =
          C.map i ≫ g.hom ≫ C.map f.group.hom := by
        rw [Category.assoc, ← C.map_comp, ← f.torus_comm, C.map_comp, ← Category.assoc, ← ht,
          Category.assoc]
      simpa only [Category.assoc] using congrArg (s.inv ≫ ·) (h'.trans h'')
    have h2 (j : SimpleRoot Q.pair) : pinnedRootMap Q.pin j ≫ u.hom = pinnedRootMap Q.pin j ≫ v.hom := by
      obtain ⟨x, hx⟩ := hp₀ j
      have h' : (a.hom ≫ pinnedRootMap Q.pin j ≫ h.inv) ≫ twistMorphism σ g.hom = C.map x := by
        rw [← hp j, ← twistMorphism_comp, Category.assoc, Category.assoc, hx, twistMorphism_ground]
      apply (cancel_epi a.hom).mp
      change a.hom ≫ pinnedRootMap Q.pin j ≫ h.inv ≫ twistMorphism σ g.hom =
        a.hom ≫ pinnedRootMap Q.pin j ≫ h.inv ≫ g.hom ≫ C.map f.group.hom
      rw [hp_f, hx]
      simpa only [Category.assoc] using h'
    exact (cancel_epi h.inv).mp (pinnedRootMaps_ext Q u v h1 h2)
  have h' := (twist_eq_iff σ _ _).mp hg'
  change schemeHom g.hom ≫ coefficientAction σ P.pair.G.val =
    coefficientAction σ H ≫ schemeHom g.hom ≫ schemeHom (C.map f.group.hom) at h'
  have eq := congrArg (fun q => q ≫ schemeHom (C.map f.group.inv)) h'
  have hC := coefficientAction_naturality (F := F) (K := K) σ f.group.inv
  have hinv : schemeHom (C.map f.group.hom) ≫ schemeHom (C.map f.group.inv) = 𝟙 _ := by
    change schemeHom (C.map f.group.hom ≫ C.map f.group.inv) = 𝟙 _
    rw [← C.map_comp, f.group.hom_inv_id, C.map_id]
    rfl
  calc
    _ = (coefficientAction σ H ≫ schemeHom g.hom ≫ schemeHom (C.map f.group.hom)) ≫
        schemeHom (C.map f.group.inv) := by
      rw [Category.assoc, Category.assoc, hinv]
      exact congrArg (coefficientAction σ H ≫ ·) (Category.comp_id _).symm
    _ = (schemeHom g.hom ≫ coefficientAction σ P.pair.G.val) ≫ schemeHom (C.map f.group.inv) :=
      eq.symm
    _ = _ := by
      rw [Category.assoc]
      exact congrArg (schemeHom g.hom ≫ ·) hC

private theorem twistOfMarkedMorphism {X Y : GroupScheme F} {X' Y' : GroupScheme K}
    (σ : Gal(K/F)) (a : (groupBaseChange F K).obj X ≅ X')
    (b : (groupBaseChange F K).obj Y ≅ Y') (f g : X' ⟶ Y')
    (h : comparedAction σ⁻¹ a ≫ schemeHom g = schemeHom f ≫ comparedAction σ⁻¹ b) :
    twistMorphism σ (a.hom ≫ g ≫ b.inv) = a.hom ≫ f ≫ b.inv := by
  let U := Grp.forget (SchemeOver K) ⋙ Over.forget (Spec (CommRingCat.of K))
  have ha : schemeHom a.hom ≫ schemeHom a.inv = 𝟙 _ := (U.mapIso a).hom_inv_id
  have hb : schemeHom b.hom ≫ schemeHom b.inv = 𝟙 _ := (U.mapIso b).hom_inv_id
  have e := congrArg (fun z => (schemeHom a.hom ≫ z) ≫ schemeHom b.inv) h
  change (schemeHom a.hom ≫ (schemeHom a.inv ≫ coefficientAction σ⁻¹ X ≫
      schemeHom a.hom) ≫ schemeHom g) ≫ schemeHom b.inv =
    (schemeHom a.hom ≫ schemeHom f ≫ schemeHom b.inv ≫
       coefficientAction σ⁻¹ Y ≫ schemeHom b.hom) ≫ schemeHom b.inv at e
  have e' : coefficientAction σ⁻¹ X ≫ schemeHom a.hom ≫ schemeHom g ≫ schemeHom b.inv =
      schemeHom a.hom ≫ schemeHom f ≫ schemeHom b.inv ≫ coefficientAction σ⁻¹ Y := by
    simp only [Category.assoc, reassoc_of% ha, hb] at e
    exact e.trans (congrArg (fun z => schemeHom a.hom ≫ schemeHom f ≫ schemeHom b.inv ≫ z)
      (Category.comp_id (coefficientAction σ⁻¹ Y)))
  apply (twist_eq_iff σ _ _).2
  have e'' := congrArg (fun z => (coefficientAction σ X ≫ z) ≫ coefficientAction σ Y) e'
  have hx := coefficientAction_hom_inv σ X
  have hy := coefficientAction_hom_inv σ⁻¹ Y
  simp only [inv_inv] at hy
  change (schemeHom a.hom ≫ schemeHom g ≫ schemeHom b.inv) ≫ coefficientAction σ Y =
    coefficientAction σ X ≫ schemeHom a.hom ≫ schemeHom f ≫ schemeHom b.inv
  simp only [Category.assoc, reassoc_of% hx, hy] at e''
  exact e''.trans (congrArg (fun z => coefficientAction σ X ≫ schemeHom a.hom ≫ schemeHom f ≫ z)
    (Category.comp_id (schemeHom b.inv)))

end PinnedCoefficientCompatibility

section BasedPinningTransport

open _root_.LinearAlgebraicGroups.Specs
open Opposite
open CategoryTheory.Limits
open Specs.Pinning (PinnedGroup PinnedIso AttachedDatum SimpleRoot BasedIso transportCharacter)
open Specs.RootGroups (AdditiveLine rootPoint)
open Specs.QuasiSplitOrbitDerivedRoots (pinnedRootMap)
open Specs.QuasiSplitOrbitLevis (MultiplicativeComparison PreservesUnits)
open Specs.CharacterDescent (Cocharacter Character)
open Specs.RationalRealization (Realization)
open LinearAlgebraicGroups.Classification.Pinning (inducedBasedIso)
open private pinnedLift from LinearAlgebraicGroups.Classification.PinnedEquivalence
open private additiveLineIso from LinearAlgebraicGroups.RootData.RootGroups

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

private theorem realization_coroot {k : Type u} [Field k] {A : AdditiveLine k}
    {D : Specs.Pinning.BasedRootDatum.{u}} (P : Realization D A) (j : D.base.support) :
    letI := P.attached.comm
    P.datumIso.val.coweightEquiv.symm (D.datum.coroot j.val) =
      (P.attached.datum.rootDatum.coroot (P.simpleRoot j).val) := by
  letI := P.attached.comm
  apply P.datumIso.val.coweightEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  have h := P.datumIso.val.toHom.coroot_coweightMap_apply D.datum P.attached.toBased.datum
    (P.datumIso.val.indexEquiv j.val)
  change P.datumIso.val.coweightEquiv
      (P.attached.datum.rootDatum.coroot (P.simpleRoot j).val) =
      D.datum.coroot (P.datumIso.val.indexEquiv.symm (P.datumIso.val.indexEquiv j.val)) at h
  rw [Equiv.symm_apply_apply] at h
  exact h.symm

private theorem pinsOfBasedIso {k : Type u} [Field k] {A : AdditiveLine k}
    {P Q : PinnedGroup A} {D : AttachedDatum P.pair} {E : AttachedDatum Q.pair}
    (f : PinnedIso P Q) (e : BasedIso D.toBased E.toBased)
    (h : inducedBasedIso f D E = e) (i : SimpleRoot P.pair) (j : SimpleRoot Q.pair)
    (hij : e.val.indexEquiv i.val = j.val) :
    transportCharacter f.torus i.val.val = j.val.val ∧
    pinnedRootMap P.pin i ≫ f.group.hom = pinnedRootMap Q.pin j ∧
    simpleCorootOfAttachedDatum P D i ≫ f.torus.hom = simpleCorootOfAttachedDatum Q E j := by
  have hroot := congrArg (fun e : BasedIso D.toBased E.toBased => e.val.indexEquiv i.val) h
  change (⟨transportCharacter f.torus i.val.val, _⟩ : Specs.AbstractPairing.Root Q.pair.T) =
    e.val.indexEquiv i.val at hroot
  have hχ : transportCharacter f.torus i.val.val = j.val.val :=
    congrArg Subtype.val (hroot.trans hij)
  refine ⟨hχ, pinnedRootMap_transport f i j hχ, ?_⟩
  have hc := congrArg (fun e' : BasedIso D.toBased E.toBased =>
    e'.val.coweightEquiv (E.toBased.datum.coroot j.val)) h
  change Additive.ofMul (simpleCorootOfAttachedDatum Q E j ≫ f.torus.inv) =
    e.val.coweightEquiv (E.toBased.datum.coroot j.val) at hc
  have h' := e.val.toHom.coroot_coweightMap_apply D.toBased.datum E.toBased.datum j.val
  change e.val.coweightEquiv (E.toBased.datum.coroot j.val) =
    D.toBased.datum.coroot (e.val.indexEquiv.symm j.val) at h'
  have hback : e.val.indexEquiv.symm j.val = i.val := by
    apply e.val.indexEquiv.injective
    exact (e.val.indexEquiv.apply_symm_apply j.val).trans hij.symm
  rw [hback] at h'
  have hy : simpleCorootOfAttachedDatum Q E j ≫ f.torus.inv = simpleCorootOfAttachedDatum P D i :=
    congrArg Additive.toMul (hc.trans h')
  apply (cancel_mono f.torus.inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact hy.symm

end BasedPinningTransport

section FibreMarkEquations

open _root_.LinearAlgebraicGroups.Specs
open Opposite
open CategoryTheory.Limits
open Specs.Pinning (PinnedGroup PinnedIso AttachedDatum SimpleRoot BasedIso transportCharacter)
open Specs.RootGroups (AdditiveLine rootPoint)
open Specs.QuasiSplitOrbitDerivedRoots (pinnedRootMap)
open Specs.QuasiSplitOrbitLevis (MultiplicativeComparison PreservesUnits)
open Specs.CharacterDescent (Cocharacter Character)
open Specs.RationalRealization (Realization)
open LinearAlgebraicGroups.Classification.Pinning (inducedBasedIso)
open private pinnedLift from LinearAlgebraicGroups.Classification.PinnedEquivalence
open private additiveLineIso from LinearAlgebraicGroups.RootData.RootGroups

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

private theorem composeMarkedSquares {C : Type u} [Category C] {X X' X'' Y Y' Y'' : C}
    (i : X ⟶ Y) (j : X' ⟶ Y') (k : X'' ⟶ Y'')
    (a : X ⟶ X') (b : X' ⟶ X'') (f : Y ⟶ Y') (g : Y' ⟶ Y'')
    (h₁ : i ≫ f = a ≫ j) (h₂ : j ≫ g = b ≫ k) :
    i ≫ (f ≫ g) = (a ≫ b) ≫ k := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

private theorem compareNormalizedRootMaps {k : Type u} [Field k] {A B C X Y Z : GroupScheme k}
    (a : B ≅ A) (e : C ≅ B) (x : A ⟶ X) (y : C ⟶ Y) (z : B ⟶ Z)
    (g : X ⟶ Y) (h : Y ⟶ Z)
    (h₁ : ((e ≪≫ a).hom ≫ x) ≫ g = y)
    (h₂ : y ≫ h = e.hom ≫ z) :
    x ≫ (g ≫ h) = a.inv ≫ z := by
  have h' : e.hom ≫ a.hom ≫ x ≫ g ≫ h = e.hom ≫ z := by
    calc
      _ = (((e ≪≫ a).hom ≫ x) ≫ g) ≫ h := by simp only [Iso.trans_hom, Category.assoc]
      _ = _ := by rw [h₁, h₂]
  have h'' := (cancel_epi e.hom).mp h'
  apply (cancel_epi a.hom).mp
  rw [a.hom_inv_id_assoc]
  exact h''

private theorem compareMarkedCoroots
    {A₁ : AdditiveLine F} {A₂ : AdditiveLine K} {D : Specs.Pinning.BasedRootDatum.{u}}
    (R₀ : Realization D A₁) (R : Realization D A₂)
    (t : R.pinned.pair.T.group ≅ (groupBaseChange F K).obj R₀.pinned.pair.T.group)
    (m : MultiplicativeComparison F K)
    (h : letI := R.attached.comm; letI := R₀.attached.comm
      ∀ y : D.Y, (R.datumIso.val.coweightEquiv.symm y).toMul ≫ t.hom =
        m.hom ≫ (groupBaseChange F K).map (R₀.datumIso.val.coweightEquiv.symm y).toMul)
    (j : D.base.support) :
    simpleCorootOfAttachedDatum R.pinned R.attached (R.simpleRoot j) ≫ t.hom =
      m.hom ≫ (groupBaseChange F K).map (simpleCorootOfAttachedDatum R₀.pinned R₀.attached (R₀.simpleRoot j)) := by
  letI := R.attached.comm
  letI := R₀.attached.comm
  have h₁ := congrArg (fun z : R.attached.toBased.Y => z.toMul ≫ t.hom) (realization_coroot R j)
  have h₂ := congrArg (fun z : R₀.attached.toBased.Y => m.hom ≫ (groupBaseChange F K).map z.toMul)
    (realization_coroot R₀ j)
  exact h₁.symm.trans ((h (D.datum.coroot j.val)).trans h₂)

end FibreMarkEquations

section NormalizedPinnedRealization

open _root_.LinearAlgebraicGroups.Specs
open Opposite
open CategoryTheory.Limits
open Specs.Pinning (PinnedGroup PinnedIso AttachedDatum SimpleRoot BasedIso transportCharacter)
open Specs.RootGroups (AdditiveLine rootPoint)
open Specs.QuasiSplitOrbitDerivedRoots (pinnedRootMap)
open Specs.QuasiSplitOrbitLevis (MultiplicativeComparison PreservesUnits)
open Specs.CharacterDescent (Cocharacter Character)
open Specs.RationalRealization (Realization)
open LinearAlgebraicGroups.Classification.Pinning (inducedBasedIso)
open private pinnedLift from LinearAlgebraicGroups.Classification.PinnedEquivalence
open private additiveLineIso from LinearAlgebraicGroups.RootData.RootGroups

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {F K : Type u} [Field F] [Field K] [Algebra F K]


private theorem normalizedFibreRoot {A₀ A₁ : GroupScheme F} {A A' X X' : GroupScheme K}
    {Y : GroupScheme F} (a : (groupBaseChange F K).obj A₀ ≅ A)
    (a' : A' ≅ (groupBaseChange F K).obj A₁) (e : A₀ ≅ A₁)
    (x : A ⟶ X) (x' : A' ⟶ X') (y : A₁ ⟶ Y)
    (f : X ⟶ X') (g : X' ⟶ (groupBaseChange F K).obj Y)
    (hp : (((a' ≪≫ (groupBaseChange F K).mapIso e.symm) ≪≫ a).hom ≫ x) ≫ f = x')
    (hg : x' ≫ g = a'.hom ≫ (groupBaseChange F K).map y) :
    x ≫ (f ≫ g) = a.inv ≫ (groupBaseChange F K).map (e.hom ≫ y) := by
  let C := groupBaseChange F K
  let ε := a' ≪≫ C.mapIso e.symm
  have he : C.map e.inv ≫ C.map (e.hom ≫ y) = C.map y := by
    rw [← C.map_comp, e.inv_hom_id_assoc]
  have h' : x' ≫ g = ε.hom ≫ C.map (e.hom ≫ y) := by
    rw [hg]
    change a'.hom ≫ C.map y = (a'.hom ≫ C.map e.inv) ≫ C.map (e.hom ≫ y)
    rw [Category.assoc, he]
  exact compareNormalizedRootMaps a ε x x' (C.map (e.hom ≫ y)) f g hp h'

private structure IntegralFibreComparison (F K : Type u) [Field F] [Field K] [Algebra F K]
    (D : Specs.Pinning.BasedRootDatum.{u}) where
  groundLine : AdditiveLine F
  splitLine : AdditiveLine K
  ground : Realization D groundLine
  split : Realization D splitLine
  group : split.pinned.pair.G.val ≅ (groupBaseChange F K).obj ground.pinned.pair.G.val
  torus : split.pinned.pair.T.group ≅ (groupBaseChange F K).obj ground.pinned.pair.T.group
  line : splitLine.group ≅ (groupBaseChange F K).obj groundLine.group
  borel : split.pinned.pair.B.group ≅ (groupBaseChange F K).obj ground.pinned.pair.B.group
  torusSquare : split.pinned.pair.T.inclusion ≫ group.hom =
    torus.hom ≫ (groupBaseChange F K).map ground.pinned.pair.T.inclusion
  borelSquare : split.pinned.pair.B.inclusion ≫ group.hom =
    borel.hom ≫ (groupBaseChange F K).map ground.pinned.pair.B.inclusion
  root : ∀ i : D.base.support,
    split.rootMap i ≫ group.hom = line.hom ≫ (groupBaseChange F K).map (ground.rootMap i)
  cocharacter : letI := split.attached.comm; letI := ground.attached.comm
    ∀ (m : MultiplicativeComparison F K), PreservesUnits m → ∀ y : D.Y,
      (split.datumIso.val.coweightEquiv.symm y).toMul ≫ torus.hom =
        m.hom ≫ (groupBaseChange F K).map (ground.datumIso.val.coweightEquiv.symm y).toMul

private theorem integralFibreComparison_nonempty (D : Specs.Pinning.BasedRootDatum.{u}) :
    Nonempty (IntegralFibreComparison F K D) := by
  obtain ⟨A₁, A₂, P, Q, g, t, a, b, ht, hb, hp, hc⟩ :=
    integralSplitComparison (F := F) (K := K) D
  exact ⟨⟨A₁, A₂, P, Q, g, t, a, b, ht, hb, hp, hc⟩⟩

private abbrev reparametrization {A₀ : AdditiveLine F} {A : AdditiveLine K}
    {D : Specs.Pinning.BasedRootDatum.{u}} (M : IntegralFibreComparison F K D)
    (a : (groupBaseChange F K).obj A₀.group ≅ A.group) (e : A₀.group ≅ M.groundLine.group) :=
  (M.line ≪≫ (groupBaseChange F K).mapIso e.symm) ≪≫ a

private theorem normalizeRealizationRoot {A₀ : AdditiveLine F} {A : AdditiveLine K}
    (Q : PinnedGroup A) (D : AttachedDatum Q.pair)
    (M : IntegralFibreComparison F K D.toBased)
    (a : (groupBaseChange F K).obj A₀.group ≅ A.group) (e : A₀.group ≅ M.groundLine.group)
    (f : PinnedIso (reparametrizePin Q (reparametrization M a e)) M.split.pinned)
    (hf : inducedBasedIso f D M.split.attached = M.split.datumIso) (j : D.toBased.base.support) :
    pinnedRootMap Q.pin (simpleRootsOfAttachedDatum Q D j) ≫ (f.group ≪≫ M.group).hom =
      a.inv ≫ (groupBaseChange F K).map (e.hom ≫ M.ground.rootMap j) := by
  let r := reparametrization M a e
  let Q' := reparametrizePin Q r
  let jQ : SimpleRoot Q'.pair := simpleRootsOfAttachedDatum Q' D j
  let jR : SimpleRoot M.split.pinned.pair := M.split.simpleRoot j
  have h := (pinsOfBasedIso (P := Q') (Q := M.split.pinned) (D := D) (E := M.split.attached)
    f M.split.datumIso hf jQ jR rfl).2.1
  rw [reparametrizeRootMap] at h
  exact normalizedFibreRoot a M.line e (pinnedRootMap Q.pin (simpleRootsOfAttachedDatum Q D j))
    (M.split.rootMap j) (M.ground.rootMap j) f.group.hom M.group.hom h (M.root j)

private theorem normalizeRealizationCoroot {A₀ : AdditiveLine F} {A : AdditiveLine K}
    (Q : PinnedGroup A) (D : AttachedDatum Q.pair)
    (M : IntegralFibreComparison F K D.toBased)
    (a : (groupBaseChange F K).obj A₀.group ≅ A.group) (e : A₀.group ≅ M.groundLine.group)
    (f : PinnedIso (reparametrizePin Q (reparametrization M a e)) M.split.pinned)
    (hf : inducedBasedIso f D M.split.attached = M.split.datumIso)
    (m : MultiplicativeComparison F K) (hm : PreservesUnits m) (j : D.toBased.base.support) :
    simpleCorootOfAttachedDatum Q D (simpleRootsOfAttachedDatum Q D j) ≫ (f.torus ≪≫ M.torus).hom =
      m.hom ≫ (groupBaseChange F K).map
        (simpleCorootOfAttachedDatum M.ground.pinned M.ground.attached (M.ground.simpleRoot j)) := by
  let Q' := reparametrizePin Q (reparametrization M a e)
  let jQ : SimpleRoot Q'.pair := simpleRootsOfAttachedDatum Q' D j
  let jR : SimpleRoot M.split.pinned.pair := M.split.simpleRoot j
  have h := (pinsOfBasedIso (P := Q') (Q := M.split.pinned) (D := D) (E := M.split.attached)
    f M.split.datumIso hf jQ jR rfl).2.2
  have h₁ : simpleCorootOfAttachedDatum Q D (simpleRootsOfAttachedDatum Q D j) ≫ f.torus.hom =
      simpleCorootOfAttachedDatum M.split.pinned M.split.attached jR := h
  have h₂ := compareMarkedCoroots M.ground M.split M.torus m (M.cocharacter m hm) j
  change simpleCorootOfAttachedDatum Q D (simpleRootsOfAttachedDatum Q D j) ≫ (f.torus.hom ≫ M.torus.hom) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun c : Cocharacter M.split.pinned.pair.T.group => c ≫ M.torus.hom) h₁).trans h₂)

set_option maxHeartbeats 400000 in
private theorem comparePinnedRealization {A₀ : AdditiveLine F} {A : AdditiveLine K}
    (Q : PinnedGroup A) (D : AttachedDatum Q.pair)
    (a : (groupBaseChange F K).obj A₀.group ≅ A.group)
    (m : MultiplicativeComparison F K) (hm : PreservesUnits m) :
    let C := groupBaseChange F K
    ∃ (A₁ : AdditiveLine F) (P : Realization D.toBased A₁) (e : A₀.group ≅ A₁.group)
      (g : Q.pair.G.val ≅ C.obj P.pinned.pair.G.val) (t : Q.pair.T.group ≅ C.obj P.pinned.pair.T.group)
      (b : Q.pair.B.group ≅ C.obj P.pinned.pair.B.group),
      Q.pair.T.inclusion ≫ g.hom = t.hom ≫ C.map P.pinned.pair.T.inclusion ∧
      Q.pair.B.inclusion ≫ g.hom = b.hom ≫ C.map P.pinned.pair.B.inclusion ∧
      ∀ j : D.toBased.base.support,
        pinnedRootMap Q.pin (simpleRootsOfAttachedDatum Q D j) ≫ g.hom =
          a.inv ≫ C.map (e.hom ≫ P.rootMap j) ∧
        simpleCorootOfAttachedDatum Q D (simpleRootsOfAttachedDatum Q D j) ≫ t.hom =
          m.hom ≫ C.map (simpleCorootOfAttachedDatum P.pinned P.attached (P.simpleRoot j)) := by
  obtain ⟨M⟩ := integralFibreComparison_nonempty (F := F) (K := K) D.toBased
  let e := additiveLineIso A₀ M.groundLine
  obtain ⟨f, hf⟩ := pinnedLift (reparametrizePin Q (reparametrization M a e))
    M.split.pinned D M.split.attached M.split.datumIso
  let C := groupBaseChange F K
  have ht : Q.pair.T.inclusion ≫ (f.group ≪≫ M.group).hom =
      (f.torus ≪≫ M.torus).hom ≫ C.map M.ground.pinned.pair.T.inclusion :=
    composeMarkedSquares Q.pair.T.inclusion M.split.pinned.pair.T.inclusion
      (C.map M.ground.pinned.pair.T.inclusion) f.torus.hom M.torus.hom f.group.hom M.group.hom
      f.torus_comm M.torusSquare
  have hb : Q.pair.B.inclusion ≫ (f.group ≪≫ M.group).hom =
      (f.borel ≪≫ M.borel).hom ≫ C.map M.ground.pinned.pair.B.inclusion :=
    composeMarkedSquares Q.pair.B.inclusion M.split.pinned.pair.B.inclusion
      (C.map M.ground.pinned.pair.B.inclusion) f.borel.hom M.borel.hom f.group.hom M.group.hom
      f.borel_comm M.borelSquare
  exact ⟨M.groundLine, M.ground, e, f.group ≪≫ M.group, f.torus ≪≫ M.torus, f.borel ≪≫ M.borel,
    ht, hb, fun j => ⟨normalizeRealizationRoot Q D M a e f hf j,
      normalizeRealizationCoroot Q D M a e f hf m hm j⟩⟩

end NormalizedPinnedRealization

section FacePinnedTwist

open _root_.LinearAlgebraicGroups.Specs
open Opposite
open CategoryTheory.Limits
open Specs.Pinning (PinnedGroup PinnedIso AttachedDatum SimpleRoot BasedIso transportCharacter)
open Specs.RootGroups (AdditiveLine)
open Specs.QuasiSplitOrbitDerivedRoots (pinnedRootMap coefficientAction comparedAction)
open Specs.QuasiSplitOrbitLevis (MultiplicativeComparison PreservesUnits simplePermutation)
open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricRadicals (IsSplitTorus IsSemisimple)
open Specs.SimplyConnectedLattice (corootLattice GeometricallySimplyConnected)
open Specs.RationalRealization (Realization)
open Specs.AdjointBorelCohomology (PinnedTwist)
open Specs.AdjointCocharacters (coordinateHopf coordinateHopfIso)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open LinearAlgebraicGroups.Classification.Pinning (inducedBasedIso)
open private splitTorus_baseChange from LinearAlgebraicGroups.Reductive.SplitToriConjugacy
open private isTorus_of_split from LinearAlgebraicGroups.RootData.CharacterPairing
open private torus_commutative from LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private realization_corootSpan of_fullCorootLattice
  from LinearAlgebraicGroups.Classification.SimplyConnectedLattice

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

private theorem realization_vertex_action {k : Type u} [Field k] {A : AdditiveLine k}
    {D : Specs.Pinning.BasedRootDatum.{u}} (P : Realization D A)
    (x : Aut D) (i j : D.base.support) (h : x.asIso.hom.val.indexEquiv i.val = j.val) :
    ((Aut.autMulEquivOfIso (asIso P.datumIso)) x).asIso.hom.val.indexEquiv (P.simpleRoot i).val =
      (P.simpleRoot j).val := by
  let e : D ≅ P.attached.toBased := asIso P.datumIso
  let v (z : Specs.AbstractPairing.Root P.pinned.pair.T) := e.inv.val.indexEquiv z
  have hv : v (P.simpleRoot i).val = i.val := by
    have h' := congrArg (fun b : D ⟶ D => b.val.indexEquiv i.val) e.hom_inv_id
    change e.inv.val.indexEquiv (P.datumIso.val.indexEquiv i.val) = i.val at h'
    exact h'
  change P.datumIso.val.indexEquiv (x.asIso.hom.val.indexEquiv (v (P.simpleRoot i).val)) =
    P.datumIso.val.indexEquiv j.val
  rw [hv, h]

private theorem corootBasisOnSimpleRoots {k : Type u} [Field k] {A : AdditiveLine k}
    (Q : PinnedGroup A) (D : AttachedDatum Q.pair) (hss : IsSemisimple Q.pair.G)
    (hsc : GeometricallySimplyConnected Q.pair.G) :
    letI := D.comm
    ∃ b : Module.Basis (SimpleRoot Q.pair) ℤ (Additive (Cocharacter Q.pair.T.group)),
      ∀ j, b j = Additive.ofMul (simpleCorootOfAttachedDatum Q D j) := by
  letI := D.comm
  obtain ⟨c, hc⟩ := attachedCorootBasis Q.pair D hss hsc
  refine ⟨c.reindex (simpleRootsOfAttachedDatum Q D), ?_⟩
  intro j
  rw [Module.Basis.reindex_apply, hc]
  rfl

private def MarkedRealizationComparison : Prop :=
  ∀ {A₀ : AdditiveLine F} {A : AdditiveLine K}
    (Q : PinnedGroup A) (D : AttachedDatum Q.pair)
    (a : (groupBaseChange F K).obj A₀.group ≅ A.group)
    (m : MultiplicativeComparison F K), PreservesUnits m →
    let C := groupBaseChange F K
    ∃ (A₁ : AdditiveLine F) (P : Realization D.toBased A₁) (e : A₀.group ≅ A₁.group)
      (g : Q.pair.G.val ≅ C.obj P.pinned.pair.G.val) (t : Q.pair.T.group ≅ C.obj P.pinned.pair.T.group)
      (b : Q.pair.B.group ≅ C.obj P.pinned.pair.B.group),
      Q.pair.T.inclusion ≫ g.hom = t.hom ≫ C.map P.pinned.pair.T.inclusion ∧
      Q.pair.B.inclusion ≫ g.hom = b.hom ≫ C.map P.pinned.pair.B.inclusion ∧
      ∀ j : D.toBased.base.support,
        pinnedRootMap Q.pin (simpleRootsOfAttachedDatum Q D j) ≫ g.hom =
          a.inv ≫ C.map (e.hom ≫ P.rootMap j) ∧
        simpleCorootOfAttachedDatum Q D (simpleRootsOfAttachedDatum Q D j) ≫ t.hom =
          m.hom ≫ C.map (simpleCorootOfAttachedDatum P.pinned P.attached (P.simpleRoot j))

set_option maxHeartbeats 750000 in
private theorem pinnedTwistOfMarkedSplitPair (comparePinnedRealization : MarkedRealizationComparison (F := F) (K := K)) {H : AffineAlgebraicGroup F}
    (T B : ClosedSubgroup H.val) {A₀ : AdditiveLine F} {A : AdditiveLine K}
    (Q : PinnedGroup A) (D : AttachedDatum Q.pair)
    (hss : IsSemisimple Q.pair.G) (hsc : GeometricallySimplyConnected Q.pair.G)
    (a : (groupBaseChange F K).obj A₀.group ≅ A.group)
    (m : MultiplicativeComparison F K) (hm : PreservesUnits m)
    (θ : Gal(K/F) →* Aut D.toBased)
    (h : (groupBaseChange F K).obj H.val ≅ Q.pair.G.val)
    (s : (groupBaseChange F K).obj T.group ≅ Q.pair.T.group)
    (b : (groupBaseChange F K).obj B.group ≅ Q.pair.B.group)
    (hs : (groupBaseChange F K).map T.inclusion ≫ h.hom = s.hom ≫ Q.pair.T.inclusion)
    (hb : (groupBaseChange F K).map B.inclusion ≫ h.hom = b.hom ≫ Q.pair.B.inclusion)
    (hco : ∀ (σ : Gal(K/F)) (j : D.toBased.base.support),
      comparedAction σ⁻¹ m.symm ≫
        schemeHom (simpleCorootOfAttachedDatum Q D (simpleRootsOfAttachedDatum Q D (simplePermutation D (θ σ) j))) =
      schemeHom (simpleCorootOfAttachedDatum Q D (simpleRootsOfAttachedDatum Q D j)) ≫ comparedAction σ⁻¹ s)
    (hpin : ∀ (σ : Gal(K/F)) (j : D.toBased.base.support),
      comparedAction σ⁻¹ a ≫
        schemeHom (pinnedRootMap Q.pin (simpleRootsOfAttachedDatum Q D (simplePermutation D (θ σ) j))) =
      schemeHom (pinnedRootMap Q.pin (simpleRootsOfAttachedDatum Q D j)) ≫ comparedAction σ⁻¹ h) :
    let C := groupBaseChange F K
    ∃ (A₁ : AdditiveLine F) (P : Realization D.toBased A₁) (e : A₀.group ≅ A₁.group)
      (l : Aut P.attached.toBased ≃* Aut P.pinned)
      (d : PinnedTwist (P := P.pinned) K P.attached l B T)
      (g : C.obj H.val ≅ C.obj P.pinned.pair.G.val) (τ : C.obj T.group ≅ C.obj P.pinned.pair.T.group),
      C.map T.inclusion ≫ g.hom = τ.hom ≫ C.map P.pinned.pair.T.inclusion ∧
      d.outer = (Aut.autMulEquivOfIso (asIso P.datumIso)).toMonoidHom.comp θ ∧
      (∀ (σ : Gal(K/F)) (j : D.toBased.base.support),
        transportCharacter (l (d.outer σ)).asIso.hom.torus (P.simpleRoot j).val.val =
          (P.simpleRoot (simplePermutation D (θ σ) j)).val.val) ∧
      (∀ j : D.toBased.base.support,
        pinnedRootMap Q.pin (simpleRootsOfAttachedDatum Q D j) ≫ h.inv ≫ g.hom =
          a.inv ≫ C.map (e.hom ≫ P.rootMap j) ∧
        simpleCorootOfAttachedDatum Q D (simpleRootsOfAttachedDatum Q D j) ≫ s.inv ≫ τ.hom =
          m.hom ≫ C.map (simpleCorootOfAttachedDatum P.pinned P.attached (P.simpleRoot j))) ∧
      (∀ (a' : ∀ U : HopfAlgebraCategory F, specGroup (extendedHopf K U) ≅ C.obj (specGroup U)),
        Descent.Forms.IsScalarExtensionComparison a' →
        (((a' (Specs.AdjointCocharacters.coordinateHopf H) ≪≫ C.mapIso (Specs.AdjointCocharacters.coordinateHopfIso H)).symm ≪≫
            (hopfSpec (CommRingCat.of K)).mapIso d.groupIso.op) ≪≫
          (a' (Specs.AdjointCocharacters.coordinateHopf P.pinned.pair.G) ≪≫
            C.mapIso (Specs.AdjointCocharacters.coordinateHopfIso P.pinned.pair.G))) = g) ∧
      IsSemisimple P.pinned.pair.G ∧ GeometricallySimplyConnected P.pinned.pair.G := by
  letI := D.comm
  let C := groupBaseChange F K
  obtain ⟨A₁, P, e, g', t', b', ht', hb', hmarks⟩ := comparePinnedRealization Q D a m hm
  obtain ⟨l, hl⟩ := liftOfAttachedDatum P.pinned P.attached
  let θ₁ := (Aut.autMulEquivOfIso (asIso P.datumIso)).toMonoidHom.comp θ
  let g := h ≪≫ g'
  let t := s ≪≫ t'
  let β := b ≪≫ b'
  let j₀ := simpleRootsOfAttachedDatum Q D
  let π (σ : Gal(K/F)) := simplePermutation D (θ σ)
  have ht : C.map T.inclusion ≫ g.hom = t.hom ≫ C.map P.pinned.pair.T.inclusion := by
    change C.map T.inclusion ≫ h.hom ≫ g'.hom =
      (s.hom ≫ t'.hom) ≫ C.map P.pinned.pair.T.inclusion
    rw [← Category.assoc, hs, Category.assoc, ht', Category.assoc]
  have hB : C.map B.inclusion ≫ g.hom = β.hom ≫ C.map P.pinned.pair.B.inclusion := by
    change C.map B.inclusion ≫ h.hom ≫ g'.hom =
      (b.hom ≫ b'.hom) ≫ C.map P.pinned.pair.B.inclusion
    rw [← Category.assoc, hb, Category.assoc, hb', Category.assoc]
  have hcor (j : D.toBased.base.support) :
      simpleCorootOfAttachedDatum Q D (j₀ j) ≫ s.inv ≫ t.hom =
        m.hom ≫ C.map (simpleCorootOfAttachedDatum P.pinned P.attached (P.simpleRoot j)) := by
    change simpleCorootOfAttachedDatum Q D (j₀ j) ≫ s.inv ≫ s.hom ≫ t'.hom = _
    rw [Iso.inv_hom_id_assoc]
    exact (hmarks j).2
  have hroot (j : D.toBased.base.support) :
      pinnedRootMap Q.pin (j₀ j) ≫ h.inv ≫ g.hom = a.inv ≫ C.map (e.hom ≫ P.rootMap j) := by
    change pinnedRootMap Q.pin (j₀ j) ≫ h.inv ≫ h.hom ≫ g'.hom = _
    rw [Iso.inv_hom_id_assoc]
    exact (hmarks j).1
  have hmarksF (σ : Gal(K/F)) (j : D.toBased.base.support) :=
    pinsOfBasedIso (l (θ₁ σ)).asIso.hom (θ₁ σ).asIso.hom (hl (θ₁ σ))
      (P.simpleRoot j) (P.simpleRoot (π σ j)) (realization_vertex_action P (θ σ) j (π σ j) rfl)
  obtain ⟨basis, hbasis⟩ := corootBasisOnSimpleRoots Q D hss hsc
  have hsplit : IsSplitTorus (C.obj P.pinned.pair.T.group) := splitTorus_baseChange P.pinned.pair.split
  have hcT : IsCommMonObj (C.obj P.pinned.pair.T.group).X :=
    torus_commutative (Unipotent.baseChangedAlgebraicGroup K
      (Unipotent.closedSubgroupAlgebraicGroup P.pinned.pair.T)) (isTorus_of_split hsplit)
  have hcoeff (σ : Gal(K/F)) :
      coefficientAction σ H.val ≫ schemeHom g.hom = schemeHom g.hom ≫
        schemeHom (C.map (l (θ₁ σ)).asIso.hom.group.inv) ≫ coefficientAction σ P.pinned.pair.G.val := by
    let f := (l (θ₁ σ)).asIso.hom
    let ρ := j₀.permCongr (π σ)
    have hρ (j : D.toBased.base.support) : ρ (j₀ j) = j₀ (π σ j) := by
      change j₀ (π σ (j₀.symm (j₀ j))) = j₀ (π σ j)
      rw [Equiv.symm_apply_apply]
    refine pinnedComparisonEquivariant Q D P.pinned h s T.inclusion hs m a g t ht σ f ρ
      hcT hsplit basis hbasis ?_ ?_ ?_ ?_ ?_ ?_
    · intro i
      obtain ⟨j, rfl⟩ := j₀.surjective i
      rw [hρ j]
      exact twistOfMarkedMorphism σ m.symm s _ _ (hco σ j)
    · intro i
      obtain ⟨j, rfl⟩ := j₀.surjective i
      rw [hρ j]
      exact twistOfMarkedMorphism σ a h _ _ (hpin σ j)
    · intro i
      obtain ⟨j, rfl⟩ := j₀.surjective i
      rw [hρ j]
      refine ⟨simpleCorootOfAttachedDatum P.pinned P.attached (P.simpleRoot (π σ j)), ?_⟩
      rw [hcor, Iso.inv_hom_id_assoc]
    · intro i
      obtain ⟨j, rfl⟩ := j₀.surjective i
      rw [hρ j]
      exact ⟨e.hom ≫ P.rootMap (π σ j), by rw [hroot, Iso.hom_inv_id_assoc]⟩
    · intro i
      obtain ⟨j, rfl⟩ := j₀.surjective i
      rw [hρ j]
      change simpleCorootOfAttachedDatum Q D (j₀ j) ≫ s.inv ≫ t.hom ≫ C.map f.torus.hom =
        simpleCorootOfAttachedDatum Q D (j₀ (π σ j)) ≫ s.inv ≫ t.hom
      calc
        _ = (simpleCorootOfAttachedDatum Q D (j₀ j) ≫ s.inv ≫ t.hom) ≫ C.map f.torus.hom := by
          simp only [Category.assoc]
        _ = _ := by
          rw [hcor, hcor, Category.assoc, ← C.map_comp, (hmarksF σ j).2.2]
    · intro i
      obtain ⟨j, rfl⟩ := j₀.surjective i
      rw [hρ j]
      have hp := (hmarksF σ j).2.1
      change P.rootMap j ≫ f.group.hom = P.rootMap (π σ j) at hp
      change pinnedRootMap Q.pin (j₀ j) ≫ h.inv ≫ g.hom ≫ C.map f.group.hom =
        pinnedRootMap Q.pin (j₀ (π σ j)) ≫ h.inv ≫ g.hom
      calc
        _ = (pinnedRootMap Q.pin (j₀ j) ≫ h.inv ≫ g.hom) ≫ C.map f.group.hom := by
          simp only [Category.assoc]
        _ = _ := by
          rw [hroot, hroot]
          simp only [Category.assoc, ← C.map_comp, hp]
  obtain ⟨d, hd, htriv⟩ := pinnedTwistFromSchemeComparison P.pinned P.attached l B T θ₁
    g β t hB.symm ht.symm (by
      intro σ
      let U := Specs.AutomorphismSequence.forgetPinning (A := A₁)
      let f := (l (θ₁ σ)).asIso
      have hh : U.mapIso f = f.hom.group := by
        apply Iso.ext
        rfl
      change coefficientAction σ H.val ≫ schemeHom g.hom =
        schemeHom g.hom ≫ schemeHom (C.map (U.mapIso f).inv) ≫ coefficientAction σ P.pinned.pair.G.val
      rw [hh]
      exact hcoeff σ)
  have hL := (Classification.SimplyConnectedLattice.latticeCriterion Q.pair.G hss
    Q.pair.T Q.pair.split Q.pair.maximal D.datum).mp hsc
  letI := P.attached.comm
  have hL₀ := realization_corootSpan P hL
  have hss₀ := of_fullCorootLattice P.pinned.pair P.attached hL₀
  have hsc₀ := (Classification.SimplyConnectedLattice.latticeCriterion P.pinned.pair.G hss₀
    P.pinned.pair.T P.pinned.pair.split P.pinned.pair.maximal P.attached.datum).mpr hL₀
  exact ⟨A₁, P, e, l, d, g, t, ht, hd, fun σ j => by rw [hd]; exact (hmarksF σ j).1,
    fun j => ⟨hroot j, hcor j⟩, htriv, hss₀, hsc₀⟩

end FacePinnedTwist

section ActualPinnedFace

open _root_.LinearAlgebraicGroups.Specs
open Opposite
open CategoryTheory.Limits
open Specs.Pinning (SplitBorelPair PinnedGroup PinnedIso AttachedDatum SimpleRoot Pinning)
open Specs.RootGroups (AdditiveLine)
open Specs.QuasiSplitOrbitDerivedRoots (pinnedRootMap coefficientAction comparedAction diagramRoot)
open Specs.QuasiSplitOrbitLevis
open Specs.QuasiSplitOrbitPinnedModels (PinnedOrbitDescent)
open Specs.GeometricRadicals (IsReductive IsTorus IsSemisimple)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.OrderedRootProducts (RootSubgroupFamily)
open Specs.AbstractPairing (Root)
open Specs.AdjointBorelCohomology (PinnedTwist)
open Specs.AdjointCocharacters (coordinateHopf coordinateHopfIso)
open Specs.RationalRealization (Realization)
open Specs.StandardParabolicLevi (leviRoots)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
variable {G : AffineAlgebraicGroup F} {T B N : ClosedSubgroup G.val}
variable {P : SplitPairOver (K := K) G T B}
variable {D : AttachedDatum P.pair} {I : Set (Root P.pair.T)} {L : RationalStandardFace D I}
variable {pair : RationalOppositePair T B N}
variable {hG : IsReductive G} {hT : IsTorus T.group} {hmax : IsGeometricallyMaximal T}
variable {A₀ : AdditiveLine F} {A : AdditiveLine K}
variable {U : RootSubgroupFamily P.pair.T} {p : Pinning A P.pair U}
variable {a : (groupBaseChange F K).obj A₀.group ≅ A.group} {ω : Gal(K/F) →* Aut D.toBased}

private abbrev inducedPinnedGroup
    (d : InducedFaceData D (L := L) (pair := pair) (hG := hG) (hT := hT) (hmax := hmax) p a ω) :
    PinnedGroup A :=
  ⟨d.positive.pair d.reductive, d.rootGroups, d.pinning⟩

set_option maxHeartbeats 600000 in
private theorem faceDiagramActsOnMarks
    (d : InducedFaceData D (L := L) (pair := pair) (hG := hG) (hT := hT) (hmax := hmax) p a ω)
    (hstable : ∀ (σ : Gal(K/F)) (α : Root P.pair.T), diagramRoot ω σ α ∈ I ↔ α ∈ I)
    (v : I ≃ d.posDatum.toBased.base.support) (θ : Gal(K/F) →* Aut d.posDatum.toBased)
    (hv : letI := D.comm; ∀ (i : I) (α : ↥(leviRoots D.datum I)), i.val = α.val → (v i).val = d.roots α)
    (hθ : ∀ (σ : Gal(K/F)) (i : I), (θ σ).asIso.hom.val.indexEquiv (v i).val =
      (v ⟨diagramRoot ω σ i.val, (hstable σ i.val).mpr i.property⟩).val) :
    let R := L.rationalFace D pair hG hT hmax
    let Q := inducedPinnedGroup d
    let E := d.posDatum
    ∀ (σ : Gal(K/F)) (j : E.toBased.base.support),
      let j' := simplePermutation E (θ σ) j
      comparedAction σ⁻¹ L.scalar.symm ≫ schemeHom (simpleCorootOfAttachedDatum Q E (simpleRootsOfAttachedDatum Q E j')) =
        schemeHom (simpleCorootOfAttachedDatum Q E (simpleRootsOfAttachedDatum Q E j)) ≫ comparedAction σ⁻¹ R.torusComparison ∧
      comparedAction σ⁻¹ a ≫ schemeHom (pinnedRootMap Q.pin (simpleRootsOfAttachedDatum Q E j')) =
        schemeHom (pinnedRootMap Q.pin (simpleRootsOfAttachedDatum Q E j)) ≫ comparedAction σ⁻¹ R.derivedComparison := by
  letI := D.comm
  let E := d.posDatum
  letI := E.comm
  let R := L.rationalFace D pair hG hT hmax
  let Q := inducedPinnedGroup d
  dsimp only
  intro σ j
  obtain ⟨α, hα⟩ := d.roots.surjective j.val
  let i : I := ⟨α.val, ((d.rootComparison α).2.2.1).mp (hα.symm ▸ j.property)⟩
  have e : v i = j := Subtype.ext ((hv i α rfl).trans hα)
  let β : ↥(leviRoots D.datum I) := ⟨diagramRoot ω σ α.val, d.stable σ α⟩
  let i' : I := ⟨β.val, (hstable σ α.val).mpr i.property⟩
  have hsh : (simplePermutation E (θ σ) j).val = d.roots β := by
    rw [← e]
    exact (hθ σ i).trans (hv i' β rfl)
  let x : SimpleRoot P.pair := ⟨α.val, (D.simple_iff α.val).mp (L.simple i.property)⟩
  have h := d.action σ α β rfl
  refine ⟨?_, ?_⟩
  · change comparedAction σ⁻¹ L.scalar.symm ≫
        schemeHom (E.datum.rootDatum.coroot (simplePermutation E (θ σ) j).val).toMul =
      schemeHom (E.datum.rootDatum.coroot j.val).toMul ≫ comparedAction σ⁻¹ R.torusComparison
    rw [hsh, ← hα]
    exact h.2.1
  · exact
    h.2.2 x (simpleRootsOfAttachedDatum Q E j) (simpleRootsOfAttachedDatum Q E (simplePermutation E (θ σ) j))
      rfl hα.symm hsh

set_option maxHeartbeats 900000 in
private theorem facePinnedForm
    (d : InducedFaceData D (L := L) (pair := pair) (hG := hG) (hT := hT) (hmax := hmax) p a ω)
    (hm : PreservesUnits L.scalar)
    (hstable : ∀ (σ : Gal(K/F)) (α : Root P.pair.T), diagramRoot ω σ α ∈ I ↔ α ∈ I) :
    Nonempty (FacePinnedForm d) := by
  letI := D.comm
  let C := groupBaseChange F K
  let R := L.rationalFace D pair hG hT hmax
  let Q := inducedPinnedGroup d
  let E := d.posDatum
  letI := E.comm
  obtain ⟨v, θ, hv, hp, hθ⟩ := rationalFaceDiagram D d hstable
  have hss : IsSemisimple Q.pair.G :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := K) R.group
      L.semisimple.1 L.semisimple.2.1).mpr L.semisimple
  have hsc : GeometricallySimplyConnected Q.pair.G :=
    QuasiSplitOrbitDerivedRoots.splitDerivedSimplyConnected D I (L.splitFace D) L.integralImage
  have ha := faceDiagramActsOnMarks d hstable v θ hv hθ
  have comparison : MarkedRealizationComparison (F := F) (K := K) :=
    fun Q' D' a' m' hm' => comparePinnedRealization Q' D' a' m' hm'
  obtain ⟨A₁, P₁, e, l, w, g, t, htorus, hw, haction, hmarks, hcomp, hss₁, hsc₁⟩ :=
    pinnedTwistOfMarkedSplitPair (H := R.group) comparison L.torus d.positive.rational Q E hss hsc a L.scalar hm θ
      R.derivedComparison R.torusComparison d.positive.comparison R.torusSquare.symm
      d.positive.square.symm (fun σ j => (ha σ j).1) (fun σ j => (ha σ j).2)
  refine ⟨⟨v, θ, hv, hp, ?_, A₁, P₁, l, w, g, t, htorus, haction, e, ?_, ?_, hcomp, hss₁, hsc₁⟩⟩
  · intro σ i j h
    have h' : (⟨diagramRoot ω σ i.val, (hstable σ i.val).mpr i.property⟩ : I) = j :=
      Subtype.ext h
    exact (hθ σ i).trans (congrArg (fun y : I => (v y).val) h')
  · dsimp only
    intro j
    have ht := (hmarks j).1
    change pinnedRootMap Q.pin (simpleRootsOfAttachedDatum Q E j) ≫ (𝟙 _) ≫ g.hom = _ at ht
    simpa only [Category.id_comp] using ht
  · dsimp only
    intro j
    have ht := (hmarks j).2
    change simpleCorootOfAttachedDatum Q E (simpleRootsOfAttachedDatum Q E j) ≫ (𝟙 _) ≫ t.hom = _ at ht
    simpa only [Category.id_comp] using ht

/-- The pinned form of the induced face with its actual ambient root labels. -/
theorem rationalFacePinnedForm : RationalFacePinnedForm.{u} := by
  intro F K _ _ _ G T B N P D I L pair hG hT hmax A₀ A U p a ω d hm hs
  exact facePinnedForm d hm hs

end ActualPinnedFace

section MarkedOrbit

open _root_.LinearAlgebraicGroups.Specs
open CategoryTheory.Limits
open Specs.AbstractPairing (Root)
open Specs.Pinning (AttachedDatum SimpleRoot Pinning transportCharacter)
open Specs.RootGroups (AdditiveLine)
open Specs.OrderedRootProducts (RootSubgroupFamily)
open Specs.GeometricRadicals (IsReductive IsTorus IsUnipotentRadical)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.QuasiSplitOrbitDerivedRoots (diagramRoot)
open Specs.QuasiSplitOrbitPinnedModels (PinnedOrbitDescent MatrixMark)
open Specs.UnipotentRadicalIntersection (IsSchemeIntersection)
open Specs.QuasiSplitOrbitLevis

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
variable {G : AffineAlgebraicGroup F} {T B N : ClosedSubgroup G.val}
variable {P : SplitPairOver (K := K) G T B}
variable {D : AttachedDatum P.pair} {I : Set (Root P.pair.T)} {L : RationalStandardFace D I}
variable {pair : RationalOppositePair T B N}
variable {hG : IsReductive G} {hT : IsTorus T.group} {hmax : IsGeometricallyMaximal T}
variable {A₀ : AdditiveLine F} {A : AdditiveLine K}
variable {U : RootSubgroupFamily P.pair.T} {p : Pinning A P.pair U}
variable {a : (groupBaseChange F K).obj A₀.group ≅ A.group} {ω : Gal(K/F) →* Aut D.toBased}
variable {d : InducedFaceData D (L := L) (pair := pair) (hG := hG) (hT := hT) (hmax := hmax) p a ω}

private theorem schemeIntersection_of_pullback {k : Type u} [Field k] {X : GroupScheme k}
    {S B₁ B₂ : ClosedSubgroup X} (b₁ : S.group ⟶ B₁.group) (b₂ : S.group ⟶ B₂.group)
    (h : IsPullback b₁ b₂ B₁.inclusion B₂.inclusion) (e : b₁ ≫ B₁.inclusion = S.inclusion) :
    IsSchemeIntersection {B₁, B₂} S := by
  let C := Grp.forget (SchemeOver k)
  have hp : IsPullback b₁.hom.hom b₂.hom.hom B₁.inclusion.hom.hom B₂.inclusion.hom.hom := h.map C
  have he₁ : b₁.hom.hom ≫ B₁.inclusion.hom.hom = S.inclusion.hom.hom :=
    congrArg (fun f : S.group ⟶ X => f.hom.hom) e
  have he₂ : b₂.hom.hom ≫ B₂.inclusion.hom.hom = S.inclusion.hom.hom := hp.w.symm.trans he₁
  intro Y y
  constructor
  · rintro ⟨s, hs⟩ V hv
    change s ≫ S.inclusion.hom.hom = y at hs
    rcases Set.mem_insert_iff.mp hv with rfl | hv
    · refine ⟨s ≫ b₁.hom.hom, ?_⟩
      change (s ≫ b₁.hom.hom) ≫ V.inclusion.hom.hom = y
      rw [Category.assoc, he₁, hs]
    · obtain rfl := Set.mem_singleton_iff.mp hv
      refine ⟨s ≫ b₂.hom.hom, ?_⟩
      change (s ≫ b₂.hom.hom) ≫ V.inclusion.hom.hom = y
      rw [Category.assoc, he₂, hs]
  · intro hy
    obtain ⟨x₁, hx₁⟩ := hy B₁ (by simp)
    obtain ⟨x₂, hx₂⟩ := hy B₂ (by simp)
    change x₁ ≫ B₁.inclusion.hom.hom = y at hx₁
    change x₂ ≫ B₂.inclusion.hom.hom = y at hx₂
    let e := hx₁.trans hx₂.symm
    refine ⟨hp.lift x₁ x₂ e, ?_⟩
    change hp.lift x₁ x₂ e ≫ S.inclusion.hom.hom = y
    rw [← he₁, ← Category.assoc, hp.lift_fst, hx₁]

private theorem faceOpposite (d : InducedFaceData D (L := L) (pair := pair)
    (hG := hG) (hT := hT) (hmax := hmax) p a ω) :
    IsSchemeIntersection {d.positive.rational, d.negative.rational} L.torus := by
  obtain ⟨b₁, b₂, hp, he⟩ := d.opposite
  exact schemeIntersection_of_pullback b₁ b₂ hp he

private theorem faceRadicals_nonempty (d : InducedFaceData D (L := L) (pair := pair)
    (hG := hG) (hT := hT) (hmax := hmax) p a ω) : Nonempty (FaceRadicals d) := by
  let H := (L.rationalFace D pair hG hT hmax).group
  have hH : IsReductive H := reductive_of_semisimple H L.semisimple
  obtain ⟨b₁, b₂, hp, he₁⟩ := d.opposite
  have he₂ := hp.w.symm.trans he₁
  obtain ⟨V₁, _, h₁, _⟩ := borelRadicalAndQuotient hH L.torus d.positive.rational
    L.maximal d.positive.isKBorel b₁ he₁
  obtain ⟨V₂, _, h₂, _⟩ := borelRadicalAndQuotient hH L.torus d.negative.rational
    L.maximal d.negative.isKBorel b₂ he₂
  exact ⟨⟨V₁, V₂, h₁, h₂⟩⟩

private theorem faceModelAction_apply (q : FacePinnedForm d) (σ : Gal(K/F)) (i j : I)
    (h : diagramRoot ω σ i.val = j.val) :
    q.modelAction σ (q.modelVertices i) = q.modelVertices j := by
  let e := realizationSimpleEquiv q.splitModel
  change e (simplePermutation d.posDatum (q.diagram σ) (e.symm (e (q.vertices i)))) =
    e (q.vertices j)
  rw [e.symm_apply_apply]
  exact congrArg e (Subtype.ext (q.vertexAction σ i j h))

private theorem faceModelAction_character (q : FacePinnedForm d) :
    ∀ (σ : Gal(K/F)) (j : SimpleRoot q.splitModel.pinned.pair),
      transportCharacter (q.lift (q.descent.outer σ)).asIso.hom.torus j.val.val =
        (q.modelAction σ j).val.val := by
  intro σ j
  let e := realizationSimpleEquiv q.splitModel
  obtain ⟨i, rfl⟩ := e.surjective j
  change transportCharacter (q.lift (q.descent.outer σ)).asIso.hom.torus
    (q.splitModel.simpleRoot i).val.val =
      (e (simplePermutation d.posDatum (q.diagram σ) (e.symm (e i)))).val.val
  rw [e.symm_apply_apply]
  exact q.simpleAction σ i

private theorem faceModelAction_transitive (q : FacePinnedForm d)
    (h : ∀ i j : I, ∃ σ, diagramRoot ω σ i.val = j.val) :
    ∀ i j, ∃ σ, q.modelAction σ i = j := by
  intro i j
  obtain ⟨i, rfl⟩ := q.modelVertices.surjective i
  obtain ⟨j, rfl⟩ := q.modelVertices.surjective j
  obtain ⟨σ, hσ⟩ := h i j
  exact ⟨σ, faceModelAction_apply q σ i j hσ⟩

private abbrev markedFace (q : FacePinnedForm d) (V : FaceRadicals d)
    (h : ∀ i j : I, ∃ σ, diagramRoot ω σ i.val = j.val) : PinnedOrbitDescent F K :=
  q.orbitDescent V (faceOpposite d) (faceModelAction_character q) (faceModelAction_transitive q h)

private theorem faceModelCartan (q : FacePinnedForm d) (V : FaceRadicals d)
    (h : ∀ i j : I, ∃ σ, diagramRoot ω σ i.val = j.val) :
    letI := D.comm
    ∀ i j : I, (markedFace q V h).cartan (q.modelVertices i) (q.modelVertices j) =
      D.datum.rootDatum.pairing j.val i.val := by
  letI := D.comm
  letI := d.posDatum.comm
  letI := q.splitModel.attached.comm
  intro i j
  have he := q.splitModel.datumIso.val.toHom.pairing (i := (q.vertices j).val) (j := (q.vertices i).val)
  change (markedFace q V h).cartan (q.modelVertices i) (q.modelVertices j) =
    d.posDatum.datum.rootDatum.pairing (q.vertices j).val (q.vertices i).val at he
  exact he.trans (q.pairings j i)

private theorem orbitRoot_transitive (i : D.toBased.base.support)
    (x y : orbitRootSet D ω i) : ∃ σ, diagramRoot ω σ x.val = y.val := by
  letI := D.comm
  obtain ⟨a₁, ⟨g, hg⟩, hx⟩ := x.property
  obtain ⟨a₂, ⟨h, hh⟩, hy⟩ := y.property
  refine ⟨h * g⁻¹, ?_⟩
  rw [← hx, ← hy, ← hg, ← hh]
  let ρ : Gal(K/F) →* Equiv.Perm D.base.support := (simplePermutation D).comp ω
  have he : ρ (h * g⁻¹) (ρ g i) = ρ h i := by
    rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel_right]
  exact congrArg Subtype.val he


set_option maxHeartbeats 850000 in
theorem rationalOrbitRankOneModels : RationalOrbitRankOneModels.{u} := by
  intro F K _ _ _ _ _ G T B N P D pair hG hT hmax A₀ A U p a ω i L d hclass hm
  letI := D.comm
  let I := orbitRootSet D ω i
  have hs : ∀ (σ : Gal(K/F)) (α : Root P.pair.T), diagramRoot ω σ α ∈ I ↔ α ∈ I :=
    (orbitRootStability D ω i).2
  obtain ⟨q⟩ := rationalFacePinnedForm d hm hs
  obtain ⟨V⟩ := faceRadicals_nonempty d
  have hh (x y : I) : ∃ σ, diagramRoot ω σ x.val = y.val := orbitRoot_transitive i x y
  let H := markedFace q V hh
  refine ⟨q, V, faceOpposite d, faceModelAction_character q, faceModelAction_transitive q hh, ?_⟩
  change (_ ∧ ∀ x : I, HasOrthogonalOrbitModel H (q.modelVertices x)) ∨
    ∃ j : Fin 2 ≃ I, _ ∧ HasAdjacentOrbitModel H (j.trans q.modelVertices)
  rcases orbitFaceCartan D hclass ω i with hc | ⟨j, hc⟩
  · have hz (a b : SimpleRoot H.P.pair) (hne : a ≠ b) : H.cartan a b = 0 := by
      obtain ⟨x, rfl⟩ := q.modelVertices.surjective a
      obtain ⟨y, rfl⟩ := q.modelVertices.surjective b
      exact (faceModelCartan q V hh x y).trans (hc y x (fun e => hne (congrArg q.modelVertices e.symm)))
    exact Or.inl ⟨hc, fun x => QuasiSplitOrbitPinnedModels.orthogonalPinnedOrbitModel H (q.modelVertices x) hz⟩
  · let k := j.trans q.modelVertices
    have hz (a b : Fin 2) : H.cartan (k a) (k b) = if a = b then 2 else -1 := by
      exact (faceModelCartan q V hh (j a) (j b)).trans (by simpa only [eq_comm] using hc b a)
    obtain ⟨hq, hsep, W, U, m, e, t, s, hE, hU, ht, hmarks, hscalar, hcoords⟩ :=
      QuasiSplitOrbitPinnedModels.adjacentPinnedOrbitModel H k hz
    exact Or.inr ⟨j, hc, hq, hsep, W, U, m, e, t, s, hE, hU, ht,
      fun b => hmarks b (Set.mem_univ b), hscalar, hcoords⟩

end MarkedOrbit

section FaceCorootCoordinates

open _root_.LinearAlgebraicGroups.Specs
open Opposite
open CategoryTheory.Limits
open Specs.AbstractPairing (Root)
open Specs.Pinning (AttachedDatum PinnedGroup SimpleRoot Pinning transportCharacter)
open Specs.RootGroups (AdditiveLine)
open Specs.OrderedRootProducts (RootSubgroupFamily)
open Specs.GeometricRadicals (IsReductive IsTorus IsSemisimple IsSplitTorus)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.QuasiSplitOrbitLevis
open Specs.QuasiSplitOrbitDerivedRoots (diagramRoot)
open Specs.QuasiSplitOrbitAmbientWords (onPoints RationalPoints rationalAlgebra onRational extendPoint groundPointIso)
open Specs.QuasiSplitOrbitPinnedModels (PinnedOrbitDescent MatrixMark)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint unitPoint)
open private mono_over from LinearAlgebraicGroups.Affine.Stabilizers

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
variable {G : AffineAlgebraicGroup F} {T B N : ClosedSubgroup G.val}
variable {P : SplitPairOver (K := K) G T B}
variable {D : AttachedDatum P.pair} {I : Set (Root P.pair.T)} {L : RationalStandardFace D I}
variable {pair : RationalOppositePair T B N}
variable {hG : IsReductive G} {hT : IsTorus T.group} {hmax : IsGeometricallyMaximal T}
variable {A₀ : AdditiveLine F} {A : AdditiveLine K}
variable {U : RootSubgroupFamily P.pair.T} {p : Pinning A P.pair U}
variable {a : (groupBaseChange F K).obj A₀.group ≅ A.group} {ω : Gal(K/F) →* Aut D.toBased}
variable {d : InducedFaceData D (L := L) (pair := pair) (hG := hG) (hT := hT) (hmax := hmax) p a ω}

private abbrev faceCoroot (q : FacePinnedForm d) (i : I) :
    Cocharacter ((groupBaseChange F K).obj L.torus.group) :=
  simpleCorootOfAttachedDatum (inducedPinnedGroup d) d.posDatum
    (simpleRootsOfAttachedDatum (inducedPinnedGroup d) d.posDatum (q.vertices i))

private theorem faceCoroot_ambient (q : FacePinnedForm d) (i : I) :
    letI := D.comm
    faceCoroot q i ≫ (groupBaseChange F K).map L.torusMap =
      (D.datum.rootDatum.coroot i.val).toMul := by
  letI := D.comm
  letI := d.posDatum.comm
  let r : ↥(Specs.StandardParabolicLevi.leviRoots D.datum I) :=
    ⟨i.val, Submodule.subset_span ⟨i.val, i.property, rfl⟩⟩
  have hr : (q.vertices i).val = d.roots r := q.vertexRoot i r rfl
  change (d.posDatum.datum.rootDatum.coroot (q.vertices i).val).toMul ≫
    (L.splitFace D).toAmbientTorus = _
  rw [hr]
  exact (d.rootComparison r).2.1

private theorem faceCoroot_span (q : FacePinnedForm d) :
    letI : IsCommMonObj ((groupBaseChange F K).obj L.torus.group).X := d.posDatum.comm
    Submodule.span ℤ (Set.range (fun i : I => Additive.ofMul (faceCoroot q i))) = ⊤ := by
  letI : IsCommMonObj ((groupBaseChange F K).obj L.torus.group).X := d.posDatum.comm
  letI : IsCommMonObj (inducedPinnedGroup d).pair.T.group.X := d.posDatum.comm
  let H := (L.rationalFace D pair hG hT hmax).group
  have hs : IsSemisimple (L.splitFace D).group :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := K) H
      L.semisimple.1 L.semisimple.2.1).mpr L.semisimple
  have hc : GeometricallySimplyConnected (L.splitFace D).group :=
    QuasiSplitOrbitDerivedRoots.splitDerivedSimplyConnected D I (L.splitFace D) L.integralImage
  obtain ⟨b, hb⟩ := corootBasisOnSimpleRoots (inducedPinnedGroup d) d.posDatum hs hc
  let e := q.vertices.trans (simpleRootsOfAttachedDatum (inducedPinnedGroup d) d.posDatum)
  let c := b.reindex e.symm
  have h : Set.range c = Set.range (fun i : I => Additive.ofMul (faceCoroot q i)) := by
    congr 1
    funext i
    change (b.reindex e.symm) i = _
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, hb]
    rfl
  rw [← h, c.span_eq]

private theorem orbitTrivialization_eq (q : FacePinnedForm d) (V : FaceRadicals d)
    (hop : Specs.UnipotentRadicalIntersection.IsSchemeIntersection
      {d.positive.rational, d.negative.rational} L.torus)
    (hact : ∀ σ j, transportCharacter
      (q.lift (q.descent.outer σ)).asIso.hom.torus j.val.val = (q.modelAction σ j).val.val)
    (htrans : ∀ i j, ∃ σ, q.modelAction σ i = j)
    (t : ∀ C : HopfAlgebraCategory F, specGroup (extendedHopf K C) ≅
        (groupBaseChange F K).obj (specGroup C))
    (ht : Descent.Forms.IsScalarExtensionComparison t) :
    (q.orbitDescent V hop hact htrans).trivialization t = q.groupComparison := by
  apply Iso.ext
  have h := congrArg Iso.hom (q.comparison_eq t ht)
  simpa only [PinnedOrbitDescent.trivialization, FacePinnedForm.orbitDescent,
    Iso.trans_hom, Category.assoc] using h

set_option maxHeartbeats 550000 in
private theorem faceCoroot_coordinates (q : FacePinnedForm d) (hm : PreservesUnits L.scalar)
    (i : I) (R : TestAlgebra K) (v : Rˣ) :
    let R₀ := (restrictTestAlgebra F K).obj R
    let H := q.splitModel.pinned.pair
    baseChangePoint F K H.G.val.X R
      (onPoints q.groupComparison.hom R
        (onPoints ((groupBaseChange F K).map L.torus.inclusion) R (cocharacterPoint (faceCoroot q i) R v))) =
      cocharacterPoint (simpleCorootOfAttachedDatum q.splitModel.pinned q.splitModel.attached
        (q.modelVertices i)) R₀ v ≫ H.T.inclusion.hom.hom := by
  let C := groupBaseChange F K
  let c := faceCoroot q i
  let c₀ := simpleCorootOfAttachedDatum q.splitModel.pinned q.splitModel.attached (q.modelVertices i)
  let M := q.splitModel.pinned.pair
  let R₀ := (restrictTestAlgebra F K).obj R
  have hc : c ≫ q.torusComparison.hom = L.scalar.hom ≫ C.map c₀ := q.coroot (q.vertices i)
  have h : (c ≫ C.map L.torus.inclusion) ≫ q.groupComparison.hom =
      L.scalar.hom ≫ C.map (c₀ ≫ M.T.inclusion) := by
    rw [Category.assoc, q.torusSquare, ← Category.assoc c, hc, Category.assoc, Functor.map_comp]
  have hh := congrArg (fun f => unitPoint R v ≫ f.hom.hom) h
  change baseChangePoint F K M.G.val.X R
    (unitPoint R v ≫ ((c ≫ C.map L.torus.inclusion) ≫ q.groupComparison.hom).hom.hom) =
    unitPoint R₀ v ≫ (c₀ ≫ M.T.inclusion).hom.hom
  rw [hh]
  change baseChangePoint F K M.G.val.X R
    (unitPoint R v ≫ L.scalar.hom.hom.hom ≫ (C.map (c₀ ≫ M.T.inclusion)).hom.hom) = _
  rw [← Category.assoc (unitPoint R v)]
  exact (baseChangePointsSchemeNaturality F K (c₀ ≫ M.T.inclusion).hom.hom R
    (unitPoint R v ≫ L.scalar.hom.hom.hom)).trans
      (congrArg (fun z => z ≫ (c₀ ≫ M.T.inclusion).hom.hom) (hm R v))

end FaceCorootCoordinates

section MarkedRankOneWords

open _root_.LinearAlgebraicGroups.Specs
open Matrix
open Opposite
open CategoryTheory.Limits
open Specs.QuasiSplitOrbitPinnedModels (PinnedOrbitDescent MatrixMark specialLinearPointsOfSize)
open Specs.QuasiSplitOrbitLevis
open Specs.QuasiSplitOrbitAmbientWords (RationalPoints rationalAlgebra onRational)
open Specs.Pinning (SimpleRoot)
open Specs.UnitaryRankOne (splitUpper splitLower splitWord unitaryWeyl unitaryRadicalGenerators
  quadraticConjugation upper lower)
open LinearAlgebraicGroups.WeilRestriction (extendScalars)
open private mark_map_iff from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitPinnedModels

set_option backward.isDefEq.respectTransparency false

variable {F K E : Type u} [Field F] [Field K] [Field E] [Algebra F K] [Algebra F E]

private abbrev GroundMatrices (n : ℕ) := SpecialLinearGroup (Fin n)

private def groundMatrixEquiv (n : ℕ) :
    GroundMatrices n (F ⊗[F] E) ≃* GroundMatrices n E where
  toFun := SpecialLinearGroup.map (Algebra.TensorProduct.lid F E).toRingEquiv.toRingHom
  invFun := SpecialLinearGroup.map (Algebra.TensorProduct.lid F E).symm.toRingEquiv.toRingHom
  left_inv g := by ext i j; exact (Algebra.TensorProduct.lid F E).symm_apply_apply _
  right_inv g := by ext i j; exact (Algebra.TensorProduct.lid F E).apply_symm_apply _
  map_mul' := map_mul _

private theorem groundMatrixEquiv_marks (n : ℕ) (j : MatrixMark) (x : GroundMatrices n (F ⊗[F] E)) :
    j.Holds (groundMatrixEquiv n x) ↔ j.Holds x :=
  mark_map_iff (Algebra.TensorProduct.lid F E).toRingEquiv.toRingHom
    (Algebra.TensorProduct.lid F E).injective j x

private theorem matrix_eq_diagonal {n : ℕ} (x : GroundMatrices n E)
    (h : MatrixMark.torus.Holds x) :
    x.val = Matrix.diagonal (fun i => x.val i i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · rw [Matrix.diagonal_apply_ne _ hij]
    exact h i j hij

private theorem diagonal_two_units (x : GroundMatrices 2 E)
    (h : MatrixMark.torus.Holds x) :
    ∃ t : Eˣ, x.val = Matrix.diagonal ![(t : E), (↑t⁻¹ : E)] := by
  have hdet := x.property
  change x.val.det = 1 at hdet
  rw [Matrix.det_fin_two, h 0 1 (by decide), zero_mul, sub_zero] at hdet
  let t : Eˣ := ⟨x.val 0 0, x.val 1 1, hdet, by rw [mul_comm, hdet]⟩
  refine ⟨t, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> first | rfl | exact h _ _ (by decide)

private theorem splitUpper_mark (x : E) : MatrixMark.positiveRadical.Holds (splitUpper x) := by
  change (splitUpper x).val.IsUpperTriangular ∧ ∀ i, (splitUpper x).val i i = 1
  simp only [splitUpper, SpecialLinearGroup.transvection_coe]
  constructor
  · intro i j hij
    change j < i at hij
    fin_cases i <;> fin_cases j <;> simp_all [Fin.lt_def]
  · intro i
    fin_cases i <;> simp

private theorem splitLower_mark (x : E) : MatrixMark.negativeRadical.Holds (splitLower x) := by
  change (splitLower x).val.IsLowerTriangular ∧ ∀ i, (splitLower x).val i i = 1
  simp only [splitLower, SpecialLinearGroup.transvection_coe]
  constructor
  · intro i j hij
    change i < j at hij
    fin_cases i <;> fin_cases j <;> simp_all [Fin.lt_def]
  · intro i
    fin_cases i <;> simp

private theorem unitaryUpper_mark [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    (x : GroundMatrices 3 E) (a b : E) (hx : x.val = upper (quadraticConjugation F E) 1 a b) :
    MatrixMark.positiveRadical.Holds x := by
  change x.val.IsUpperTriangular ∧ ∀ i, x.val i i = 1
  rw [hx]
  constructor
  · intro i j hij
    change j < i at hij
    fin_cases i <;> fin_cases j <;> simp_all [Fin.lt_def, upper]
  · intro i
    fin_cases i <;> rfl

private theorem unitaryLower_mark [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    (x : GroundMatrices 3 E) (a b : E) (hx : x.val = lower (quadraticConjugation F E) 1 a b) :
    MatrixMark.negativeRadical.Holds x := by
  change x.val.IsLowerTriangular ∧ ∀ i, x.val i i = 1
  rw [hx]
  constructor
  · intro i j hij
    change i < j at hij
    fin_cases i <;> fin_cases j <;> simp_all [Fin.lt_def, lower]
  · intro i
    fin_cases i <;> rfl

private def orbitRadicalWords (H : PinnedOrbitDescent F K) : Subgroup (RationalPoints H.G.val) :=
  Subgroup.closure {x | x ∈ SubgroupSections (H.mark .positiveRadical) _ ∨
    x ∈ SubgroupSections (H.mark .negativeRadical) _}

private theorem orbitTorus_mark (H : PinnedOrbitDescent F K) (t : RationalPoints H.T.group) :
    onRational H.T.inclusion t ∈ SubgroupSections (H.mark .torus) _ :=
  ⟨t, rfl⟩

private theorem orthogonalMatrixWords (H : PinnedOrbitDescent F K)
    (e : RationalPoints H.G.val ≃* GroundMatrices 2 E)
    (h : ∀ b x, b.Holds (e x) ↔ x ∈ SubgroupSections (H.mark b) _) :
    (∀ t : RationalPoints H.T.group, onRational H.T.inclusion t ∈ orbitRadicalWords H) ∧
    e.symm (splitWord 1) ∈ orbitRadicalWords H := by
  let Q := orbitRadicalWords H
  have hu (a : E) : e.symm (splitUpper a) ∈ Q := by
    apply Subgroup.subset_closure
    left
    apply (h .positiveRadical _).mp
    rw [e.apply_symm_apply]
    exact splitUpper_mark a
  have hl (a : E) : e.symm (splitLower a) ∈ Q := by
    apply Subgroup.subset_closure
    right
    apply (h .negativeRadical _).mp
    rw [e.apply_symm_apply]
    exact splitLower_mark a
  obtain ⟨ht, hw⟩ := splitWordsTransfer Q e.symm.toMonoidHom hu hl
  refine ⟨fun t => ?_, hw⟩
  let g := onRational H.T.inclusion t
  have hdiag := diagonal_two_units (e g) ((h .torus g).mpr (orbitTorus_mark H t))
  have hg := ht (e g) hdiag
  simpa only [MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using hg

private theorem adjacentMatrixWords [Infinite F] [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    (H : PinnedOrbitDescent F K) (M : Subgroup (GroundMatrices 3 E))
    (e : RationalPoints H.G.val ≃* M)
    (hform : ∀ x, x ∈ M ↔ Specs.UnitaryRankOne.PreservesForm (quadraticConjugation F E) 1 x.val)
    (h : ∀ b x, b.Holds (e x).val ↔ x ∈ SubgroupSections (H.mark b) _) :
    (∀ t : RationalPoints H.T.group, onRational H.T.inclusion t ∈ orbitRadicalWords H) ∧
    ∃ w : M, w.val.val = unitaryWeyl E ∧ e.symm w ∈ orbitRadicalWords H := by
  let Q := orbitRadicalWords H
  have hU (x : M) (hx : x.val ∈ unitaryRadicalGenerators (quadraticConjugation F E) 1) :
      e.symm x ∈ Q := by
    obtain ⟨a, b, _, hp | hn⟩ := hx
    · apply Subgroup.subset_closure
      left
      apply (h .positiveRadical _).mp
      rw [e.apply_symm_apply]
      exact unitaryUpper_mark x.val a b hp
    · apply Subgroup.subset_closure
      right
      apply (h .negativeRadical _).mp
      rw [e.apply_symm_apply]
      exact unitaryLower_mark x.val a b hn
  obtain ⟨ht, hw⟩ := unitaryWordsTransfer M Q e.symm.toMonoidHom hform hU
  refine ⟨fun t => ?_, hw⟩
  let g := onRational H.T.inclusion t
  have hi := matrix_eq_diagonal (e g).val ((h .torus g).mpr (orbitTorus_mark H t))
  have hg := ht (e g) ⟨_, hi⟩
  simpa only [MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using hg

end MarkedRankOneWords

section WordNormalizes

open _root_.LinearAlgebraicGroups.Specs
open Opposite CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.QuasiSplitOrbitAmbientWords (onPoints RationalPoints rationalAlgebra extendPoint groundPointIso)
open CocharacterDynamics (cocharacterPoint unitPoint factorsThroughClosed_iff)
open private conjugate rationalConstant comp_conjugate from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private normalizes_iff_sections from LinearAlgebraicGroups.RootData.BorelNormalizer
open private cocharacterPoint_inv from LinearAlgebraicGroups.RootData.RootGroups

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

private def evalCocharacter {S : GroupScheme k} [IsCommMonObj S.X]
    (R : TestAlgebra k) (t : Rˣ) : Cocharacter S →* GroupPoints S R where
  toFun c := cocharacterPoint c R t
  map_one' := by
    change unitPoint R t ≫ (1 : _ ⟶ S.X) = 1
    exact MonObj.comp_one _
  map_mul' c d := by
    change unitPoint R t ≫ (c.hom.hom * d.hom.hom) =
      (unitPoint R t ≫ c.hom.hom) * (unitPoint R t ≫ d.hom.hom)
    exact MonObj.comp_mul _ _ _

private theorem cocharacter_lifts_generate {H : GroupScheme k} (S : ClosedSubgroup H)
    (hS : IsSplitTorus S.group) [IsCommMonObj S.group.X]
    {J : Type u} (b : J → Cocharacter S.group)
    (hb : Submodule.span ℤ (Set.range (fun j => Additive.ofMul (b j))) = ⊤)
    (R : TestAlgebra k) (Q : Subgroup (GroupPoints S.group R))
    (h : ∀ j t, cocharacterPoint (b j) R t ∈ Q) : Q = ⊤ := by
  apply subgroup_eq_top_of_cocharacters hS
  intro c t
  let M := (Q.comap (evalCocharacter R t)).toAddSubgroup.toIntSubmodule
  have hspan : Submodule.span ℤ (Set.range (fun j => Additive.ofMul (b j))) ≤ M :=
    Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact h j t)
  apply hspan
  rw [hb]
  exact Submodule.mem_top

private theorem normalize_from_coroots {H : GroupScheme k} (S : ClosedSubgroup H)
    (hS : IsSplitTorus S.group) [IsCommMonObj S.group.X] {J : Type u}
    (b : J → Cocharacter S.group)
    (hb : Submodule.span ℤ (Set.range (fun j => Additive.ofMul (b j))) = ⊤)
    (x : 𝟙_ (SchemeOver k) ⟶ H.X) (π : Equiv.Perm J)
    (h : ∀ (R : TestAlgebra k) j (t : Rˣ),
      conjugate x (onPoints S.inclusion R (cocharacterPoint (b j) R t)) =
        onPoints S.inclusion R (cocharacterPoint (b (π j)) R t⁻¹)) :
    Normalizes S.inclusion x := by
  have factor (y : 𝟙_ (SchemeOver k) ⟶ H.X)
      (hy : ∀ (R : TestAlgebra k) j (t : Rˣ),
        conjugate y (onPoints S.inclusion R (cocharacterPoint (b j) R t)) ∈
          (onPoints S.inclusion R).range) :
      ∃ f, f ≫ S.inclusion.hom.hom = conjugate y S.inclusion.hom.hom := by
    apply (factorsThroughClosed_iff S.inclusion.hom.hom S.isClosedImmersion _).mpr
    intro R s
    let yR : GroupPoints H R := rationalConstant y
    let f := (MulAut.conj yR).toMonoidHom.comp (onPoints S.inclusion R)
    let Q := (onPoints S.inclusion R).range.comap f
    have hQ := cocharacter_lifts_generate S hS b hb R Q (hy R)
    have hs : s ∈ Q := hQ.symm ▸ Subgroup.mem_top s
    rw [comp_conjugate]
    exact hs
  obtain ⟨f, hf⟩ := factor x (fun R j t => ⟨_, (h R j t).symm⟩)
  have hi (R : TestAlgebra k) (j : J) (t : Rˣ) :
      conjugate x⁻¹ (onPoints S.inclusion R (cocharacterPoint (b j) R t)) =
        onPoints S.inclusion R (cocharacterPoint (b (π.symm j)) R t⁻¹) := by
    have e := h R (π.symm j) t⁻¹
    rw [π.apply_symm_apply, inv_inv] at e
    rw [← e]
    simp only [conjugate, rationalConstant, GrpObj.comp_inv, inv_inv]
    group
  obtain ⟨g, hg⟩ := factor x⁻¹ (fun R j t => ⟨_, (hi R j t).symm⟩)
  apply (normalizes_iff_sections S x).mpr
  intro Y y s
  have hy : y = toUnit Y := Subsingleton.elim _ _
  subst y
  constructor
  · refine ⟨s ≫ f, ?_⟩
    change (s ≫ f) ≫ S.inclusion.hom.hom = _
    rw [Category.assoc, hf, comp_conjugate]
    rfl
  · refine ⟨s ≫ g, ?_⟩
    change (s ≫ g) ≫ S.inclusion.hom.hom = _
    rw [Category.assoc, hg, comp_conjugate]
    simp only [conjugate, rationalConstant, GrpObj.comp_inv, inv_inv]

end WordNormalizes

section WordScalarPoints

open _root_.LinearAlgebraicGroups.Specs
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.Limits
open Specs.AdjointRepresentation (GroupPoints)
open Specs.QuasiSplitOrbitAmbientWords (RationalPoints rationalAlgebra extendPoint groundPointIso)
open private rationalConstant from LinearAlgebraicGroups.Reductive.MaximalToriConjugate

set_option backward.isDefEq.respectTransparency false

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

private def rationalAlgebraMap (R : TestAlgebra F) : rationalAlgebra F ⟶ R :=
  CommAlgCat.ofHom (Algebra.ofId F R)

private theorem mapPoints_rationalConstant {X : GroupScheme F} (x : RationalPoints X)
    (R : TestAlgebra F) :
    mapPoints (rationalAlgebraMap R) x = rationalConstant ((groundPointIso F).hom ≫ x) := by
  change (testSpec F).map (rationalAlgebraMap R).op ≫ x = toUnit _ ≫ (groundPointIso F).hom ≫ x
  have e : (testSpec F).map (rationalAlgebraMap R).op = toUnit _ ≫ (groundPointIso F).hom := by
    apply (cancel_mono (groundPointIso F).inv).mp
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact Subsingleton.elim _ _
  rw [e, Category.assoc]

private theorem baseChange_of_rationalConstant (X : GroupScheme F) (x : RationalPoints X)
    (R : TestAlgebra K) :
    baseChangePoint F K X.X R
      (rationalConstant ((groundPointIso K).hom ≫ extendPoint (K := K) X x)) =
        mapPoints (rationalAlgebraMap ((restrictTestAlgebra F K).obj R)) x := by
  let C := baseChange F K
  let Y : SchemeOver F := (testSpec F).obj (.op (rationalAlgebra F))
  let u := Functor.LaxMonoidal.ε C
  let x₀ := (groundPointIso F).hom ≫ x
  let S := (testSpec K).obj (.op R)
  change baseChangePoint F K X.X R (toUnit S ≫ (groundPointIso K).hom ≫
    (groundPointIso K).inv ≫ u ≫ C.map x₀) = _
  rw [Iso.hom_inv_id_assoc]
  rw [← Category.assoc (toUnit S)]
  refine (baseChangePointsSchemeNaturality F K x₀ R (toUnit S ≫ u)).trans ?_
  rw [mapPoints_rationalConstant]
  have e : baseChangePoint F K (𝟙_ (SchemeOver F)) R (toUnit S ≫ u) = toUnit _ :=
    Subsingleton.elim _ _
  rw [e]

end WordScalarPoints

section MatrixScalarSpecialization

open _root_.LinearAlgebraicGroups.Specs
open Matrix
open Specs.AdjointRepresentation (GroupPoints)
open Specs.QuasiSplitOrbitAmbientWords (RationalPoints rationalAlgebra)
open Specs.QuasiSplitOrbitPinnedModels (specialLinearPointsOfSize)
open LinearAlgebraicGroups.WeilRestriction (extendScalars)

set_option backward.isDefEq.respectTransparency false

variable {F E : Type u} [Field F] [Field E] [Algebra F E]

private theorem scalar_projection_on_ground_matrix (n : ℕ) (R : TestAlgebra F)
    (e : E →ₐ[F] R) (g : GroundMatrices n (F ⊗[F] E)) :
    SpecialLinearGroup.map (Algebra.TensorProduct.lift (AlgHom.id F R) e
      (fun _ _ => Commute.all _ _)).toRingHom
      (SpecialLinearGroup.map (Algebra.TensorProduct.map (Algebra.ofId F R) (AlgHom.id F E)).toRingHom g) =
    SpecialLinearGroup.map e.toRingHom (groundMatrixEquiv n g) := by
  let f := Algebra.TensorProduct.lift (AlgHom.id F R) e (fun _ _ => Commute.all _ _)
  let a := Algebra.TensorProduct.map (Algebra.ofId F R) (AlgHom.id F E)
  let b := Algebra.TensorProduct.lid F E
  have hb : f.comp a = e.comp b.toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro x y
    simp [f, a, b, Algebra.smul_def]
  apply Subtype.ext
  ext i j
  exact DFunLike.congr_fun hb (g.val i j)

private theorem scalar_projection_on_ground_points (n : ℕ) {X : GroupScheme F}
    (w : (groupPointsFunctor F).obj X ⟶ extendScalars F E ⋙ specialLinearPointsOfSize n E)
    (x : RationalPoints X) (R : TestAlgebra F) (e : E →ₐ[F] R) :
    SpecialLinearGroup.map (Algebra.TensorProduct.lift (AlgHom.id F R) e
      (fun _ _ => Commute.all _ _)).toRingHom
      (w.app R (mapPoints (rationalAlgebraMap R) x)) =
    SpecialLinearGroup.map e.toRingHom (groundMatrixEquiv n (w.app (rationalAlgebra F) x)) := by
  have hn := w.naturality_apply (rationalAlgebraMap R) x
  change w.app R (mapPoints (rationalAlgebraMap R) x) =
    SpecialLinearGroup.map (Algebra.TensorProduct.map (Algebra.ofId F R) (AlgHom.id F E)).toRingHom
      (w.app (rationalAlgebra F) x) at hn
  rw [hn]
  exact scalar_projection_on_ground_matrix n R e _

private def pointsMulEquiv {k : Type u} [Field k] {X Y : GroupScheme k}
    (e : X ≅ Y) (R : TestAlgebra k) : GroupPoints X R ≃* GroupPoints Y R :=
  (((groupPointsFunctor k).mapIso e).app R).groupIsoToMulEquiv

private theorem map_splitWord_one_ring {k R : Type u} [Field k] [CommRing R] (f : k →+* R) :
    SpecialLinearGroup.map f (Specs.UnitaryRankOne.splitWord 1) = Specs.UnitaryRankOne.splitWord 1 := by
  apply Subtype.ext
  change (Specs.UnitaryRankOne.splitWord (1 : kˣ)).val.map f =
    (Specs.UnitaryRankOne.splitWord (1 : Rˣ)).val
  rw [(UnitaryRankOne.splitRankOneWords.1 (1 : kˣ)).1, (UnitaryRankOne.splitRankOneWords.1 (1 : Rˣ)).1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem splitWord_conjugates_diagonal {R : Type u} [CommRing R]
    (g h : GroundMatrices 2 R) (v : Rˣ)
    (hg : g.val = Matrix.diagonal ![(v : R), (↑v⁻¹ : R)])
    (hh : h.val = Matrix.diagonal ![(↑v⁻¹ : R), (v : R)]) :
    Specs.UnitaryRankOne.splitWord 1 * g * (Specs.UnitaryRankOne.splitWord (1 : Rˣ))⁻¹ = h := by
  have e : g = Specs.UnitaryRankOne.splitWord v * Specs.UnitaryRankOne.splitWord (-1) :=
    Subtype.ext (hg.trans (UnitaryRankOne.splitRankOneWords.1 v).2.symm)
  apply Subtype.ext
  rw [e, splitWeylCorootAction _, hh]

private theorem unitaryFlip_conjugates_coroot {R : Type u} [CommRing R]
    (w : GroundMatrices 3 R) (hw : w.val = !![0, 0, 1; 0, -1, 0; 1, 0, 0])
    (i : Fin 2) (t : Rˣ) :
    w * Specs.QuasiSplitOrbitPinnedModels.matrixSimpleCoroot i t * w⁻¹ =
      Specs.QuasiSplitOrbitPinnedModels.matrixSimpleCoroot i.rev t⁻¹ := by
  have hsq : w * w = 1 := by
    apply Subtype.ext
    change w.val * w.val = 1
    rw [hw]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  rw [inv_eq_of_mul_eq_one_left hsq]
  apply Subtype.ext
  change w.val * (Specs.QuasiSplitOrbitPinnedModels.matrixSimpleCoroot i t).val * w.val = _
  rw [hw]
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [Specs.QuasiSplitOrbitPinnedModels.matrixSimpleCoroot,
      Specs.SpecialLinearDatum.coordinatePairUnits, Matrix.mul_apply, Matrix.vecMul_diagonal,
      Fin.sum_univ_three, Fin.rev]

private theorem map_unitaryFlip {k R : Type u} [Field k] [CommRing R] (f : k →+* R)
    (g : GroundMatrices 3 k) (hg : g.val = Specs.UnitaryRankOne.unitaryWeyl k) :
    (SpecialLinearGroup.map f g).val = !![0, 0, 1; 0, -1, 0; 1, 0, 0] := by
  change g.val.map f = _
  rw [hg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Specs.UnitaryRankOne.unitaryWeyl]

end MatrixScalarSpecialization

section FaceWordWitnesses

open _root_.LinearAlgebraicGroups.Specs
open Matrix Opposite CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Specs.AbstractPairing (Root)
open Specs.Pinning (AttachedDatum SimpleRoot Pinning)
open Specs.RootGroups (AdditiveLine rootPoint)
open Specs.OrderedRootProducts (RootSubgroupFamily)
open Specs.GeometricRadicals (IsReductive IsTorus)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.QuasiSplitOrbitLevis
open Specs.QuasiSplitOrbitDerivedRoots (diagramRoot pinnedRootMap)
open Specs.QuasiSplitOrbitAmbientWords (onPoints onRational RationalPoints rationalAlgebra extendPoint groundPointIso)
open Specs.QuasiSplitOrbitPinnedModels (PinnedOrbitDescent MatrixMark specialLinearPointsOfSize)
open Specs.UnitaryRankOne (splitWord unitaryWeyl)
open Specs.AdjointRepresentation (GroupPoints)
open CocharacterDynamics (cocharacterPoint)
open private rationalConstant conjugate from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open LinearAlgebraicGroups.WeilRestriction (extendScalars)

set_option backward.isDefEq.respectTransparency false

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
variable {G : AffineAlgebraicGroup F} {T B N : ClosedSubgroup G.val}
variable {P : SplitPairOver (K := K) G T B}
variable {D : AttachedDatum P.pair} {I : Set (Root P.pair.T)} {L : RationalStandardFace D I}
variable {pair : RationalOppositePair T B N}
variable {hG : IsReductive G} {hT : IsTorus T.group} {hmax : IsGeometricallyMaximal T}
variable {A₀ : AdditiveLine F} {A : AdditiveLine K}
variable {U : RootSubgroupFamily P.pair.T} {p : Pinning A P.pair U}
variable {a : (groupBaseChange F K).obj A₀.group ≅ A.group} {ω : Gal(K/F) →* Aut D.toBased}
variable {d : InducedFaceData D (L := L) (pair := pair) (hG := hG) (hT := hT) (hmax := hmax) p a ω}

private abbrev splitFaceCorootPoint (q : FacePinnedForm d) (R : TestAlgebra K)
    (i : I) (t : Rˣ) :
    GroupPoints ((groupBaseChange F K).obj L.derived.group) R :=
  onPoints ((groupBaseChange F K).map L.torus.inclusion) R (cocharacterPoint (faceCoroot q i) R t)

private abbrev splitWordSection (x : RationalPoints L.derived.group) :
    𝟙_ (SchemeOver K) ⟶ ((groupBaseChange F K).obj L.derived.group).X :=
  (groundPointIso K).hom ≫ extendPoint (K := K) L.derived.group x

private def FaceWordConjugates (q : FacePinnedForm d) (x : RationalPoints L.derived.group)
    (π : Equiv.Perm I) : Prop :=
  ∀ (R : TestAlgebra K) i (v : Rˣ),
    conjugate (splitWordSection (K := K) x) (splitFaceCorootPoint q R i v) =
      splitFaceCorootPoint q R (π i) v⁻¹

private def FaceWordWitness (q : FacePinnedForm d) (V : FaceRadicals d)
    (h : ∀ i j : I, ∃ σ, diagramRoot ω σ i.val = j.val) : Prop :=
  let H := markedFace q V h
  (∀ t : RationalPoints L.torus.group, onRational L.torus.inclusion t ∈ orbitRadicalWords H) ∧
  ∃ (x : RationalPoints L.derived.group) (π : Equiv.Perm I),
    x ∈ orbitRadicalWords H ∧ FaceWordConjugates q x π

set_option maxHeartbeats 950000 in
private theorem orthogonalFaceWord (q : FacePinnedForm d) (V : FaceRadicals d)
    (h : ∀ i j : I, ∃ σ, diagramRoot ω σ i.val = j.val) (hm : PreservesUnits L.scalar)
    (i₀ : I) (model : HasOrthogonalOrbitModel (markedFace q V h) (q.modelVertices i₀)) :
    FaceWordWitness q V h := by
  let H := markedFace q V h
  let E := Specs.QuasiSplitOrbitPinnedModels.orbitField H.action (q.modelVertices i₀)
  obtain ⟨W, f, m, emb, t, s, ht, hmark, _, _, hscalar, hcoords⟩ := model
  let w := (groupPointsFunctor F).map f.hom ≫ m.hom
  let e := (pointsMulEquiv f (rationalAlgebra F)).trans
    (((m.app (rationalAlgebra F)).groupIsoToMulEquiv).trans (groundMatrixEquiv 2))
  have emark (b : MatrixMark) (x : RationalPoints H.G.val) :
      b.Holds (e x) ↔ x ∈ SubgroupSections (H.mark b) _ :=
    (groundMatrixEquiv_marks 2 b (w.app (rationalAlgebra F) x)).trans (hmark b _ x)
  obtain ⟨htorus, hword⟩ := orthogonalMatrixWords H e emark
  let x := e.symm (splitWord 1)
  let y := splitWordSection (K := K) (L := L) x
  have hcomparison : H.trivialization t = q.groupComparison := orbitTrivialization_eq q V
    (faceOpposite d) (faceModelAction_character q) (faceModelAction_transitive q h) t ht
  let φ (R : TestAlgebra K) := (pointsMulEquiv q.groupComparison R).trans (s R)
  have hx (R : TestAlgebra K) (j : SimpleRoot H.P.pair) :
      φ R (rationalConstant y) j = splitWord 1 := by
    let R₀ := (restrictTestAlgebra F K).obj R
    letI : Algebra K R₀ := inferInstanceAs (Algebra K R)
    letI : IsScalarTower F K R₀ := IsScalarTower.of_algebraMap_eq' rfl
    let u := ((Algebra.ofId K R₀).restrictScalars F).comp (emb j)
    have he := hscalar R j (rationalConstant y)
    rw [hcomparison] at he
    change φ R (rationalConstant y) j =
      SpecialLinearGroup.map (Algebra.TensorProduct.lift (AlgHom.id F R₀) u
        (fun _ _ => Commute.all _ _)).toRingHom
        (w.app R₀ (baseChangePoint F K H.G.val.X R (rationalConstant y))) at he
    have hbc : baseChangePoint F K H.G.val.X R (rationalConstant y) =
        mapPoints (rationalAlgebraMap R₀) x := baseChange_of_rationalConstant H.G.val x R
    rw [he, hbc, scalar_projection_on_ground_points 2 w x R₀ u]
    change SpecialLinearGroup.map u.toRingHom (e x) = _
    rw [e.apply_symm_apply]
    exact map_splitWord_one_ring u.toRingHom
  have hc (R : TestAlgebra K) (i : I) (v : Rˣ) :
      (φ R (splitFaceCorootPoint q R i v) (q.modelVertices i)).val =
        Matrix.diagonal ![(v : R), (↑v⁻¹ : R)] ∧
      ∀ j : SimpleRoot H.P.pair, j ≠ q.modelVertices i → φ R (splitFaceCorootPoint q R i v) j = 1 := by
    let R₀ := (restrictTestAlgebra F K).obj R
    let j := q.modelVertices i
    let z := rootPoint (pinnedRootMap H.P.pin j) R₀ (0 : R)
    obtain ⟨z', hz'⟩ := (baseChangePoints F K H.P.pair.G.val.X R).2 z
    let c := pointsMulEquiv q.groupComparison R (splitFaceCorootPoint q R i v)
    have h₀ := hcoords R j 0 v z' c hz' (faceCoroot_coordinates q hm i R v)
    exact ⟨h₀.2.1, fun j' hj' => (h₀.2.2 j' hj').2⟩
  refine ⟨htorus, x, Equiv.refl I, hword, ?_⟩
  intro R i v
  apply (φ R).injective
  let xR : GroupPoints ((groupBaseChange F K).obj L.derived.group) R := rationalConstant y
  change φ R (xR * splitFaceCorootPoint q R i v *
      (xR)⁻¹) = φ R (splitFaceCorootPoint q R i v⁻¹)
  simp only [map_mul, map_inv]
  funext j
  change φ R (rationalConstant y) j * φ R (splitFaceCorootPoint q R i v) j *
    (φ R (rationalConstant y) j)⁻¹ = φ R (splitFaceCorootPoint q R i v⁻¹) j
  rw [show φ R (rationalConstant y) j = splitWord 1 from hx R j]
  by_cases hj : j = q.modelVertices i
  · subst j
    apply splitWord_conjugates_diagonal _ _ v (hc R i v).1
    simpa only [inv_inv] using (hc R i v⁻¹).1
  · rw [(hc R i v).2 j hj, (hc R i v⁻¹).2 j hj, mul_one, mul_inv_cancel]

set_option maxHeartbeats 950000 in
private theorem adjacentFaceWord [Infinite F] (q : FacePinnedForm d) (V : FaceRadicals d)
    (h : ∀ i j : I, ∃ σ, diagramRoot ω σ i.val = j.val) (hm : PreservesUnits L.scalar)
    (j : Fin 2 ≃ I) (model : HasAdjacentOrbitModel (markedFace q V h) (j.trans q.modelVertices)) :
    FaceWordWitness q V h := by
  let H := markedFace q V h
  let J := j.trans q.modelVertices
  let E := Specs.QuasiSplitOrbitPinnedModels.orbitField (H.adjacentAction J) 0
  obtain ⟨hq, hs, W, U, m, f, t, s, _, hU, ht, hmark, hscalar, hcoords⟩ := model
  letI : Algebra.IsQuadraticExtension F E := hq
  letI : Algebra.IsSeparable F E := hs
  obtain ⟨M, e₀, hform, he₀⟩ := hyperbolicUnitaryRationalPoints F E W U m hU
  let w := (groupPointsFunctor F).map (f.hom ≫ U.inclusion) ≫ m.hom
  let e := (pointsMulEquiv f (rationalAlgebra F)).trans e₀
  have he (x : RationalPoints H.G.val) : (e x).val =
      groundMatrixEquiv 3 (w.app (rationalAlgebra F) x) := by
    have hp := he₀ (pointsMulEquiv f (rationalAlgebra F) x)
    change (e x).val = groundMatrixEquiv 3
      (m.hom.app (rationalAlgebra F)
        ((onRational f.hom x) ≫ U.inclusion.hom.hom)) at hp
    have eq : (onRational f.hom x) ≫ U.inclusion.hom.hom =
        onRational (f.hom ≫ U.inclusion) x := by
      change (x ≫ f.hom.hom.hom) ≫ U.inclusion.hom.hom = x ≫ (f.hom ≫ U.inclusion).hom.hom
      rw [Category.assoc, Grp.comp_hom_hom]
    exact hp.trans (congrArg (fun z => groundMatrixEquiv 3 (m.hom.app (rationalAlgebra F) z)) eq)
  have emark (b : MatrixMark) (x : RationalPoints H.G.val) :
      b.Holds (e x).val ↔ x ∈ SubgroupSections (H.mark b) _ :=
    by
      rw [he]
      exact (groundMatrixEquiv_marks 3 b (w.app (rationalAlgebra F) x)).trans (hmark b _ x)
  obtain ⟨htorus, g, hg, hword⟩ := adjacentMatrixWords H M e hform emark
  let x := e.symm g
  let y := splitWordSection (K := K) (L := L) x
  have hcomparison : H.trivialization t = q.groupComparison := orbitTrivialization_eq q V
    (faceOpposite d) (faceModelAction_character q) (faceModelAction_transitive q h) t ht
  let φ (R : TestAlgebra K) :=
    (pointsMulEquiv q.groupComparison R).trans ((s.app R).groupIsoToMulEquiv)
  have hx (R : TestAlgebra K) :
      (φ R (rationalConstant y)).val = !![0, 0, 1; 0, -1, 0; 1, 0, 0] := by
    let R₀ := (restrictTestAlgebra F K).obj R
    letI : Algebra K R₀ := inferInstanceAs (Algebra K R)
    letI : IsScalarTower F K R₀ := IsScalarTower.of_algebraMap_eq' rfl
    let u := ((Algebra.ofId K R₀).restrictScalars F).comp E.val
    have he' := hscalar R (rationalConstant y)
    rw [hcomparison] at he'
    change φ R (rationalConstant y) =
      SpecialLinearGroup.map (Algebra.TensorProduct.lift (AlgHom.id F R₀) u
        (fun _ _ => Commute.all _ _)).toRingHom
        (w.app R₀ (baseChangePoint F K H.G.val.X R (rationalConstant y))) at he'
    have hbc : baseChangePoint F K H.G.val.X R (rationalConstant y) =
        mapPoints (rationalAlgebraMap R₀) x := baseChange_of_rationalConstant H.G.val x R
    rw [hbc] at he'
    have hsc := scalar_projection_on_ground_points 3 w x R₀ u
    have hg₀ : (e x).val = g.val := congrArg Subtype.val (e.apply_symm_apply g)
    have hy : φ R (rationalConstant y) = SpecialLinearGroup.map u.toRingHom g.val :=
      he'.trans (hsc.trans (congrArg (SpecialLinearGroup.map u.toRingHom) ((he x).symm.trans hg₀)))
    exact (congrArg (fun v : GroundMatrices 3 R => v.val) hy).trans
      (map_unitaryFlip u.toRingHom g.val hg)
  have hc (R : TestAlgebra K) (i : Fin 2) (v : Rˣ) :
      φ R (splitFaceCorootPoint q R (j i) v) =
        Specs.QuasiSplitOrbitPinnedModels.matrixSimpleCoroot i v := by
    let R₀ := (restrictTestAlgebra F K).obj R
    let z := rootPoint (pinnedRootMap H.P.pin (J i)) R₀ (0 : R)
    obtain ⟨z', hz'⟩ := (baseChangePoints F K H.P.pair.G.val.X R).2 z
    let c := pointsMulEquiv q.groupComparison R (splitFaceCorootPoint q R (j i) v)
    exact (hcoords R i 0 v z' c hz' (faceCoroot_coordinates q hm (j i) R v)).2
  let r : Equiv.Perm (Fin 2) := ⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩
  let π := j.symm.trans (r.trans j)
  refine ⟨htorus, x, π, hword, ?_⟩
  intro R i v
  obtain ⟨k, rfl⟩ := j.surjective i
  apply (φ R).injective
  let xR : GroupPoints ((groupBaseChange F K).obj L.derived.group) R := rationalConstant y
  change φ R (xR * splitFaceCorootPoint q R (j k) v *
      (xR)⁻¹) = φ R (splitFaceCorootPoint q R (π (j k)) v⁻¹)
  have eπ : π (j k) = j k.rev := by
    change j (r (j.symm (j k))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  rw [map_mul, map_mul, map_inv, eπ, hc, hc]
  exact unitaryFlip_conjugates_coroot _ (hx R) k v

end FaceWordWitnesses

section AmbientOrbitWords

open _root_.LinearAlgebraicGroups.Specs
open Opposite CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Specs.AbstractPairing (Root)
open Specs.Pinning (AttachedDatum Pinning)
open Specs.RootGroups (AdditiveLine)
open Specs.OrderedRootProducts (RootSubgroupFamily)
open Specs.GeometricRadicals (IsReductive IsTorus baseChangedSubgroup)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.QuasiSplitOrbitLevis
open Specs.QuasiSplitOrbitDerivedRoots (diagramRoot)
open Specs.QuasiSplitOrbitAmbientWords (onPoints onRational RationalPoints rationalAlgebra extendPoint groundPointIso BorelRadical)
open Specs.QuasiSplitOrbitPinnedModels (PinnedOrbitDescent MatrixMark)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open Specs.CharacterPairing (pairing)
open Specs.StandardParabolicLevi (HasFace leviRoots parabolicWeylGroup)
open Specs.SimpleRoots (IsBaseFor evaluate)
open Specs.BorelsAndChambers (IsRegular)
open CocharacterDynamics (cocharacterPoint unitPoint)
open private rationalConstant conjugate comp_conjugate conjugate_comp
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies
open private extendPoint_natural normalizes_of_extended from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitAmbientWords
open private hasConstantLabel conjugationForLabel from LinearAlgebraicGroups.Reductive.CentralDerived
open private face_stabilizes_cocharacter representative_in_limit_iff from LinearAlgebraicGroups.Flag.StandardParabolicLevi
open private exists_weylIdentification from LinearAlgebraicGroups.Classification.TransportedRootCoordinates
open private attachedBase_regular from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitDerivedRoots
open private mono_over from LinearAlgebraicGroups.Affine.Stabilizers
open private cocharacter_ext_units from LinearAlgebraicGroups.RootData.RankOneFlag
open private cocharacterPoint_postcompose from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private cocharacterPoint_inv from LinearAlgebraicGroups.RootData.RootGroups

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
variable {G : AffineAlgebraicGroup F} {T B N : ClosedSubgroup G.val}
variable {P : SplitPairOver (K := K) G T B}
variable {D : AttachedDatum P.pair} {I : Set (Root P.pair.T)} {L : RationalStandardFace D I}
variable {pair : RationalOppositePair T B N}
variable {hG : IsReductive G} {hT : IsTorus T.group} {hmax : IsGeometricallyMaximal T}
variable {A₀ : AdditiveLine F} {A : AdditiveLine K}
variable {U : RootSubgroupFamily P.pair.T} {p : Pinning A P.pair U}
variable {a : (groupBaseChange F K).obj A₀.group ≅ A.group} {ω : Gal(K/F) →* Aut D.toBased}
variable {d : InducedFaceData D (L := L) (pair := pair) (hG := hG) (hT := hT) (hmax := hmax) p a ω}

private abbrev faceInclusion (L : RationalStandardFace D I) : L.derived.group ⟶ G.val :=
  L.derived.inclusion ≫ L.limit.centralizer.inclusion

private theorem faceInclusion_split (L : RationalStandardFace D I) :
    (groupBaseChange F K).map (faceInclusion L) = (L.splitFace D).inclusion := by
  change (groupBaseChange F K).map (L.derived.inclusion ≫ L.limit.centralizer.inclusion) =
    ((groupBaseChange F K).map L.derived.inclusion ≫ L.comparison.hom) ≫ L.splitLimit.centralizer.inclusion
  rw [Functor.map_comp, Category.assoc, L.comparisonSquare]

set_option maxHeartbeats 800000 in
private theorem faceRadicalWords_in_ambient (B₀ : Bool → BorelRadical G)
    (hpos : (B₀ true).borel = B) (hneg : (B₀ false).borel = N)
    (q : FacePinnedForm d) (V : FaceRadicals d)
    (h : ∀ i j : I, ∃ σ, diagramRoot ω σ i.val = j.val) :
    orbitRadicalWords (markedFace q V h) ≤
      (oppositeRadicalWords B₀).comap (onRational (faceInclusion L)) := by
  let H := (L.rationalFace D pair hG hT hmax).group
  let e := faceInclusion L
  apply (Subgroup.closure_le _).mpr
  intro x hx
  change onRational e x ∈ oppositeRadicalWords B₀
  apply Subgroup.subset_closure
  rcases hx with ⟨z, hz⟩ | ⟨z, hz⟩
  · refine ⟨true, ?_⟩
    let Q := B₀ true
    have eQ : Q.borel = B := hpos
    cases eQ
    obtain ⟨f, hf⟩ := inducedRadicalInclusion hG hT hmax Q.isBorel pair.toPositive
      pair.positiveSquare e d.positive.toAmbient d.positive.intersection.w Q.radical Q.isRadical
      V.positive V.isPositive
    refine ⟨onRational f z, ?_⟩
    change z ≫ (V.positive.inclusion ≫ d.positive.rational.inclusion).hom.hom = x at hz
    change (z ≫ f.hom.hom) ≫ (Q.radical.inclusion ≫ Q.borel.inclusion).hom.hom = x ≫ e.hom.hom
    rw [← hz]
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun v : V.positive.group ⟶ G.val => z ≫ v.hom.hom) hf
  · refine ⟨false, ?_⟩
    let Q := B₀ false
    have eQ : Q.borel = N := hneg
    cases eQ
    obtain ⟨f, hf⟩ := inducedRadicalInclusion hG hT hmax Q.isBorel pair.toNegative
      (pair.intersection.w.symm.trans pair.positiveSquare) e d.negative.toAmbient d.negative.intersection.w
      Q.radical Q.isRadical V.negative V.isNegative
    refine ⟨onRational f z, ?_⟩
    change z ≫ (V.negative.inclusion ≫ d.negative.rational.inclusion).hom.hom = x at hz
    change (z ≫ f.hom.hom) ≫ (Q.radical.inclusion ≫ Q.borel.inclusion).hom.hom = x ≫ e.hom.hom
    rw [← hz]
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun v : V.negative.group ⟶ G.val => z ≫ v.hom.hom) hf

private theorem conjugates_ambient_coroot_point (q : FacePinnedForm d)
    (x : RationalPoints L.derived.group) (π : Equiv.Perm I) (h : FaceWordConjugates q x π)
    (R : TestAlgebra K) (i : I) (v : Rˣ) :
    letI := D.comm
    let S := L.splitFace D
    let y := splitWordSection (K := K) (L := L) x ≫ S.inclusion.hom.hom
    conjugate y (cocharacterPoint (D.datum.rootDatum.coroot i.val).toMul R v ≫ P.pair.T.inclusion.hom.hom) =
      cocharacterPoint (D.datum.rootDatum.coroot (π i).val).toMul R v⁻¹ ≫ P.pair.T.inclusion.hom.hom := by
  letI := D.comm
  let C := groupBaseChange F K
  let S := L.splitFace D
  have hs : C.map L.torusMap ≫ P.pair.T.inclusion = C.map L.torus.inclusion ≫ S.inclusion :=
    S.intersection.w
  have hi (j : I) (t : Rˣ) :
      cocharacterPoint (D.datum.rootDatum.coroot j.val).toMul R t ≫ P.pair.T.inclusion.hom.hom =
        splitFaceCorootPoint q R j t ≫ S.inclusion.hom.hom := by
    rw [← faceCoroot_ambient q j, cocharacterPoint_postcompose, Category.assoc]
    change cocharacterPoint (faceCoroot q j) R t ≫ (C.map L.torusMap ≫ P.pair.T.inclusion).hom.hom =
      (cocharacterPoint (faceCoroot q j) R t ≫ (C.map L.torus.inclusion).hom.hom) ≫ S.inclusion.hom.hom
    rw [hs, Grp.comp_hom_hom, Category.assoc]
  dsimp only
  rw [hi, hi, ← conjugate_comp]
  exact congrArg (fun z : GroupPoints S.group.val R => z ≫ S.inclusion.hom.hom) (h R i v)

private theorem negative_root_of_coroot_image
    {k : Type u} [Field k] {P : Specs.Pinning.SplitBorelPair k} (D : AttachedDatum P) :
    letI := D.comm
    ∀ (w : D.datum.rootDatum.weylGroup) (i j : Root P.T),
      w.val.coweightEquiv.symm (D.datum.rootDatum.coroot i) = -D.datum.rootDatum.coroot j →
      w.val.weightEquiv (D.datum.rootDatum.root i) = -D.datum.rootDatum.root j := by
  letI := D.comm
  intro w i j h
  let Q := D.datum.rootDatum
  let e := w.val
  have h₁ : e.coweightEquiv (Q.coroot (e.indexEquiv i)) = Q.coroot i := by
    have he := e.toHom.coroot_coweightMap_apply Q Q (e.indexEquiv i)
    change e.coweightEquiv (Q.coroot (e.indexEquiv i)) = Q.coroot (e.indexEquiv.symm (e.indexEquiv i)) at he
    simpa only [Equiv.symm_apply_apply] using he
  have h₂ : Q.coroot (e.indexEquiv i) = Q.coroot (Q.reflectionPerm j j) := by
    rw [← e.coweightEquiv.symm_apply_eq.mpr h₁.symm, h, RootPairing.coroot_reflectionPerm,
      RootPairing.coreflection_apply_self]
  rw [show e.weightEquiv (Q.root i) = Q.root (e.indexEquiv i) from e.toHom.root_weightMap_apply Q Q i,
    Q.coroot.injective h₂, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]

set_option maxHeartbeats 800000 in
private theorem negative_face_positive_roots {k : Type u} [Field k]
    {P : Specs.Pinning.SplitBorelPair k} (D : AttachedDatum P) (I : Set (Root P.T)) :
    letI := D.comm
    ∀ (c lam : Cocharacter P.T.group) (w : D.datum.rootDatum.weylGroup),
      IsBaseFor D.datum.rootDatum (evaluate D.datum c) D.base →
      HasFace D.base I lam → I ⊆ D.base.support →
      (∀ j : I, ∃ l : I, w.val.weightEquiv (D.datum.rootDatum.root j.val) = -D.datum.rootDatum.root l.val) →
      ∀ i ∈ leviRoots D.datum I, 0 < evaluate D.datum c (D.datum.rootDatum.root i) →
        evaluate D.datum c (w.val.weightEquiv (D.datum.rootDatum.root i)) < 0 := by
  classical
  letI := D.comm
  letI := D.datum.finiteRoots
  intro c l w hb hl hI hsimple i hi hip
  let P₀ := D.datum.rootDatum
  let f := evaluate D.datum c
  let g := evaluate D.datum l
  have hg (j : Root P.T) : g (P₀.root j) = pairing P.T.group j.val l :=
    (congrArg (fun x => P₀.toLinearMap x (Additive.ofMul l)) (D.datum.root_eq j)).trans
      (D.datum.pairing_eq _ _)
  have hz : g (P₀.root i) = 0 := by
    have hle : Submodule.span ℤ (P₀.root '' I) ≤ LinearMap.ker g := by
      apply Submodule.span_le.mpr
      rintro v ⟨j, hj, rfl⟩
      exact (hg j).trans (hl.1 j hj)
    exact hle hi
  obtain ⟨b, _, hbsgn, hsum⟩ := hb.integral_coordinates i
  have hpos (j : Root P.T) (hj : j ∈ D.base.support) : 0 < f (P₀.root j) :=
    ((hb.simple_iff j).mp hj).1
  have hn : ∀ j, 0 ≤ b j := by
    rcases hbsgn with h | h
    · exact h
    · exfalso
      apply (not_lt_of_ge _ hip)
      change f (P₀.root i) ≤ 0
      rw [hsum, map_sum]
      exact Finset.sum_nonpos (fun j hj => by
        rw [map_smul, zsmul_eq_mul]
        exact mul_nonpos_of_nonpos_of_nonneg (h j) (hpos j hj).le)
  have hgn (j : Root P.T) (hj : j ∈ D.base.support) : 0 ≤ g (P₀.root j) := by
    by_cases h : j ∈ I
    · exact le_of_eq ((hg j).trans (hl.1 j h)).symm
    · rw [hg]
      exact (hl.2 j ⟨hj, h⟩).le
  have hout (j : Root P.T) (hj : j ∈ D.base.support) (hjI : j ∉ I) : b j = 0 := by
    have h := Finset.single_le_sum
      (f := fun j => b j * g (P₀.root j)) (fun j hj => mul_nonneg (hn j) (hgn j hj)) hj
    have hs : (∑ j ∈ D.base.support, b j * g (P₀.root j)) = 0 := by
      calc
        _ = g (∑ j ∈ D.base.support, b j • D.datum.rootDatum.root j) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [map_smul, zsmul_eq_mul]
          rfl
        _ = 0 := (congrArg g hsum.symm).trans hz
    rw [hs] at h
    have hgp : 0 < g (P₀.root j) := by rw [hg]; exact hl.2 j ⟨hj, hjI⟩
    exact le_antisymm (le_of_not_gt (fun hb => (not_lt_of_ge h) (mul_pos hb hgp))) (hn j)
  have hone : ∃ j ∈ D.base.support, 0 < b j := by
    by_contra! h
    apply (ne_of_gt hip)
    change f (P₀.root i) = 0
    rw [hsum, map_sum, Finset.sum_eq_zero]
    intro j hj
    rw [le_antisymm (h j hj) (hn j), zero_smul, map_zero]
  let e := f.comp w.val.weightEquiv.toLinearMap
  change e (P₀.root i) < 0
  rw [hsum, map_sum]
  apply Finset.sum_neg'
  · intro j hj
    by_cases hjI : j ∈ I
    · obtain ⟨l, he⟩ := hsimple ⟨j, hjI⟩
      change f (w.val.weightEquiv (b j • P₀.root j)) ≤ 0
      rw [map_smul, he, map_smul, map_neg, zsmul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (hn j) (neg_nonpos.mpr (hpos _ (hI l.property)).le)
    · rw [hout j hj hjI, zero_smul, map_zero]
  · obtain ⟨j, hj, hp⟩ := hone
    have hjI : j ∈ I := by
      by_contra h
      rw [hout j hj h] at hp
      exact (lt_irrefl _ hp)
    obtain ⟨l, he⟩ := hsimple ⟨j, hjI⟩
    refine ⟨j, hj, ?_⟩
    change f (w.val.weightEquiv (b j • P₀.root j)) < 0
    rw [map_smul, he, map_smul, map_neg, zsmul_eq_mul]
    exact mul_neg_of_pos_of_neg hp (neg_lt_zero.mpr (hpos _ (hI l.property)))

set_option maxHeartbeats 1300000 in
private theorem ambientFaceWord (B₀ : Bool → BorelRadical G)
    (q : FacePinnedForm d) (V : FaceRadicals d)
    (tg : ∀ t : RationalPoints L.torus.group,
      onRational L.torus.inclusion t ∈ derivedOrbitWords V ∧
        onRational (L.torusMap ≫ T.inclusion) t ∈ oppositeRadicalWords B₀)
    (x : RationalPoints L.derived.group) (π : Equiv.Perm I)
    (hx₀ : x ∈ derivedOrbitWords V) (hx : onRational (faceInclusion L) x ∈ oppositeRadicalWords B₀)
    (h : FaceWordConjugates q x π) : HasOrbitWords B₀ V := by
  letI := D.comm
  let C := groupBaseChange F K
  let S := L.splitFace D
  let g := onRational (faceInclusion L) x
  let z := splitWordSection (K := K) (L := L) x
  let y := (groundPointIso K).hom ≫ extendPoint (K := K) G.val g
  have hy : y = z ≫ S.inclusion.hom.hom := by
    change (groundPointIso K).hom ≫ extendPoint (K := K) G.val (onRational (faceInclusion L) x) = _
    rw [extendPoint_natural, faceInclusion_split]
    exact (Category.assoc _ _ _).symm
  have hz : Normalizes S.torus.inclusion z := by
    letI : IsCommMonObj S.torus.group.X := d.posDatum.comm
    exact normalize_from_coroots S.torus L.splitTorus (faceCoroot q) (faceCoroot_span q) z π h
  have hcen : Centralizes (S.kernelTorus.inclusion ≫ P.pair.T.inclusion) (z ≫ S.inclusion.hom.hom) :=
    (S.centralizer _ _).mpr ⟨z ≫ S.derived.inclusion.hom.hom, Category.assoc _ _ _⟩
  have hN : Normalizes P.pair.T.inclusion y :=
    hy.symm ▸ faceNormalizer D I S L.integralImage z hz hcen
  have hn : Normalizes T.inclusion g := by
    apply normalizes_of_extended (K := K)
    exact (normalizes_precomp_iso P.pair.T (groundPointIso K)
      (extendPoint (K := K) G.val g)).mp hN
  obtain ⟨W⟩ := exists_weylIdentification P.pair D
  obtain ⟨n₀, hinc⟩ := (W.representsNormalizer _ y).mp hN
  obtain ⟨b, hb⟩ := hasConstantLabel W.image.constantGroup (n₀ ≫ W.quotient.hom.hom)
  let w := W.labelEquiv.symm b
  have hlabel : W.labelEquiv w = b := W.labelEquiv.apply_symm_apply b
  have hr : Specs.BruhatOrbitParametrization.IsRepresentative W w n₀ := by
    change n₀ ≫ W.quotient.hom.hom = W.image.constantGroup.sectionPoint (W.labelEquiv w)
    rw [hlabel, hb, show toUnit (𝟙_ (SchemeOver K)) = 𝟙 _ from Subsingleton.elim _ _, Category.id_comp]
  let l := L.scalar.hom ≫ C.map L.cocharacter
  have hl : l ≫ (W.image.conjugation (W.labelEquiv w)).hom = l := by
    apply (representative_in_limit_iff W hr l L.splitLimit).mp
    let v := z ≫ S.derived.inclusion.hom.hom ≫ L.splitLimit.sectionMap.hom.hom
    refine ⟨v, ?_⟩
    change v ≫ L.splitLimit.parabolic.inclusion.hom.hom = n₀ ≫ W.normalizer.inclusion.hom.hom
    rw [hinc, hy]
    have he := congrArg (fun f => f.hom.hom) L.splitLimit.section_in_G
    simp only [Grp.comp_hom_hom] at he
    change (z ≫ S.derived.inclusion.hom.hom ≫ L.splitLimit.sectionMap.hom.hom) ≫
        L.splitLimit.parabolic.inclusion.hom.hom =
      z ≫ S.derived.inclusion.hom.hom ≫ L.splitLimit.centralizer.inclusion.hom.hom
    simp only [Category.assoc, he]
  have hc : ∀ i : I, w.val.coweightEquiv.symm (D.datum.rootDatum.coroot i.val) =
      -D.datum.rootDatum.coroot (π i).val := by
    intro i
    change w.val.coweightEquiv.symm (Additive.ofMul (D.datum.rootDatum.coroot i.val).toMul) =
      Additive.ofMul ((D.datum.rootDatum.coroot (π i).val).toMul)⁻¹
    rw [W.cocharacterAction]
    apply congrArg Additive.ofMul
    letI : Mono P.pair.T.inclusion := (Grp.forget (SchemeOver K)).mono_of_mono_map
      (mono_over P.pair.T.inclusion.hom.hom P.pair.T.isClosedImmersion)
    apply (cancel_mono P.pair.T.inclusion).mp
    rw [Category.assoc]
    apply cocharacter_ext_units
    intro R v
    rw [cocharacterPoint_postcompose (D.datum.rootDatum.coroot i.val).toMul,
      cocharacterPoint_postcompose ((D.datum.rootDatum.coroot (π i).val).toMul)⁻¹]
    have hh := conjugationForLabel W.image hb
    have hh' : ((W.image.conjugation (W.labelEquiv w)).hom ≫ P.pair.T.inclusion).hom.hom =
        conjugate y P.pair.T.inclusion.hom.hom := by
      have hn' : toUnit P.pair.T.group.X ≫ n₀ ≫ W.normalizer.inclusion.hom.hom =
          rationalConstant y := by rw [hinc]
      rw [hlabel, hh, hn']
      rfl
    change cocharacterPoint (D.datum.rootDatum.coroot i.val).toMul R v ≫
        ((W.image.conjugation (W.labelEquiv w)).hom ≫ P.pair.T.inclusion).hom.hom =
      cocharacterPoint ((D.datum.rootDatum.coroot (π i).val).toMul)⁻¹ R v ≫ P.pair.T.inclusion.hom.hom
    rw [hh', comp_conjugate, hy]
    have hv : cocharacterPoint ((D.datum.rootDatum.coroot (π i).val).toMul)⁻¹ R v =
        cocharacterPoint (D.datum.rootDatum.coroot (π i).val).toMul R v⁻¹ := by
      change unitPoint R v ≫ ((D.datum.rootDatum.coroot (π i).val).toMul⁻¹).hom.hom = _
      simp only [Grp.Hom.hom_hom_inv, GrpObj.comp_inv]
      exact (cocharacterPoint_inv _ R v).symm
    rw [hv]
    exact conjugates_ambient_coroot_point q x π h R i v
  obtain ⟨c, hreg, _, hbase⟩ := attachedBase_regular D
  have hw := (face_stabilizes_cocharacter hreg hbase L.hasFace W w).mp hl
  have hlong := negative_face_positive_roots D I c l w hbase L.hasFace L.simple
    (fun i => ⟨π i, negative_root_of_coroot_image D w i.val (π i).val (hc i)⟩)
  let n : RationalPoints W.normalizer.group := (groundPointIso K).inv ≫ n₀
  refine ⟨tg, c, W, x, w, n, hreg, hbase, hx₀, hx, hn, hw, hlong, ?_, ?_⟩
  · change ((groundPointIso K).inv ≫ n₀) ≫ W.normalizer.inclusion.hom.hom = _
    rw [Category.assoc, hinc, show y = (groundPointIso K).hom ≫ extendPoint (K := K) G.val g from rfl,
      Iso.inv_hom_id_assoc]
  · change ((groundPointIso K).inv ≫ n₀) ≫ W.quotient.hom.hom = _
    rw [Category.assoc, hb, hlabel, ← Category.assoc, comp_toUnit] <;> rfl

set_option maxHeartbeats 900000 in
theorem rationalOrbitWords : RationalOrbitWords.{u} := by
  intro F K _ _ _ _ _ _ G T B P D pair hG hT hmax A₀ A U p a ω i L d hclass hm
  letI := D.comm
  let I := orbitRootSet D ω i
  obtain ⟨q, V, hop, hact, htrans, model⟩ := rationalOrbitRankOneModels i d hclass hm
  have hh (x y : I) : ∃ σ, diagramRoot ω σ x.val = y.val := orbitRoot_transitive i x y
  have hf : FaceWordWitness q V hh := by
    rcases model with ⟨_, ho⟩ | ⟨j, _, ha⟩
    · have hi : i.val ∈ I := by
        refine ⟨i, ⟨1, ?_⟩, rfl⟩
        change ((simplePermutation D).comp ω) 1 i = i
        rw [map_one]
        rfl
      let i₀ : I := ⟨i.val, hi⟩
      exact orthogonalFaceWord q V hh hm i₀ (ho i₀)
    · exact adjacentFaceWord q V hh hm j ha
  obtain ⟨ht, x, π, hx, h⟩ := hf
  have hA := faceRadicalWords_in_ambient B rfl rfl q V hh
  have htor (s : RationalPoints L.torus.group) :
      onRational (L.torusMap ≫ T.inclusion) s ∈ oppositeRadicalWords B := by
    have e : onRational (L.torusMap ≫ T.inclusion) s =
        onRational (faceInclusion L) (onRational L.torus.inclusion s) := by
      change s ≫ (L.torusMap ≫ T.inclusion).hom.hom =
        (s ≫ L.torus.inclusion.hom.hom) ≫ (faceInclusion L).hom.hom
      rw [Category.assoc, ← Grp.comp_hom_hom]
      exact congrArg (fun f : L.torus.group ⟶ G.val => s ≫ f.hom.hom) L.intersection.w
    rw [e]
    exact hA (ht s)
  exact ⟨q, V, hop, hact, htrans, model,
    ambientFaceWord B q V (fun t => ⟨ht t, htor t⟩) x π hx (hA hx) h⟩

end AmbientOrbitWords

section CompleteOrbitLevis

open _root_.LinearAlgebraicGroups.Specs
open Specs.AbstractPairing (Root)
open Specs.QuasiSplitOrbitAmbientWords (BorelRadical)
open Specs.QuasiSplitOrbitLevis

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000 in
/-- The derived orbit Levis of the specified pair, their marked models and
the ambient rational words attached to each orbit. -/
theorem rationalOrbitLevis : RationalOrbitLevis.{u} := by
  intro F K _ _ _ _ _ _ G T B P D pair hG hT hmax habs hsc A₀ A U p a m ω hm hpin
  letI := D.comm
  let ρ : Gal(K/F) →* Equiv.Perm D.base.support := (simplePermutation D).comp ω
  letI : MulAction Gal(K/F) D.base.support := MulAction.compHom D.base.support ρ
  let O := MulAction.orbitRel.Quotient Gal(K/F) D.base.support
  let q : D.base.support → O := Quotient.mk (MulAction.orbitRel Gal(K/F) D.base.support)
  let I (o : O) : Set (Root P.pair.T) := Subtype.val '' {i | q i = o}
  obtain ⟨_, _, hclass⟩ := absoluteClassificationOfSplitPair P D habs hsc
  obtain ⟨L, b, c, hb, hl, he, hs, hd⟩ :=
    rationalOrbitLeviStructure G T B P D pair hG hT hmax habs hsc U p a m ω hm hpin
  have complete (j : D.toBased.base.support) (J : Set (Root P.pair.T))
      (L' : RationalStandardFace D J)
      (d : InducedFaceData D (L := L') (pair := pair) (hG := hG) (hT := hT) (hmax := hmax) p a ω)
      (hJ : J = orbitRootSet D ω j) (hm' : PreservesUnits L'.scalar) : HasMarkedOrbitWords B d := by
    subst J
    exact rationalOrbitWords B j d hclass hm'
  let L' (o : O) : RationalStandardFace D (I o) := L o
  dsimp only
  refine ⟨L', b, c, hb, hl, he, hs, fun o => ?_⟩
  obtain ⟨d, hD⟩ := hd o
  have hm' : PreservesUnits (L o).scalar := (hl o).symm ▸ hm
  obtain ⟨j, hj⟩ := Quotient.exists_rep o
  have hI : I o = orbitRootSet D ω j := by
    change q j = o at hj
    rw [← hj]
    exact orbitRoots_eq_fiber D ω j
  exact ⟨d, hD, complete j (I o) (L o) d hI hm'⟩

end CompleteOrbitLevis

end

end LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis
