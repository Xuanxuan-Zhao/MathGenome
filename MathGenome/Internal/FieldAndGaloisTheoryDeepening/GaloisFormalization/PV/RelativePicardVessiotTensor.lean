import Mathlib.Algebra.CharZero.AddMonoidHom
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.IntermediateTotalRing
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotTorsor
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.ReducedOperatorTensors
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.RelativePicardVessiotTensor

namespace GaloisFormalization.PV

open scoped Matrix TensorProduct nonZeroDivisors
open Matrix (GeneralLinearGroup)
open Algebra.TensorProduct (includeLeftRingHom includeRight lift)
open LinearSystem (determinantInverse)
open MatrixGroupCoordinates (evalAt)
open private determinantInverse_map matrixGeneratedSubalgebra_le_iff
  matrixGeneratedSubalgebra_mul_le matrixUnit_over_generatedSubalgebra
  finiteType_of_matrixGenerated matrixGeneratedSubalgebra_of_fundamental fundamental_map
  from MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotTensor
open private tensorHom_commutes mapGL_injective evalAt_map evalAt_ratio_surjective
  matrixAutomorphism_spec from MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotTorsor

universe u v
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

private theorem relativeTensor_adjoin_eq_top {C F Q B : Type*}
    [CommRing C] [CommRing F] [CommRing Q] [CommRing B]
    [Algebra F Q] [Algebra F B] [Algebra C Q]
    {n : ℕ} (YQ : GL (Fin n) Q) (YB : GL (Fin n) B)
    (hB : matrixGeneratedSubalgebra F YB = ⊤) :
    letI : Algebra C (Q ⊗[F] B) := Algebra.compHom _ (algebraMap C Q)
    Algebra.adjoin Q (Specs.matrixGeneratedSubalgebra C
      (Specs.relativeTensorRatio F YQ YB) : Set (Q ⊗[F] B)) = ⊤ := by
  let P := Q ⊗[F] B
  letI : CommRing P := Algebra.TensorProduct.instCommRing
  letI : Algebra Q P := Algebra.TensorProduct.leftAlgebra
  letI : Algebra C P := Algebra.compHom P (algebraMap C Q)
  let Z := Specs.relativeTensorRatio F YQ YB
  let D := Specs.matrixGeneratedSubalgebra C Z
  let M : Subalgebra Q P := Algebra.adjoin Q (D : Set P)
  let left : Q →+* P := includeLeftRingHom
  let right : B →ₐ[F] P := includeRight
  letI : IsScalarTower F Q P := inferInstance
  have hYZ : GeneralLinearGroup.map right.toRingHom YB = GeneralLinearGroup.map left YQ * Z := by
    change _ = GeneralLinearGroup.map left YQ *
      ((GeneralLinearGroup.map left YQ)⁻¹ * GeneralLinearGroup.map right.toRingHom YB)
    rw [mul_inv_cancel_left]
  have hmem : matrixGeneratedSubalgebra Q (GeneralLinearGroup.map right.toRingHom YB) ≤ M := by
    rw [hYZ]
    apply matrixGeneratedSubalgebra_mul_le
    · refine (matrixGeneratedSubalgebra_le_iff _ _).2 ⟨fun i j => ?_, ?_⟩
      · exact M.algebraMap_mem (YQ.val i j)
      · rw [determinantInverse_map]
        exact M.algebraMap_mem (determinantInverse YQ)
    · obtain ⟨he, hd⟩ := (matrixGeneratedSubalgebra_le_iff Z D).1 le_rfl
      exact (matrixGeneratedSubalgebra_le_iff _ _).2
        ⟨fun i j => Algebra.subset_adjoin (he i j), Algebra.subset_adjoin hd⟩
  have hr : ∀ b : B, right b ∈ M := by
    let N : Subalgebra F B := (M.restrictScalars F).comap right
    have hN : matrixGeneratedSubalgebra F YB ≤ N := by
      obtain ⟨he, hd⟩ := (matrixGeneratedSubalgebra_le_iff _ _).1 hmem
      rw [determinantInverse_map] at hd
      exact (matrixGeneratedSubalgebra_le_iff _ _).2 ⟨he, hd⟩
    rw [hB] at hN
    exact fun b => hN (show b ∈ (⊤ : Subalgebra F B) from trivial)
  apply top_unique
  intro t ht
  clear ht
  change t ∈ M
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    have h := M.mul_mem (M.algebraMap_mem a) (hr b)
    change (a ⊗ₜ[F] (1 : B)) * ((1 : Q) ⊗ₜ[F] b) ∈ M at h
    simpa only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] using h
  | add a b ha hb => exact M.add_mem ha hb

private theorem matrixGeneratedSubalgebra_map_eq_top {F Q : Type*} [CommRing F]
    [CommRing Q] [Algebra F Q] {n : ℕ} {YQ : GL (Fin n) Q}
    {B : Subalgebra F Q} {YB : GL (Fin n) B}
    (hB : B = matrixGeneratedSubalgebra F YQ)
    (hY : GeneralLinearGroup.map B.val.toRingHom YB = YQ) :
    matrixGeneratedSubalgebra F YB = ⊤ := by
  let M := matrixGeneratedSubalgebra F YB
  have hM : matrixGeneratedSubalgebra F YQ ≤ M.map B.val := by
    rw [← hY]
    refine (matrixGeneratedSubalgebra_le_iff _ _).2 ⟨fun i j => ?_, ?_⟩
    · exact ⟨YB.val i j, (matrixGeneratedSubalgebra_le_iff _ _).1 le_rfl |>.1 i j, rfl⟩
    · rw [determinantInverse_map]
      exact ⟨_, (matrixGeneratedSubalgebra_le_iff _ _).1 le_rfl |>.2, rfl⟩
  rw [← hB] at hM
  apply top_unique
  intro b _
  obtain ⟨a, ha, hab⟩ := hM b.property
  exact (Subtype.ext hab : a = b) ▸ ha

private theorem relativeRange_eq_of_image_matrix {F B Q : Type*}
    [CommRing F] [CommRing B] [CommRing Q] [Algebra F B] [Algebra F Q] {n : ℕ}
    {Y : GL (Fin n) B} (hgen : matrixGeneratedSubalgebra F Y = ⊤)
    (f g : B →ₐ[F] Q) (c : GL (Fin n) F)
    (h : GeneralLinearGroup.map f.toRingHom Y =
      GeneralLinearGroup.map g.toRingHom Y * GeneralLinearGroup.map (algebraMap F Q) c) :
    f.range = g.range := by
  have le_of_image (a b : B →ₐ[F] Q) (d : GL (Fin n) F)
      (hab : GeneralLinearGroup.map a.toRingHom Y =
        GeneralLinearGroup.map b.toRingHom Y * GeneralLinearGroup.map (algebraMap F Q) d) :
      a.range ≤ b.range := by
    have hm : matrixGeneratedSubalgebra F (GeneralLinearGroup.map a.toRingHom Y) ≤ b.range := by
      rw [hab]
      apply matrixGeneratedSubalgebra_mul_le
      · refine (matrixGeneratedSubalgebra_le_iff _ _).2 ⟨fun i j => ⟨Y.val i j, rfl⟩, ?_⟩
        rw [determinantInverse_map]
        exact ⟨_, rfl⟩
      · refine (matrixGeneratedSubalgebra_le_iff _ _).2
          ⟨fun i j => b.range.algebraMap_mem (d.val i j), ?_⟩
        rw [determinantInverse_map]
        exact b.range.algebraMap_mem _
    have hs : matrixGeneratedSubalgebra F Y ≤ b.range.comap a := by
      obtain ⟨he, hd⟩ := (matrixGeneratedSubalgebra_le_iff _ _).1 hm
      rw [determinantInverse_map] at hd
      exact (matrixGeneratedSubalgebra_le_iff _ _).2 ⟨he, hd⟩
    rw [hgen] at hs
    rintro _ ⟨x, rfl⟩
    exact hs (show x ∈ (⊤ : Subalgebra F B) from trivial)
  exact le_antisymm (le_of_image f g c h)
    (le_of_image g f c⁻¹ (by rw [map_inv]; exact eq_mul_inv_iff_mul_eq.2 h.symm))

private theorem injective_of_surjective_ringEnd {B : Type*} [CommRing B]
    [IsNoetherianRing B] (f : B →+* B) (hs : Function.Surjective f) :
    Function.Injective f := by
  let ker : ℕ →o Submodule B B :=
    { toFun := fun n => RingHom.ker (f ^ n)
      monotone' := monotone_nat_of_le_succ fun n x hx => by
        change (f ^ n) x = 0 at hx
        change (f ^ (n + 1)) x = 0
        rw [pow_succ', RingHom.coe_mul, Function.comp_apply, hx, map_zero] }
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian B B) ker
  apply (RingHom.injective_iff_ker_eq_bot f).2
  apply le_antisymm ?_ bot_le
  intro x hx
  change f x = 0 at hx
  obtain ⟨y, hy⟩ := (hs.iterate n) x
  change (f ^ n) y = x at hy
  have hy' : y ∈ ker (n + 1) := by
    change (f ^ (n + 1)) y = 0
    rw [pow_succ', RingHom.coe_mul, Function.comp_apply, hy, hx]
  rw [← hn (n + 1) (Nat.le_succ n)] at hy'
  exact (Ideal.mem_bot.mpr (hy.symm.trans (RingHom.mem_ker.mp hy')))

private theorem relativeTensor_evaluations_and_closed
    {kind : OperatorKind} {C F Q B : Type*}
    [Field C] [CommRing F] [CommRing Q] [CommRing B]
    [Algebra C Q] [Algebra F Q] [Algebra F B] [Algebra B Q]
    [IsScalarTower F B Q] [IsFractionRing B Q] [IsNoetherianRing B]
    [Algebra C (Q ⊗[F] B)]
    (hscalar : ∀ c : C, algebraMap C (Q ⊗[F] B) c =
      algebraMap Q (Q ⊗[F] B) (algebraMap C Q c))
    {n : ℕ} (T : Operator kind Q) (EB : Operator kind B)
    (EP : Operator kind (Q ⊗[F] B)) (YQ : GL (Fin n) Q) (YB : GL (Fin n) B)
    (G : Subgroup (GL (Fin n) C)) (act : G →* (Q ≃+* Q))
    (hop : ∀ g : G, T.Commutes T (act g))
    (hactY : ∀ g : G, GeneralLinearGroup.map (act g).toRingHom YQ =
      YQ * GeneralLinearGroup.map (algebraMap C Q) g.val)
    (realize : ∀ τ : Q ≃+* Q, T.Commutes T τ →
      (∀ x : F, τ (algebraMap F Q x) = algebraMap F Q x) → ∃ g : G, act g = τ)
    (iC : C →+* F) (hiC : (algebraMap F Q).comp iC = algebraMap C Q)
    (hBT : EB.IsExtension T) (hsimple : T.IsSimple) (hC : T.HasConstantField (C := C))
    (hYB : GeneralLinearGroup.map (algebraMap B Q) YB = YQ)
    (hgen : matrixGeneratedSubalgebra F YB = ⊤)
    (hP : Specs.tensorLaws (R := F) T EB EP)
    (D : Subalgebra C (Q ⊗[F] B)) (ZD : GL (Fin n) D)
    (hpol : Function.Surjective (evalAt (C := C) ZD))
    (hZD : GeneralLinearGroup.map D.val.toRingHom ZD = Specs.relativeTensorRatio F YQ YB)
    (EU : Operator kind (Q ⊗[C] D)) (e : Operator.AlgEquiv Q EU EP)
    (hU : Specs.tensorLaws (R := C) T (Operator.trivial kind D) EU)
    (hD : ∀ d : D, EP.IsConstant (d : Q ⊗[F] B))
    (hmul : ∀ q : Q, ∀ d : D, e.val (q ⊗ₜ[C] d) = algebraMap Q (Q ⊗[F] B) q * (d : Q ⊗[F] B))
    (S : Set G) (action : G → Q ≃+* Q)
    (hS : S = {g : G | ∀ x : F, act g (algebraMap F Q x) = algebraMap F Q x})
    (haction : (fun g => act g) = action) :
    Specs.relativeTensorEvaluations T EB YQ YB G S action e.val ZD ∧
    ∃ H : Subgroup (GL (Fin n) C),
      (H : Set (GL (Fin n) C)) = Subtype.val '' S ∧
      (H : Set (GL (Fin n) C)) = MatrixGroupCoordinates.Specs.zeroLocus
        (RingHom.ker (evalAt (C := C) (Specs.relativeTensorRatio F YQ YB)) : Set _) ∧
      MatrixGroupCoordinates.Specs.IsAlgebraicSubgroup H := by
  subst S
  subst action
  let P := Q ⊗[F] B
  let U := Q ⊗[C] D
  let Z := Specs.relativeTensorRatio F YQ YB
  change GeneralLinearGroup.map D.val.toRingHom ZD = Z at hZD
  let S := {g : G | ∀ x : F, act g (algebraMap F Q x) = algebraMap F Q x}
  let j : B →ₐ[F] Q := IsScalarTower.toAlgHom F B Q
  let ι : C →ₐ[C] Q := Algebra.ofId C Q
  let left : Q →+* P := includeLeftRingHom
  let right : B →ₐ[F] P := includeRight
  let rightD : D →ₐ[C] U := includeRight
  letI : Nontrivial Q := hsimple.1
  have hι : Function.Injective ι := (algebraMap C Q).injective
  have hratio (m : P →ₐ[Q] Q) :
      GeneralLinearGroup.map m.toRingHom Z =
        YQ⁻¹ * GeneralLinearGroup.map (m.toRingHom.comp right.toRingHom) YB := by
    have hl : m.toRingHom.comp left = RingHom.id Q := RingHom.ext m.commutes
    change GeneralLinearGroup.map m.toRingHom
      ((GeneralLinearGroup.map left YQ)⁻¹ * GeneralLinearGroup.map right.toRingHom YB) = _
    rw [map_mul, map_inv]
    change (GeneralLinearGroup.map (m.toRingHom.comp left) YQ)⁻¹ * _ = _
    rw [hl, GeneralLinearGroup.map_id, MonoidHom.id_apply]
    rfl
  let ev (f : D →ₐ[C] C) : U →ₐ[Q] Q := Specs.evaluateConstantTensor f
  let specialize (f : D →ₐ[C] C) : P →ₐ[Q] Q := (ev f).comp e.val.symm.toAlgHom
  have hforward (f : D →ₐ[C] C) :
      ∃ g : S, (g.val : GL (Fin n) C) = GeneralLinearGroup.map f.toRingHom ZD ∧
        ∃ σ : Operator.AlgHom F EB EB,
          Function.Bijective σ.val ∧
          (∀ q b, specialize f (q ⊗ₜ[F] b) = q * j (σ.val b)) ∧
          (∀ b, act g.val (j b) = j (σ.val b)) ∧
          GeneralLinearGroup.map (j.toRingHom.comp σ.val.toRingHom) YB =
            YQ * GeneralLinearGroup.map ι.toRingHom (g.val : GL (Fin n) C) := by
    let m := specialize f
    let ψ : B →ₐ[F] Q := (m.restrictScalars F).comp right
    let γ := GeneralLinearGroup.map f.toRingHom ZD
    have hl : (ev f).toRingHom.comp includeLeftRingHom = RingHom.id Q :=
      RingHom.ext (ev f).commutes
    have hr : (ev f).toRingHom.comp rightD.toRingHom = ι.toRingHom.comp f.toRingHom :=
      RingHom.ext (fun d => one_mul (ι (f d)))
    have heval : EU.Commutes T (ev f) := by
      apply tensorHom_commutes hU (ev f).toRingHom
      · rw [hl]
        exact Operator.Commutes.id T
      · rw [hr]
        intro d
        have hc := (hC (ι (f d))).2 ⟨f d, rfl⟩
        cases kind with
        | differential =>
          change ι (f 0) = T.toDerivation (ι (f d))
          rw [map_zero, map_zero]
          exact hc.symm
        | difference => exact hc.symm
    have hm : EP.Commutes T m :=
      heval.comp (Operator.Commutes.inverse (f := e.val.toEquiv) e.property)
    have hψ : EB.Commutes T ψ := hm.comp hP.2.2
    have hspec (d : D) : m (d : P) = ι (f d) := by
      have h := hmul 1 d
      rw [map_one, one_mul] at h
      change (ev f) (e.val.symm (d : P)) = _
      rw [← h, e.val.symm_apply_apply]
      exact DFunLike.congr_fun hr d
    have hmat : GeneralLinearGroup.map ψ.toRingHom YB =
        YQ * GeneralLinearGroup.map ι.toRingHom γ := by
      have h := hratio m
      have hcomp : m.toRingHom.comp D.val.toRingHom = ι.toRingHom.comp f.toRingHom :=
        RingHom.ext hspec
      rw [← hZD] at h
      change GeneralLinearGroup.map (m.toRingHom.comp D.val.toRingHom) ZD =
        YQ⁻¹ * GeneralLinearGroup.map ψ.toRingHom YB at h
      rw [hcomp] at h
      change GeneralLinearGroup.map ψ.toRingHom YB =
        YQ * GeneralLinearGroup.map (ι.toRingHom.comp f.toRingHom) ZD
      rw [h, mul_inv_cancel_left]
    let bγ := GeneralLinearGroup.map iC γ
    have hform : GeneralLinearGroup.map ψ.toRingHom YB =
        GeneralLinearGroup.map j.toRingHom YB * GeneralLinearGroup.map (algebraMap F Q) bγ := by
      change GeneralLinearGroup.map ψ.toRingHom YB =
        GeneralLinearGroup.map (algebraMap B Q) YB *
          GeneralLinearGroup.map ((algebraMap F Q).comp iC) γ
      rw [hiC, hYB]
      exact hmat
    have hrange := relativeRange_eq_of_image_matrix hgen ψ j bγ hform
    let ej := AlgEquiv.ofInjective j hBT.2
    let ψ' : B →ₐ[F] j.range := ψ.codRestrict j.range (fun b => hrange.le ⟨b, rfl⟩)
    let σ : B →ₐ[F] B := ej.symm.toAlgHom.comp ψ'
    have hσb (b : B) : j (σ b) = ψ b :=
      congrArg Subtype.val (ej.apply_symm_apply (ψ' b))
    have hsurj : Function.Surjective σ := by
      intro b
      obtain ⟨a, ha⟩ := hrange.ge (show j b ∈ j.range from ⟨b, rfl⟩)
      exact ⟨a, hBT.2 ((hσb a).trans ha)⟩
    have hσinj := injective_of_surjective_ringEnd σ.toRingHom hsurj
    have hσop : EB.Commutes EB σ := by
      intro b
      apply hBT.2
      change j (σ (EB b)) = j (EB (σ b))
      calc
        j (σ (EB b)) = ψ (EB b) := hσb _
        _ = T (ψ b) := hψ b
        _ = T (j (σ b)) := congrArg (Operator.apply T) (hσb b).symm
        _ = j (EB (σ b)) := (hBT.1 (σ b)).symm
    let σe := AlgEquiv.ofBijective σ ⟨hσinj, hsurj⟩
    let τ : Q ≃+* Q := Operator.fractionRingEquiv σe.toRingEquiv
    have hτ (b : B) : τ (j b) = j (σ b) := Operator.fractionRingEquiv_algebraMap _ b
    have hτop : T.Commutes T τ :=
      Operator.fractionRingEquiv_commutes ⟨σe.toRingEquiv, hσop⟩ hBT.1 hBT.1
    have hfix (x : F) : τ (algebraMap F Q x) = algebraMap F Q x := by
      rw [← j.commutes x, hτ, σ.commutes]
    obtain ⟨g, hgτ⟩ := realize τ hτop hfix
    have hg : g ∈ S := fun x => by rw [hgτ]; exact hfix x
    have hτY : GeneralLinearGroup.map τ.toRingHom YQ = GeneralLinearGroup.map ψ.toRingHom YB := by
      rw [← hYB]
      change GeneralLinearGroup.map (τ.toRingHom.comp j.toRingHom) YB = _
      rw [show τ.toRingHom.comp j.toRingHom = ψ.toRingHom from
        RingHom.ext (fun b => (hτ b).trans (hσb b))]
    have hgmat : g.val = γ := by
      apply mapGL_injective ι.toRingHom hι
      apply mul_left_cancel (a := YQ)
      change YQ * GeneralLinearGroup.map (algebraMap C Q) g.val =
        YQ * GeneralLinearGroup.map ι.toRingHom γ
      rw [← hactY g, hgτ, hτY, hmat]
    refine ⟨⟨g, hg⟩, hgmat, ⟨σ, hσop⟩, ⟨hσinj, hsurj⟩, ?_, ?_, ?_⟩
    · intro q b
      change m (q ⊗ₜ[F] b) = q * j (σ b)
      rw [hσb, show q ⊗ₜ[F] b = (algebraMap Q P q) * right b from by
        change _ = (q ⊗ₜ[F] (1 : B)) * ((1 : Q) ⊗ₜ[F] b)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul], map_mul, m.commutes]
      rfl
    · intro b
      rw [hgτ]
      exact hτ b
    · rw [show j.toRingHom.comp σ.toRingHom = ψ.toRingHom from RingHom.ext hσb, hgmat]
      exact hmat
  let forward (f : D →ₐ[C] C) : S := (hforward f).choose
  have hforwardMat (f : D →ₐ[C] C) :
      ((forward f).val : GL (Fin n) C) = GeneralLinearGroup.map f.toRingHom ZD :=
    (hforward f).choose_spec.1
  let pol := evalAt (C := C) ZD
  have hinj : Function.Injective forward := by
    intro f f' h
    have hh := congrArg (fun s : S => (s.val : GL (Fin n) C)) h
    rw [hforwardMat, hforwardMat] at hh
    have he := congrArg (evalAt (C := C)) hh
    rw [evalAt_map f, evalAt_map f'] at he
    apply AlgHom.ext
    intro d
    obtain ⟨p, rfl⟩ := hpol d
    exact DFunLike.congr_fun he p
  let M (g : S) : P →ₐ[Q] Q :=
    let a : B →ₐ[F] Q :=
      { (act g.val).toRingHom.comp j.toRingHom with
        commutes' := by
          intro x
          change act g.val (j (algebraMap F B x)) = _
          rw [j.commutes]
          exact g.property x }
    lift (AlgHom.id Q Q) a (fun _ _ => Commute.all _ _)
  have hMr (g : S) : (M g).toRingHom.comp right.toRingHom =
      (act g.val).toRingHom.comp j.toRingHom :=
    RingHom.ext (fun b => one_mul (act g.val (j b)))
  have hM (g : S) : EP.Commutes T (M g) := by
    apply tensorHom_commutes hP (M g).toRingHom
    · rw [show (M g).toRingHom.comp left = RingHom.id Q from RingHom.ext (M g).commutes]
      exact Operator.Commutes.id T
    · rw [hMr]
      exact (hop g.val).comp hBT.1
  let restrict (g : S) : D →ₐ[C] Q :=
    { (M g).toRingHom.comp D.val.toRingHom with
      commutes' := fun c => by
        change (M g) (D.val (algebraMap C D c)) = _
        rw [D.val.commutes, hscalar]
        exact (M g).commutes (algebraMap C Q c) }
  let eι := AlgEquiv.ofInjective ι hι
  let backward (g : S) : D →ₐ[C] C :=
    eι.symm.toAlgHom.comp ((restrict g).codRestrict ι.range (fun d =>
      (hC _).1 ((hM g).isConstant (hD d))))
  have hback (g : S) (d : D) : ι (backward g d) = M g (d : P) :=
    congrArg Subtype.val (eι.apply_symm_apply ((restrict g).codRestrict _ _ d))
  have hrightInv (g : S) : forward (backward g) = g := by
    apply Subtype.ext
    apply Subtype.ext
    rw [hforwardMat]
    apply mapGL_injective ι.toRingHom hι
    change GeneralLinearGroup.map (ι.toRingHom.comp (backward g).toRingHom) ZD = _
    rw [show ι.toRingHom.comp (backward g).toRingHom = (M g).toRingHom.comp D.val.toRingHom
      from RingHom.ext (hback g), GeneralLinearGroup.map_comp, MonoidHom.comp_apply, hZD,
      hratio, hMr]
    change YQ⁻¹ * GeneralLinearGroup.map (act g.val).toRingHom
      (GeneralLinearGroup.map (algebraMap B Q) YB) =
        GeneralLinearGroup.map (algebraMap C Q) g.val.val
    rw [hYB, hactY, inv_mul_cancel_left]
  let points : (D →ₐ[C] C) ≃ S :=
    ⟨forward, backward, fun f => hinj (hrightInv (forward f)), hrightInv⟩
  refine ⟨⟨points, hforwardMat, fun f => ?_⟩, ?_⟩
  · obtain ⟨σ, hb, he, ha, hy⟩ := (hforward f).choose_spec.2
    exact ⟨σ, hb, hop (forward f).val, he, ha, hy⟩
  · let J : Subgroup G :=
      { carrier := S
        one_mem' := by
          intro x
          change act 1 (algebraMap F Q x) = _
          rw [map_one]
          rfl
        mul_mem' := by
          intro g h hg hh x
          change act (g * h) (algebraMap F Q x) = _
          rw [map_mul]
          change act g (act h (algebraMap F Q x)) = _
          rw [hh x, hg x]
        inv_mem' := by
          intro g hg x
          change act g⁻¹ (algebraMap F Q x) = _
          rw [map_inv]
          change (act g).symm (algebraMap F Q x) = _
          apply (act g).injective
          rw [RingEquiv.apply_symm_apply]
          exact (hg x).symm }
    let H := J.map G.subtype
    have hI : RingHom.ker (evalAt (C := C) Z) = RingHom.ker pol := by
      ext p
      change evalAt (C := C) Z p = 0 ↔ pol p = 0
      rw [← hZD, evalAt_map, AlgHom.comp_apply]
      exact map_eq_zero_iff D.val Subtype.val_injective
    have hz : (H : Set (GL (Fin n) C)) =
        MatrixGroupCoordinates.Specs.zeroLocus (RingHom.ker pol : Set _) := by
      ext γ
      constructor
      · rintro ⟨g, hg, rfl⟩ p hp
        let f := points.symm ⟨g, hg⟩
        have h := hforwardMat f
        change ((points f).val : GL (Fin n) C) = _ at h
        rw [points.apply_symm_apply] at h
        change evalAt (C := C) g.val p = 0
        rw [h, evalAt_map, AlgHom.comp_apply]
        exact (congrArg f (RingHom.mem_ker.mp hp)).trans (map_zero f)
      · intro h
        let f := pol.liftOfSurjective hpol (evalAt γ) (show RingHom.ker pol ≤ _ from h)
        have hg : ((forward f).val : GL (Fin n) C) = γ := by
          apply Units.ext
          apply Matrix.ext
          intro a b
          have hm := congrArg (evalAt (C := C)) (hforwardMat f)
          rw [evalAt_map f] at hm
          have hh := DFunLike.congr_fun hm (MvPolynomial.X (Sum.inl (a, b)))
          rw [MatrixGroupCoordinates.evalAt_entry, AlgHom.comp_apply,
            AlgHom.liftOfSurjective_apply, MatrixGroupCoordinates.evalAt_entry] at hh
          exact hh
        exact ⟨(forward f).val, (forward f).property, hg⟩
    exact ⟨H, rfl, by rwa [hI], (MatrixGroupCoordinates.isClosed_iff_zeroLocus _).2 ⟨_, hz⟩⟩

private theorem ringHom_product_to_field {ι : Type*} [Finite ι]
    (L : ι → Type*) [∀ i, Field (L i)] {M : Type*} [Field M]
    (f : (∀ i, L i) →+* M) :
    ∃ i, ∃ g : L i →+* M, f = g.comp (Pi.evalRingHom L i) := by
  classical
  letI := Fintype.ofFinite ι
  have hex : ∃ i, f (Pi.single i 1) ≠ 0 := by
    by_contra! hz
    have h := congrArg f (Finset.univ_sum_single (1 : ∀ i, L i))
    simp only [Pi.one_apply, map_sum, map_one] at h
    exact zero_ne_one ((Finset.sum_eq_zero (fun i _ => hz i)).symm.trans h)
  obtain ⟨i, hi⟩ := hex
  have he : f (Pi.single i 1) = 1 := by
    have h : IsIdempotentElem (f (Pi.single i 1)) := by
      simp [IsIdempotentElem, ← map_mul, ← Pi.single_mul]
    exact (IsIdempotentElem.iff_eq_zero_or_one.mp h).resolve_left hi
  let g : L i →+* M :=
    { toFun := fun x => f (Pi.single i x)
      map_zero' := by simp
      map_one' := he
      map_add' := fun x y => by simp [Pi.single_add]
      map_mul' := fun x y => by simp [Pi.single_mul] }
  refine ⟨i, g, RingHom.ext fun x => ?_⟩
  change f x = f (Pi.single i (x i))
  rw [← one_mul (x i), Pi.single_mul_left, map_mul, he, one_mul]

private theorem reducedTensor_of_field_products
    {K F Q B : Type*} [Field K] [CharZero K] [CommRing F] [Algebra K F]
    [CommRing Q] [CommRing B] [Algebra F Q] [Algebra F B]
    [Algebra.FiniteType F B] [IsReduced B]
    {ι κ : Type*} [Finite ι] [Finite κ]
    (L : ι → Type*) (M : κ → Type*) [∀ i, Field (L i)] [∀ j, Field (M j)]
    (eF : F ≃+* (∀ i, L i)) (eQ : Q ≃+* (∀ j, M j)) :
    IsReduced (Q ⊗[F] B) := by
  let F' := ∀ i, L i
  letI : Algebra F F' := eF.toRingHom.toAlgebra
  letI : Algebra F' Q := Algebra.compHom Q eF.symm.toRingHom
  letI : Algebra F' B := Algebra.compHom B eF.symm.toRingHom
  letI : IsScalarTower F F' B := IsScalarTower.of_algebraMap_eq fun x =>
    (congrArg (algebraMap F B) (eF.symm_apply_apply x)).symm
  letI : Algebra.FiniteType F' B := Algebra.FiniteType.of_restrictScalars_finiteType F F' B
  letI (i : ι) : CharZero (L i) := by
    let f := (Pi.evalRingHom L i).comp (eF.toRingHom.comp (algebraMap K F))
    exact CharZero.of_addMonoidHom f.toAddMonoidHom f.map_one f.injective
  let jMap (j : κ) : F' →+* M j :=
    (Pi.evalRingHom M j).comp (eQ.toRingHom.comp (algebraMap F' Q))
  choose component fieldMap hfieldMap using fun j : κ => ringHom_product_to_field L (jMap j)
  letI (j : κ) : Algebra (L (component j)) (M j) := (fieldMap j).toAlgebra
  letI (j : κ) : Algebra F' (M j) := (jMap j).toAlgebra
  letI : Algebra F' (∀ j, M j) := Pi.algebra κ M
  have hcompat (a : F') (j : κ) :
      algebraMap F' (∀ j, M j) a j =
        algebraMap (L (component j)) (M j) (a (component j)) :=
    DFunLike.congr_fun (hfieldMap j) a
  letI : IsReduced ((∀ j, M j) ⊗[F'] B) :=
    reducedProductBaseChange L M component B hcompat
  let eqQ : Q ≃ₐ[F'] (∀ j, M j) :=
    AlgEquiv.ofRingEquiv (f := eQ) (fun _ => rfl)
  let e := Algebra.TensorProduct.congr eqQ (AlgEquiv.refl (R := F') (A₁ := B))
  letI : TensorProduct.CompatibleSMul F F' Q B :=
    ⟨fun x q b => TensorProduct.smul_tmul (eF.symm x) q b⟩
  letI : TensorProduct.CompatibleSMul F' F Q B := ⟨fun x q b => by
    have h := TensorProduct.smul_tmul (R := F') (eF x) q b
    change ((eF.symm (eF x) • q) ⊗ₜ[F'] b) = q ⊗ₜ[F'] (eF.symm (eF x) • b) at h
    simpa only [eF.symm_apply_apply] using h⟩
  let f := (Algebra.TensorProduct.equivOfCompatibleSMul F' F Q Q B).toRingEquiv.trans e.toRingEquiv
  exact isReduced_of_injective f f.injective

private theorem relativeTensor_isReduced
    {kind : OperatorKind} {K : Type u} {R : Type v} [Field K] [CharZero K]
    [CommRing R] [Algebra K R] [IsNoetherianRing R]
    [Algebra K (TotalQuotientRing R)]
    {E : Operator kind R} {T : Operator kind (TotalQuotientRing R)}
    (hE : E.IsSimple) (hT : E.IsAlgebra T)
    (F : Subalgebra K (TotalQuotientRing R))
    {EF : Operator kind F} (hF : Specs.intermediateFieldStructure EF)
    (B : Subalgebra F (TotalQuotientRing R)) [Algebra.FiniteType F B] :
    IsReduced (TotalQuotientRing R ⊗[F] B) := by
  let Q := TotalQuotientRing R
  cases kind with
  | differential =>
    letI : Algebra ℚ R := Algebra.compHom R (algebraMap ℚ K)
    letI : Field Q := (Operator.simpleDifferentialFractionField (K := Q) E hE).2.toField
    letI : Field F := (show IsField F from hF).toField
    letI : CharZero F := CharZero.of_addMonoidHom
      (algebraMap K F).toAddMonoidHom (algebraMap K F).map_one (algebraMap K F).injective
    letI : IsReduced B := isReduced_of_injective B.val Subtype.val_injective
    exact reducedFieldBaseChange F Q B
  | difference =>
    obtain ⟨hfin, _, _, hfield, _, _, _, eQ, _, _, _, _, _, _⟩ :=
      simpleDifferenceFractionComponents E.toRingEquiv T.toRingEquiv hE hT
    let κ := minimalPrimes R
    let M (i : κ) := TotalQuotientRing (R ⧸ i.val)
    letI : ∀ i, Field (M i) := fun i => (hfield i).toField
    letI : Finite κ := hfin
    letI : IsReduced Q := isReduced_of_injective eQ eQ.injective
    letI : IsReduced B := isReduced_of_injective B.val Subtype.val_injective
    obtain ⟨ι, L, hL, hfinite, _, eF, _, _, _, _⟩ := hF
    letI := hL
    letI := hfinite
    exact reducedTensor_of_field_products (K := K) (F := (F : Type v)) (Q := Q) (B := (B : Type v)) L M eF eQ

private theorem relativeFractionAction
    {kind : OperatorKind} {K : Type u} {R : Type v}
    [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    (δ : OperatorField kind K) (A : LinearSystem kind K n) (E : Operator kind R)
    (T : Operator kind (TotalQuotientRing R)) (Y : GL (Fin n) R)
    (hk : δ.IsBaseField) (hpv : IsPicardVessiotTotalExtension δ A E T)
    (hY : A.IsFundamental E Y) :
    let Q := TotalQuotientRing R
    letI : Algebra K Q := Algebra.compHom Q (algebraMap K R)
    letI : Algebra δ.constantSubfield Q := Algebra.compHom Q δ.constantSubfield.subtype
    let G := matrixGaloisGroup δ E Y
    let YQ := GeneralLinearGroup.map (algebraMap R Q) Y
    ∃ act : G →* (Q ≃+* Q),
      (∀ g, act g = matrixFractionAutomorphism δ E Y g) ∧
      (∀ g : G, T.Commutes T (act g)) ∧
      (∀ g : G, GeneralLinearGroup.map (act g).toRingHom YQ =
        YQ * GeneralLinearGroup.map (algebraMap δ.constantSubfield Q) g.val) ∧
      ∀ τ : Q ≃+* Q, T.Commutes T τ →
        (∀ k : K, τ (algebraMap K Q k) = algebraMap K Q k) → ∃ g : G, act g = τ := by
  let Q := TotalQuotientRing R
  let G := matrixGaloisGroup δ E Y
  letI : Algebra K Q := Algebra.compHom Q (algebraMap K R)
  letI : Algebra δ.constantSubfield Q := Algebra.compHom Q δ.constantSubfield.subtype
  let YQ := GeneralLinearGroup.map (algebraMap R Q) Y
  obtain ⟨α, hα, _⟩ := galoisTotalRingAction δ A E Y T hk hpv.1 hY hpv.2.1
  change ∀ g : G, (α g).val.toRingEquiv = matrixFractionAutomorphism δ E Y g at hα
  let act : G →* (Q ≃+* Q) :=
    { toFun := matrixFractionAutomorphism δ E Y
      map_one' := by rw [← hα, map_one]; rfl
      map_mul' := fun a b => by rw [← hα (a * b), ← hα a, ← hα b, map_mul]; rfl }
  refine ⟨act, fun _ => rfl, ?_, ?_, ?_⟩
  · intro g
    change T.Commutes T (matrixFractionAutomorphism δ E Y g)
    rw [← hα g]
    exact (α g).property
  · intro g
    have hr : (act g).toRingHom.comp (algebraMap R Q) =
        (algebraMap R Q).comp (matrixAutomorphism δ E Y g).val.toRingHom :=
      RingHom.ext (Operator.fractionRingEquiv_algebraMap _)
    change GeneralLinearGroup.map ((act g).toRingHom.comp (algebraMap R Q)) Y = _
    rw [hr, GeneralLinearGroup.map_comp, MonoidHom.comp_apply, matrixAutomorphism_spec, map_mul]
    rfl
  · intro τ hτ hfix
    let τK : operatorAutomorphisms K T := ⟨AlgEquiv.ofRingEquiv (f := τ) hfix, hτ⟩
    refine ⟨α.symm τK, ?_⟩
    change matrixFractionAutomorphism δ E Y (α.symm τK) = τ
    rw [← hα, α.apply_symm_apply]
    rfl

private theorem relativeTensor_presentation
    {kind : OperatorKind} {K C F Q B : Type*} {n : ℕ}
    [Field K] [Field C] [CommRing F] [CommRing Q] [CommRing B]
    [Algebra C Q] [Algebra F Q] [Algebra F B] [Algebra B Q]
    [IsScalarTower F B Q] [IsFractionRing B Q] [IsNoetherianRing B]
    [Algebra K (Q ⊗[F] B)]
    (δ : OperatorField kind K) (A : LinearSystem kind K n)
    (T : Operator kind Q) (EB : Operator kind B) (EP : Operator kind (Q ⊗[F] B))
    (YQ : GL (Fin n) Q) (YB : GL (Fin n) B)
    (G : Subgroup (GL (Fin n) C)) (act : G →* (Q ≃+* Q))
    (S : Set G) (action : G → Q ≃+* Q)
    (hS : S = {g : G | ∀ x : F, act g (algebraMap F Q x) = algebraMap F Q x})
    (haction : (fun g => act g) = action)
    (hop : ∀ g : G, T.Commutes T (act g))
    (hactY : ∀ g : G, GeneralLinearGroup.map (act g).toRingHom YQ =
      YQ * GeneralLinearGroup.map (algebraMap C Q) g.val)
    (realize : ∀ τ : Q ≃+* Q, T.Commutes T τ →
      (∀ x : F, τ (algebraMap F Q x) = algebraMap F Q x) → ∃ g : G, act g = τ)
    (iC : C →+* F) (hiC : (algebraMap F Q).comp iC = algebraMap C Q)
    (hBT : EB.IsExtension T) (hsimple : T.IsSimple) (hC : T.HasConstantField (C := C))
    (hYB : GeneralLinearGroup.map (algebraMap B Q) YB = YQ)
    (hgen : matrixGeneratedSubalgebra F YB = ⊤)
    (hP : Specs.tensorLaws (R := F) T EB EP)
    (hleft : Function.Injective (algebraMap Q (Q ⊗[F] B)))
    (hred : IsReduced (Q ⊗[F] B))
    (hk : δ.IsBaseField) (hδP : δ.IsExtension EP)
    (hY₁ : A.IsFundamental EP (GeneralLinearGroup.map includeLeftRingHom YQ))
    (hY₂ : A.IsFundamental EP
      (GeneralLinearGroup.map (includeRight : B →ₐ[F] Q ⊗[F] B).toRingHom YB)) :
    Specs.relativeTensorPresentation T EB EP YQ YB G S action := by
  let P := Q ⊗[F] B
  letI : CommRing P := Algebra.TensorProduct.instCommRing
  letI : Algebra Q P := Algebra.TensorProduct.leftAlgebra
  letI : Algebra C P := Algebra.compHom P (algebraMap C Q)
  letI towerC : @IsScalarTower C Q P Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    @IsScalarTower.of_algebraMap_eq C Q P _ _ _ _ _ _ (fun _ => rfl)
  let Z := Specs.relativeTensorRatio F YQ YB
  let D : Subalgebra C P := Specs.matrixGeneratedSubalgebra C Z
  let Y₁ := GeneralLinearGroup.map (includeLeftRingHom : Q →+* P) YQ
  let Y₂ := GeneralLinearGroup.map (includeRight : B →ₐ[F] P).toRingHom YB
  have hYZ : Y₂ = Y₁ * Z := by
    change Y₂ = Y₁ * (Y₁⁻¹ * Y₂)
    rw [mul_inv_cancel_left]
  obtain ⟨W, hW, _⟩ := A.fundamentalRightMultiplier δ hk EP hδP Y₁ Y₂ hY₁ hY₂
  have hZ : GeneralLinearGroup.map EP.constantSubring.subtype W = Z :=
    mul_left_cancel (hW.symm.trans hYZ)
  have hentry (a b : Fin n) : EP.IsConstant (Z.val a b) := by
    rw [← hZ]
    exact (Operator.mem_constantSubring EP _).1 (W.val a b).property
  have hdet : EP.IsConstant (determinantInverse Z) := by
    rw [← hZ, determinantInverse_map]
    exact (Operator.mem_constantSubring EP _).1 (determinantInverse W).property
  let M : Subalgebra C P :=
    { EP.constantSubring with
      algebraMap_mem' := fun c =>
        (Operator.mem_constantSubring EP _).2
          ((show T.Commutes EP (includeLeftRingHom : Q →+* P) from hP.2.1).isConstant
            ((hC _).2 ⟨c, rfl⟩)) }
  have hDM : D ≤ M := (matrixGeneratedSubalgebra_le_iff Z M).2
    ⟨fun a b => (Operator.mem_constantSubring EP _).2 (hentry a b),
      (Operator.mem_constantSubring EP _).2 hdet⟩
  have hD (d : D) : EP.IsConstant (d : P) :=
    (Operator.mem_constantSubring EP _).1 (hDM d.property)
  letI : IsReduced P := hred
  have hredD : IsReduced D := isReduced_of_injective D.val Subtype.val_injective
  have hDP : Algebra.adjoin Q (D : Set P) = ⊤ := relativeTensor_adjoin_eq_top YQ YB hgen
  obtain ⟨EU, hU, _⟩ := Operator.tensor_constant_existsUnique (R := C) (T := D) hC.isAlgebra
  obtain ⟨e, he⟩ := Operator.constantTensorMulIsEquiv D hsimple hC ⟨hP.2.1, hleft⟩ hU hD hDP
  obtain ⟨ZD, hZD⟩ := matrixUnit_over_generatedSubalgebra (C := C) Z
  have hmul (q : Q) (d : D) : e.val (q ⊗ₜ[C] d) = algebraMap Q P q * (d : P) := by
    change e.val.toAlgHom (q ⊗ₜ[C] d) = _
    rw [he]
    rfl
  have hpol : Function.Surjective (evalAt (C := C) ZD) := evalAt_ratio_surjective hZD
  have hfiniteD : Algebra.FiniteType C D := Algebra.FiniteType.of_surjective (evalAt ZD) hpol
  have hpoints := relativeTensor_evaluations_and_closed
    (fun _ => rfl) T EB EP YQ YB G act hop hactY realize iC hiC hBT hsimple hC
    hYB hgen hP D ZD hpol hZD EU e hU hD hmul S action hS haction
  exact ⟨hentry, hdet, hD, hred, hredD, hfiniteD, EU, e, ZD, hU, hmul, hZD, hpoints.1, hpoints.2⟩

set_option maxHeartbeats 2500000 in
/-- The relative tensor is the scalar extension of its constant matrix algebra,
whose points are the actual automorphisms fixing the intermediate total ring. -/
theorem relativePicardVessiotTensor : Specs.relativePicardVessiotTensor.{u, v} := by
  intro kind K R _ _ _ n δ A E T Y hk hpv hY
  dsimp only
  intro F hF
  change OperatorField kind K at δ
  change Operator kind R at E
  change Operator kind (TotalQuotientRing R) at T
  change LinearSystem kind K n at A
  change δ.IsBaseField at hk
  change IsPicardVessiotTotalExtension δ A E T at hpv
  change A.IsFundamental E Y at hY
  let Q := TotalQuotientRing R
  let C : Type u := δ.constantSubfield
  letI cField : Field C := inferInstanceAs (Field δ.constantSubfield)
  letI cAlgQ : Algebra C Q := Algebra.compHom Q δ.constantSubfield.subtype
  let YQ := GeneralLinearGroup.map (algebraMap R Q) Y
  let B := relativePicardVessiotSubalgebra F YQ
  letI : CommRing B := Subalgebra.toCommRing B
  letI : Algebra F B := B.algebra
  let P := Q ⊗[F] B
  letI : CommRing P := Algebra.TensorProduct.instCommRing
  letI : Algebra Q P := Algebra.TensorProduct.leftAlgebra
  letI : IsScalarTower F Q P := inferInstance
  letI kAlgP : Algebra K P := Algebra.compHom P (algebraMap K Q)
  letI towerK : @IsScalarTower K F P Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    @IsScalarTower.of_algebraMap_eq K F P _ _ _ _ _ _ (fun _ => rfl)
  letI : CharZero K := hk.1
  have hgen := matrixGeneratedSubalgebra_of_fundamental hk hpv.1 Y hY
  letI : Algebra.FiniteType K R := finiteType_of_matrixGenerated Y hgen
  letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  have hsimple : T.IsSimple := Operator.isSimple_fractionRing E T hpv.1.2.1 hpv.2.1
  have hC : T.HasConstantField (C := C) := by
    have h := Operator.constants_finiteType_fractionRing δ E T hk hpv.1.2.1 hpv.1.1.1 hpv.2.1
    intro x
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := h.2 ⟨x, (Operator.mem_constantSubring T x).2 hx⟩
      exact ⟨c, congrArg Subtype.val hc⟩
    · rintro ⟨c, rfl⟩
      exact (Operator.mem_constantSubring T _).1
        (((Operator.RingHom.mapConstants (D := E) (E := T) ⟨algebraMap R Q, hpv.2.1⟩).comp
          (Operator.RingHom.mapConstants (D := δ) (E := E) ⟨algebraMap K R, hpv.1.1.1⟩)) c).property
  obtain ⟨EF, EB, i, hδF, hFT, hFB, hBT, hiop, hi, _, hstructure, hfinite, hnoeth, _, _, hfrac⟩ :=
    intermediateTotalRing_structure δ A E T Y hk hpv hY F hF
  change Operator kind F at EF
  change Operator kind B at EB
  change R →+* B at i
  change Algebra.FiniteType F B at hfinite
  letI : Algebra.FiniteType F B := hfinite
  have hred : IsReduced P := relativeTensor_isReduced hpv.1.2.1 hpv.2.1 F hstructure B
  have hFT' : EF.IsAlgebra T := hFT.1
  have hFB' : EF.IsAlgebra EB := hFB.1
  let EP := Operator.tensor (R := (F : Type v)) (S := Q) (T := (B : Type v)) hFT' hFB'
  have hP := Operator.tensor_laws (R := (F : Type v)) (S := Q) (T := (B : Type v)) hFT' hFB'
  let left : Q →ₐ[F] P := Algebra.TensorProduct.includeLeft
  let right : B →ₐ[F] P := includeRight
  let j : B →ₐ[F] Q := B.val
  let mul : P →ₐ[Q] Q := lift (AlgHom.id Q Q) j (fun _ _ => Commute.all _ _)
  have hleft : Function.Injective (algebraMap Q P) :=
    (show Function.LeftInverse mul (algebraMap Q P) from mul.commutes).injective
  let YB : GL (Fin n) B := GeneralLinearGroup.map (R := R) (S := (B : Type v)) i Y
  have hYB : GeneralLinearGroup.map B.val.toRingHom YB = YQ := by
    change GeneralLinearGroup.map (B.val.toRingHom.comp i) Y = _
    rw [show B.val.toRingHom.comp i = algebraMap R Q from RingHom.ext hi]
  have hB : matrixGeneratedSubalgebra F YB = ⊤ :=
    matrixGeneratedSubalgebra_map_eq_top rfl hYB
  let rQ : R →ₐ[K] Q := { algebraMap R Q with commutes' := fun _ => rfl }
  let rB : R →ₐ[K] B := { i with commutes' := fun k => Subtype.ext (hi (algebraMap K R k)) }
  have hLop : T.Commutes EP left := hP.2.1
  have hRop : EB.Commutes EP right := hP.2.2
  have hδP : δ.IsExtension EP :=
    ⟨hLop.comp hpv.isExtension.1, hleft.comp hpv.isExtension.2⟩
  have hY₁ : A.IsFundamental EP (GeneralLinearGroup.map (includeLeftRingHom : Q →+* P) YQ) :=
    fundamental_map (left.restrictScalars K) hLop (fundamental_map rQ hpv.2.1 hY)
  have hY₂ : A.IsFundamental EP (GeneralLinearGroup.map right.toRingHom YB) :=
    fundamental_map (right.restrictScalars K) hRop (fundamental_map rB hiop hY)
  letI : IsFractionRing B Q := hfrac
  letI : IsNoetherianRing B := hnoeth
  let G := matrixGaloisGroup δ E Y
  let jKF : K →+* F := algebraMap K F
  let iC : C →+* F := jKF.comp δ.constantSubfield.subtype
  have hiC : (algebraMap F Q).comp iC = algebraMap C Q := rfl
  obtain ⟨act, hact, hop, hactY, realizeOverK⟩ := relativeFractionAction δ A E T Y hk hpv hY
  have realize (τ : Q ≃+* Q) (hτ : T.Commutes T τ)
      (hfix : ∀ x : F, τ (algebraMap F Q x) = algebraMap F Q x) : ∃ g : G, act g = τ :=
    realizeOverK τ hτ (fun k => hfix (jKF k))
  have hS : Specs.relativeStabilizer δ E Y F =
      {g : G | ∀ x : F, act g (algebraMap F Q x) = algebraMap F Q x} := by
    ext g
    change (∀ x : F, matrixFractionAutomorphism δ E Y g (x : Q) = x) ↔
      (∀ x : F, act g (x : Q) = x)
    rw [hact g]
  have hpresentation := @relativeTensor_presentation kind K C (F : Type v) Q (B : Type v) n
    _ cField _ _ _ cAlgQ _ _ _ _ _ _ kAlgP δ A T EB EP YQ YB G act
    (Specs.relativeStabilizer δ E Y F) (matrixFractionAutomorphism δ E Y) hS (funext hact)
    hop hactY realize iC hiC hBT hsimple hC hYB hB hP hleft hred hk hδP hY₁ hY₂
  exact ⟨EF, EB, EP, i, hFT, hFB, hBT, hiop, hi, hfrac, hP, hleft, hsimple, hpresentation⟩

end
end GaloisFormalization.PV
