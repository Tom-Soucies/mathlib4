/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.NormedSpace.Spectrum
import Mathlib.Topology.ContinuousFunction.FunctionalCalculus
import Mathlib.Topology.ContinuousFunction.StoneWeierstrass

/-!
# Uniqueness of the continuous functional calculus

Let `s : Set 𝕜` be compact where `𝕜` is either `ℝ` or `ℂ`. By the Stone-Weierstrass theorem, the
(star) subalgebra generated by polynomial functions on `s` is dense in `C(s, 𝕜)`. Moreover, this
star subalgebra is generated by `X : 𝕜[X]` (i.e., `ContinuousMap.restrict s (.id 𝕜)`) alone.
Consequently, any continuous star `𝕜`-algebra homomorphism with domain `C(s, 𝕜)`, is uniquely
determined by its value on `X : 𝕜[X]`.

The same is true for `𝕜 := ℝ≥0`, so long as the algebra `A` is an `ℝ`-algebra, which we establish
by upgrading a map `C((s : Set ℝ≥0), ℝ≥0) →⋆ₐ[ℝ≥0] A` to `C(((↑) '' s : Set ℝ), ℝ) →⋆ₐ[ℝ] A` in
the natural way, and then applying the uniqueness for `ℝ`-algebra homomorphisms.

This is the reason the `UniqueContinuousFunctionalCalculus` class exists in the first place, as
opposed to simply appealing directly to Stone-Weierstrass to prove `StarAlgHom.ext_continuousMap`.
-/

section UniqueUnital

section RCLike

variable {𝕜 A : Type*} [RCLike 𝕜]

theorem RCLike.uniqueContinuousFunctionalCalculus_of_compactSpace_spectrum [TopologicalSpace A]
    [T2Space A] [Ring A] [StarRing A] [Algebra 𝕜 A] [h : ∀ a : A, CompactSpace (spectrum 𝕜 a)] :
    UniqueContinuousFunctionalCalculus 𝕜 A where
  eq_of_continuous_of_map_id s hs φ ψ hφ hψ h :=
    ContinuousMap.starAlgHom_ext_map_X hφ hψ <| by
      convert h using 1
      all_goals exact congr_arg _ (by ext; simp)
  compactSpace_spectrum := h

instance RCLike.instUniqueContinuousFunctionalCalculus [NormedRing A] [StarRing A]
    [NormedAlgebra 𝕜 A] [CompleteSpace A] : UniqueContinuousFunctionalCalculus 𝕜 A :=
  RCLike.uniqueContinuousFunctionalCalculus_of_compactSpace_spectrum

end RCLike

section NNReal
open NNReal

variable {X : Type*} [TopologicalSpace X]

namespace ContinuousMap

/-- This map sends `f : C(X, ℝ)` to `Real.toNNReal ∘ f`, bundled as a continuous map `C(X, ℝ≥0)`. -/
@[pp_dot]
noncomputable def toNNReal (f : C(X, ℝ)) : C(X, ℝ≥0) := .realToNNReal |>.comp f

@[fun_prop]
lemma continuous_toNNReal : Continuous (toNNReal (X := X)) := continuous_comp _

@[simp]
lemma toNNReal_apply (f : C(X, ℝ)) (x : X) : f.toNNReal x = (f x).toNNReal := rfl

lemma toNNReal_add_add_neg_add_neg_eq (f g : C(X, ℝ)) :
    (f + g).toNNReal + (-f).toNNReal + (-g).toNNReal =
      (-(f + g)).toNNReal + f.toNNReal + g.toNNReal := by
  ext x
  simp [max_neg_zero, -neg_add_rev]
  abel

lemma toNNReal_mul_add_neg_mul_add_mul_neg_eq (f g : C(X, ℝ)) :
    (f * g).toNNReal + (-f).toNNReal * g.toNNReal + f.toNNReal * (-g).toNNReal =
      (-(f * g)).toNNReal + f.toNNReal * g.toNNReal + (-f).toNNReal * (-g).toNNReal := by
  ext x
  simp [max_neg_zero, add_mul, mul_add]
  abel

@[simp]
lemma toNNReal_algebraMap (r : ℝ≥0) :
    (algebraMap ℝ C(X, ℝ) r).toNNReal = algebraMap ℝ≥0 C(X, ℝ≥0) r := by
  ext; simp

@[simp]
lemma toNNReal_neg_algebraMap (r : ℝ≥0) : (- algebraMap ℝ C(X, ℝ) r).toNNReal = 0 := by
  ext; simp

@[simp]
lemma toNNReal_one : (1 : C(X, ℝ)).toNNReal = 1 := toNNReal_algebraMap 1

@[simp]
lemma toNNReal_neg_one : (-1 : C(X, ℝ)).toNNReal = 0 := toNNReal_neg_algebraMap 1

end ContinuousMap

variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [Algebra ℝ A] [TopologicalRing A]

namespace StarAlgHom

/-- Given a star `ℝ≥0`-algebra homomorphism `φ` from `C(X, ℝ≥0)` into an `ℝ`-algebra `A`, this is
the unique extension of `φ` from `C(X, ℝ)` to `A` as a star `ℝ`-algebra homomorphism. -/
@[simps]
noncomputable def realContinuousMapOfNNReal (φ : C(X, ℝ≥0) →⋆ₐ[ℝ≥0] A) :
    C(X, ℝ) →⋆ₐ[ℝ] A where
  toFun f := φ f.toNNReal - φ (-f).toNNReal
  map_one' := by simp
  map_zero' := by simp
  map_mul' f g := by
    have := congr(φ $(f.toNNReal_mul_add_neg_mul_add_mul_neg_eq g))
    simp only [map_add, map_mul, sub_mul, mul_sub] at this ⊢
    rw [← sub_eq_zero] at this ⊢
    convert this using 1
    abel
  map_add' f g := by
    have := congr(φ $(f.toNNReal_add_add_neg_add_neg_eq g))
    simp only [map_add] at this ⊢
    rw [← sub_eq_zero] at this ⊢
    convert this using 1
    abel
  commutes' r := by
    simp only
    obtain (hr | hr) := le_total 0 r
    · lift r to ℝ≥0 using hr
      simpa only [ContinuousMap.toNNReal_algebraMap, ContinuousMap.toNNReal_neg_algebraMap,
        map_zero, sub_zero] using AlgHomClass.commutes φ r
    · rw [← neg_neg r, ← map_neg, neg_neg (-r)]
      rw [← neg_nonneg] at hr
      lift -r to ℝ≥0 using hr with r
      simpa only [map_neg, ContinuousMap.toNNReal_neg_algebraMap, map_zero,
        ContinuousMap.toNNReal_algebraMap, zero_sub, neg_inj] using AlgHomClass.commutes φ r
  map_star' f := by simp only [star_trivial, star_sub, ← map_star]

@[fun_prop]
lemma continuous_realContinuousMapOfNNReal (φ : C(X, ℝ≥0) →⋆ₐ[ℝ≥0] A)
    (hφ : Continuous φ) : Continuous φ.realContinuousMapOfNNReal := by
  simp [realContinuousMapOfNNReal]
  fun_prop

@[simp high]
lemma realContinuousMapOfNNReal_apply_comp_toReal (φ : C(X, ℝ≥0) →⋆ₐ[ℝ≥0] A)
    (f : C(X, ℝ≥0)) :
    φ.realContinuousMapOfNNReal ((ContinuousMap.mk toReal continuous_coe).comp f) = φ f := by
  simp only [realContinuousMapOfNNReal_apply]
  convert_to φ f - φ 0 = φ f using 2
  on_goal -1 => rw [map_zero, sub_zero]
  all_goals
    congr
    ext x
    simp

lemma realContinuousMapOfNNReal_injective :
    Function.Injective (realContinuousMapOfNNReal (X := X) (A := A)) := by
  intro φ ψ h
  ext f
  simpa using congr($(h) ((ContinuousMap.mk toReal continuous_coe).comp f))

end StarAlgHom

instance NNReal.instUniqueContinuousFunctionalCalculus [UniqueContinuousFunctionalCalculus ℝ A] :
    UniqueContinuousFunctionalCalculus ℝ≥0 A where
  compactSpace_spectrum a := by
    have : CompactSpace (spectrum ℝ a) := UniqueContinuousFunctionalCalculus.compactSpace_spectrum a
    rw [← isCompact_iff_compactSpace] at *
    rw [← spectrum.preimage_algebraMap ℝ]
    exact closedEmbedding_subtype_val isClosed_nonneg |>.isCompact_preimage <| by assumption
  eq_of_continuous_of_map_id s hs φ ψ hφ hψ h := by
    let s' : Set ℝ := (↑) '' s
    let e : s ≃ₜ s' :=
      { toFun := Subtype.map (↑) (by simp [s'])
        invFun := Subtype.map Real.toNNReal (by simp [s'])
        left_inv := fun _ ↦ by ext; simp
        right_inv := fun x ↦ by
          ext
          obtain ⟨y, -, hy⟩ := x.2
          simpa using hy ▸ NNReal.coe_nonneg y
        continuous_toFun := continuous_coe.subtype_map (by simp [s'])
        continuous_invFun := continuous_real_toNNReal.subtype_map (by simp [s']) }
    have (ξ : C(s, ℝ≥0) →⋆ₐ[ℝ≥0] A) (hξ : Continuous ξ) :
        (let ξ' := ξ.realContinuousMapOfNNReal.comp <| ContinuousMap.compStarAlgHom' ℝ ℝ e;
        Continuous ξ' ∧ ξ' (.restrict s' <| .id ℝ) = ξ (.restrict s <| .id ℝ≥0)) := by
      intro ξ'
      refine ⟨ξ.continuous_realContinuousMapOfNNReal hξ |>.comp <|
        ContinuousMap.continuous_comp_left _, ?_⟩
      exact ξ.realContinuousMapOfNNReal_apply_comp_toReal (.restrict s <| .id ℝ≥0)
    obtain ⟨hφ', hφ_id⟩ := this φ hφ
    obtain ⟨hψ', hψ_id⟩ := this ψ hψ
    have hs' : CompactSpace s' := e.compactSpace
    have h' := UniqueContinuousFunctionalCalculus.eq_of_continuous_of_map_id s' _ _ hφ' hψ'
      (hφ_id ▸ hψ_id ▸ h)
    have h'' := congr($(h').comp <| ContinuousMap.compStarAlgHom' ℝ ℝ (e.symm : C(s', s)))
    have : (ContinuousMap.compStarAlgHom' ℝ ℝ (e : C(s, s'))).comp
        (ContinuousMap.compStarAlgHom' ℝ ℝ (e.symm : C(s', s))) = StarAlgHom.id _ _ := by
      ext1; simp
    simp only [StarAlgHom.comp_assoc, this, StarAlgHom.comp_id] at h''
    exact StarAlgHom.realContinuousMapOfNNReal_injective h''

end NNReal

end UniqueUnital