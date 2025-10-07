/-
Copyright (c) 2025 Anthony Fernandes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Fernandes
-/
import Mathlib.Algebra.Exact
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Exact sequences of finite modules

-/

open Function Module Submodule Set

variable {R₁ R₂ R₃ M₁ M₂ M₃ : Type*}
  [Semiring R₁] [AddCommGroup M₁] [Module R₁ M₁] [h₁ : Module.Finite R₁ M₁]
  [Ring R₂] [AddCommGroup M₂] [Module R₂ M₂]
  [Semiring R₃] [AddCommGroup M₃] [Module R₃ M₃] [h₃ : Module.Finite R₃ M₃]
  {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} [RingHomSurjective σ₂₃]
  (f : M₁ →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] M₃)
  (hg : Surjective g) (H : Exact f g)

include hg H in
/-- Given an exact sequence `M₁ → M₂ → M₃ → 0` where M₁ and M₃ are finite, then M₂ is also finite.
-/
theorem Module.Finite.of_exact : Module.Finite R₂ M₂ := by
  obtain ⟨G₁, span_G₁⟩ := h₁.fg_top
  obtain ⟨G₃, span_G₃⟩ := h₃.fg_top
  refine ⟨fg_def.2 ⟨f '' G₁ ∪ (surjInv hg) '' G₃, toFinite _, top_le_iff.1 fun x _ ↦ ?_⟩⟩
  obtain ⟨α, s₃, s₃_subset, _, sum_α_eq_g_x⟩ :=
    mem_span_iff_exists_finset_subset.1 (span_G₃ ▸ trivial : g x ∈ span R₃ G₃)
  replace sum_α_eq_g_x : g (∑ x ∈ s₃, surjInv σ₂₃.surjective (α x) • surjInv hg x - x) = 0 :=
    calc g (∑ x ∈ s₃, surjInv σ₂₃.surjective (α x) • surjInv hg x - x)
      _ = ∑ x ∈ s₃, g (surjInv σ₂₃.surjective (α x) • surjInv hg x) - g x := by simp
      _ = ∑ x ∈ s₃, (α x) • x - g x := by simp [map_smulₛₗ, surjInv_eq]
      _ = g x - g x := by rw [sum_α_eq_g_x]
      _ = 0 := sub_self _
  obtain ⟨y, hfy⟩ := (H _).1 sum_α_eq_g_x
  obtain ⟨β, s₁, s₁_subset, _, rfl⟩ :=
    mem_span_iff_exists_finset_subset.1 (span_G₁ ▸ trivial : y ∈ span R₁ G₁)
  replace hfy := eq_sub_of_add_eq' <| add_eq_of_eq_sub hfy
  rw [sub_eq_neg_add] at hfy
  rw [span_union, mem_sup]
  refine ⟨_, ?_, _, ?_, hfy.symm⟩
  · simp only [map_sum, LinearMap.map_smulₛₗ, neg_mem_iff]
    exact sum_smul_mem _ _ fun i₁ hi₁ ↦ mem_span_of_mem <| mem_image_of_mem _ (s₁_subset hi₁)
  · exact sum_smul_mem _ _ fun i₃ hi₃ ↦ mem_span_of_mem <| mem_image_of_mem _ (s₃_subset hi₃)
