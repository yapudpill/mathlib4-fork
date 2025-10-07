/-
Copyright (c) 2025 Anthony Fernandes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Fernandes, Marc Robin
-/
import Mathlib.RingTheory.Finiteness.Exact
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Oka
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Noetherian rings and prime ideals

## Main results

- `IsNoetherianRing.of_prime`: a ring where all prime ideals are finitely generated is a noetherian
  ring

## References

- [cohen1950]: *Commutative rings with restricted minimum condition*, I. S. Cohen, Theorem 2
-/

variable {R : Type*} [CommRing R]

namespace Ideal

open Set Finset Submodule LinearMap

/-- `Ideal.FG` is an Oka predicate. -/
theorem isOka_fg : IsOka (FG (R := R)) where
  top := ⟨{1}, by simp⟩
  oka {I a} hsup hcolon := by
    let f : colon I (span {a}) →ₗ[R] I := {
      toFun := fun ⟨x, hx⟩ ↦ ⟨x * a, mem_colon_singleton.1 hx⟩
      map_add' _ _ := by simp [add_mul]
      map_smul' _ _ := by simp [mul_assoc]
    }
    let g' := Quotient.mk (span {a})
    have ha : g' a = 0 := Quotient.eq_zero_iff_mem.2 (mem_span_singleton_self a)
    have : ∀ x : I, (g'.toSemilinearMap.domRestrict I) x ∈ map g' (I ⊔ span {a}) :=
      fun ⟨_, hx⟩ ↦ mem_map_of_mem _ (mem_sup_left hx)
    let g := g'.toSemilinearMap.domRestrict I |>.codRestrict _ this
    have hquot : (map g' (I ⊔ span {a})).FG := FG.map hsup _
    have surj_g : Function.Surjective g := by
      intro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := Ideal.mem_map_iff_of_surjective _ Quotient.mk_surjective |>.1 hy
      obtain ⟨_, i, hi, rfl⟩ := mem_span_singleton_sup.1 (sup_comm I _ ▸ hx)
      use ⟨i, hi⟩
      simp [Subtype.ext_iff, g, g', ha]
    change Submodule.FG _ at hcolon hquot ⊢
    rw [← Module.Finite.iff_fg] at hcolon hquot ⊢
    refine Module.Finite.of_exact f g surj_g (fun ⟨x, hx⟩ ↦ ⟨fun hx' ↦ ?_, fun ⟨⟨y, _⟩, hy⟩ ↦ ?_⟩)
    · simp [g, Subtype.ext_iff, g', Quotient.eq_zero_iff_mem] at hx'
      obtain ⟨r, rfl⟩ := mem_span_singleton'.1 hx'
      use ⟨r, mem_colon_singleton.2 hx⟩
      simp [f]
    · simp [Subtype.ext_iff, ← hy, g, g', f, ha]

end Ideal

open Ideal

/-- If all prime ideals in a commutative ring are finitely generated, so are all other ideals. -/
theorem IsNoetherianRing.of_prime (H : ∀ I : Ideal R, I.IsPrime → I.FG) :
    IsNoetherianRing R := by
  refine ⟨isOka_fg.forall_of_forall_prime' (fun C hC₁ hC₂ I hI h ↦ ⟨sSup C, ?_, h⟩) H⟩
  obtain ⟨G, hG⟩ := h
  obtain ⟨J, J_mem_C, G_subset_J⟩ : ∃ J ∈ C, G.toSet ⊆ J := by
    refine hC₂.directedOn.exists_mem_subset_of_finset_subset_biUnion ⟨I, hI⟩ (fun _ hx ↦ ?_)
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    exact (Submodule.mem_sSup_of_directed ⟨I, hI⟩ hC₂.directedOn).1 <| hG ▸ subset_span hx
  suffices J_eq_sSup : J = sSup C from J_eq_sSup ▸ J_mem_C
  exact le_antisymm (le_sSup J_mem_C) (hG ▸ Ideal.span_le.2 G_subset_J)
