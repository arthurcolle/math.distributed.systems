import CollatzCoalescence.Main
import CollatzCoalescence.RatePotentials
import CollatzCoalescence.RateTime
import CollatzCoalescence.RateGeneric
import CollatzCoalescence.RateLower

/-!
# The rate: the unmerged proportion is of exact order `1/√k`

`neighbour_merge_rate`: there are constants `0 < c₁`, `0 < c₂` such that for every `k ≥ 1` the number
of residues `r` mod `2^k` on whose class `T^[k] x = T^[k] (x + 1)` does *not* hold identically lies
between `c₁ 2^k / √k` and `c₂ 2^k / √k`.

The lower bound is `RateLower.lean` (a simple random walk staying above level `2`).  The upper bound
combines: the maximal inequality for the potential `Gam` (the level rarely exceeds `√t` before the
chain visits `F`), the expected-time potential `QL` (the chain spends at most `O(L)` expected time
below level `L` before visiting `F`), and a renewal argument over successive visits to `F`.
-/

namespace Coalescence
open Filter Topology Generic

theorem Gam_nonneg (s : State) : 0 ≤ Gam s := by
  unfold Gam
  have := Gam2_nonneg s
  positivity

theorem d_le_Gam (s : State) : (s.d : ℝ) ≤ Gam s := by
  unfold Gam
  have := Gam2_nonneg s
  linarith

/-- Tail of the hitting time of `F`: at most `g(x) / √t`. -/
theorem one_sub_hit_F_le (x : State) (t : ℕ) (ht : 1 ≤ t) :
    1 - hit step (↑F : Set State) t x ≤ (33 * (x.d : ℝ) + 6 + 3 * Gam2 x) / Real.sqrt t := by
  have ht' : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hsq1 : 1 ≤ Real.sqrt t := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt ht'
  have hsq0 : 0 < Real.sqrt t := by linarith
  have hsqsq : Real.sqrt t * Real.sqrt t = (t : ℝ) := Real.mul_self_sqrt (by linarith)
  set L : ℕ := ⌈Real.sqrt t⌉₊ with hL
  have hLge : Real.sqrt t ≤ (L : ℝ) := Nat.le_ceil _
  have hLle : (L : ℝ) ≤ Real.sqrt t + 1 := (Nat.ceil_lt_add_one hsq0.le).le
  have hL0 : (0 : ℝ) < (L : ℝ) := by linarith
  have hL1 : 1 ≤ L := by exact_mod_cast (by linarith : (1 : ℝ) ≤ (L : ℝ))
  have hG2 := Gam2_nonneg x
  have hd0 : (0 : ℝ) ≤ (x.d : ℝ) := Nat.cast_nonneg _
  have key := one_sub_hit_le step (↑F : Set State) Gam (L : ℝ) (QL L) Gam_nonneg hL0
    (fun s hs => Gam_super s (fun h => hs (Finset.mem_coe.mpr h)))
    (QL_nonneg L)
    (fun s hs hV => QL_step L hL1 s (fun h => hs (Finset.mem_coe.mpr h))
      (by exact_mod_cast lt_of_le_of_lt (d_le_Gam s) hV))
    t x
  -- first term
  have h1 : Gam x / (L : ℝ) ≤ Gam x / Real.sqrt t :=
    div_le_div_of_nonneg_left (Gam_nonneg x) hsq0 hLge
  -- second term
  have h2 : QL L x / ((t : ℝ) + 1) ≤ (32 * (x.d : ℝ) + 6 + 2 * Gam2 x) / Real.sqrt t := by
    have hnum : QL L x ≤ Real.sqrt t * (32 * (x.d : ℝ) + 6 + 2 * Gam2 x) := by
      by_cases hd : x.d ≤ L
      · have hle := QL_le L x hd
        nlinarith [mul_nonneg hd0 (by linarith : (0 : ℝ) ≤ Real.sqrt t - 1),
          mul_nonneg hG2 (by linarith : (0 : ℝ) ≤ Real.sqrt t + 1 - (L : ℝ)),
          mul_nonneg hd0 (by linarith : (0 : ℝ) ≤ Real.sqrt t + 1 - (L : ℝ))]
      · have h0 : QL L x = 0 := by unfold QL; rw [if_neg hd]
        rw [h0]
        positivity
    have hpos : (0 : ℝ) ≤ 32 * (x.d : ℝ) + 6 + 2 * Gam2 x := by positivity
    calc QL L x / ((t : ℝ) + 1) ≤ QL L x / (t : ℝ) :=
          div_le_div_of_nonneg_left (QL_nonneg L x) (by linarith) (by linarith)
      _ ≤ Real.sqrt t * (32 * (x.d : ℝ) + 6 + 2 * Gam2 x) / (t : ℝ) :=
          div_le_div_of_nonneg_right hnum (by linarith)
      _ = (32 * (x.d : ℝ) + 6 + 2 * Gam2 x) / Real.sqrt t := by
          rw [div_eq_div_iff (by linarith) hsq0.ne']
          calc Real.sqrt t * (32 * (x.d : ℝ) + 6 + 2 * Gam2 x) * Real.sqrt t
              = (32 * (x.d : ℝ) + 6 + 2 * Gam2 x) * (Real.sqrt t * Real.sqrt t) := by ring
            _ = (32 * (x.d : ℝ) + 6 + 2 * Gam2 x) * (t : ℝ) := by rw [hsqsq]
  have hsum : Gam x / Real.sqrt t + (32 * (x.d : ℝ) + 6 + 2 * Gam2 x) / Real.sqrt t
      = (33 * (x.d : ℝ) + 6 + 3 * Gam2 x) / Real.sqrt t := by
    unfold Gam
    ring
  linarith

/-- Every state of `F` is absorbed with positive probability. -/
theorem F_absorbable : ∀ f ∈ F, ∃ k, 0 < pAbs step absorbed k f := by
  intro f hf
  obtain ⟨d, mu⟩ := f
  have hd : d = 0 := ((mem_F _).mp hf).1
  subst hd
  obtain ⟨w, hw⟩ := offset_absorbable mu
  exact ⟨w.length, pAbs_pos_of_run w _ hw⟩

/-- **Upper bound.** The probability of not being absorbed within `k` steps is `O(1/√k)`. -/
theorem survival_upper :
    ∃ B : ℝ, 0 < B ∧ ∀ k : ℕ, 1 ≤ k → 1 - pAbs step absorbed k ⟨0, 1⟩ ≤ B / Real.sqrt k := by
  obtain ⟨K₀, c₀, hc₀, hK⟩ := exists_uniform_on_finset step absorbed step_absorbed' F F_absorbable
  let R : Set State := ⋃ f ∈ (↑F : Set State), (fun w : List Bool => run f w) '' {w | w.length = K₀}
  have hRfin : R.Finite :=
    Set.Finite.biUnion F.finite_toSet (fun f _ => (List.finite_length_eq Bool K₀).image _)
  obtain ⟨G₀, hG₀⟩ := (hRfin.image (fun x : State => 33 * (x.d : ℝ) + 6 + 3 * Gam2 x)).bddAbove
  have hG₀' : ∀ x ∈ R, 33 * (x.d : ℝ) + 6 + 3 * Gam2 x ≤ max G₀ 0 := fun x hx =>
    (hG₀ (Set.mem_image_of_mem _ hx)).trans (le_max_left _ _)
  obtain ⟨B, hB, hrate⟩ := survival_rate_of_renewal step absorbed step_absorbed' (↑F : Set State) R
    K₀ c₀ hc₀ (fun f hf => hK f (Finset.mem_coe.mp hf))
    (fun f hf w hw => Or.inl (Set.mem_biUnion hf ⟨w, hw, rfl⟩))
    (max G₀ 0) (le_max_right _ _)
    (fun x hx t ht => (one_sub_hit_F_le x t ht).trans
      (div_le_div_of_nonneg_right (hG₀' x hx) (Real.sqrt_nonneg _)))
  refine ⟨B, hB, fun k hk => hrate ⟨0, 1⟩ (Or.inr ?_) k hk⟩
  rw [Finset.mem_coe, mem_F]
  exact ⟨rfl, by norm_num [M]⟩

/-- **The rate, for the chain.** -/
theorem survival_rate :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ, 1 ≤ k →
      c₁ / Real.sqrt k ≤ 1 - pAbs step absorbed k ⟨0, 1⟩ ∧
      1 - pAbs step absorbed k ⟨0, 1⟩ ≤ c₂ / Real.sqrt k := by
  obtain ⟨B, hB, hup⟩ := survival_upper
  refine ⟨1 / 8, B, by norm_num, hB, fun k hk => ⟨?_, hup k hk⟩⟩
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by linarith)
  have h1 : Real.sqrt (2 * (k : ℝ) + 2) ≤ 2 * Real.sqrt k := by
    rw [show (2 : ℝ) * Real.sqrt k = Real.sqrt (4 * k) by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have h2 : 0 < Real.sqrt (2 * (k : ℝ) + 2) := Real.sqrt_pos.mpr (by linarith)
  calc 1 / 8 / Real.sqrt k = 1 / (4 * (2 * Real.sqrt k)) := by ring
    _ ≤ 1 / (4 * Real.sqrt (2 * (k : ℝ) + 2)) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
    _ ≤ 1 - pAbs step absorbed k ⟨0, 1⟩ := survival_lower k

open Classical in
/-- **The rate.** The number of residues `r` mod `2^k` on whose class the orbits of `x` and `x + 1`
have not merged after `k` steps is between `c₁ 2^k / √k` and `c₂ 2^k / √k`. -/
theorem neighbour_merge_rate :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ, 1 ≤ k →
      c₁ * 2 ^ k / Real.sqrt k ≤
        (((Finset.range (2 ^ k)).filter fun r : ℕ =>
          ¬ ∀ t : ℤ, T^[k] ((r : ℤ) + 2 ^ k * t) = T^[k] ((r : ℤ) + 2 ^ k * t + 1)).card : ℝ) ∧
      (((Finset.range (2 ^ k)).filter fun r : ℕ =>
          ¬ ∀ t : ℤ, T^[k] ((r : ℤ) + 2 ^ k * t) = T^[k] ((r : ℤ) + 2 ^ k * t + 1)).card : ℝ) ≤
        c₂ * 2 ^ k / Real.sqrt k := by
  obtain ⟨c₁, c₂, h1, h2, h⟩ := survival_rate
  refine ⟨c₁, c₂, h1, h2, fun k hk => ?_⟩
  have heq : merged ⟨0, 1⟩ k = (Finset.range (2 ^ k)).filter fun r : ℕ =>
      ∀ t : ℤ, T^[k] ((r : ℤ) + 2 ^ k * t) = T^[k] ((r : ℤ) + 2 ^ k * t + 1) := by
    unfold merged
    refine Finset.filter_congr fun r _ => ?_
    simp only [pow_zero, one_mul]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.range (2 ^ k))
    (fun r : ℕ => ∀ t : ℤ, T^[k] ((r : ℤ) + 2 ^ k * t) = T^[k] ((r : ℤ) + 2 ^ k * t + 1))
  rw [← heq, Finset.card_range] at hsplit
  have hcard : (((Finset.range (2 ^ k)).filter fun r : ℕ =>
      ¬ ∀ t : ℤ, T^[k] ((r : ℤ) + 2 ^ k * t) = T^[k] ((r : ℤ) + 2 ^ k * t + 1)).card : ℝ)
      = (1 - pAbs step absorbed k ⟨0, 1⟩) * 2 ^ k := by
    have h3 : ((merged ⟨0, 1⟩ k).card : ℝ) + (((Finset.range (2 ^ k)).filter fun r : ℕ =>
      ¬ ∀ t : ℤ, T^[k] ((r : ℤ) + 2 ^ k * t) = T^[k] ((r : ℤ) + 2 ^ k * t + 1)).card : ℝ)
        = (2 : ℝ) ^ k := by exact_mod_cast hsplit
    rw [card_merged_eq] at h3
    linarith
  rw [hcard]
  obtain ⟨hlo, hhi⟩ := h k hk
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  constructor
  · calc c₁ * 2 ^ k / Real.sqrt k = c₁ / Real.sqrt k * 2 ^ k := by ring
      _ ≤ (1 - pAbs step absorbed k ⟨0, 1⟩) * 2 ^ k := mul_le_mul_of_nonneg_right hlo hp.le
  · calc (1 - pAbs step absorbed k ⟨0, 1⟩) * 2 ^ k ≤ c₂ / Real.sqrt k * 2 ^ k :=
        mul_le_mul_of_nonneg_right hhi hp.le
      _ = c₂ * 2 ^ k / Real.sqrt k := by ring

#print axioms survival_upper
#print axioms survival_rate
#print axioms neighbour_merge_rate

end Coalescence
