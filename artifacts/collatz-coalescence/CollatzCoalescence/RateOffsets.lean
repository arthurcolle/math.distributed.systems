import CollatzCoalescence.RateMain

/-!
# The rate for every offset

`offset_merge_rate`: for every `m ≠ 0` there are constants `0 < c₁`, `0 < c₂` such that for every
`k ≥ 1` the number of residues `r` mod `2^k` on whose class `T^[k] x = T^[k] (x + m)` does *not*
hold identically lies between `c₁ 2^k / √k` and `c₂ 2^k / √k`.

The upper bound is the renewal argument of `survival_upper` with the start state added to the
return set.  The lower bound steers `⟨0, m⟩` to level `2` along a fixed coin word and then uses the
random-walk comparison of `RateLower.lean`.
-/

namespace Coalescence
open Filter Topology Generic

/-- Upper bound from every start state. -/
theorem survival_upper_state (s : State) :
    ∃ B : ℝ, 0 < B ∧ ∀ k : ℕ, 1 ≤ k → 1 - pAbs step absorbed k s ≤ B / Real.sqrt k := by
  obtain ⟨K₀, c₀, hc₀, hK⟩ := exists_uniform_on_finset step absorbed step_absorbed' F F_absorbable
  let R : Set State := insert s
    (⋃ f ∈ (↑F : Set State), (fun w : List Bool => run f w) '' {w | w.length = K₀})
  have hRfin : R.Finite :=
    (Set.Finite.biUnion F.finite_toSet
      (fun f _ => (List.finite_length_eq Bool K₀).image _)).insert s
  obtain ⟨G₀, hG₀⟩ := (hRfin.image (fun x : State => 33 * (x.d : ℝ) + 6 + 3 * Gam2 x)).bddAbove
  have hG₀' : ∀ x ∈ R, 33 * (x.d : ℝ) + 6 + 3 * Gam2 x ≤ max G₀ 0 := fun x hx =>
    (hG₀ (Set.mem_image_of_mem _ hx)).trans (le_max_left _ _)
  obtain ⟨B, hB, hrate⟩ := survival_rate_of_renewal step absorbed step_absorbed' (↑F : Set State) R
    K₀ c₀ hc₀ (fun f hf => hK f (Finset.mem_coe.mp hf))
    (fun f hf w hw => Or.inl (Set.mem_insert_of_mem _ (Set.mem_biUnion hf ⟨w, hw, rfl⟩)))
    (max G₀ 0) (le_max_right _ _)
    (fun x hx t ht => (one_sub_hit_F_le x t ht).trans
      (div_le_div_of_nonneg_right (hG₀' x hx) (Real.sqrt_nonneg _)))
  exact ⟨B, hB, fun k hk => hrate s (Or.inl (Set.mem_insert _ _)) k hk⟩

namespace RateOffsets

/-- Following a prescribed coin word costs a factor `2^(-|w|)`. -/
theorem survival_along_word (j : ℕ) : ∀ (w : List Bool) (s : State),
    (1 / 2 : ℝ) ^ w.length * (1 - pAbs step absorbed j (run s w))
      ≤ 1 - pAbs step absorbed (w.length + j) s
  | [], s => by simp [run_nil]
  | c :: w, s => by
    have ih := survival_along_word j w (step s c)
    have h0 := pAbs_le_one step absorbed (w.length + j) (step s false)
    have h1 := pAbs_le_one step absorbed (w.length + j) (step s true)
    have e : (c :: w).length + j = (w.length + j) + 1 := by
      rw [List.length_cons]; omega
    rw [e, pAbs_succ, run_cons, List.length_cons, pow_succ]
    cases c <;> linarith

/-- From level one, some coin word reaches level two. -/
theorem reach_two_of_one : ∀ (n : ℕ) (μ : ℤ), ell ⟨1, μ⟩ ≤ n →
    ∃ (w : List Bool) (ν : ℤ), run ⟨1, μ⟩ w = ⟨2, ν⟩ := by
  intro n
  induction n with
  | zero =>
    intro μ h
    have hodd : μ % 2 = 1 := (ell_eq_zero_iff ⟨1, μ⟩ Nat.one_pos).mp (by omega)
    exact ⟨[false], (3 * μ + 1) / 2, step_odd_false 1 μ hodd⟩
  | succ n ih =>
    intro μ h
    rcases Int.emod_two_eq_zero_or_one μ with hμ | hμ
    · have hstep := ell_even_step 1 Nat.one_pos μ hμ
      by_cases hc : ell ⟨1, μ / 2⟩ < ell ⟨1, μ⟩
      · obtain ⟨w, ν, hw⟩ := ih (μ / 2) (by omega)
        refine ⟨false :: w, ν, ?_⟩
        rw [run_cons, step_even_false _ _ hμ, State.norm_of_pos _ _ Nat.one_pos]
        exact hw
      · obtain ⟨w, ν, hw⟩ := ih ((3 * μ + 1 - 3 ^ 1) / 2) (by omega)
        refine ⟨true :: w, ν, ?_⟩
        rw [run_cons, step_even_true _ _ hμ, State.norm_of_pos _ _ Nat.one_pos]
        exact hw
    · exact ⟨[false], (3 * μ + 1) / 2, step_odd_false 1 μ hμ⟩

/-- From `⟨0, m⟩` with `m ≠ 0`, some coin word reaches level one. -/
theorem reach_one_of_zero : ∀ (n : ℕ) (m : ℤ), m ≠ 0 → m.natAbs ≤ n →
    ∃ (w : List Bool) (ν : ℤ), run ⟨0, m⟩ w = ⟨1, ν⟩ := by
  intro n
  induction n with
  | zero =>
    intro m hm h
    omega
  | succ n ih =>
    intro m hm h
    rcases Int.emod_two_eq_zero_or_one m with hμ | hμ
    · have h1 : |m / 2| ≠ 0 := abs_ne_zero.mpr (by omega)
      have h2 : |m / 2|.natAbs ≤ n := by
        rw [Int.natAbs_abs]; omega
      obtain ⟨w, ν, hw⟩ := ih |m / 2| h1 h2
      refine ⟨false :: w, ν, ?_⟩
      rw [run_cons, step_even_false _ _ hμ, State.norm_zero]
      exact hw
    · exact ⟨[false], (3 * m + 1) / 2, step_odd_false 0 m hμ⟩

/-- From `⟨0, m⟩` with `m ≠ 0`, some coin word reaches level two. -/
theorem reach_two (m : ℤ) (hm : m ≠ 0) :
    ∃ (w : List Bool) (ν : ℤ), run ⟨0, m⟩ w = ⟨2, ν⟩ := by
  obtain ⟨w₁, ν₁, h₁⟩ := reach_one_of_zero _ m hm le_rfl
  obtain ⟨w₂, ν₂, h₂⟩ := reach_two_of_one _ ν₁ le_rfl
  exact ⟨w₁ ++ w₂, ν₂, by rw [run_append, h₁, h₂]⟩

/-- The killed walk started at `0` survives `k` steps with probability at least `1/√(2k+2)`. -/
theorem one_div_sqrt_le_r (k : ℕ) : 1 / Real.sqrt (2 * (k : ℝ) + 2) ≤ RateLower.r k 0 := by
  have h2 := RateLower.r_zero_mul_two_pow k
  have h3 := RateLower.two_pow_le_choose_mul_sqrt k
  have hs : 0 < Real.sqrt (2 * (k : ℝ) + 2) := Real.sqrt_pos.mpr (by positivity)
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have h4 : 1 ≤ RateLower.r k 0 * Real.sqrt (2 * (k : ℝ) + 2) := by
    rw [← h2] at h3
    have h3' : 1 * (2 : ℝ) ^ k ≤ RateLower.r k 0 * Real.sqrt (2 * (k : ℝ) + 2) * 2 ^ k := by
      linarith
    exact le_of_mul_le_mul_right h3' hp
  rw [div_le_iff₀ hs]
  exact h4

end RateOffsets

/-- Lower bound from every state `(0, m)`, `m ≠ 0`. -/
theorem survival_lower_offset (m : ℤ) (hm : m ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k → c / Real.sqrt k ≤ 1 - pAbs step absorbed k ⟨0, m⟩ := by
  obtain ⟨w, ν, hw⟩ := RateOffsets.reach_two m hm
  refine ⟨(1 / 2 : ℝ) ^ w.length / 2, by positivity, fun k hk => ?_⟩
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h1 : Real.sqrt (2 * (k : ℝ) + 2) ≤ 2 * Real.sqrt k := by
    rw [show (2 : ℝ) * Real.sqrt k = Real.sqrt (4 * k) by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have h2 : 0 < Real.sqrt (2 * (k : ℝ) + 2) := Real.sqrt_pos.mpr (by linarith)
  have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ w.length := by positivity
  have hr := RateOffsets.one_div_sqrt_le_r k
  have hsurv : RateLower.r k 0 ≤ 1 - pAbs step absorbed k ⟨2, ν⟩ := RateLower.r_le_survival k 0 ν
  have hword := RateOffsets.survival_along_word k w ⟨0, m⟩
  rw [hw] at hword
  have hmono := pAbs_mono step absorbed step_absorbed' (Nat.le_add_left k w.length) ⟨0, m⟩
  calc (1 / 2 : ℝ) ^ w.length / 2 / Real.sqrt k
      = (1 / 2 : ℝ) ^ w.length * (1 / (2 * Real.sqrt k)) := by ring
    _ ≤ (1 / 2 : ℝ) ^ w.length * (1 / Real.sqrt (2 * (k : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le h2 h1) hp.le
    _ ≤ (1 / 2 : ℝ) ^ w.length * (1 - pAbs step absorbed k ⟨2, ν⟩) :=
        mul_le_mul_of_nonneg_left (hr.trans hsurv) hp.le
    _ ≤ 1 - pAbs step absorbed (w.length + k) ⟨0, m⟩ := hword
    _ ≤ 1 - pAbs step absorbed k ⟨0, m⟩ := by linarith

open Classical in
/-- **The rate for every offset.** For `m ≠ 0` the number of residues `r` mod `2^k` on whose class
the orbits of `x` and `x + m` have not merged after `k` steps is of exact order `2^k / √k`. -/
theorem offset_merge_rate (m : ℤ) (hm : m ≠ 0) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ, 1 ≤ k →
      c₁ * 2 ^ k / Real.sqrt k ≤
        (((Finset.range (2 ^ k)).filter fun r : ℕ =>
          ¬ ∀ t : ℤ, T^[k] ((r : ℤ) + 2 ^ k * t) = T^[k] ((r : ℤ) + 2 ^ k * t + m)).card : ℝ) ∧
      (((Finset.range (2 ^ k)).filter fun r : ℕ =>
          ¬ ∀ t : ℤ, T^[k] ((r : ℤ) + 2 ^ k * t) = T^[k] ((r : ℤ) + 2 ^ k * t + m)).card : ℝ) ≤
        c₂ * 2 ^ k / Real.sqrt k := by
  obtain ⟨c₁, h1, hlo⟩ := survival_lower_offset m hm
  obtain ⟨c₂, h2, hhi⟩ := survival_upper_state ⟨0, m⟩
  refine ⟨c₁, c₂, h1, h2, fun k hk => ?_⟩
  have heq : merged ⟨0, m⟩ k = (Finset.range (2 ^ k)).filter fun r : ℕ =>
      ∀ t : ℤ, T^[k] ((r : ℤ) + 2 ^ k * t) = T^[k] ((r : ℤ) + 2 ^ k * t + m) := by
    unfold merged
    refine Finset.filter_congr fun r _ => ?_
    simp only [pow_zero, one_mul]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.range (2 ^ k))
    (fun r : ℕ => ∀ t : ℤ, T^[k] ((r : ℤ) + 2 ^ k * t) = T^[k] ((r : ℤ) + 2 ^ k * t + m))
  rw [← heq, Finset.card_range] at hsplit
  have hcard : (((Finset.range (2 ^ k)).filter fun r : ℕ =>
      ¬ ∀ t : ℤ, T^[k] ((r : ℤ) + 2 ^ k * t) = T^[k] ((r : ℤ) + 2 ^ k * t + m)).card : ℝ)
      = (1 - pAbs step absorbed k ⟨0, m⟩) * 2 ^ k := by
    have h3 : ((merged ⟨0, m⟩ k).card : ℝ) + (((Finset.range (2 ^ k)).filter fun r : ℕ =>
      ¬ ∀ t : ℤ, T^[k] ((r : ℤ) + 2 ^ k * t) = T^[k] ((r : ℤ) + 2 ^ k * t + m)).card : ℝ)
        = (2 : ℝ) ^ k := by exact_mod_cast hsplit
    rw [card_merged_eq] at h3
    linarith
  rw [hcard]
  have hlo' := hlo k hk
  have hhi' := hhi k hk
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  constructor
  · calc c₁ * 2 ^ k / Real.sqrt k = c₁ / Real.sqrt k * 2 ^ k := by ring
      _ ≤ (1 - pAbs step absorbed k ⟨0, m⟩) * 2 ^ k := mul_le_mul_of_nonneg_right hlo' hp.le
  · calc (1 - pAbs step absorbed k ⟨0, m⟩) * 2 ^ k ≤ c₂ / Real.sqrt k * 2 ^ k :=
        mul_le_mul_of_nonneg_right hhi' hp.le
      _ = c₂ * 2 ^ k / Real.sqrt k := by ring

#print axioms survival_upper_state
#print axioms survival_lower_offset
#print axioms offset_merge_rate

end Coalescence
