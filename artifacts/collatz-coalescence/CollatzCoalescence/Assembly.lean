import CollatzCoalescence.Generic
import CollatzCoalescence.PotentialDefs

/-!
# Assembly of the absorption theorem from its four inputs

`absorption_tendsto` takes the superharmonicity of `V` off `F`, the escape property, and the
absorbability of every `(0, μ)` as hypotheses and concludes that the pair chain is absorbed with
probability tending to `1` from every state.  `Main.lean` supplies the hypotheses.
-/

namespace Coalescence
open Filter Topology Generic

/-- A coin word leading to the merged state has positive probability. -/
theorem pAbs_pos_of_run : ∀ (w : List Bool) (s : State), run s w = absorbed →
    0 < pAbs step absorbed w.length s
  | [], s, h => by
      have hs : s = absorbed := h
      rw [List.length_nil, pAbs_zero, if_pos hs]
      exact one_pos
  | c :: w, s, h => by
      have ih := pAbs_pos_of_run w (step s c) h
      rw [List.length_cons, pAbs_succ]
      have h0 := pAbs_nonneg step absorbed w.length (step s false)
      have h1 := pAbs_nonneg step absorbed w.length (step s true)
      cases c <;> linarith

theorem absorption_tendsto
    (hVnonneg : ∀ s, 0 ≤ V s)
    (hsuper : ∀ s, s ∉ F → (V (step s false) + V (step s true)) / 2 ≤ V s)
    (hesc : ∀ Λ : ℝ, ∃ L : ℕ, ∀ s : State, s ∉ F → V s < Λ →
      ∃ w : List Bool, w.length ≤ L ∧ (run s w ∈ F ∨ Λ ≤ V (run s w)))
    (hoff : ∀ μ : ℤ, ∃ w : List Bool, run ⟨0, μ⟩ w = absorbed) :
    ∀ s : State, Tendsto (fun k => pAbs step absorbed k s) atTop (𝓝 1) := by
  refine G4_corollary step F absorbed step_absorbed' ?_ V hVnonneg ?_ ?_
  · intro f hf
    obtain ⟨d, mu⟩ := f
    have hd : d = 0 := ((mem_F _).mp hf).1
    subst hd
    obtain ⟨w, hw⟩ := hoff mu
    exact ⟨w.length, pAbs_pos_of_run w _ hw⟩
  · intro s hs
    exact hsuper s (fun h => hs (Finset.mem_coe.mpr h))
  · intro Λ
    obtain ⟨L, hL⟩ := hesc Λ
    refine ⟨L, fun s hs hV => ?_⟩
    obtain ⟨w, hw, h⟩ := hL s (fun h => hs (Finset.mem_coe.mpr h)) hV
    exact ⟨w, hw, h.imp (fun h => Finset.mem_coe.mpr h) id⟩

#print axioms absorption_tendsto

end Coalescence
