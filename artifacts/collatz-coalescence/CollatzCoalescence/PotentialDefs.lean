import CollatzCoalescence.Defs

/-!
# The potential `V` for the pair chain (definitions only)

`V s = √d + A (1 - λ^d) + θ^d / √2 * ℓ(s) + θ^d * √(|μ| / 3^d)` and the finite target set
`F = {(0, m) : |m| ≤ M}`.  See `main.tex`, Section 4.
-/

namespace Coalescence

/-- `e d = v₂(3^d - 1)`. -/
def e (d : ℕ) : ℕ := padicValNat 2 (3 ^ d - 1)

/-- Even-phase potential: `#{1 ≤ j ≤ e d : 2^j ∣ μ} + [2^(e d) ∣ μ]` above level `0`, and `0` at level `0`. -/
def ell (s : State) : ℕ :=
  if s.d = 0 then 0
  else ((Finset.Icc 1 (e s.d)).filter (fun j => (2 : ℤ) ^ j ∣ s.mu)).card
        + (if (2 : ℤ) ^ (e s.d) ∣ s.mu then 1 else 0)

noncomputable def theta : ℝ := 19 / 20
noncomputable def lam : ℝ := 39 / 40
noncomputable def A : ℝ := 250000
def M : ℤ := 400000000

/-- `|μ| / 3^d`. -/
noncomputable def size (s : State) : ℝ := |(s.mu : ℝ)| / 3 ^ s.d

noncomputable def V (s : State) : ℝ :=
  Real.sqrt s.d + A * (1 - lam ^ s.d) + theta ^ s.d / Real.sqrt 2 * (ell s : ℝ)
    + theta ^ s.d * Real.sqrt (size s)

/-- The target set `{(0, m) : |m| ≤ M}`. -/
noncomputable def F : Finset State := (Finset.Icc (-M) M).image (fun m => (⟨0, m⟩ : State))

theorem mem_F (s : State) : s ∈ F ↔ s.d = 0 ∧ |s.mu| ≤ M := by
  constructor
  · intro h
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp h
    rw [Finset.mem_Icc] at hm
    exact ⟨rfl, abs_le.mpr hm⟩
  · rintro ⟨hd, hm⟩
    obtain ⟨d, mu⟩ := s
    simp only at hd hm
    subst hd
    exact Finset.mem_image.mpr ⟨mu, Finset.mem_Icc.mpr (abs_le.mp hm), rfl⟩

end Coalescence
