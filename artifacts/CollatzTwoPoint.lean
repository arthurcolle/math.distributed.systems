import CollatzNeighbors
namespace CollatzNeighbors
/-- The test permits arbitrary offsets, including crossing a residue boundary. -/
theorem twoPoint (k x y : Nat) :
    (∀ q : Nat, iter k (x + 2^k*q) = iter k (y + 2^k*q)) ↔
      iter k x = iter k y ∧ iter k (x + 2^k) = iter k (y + 2^k) := by
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1⟩
  · rintro ⟨h0, h1⟩ q
    have h1' : iter k x + slope k x = iter k y + slope k y := by
      simpa using ((liftOrbit k x 1).symm.trans ((by simpa using h1 :
        iter k (x + 2^k*1) = iter k (y + 2^k*1)).trans (liftOrbit k y 1)))
    have hs : slope k x = slope k y := by omega
    rw [liftOrbit, liftOrbit, h0, hs]
#print axioms twoPoint
end CollatzNeighbors
