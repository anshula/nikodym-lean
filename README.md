# Lean formalization of the finite-field Nikodym theorem

An (incomplete) formalization of the finite field Nikodym theorem in Lean.

Made based on the proof detailed in [Terence Tao’s survey of the polynomial method](https://arxiv.org/pdf/1310.6482.pdf) and with guidance from the [Lean formalization of the cap set problem](https://github.com/lean-forward/cap_set_problem).

# Theorem
```lean
theorem nikodym:
    /- Let n,d ≥ 1 be integers  -/
    ∀ n d: ℕ, 
    n ≥ 1 → d ≥ 1 →  
    /- Let α be a finite field (we also refer to it as F)-/
    /- with d < |F|. -/
    (d < fintype.card α) →  
    /- Then for any set E, where E is a subset of vector space F^n...-/
    ∀ (E: finset (fin n → α)),  
    /- ...and E has that property that -/
    (
      /- for every point x ∈ F^n-/
      ∀ (x : fin n → α), 
      /- you can find a line (that goes through x in the direction of any v ∈ F^n) -/
      ∃ (v : fin n → α),
      let L := line n x v in 
      /- that intersects E at more than d points...-/
        --(E ∩ L).card > d 
        ((line n x v).filter (λ e, e ∈ E)).card > d
    ) → 
    /- ...then the size of E must be at least d+n choose n. -/
      E.card ≥ (d+n).choose(n)
```

# Install

Install mathlib by running `leanpkg build` from the main directory.
