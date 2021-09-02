
import 
field_theory.finite.polynomial
import data.nat.basic

open mv_polynomial
open polynomial

section polys

  set_option class.instance_max_depth 200

  parameters {α : Type} [field α] [fintype α] [decidable_eq α] [nonempty α]
  parameters {σ : Type*} [decidable_eq σ] 
  parameters {τ : Type*} [decidable_eq τ]

  -- The vanishing lemma (Lemma 1.1 i in Tao's exposition on the Polynomial Method)
  lemma vanishing (d : ℕ) (p : polynomial α) (hp : nat_degree p ≤ d):
    -- For any single-variable polynomials whose degree is at most d
    -- and is not the zero polynomial
    p ≠ 0 → 
    -- It has at most d roots
    p.roots.card ≤ d
      :=
  begin
    intros hp0,
    have hpd := polynomial.card_roots' hp0,
    transitivity (nat_degree p), exact hpd, exact hp,
  end

  -- The vanishing lemma rewritten (Lemma 1.1 i in Tao's exposition on the Polynomial Method)
  lemma vanishing_contrapos (d : ℕ) (p : polynomial α) (hp : nat_degree p ≤ d):
    -- For any single-variable polynomials whose degree is at most d
     -- If it has more than d roots
    p.roots.card > d → 
    -- It is the zero polynomial
    p = 0 
      :=
  begin
    contrapose, simp, apply vanishing, exact hp,
  end

  --The vanishing lemma (applied specifically to finsets)
  lemma vanishing' (d : ℕ) (p : polynomial α) (hp : nat_degree p ≤ d):
    -- If it reaches zero on more than d points of some set
    ∀ (S: finset α),
    let ZPS : multiset α := (multiset.filter (λ x, x ∈ S) p.roots) in
                                --p.roots ∩ S.val in -- we can remove duplicates from the finset, because a finset intersected with a multiset is a finset
                                -- (finset.filter (λ x, x ∈ S) p.roots.to_finset) in 
                                --finset.univ.filter (λ x, x ∈ p.roots ∧ x ∈ S) in
                                --let ZPS : finset α:= finset.univ.filter (λ x, polynomial.eval x p = 0 ∧ x ∈ S) in
      ZPS.card > d → 
      -- Then it vanishes on every point of that set
      --ZPS.card = S.card
      --ZPS = S.val
      ∀ (x : α), polynomial.eval x p = 0
      :=
  begin
    intros S ZPS hZPS,
    have hr := multiset.filter_le (λ x, x ∈ S) p.roots,
    replace hr := multiset.card_le_of_le hr,
    have hpd : p.roots.card > d := by apply lt_of_lt_of_le hZPS hr,
    -- It suffices to prove that p is the zero polynomial
    suffices : p = 0, { 
      rw this, simp,
    },
    apply vanishing_contrapos d p hp, exact hpd,
  end

-- The vanishing lemma for multivariate polynomials, which requires the degree of the poly be less than the cardinality of the field 
-- A variant of Lemma 1.2 in Tao (Schwartz-Zippel lemma).
  lemma vanishing_mv (n d : ℕ) (hn : n ≥ 1) (p : mv_polynomial (fin n) α) (hp : total_degree p ≤ d) (hd : d < fintype.card α):
    -- If a d-degree polynomial is zero on all the points of a finite field
    (∀ x, mv_polynomial.eval x p = 0 )→ 
    -- Then it is the zero polynomial
    p = 0
      :=
  begin
    intros hZero,

    --Polynomials where the max degree is < |F| means it can't eval 0 everywhere
    apply mv_polynomial.eq_zero_of_eval_eq_zero (fin n) α p _, 
    
    -- And now we want to prove that the max degree of each variable < |F|
    swap, exact hZero, clear hZero,
    have hpd := lt_of_le_of_lt hp hd, clear hp hd,
    rw mv_polynomial.mem_restrict_degree_iff_sup, intros i, 
    apply nat.le_pred_of_lt,

    -- So first we prove that the max degree of each variable <= total degree
    -- Note: mv_polynomial.degree_of n p = multiset.count n p.degrees
    have hp : mv_polynomial.degree_of i p ≤ p.total_degree, {

      -- Rewrite to an expression involving supremums and sums
      rw total_degree_eq, 
      rw degree_of, rw degrees, 
      rw multiset.count_sup,
      simp only [finsupp.count_to_multiset, finsupp.card_to_multiset],
      
      -- A positive element <= sum of positive elements
      apply finset.sup_mono_fun,
      intros b hb, 
      rw finsupp.sum_fintype, simp,
      apply finset.single_le_sum,
        intros i hi, simp, 
        simp,
      simp,

    },

    -- And then since total degree < |F|, we have that the max degree of each variable < |F|
    exact lt_of_le_of_lt hp hpd,
  end


parameters {n : ℕ} (V : subspace α (mv_polynomial (fin n) α)) (A : finset (fin n → α))

def zero_set : set (mv_polynomial (fin n) α) := {p ∈ V.carrier | ∀ a ∈ A, mv_polynomial.eval a p = 0}

def zero_set_subspace : subspace α (mv_polynomial (fin n) α) :=
{ carrier := zero_set,
  zero_mem' := ⟨submodule.zero_mem _, by simp⟩,
  add_mem' := λ _ _ hx hy, ⟨submodule.add_mem _ hx.1 hy.1, λ _ hp, by simp [hx.2 _ hp, hy.2 _ hp]⟩,
  smul_mem' := λ _ _ hp, ⟨submodule.smul_mem _ _ hp.1, λ _ hx, by simp [hp.2 _ hx]⟩ }


  -- The interpolation lemma (Lemma 1.1(ii) in Tao's exposition on the Polynomial Method)
  lemma interpolation':
    /- Let n,d ≥ 1 be integers  -/
    ∀ n d: ℕ, n ≥ 1 → d ≥ 1 → 
    /- Then for any set E, where E is a subset of vector space F...-/
    ∀ (E: finset α),
    /- ...such that the size of E is at least d+n choose n... -/
    E.card < d → 
    /- ...there exists a nonzero polynomial p of degree at most d ... -/
    ∃ p : polynomial α, nat_degree (p) ≤ d ∧ p ≠ 0 ∧
    /- ...such that the poly evaluates to zero on all points of E. -/
    /- That is, filtering the set by where the polynomial is zero and E is the same as just filtering by E-/
    --let ZP := finset.univ.filter (λ x, mv_polynomial.eval x p = 0) in E ⊆ ZP
    --∀ e ∈ E , mv_polynomial.eval e p = 0
    finset.filter (λ (a : α), p.eval a = 0 ∧ a ∈ E) = finset.filter (λ (a : α), a ∈ E) 
     :=

  begin
    intros n d hn hd E hE,
    -- The vector space of d-degree polys has d+1 dimensions
    --have vs := 
    -- The vector space of functions that take you from E to F has d dim
    --      Since you can write a function that takes in d variables as a d-dim tuple
    -- And so the function that takes you from one vector space to the next has a nontrivial kernel
    -- So the polynomial exists in that nontrivial kernel (a nontrivial d-dim function that takes you from E to all 0s).

    -- probably can use Lemma 9.2. or lemma_9_2_pre in section_9
    -- lemma lemma_9_2_pre : (vector_space.dim α zero_set_subspace) + A.card ≥ (vector_space.dim α V) :=

    sorry,
  end

  -- The interpolation lemma (Lemma 1.4 in Tao's exposition on the Polynomial Method)
  lemma interpolation:
    /- Let n,d ≥ 1 be integers  -/
    ∀ n d: ℕ, n ≥ 1 → d ≥ 1 → 
    /- Then for any set E, where E is a subset of vector space F^n...-/
    ∀ (E: finset (fin n → α)),
    /- ...such that the size of E is at least d+n choose n... -/
    E.card < (d+n).choose(n) → 
    /- ...there exists a nonzero polynomial p of degree at most d ... -/
    ∃ p : mv_polynomial (fin n) α, total_degree (p) ≤ d ∧ p ≠ 0 ∧
    /- ...such that the poly evaluates to zero on all points of E. -/
    /- That is, filtering the set by where the polynomial is zero and E is the same as just filtering by E-/
    --let ZP := finset.univ.filter (λ x, mv_polynomial.eval x p = 0) in E ⊆ ZP
    --∀ e ∈ E , mv_polynomial.eval e p = 0
    finset.filter (λ (a : fin n → α), ⇑(eval a) p = 0 ∧ a ∈ E) = finset.filter (λ (a : fin n → α), a ∈ E) 
     :=

  begin
    intros n d hn hd E hE,
    sorry,
  end
  
  -- def fin_eq_unit: (fin 1) ≃ unit :=  -- "unit" means "punit.{0}"
  -- {
  --   to_fun := (λ x, punit.star),-- or,  begin intro f, apply punit.star, end, 
  --   inv_fun := λ u: unit, {
  --       val := 0,
  --       is_lt := nat.zero_lt_succ 0, -- proof that 0 < 1
  --     },
  --   left_inv := begin --a proof that  inv_fun (to_fun x) = x
  --       intro x, simp, cases x, cases x_is_lt,
  --         refl,
  --         exfalso, apply nat.not_succ_le_zero x_val, exact x_is_lt_a,
  --     end,
  --   right_inv := begin  --a proof that  to_fun (inv_fun x) = x
  --       intro u, cases u, simp,
  --     end
  -- }

  -- def transform: mv_polynomial (fin 1) α → polynomial α :=
  --   begin
      
  --     intro p,
  --     have eq := punit_alg_equiv α, have eq_imp := eq.to_fun, apply eq_imp,
  --     have eq2 := rename_equiv α fin_eq_unit, have eq2_imp := eq2.to_fun, apply eq2_imp, 
  --     exact p,
  --   end 


    -- A line in a finite field passes through the point "u" and extends in direction "v"
  def line  (n: ℕ)
    (u : fin n → α)  (v : fin n → α)
    : finset (fin n → α) := 
    finset.univ.filter (λ k, (∃ t: α, k = u + t•v ))


  -- The rigidity lemma (Lemma 1.6 in Tao's exposition on the Polynomial Method)
  lemma rigidity:
    /- Let α be a finite field (call it F).-/
    /- Let n,d ≥ 1 be integers  -/
    ∀ n d: ℕ, 
    n ≥ 1 → d ≥ 1 →  
    /- For all polynomials p of degree at most d ... -/
    ∀ p : mv_polynomial (fin n) α, total_degree (p) ≤ d  → 
    /- And for all lines in the field ... -/
    ∀ (u v : fin n → α),
    let L := line n u v in 
    /- If the polynomial is zero along more than d points of the line -/
    let ZPL : finset (fin n → α):= (line n u v).filter (λ x, mv_polynomial.eval x p = 0) in
      (ZPL.card > d) →  
    /- Then it is zero along the entire line -/
      --(ZPL.card = L.card) 
      ∀ x ∈ line n u v, mv_polynomial.eval x p = 0
      :=
  begin
    intros n d hn hd p hp u v L ZPL hZPL x hxL, 
                                                  -- u_i + X_0^1 * v_i    (and note we refer to "X_0" as "t")
    let q : (fin n) →  mv_polynomial (fin 1) α := (λi, (mv_polynomial.C (u i)) + (monomial (finsupp.single 0 1) (v i))),
  
    
    -- would probably use mv_polynomial.map_mv_polynomial_eq_eval₂

    -- deterministic timeout!
    have f := comp p q,
    
    --have f := (λ t : α, comp p q),
    -- have h := rename g p,
    -- have j := transform h,

    -- Show that the one-dimensional polynomial j(t) vanishes on the set of all t
    -- have T : finset α := finset.univ.filter (λ x, true), -- finset.univ.filter (λ x, x ∈ L), --
    -- have h0 := vanishing d j hj T,

    -- Which means the set of all ZPL is also all zero.

    sorry

  -- have f := (λ t : ℕ, p.eval (u + t•v)),
    -- have g : polynomial α := finsupp.mk _ f _, 

    -- have f := (λ t : α, p.eval (u + t•v)),
    -- have g : polynomial α := finsupp.mk _ f _, 

    -- have f : polynomial α := ↑(λ t : α, p.eval (u + t•v)),
    -- have f : polynomial α := ↑(λ t : α, p.eval (u) + t•p.eval(v)),

    --apply vanishing d p hp L, -- Invoke the vanishing lemma to show it suffices to prove that |ZPL| > d
    --exact hZPL,-- Use our assumption that |ZPL| > d
  end


-- The finite field nikodym theorem (the contradictory statement that implies false)
theorem nikodym_contra:
    /- Let α be a finite field (call it F).-/
    /- Let n,d ≥ 1 be integers  -/
    ∀ n d: ℕ, 
    n ≥ 1 → d ≥ 1 →  
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
      --let L := line n x v in 
      /- that intersects E at more than d points...-/
        --(E ∩ line n x v).card > d 
        ((line n x v).filter (λ e, e ∈ E)).card > d
    ) → 
    /- ...then the size of E must be at least d+n choose n. -/
      E.card < (d+n).choose(n) → false :=
begin
  intros n d hn hd hd2 E hl hE,
  
  -- We know by interpolation that there exists a nonzero degree d poly that is 0 on all of E
  have hp := interpolation n d hn hd E hE,
  rcases hp with ⟨p, hpd, hp0, hpE⟩,

  -- Make the contradiction to prove that p=0
  apply hp0,

  -- To prove p=0, it suffices to prove that it evaluates to 0 everywhere
  suffices : ∀ x : fin n → α, mv_polynomial.eval x p = 0, {
    exact vanishing_mv n d hn p hpd hd2 this,
  },

  intros x,

  -- Show that for every point x, there is a line that goes through x that intersects E (which is in the zero set) at more than d places...
  specialize hl x, cases hl with v hl,  

  -- And also use rigidity to show that if we can prove the line is 0 at more than d places, then it is zero everywhere
  have hr := rigidity n d hn hd, specialize hr p hpd x v, apply hr,
    
  -- Proving the line is 0 at more than d places...
  {
    -- to prove |ZP ∩ line | > d, it suffices to prove |E ∩ ZP ∩ line  | > d
    have hzp := finset.card_filter_le  (finset.filter (λ (x : fin n → α), ⇑(eval x) p = 0) (line n x v)) (λ x, x ∈ E),
    apply gt_of_ge_of_gt hzp,
    -- show |E ∩ ZP ∩ line| is the same as |E ∩ line|
    rw finset.filter_filter,
    rw hpE,
    -- then use hl which says |E ∩ line| > d
    apply hl,
  },

  -- Proving every x is on the line
  {rw line, simp},
end


-- The finite field nikodym theorem (proof by contradiction)
theorem nikodym:
    /- Let α be a finite field (call it F).-/
    /- Let n,d ≥ 1 be integers  -/
    ∀ n d: ℕ, 
    n ≥ 1 → d ≥ 1 →  
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
      E.card ≥ (d+n).choose(n) :=
begin
  intros  n d hn hd hd2 E hl,
  -- To prove P, we prove ¬ P → false (which is the same as ¬¬ P)
  -- That is, to prove hE, we prove ¬ hE → false
  have nhEimpfalse: ( (E.card < (d+n).choose(n)) → false) := nikodym_contra n d hn hd hd2 E hl,
  -- Then we bring our current goal hE into the hypothesis as ¬hE
  by_contra nhE,
  -- Then we make it clear that nhE and the hypothesis of nhE → false are the same
  simp at nhE nhEimpfalse,
  -- Then since nhE -> false, and nhE, we have a contradiction
  contradiction,
end

end polys