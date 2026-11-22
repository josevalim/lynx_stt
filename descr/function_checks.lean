namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! What the function checks compute: applications of arrows to domains, and the shortcuts of `phi_starter/4`. -/

/-- A proposition as a Boolean. -/
noncomputable def bp (p : Prop) : Bool := @decide p (Classical.propDecidable p)

@[simp] theorem bp_true {p : Prop} : bp p = Bool.true ↔ p := by simp [bp]
@[simp] theorem bp_false {p : Prop} : bp p = Bool.false ↔ ¬p := by simp [bp]

theorem bp_congr {p q : Prop} (h : p ↔ q) : bp p = bp q := by
  rw [propext h]

section
variable {V : Type}

/-- Element types for the function checks under the seen set `seen`: closed under the operations the checks
perform, with exact emptiness under `seen` and exact subtyping, and sound disjointness, from call depth `K`. -/
structure FunElem (E : Term → Prop) (den : Term → V → Prop) (K : Nat) (seen : Term) : Prop where
  phi : PhiCtx E den K seen
  union : ∀ {a b}, E a → E b → ∃ c, E c ∧ (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok c) ∧
    ∀ v, den c v ↔ den a v ∨ den b v
  neg : ∀ {a}, E a → ∃ c, E c ∧ (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_negation/1» (D m) a = .ok c) ∧
    ∀ v, den c v ↔ ¬den a v
  sub : ∀ {a b}, E a → E b → ∀ m, K ≤ m →
    Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (boolAtom (bp (∀ v, den a v → den b v)))
  disj : ∀ {a b}, E a → E b → ∃ s : Bool,
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«disjoint?/2» (D m) a b = .ok (boolAtom s)) ∧
    (s = Bool.true → ∀ v, den a v → den b v → False)
  term : E (.atom "term") ∧ ∀ v, den (.atom "term") v
  none : E (.map []) ∧ ∀ v, ¬den (.map []) v
  empty0 : ∀ {a}, E a → ∀ m, K ≤ m →
    Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map []) = .ok (boolAtom (isEmpty den a))
  empty1 : ∀ {a}, E a → ∀ m, K ≤ m → Elixir.Module.Types.Descr.«empty?/1» (D m) a = .ok (boolAtom (isEmpty den a))

/-- Domains of arrows, tuple types of their arguments standing for lists of values `dden`: closed under the
operations the checks perform, with exact emptiness with no seen set and under `seen`, from call depth `K`. -/
structure FunDom (Dm E : Term → Prop) (den : Term → V → Prop) (dden : Term → List V → Prop) (K : Nat)
    (seen : Term) : Prop where
  dom : ∀ l : List Term, (∀ a ∈ l, E a) → ∃ t, Dm t ∧ Elixir.Module.Types.Descr.«args_to_domain/1» (Term.list l) = .ok t ∧
    ∀ x, dden t x ↔ FunSem.InDomR (l.map den) x
  none : Dm (.map []) ∧ ∀ x, ¬dden (.map []) x
  isMap : ∀ {a}, Dm a → ∃ X, a = .map X
  union : ∀ {a b}, Dm a → Dm b → ∃ c, Dm c ∧
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok c) ∧ ∀ x, dden c x ↔ dden a x ∨ dden b x
  inter : ∀ {a b}, Dm a → Dm b → ∃ c, Dm c ∧
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c) ∧
    ∀ x, dden c x ↔ dden a x ∧ dden b x
  diff : ∀ {a b}, Dm a → Dm b → ∃ c, Dm c ∧
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c) ∧
    ∀ x, dden c x ↔ dden a x ∧ ¬dden b x
  empty : ∀ {a}, Dm a → ∀ m, K ≤ m →
    Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map []) = .ok (boolAtom (bp (∀ x, ¬dden a x)))
  emptySeen : ∀ {a}, Dm a → ∀ m, K ≤ m →
    Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a seen = .ok (boolAtom (bp (∀ x, ¬dden a x)))

variable {E Dm : Term → Prop} {den : Term → V → Prop} {dden : Term → List V → Prop} {K : Nat} {seen : Term}

theorem FunDom.empty1 (fd : FunDom Dm E den dden K seen) {a : Term} (ha : Dm a) (m : Nat) (hm : K ≤ m) :
    Elixir.Module.Types.Descr.«empty?/1» (D m) a = .ok (boolAtom (bp (∀ x, ¬dden a x))) := by
  obtain ⟨X, rfl⟩ := fd.isMap ha
  simp only [Elixir.Module.Types.Descr.«empty?/1»]
  exact fd.empty ha m hm

theorem app_congr_I {I I' : List V → Prop} (h : ∀ x, I x ↔ I' x) (r : V → Prop) (P : List (FunSem.Arrow V)) (v : V) :
    FunSem.App I r P v ↔ FunSem.App I' r P v := by
  have : I = I' := funext fun x => propext (h x)
  rw [this]

theorem app_congr_r (I : List V → Prop) {r r' : V → Prop} (h : ∀ v, r v ↔ r' v) (P : List (FunSem.Arrow V)) (v : V) :
    FunSem.App I r P v ↔ FunSem.App I r' P v := by
  have : r = r' := funext fun x => propext (h x)
  rw [this]

theorem inDomR_exists : ∀ (ts : List (V → Prop)), (∀ t ∈ ts, ∃ v, t v) → ∃ w, FunSem.InDomR ts w
  | [], _ => ⟨[], trivial⟩
  | t :: ts, h => by
    obtain ⟨v, hv⟩ := h t List.mem_cons_self
    obtain ⟨w, hw⟩ := inDomR_exists ts fun u mu => h u (List.mem_cons_of_mem _ mu)
    exact ⟨v :: w, hv, hw⟩

theorem inDomR_nil_iff {xs : List V} : FunSem.InDomR [] xs ↔ xs = [] := by
  cases xs <;> simp [FunSem.InDomR]

theorem inDomR_cons_iff {t : V → Prop} {B : List (V → Prop)} {zs : List V} :
    FunSem.InDomR (t :: B) zs ↔ ∃ z zs', zs = z :: zs' ∧ t z ∧ FunSem.InDomR B zs' := by
  cases zs with
  | nil => simp [FunSem.InDomR]
  | cons z zs =>
    simp only [FunSem.InDomR]
    exact ⟨fun h => ⟨z, zs, rfl, h⟩, fun ⟨z', zs', e, h⟩ => by
      simp only [List.cons.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact h⟩

theorem inDomR_append : ∀ (A B : List (V → Prop)) (xs : List V),
    FunSem.InDomR (A ++ B) xs ↔ ∃ ys zs, xs = ys ++ zs ∧ FunSem.InDomR A ys ∧ FunSem.InDomR B zs
  | [], B, xs => by
    constructor
    · intro h; exact ⟨[], xs, rfl, trivial, h⟩
    · rintro ⟨ys, zs, rfl, hy, hz⟩
      obtain rfl := inDomR_nil_iff.mp hy
      simpa using hz
  | t :: A, B, xs => by
    rw [List.cons_append, inDomR_cons_iff]
    constructor
    · rintro ⟨x, xs', rfl, hx, h⟩
      obtain ⟨ys, zs, rfl, hy, hz⟩ := (inDomR_append A B xs').mp h
      exact ⟨x :: ys, zs, rfl, inDomR_cons_iff.mpr ⟨x, ys, rfl, hx, hy⟩, hz⟩
    · rintro ⟨ys, zs, rfl, hy, hz⟩
      obtain ⟨y, ys', rfl, hx, hy'⟩ := inDomR_cons_iff.mp hy
      exact ⟨y, ys' ++ zs, rfl, hx, (inDomR_append A B _).mpr ⟨ys', zs, rfl, hy', hz⟩⟩

/-- Lists of values with a prefix in `A`, followed by a value and a rest that satisfy `Q`. -/
def Split (A : List (V → Prop)) (Q : V → List V → Prop) (x : List V) : Prop :=
  ∃ ys z zs, x = ys ++ z :: zs ∧ FunSem.InDomR A ys ∧ Q z zs

theorem split_congr {A : List (V → Prop)} {Q Q' : V → List V → Prop} (h : ∀ z zs, Q z zs ↔ Q' z zs) (x : List V) :
    Split A Q x ↔ Split A Q' x := by
  constructor
  · rintro ⟨ys, z, zs, e, a, q⟩; exact ⟨ys, z, zs, e, a, (h z zs).mp q⟩
  · rintro ⟨ys, z, zs, e, a, q⟩; exact ⟨ys, z, zs, e, a, (h z zs).mpr q⟩

theorem split_or {A : List (V → Prop)} {Q Q' : V → List V → Prop} (x : List V) :
    (Split A Q x ∨ Split A Q' x) ↔ Split A (fun z zs => Q z zs ∨ Q' z zs) x := by
  constructor
  · rintro (⟨ys, z, zs, e, a, q⟩ | ⟨ys, z, zs, e, a, q⟩)
    · exact ⟨ys, z, zs, e, a, Or.inl q⟩
    · exact ⟨ys, z, zs, e, a, Or.inr q⟩
  · rintro ⟨ys, z, zs, e, a, q | q⟩
    · exact Or.inl ⟨ys, z, zs, e, a, q⟩
    · exact Or.inr ⟨ys, z, zs, e, a, q⟩

theorem split_cons {A : List (V → Prop)} {d : V → Prop} {B : List (V → Prop)} (x : List V) :
    FunSem.InDomR (A ++ d :: B) x ↔ Split A (fun z zs => d z ∧ FunSem.InDomR B zs) x := by
  rw [inDomR_append]
  constructor
  · rintro ⟨ys, zs, rfl, hy, hz⟩
    obtain ⟨z, zs', rfl, hd, hb⟩ := inDomR_cons_iff.mp hz
    exact ⟨ys, z, zs', rfl, hy, hd, hb⟩
  · rintro ⟨ys, z, zs, rfl, hy, hd, hb⟩
    exact ⟨ys, z :: zs, rfl, hy, inDomR_cons_iff.mpr ⟨z, zs, rfl, hd, hb⟩⟩

/-- Lists of values in the products of `accm` reversed, followed by values of `types` that are not values of
`args`, position by position. -/
def RestSem (den : Term → V → Prop) (accm types args : List Term) (x : List V) : Prop :=
  ∃ ys zs, x = ys ++ zs ∧ FunSem.InDomR (accm.reverse.map den) ys ∧ FunSem.InDomR (types.map den) zs ∧
    ¬FunSem.InDomR (args.map den) zs

theorem rest_cons (accm types args : List Term) (t a : Term) (x : List V) :
    RestSem den accm (t :: types) (a :: args) x ↔ Split (accm.reverse.map den)
      (fun z zs => den t z ∧ FunSem.InDomR (types.map den) zs ∧ ¬(den a z ∧ FunSem.InDomR (args.map den) zs)) x := by
  constructor
  · rintro ⟨ys, zs, rfl, hy, hz, hn⟩
    obtain ⟨z, zs', rfl, ht, hb⟩ := inDomR_cons_iff.mp (by simpa using hz)
    exact ⟨ys, z, zs', rfl, hy, ht, hb, fun ⟨h₁, h₂⟩ => hn (by simpa using inDomR_cons_iff.mpr ⟨z, zs', rfl, h₁, h₂⟩)⟩
  · rintro ⟨ys, z, zs, rfl, hy, ht, hb, hn⟩
    refine ⟨ys, z :: zs, rfl, hy, by simpa using inDomR_cons_iff.mpr ⟨z, zs, rfl, ht, hb⟩, fun h => hn ?_⟩
    obtain ⟨z', zs', e, h₁, h₂⟩ := inDomR_cons_iff.mp (by simpa using h)
    simp only [List.cons.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨h₁, h₂⟩

theorem rest_snoc (m : Term) (accm types args : List Term) (x : List V) :
    RestSem den (m :: accm) types args x ↔ Split (accm.reverse.map den)
      (fun z zs => den m z ∧ FunSem.InDomR (types.map den) zs ∧ ¬FunSem.InDomR (args.map den) zs) x := by
  have e : (m :: accm).reverse.map den = accm.reverse.map den ++ [den m] := by simp
  constructor
  · rintro ⟨ys, zs, rfl, hy, hz, hn⟩
    rw [e] at hy
    obtain ⟨ys₁, ys₂, rfl, h₁, h₂⟩ := (inDomR_append _ _ ys).mp hy
    obtain ⟨z, zs', rfl, hd, hn'⟩ := inDomR_cons_iff.mp h₂
    obtain rfl := inDomR_nil_iff.mp hn'
    exact ⟨ys₁, z, zs, by simp, h₁, hd, hz, hn⟩
  · rintro ⟨ys, z, zs, rfl, hy, hd, hz, hn⟩
    refine ⟨ys ++ [z], zs, by simp, ?_, hz, hn⟩
    rw [e]
    exact (inDomR_append _ _ _).mpr ⟨ys, [z], rfl, hy, inDomR_cons_iff.mpr ⟨z, [], rfl, hd, trivial⟩⟩

theorem rest_nil (types args : List Term) (x : List V) :
    RestSem den [] types args x ↔ FunSem.InDomR (types.map den) x ∧ ¬FunSem.InDomR (args.map den) x := by
  constructor
  · rintro ⟨ys, zs, rfl, hy, hz, hn⟩
    obtain rfl := inDomR_nil_iff.mp (by simpa using hy)
    exact ⟨by simpa using hz, by simpa using hn⟩
  · rintro ⟨hz, hn⟩
    exact ⟨[], x, rfl, by simp [FunSem.InDomR], hz, hn⟩

/-- Products of arguments: lists of `n` element types, each with some value. -/
def ProdOk (E : Term → Prop) (den : Term → V → Prop) (n : Nat) (p : List Term) : Prop :=
  p.length = n ∧ ∀ e ∈ p, E e ∧ ∃ v, den e v

/-- The lists of values of a list of products. -/
def ProdSem (den : Term → V → Prop) (ps : List (List Term)) (x : List V) : Prop :=
  ∃ p ∈ ps, FunSem.InDomR (p.map den) x

theorem prodSem_cons (p : List Term) (ps : List (List Term)) (x : List V) :
    ProdSem den (p :: ps) x ↔ FunSem.InDomR (p.map den) x ∨ ProdSem den ps x := by
  simp [ProdSem]

theorem prodSem_ne {n : Nat} {ps : List (List Term)} (h : ∀ p ∈ ps, ProdOk E den n p) (ne : ps ≠ []) :
    ∃ x, ProdSem den ps x := by
  obtain ⟨p, mp⟩ : ∃ p, p ∈ ps := by
    cases ps with
    | nil => exact absurd rfl ne
    | cons p _ => exact ⟨p, List.mem_cons_self⟩
  obtain ⟨x, hx⟩ := inDomR_exists (p.map den) fun t mt => by
    obtain ⟨a, ma, rfl⟩ := List.mem_map.mp mt
    exact ((h p mp).2 a ma).2
  exact ⟨x, p, mp, hx⟩

/-- Meets of elements with negated elements, position by position, each with some value. -/
def Meets (E : Term → Prop) (den : Term → V → Prop) : List Term → List Term → List Term → Prop
  | [], ts, as => ts = [] ∧ as = []
  | m :: ms, ts, as => ∃ t ts' a as', ts = t :: ts' ∧ as = a :: as' ∧ E m ∧ (∀ v, den m v ↔ den t v ∧ den a v) ∧
      (∃ v, den m v) ∧ Meets E den ms ts' as'

/-- `tuple_elements_meets/4` with no seen set meets a product with the arguments of an arrow, or finds them
disjoint. -/
theorem meets_sem (fe : FunElem E den K seen) : ∀ (nl l acc : List Term), l.length = nl.length →
    (∀ e ∈ l, E e) → (∀ e ∈ nl, E e) →
    ((∀ m, K ≤ m → Elixir.Module.Types.Descr.«tuple_elements_meets/4» (D m) (Term.list l) (Term.list nl)
        (Term.list acc) (.map []) = .ok (.atom "disjoint")) ∧
      ∀ x, FunSem.InDomR (l.map den) x → ¬FunSem.InDomR (nl.map den) x) ∨
    ∃ ms, Meets E den ms l nl ∧ ∀ m, K ≤ m → Elixir.Module.Types.Descr.«tuple_elements_meets/4» (D m)
      (Term.list l) (Term.list nl) (Term.list acc) (.map []) = .ok (Term.list (acc.reverse ++ ms))
  | [], l, acc, hlen, _, _ => by
    obtain rfl : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    exact Or.inr ⟨[], ⟨rfl, rfl⟩, fun m _ => by simpa using meets_done (D m) _ _ acc⟩
  | nt :: nl, l, acc, hlen, hl, hnl => by
    obtain ⟨ty, es, rfl⟩ : ∃ ty es, l = ty :: es := by
      cases l with
      | nil => simp at hlen
      | cons x xs => exact ⟨x, xs, rfl⟩
    have hty := hl ty List.mem_cons_self
    have hes : ∀ e ∈ es, E e := fun e m => hl e (List.mem_cons_of_mem _ m)
    have hnt := hnl nt List.mem_cons_self
    have hnl' : ∀ e ∈ nl, E e := fun e m => hnl e (List.mem_cons_of_mem _ m)
    obtain ⟨meet, lmeet, hmeet, smeet⟩ := fe.phi.inter hty hnt
    have step := fun m (hm : K ≤ m) => meets_step (D m) acc (ty :: es) nt nl (.map []) ty es (Or.inr rfl) meet
      (hmeet m hm)
    have em := fe.empty0 lmeet
    rw [list_cons nt nl]
    by_cases ne : ∃ v, den meet v
    · have hb : isEmpty den meet = Bool.false := by
        cases h : isEmpty den meet
        · rfl
        · obtain ⟨v, hv⟩ := ne; exact absurd hv ((isEmpty_iff den meet).mp h v)
      rcases meets_sem fe nl es (meet :: acc) (by simpa using hlen) hes hnl' with ⟨dis, sem⟩ | ⟨ms, hms, run⟩
      · refine Or.inl ⟨fun m hm => by rw [(step m hm).2 (by simpa [hb, boolAtom] using em m hm)]; exact dis m hm, ?_⟩
        intro x h₁ h₂
        cases x with
        | nil => simp [FunSem.InDomR] at h₁
        | cons y ys => exact sem ys h₁.2 h₂.2
      · refine Or.inr ⟨meet :: ms, ⟨ty, es, nt, nl, rfl, rfl, lmeet, smeet, ne, hms⟩, fun m hm => ?_⟩
        rw [(step m hm).2 (by simpa [hb, boolAtom] using em m hm), run m hm]
        simp
    · have hb : isEmpty den meet = Bool.true := (isEmpty_iff den meet).mpr fun v hv => ne ⟨v, hv⟩
      refine Or.inl ⟨fun m hm => (step m hm).1 (by simpa [hb, boolAtom] using em m hm), ?_⟩
      intro x h₁ h₂
      cases x with
      | nil => simp [FunSem.InDomR] at h₁
      | cons y ys => exact ne ⟨y, (smeet y).mpr ⟨h₁.1, h₂.1⟩⟩

/-- `product_difference/5` splits a product minus the arguments of an arrow into products, after the products `acc`
already found. -/
theorem prod_diff_sem (fe : FunElem E den K seen) (n : Nat) :
    ∀ types args meets : List Term, Meets E den meets types args → (∀ e ∈ types, E e ∧ ∃ v, den e v) →
      (∀ e ∈ args, E e) → ∀ accm : List Term, accm.length + types.length = n → (∀ e ∈ accm, E e ∧ ∃ v, den e v) →
      ∀ acc : List (List Term), (∀ p ∈ acc, ProdOk E den n p) →
      ∃ out : List (List Term), (∀ p ∈ out, ProdOk E den n p) ∧ (∀ m, K ≤ m →
        Elixir.Module.Types.Descr.«product_difference/5» (D m) (Term.list types) (Term.list args)
          (Term.list meets) (Term.list accm) (Term.list (acc.map Term.list)) = .ok (Term.list (out.map Term.list))) ∧
        ∀ x, ProdSem den out x ↔ ProdSem den acc x ∨ RestSem den accm types args x
  | [], args, meets, hM, _, _, accm, _, _, acc, hacc => by
    have hm : meets = [] ∧ args = [] := by
      cases meets with
      | nil => exact ⟨rfl, hM.2⟩
      | cons _ _ => obtain ⟨_, _, _, _, h, -⟩ := hM; cases h
    obtain ⟨rfl, rfl⟩ := hm
    refine ⟨acc, hacc, fun m _ => by rw [Elixir.Module.Types.Descr.«product_difference/5».eq_def]; rfl,
      fun x => ⟨Or.inl, ?_⟩⟩
    rintro (h | ⟨ys, zs, -, -, hz, hn⟩)
    · exact h
    · exact absurd (by simpa using hz) hn
  | ty :: types, args, meets, hM, ht, hargs, accm, hn, haccm, acc, hacc => by
    obtain ⟨mt, meets, rfl⟩ : ∃ mt ms, meets = mt :: ms := by
      cases meets with
      | nil => obtain ⟨h, -⟩ := hM; cases h
      | cons x xs => exact ⟨x, xs, rfl⟩
    obtain ⟨t', ts', a, args', e₁, rfl, lmt, smt, nmt, hM'⟩ := hM
    simp only [List.cons.injEq] at e₁
    obtain ⟨rfl, rfl⟩ := e₁
    have hty := ht ty List.mem_cons_self
    have ht' : ∀ e ∈ types, E e ∧ ∃ v, den e v := fun e m => ht e (List.mem_cons_of_mem _ m)
    have ha := hargs a List.mem_cons_self
    have ha' : ∀ e ∈ args', E e := fun e m => hargs e (List.mem_cons_of_mem _ m)
    obtain ⟨diff, ldiff, hdiff, sdiff⟩ := fe.phi.diff hty.1 ha
    have e1 := fe.empty1 ldiff
    simp only [List.length_cons] at hn
    by_cases ne : ∃ v, den diff v
    · have hb : isEmpty den diff = Bool.false := by
        cases h : isEmpty den diff
        · rfl
        · obtain ⟨v, hv⟩ := ne; exact absurd hv ((isEmpty_iff den diff).mp h v)
      obtain ⟨out, hout, run, sem⟩ := prod_diff_sem fe n types args' meets hM' ht' ha' (mt :: accm) (by simp; omega)
        (fun e me => by
          rcases List.mem_cons.mp me with rfl | me
          · exact ⟨lmt, nmt⟩
          · exact haccm e me)
        ((accm.reverse ++ diff :: types) :: acc) (fun p mp => by
          rcases List.mem_cons.mp mp with rfl | mp
          · refine ⟨by simp; omega, fun e me => ?_⟩
            simp only [List.mem_append, List.mem_reverse, List.mem_cons] at me
            rcases me with me | rfl | me
            · exact haccm e me
            · exact ⟨ldiff, ne⟩
            · exact ht' e me
          · exact hacc p mp)
      refine ⟨out, hout, fun m hm => ?_, fun x => ?_⟩
      · rw [Elixir.Module.Types.Descr.«product_difference/5».eq_def]
        simp only [Term.list] at run ⊢
        have rev := reverse_list accm (diff :: types)
        simp only [Term.list] at rev
        simp [hdiff m hm, e1 m hm, hb, boolAtom, isMember, rev]
        simpa using run m hm
      · rw [sem x, prodSem_cons, rest_cons, rest_snoc, List.map_append, List.map_cons, split_cons]
        have key : Split (accm.reverse.map den) (fun z zs => den diff z ∧ FunSem.InDomR (types.map den) zs) x ∨
              Split (accm.reverse.map den) (fun z zs => den mt z ∧ FunSem.InDomR (types.map den) zs ∧
                ¬FunSem.InDomR (args'.map den) zs) x ↔
            Split (accm.reverse.map den) (fun z zs => den ty z ∧ FunSem.InDomR (types.map den) zs ∧
              ¬(den a z ∧ FunSem.InDomR (args'.map den) zs)) x := by
          rw [split_or]
          refine split_congr (fun z zs => ?_) x
          rw [sdiff z, smt z]
          constructor
          · rintro (⟨⟨h₁, h₂⟩, h₃⟩ | ⟨⟨h₁, h₂⟩, h₃, h₄⟩)
            · exact ⟨h₁, h₃, fun h => h₂ h.1⟩
            · exact ⟨h₁, h₃, fun h => h₄ h.2⟩
          · rintro ⟨h₁, h₂, h₃⟩
            by_cases h : den a z
            · exact Or.inr ⟨⟨h₁, h⟩, h₂, fun h' => h₃ ⟨h, h'⟩⟩
            · exact Or.inl ⟨⟨h₁, h⟩, h₂⟩
        rw [← key]
        constructor
        · rintro ((h | h) | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | h | h)
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
    · have hb : isEmpty den diff = Bool.true := (isEmpty_iff den diff).mpr fun v hv => ne ⟨v, hv⟩
      obtain ⟨out, hout, run, sem⟩ := prod_diff_sem fe n types args' meets hM' ht' ha' (ty :: accm) (by simp; omega)
        (fun e me => by
          rcases List.mem_cons.mp me with rfl | me
          · exact hty
          · exact haccm e me) acc hacc
      refine ⟨out, hout, fun m hm => ?_, fun x => ?_⟩
      · rw [Elixir.Module.Types.Descr.«product_difference/5».eq_def]
        simp only [Term.list] at run ⊢
        simp [hdiff m hm, e1 m hm, hb, boolAtom, isMember]
        simpa using run m hm
      · rw [sem x, rest_cons, rest_snoc]
        refine or_congr Iff.rfl (split_congr (fun z zs => ?_) x)
        constructor
        · rintro ⟨h₁, h₂, h₃⟩; exact ⟨h₁, h₂, fun h => h₃ h.2⟩
        · rintro ⟨h₁, h₂, h₃⟩
          refine ⟨h₁, h₂, fun h => h₃ ⟨?_, h⟩⟩
          exact Classical.byContradiction fun na => ne ⟨z, (sdiff z).mpr ⟨h₁, na⟩⟩

/-- `args_difference/4` subtracts the arguments of an arrow from products: all of them are disjoint from the
arguments, or the products of what remains are found, after the products `acc` already found. -/
theorem args_diff_sem (fe : FunElem E den K seen) (args : List Term) (hargs : ∀ e ∈ args, E e) :
    ∀ products : List (List Term), (∀ p ∈ products, ProdOk E den args.length p) →
      ∀ acc : List (List Term), (∀ p ∈ acc, ProdOk E den args.length p) → ∀ dj : Bool,
      ∃ out : Term, (∀ m, K ≤ m → Elixir.Module.Types.Descr.«args_difference/4» (D m)
          (Term.list (products.map Term.list)) (Term.list args) (Term.list (acc.map Term.list)) (boolAtom dj) =
            .ok out) ∧
        ((out = .atom "disjoint" ∧ dj = Bool.true ∧ ∀ x, ProdSem den products x → ¬FunSem.InDomR (args.map den) x) ∨
          ∃ ps, out = Term.list (ps.map Term.list) ∧ (∀ p ∈ ps, ProdOk E den args.length p) ∧
            ∀ x, ProdSem den ps x ↔ ProdSem den acc x ∨ (ProdSem den products x ∧ ¬FunSem.InDomR (args.map den) x)) := by
  intro products
  induction products with
  | nil =>
    intro _ acc hacc dj
    cases dj
    · refine ⟨_, fun m _ => by rw [Elixir.Module.Types.Descr.«args_difference/4».eq_def]; rfl,
        Or.inr ⟨acc, rfl, hacc, fun x => ?_⟩⟩
      simp [ProdSem]
    · exact ⟨_, fun m _ => by rw [Elixir.Module.Types.Descr.«args_difference/4».eq_def]; rfl,
        Or.inl ⟨rfl, rfl, fun x h => by simp [ProdSem] at h⟩⟩
  | cons p products ih =>
    intro hps acc hacc dj
    obtain ⟨hpl, hp⟩ := hps p List.mem_cons_self
    have hps' : ∀ q ∈ products, ProdOk E den args.length q := fun q m => hps q (List.mem_cons_of_mem _ m)
    rcases meets_sem fe args p [] hpl (fun e me => (hp e me).1) hargs with ⟨dis, sem⟩ | ⟨ms, hms, run⟩
    · obtain ⟨out, rout, hout⟩ := ih hps' (p :: acc) (fun q mq => by
        rcases List.mem_cons.mp mq with rfl | mq
        · exact ⟨hpl, hp⟩
        · exact hacc q mq) dj
      refine ⟨out, fun m hm => ?_, ?_⟩
      · have d := dis m hm
        rw [Elixir.Module.Types.Descr.«args_difference/4».eq_def]
        simp [d]
        simpa using rout m hm
      · rcases hout with ⟨e, edj, h⟩ | ⟨ps, e, hps'', h⟩
        · refine Or.inl ⟨e, edj, fun x hx => ?_⟩
          rcases (prodSem_cons p products x).mp hx with hx | hx
          · exact sem x hx
          · exact h x hx
        · refine Or.inr ⟨ps, e, hps'', fun x => ?_⟩
          rw [h x, prodSem_cons, prodSem_cons]
          constructor
          · rintro ((h | h) | ⟨h, n⟩)
            · exact Or.inr ⟨Or.inl h, sem x h⟩
            · exact Or.inl h
            · exact Or.inr ⟨Or.inr h, n⟩
          · rintro (h | ⟨h | h, n⟩)
            · exact Or.inl (Or.inr h)
            · exact Or.inl (Or.inl h)
            · exact Or.inr ⟨h, n⟩
    · obtain ⟨acc', hacc', rpd, spd⟩ := prod_diff_sem fe args.length p args ms hms hp hargs [] (by simp [hpl])
        (by simp) acc hacc
      obtain ⟨out, rout, hout⟩ := ih hps' acc' hacc' Bool.false
      refine ⟨out, fun m hm => ?_, ?_⟩
      · have d := run m hm
        simp only [List.reverse_nil, List.nil_append] at d
        have pd := rpd m hm
        rw [Elixir.Module.Types.Descr.«args_difference/4».eq_def]
        cases ms with
        | nil => simp [d, pd]; simpa [boolAtom] using rout m hm
        | cons x xs => simp [d] at pd ⊢; simp [pd]; simpa [boolAtom] using rout m hm
      · rcases hout with ⟨-, h, -⟩ | ⟨ps, e, hps'', h⟩
        · cases h
        · refine Or.inr ⟨ps, e, hps'', fun x => ?_⟩
          rw [h x, spd x, rest_nil, prodSem_cons]
          constructor
          · rintro ((h | ⟨h, n⟩) | ⟨h, n⟩)
            · exact Or.inl h
            · exact Or.inr ⟨Or.inl h, n⟩
            · exact Or.inr ⟨Or.inr h, n⟩
          · rintro (h | ⟨h | h, n⟩)
            · exact Or.inl (Or.inl h)
            · exact Or.inl (Or.inr ⟨h, n⟩)
            · exact Or.inr ⟨h, n⟩

theorem app_mono_r : ∀ (P : List (FunSem.Arrow V)) (I : List V → Prop) (r r' : V → Prop), (∀ v, r v → r' v) →
    ∀ v, FunSem.App I r P v → FunSem.App I r' P v
  | [], _, _, _, h, v, a => h v a
  | (us, s) :: P, I, r, r', h, v, a => by
    simp only [FunSem.App] at a ⊢
    rcases a with ⟨ne, a⟩ | a
    · exact Or.inl ⟨ne, app_mono_r P _ r r' h v a⟩
    · exact Or.inr (app_mono_r P I _ _ (fun v ⟨x, y⟩ => ⟨h v x, y⟩) v a)

/-- Applications return values of the returns reached. -/
theorem app_sub_r : ∀ (P : List (FunSem.Arrow V)) (I : List V → Prop) (r : V → Prop) (v : V),
    FunSem.App I r P v → r v
  | [], _, _, _, a => a
  | (us, s) :: P, I, r, v, a => by
    simp only [FunSem.App] at a
    rcases a with ⟨-, a⟩ | a
    · exact app_sub_r P _ r v a
    · exact (app_sub_r P I _ v a).1

/-- `aux_apply/4` unites its result with the application of the arrows to the products, refined by the returns
reached so far. -/
theorem aux_apply_sem (fe : FunElem E den K seen) (n : Nat) :
    ∀ P : List (Term × List Term × Term), PosOk E n P → ∀ result rets (products : List (List Term)), E result →
      E rets → (∀ p ∈ products, ProdOk E den n p) → products ≠ [] →
      ∃ r, E r ∧ (∀ m, K ≤ m → Elixir.Module.Types.Descr.«aux_apply/4» (D m) result
          (Term.list (products.map Term.list)) rets (encP P) = .ok r) ∧
        ∀ v, den r v ↔ den result v ∨ FunSem.App (ProdSem den products) (den rets) (semP den P) v := by
  intro P
  induction P with
  | nil =>
    intro _ result rets products hres hrets _ _
    obtain ⟨u, hu, ru, su⟩ := fe.union hres hrets
    by_cases hs : ∀ v, den rets v → den result v
    · refine ⟨result, hres, fun m hm => ?_, fun v => ?_⟩
      · have h := fe.sub hrets hres m hm
        have hb : bp (∀ v, den rets v → den result v) = Bool.true := bp_true.mpr hs
        unfold Elixir.Module.Types.Descr.«aux_apply/4»
        simp [encP, Term.list, h, hb, isMember]
      · simp only [semP, List.map_nil, FunSem.App]
        exact ⟨Or.inl, fun h => h.elim id (hs v)⟩
    · refine ⟨u, hu, fun m hm => ?_, fun v => ?_⟩
      · have h := fe.sub hrets hres m hm
        have hb : bp (∀ v, den rets v → den result v) = Bool.false := bp_false.mpr hs
        unfold Elixir.Module.Types.Descr.«aux_apply/4»
        simp [encP, Term.list, h, hb, isMember, ru m hm]
      · simp only [semP, List.map_nil, FunSem.App]
        exact su v
  | cons p rest ih =>
    intro hP result rets products hres hrets hps nep
    obtain ⟨key, args, ret⟩ := p
    obtain ⟨hargs, hret, hlen⟩ := hP _ List.mem_cons_self
    have ih' := ih fun q mq => hP q (List.mem_cons_of_mem _ mq)
    have hps' : ∀ q ∈ products, ProdOk E den args.length q := fun q mq => ⟨by rw [(hps q mq).1, hlen], (hps q mq).2⟩
    obtain ⟨refine, hrefine, rrefine, srefine⟩ := fe.phi.inter hrets hret
    obtain ⟨x₀, hx₀⟩ := prodSem_ne hps nep
    have app : ∀ v, FunSem.App (ProdSem den products) (den rets) (semP den ((key, args, ret) :: rest)) v ↔
        ((∃ x, ProdSem den products x ∧ ¬FunSem.InDomR (args.map den) x) ∧
          FunSem.App (fun x => ProdSem den products x ∧ ¬FunSem.InDomR (args.map den) x) (den rets) (semP den rest) v) ∨
          FunSem.App (ProdSem den products) (den refine) (semP den rest) v := by
      intro v
      simp only [semP, List.map_cons, FunSem.App]
      exact or_congr Iff.rfl (app_congr_r _ (fun v => (srefine v).symm) _ v)
    obtain ⟨out, rout, hout⟩ := args_diff_sem fe args hargs products hps' [] (by simp) Bool.true
    have runs : ∀ m, K ≤ m → Elixir.Module.Types.Descr.«args_difference/4» (D m) (Term.list (products.map Term.list))
        (Term.list args) .nil (.atom "true") = .ok out := fun m hm => by simpa [boolAtom] using rout m hm
    rcases hout with ⟨rfl, -, dis⟩ | ⟨ps, rfl, hps'', sps⟩
    · -- the products are disjoint from the domain of the arrow, which is skipped
      obtain ⟨r, hr, run, s⟩ := ih' result rets products hres hrets hps nep
      refine ⟨r, hr, fun m hm => ?_, fun v => ?_⟩
      · unfold Elixir.Module.Types.Descr.«aux_apply/4»
        simp only [encP, List.map_cons, Term.list] at run ⊢
        simp [runs m hm]
        exact run m hm
      · rw [s, app]
        have same : ∀ x, ProdSem den products x ∧ ¬FunSem.InDomR (args.map den) x ↔ ProdSem den products x :=
          fun x => ⟨And.left, fun h => ⟨h, dis x h⟩⟩
        rw [app_congr_I same]
        refine or_congr Iff.rfl ⟨fun h => Or.inl ⟨⟨x₀, hx₀, dis x₀ hx₀⟩, h⟩, ?_⟩
        rintro (⟨-, h⟩ | h)
        · exact h
        · exact app_mono_r _ _ _ _ (fun v h => ((srefine v).mp h).1) v h
    cases ps with
    | nil =>
      -- the domain of the arrow covers the products: the return is refined
      obtain ⟨r, hr, run, s⟩ := ih' result refine products hres hrefine hps nep
      refine ⟨r, hr, fun m hm => ?_, fun v => ?_⟩
      · unfold Elixir.Module.Types.Descr.«aux_apply/4»
        simp only [encP, List.map_cons, Term.list] at run ⊢
        simp [runs m hm, rrefine m hm]
        exact run m hm
      · rw [s, app]
        refine or_congr Iff.rfl ⟨Or.inr, ?_⟩
        rintro (⟨⟨x, hx, hn⟩, -⟩ | h)
        · exact absurd ((sps x).mpr (Or.inr ⟨hx, hn⟩)) (by simp [ProdSem])
        · exact h
    | cons q qs =>
      -- the products are split: the uncovered ones go on, and the return is refined on all of them
      have uncovered : ∀ x, ProdSem den (q :: qs) x ↔ ProdSem den products x ∧ ¬FunSem.InDomR (args.map den) x :=
        fun x => by rw [sps x]; simp [ProdSem]
      have hq : ∀ x ∈ q :: qs, ProdOk E den n x := fun x mx => ⟨by rw [(hps'' x mx).1, hlen], (hps'' x mx).2⟩
      obtain ⟨r₁, hr₁, run₁, s₁⟩ := ih' result rets (q :: qs) hres hrets hq (by simp)
      obtain ⟨r₂, hr₂, run₂, s₂⟩ := ih' r₁ refine products hr₁ hrefine hps nep
      obtain ⟨y₀, hy₀⟩ := prodSem_ne hq (by simp)
      have first : ∀ v, den r₁ v ↔ den result v ∨
          ((∃ x, ProdSem den products x ∧ ¬FunSem.InDomR (args.map den) x) ∧
            FunSem.App (fun x => ProdSem den products x ∧ ¬FunSem.InDomR (args.map den) x) (den rets)
              (semP den rest) v) := fun v => by
        rw [s₁, app_congr_I uncovered]
        exact or_congr Iff.rfl ⟨fun h => ⟨⟨y₀, (uncovered y₀).mp hy₀⟩, h⟩, And.right⟩
      by_cases sb : ∀ v, den refine v → den r₁ v
      · refine ⟨r₁, hr₁, fun m hm => ?_, fun v => ?_⟩
        · have h := fe.sub hrefine hr₁ m hm
          have hb : bp (∀ v, den refine v → den r₁ v) = Bool.true := bp_true.mpr sb
          have r1 := run₁ m hm
          simp only [List.map_cons] at r1
          unfold Elixir.Module.Types.Descr.«aux_apply/4»
          simp only [encP, List.map_cons, Term.list] at r1 ⊢
          simp [runs m hm, rrefine m hm, r1, h, hb, isMember]
        · rw [first, app]
          constructor
          · rintro (h | h)
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
          · rintro (h | h | h)
            · exact Or.inl h
            · exact Or.inr h
            · exact (first v).mp (sb v (app_sub_r _ _ _ v h))
      · refine ⟨r₂, hr₂, fun m hm => ?_, fun v => ?_⟩
        · have h := fe.sub hrefine hr₁ m hm
          have hb : bp (∀ v, den refine v → den r₁ v) = Bool.false := bp_false.mpr sb
          have r1 := run₁ m hm
          simp only [List.map_cons] at r1
          unfold Elixir.Module.Types.Descr.«aux_apply/4»
          simp only [encP, List.map_cons, Term.list] at r1 run₂ ⊢
          simp [runs m hm, rrefine m hm, r1, h, hb, isMember, run₂ m hm]
        · rw [s₂, first, app]
          constructor
          · rintro ((h | h) | h)
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
          · rintro (h | h | h)
            · exact Or.inl (Or.inl h)
            · exact Or.inl (Or.inr h)
            · exact Or.inr h

/-- Folds that unite into their accumulator, at every call depth from `K`. -/
theorem foldl1_or {W : Type} (K : Nat) (f : Term) (Inv : Term → Prop) (sem : Term → W → Prop) (G : Term → W → Prop) :
    ∀ l : List Term, (∀ x ∈ l, ∀ a, Inv a → ∃ a', Inv a' ∧ (∀ m, K ≤ m → (D m).pure f #[x, a] = .ok a') ∧
      ∀ w, sem a' w ↔ sem a w ∨ G x w) →
      ∀ acc, Inv acc → ∃ r, Inv r ∧ (∀ m, K ≤ m → Erlang.lists.«foldl_1/3» (D m) f acc (Term.list l) = .ok r) ∧
        ∀ w, sem r w ↔ sem acc w ∨ ∃ x ∈ l, G x w := by
  intro l
  induction l with
  | nil => exact fun _ acc h => ⟨acc, h, fun m _ => by simp [Erlang.lists.«foldl_1/3»], fun w => by simp⟩
  | cons x xs ih =>
    intro step acc hacc
    obtain ⟨a', ha', run, s'⟩ := step x List.mem_cons_self acc hacc
    obtain ⟨r, hr, rest, s⟩ := ih (fun y my => step y (List.mem_cons_of_mem _ my)) a' ha'
    refine ⟨r, hr, fun m hm => ?_, fun w => ?_⟩
    · rw [Erlang.lists.«foldl_1/3».eq_def]
      simp only [run m hm, Lynx.Except.ok_bind]
      exact rest m hm
    · rw [s, s']
      constructor
      · rintro ((h | h) | ⟨y, my, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨x, List.mem_cons_self, h⟩
        · exact Or.inr ⟨y, List.mem_cons_of_mem _ my, h⟩
      · rintro (h | ⟨y, my, h⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp my with rfl | my
          · exact Or.inl (Or.inr h)
          · exact Or.inr ⟨y, my, h⟩

theorem foldl_or {W : Type} (K : Nat) (mo nm : String) (caps : Array Term) (Inv : Term → Prop) (sem : Term → W → Prop)
    (G : Term → W → Prop) (l : List Term)
    (step : ∀ x ∈ l, ∀ a, Inv a → ∃ a', Inv a' ∧ (∀ m, K ≤ m → (D m).pure (.function mo nm 2 caps) #[x, a] = .ok a') ∧
      ∀ w, sem a' w ↔ sem a w ∨ G x w) (acc : Term) (hacc : Inv acc) :
    ∃ r, Inv r ∧ (∀ m, K ≤ m →
      Erlang.lists.«foldl/3» (D m) (.function mo nm 2 caps) acc (Term.list l) = .ok r) ∧
      ∀ w, sem r w ↔ sem acc w ∨ ∃ x ∈ l, G x w := by
  obtain ⟨r, hr, run, s⟩ := foldl1_or K _ Inv sem G l step acc hacc
  refine ⟨r, hr, fun m hm => ?_, s⟩
  have := run m hm
  cases l with
  | nil =>
    have e : acc = r := by simpa [Term.list, Erlang.lists.«foldl_1/3», pure, Except.pure] using this
    subst e
    simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  | cons x xs =>
    rw [Erlang.lists.«foldl_1/3».eq_def] at this
    simpa [Erlang.lists.«foldl/3», Lynx.Except.guard, Erlang.erlang.«is_function/2», Term.list] using this

theorem enc_inj {a b a' b' : Term} {l l' : List Term}
    (e : Term.tuple #[a, Term.list l, b] = .tuple #[a', Term.list l', b']) : a = a' ∧ l = l' ∧ b = b' := by
  simp only [Term.tuple.injEq] at e
  have e₀ := congrArg (fun a : Array Term => a[0]?) e
  have e₁ := congrArg (fun a : Array Term => a[1]?) e
  have e₂ := congrArg (fun a : Array Term => a[2]?) e
  simp at e₀ e₁ e₂
  exact ⟨e₀, list_inj e₁, e₂⟩

/-- `fetch_domain/1` unites the domains of the positive arrows. -/
theorem fetch_domain_sem (fd : FunDom Dm E den dden K seen) (n : Nat) (P : List (Term × List Term × Term))
    (hP : PosOk E n P) :
    ∃ fdom, Dm fdom ∧ (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«fetch_domain/1» (D m) (encP P) = .ok fdom) ∧
      ∀ x, dden fdom x ↔ ∃ p ∈ semP den P, FunSem.InDomR p.1 x := by
  let G : Term → List V → Prop := fun t x => ∃ p ∈ P, t = .tuple #[p.1, Term.list p.2.1, p.2.2] ∧
    FunSem.InDomR (p.2.1.map den) x
  obtain ⟨r, hr, run, s⟩ := foldl_or (K + 1) "Elixir.Module.Types.Descr" "-fetch_domain/1-fun-0-" #[] Dm dden G
    (P.map fun p => .tuple #[p.1, Term.list p.2.1, p.2.2]) (by
      intro t mt a ha
      obtain ⟨p, mp, rfl⟩ := List.mem_map.mp mt
      obtain ⟨hargs, -, -⟩ := hP p mp
      obtain ⟨dom, hdom, rdom, sdom⟩ := fd.dom p.2.1 hargs
      obtain ⟨u, hu, ru, su⟩ := fd.union ha hdom
      refine ⟨u, hu, fun m hm => ?_, fun x => ?_⟩
      · obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
        rw [Erlang.program.«Elixir.Module.Types.Descr:-fetch_domain/1-fun-0-/2».pure]
        simp [Elixir.Module.Types.Descr.«-fetch_domain/1-fun-0-/2», rdom, ru m' hm']
      · rw [su, sdom]
        refine or_congr Iff.rfl ⟨fun h => ⟨p, mp, rfl, h⟩, fun ⟨q, mq, e, h⟩ => ?_⟩
        obtain ⟨-, el, -⟩ := enc_inj e
        rw [el]; exact h) (.map []) fd.none.1
  refine ⟨r, hr, fun m hm => by unfold Elixir.Module.Types.Descr.«fetch_domain/1»; exact run m hm, fun x => ?_⟩
  rw [s]
  simp only [fd.none.2, false_or, List.mem_map, semP, G]
  constructor
  · rintro ⟨_, ⟨p, mp, rfl⟩, q, mq, e, h⟩
    exact ⟨_, ⟨q, mq, rfl⟩, h⟩
  · rintro ⟨_, ⟨p, mp, rfl⟩, h⟩
    exact ⟨_, ⟨p, mp, rfl⟩, p, mp, rfl, h⟩

/-- `fun_apply_static/2` applies the positive arrows to nonempty arguments. -/
theorem apply_static_sem (fe : FunElem E den K seen) (n : Nat) (args : List Term) (hargs : ∀ a ∈ args, E a)
    (ne : ∀ a ∈ args, ∃ v, den a v) (len : args.length = n) (P : List (Term × List Term × Term)) (hP : PosOk E n P) :
    ∃ r, E r ∧ (∀ m, K + 1 ≤ m →
      Elixir.Module.Types.Descr.«fun_apply_static/2» (D m) (Term.list args) (Term.list [encP P]) = .ok r) ∧
      ∀ v, den r v ↔ FunSem.App (FunSem.InDomR (args.map den)) (fun _ => True) (semP den P) v := by
  let G : Term → V → Prop := fun t v => t = encP P ∧ FunSem.App (FunSem.InDomR (args.map den)) (fun _ => True) (semP den P) v
  have prod : ∀ x, ProdSem den [args] x ↔ FunSem.InDomR (args.map den) x := fun x => by simp [ProdSem]
  obtain ⟨r, hr, run, s⟩ := foldl_or (K + 1) "Elixir.Module.Types.Descr" "-fun_apply_static/2-fun-0-"
    #[Term.list args] E den G [encP P] (by
      intro t mt a ha
      rw [List.mem_singleton.mp mt]
      obtain ⟨r, hr, run, s⟩ := aux_apply_sem fe n P hP a (.atom "term") [args] ha fe.term.1
        (fun p mp => by
          rw [List.mem_singleton.mp mp]
          exact ⟨len, fun e me => ⟨hargs e me, ne e me⟩⟩) (by simp)
      refine ⟨r, hr, fun m hm => ?_, fun v => ?_⟩
      · obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
        rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_apply_static/2-fun-0-/2».pure]
        simpa [Elixir.Module.Types.Descr.«-fun_apply_static/2-fun-0-/3»] using run m' hm'
      · rw [s, app_congr_I prod, app_congr_r _ (fun v => iff_true_intro (fe.term.2 v))]
        simp [G]) (.map []) fe.none.1
  refine ⟨r, hr, fun m hm => by unfold Elixir.Module.Types.Descr.«fun_apply_static/2»; simpa using run m hm,
    fun v => ?_⟩
  rw [s]
  simp [fe.none.2, G]

/-- `apply_disjoint/2` unites the returns of the positive arrows whose domain meets the arguments. -/
theorem apply_disjoint_sem (fe : FunElem E den K seen) (fd : FunDom Dm E den dden K seen) (n : Nat) (args : List Term)
    (hargs : ∀ a ∈ args, E a) (P : List (Term × List Term × Term)) (hP : PosOk E n P) :
    ∃ r, E r ∧ (∀ m, K + 1 ≤ m →
      Elixir.Module.Types.Descr.«apply_disjoint/2» (D m) (Term.list args) (encP P) = .ok r) ∧
      ∀ v, den r v ↔ ∃ p ∈ semP den P, (∃ x, FunSem.InDomR (args.map den) x ∧ FunSem.InDomR p.1 x) ∧ p.2 v := by
  obtain ⟨dom, hdom, rdom, sdom⟩ := fd.dom args hargs
  let G : Term → V → Prop := fun t v => ∃ p ∈ P, t = .tuple #[p.1, Term.list p.2.1, p.2.2] ∧
    (∃ x, FunSem.InDomR (args.map den) x ∧ FunSem.InDomR (p.2.1.map den) x) ∧ den p.2.2 v
  have G_enc : ∀ p ∈ P, ∀ v, G (.tuple #[p.1, Term.list p.2.1, p.2.2]) v ↔
      (∃ x, FunSem.InDomR (args.map den) x ∧ FunSem.InDomR (p.2.1.map den) x) ∧ den p.2.2 v := by
    intro p mp v
    constructor
    · rintro ⟨q, mq, e, h⟩
      obtain ⟨-, el, er⟩ := enc_inj e
      rw [el, er]; exact h
    · exact fun h => ⟨p, mp, rfl, h⟩
  obtain ⟨r, hr, run, s⟩ := foldl_or (K + 1) "Elixir.Module.Types.Descr" "-apply_disjoint/2-fun-0-" #[dom] E den G
    (P.map fun p => .tuple #[p.1, Term.list p.2.1, p.2.2]) (by
      intro t mt a ha
      obtain ⟨p, mp, rfl⟩ := List.mem_map.mp mt
      obtain ⟨hargs', hret', -⟩ := hP p mp
      obtain ⟨dom', hdom', rdom', sdom'⟩ := fd.dom p.2.1 hargs'
      obtain ⟨i, hi, ri, si⟩ := fd.inter hdom' hdom
      have ei := fd.empty1 hi
      obtain ⟨u, hu, ru, su⟩ := fe.union ha hret'
      by_cases meet : ∃ x, FunSem.InDomR (args.map den) x ∧ FunSem.InDomR (p.2.1.map den) x
      · have hb : bp (∀ x, ¬dden i x) = Bool.false := bp_false.mpr fun h => by
          obtain ⟨x, h₁, h₂⟩ := meet
          exact h x ((si x).mpr ⟨(sdom' x).mpr h₂, (sdom x).mpr h₁⟩)
        refine ⟨u, hu, fun m hm => ?_, fun v => ?_⟩
        · obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
          rw [Erlang.program.«Elixir.Module.Types.Descr:-apply_disjoint/2-fun-0-/2».pure]
          simp [Elixir.Module.Types.Descr.«-apply_disjoint/2-fun-0-/3», rdom', ri m' hm', ei m' hm', hb,
            isMember, ru m' hm']
        · rw [su, G_enc p mp]
          exact or_congr Iff.rfl ⟨fun h => ⟨meet, h⟩, fun h => h.2⟩
      · have hb : bp (∀ x, ¬dden i x) = Bool.true := bp_true.mpr fun x hx => by
          rw [si, sdom, sdom'] at hx
          exact meet ⟨x, hx.2, hx.1⟩
        refine ⟨a, ha, fun m hm => ?_, fun v => ?_⟩
        · obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
          rw [Erlang.program.«Elixir.Module.Types.Descr:-apply_disjoint/2-fun-0-/2».pure]
          simp [Elixir.Module.Types.Descr.«-apply_disjoint/2-fun-0-/3», rdom', ri m' hm', ei m' hm', hb,
            isMember]
        · rw [G_enc p mp]
          exact ⟨Or.inl, fun h => h.elim id fun h => absurd h.1 meet⟩) (.map []) fe.none.1
  refine ⟨r, hr, fun m hm => by
    unfold Elixir.Module.Types.Descr.«apply_disjoint/2»; simp [rdom, encP, run m hm], fun v => ?_⟩
  rw [s]
  simp only [fe.none.2, false_or, List.mem_map, semP]
  constructor
  · rintro ⟨_, ⟨p, mp, rfl⟩, h⟩
    exact ⟨_, ⟨p, mp, rfl⟩, (G_enc p mp v).mp h⟩
  · rintro ⟨_, ⟨p, mp, rfl⟩, h⟩
    exact ⟨_, ⟨p, mp, rfl⟩, (G_enc p mp v).mpr h⟩

/-- Arguments with no row are covered by the domains of the positive arrows. -/
theorem noRow_cover (P : List (FunSem.Arrow V)) (t : List (V → Prop)) (s : V → Prop)
    (h : FunSem.NoRow (t.map (false, ·)) (false, fun v => ¬s v) P) :
    ∀ x, FunSem.InDomR t x → ∃ p ∈ P, FunSem.InDomR p.1 x := by
  intro x hx
  apply Classical.byContradiction
  intro hn
  refine h (x.map some) none ((FunSem.inDom_args t _).mp ((FunSem.inDom_real t x).mpr hx)) rfl fun p mp hd => ?_
  exact absurd ⟨p, mp, (FunSem.inDom_real p.1 x).mp hd⟩ hn

/-- Arguments in disjoint domains, position by position. -/
def DisjDom (a b : FunSem.Arrow V) : Prop := ∀ x, FunSem.InDomR a.1 x → FunSem.InDomR b.1 x → False

theorem disjoint_args_sem (fe : FunElem E den K seen) : ∀ (l₁ l₂ : List Term), (∀ a ∈ l₁, E a) → (∀ a ∈ l₂, E a) →
    l₁.length = l₂.length → ∃ b : Bool,
      (∀ m, K ≤ m → Elixir.Module.Types.Descr.«disjoint_arguments?/2» (D m) (Term.list l₁) (Term.list l₂) =
        .ok (boolAtom b)) ∧
      (b = Bool.true → ∀ x, FunSem.InDomR (l₁.map den) x → FunSem.InDomR (l₂.map den) x → False)
  | [], [], _, _, _ => ⟨Bool.false, fun m _ => by
      unfold Elixir.Module.Types.Descr.«disjoint_arguments?/2»; simp, by simp⟩
  | a :: l₁, b :: l₂, h₁, h₂, len => by
    obtain ⟨d, hd, sd⟩ := fe.disj (h₁ a List.mem_cons_self) (h₂ b List.mem_cons_self)
    obtain ⟨r, hr, sr⟩ := disjoint_args_sem fe l₁ l₂ (fun x m => h₁ x (List.mem_cons_of_mem _ m))
      (fun x m => h₂ x (List.mem_cons_of_mem _ m)) (by simpa using len)
    refine ⟨d || r, fun m hm => ?_, fun hb x hx hy => ?_⟩
    · unfold Elixir.Module.Types.Descr.«disjoint_arguments?/2»
      rw [hd m hm, hr m hm]
      cases d <;> cases r <;> simp [Lynx.Except.orElse, boolAtom]
    · cases x with
      | nil => exact hx.elim
      | cons v x =>
        obtain ⟨hv₁, hx₁⟩ := hx
        obtain ⟨hv₂, hx₂⟩ := hy
        rcases Bool.or_eq_true _ _ |>.mp hb with h | h
        · exact sd h v hv₁ hv₂
        · exact sr h x hx₁ hx₂
  | [], _ :: _, _, _, len => by simp at len
  | _ :: _, [], _, _, len => by simp at len

theorem all_disjoint_sem (fe : FunElem E den K seen) (n : Nat) : ∀ P : List (Term × List Term × Term), PosOk E n P →
    ∃ b : Bool, (∀ m, K + 1 ≤ m →
      Elixir.Module.Types.Descr.«all_disjoint_arguments?/1» (D m) (encP P) = .ok (boolAtom b)) ∧
      (b = Bool.true → List.Pairwise DisjDom (semP den P))
  | [], _ => ⟨Bool.true, fun m _ => by
      unfold Elixir.Module.Types.Descr.«all_disjoint_arguments?/1»; simp [encP, Term.list], fun _ => by simp [semP]⟩
  | p :: rest, hP => by
    obtain ⟨hargs, -, plen⟩ := hP p List.mem_cons_self
    have hrest : PosOk E n rest := fun q mq => hP q (List.mem_cons_of_mem _ mq)
    obtain ⟨b₂, r₂, s₂⟩ := all_disjoint_sem fe n rest hrest
    let res : Term → Bool := fun t => bp (∃ q ∈ rest, t = .tuple #[q.1, Term.list q.2.1, q.2.2] ∧
      ∃ b : Bool, b = Bool.true ∧ ∀ m, K ≤ m → Elixir.Module.Types.Descr.«disjoint_arguments?/2» (D m)
        (Term.list p.2.1) (Term.list q.2.1) = .ok (boolAtom b))
    have each : ∀ q ∈ rest, ∃ b : Bool, (∀ m, K ≤ m → Elixir.Module.Types.Descr.«disjoint_arguments?/2» (D m)
        (Term.list p.2.1) (Term.list q.2.1) = .ok (boolAtom b)) ∧ res (.tuple #[q.1, Term.list q.2.1, q.2.2]) = b ∧
        (b = Bool.true → DisjDom (p.2.1.map den, den p.2.2) (q.2.1.map den, den q.2.2)) := by
      intro q mq
      obtain ⟨hargs', -, qlen⟩ := hrest q mq
      obtain ⟨b, hb, sb⟩ := disjoint_args_sem fe p.2.1 q.2.1 hargs hargs' (by omega)
      refine ⟨b, hb, ?_, fun h x hx hy => sb h x hx hy⟩
      cases b
      · refine bp_false.mpr fun ⟨q', mq', e, b', hb', run⟩ => ?_
        obtain ⟨-, el, -⟩ := enc_inj e
        rw [← el] at run
        have := (run K (Nat.le_refl _)).symm.trans (hb K (Nat.le_refl _))
        subst hb'
        simp [boolAtom] at this
      · exact bp_true.mpr ⟨q, mq, rfl, Bool.true, rfl, hb⟩
    let b₁ := (rest.map fun q => Term.tuple #[q.1, Term.list q.2.1, q.2.2]).all res
    refine ⟨b₁ && b₂, fun m hm => ?_, fun hb => ?_⟩
    · obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
      have run₁ := all_list (D (m' + 1)) "Elixir.Module.Types.Descr" "-all_disjoint_arguments?/1-fun-0-"
        #[Term.list p.2.1] res (rest.map fun q => Term.tuple #[q.1, Term.list q.2.1, q.2.2]) (by
          intro t mt
          obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mt
          obtain ⟨b, hb, rb, -⟩ := each q mq
          rw [Erlang.program.«Elixir.Module.Types.Descr:-all_disjoint_arguments?/1-fun-0-/1».pure, rb]
          simp only [Elixir.Module.Types.Descr.«-all_disjoint_arguments?/1-fun-0-/2»]
          exact hb m' hm')
      unfold Elixir.Module.Types.Descr.«all_disjoint_arguments?/1»
      simp only [encP, List.map_cons, Term.list] at run₁ r₂ ⊢
      simp only [pure_bind, run₁, r₂ (m' + 1) hm, andAlso_bool]; rfl
    · obtain ⟨h₁, h₂⟩ := Bool.and_eq_true _ _ |>.mp hb
      simp only [semP, List.map_cons, List.pairwise_cons]
      refine ⟨fun a ma => ?_, s₂ h₂⟩
      obtain ⟨q, mq, rfl⟩ := List.mem_map.mp ma
      obtain ⟨b, -, rb, sb⟩ := each q mq
      have : res (.tuple #[q.1, Term.list q.2.1, q.2.2]) = Bool.true :=
        List.all_eq_true.mp h₁ _ (List.mem_map.mpr ⟨q, mq, rfl⟩)
      rw [rb] at this
      exact sb this

theorem nonempty_args_sem (fe : FunElem E den K seen) (args : List Term) (hargs : ∀ a ∈ args, E a)
    (name : String) (lam : ∀ d a, (D (d + 1)).pure (.function "Elixir.Module.Types.Descr" name 1 #[seen]) #[a] =
      (do let e ← Elixir.Module.Types.Descr.«empty_seen?/2» (D d) a seen; Erlang.erlang.«not/1» e))
    {m : Nat} (hm : K + 1 ≤ m) :
    Erlang.lists.«all/2» (D m) (.function "Elixir.Module.Types.Descr" name 1 #[seen]) (Term.list args) =
      .ok (boolAtom (bp (∀ a ∈ args, ∃ v, den a v))) := by
  obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
  have run := all_list (D (m' + 1)) "Elixir.Module.Types.Descr" name #[seen] (fun a => !isEmpty den a) args
    (fun a ma => by
      rw [lam, fe.phi.empty (hargs a ma) m' hm']
      cases isEmpty den a <;> rfl)
  rw [run]
  congr 2
  cases h : args.all (fun a => !isEmpty den a)
  · symm; refine bp_false.mpr fun hall => ?_
    obtain ⟨a, ma, ha⟩ := List.all_eq_false.mp h
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at ha
    obtain ⟨v, hv⟩ := hall a ma
    exact absurd hv ((isEmpty_iff den a).mp (by simpa using ha) v)
  · symm; refine bp_true.mpr fun a ma => ?_
    have := List.all_eq_true.mp h a ma
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at this
    apply Classical.byContradiction
    intro hn
    have : isEmpty den a = Bool.true := (isEmpty_iff den a).mpr fun v hv => hn ⟨v, hv⟩
    simp_all

/-- `disjoint_non_empty_domains?/3` takes a shortcut only when the arguments are not empty, and the disjoint one
only when the domains of the positive arrows are disjoint. -/
theorem domains_sem (fe : FunElem E den K seen) (n : Nat) (args : List Term) (hargs : ∀ a ∈ args, E a)
    (P : List (Term × List Term × Term)) (hP : PosOk E n P) :
    ∃ v, (∀ m, K + 2 ≤ m →
      Elixir.Module.Types.Descr.«disjoint_non_empty_domains?/3» (D m) (Term.list args) (encP P) seen = .ok v) ∧
      (v = .atom "nil" ∨ ((∀ a ∈ args, ∃ x, den a x) ∧
        (v = .atom "non_empty" ∨ (v = .atom "disjoint_non_empty" ∧ List.Pairwise DisjDom (semP den P))))) := by
  let a₁ := bp (∀ a ∈ args, ∃ v, den a v)
  have h₁ : ∀ m, K + 1 ≤ m → Erlang.lists.«all/2» (D m)
      (.function "Elixir.Module.Types.Descr" "-disjoint_non_empty_domains?/3-fun-0-" 1 #[seen]) (Term.list args) =
      .ok (boolAtom a₁) := fun m hm => nonempty_args_sem fe args hargs _ (fun d a => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-disjoint_non_empty_domains?/3-fun-0-/1».pure]; rfl) hm
  obtain ⟨a₂, h₂⟩ := all_uni (K + 2) "Elixir.Module.Types.Descr" "-all_non_empty_arguments?/2-fun-1-" #[seen]
    (P.map fun p => .tuple #[p.1, Term.list p.2.1, p.2.2]) (fun t mt => by
      obtain ⟨p, mp, rfl⟩ := List.mem_map.mp mt
      obtain ⟨hargs', -, -⟩ := hP p mp
      refine ⟨bp (∀ a ∈ p.2.1, ∃ v, den a v), fun m hm => ?_⟩
      obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
      dsimp only
      rw [Erlang.program.«Elixir.Module.Types.Descr:-all_non_empty_arguments?/2-fun-1-/1».pure]
      simp only [Elixir.Module.Types.Descr.«-all_non_empty_arguments?/2-fun-1-/2»]
      exact nonempty_args_sem fe p.2.1 hargs' _ (fun d a => by
        rw [Erlang.program.«Elixir.Module.Types.Descr:-all_non_empty_arguments?/2-fun-0-/1».pure]; rfl) (by omega))
  obtain ⟨dj, hdj, sdj⟩ := all_disjoint_sem fe n P hP
  refine ⟨if a₁ && a₂ then (if dj then .atom "disjoint_non_empty" else .atom "non_empty") else .atom "nil",
    fun m hm => ?_, ?_⟩
  · have e₁ := h₁ m (by omega)
    have e₂ := h₂ m hm
    have e₃ := hdj m (by omega)
    dsimp only at e₂
    unfold Elixir.Module.Types.Descr.«disjoint_non_empty_domains?/3»
    simp only [Elixir.Module.Types.Descr.«all_non_empty_arguments?/2», pure_bind, e₁, encP, e₂, andAlso_bool]
    simp only [encP] at e₃
    cases a₁ <;> cases a₂ <;> cases dj <;>
      simp [e₃, Lynx.Except.andAlso, Erlang.erlang.«/=/2», boolAtom]
  · by_cases ha : (a₁ && a₂) = Bool.true
    · have ne : ∀ a ∈ args, ∃ x, den a x := bp_true.mp (Bool.and_eq_true _ _ |>.mp ha).1
      rw [ite_eq_left ha]
      cases dj
      · exact Or.inr ⟨ne, Or.inl rfl⟩
      · exact Or.inr ⟨ne, Or.inr ⟨rfl, sdj rfl⟩⟩
    · have ha' : (a₁ && a₂) = Bool.false := by simpa using ha
      simp [ha']

/-- `phi_starter/4` decides whether the positive arrows are in the arrow from `args` to `ret`, when the domains of
the positive arrows cover the arguments: by `phi/5`, or by its shortcuts. -/
theorem phi_starter_sem (fe : FunElem E den K seen) (fd : FunDom Dm E den dden K seen) (n : Nat) (args : List Term)
    (hargs : ∀ a ∈ args, E a) (len : args.length = n) {ret : Term} (hret : E ret) (P : List (Term × List Term × Term))
    (hP : PosOk E n P) :
    ∃ b : Bool, (∀ m, K + 2 ≤ m →
      Elixir.Module.Types.Descr.«phi_starter/4» (D m) (Term.list args) ret (encP P) seen = .ok (boolAtom b)) ∧
      ((∀ x, FunSem.InDomR (args.map den) x → ∃ p ∈ semP den P, FunSem.InDomR p.1 x) →
        (b = Bool.true ↔ FunSem.NoRow ((args.map den).map (Bool.false, ·)) (Bool.false, fun v => ¬den ret v) (semP den P))) := by
  obtain ⟨v, rv, hv⟩ := domains_sem fe n args hargs P hP
  have lP : ∀ p ∈ semP den P, p.1.length = ((args.map den).map (Bool.false, ·)).length := by
    intro p mp
    obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mp
    simp [(hP q mq).2.2, len]
  rcases hv with rfl | ⟨ne, rfl | ⟨rfl, disj⟩⟩
  · obtain ⟨neg, hneg, rneg, sneg⟩ := fe.neg hret
    have margs : ∀ m, Erlang.lists.«map/2» (D m) (.function "Elixir.Module.Types.Descr" "-phi_starter/4-fun-0-" 1 #[])
        (Term.list args) = .ok (encA (args.map fun x => (Bool.false, x))) := fun m => by
      have := map_list (D m) "Elixir.Module.Types.Descr" "-phi_starter/4-fun-0-" #[]
        (fun x => .tuple #[boolAtom Bool.false, x]) args fun x _ => by
          rw [Erlang.program.«Elixir.Module.Types.Descr:-phi_starter/4-fun-0-/1».pure]; rfl
      rw [this]; simp only [encA, List.map_map]; rfl
    obtain ⟨b, c, run, sb, -⟩ := phi_run fe.phi (m := K + 2) (by omega) P hP (args.map fun x => (Bool.false, x))
      (Bool.false, neg) (.map []) (by simpa using hargs) (by simpa using len) hneg (cacheOk_nil E den n)
    have dneg : den neg = fun v => ¬den ret v := funext fun v => propext (sneg v)
    have sem : FunSem.phiS (semA den (args.map fun x => (Bool.false, x))) (semR den (Bool.false, neg)) (semP den P) ↔
        FunSem.NoRow ((args.map den).map (Bool.false, ·)) (Bool.false, fun v => ¬den ret v) (semP den P) := by
      have e : semA den (args.map fun x => (Bool.false, x)) = (args.map den).map (Bool.false, ·) := by simp [semA]
      rw [e, semR, dneg]
      exact FunSem.phiS_iff _ _ _ lP
    refine ⟨b, fun m hm => ?_, fun _ => sb.trans sem⟩
    obtain ⟨b', c', run', sb', -⟩ := phi_run fe.phi (m := m) (by omega) P hP (args.map fun x => (Bool.false, x))
      (Bool.false, neg) (.map []) (by simpa using hargs) (by simpa using len) hneg (cacheOk_nil E den n)
    have bb : b' = b := by
      cases b <;> cases b' <;> simp_all
    subst bb
    unfold Elixir.Module.Types.Descr.«phi_starter/4»
    simp only [encR, boolAtom_false] at run'
    simp [rv m hm, margs, rneg m (by omega), run']
  · obtain ⟨w, hw⟩ := inDomR_exists (args.map den) fun t mt => by
      obtain ⟨a, ma, rfl⟩ := List.mem_map.mp mt; exact ne a ma
    obtain ⟨r, hr, ra, sr⟩ := apply_static_sem fe n args hargs ne len P hP
    refine ⟨bp (∀ v, den r v → den ret v), fun m hm => ?_, fun cover => ?_⟩
    · unfold Elixir.Module.Types.Descr.«phi_starter/4»
      simp [rv m hm, ra m (by omega), fe.sub hr hret m (by omega)]
    · rw [bp_true, FunSem.noRow_app _ _ _ w hw cover]
      exact forall_congr' fun v => imp_congr_left (sr v)
  · obtain ⟨w, hw⟩ := inDomR_exists (args.map den) fun t mt => by
      obtain ⟨a, ma, rfl⟩ := List.mem_map.mp mt; exact ne a ma
    obtain ⟨r, hr, ra, sr⟩ := apply_disjoint_sem fe fd n args hargs P hP
    refine ⟨bp (∀ v, den r v → den ret v), fun m hm => ?_, fun cover => ?_⟩
    · unfold Elixir.Module.Types.Descr.«phi_starter/4»
      simp [rv m hm, ra m (by omega), fe.sub hr hret m (by omega)]
    · have dj : ∀ i j (hi : i < (semP den P).length) (hj : j < (semP den P).length), i ≠ j →
          ∀ x, FunSem.InDomR (semP den P)[i].1 x → ¬FunSem.InDomR (semP den P)[j].1 x := by
        intro i j hi hj ne x h₁ h₂
        have pw := List.pairwise_iff_getElem.mp disj
        rcases Nat.lt_or_gt_of_ne ne with lt | lt
        · exact pw i j hi hj lt x h₁ h₂
        · exact pw j i hj hi lt x h₂ h₁
      rw [bp_true, FunSem.noRow_app _ _ _ w hw cover,
        FunSem.app_disjoint _ _ ⟨w, hw⟩ dj cover]
      constructor
      · intro h p mp hx v hv
        exact h v ((sr v).mpr ⟨p, mp, hx, hv⟩)
      · intro h v hv
        obtain ⟨p, mp, hx, hp⟩ := (sr v).mp hv
        exact h p mp hx v hp

/-- The negative arrows a line of positive arrows `P` is contained in, as `phi` sees them. -/
def NegIn (_n : Nat) (den : Term → V → Prop) (P : List (Term × List Term × Term)) (q : Term × List Term × Term) : Prop :=
  FunSem.NoRow ((q.2.1.map den).map (Bool.false, ·)) (Bool.false, fun v => ¬den q.2.2 v) (semP den P)

/-- Lines with positive arrows: the line is empty exactly when some negative arrow contains the positive ones. -/
theorem fun_line_pos_sem (fe : FunElem E den K seen) (fd : FunDom Dm E den dden K seen) (n : Nat)
    (P N : List (Term × List Term × Term)) (hP : PosOk E n P) (hN : PosOk E n N) (ne : P ≠ []) :
    ∃ b : Bool, (∀ m, K + 3 ≤ m →
      Elixir.Module.Types.Descr.«fun_line_empty?/3» (D m) (encP P) (encP N) seen = .ok (boolAtom b)) ∧
      (b = Bool.true ↔ ∃ q ∈ N, NegIn n den P q) := by
  obtain ⟨fdom, hfdom, rfdom, sfdom⟩ := fetch_domain_sem fd n P hP
  let res : Term → Bool := fun t => bp (∃ q ∈ N, t = .tuple #[q.1, Term.list q.2.1, q.2.2] ∧ NegIn n den P q)
  have each : ∀ q ∈ N, res (.tuple #[q.1, Term.list q.2.1, q.2.2]) = bp (NegIn n den P q) ∧ ∀ m, K + 2 ≤ m →
      (Elixir.Module.Types.Descr.«-fun_line_empty?/3-fun-1-/3» (D m) (encP P) seen
        (.tuple #[q.1, Term.list q.2.1, q.2.2])) = .ok (boolAtom (bp (NegIn n den P q))) := by
    intro q mq
    refine ⟨bp_congr ⟨fun ⟨q', mq', e, h⟩ => ?_, fun h => ⟨q, mq, rfl, h⟩⟩, fun m hm => ?_⟩
    · obtain ⟨-, el, er⟩ := enc_inj e
      simp only [NegIn] at h ⊢
      rw [el, er]; exact h
    obtain ⟨hargs, hret, len⟩ := hN q mq
    obtain ⟨dom, hdom, rdom, sdom⟩ := fd.dom q.2.1 hargs
    obtain ⟨c, hc, rc, sc⟩ := fd.diff hdom hfdom
    obtain ⟨b, rb, sb⟩ := phi_starter_sem fe fd n q.2.1 hargs len hret P hP
    have cover : bp (∀ x, ¬dden c x) = Bool.true ↔
        ∀ x, FunSem.InDomR (q.2.1.map den) x → ∃ p ∈ semP den P, FunSem.InDomR p.1 x := by
      rw [bp_true]
      refine forall_congr' fun x => ?_
      rw [sc, sdom, sfdom]
      constructor
      · intro h hx; apply Classical.byContradiction; exact fun hn => h ⟨hx, hn⟩
      · exact fun h ⟨hx, hn⟩ => hn (h hx)
    simp only [Elixir.Module.Types.Descr.«-fun_line_empty?/3-fun-1-/3», rdom, rfdom m (by omega),
      Elixir.Module.Types.Descr.«subtype_seen?/3», rc m (by omega), fd.emptySeen hc m (by omega), rb m hm,
      Lynx.Except.ok_bind, andAlso_bool]
    congr 2
    cases hcv : bp (∀ x, ¬dden c x)
    · symm; refine bp_false.mpr fun h => ?_
      have := cover.mpr (noRow_cover _ _ _ h)
      rw [hcv] at this; cases this
    · have cv := cover.mp hcv
      cases hb : b
      · symm; exact bp_false.mpr fun h => by have := (sb cv).mpr h; rw [hb] at this; cases this
      · symm; exact bp_true.mpr ((sb cv).mp hb)
  have run : ∀ m, K + 3 ≤ m → Erlang.lists.«any/2» (D m)
      (.function "Elixir.Module.Types.Descr" "-fun_line_empty?/3-fun-1-" 1 #[encP P, seen])
      (Term.list (N.map fun q => .tuple #[q.1, Term.list q.2.1, q.2.2])) =
      .ok (boolAtom ((N.map fun q => Term.tuple #[q.1, Term.list q.2.1, q.2.2]).any res)) := fun m hm => by
    obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
    refine any_list _ _ _ _ res _ fun t mt => ?_
    obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mt
    rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_line_empty?/3-fun-1-/1».pure, (each q mq).2 m' hm',
      (each q mq).1]
  refine ⟨(N.map fun q => Term.tuple #[q.1, Term.list q.2.1, q.2.2]).any res, fun m hm => ?_, ?_⟩
  · obtain ⟨p, rest, rfl⟩ := List.exists_cons_of_ne_nil ne
    rw [Elixir.Module.Types.Descr.«fun_line_empty?/3».eq_def]
    have r := run m hm
    simp only [encP, List.map_cons, Term.list] at r ⊢
    simp only [pure_bind]
    exact r
  · rw [List.any_eq_true]
    constructor
    · rintro ⟨t, mt, ht⟩
      obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mt
      rw [(each q mq).1, bp_true] at ht
      exact ⟨q, mq, ht⟩
    · rintro ⟨q, mq, h⟩
      exact ⟨_, List.mem_map.mpr ⟨q, mq, rfl⟩, by rw [(each q mq).1, bp_true]; exact h⟩

theorem lineEmpty_negIn (n : Nat) (P N : List (Term × List Term × Term)) (hP : PosOk E n P) (hN : PosOk E n N)
    (ne : P ≠ []) : FunSem.LineEmpty n (semP den P) (semP den N) ↔ ∃ q ∈ N, NegIn n den P q := by
  have lP : ∀ p ∈ semP den P, p.1.length = n := by
    intro p mp
    obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mp
    simp [(hP q mq).2.2]
  rw [FunSem.lineEmpty_iff]
  constructor
  · rintro ⟨q', mq', h⟩
    obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mq'
    have lt : (q.2.1.map den).length = n := by simp [(hN q mq).2.2]
    refine ⟨q, mq, ?_⟩
    have := (FunSem.neg_iff_phi n _ (by simpa [semP] using ne) lP _ _ lt).mp h
    exact (FunSem.phiS_iff _ _ _ (fun p mp => by rw [lP p mp]; simp [(hN q mq).2.2])).mp this
  · rintro ⟨q, mq, h⟩
    have lt : (q.2.1.map den).length = n := by simp [(hN q mq).2.2]
    refine ⟨_, List.mem_map.mpr ⟨q, mq, rfl⟩, ?_⟩
    refine (FunSem.neg_iff_phi n _ (by simpa [semP] using ne) lP _ _ lt).mpr ?_
    exact (FunSem.phiS_iff _ _ _ (fun p mp => by rw [lP p mp]; simp [(hN q mq).2.2])).mpr h

/-- `fun_line_empty?/3` decides whether a line of arrows of arity `n` is empty, from call depth `K + 3`. -/
theorem fun_line_sem (fe : FunElem E den K seen) (fd : FunDom Dm E den dden K seen) (n : Nat)
    (P N : List (Term × List Term × Term)) (hP : PosOk E n P) (hN : PosOk E n N) :
    ∃ b : Bool, (∀ m, K + 3 ≤ m →
      Elixir.Module.Types.Descr.«fun_line_empty?/3» (D m) (encP P) (encP N) seen = .ok (boolAtom b)) ∧
      (b = Bool.true ↔ FunSem.LineEmpty n (semP den P) (semP den N)) := by
  by_cases ne : P ≠ []
  · obtain ⟨b, rb, sb⟩ := fun_line_pos_sem fe fd n P N hP hN ne
    exact ⟨b, rb, sb.trans (lineEmpty_negIn n P N hP hN ne).symm⟩
  simp only [ne_eq, Decidable.not_not] at ne
  subst ne
  cases N with
  | nil =>
    refine ⟨Bool.false, fun m _ => ?_, ?_⟩
    · rw [Elixir.Module.Types.Descr.«fun_line_empty?/3».eq_def]; simp [encP, Term.list]
    · simp only [semP, List.map_nil]
      exact ⟨fun h => (by cases h), fun h => absurd h (FunSem.lineEmpty_nil n)⟩
  | cons q qs =>
    obtain ⟨hargs, -, len⟩ := hN q List.mem_cons_self
    obtain ⟨kt, leaf⟩ := leaf_fun (q.2.1.map fun _ => .map [])
    let top : Term × List Term × Term := (.integer kt, q.2.1.map fun _ => .map [], .atom "term")
    have hT : PosOk E n [top] := fun t mt => by
      rw [List.mem_singleton.mp mt]
      exact ⟨fun a ma => by obtain ⟨_, _, rfl⟩ := List.mem_map.mp ma; exact fe.none.1, fe.term.1, by simp [top, len]⟩
    obtain ⟨b, rb, sb⟩ := fun_line_pos_sem fe fd n [top] (q :: qs) hT hN (by simp)
    have margs : ∀ m, Erlang.lists.«map/2» (D m) (.function "Elixir.Module.Types.Descr" "-fun_line_empty?/3-fun-0-" 1 #[])
        (Term.list q.2.1) = .ok (Term.list (q.2.1.map fun _ => .map [])) := fun m =>
      map_list (D m) _ _ _ _ _ fun x _ => by
        rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_line_empty?/3-fun-0-/1».pure]; rfl
    have semT : semP den [top] = [FunSem.top n] := by
      simp only [semP, List.map_cons, List.map_nil, List.map_map, FunSem.top, top]
      have e₁ : (den ∘ fun _ : Term => Term.map []) = fun _ => fun _ => False :=
        funext fun _ => funext fun v => propext (iff_false_intro (fe.none.2 v))
      have e₂ : den (.atom "term") = fun _ => True := funext fun v => propext (iff_true_intro (fe.term.2 v))
      rw [e₁, e₂, List.map_const', len]
    refine ⟨b, fun m hm => ?_, ?_⟩
    · have r := rb m hm
      rw [Elixir.Module.Types.Descr.«fun_line_empty?/3».eq_def]
      simp only [encP, List.map_cons, List.map_nil, Term.list, top] at r ⊢
      simp [margs, leaf]
      exact r
    · rw [sb, ← lineEmpty_negIn n [top] (q :: qs) hT hN (by simp), semT]
      simp only [semP, List.map_nil]
      exact (FunSem.lineEmpty_top n _).symm

end

end Elixir.STTDescrProofsTest.Nest
