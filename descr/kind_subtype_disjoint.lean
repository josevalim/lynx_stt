namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Subtyping and disjointness of types over the structural kinds. -/

section
variable {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop} {FV : Term → (Term → Bool) → Prop}
  {FS : List (Term × Term) → Prop}
  {H : Prop}

/-- A checked field is included in the other type's field. -/
theorem keySub_sound (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) (hH : H) (hS : FS []) {m : Nat} (hm : K + 2 ≤ m)
    {B : List (Term × Term)} (sB : DescrC Fn TF LF MF B) {name : String} {x : Term} (fx : FieldC Fn TF LF MF name x)
    (h : KeySub (D m) B (.atom name) x) (p : Point) (ok : PtOkC TV LV MV FV name p) (hx : dn name (some x) p = Bool.true) :
    dn name (mapLookup B (.atom name)) p = Bool.true := by
  rcases h with ⟨y, w, hy, run, e⟩ | ⟨hy, e⟩
  · obtain ⟨w', run', k, sem⟩ := fieldC_diff ks fc hm fx (sB.fields name y hy)
    rw [run] at run'; cases run'
    have hd := sem p ok
    rw [hy]
    have gone : dn name (keptO name w) p = Bool.false := by
      cases kw : kept (.atom name, w)
      · rw [keptO_false kw, dn_none]
      · rw [keptO_true kw]
        rcases e with rfl | rfl | e
        · simp [kept] at kw
        · simp [kept] at kw
        · obtain ⟨fw, -⟩ := k kw
          obtain ⟨b, rb, ex⟩ := fieldC_empty ks fc hH (show K ≤ m by omega) fw [] (fun _ => hS)
          have hb : b = Bool.true := by
            have := rb.symm.trans e; cases b <;> simp_all [boolAtom]
          exact (ex (lh w + 1) (by omega) (safeN_nil _)).2 hb p ok
    rw [gone, hx] at hd
    cases hdy : dn name (some y) p
    · rw [hdy] at hd; simp at hd
    · rfl
  · exfalso
    rcases fieldC_cases fx with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [Elixir.Module.Types.Descr.«empty_key?/3»] at e
    all_goals
      obtain ⟨b, rb, ex⟩ := fieldC_empty ks fc hH (show K ≤ m by omega) fx [] (fun _ => hS)
      have hb : b = Bool.true := by
        have := rb.symm.trans e; cases b <;> simp_all [boolAtom]
      have := (ex (lh x + 1) (by omega) (safeN_nil _)).2 hb p ok
      rw [hx] at this; cases this

/-- `subtype?/2` answers `true` only on included types. -/
theorem descr_sub_sound (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) (hH : H) (hS : FS []) {m : Nat}
    (hm : K + 2 ≤ m) {A B : List (Term × Term)} (sA : DescrC Fn TF LF MF A) (sB : DescrC Fn TF LF MF B)
    (h : Elixir.Module.Types.Descr.«subtype?/2» (D m) (.map A) (.map B) = .ok (.atom "true")) :
    ∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup A (.atom name)) p = Bool.true →
      dn name (mapLookup B (.atom name)) p = Bool.true := by
  have stA := sA.static
  have stB := sB.static
  unfold Elixir.Module.Types.Descr.«subtype?/2» at h
  simp [unfold_map, Erlang.erlang.«is_map_key/2», stA, stB, any_key, Lynx.Except.andAlso,
    Erlang.erlang.«/=/2»] at h
  unfold Elixir.Module.Types.Descr.«subtype_static?/2» at h
  by_cases same : compareExact (fuel (.map B) (.map A)) (.map B) (.map A) = .eq
  · intro name p ok hx
    rw [← descr_congr ks fc sA sB (Lynx.Term.compare_eq_symm (compare_eq_of_compareExact_eq _ _ same)) name p ok]
    exact hx
  · simp [Erlang.erlang.«=:=/2», same, Elixir.Module.Types.Descr.«empty_difference_subtype?/2»] at h
    rw [Elixir.Module.Types.Descr.«empty_difference_subtype?/3».eq_def] at h
    simp [getMapKeys_single, stA, Erlang.maps.«iterator/1»] at h
    have walk := iterator_sound (D m) B (mapEntries A) h
    intro name p ok hx
    cases hA : mapLookup A (.atom name) with
    | none => rw [hA, dn_none] at hx; cases hx
    | some x =>
      rw [hA] at hx
      obtain ⟨e, me, qe, ex⟩ := lookup_entry hA
      have e1 : e.1 = .atom name := by
        have := Lynx.Term.compareExact_eq_symm qe
        simpa using this
      have := walk e me
      rw [e1, ex] at this
      exact keySub_sound ks fc hH hS hm sB (sA.fields name x hA) this p ok hx

/-- `subtype?/2` answers `true` on included types. -/
theorem descr_sub_complete (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) (hS : FS []) {m : Nat}
    (hm : K + 2 ≤ m) {A B : List (Term × Term)} (sA : DescrC Fn TF LF MF A) (sB : DescrC Fn TF LF MF B)
    (incl : ∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup A (.atom name)) p = Bool.true →
      dn name (mapLookup B (.atom name)) p = Bool.true) :
    Elixir.Module.Types.Descr.«subtype?/2» (D m) (.map A) (.map B) = .ok (.atom "true") := by
  refine subtype_keys (D m) A B sA.static sB.static fun e me => ?_
  have hx := mapLookup_of_mem_mapEntries me
  obtain ⟨name, -, key⟩ := sA.keys e.1 (by simp [hx])
  rw [key] at hx ⊢
  have fx := sA.fields name e.2 hx
  have none : ∀ w, FieldC Fn TF LF MF name w →
      (∀ p, PtOkC TV LV MV FV name p → dn name (some w) p = Bool.false) →
      Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom name) w (.map []) = .ok (.atom "true") := by
    intro w fw empty
    exact fieldC_empty_none ks fc (show K ≤ m by omega) fw (fun _ => hS) empty
  cases hy : mapLookup B (.atom name) with
  | none =>
    refine Or.inr ⟨hy, none _ fx fun p ok => ?_⟩
    cases h : dn name (some e.2) p
    · rfl
    · have := incl name p ok (by rw [hx]; exact h)
      rw [hy, dn_none] at this; cases this
  | some y =>
    obtain ⟨w, run, k, sem⟩ := fieldC_diff ks fc hm fx (sB.fields name y hy)
    refine Or.inl ⟨y, w, hy, run, ?_⟩
    cases kw : kept (.atom name, w)
    · rcases kept_of_ne kw with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr (none w (k kw).1 fun p ok => ?_))
      have := sem p ok
      rw [keptO_true kw] at this
      rw [this]
      cases h : dn name (some e.2) p
      · rfl
      · have := incl name p ok (by rw [hx]; exact h)
        rw [hy] at this; simp [this]

/-- Walks that find no common field leave only intersections that drop their field or are checked empty. -/
theorem iter_disj_gen (K' : Nat) (B : List (Term × Term)) (Sm : Term) :
    ∀ es : List (Term × Term), (∀ e ∈ es, ∀ y d', K' ≤ d' → mapLookup B e.1 = some y → ∃ w,
      Elixir.Module.Types.Descr.«bare_intersection/3» (D d') e.1 e.2 y = .ok w ∧ (kept (e.1, w) = Bool.true →
        ∃ b : Bool, Elixir.Module.Types.Descr.«empty_key?/3» (D d') e.1 w Sm = .ok (boolAtom b))) →
    ∀ m, K' + es.length ≤ m →
      (do
        let it ← Erlang.maps.«next/1» (Term.list (es.map fun (e : Term × Term) => .tuple #[e.1, e.2]))
        Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/3» (D m) it (.map B) Sm) = .ok (.atom "false") →
      ∀ e ∈ es, ∀ y, mapLookup B e.1 = some y → ∃ d', K' ≤ d' ∧ ∃ w,
        Elixir.Module.Types.Descr.«bare_intersection/3» (D d') e.1 e.2 y = .ok w ∧
        (kept (e.1, w) = Bool.false ∨ Elixir.Module.Types.Descr.«empty_key?/3» (D d') e.1 w Sm = .ok (.atom "true")) := by
  intro es
  induction es with
  | nil => intro _ _ _ _ e m; simp at m
  | cons e rest ih =>
    intro calls m hm h
    have calls' := fun e' (me' : e' ∈ rest) => calls e' (List.mem_cons_of_mem _ me')
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp at hm; omega⟩
    have hm' : K' + rest.length ≤ m := by simp at hm; omega
    have cont : ∀ x, (D (m + 1)).pure (.function false "Elixir.Module.Types.Descr"
        "-iterator_non_disjoint_intersection?/3-fun-0-" 1
        #[Term.list (rest.map fun (e : Term × Term) => .tuple #[e.1, e.2]), .map B, Sm]) #[x] =
        (do
          let it ← Erlang.maps.«next/1» (Term.list (rest.map fun (e : Term × Term) => .tuple #[e.1, e.2]))
          Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/3» (D m) it (.map B) Sm) := by
      intro x
      rw [Erlang.program.«Elixir.Module.Types.Descr:-iterator_non_disjoint_intersection?/3-fun-0-/1».pure]
      simp [Elixir.Module.Types.Descr.«-iterator_non_disjoint_intersection?/3-fun-0-/4»]
    cases hb : mapLookup B e.1 with
    | none =>
      have hrest : (do
          let it ← Erlang.maps.«next/1» (Term.list (rest.map fun (e : Term × Term) => .tuple #[e.1, e.2]))
          Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/3» (D m) it (.map B) Sm) = .ok (.atom "false") := by
        rw [← h]
        simp only [List.map, Term.list, next_cons, Lynx.Except.ok_bind]
        rw [Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/3».eq_def]
        simp [getMapKeys_single, hb, cont]
      intro e' me' y hy
      rcases List.mem_cons.mp me' with rfl | me'
      · rw [hb] at hy; cases hy
      · exact ih calls' m hm' hrest e' me' y hy
    | some y₀ =>
      obtain ⟨w, rw', hb''⟩ := calls e List.mem_cons_self y₀ (m + 1) (by simp at hm; omega) hb
      have k₀ : kept (e.1, w) = Bool.false ∨
          Elixir.Module.Types.Descr.«empty_key?/3» (D (m + 1)) e.1 w Sm = .ok (boolAtom Bool.true) := by
        cases k : kept (e.1, w)
        · exact Or.inl rfl
        · right
          obtain ⟨b, hb'⟩ := hb'' k
          rw [hb']
          cases b
          · exfalso
            have ⟨z, b0⟩ : compareExact (fuel w (.integer 0)) w (.integer 0) ≠ .eq ∧ compareExact (fuel w (.atom "bdd_bot")) w (.atom "bdd_bot") ≠ .eq := by
              simpa [kept] using k
            revert h
            simp only [List.map, Term.list, next_cons, Lynx.Except.ok_bind]
            rw [Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/3».eq_def]
            simp [getMapKeys_single, hb, rw', z, b0, hb',
              Erlang.erlang.«=:=/2», isMember, boolAtom]
          · rfl
      have hrest : (do
          let it ← Erlang.maps.«next/1» (Term.list (rest.map fun (e : Term × Term) => .tuple #[e.1, e.2]))
          Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/3» (D m) it (.map B) Sm) = .ok (.atom "false") := by
        rw [← h]
        simp only [List.map, Term.list, next_cons, Lynx.Except.ok_bind]
        rw [Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/3».eq_def]
        rcases k₀ with k | hb'
        · rcases dropped k with e₀ | e₀ <;> rw [e₀] at rw' <;>
            simp [getMapKeys_single, hb, rw', Erlang.erlang.«=:=/2», cont,
              isMember]
        · by_cases dz : (compareExact (fuel w (.integer 0)) w (.integer 0) = .eq ∨ compareExact (fuel w (.atom "bdd_bot")) w (.atom "bdd_bot") = .eq)
          · rcases dz with dz | dz <;>
              simp [getMapKeys_single, hb, rw', Erlang.erlang.«=:=/2», cont,
                isMember, dz]
          · simp only [not_or] at dz
            simp [getMapKeys_single, hb, rw', Erlang.erlang.«=:=/2», cont,
              isMember, dz.1, dz.2, hb', boolAtom]
      intro e' me' y hy
      rcases List.mem_cons.mp me' with rfl | me'
      · rw [hb] at hy; cases hy
        refine ⟨m + 1, by simp at hm; omega, w, rw', ?_⟩
        rcases k₀ with k | hb'
        · exact Or.inl k
        · exact Or.inr (by simpa [boolAtom] using hb')
      · exact ih calls' m hm' hrest e' me' y hy

theorem descrC_six {X : List (Term × Term)} (sX : DescrC Fn TF LF MF X) : (mapEntries X).length ≤ 6 :=
  entries_le_six fun q h => by
    obtain ⟨name, m, rfl⟩ := sX.keys q h
    rcases names_mem m with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- Fields the disjointness walk leaves share no point. -/
theorem walk_disj_sem (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) (hH : H) {S : List (Term × Term)}
    (hS : FS S) {N : Nat} (safe : SafeN N S)
    {X Y : List (Term × Term)} (sX : DescrC Fn TF LF MF X) (sY : DescrC Fn TF LF MF Y) (lX : lh (.map X) < N)
    (lY : lh (.map Y) < N)
    (walk : ∀ e ∈ mapEntries X, ∀ y, mapLookup Y e.1 = some y → ∃ d', K + 1 ≤ d' ∧ ∃ w,
      Elixir.Module.Types.Descr.«bare_intersection/3» (D d') e.1 e.2 y = .ok w ∧
      (kept (e.1, w) = Bool.false ∨ Elixir.Module.Types.Descr.«empty_key?/3» (D d') e.1 w (.map S) = .ok (.atom "true")))
    (name : String) (p : Point) (ok : PtOkC TV LV MV FV name p) :
    (dn name (mapLookup X (.atom name)) p && dn name (mapLookup Y (.atom name)) p) = Bool.false := by
  cases hx : mapLookup X (.atom name) with
  | none => simp [dn_none]
  | some x =>
    cases hy : mapLookup Y (.atom name) with
    | none => simp [dn_none]
    | some y =>
      obtain ⟨e, me, qe, ex⟩ := lookup_entry hx
      have e1 : e.1 = .atom name := by
        have := Lynx.Term.compareExact_eq_symm qe
        simpa using this
      obtain ⟨d', hd', w, run, out⟩ := walk e me y (by rw [e1]; exact hy)
      rw [e1, ex] at run
      rw [e1] at out
      obtain ⟨w', run', k, sem⟩ := fieldC_inter ks fc hd' (sX.fields name x hx) (sY.fields name y hy)
      rw [run] at run'; cases run'
      rw [← sem p ok]
      cases kw : kept (.atom name, w)
      · rw [keptO_false kw, dn_none]
      · rw [keptO_true kw]
        rcases out with out | out
        · rw [kw] at out; cases out
        · have fw := (k kw).1
          obtain ⟨b, rb, ex'⟩ := fieldC_empty ks fc hH (show K ≤ d' by omega) fw S (fun _ => hS)
          have hb : b = Bool.true := by
            have := rb.symm.trans (by simpa using out)
            cases b <;> simp_all [boolAtom]
          have lw := (k kw).2 hH
          have lx := lh_field_le hx
          have ly := lh_field_le hy
          exact (ex' N (by omega) safe).2 hb p ok

/-- `disjoint?/2` answers `true` only on types that share no point. -/
theorem descr_disj_sound (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) (hH : H) (hS : FS [])
    {m : Nat} (hm : K + 7 ≤ m) {A B : List (Term × Term)} (sA : DescrC Fn TF LF MF A) (sB : DescrC Fn TF LF MF B)
    (h : Elixir.Module.Types.Descr.«disjoint?/2» (D m) (.map A) (.map B) = .ok (.atom "true")) :
    ∀ name p, PtOkC TV LV MV FV name p →
      (dn name (mapLookup A (.atom name)) p && dn name (mapLookup B (.atom name)) p) = Bool.false := by
  have stA := sA.static
  have stB := sB.static
  have calls : ∀ {X Y : List (Term × Term)}, DescrC Fn TF LF MF X → DescrC Fn TF LF MF Y → ∀ e ∈ mapEntries X,
      ∀ y d', K + 1 ≤ d' → mapLookup Y e.1 = some y → ∃ w,
        Elixir.Module.Types.Descr.«bare_intersection/3» (D d') e.1 e.2 y = .ok w ∧ (kept (e.1, w) = Bool.true →
          ∃ b : Bool, Elixir.Module.Types.Descr.«empty_key?/3» (D d') e.1 w (.map []) = .ok (boolAtom b)) := by
    intro X Y sX sY e me y d' hd hy
    have hx := mapLookup_of_mem_mapEntries me
    obtain ⟨name, -, key⟩ := sX.keys e.1 (by simp [hx])
    rw [key] at hx hy ⊢
    obtain ⟨w, run, k, -⟩ := fieldC_inter ks fc hd (sX.fields name e.2 hx) (sY.fields name y hy)
    refine ⟨w, run, fun kw => ?_⟩
    obtain ⟨b, rb, -⟩ := fieldC_empty ks fc hH (show K ≤ d' by omega) (k kw).1 [] (fun _ => hS)
    exact ⟨b, by simpa using rb⟩
  obtain ⟨sa, hsa⟩ : ∃ sa : Int, Erlang.erlang.«map_size/1» (.map A) = .ok (.integer sa) :=
    ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
  obtain ⟨sb, hsb⟩ : ∃ sb : Int, Erlang.erlang.«map_size/1» (.map B) = .ok (.integer sb) :=
    ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
  unfold Elixir.Module.Types.Descr.«disjoint?/2» at h
  simp [getMapKeys_single, stA, stB] at h
  unfold Elixir.Module.Types.Descr.«non_disjoint_intersection?/2» at h
  rw [Elixir.Module.Types.Descr.«non_disjoint_intersection?/3».eq_def] at h
  by_cases g : sa > sb
  · simp [hsa, hsb, g, Erlang.maps.«iterator/1»] at h
    have walk := iter_disj_gen (K + 1) A (.map []) (mapEntries B) (calls sB sA) m
      (by have := descrC_six sB; omega) (not_true (by rw [bind_assoc]; exact h))
    intro name p ok
    rw [Bool.and_comm]
    exact walk_disj_sem ks fc hH hS (safeN_nil (max (lh (.map A)) (lh (.map B)) + 1)) sB sA (by omega) (by omega) walk name p ok
  · simp [hsa, hsb, g, Erlang.maps.«iterator/1»] at h
    have walk := iter_disj_gen (K + 1) B (.map []) (mapEntries A) (calls sA sB) m
      (by have := descrC_six sA; omega) (not_true (by rw [bind_assoc]; exact h))
    exact walk_disj_sem ks fc hH hS (safeN_nil (max (lh (.map A)) (lh (.map B)) + 1)) sA sB (by omega) (by omega) walk

/-- Walks whose common fields all intersect into dropped or empty fields under the seen set find no common field. -/
theorem iter_disj_false_seen (K' : Nat) (B : List (Term × Term)) (Sm : Term) :
    ∀ es : List (Term × Term), (∀ e ∈ es, ∀ y, mapLookup B e.1 = some y → ∀ d', K' ≤ d' → ∃ w,
      Elixir.Module.Types.Descr.«bare_intersection/3» (D d') e.1 e.2 y = .ok w ∧
        (kept (e.1, w) = Bool.false ∨ Elixir.Module.Types.Descr.«empty_key?/3» (D d') e.1 w Sm = .ok (.atom "true"))) →
    ∀ m, K' + es.length ≤ m →
      (do
        let it ← Erlang.maps.«next/1» (Term.list (es.map fun (e : Term × Term) => .tuple #[e.1, e.2]))
        Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/3» (D m) it (.map B) Sm) = .ok (.atom "false") := by
  intro es
  induction es with
  | nil =>
    intro _ m _
    simp [Term.list, Erlang.maps.«next/1»]
    rw [Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/3».eq_def]
    simp
  | cons e rest ih =>
    intro calls m hm
    have calls' := fun e' (me' : e' ∈ rest) => calls e' (List.mem_cons_of_mem _ me')
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp at hm; omega⟩
    have hm' : K' + rest.length ≤ m := by simp at hm; omega
    have cont : ∀ x, (D (m + 1)).pure (.function false "Elixir.Module.Types.Descr"
        "-iterator_non_disjoint_intersection?/3-fun-0-" 1
        #[Term.list (rest.map fun (e : Term × Term) => .tuple #[e.1, e.2]), .map B, Sm]) #[x] =
        (do
          let it ← Erlang.maps.«next/1» (Term.list (rest.map fun (e : Term × Term) => .tuple #[e.1, e.2]))
          Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/3» (D m) it (.map B) Sm) := by
      intro x
      rw [Erlang.program.«Elixir.Module.Types.Descr:-iterator_non_disjoint_intersection?/3-fun-0-/1».pure]
      simp [Elixir.Module.Types.Descr.«-iterator_non_disjoint_intersection?/3-fun-0-/4»]
    refine Eq.trans ?_ (ih calls' m hm')
    simp only [List.map, Term.list, next_cons, Lynx.Except.ok_bind]
    rw [Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/3».eq_def]
    cases hb : mapLookup B e.1 with
    | none => simp [getMapKeys_single, hb, cont]
    | some y₀ =>
      obtain ⟨w, rw', k₀⟩ := calls e List.mem_cons_self y₀ hb (m + 1) (by simp at hm; omega)
      rcases k₀ with k | hb'
      · rcases dropped k with e₀ | e₀ <;> rw [e₀] at rw' <;>
          simp [getMapKeys_single, hb, rw', Erlang.erlang.«=:=/2», cont, isMember]
      · by_cases dz : (compareExact (fuel w (.integer 0)) w (.integer 0) = .eq ∨ compareExact (fuel w (.atom "bdd_bot")) w (.atom "bdd_bot") = .eq)
        · rcases dz with dz | dz <;>
            simp [getMapKeys_single, hb, rw', Erlang.erlang.«=:=/2», cont, isMember, dz]
        · simp only [not_or] at dz
          simp [getMapKeys_single, hb, rw', Erlang.erlang.«=:=/2», cont, isMember, dz.1, dz.2, hb']

/-- `disjoint_seen?/3` answers `true` on static maps only when they share no point, when the seen BDDs are higher
than them. -/
theorem descr_sdisj_sound (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) (hH : H) {S : List (Term × Term)}
    (hS : FS S) {N : Nat} (safe : SafeN N S) {m : Nat} (hm : K + 7 ≤ m) {A B : List (Term × Term)}
    (sA : DescrC Fn TF LF MF A) (sB : DescrC Fn TF LF MF B) (lA : lh (.map A) < N) (lB : lh (.map B) < N)
    (h : Elixir.Module.Types.Descr.«disjoint_seen?/3» (D m) (.map A) (.map B) (.map S) = .ok (.atom "true")) :
    ∀ name p, PtOkC TV LV MV FV name p →
      (dn name (mapLookup A (.atom name)) p && dn name (mapLookup B (.atom name)) p) = Bool.false := by
  have stA := sA.static
  have stB := sB.static
  have calls : ∀ {X Y : List (Term × Term)}, DescrC Fn TF LF MF X → DescrC Fn TF LF MF Y → ∀ e ∈ mapEntries X,
      ∀ y d', K + 1 ≤ d' → mapLookup Y e.1 = some y → ∃ w,
        Elixir.Module.Types.Descr.«bare_intersection/3» (D d') e.1 e.2 y = .ok w ∧ (kept (e.1, w) = Bool.true →
          ∃ b : Bool, Elixir.Module.Types.Descr.«empty_key?/3» (D d') e.1 w (.map S) = .ok (boolAtom b)) := by
    intro X Y sX sY e me y d' hd hy
    have hx := mapLookup_of_mem_mapEntries me
    obtain ⟨name, -, key⟩ := sX.keys e.1 (by simp [hx])
    rw [key] at hx hy ⊢
    obtain ⟨w, run, k, -⟩ := fieldC_inter ks fc hd (sX.fields name e.2 hx) (sY.fields name y hy)
    refine ⟨w, run, fun kw => ?_⟩
    obtain ⟨b, rb, -⟩ := fieldC_empty ks fc hH (show K ≤ d' by omega) (k kw).1 S (fun _ => hS)
    exact ⟨b, by simpa using rb⟩
  obtain ⟨sa, hsa⟩ : ∃ sa : Int, Erlang.erlang.«map_size/1» (.map A) = .ok (.integer sa) :=
    ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
  obtain ⟨sb, hsb⟩ : ∃ sb : Int, Erlang.erlang.«map_size/1» (.map B) = .ok (.integer sb) :=
    ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
  rw [disj_seen_maps _ _ _ _ stA stB] at h
  have h' := not_true h
  rw [Elixir.Module.Types.Descr.«non_disjoint_intersection?/3».eq_def] at h'
  by_cases g : sa > sb
  · simp [hsa, hsb, g, Erlang.maps.«iterator/1»] at h'
    have walk := iter_disj_gen (K + 1) A (.map S) (mapEntries B) (calls sB sA) m
      (by have := descrC_six sB; omega) h'
    intro name p ok
    rw [Bool.and_comm]
    exact walk_disj_sem ks fc hH hS safe sB sA lB lA walk name p ok
  · simp [hsa, hsb, g, Erlang.maps.«iterator/1»] at h'
    have walk := iter_disj_gen (K + 1) B (.map S) (mapEntries A) (calls sA sB) m
      (by have := descrC_six sA; omega) h'
    exact walk_disj_sem ks fc hH hS safe sA sB lA lB walk

/-- `disjoint_seen?/3` answers `true` on static maps that share no point, when the seen BDDs are higher than them. -/
theorem descr_sdisj_complete (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) (hH : H)
    {S : List (Term × Term)} (hS : FS S) {N : Nat} (safe : SafeN N S) {m : Nat} (hm : K + 7 ≤ m)
    {A B : List (Term × Term)} (sA : DescrC Fn TF LF MF A) (sB : DescrC Fn TF LF MF B) (lA : lh (.map A) < N)
    (lB : lh (.map B) < N)
    (disj : ∀ name p, PtOkC TV LV MV FV name p →
      (dn name (mapLookup A (.atom name)) p && dn name (mapLookup B (.atom name)) p) = Bool.false) :
    Elixir.Module.Types.Descr.«disjoint_seen?/3» (D m) (.map A) (.map B) (.map S) = .ok (.atom "true") := by
  have stA := sA.static
  have stB := sB.static
  have calls : ∀ {X Y : List (Term × Term)}, DescrC Fn TF LF MF X → DescrC Fn TF LF MF Y → lh (.map X) < N →
      lh (.map Y) < N → (∀ name p, PtOkC TV LV MV FV name p →
        (dn name (mapLookup X (.atom name)) p && dn name (mapLookup Y (.atom name)) p) = Bool.false) →
      ∀ e ∈ mapEntries X, ∀ y, mapLookup Y e.1 = some y → ∀ d', K + 1 ≤ d' → ∃ w,
        Elixir.Module.Types.Descr.«bare_intersection/3» (D d') e.1 e.2 y = .ok w ∧
          (kept (e.1, w) = Bool.false ∨
            Elixir.Module.Types.Descr.«empty_key?/3» (D d') e.1 w (.map S) = .ok (.atom "true")) := by
    intro X Y sX sY lX lY dXY e me y hy d' hd
    have hx := mapLookup_of_mem_mapEntries me
    obtain ⟨name, -, key⟩ := sX.keys e.1 (by simp [hx])
    rw [key] at hx hy ⊢
    obtain ⟨w, run, k, sem⟩ := fieldC_inter ks fc hd (sX.fields name e.2 hx) (sY.fields name y hy)
    refine ⟨w, run, ?_⟩
    cases kw : kept (.atom name, w)
    · exact Or.inl rfl
    · refine Or.inr ?_
      obtain ⟨b, rb, ex⟩ := fieldC_empty ks fc hH (show K ≤ d' by omega) (k kw).1 S (fun _ => hS)
      have lw := (k kw).2 hH
      have lx := lh_field_le hx
      have ly := lh_field_le hy
      have hb := (ex N (by omega) safe).1 fun p ok => by
        have := sem p ok
        rw [keptO_true kw] at this
        rw [this, ← hx, ← hy]
        exact dXY name p ok
      subst hb
      simpa using rb
  obtain ⟨sa, hsa⟩ : ∃ sa : Int, Erlang.erlang.«map_size/1» (.map A) = .ok (.integer sa) :=
    ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
  obtain ⟨sb, hsb⟩ : ∃ sb : Int, Erlang.erlang.«map_size/1» (.map B) = .ok (.integer sb) :=
    ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
  rw [disj_seen_maps _ _ _ _ stA stB, Elixir.Module.Types.Descr.«non_disjoint_intersection?/3».eq_def]
  by_cases g : sa > sb
  · have walk := iter_disj_false_seen (K + 1) A (.map S) (mapEntries B)
      (calls sB sA lB lA fun name p ok => by rw [Bool.and_comm]; exact disj name p ok) m
      (by have := descrC_six sB; omega)
    simp [hsa, hsb, g, Erlang.maps.«iterator/1»]
    rw [walk]
    rfl
  · have walk := iter_disj_false_seen (K + 1) B (.map S) (mapEntries A) (calls sA sB lA lB disj) m
      (by have := descrC_six sA; omega)
    simp [hsa, hsb, g, Erlang.maps.«iterator/1»]
    rw [walk]
    rfl

end

end Elixir.STTDescrProofsTest.Nest
