/-! Gradual function application: the shapes of its results, element types of the level of the arguments, or the
recursive node, which unfolds to its expansion. -/

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {V : Type} {E : Term → Prop} {den : Term → V → Prop}

/-- Lines of arrows of arity `n` that `fun_normalize/2` keeps for the functions `Live`: each function is in one of
them, and each comes from a non-empty line whose functions are live. -/
structure NormP (E : Term → Prop) (den : Term → V → Prop) (n : Nat) (Live : List (FunSem.Row V) → Prop)
    (Q : List (List (Term × List Term × Term))) : Prop where
  pos : ∀ q ∈ Q, PosOk E n q
  nonempty : ∀ q ∈ Q, q ≠ []
  cover : ∀ g : List (FunSem.Row V), (∀ r ∈ g, FunSem.ValidRow n r) → Live g →
    ∃ q ∈ Q, ∀ p ∈ semP den q, ∀ r ∈ g, FunSem.Allows p r
  live : ∀ q ∈ Q, ∃ N, PosOk E n N ∧ ¬FunSem.LineEmpty n (semP den q) (semP den N) ∧
    ∀ g : List (FunSem.Row V), (∀ r ∈ g, FunSem.ValidRow n r) → (∀ p ∈ semP den q, ∀ r ∈ g, FunSem.Allows p r) →
      (∀ q' ∈ semP den N, ¬∀ r ∈ g, FunSem.Allows q' r) → Live g

theorem NormOk.toP {E₀ : Term → Prop} {n : Nat} {b : Term} {Q : List (List (Term × List Term × Term))}
    (h : NormOk E E₀ den n b Q) : NormP E den n (fun g => eval (valF E₀ den g) b = Bool.true) Q :=
  ⟨h.pos, h.nonempty, h.cover, fun q mq => let ⟨N, hN, lv, sat⟩ := h.live q mq; ⟨N, hN, lv, fun g _ => sat g⟩⟩

theorem NormP.congr {n : Nat} {Live Live' : List (FunSem.Row V) → Prop} {Q : List (List (Term × List Term × Term))}
    (h : NormP E den n Live Q) (e : ∀ g, (∀ r ∈ g, FunSem.ValidRow n r) → (Live g ↔ Live' g)) :
    NormP E den n Live' Q :=
  ⟨h.pos, h.nonempty, fun g vg hg => h.cover g vg ((e g vg).mpr hg),
    fun q mq => let ⟨N, hN, lv, sat⟩ := h.live q mq; ⟨N, hN, lv, fun g vg a b => (e g vg).mp (sat g vg a b)⟩⟩

/-- Some live function of a line. -/
theorem NormP.witness {n : Nat} {Live : List (FunSem.Row V) → Prop} {Q : List (List (Term × List Term × Term))}
    (h : NormP E den n Live Q) {q : List (Term × List Term × Term)} (mq : q ∈ Q) :
    ∃ N, ∃ g : List (FunSem.Row V), (∀ r ∈ g, FunSem.ValidRow n r) ∧ (∀ p ∈ semP den q, ∀ r ∈ g, FunSem.Allows p r) ∧
      (∀ q' ∈ semP den N, ¬∀ r ∈ g, FunSem.Allows q' r) ∧
      ∀ g' : List (FunSem.Row V), (∀ r ∈ g', FunSem.ValidRow n r) → (∀ p ∈ semP den q, ∀ r ∈ g', FunSem.Allows p r) →
        (∀ q' ∈ semP den N, ¬∀ r ∈ g', FunSem.Allows q' r) → Live g' := by
  obtain ⟨N, -, lv, sat⟩ := h.live q mq
  rw [lineEmpty_iff_none] at lv
  obtain ⟨g, hg⟩ := Classical.not_forall.mp lv
  obtain ⟨vg, hab⟩ := Classical.not_imp.mp hg
  obtain ⟨allP, noN⟩ := Classical.not_not.mp hab
  exact ⟨N, g, vg, allP, noN, sat⟩

/-- The image of live functions of arity `n` on the argument lists `I`. -/
def ImgP (n : Nat) (Live : List (FunSem.Row V) → Prop) (I : List V → Prop) (v : V) : Prop :=
  ∃ g : List (FunSem.Row V), (∀ r ∈ g, FunSem.ValidRow n r) ∧ Live g ∧ ∃ x, I x ∧ (x.map some, some v) ∈ g

/-- Applying the lines `fun_normalize/2` keeps gives the image of the live functions. -/
theorem app_imageP {n : Nat} {Live : List (FunSem.Row V) → Prop} {Q : List (List (Term × List Term × Term))}
    (nQ : NormP E den n Live Q) {I : List V → Prop} (len : ∀ x, I x → x.length = n) (ne : ∃ x, I x) (v : V) :
    (∃ q ∈ Q, FunSem.App I (fun _ => True) (semP den q) v) ↔ ImgP n Live I v := by
  constructor
  · rintro ⟨q, mq, app⟩
    obtain ⟨x, hx, -, hall⟩ := (FunSem.app_iff _ I _ ne v).mp app
    obtain ⟨N, g, vg, allP, noN, sat⟩ := nQ.witness mq
    let row : FunSem.Row V := (x.map some, some v)
    have vg' : ∀ r ∈ row :: g, FunSem.ValidRow n r := by
      intro r mr
      rcases List.mem_cons.mp mr with rfl | mr
      · exact ⟨by simp [row, len x hx], fun h => by simp [row] at h⟩
      · exact vg r mr
    refine ⟨row :: g, vg', sat _ vg' (fun p mp r mr => ?_) (fun q' mq' h => noN q' mq' fun r mr =>
      h r (List.mem_cons_of_mem _ mr)), x, hx, List.mem_cons_self⟩
    rcases List.mem_cons.mp mr with rfl | mr
    · exact (allows_row p x v).mpr (hall p mp)
    · exact allP p mp r mr
  · rintro ⟨g, vg, hg, x, hx, mr⟩
    obtain ⟨q, mq, allP⟩ := nQ.cover g vg hg
    exact ⟨q, mq, (FunSem.app_iff _ I _ ne v).mpr ⟨x, hx, trivial, fun p mp => (allows_row p x v).mp (allP p mp _ mr)⟩⟩

/-- Argument lists in the domain of the lines are those no live function fails on. -/
theorem dom_safeP {n : Nat} {Live : List (FunSem.Row V) → Prop} {Q : List (List (Term × List Term × Term))}
    (nQ : NormP E den n Live Q) (x : List V) (lx : x.length = n) :
    (∀ q ∈ Q, ∃ p ∈ semP den q, FunSem.InDomR p.1 x) ↔
      ∀ g : List (FunSem.Row V), (∀ r ∈ g, FunSem.ValidRow n r) → Live g → (x.map some, Option.none) ∉ g := by
  constructor
  · intro h g vg hg mr
    obtain ⟨q, mq, allP⟩ := nQ.cover g vg hg
    obtain ⟨p, mp, hp⟩ := h q mq
    obtain ⟨y, e, -⟩ := allP p mp _ mr ((FunSem.inDom_real p.1 x).mpr hp)
    cases e
  · intro h q mq
    refine Classical.byContradiction fun none => ?_
    obtain ⟨N, g, vg, allP, noN, sat⟩ := nQ.witness mq
    obtain ⟨v, x', rfl⟩ : ∃ v x', x = v :: x' := by
      cases x with
      | cons v x' => exact ⟨v, x', rfl⟩
      | nil =>
        exfalso
        obtain ⟨p, mp⟩ := List.exists_mem_of_ne_nil q (nQ.nonempty q mq)
        have lp : p.2.1.length = 0 := by rw [(nQ.pos q mq p mp).2.2]; simp at lx; omega
        exact none ⟨_, List.mem_map.mpr ⟨p, mp, rfl⟩, by simp [List.length_eq_zero_iff.mp lp, FunSem.InDomR]⟩
    let row : FunSem.Row V := ((v :: x').map some, Option.none)
    have vg' : ∀ r ∈ row :: g, FunSem.ValidRow n r := by
      intro r mr
      rcases List.mem_cons.mp mr with rfl | mr
      · refine ⟨by simp only [row, List.length_map]; exact lx, fun h => ?_⟩
        have e := h.1
        simp only [row] at e
        rw [← lx] at e
        simp [List.replicate_succ] at e
      · exact vg r mr
    refine h (row :: g) vg' (sat _ vg' (fun p mp r mr => ?_) (fun q' mq' h' => noN q' mq' fun r mr =>
      h' r (List.mem_cons_of_mem _ mr))) List.mem_cons_self
    rcases List.mem_cons.mp mr with rfl | mr
    · intro hd; exact absurd ⟨p, mp, (FunSem.inDom_real p.1 _).mp hd⟩ none
    · exact allP p mp r mr

end

section
variable {t : Term} {d : Nat}

/-- Element types of the level above `d` are types of level `d`, or the node, whose expansion is one. -/
theorem el_canon {e : Term} (he : (level t (d + 1)).E e) :
    ∃ c, DE (level t d).E c ∧ (∀ v : PN t d, (level t (d + 1)).den e v ↔ denD c v) ∧
      (DE (level t d).E e ∧ c = e ∨ IsT (level t d).nd e ∧ c = expN e (keyOf (level t d).nd)) := by
  rcases he with h | h
  · exact ⟨e, h, fun v => den_succ h v, Or.inl ⟨h, rfl⟩⟩
  · refine ⟨_, (nodeOk_DE (level t d).ef.term (level t d).hasT).exp h, fun v => ?_, Or.inr ⟨h, rfl⟩⟩
    show denN (level t d).nd denD e v ↔ _
    rw [denN_node h]

theorem node_tuple {e : Term} (h : IsT (level t d).nd e) : ∃ r S, e = .tuple #[.reference r, .map S, gen] := by
  obtain ⟨S, rfl, -⟩ := h.node
  exact ⟨_, S, rfl⟩

theorem expN_map (e : Term) (k : Int) : ∃ X, expN e k = .map X ∧ mapLookup X (.atom "dynamic") = none :=
  ⟨_, rfl, by simp [mapLookup]⟩

/-- A node is compared as its expansion. -/
theorem sub_node {e : Term} (hn : IsT (level t d).nd e) (b : Term) (m : Nat) :
    Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) e b =
      Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) (expN e (keyOf (level t d).nd)) b := by
  obtain ⟨r, S, rfl⟩ := node_tuple hn
  have ex := expand_isT hn m
  obtain ⟨X, eX, -⟩ := expN_map (.tuple #[.reference r, .map S, gen]) (keyOf (level t d).nd)
  rw [eX] at ex ⊢
  rw [Elixir.Module.Types.Descr.«subtype?/2».eq_def, Elixir.Module.Types.Descr.«subtype?/2».eq_def]
  simp [ex, unfold_map]

/-- The bounds and the dynamic type of an element type of the level above `d`. -/
theorem el_ops {e : Term} (he : (level t (d + 1)).E e) (m : Nat) :
    ∃ c, DE (level t d).E c ∧ (∀ v : PN t d, (level t (d + 1)).den e v ↔ denD c v) ∧
      Elixir.Module.Types.Descr.«upper_bound/1» (D (m + 1)) e = .ok c ∧
      Elixir.Module.Types.Descr.«lower_bound/1» (D (m + 1)) e = .ok c ∧
      Elixir.Module.Types.Descr.«dynamic/1» (D (m + 1)) e = .ok (.map [(.atom "dynamic", c)]) ∧
      ((level t d).K + 22 ≤ m → ∀ b, GD t d b → Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) e b =
        .ok (boolAtom (bp (SubN t d c (lower b) ∧ SubN t d c (upper b))))) := by
  obtain ⟨c, hc, sem, h⟩ := el_canon he
  refine ⟨c, hc, sem, ?_⟩
  have subC : (level t d).K + 22 ≤ m → ∀ b, GD t d b → Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) c b =
      .ok (boolAtom (bp (SubN t d c (lower b) ∧ SubN t d c (upper b)))) := by
    intro hm b gb
    obtain ⟨g, lo, up⟩ := de_gd hc
    rw [gd_sub g.1 gb.1 g.2.1 g.2.2 gb.2.1 gb.2.2 (by omega), lo, up]
  suffices Elixir.Module.Types.Descr.«upper_bound/1» (D (m + 1)) e = .ok c ∧
      Elixir.Module.Types.Descr.«lower_bound/1» (D (m + 1)) e = .ok c ∧
      Elixir.Module.Types.Descr.«dynamic/1» (D (m + 1)) e = .ok (.map [(.atom "dynamic", c)]) by
    refine ⟨this.1, this.2.1, this.2.2, fun hm b gb => ?_⟩
    rcases h with ⟨-, rfl⟩ | ⟨hn, rfl⟩
    · exact subC hm b gb
    · rw [sub_node hn b m]; exact subC hm b gb
  have st : c = .atom "term" ∨ ∃ X, c = .map X ∧ mapLookup X (.atom "dynamic") = none := by
    rcases hc with rfl | ⟨X, rfl, sX⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨X, rfl, sX.static⟩
  rcases h with ⟨-, rfl⟩ | ⟨hn, rfl⟩
  · rcases st with rfl | ⟨X, rfl, sX⟩
    · refine ⟨upper_bound_term _, ?_, ?_⟩
      · unfold Elixir.Module.Types.Descr.«lower_bound/1»; rfl
      · unfold Elixir.Module.Types.Descr.«dynamic/1»; rfl
    · refine ⟨upper_bound_static sX, ?_, ?_⟩
      · rw [lower_bound_run (Or.inr ⟨X, rfl⟩)]; simp [lower, rmDyn_static sX]
      · unfold Elixir.Module.Types.Descr.«dynamic/1»; simp [getMapKeys_single, sX]
  · obtain ⟨r, S, rfl⟩ := node_tuple hn
    have ex := expand_isT hn m
    obtain ⟨X, eX, sX⟩ := expN_map (.tuple #[.reference r, .map S, gen]) (keyOf (level t d).nd)
    rw [eX] at ⊢
    have gt : getMapKeys [Term.atom "dynamic"] (.tuple #[.reference r, .map S, gen]) = [] := by
      simp [getMapKeys]
    refine ⟨?_, ?_, ?_⟩
    · unfold Elixir.Module.Types.Descr.«upper_bound/1»
      simp [getMapKeys_single, gt, ex, eX, unfold_map, sX]
    · unfold Elixir.Module.Types.Descr.«lower_bound/1»
      simp [ex, eX, unfold_map, lower_bound_run (Or.inr ⟨X, rfl⟩), lower, rmDyn_static sX]
    · unfold Elixir.Module.Types.Descr.«dynamic/1»
      simp [getMapKeys_single, gt, ex, eX, unfold_map, sX]

end

/-! Domains of gradual arguments: tuples of their lower bounds, with the tuples of their upper bounds as dynamic
part. -/

/-- Gradual types as arguments: the top type or maps. -/
def GA (a : Term) : Prop := a = .atom "term" ∨ ∃ X, a = .map X

/-- Whether a type has a dynamic part. -/
def isDynB : Term → Bool
  | .map X => (mapLookup X (.atom "dynamic")).isSome
  | _ => Bool.false

theorem split_ga {a : Term} (h : GA a) :
    Elixir.Module.Types.Descr.«split_dynamic/1» a = .ok (.tuple #[upper a, lower a, boolAtom (isDynB a)]) := by
  rcases h with rfl | ⟨X, rfl⟩
  · rfl
  · unfold Elixir.Module.Types.Descr.«split_dynamic/1»
    cases e : mapLookup X (.atom "dynamic") with
    | none => simp [getMapKeys_single, e, upper, lower, rmDyn_static e, isDynB, boolAtom]
    | some Dy => simp [getMapKeys_single, e, upper, lower, Erlang.maps.«remove/2», rmDyn, isDynB, boolAtom]

/-- Whether a type is `%{}` by comparison. -/
def isNoneB (a : Term) : Bool := Term.compare (Term.fuel a (.map [])) a (.map []) == .eq

theorem descr_fields_g (l : List Term) (hl : ∀ e ∈ l, GA e) :
    ∀ (acc dacc : List Term) (dy se : Bool),
      Elixir.Module.Types.Descr.«tuple_descr_fields/5» (Term.list l) (Term.list acc) (Term.list dacc)
        (boolAtom dy) (boolAtom se) =
      .ok (Term.tuple #[Term.list ((l.map lower).reverse ++ acc), Term.list ((l.map upper).reverse ++ dacc),
        boolAtom (dy || l.any isDynB), boolAtom (se || l.any fun e => isNoneB (lower e))]) := by
  induction l with
  | nil => intro acc dacc dy se; simp [Elixir.Module.Types.Descr.«tuple_descr_fields/5»]
  | cons x xs ih =>
    intro acc dacc dy se
    have hx := hl x List.mem_cons_self
    have run := ih (fun e m => hl e (List.mem_cons_of_mem _ m)) (lower x :: acc) (upper x :: dacc)
      (dy || isDynB x) (se || isNoneB (lower x))
    have eq : Erlang.erlang.«==/2» (lower x) (.map []) = .ok (boolAtom (isNoneB (lower x))) := by
      simp only [Erlang.erlang.«==/2», isNoneB]
      by_cases h : Term.compare (Term.fuel (lower x) (.map [])) (lower x) (.map []) = .eq <;> simp [h, boolAtom]
    rw [Elixir.Module.Types.Descr.«tuple_descr_fields/5».eq_def]
    simp only [Term.list] at run ⊢
    simp only [split_ga hx, Lynx.Except.ok_bind, eq]
    have o₁ : Lynx.Except.orElse (pure (boolAtom dy)) (pure (boolAtom (isDynB x))) Bool.true =
        .ok (boolAtom (dy || isDynB x)) := by cases dy <;> cases isDynB x <;> rfl
    have o₂ : Lynx.Except.orElse (pure (boolAtom se)) (Except.ok (boolAtom (isNoneB (lower x)))) Bool.true =
        .ok (boolAtom (se || isNoneB (lower x))) := by cases se <;> cases isNoneB (lower x) <;> rfl
    simp only [o₁, o₂, Lynx.Except.ok_bind]
    rw [run]
    simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append, List.any_cons, Bool.or_assoc]

/-- The domain of gradual arguments: the tuple of their upper bounds, as a static type when none is gradual, and
otherwise as the dynamic part of the tuple of their lower bounds, or of `%{}` when one of them is `%{}`. -/
theorem args_domain_g (l : List Term) (hl : ∀ e ∈ l, GA e) : ∃ kU kL : Int,
    Elixir.Module.Types.Descr.«bdd_leaf_new/2» (.atom "closed") (Term.list (l.map upper)) =
      .ok (.tuple #[.integer kU, .atom "closed", Term.list (l.map upper)]) ∧
    Elixir.Module.Types.Descr.«bdd_leaf_new/2» (.atom "closed") (Term.list (l.map lower)) =
      .ok (.tuple #[.integer kL, .atom "closed", Term.list (l.map lower)]) ∧
    Elixir.Module.Types.Descr.«args_to_domain/1» (Term.list l) =
      .ok (if l.any isDynB then
        (if l.any fun e => isNoneB (lower e) then
          .map [(.atom "dynamic", .map [(.atom "tuple", .tuple #[.integer kU, .atom "closed", Term.list (l.map upper)])])]
        else
          .map [(.atom "dynamic", .map [(.atom "tuple", .tuple #[.integer kU, .atom "closed", Term.list (l.map upper)])]),
            (.atom "tuple", .tuple #[.integer kL, .atom "closed", Term.list (l.map lower)])])
      else .map [(.atom "tuple", .tuple #[.integer kU, .atom "closed", Term.list (l.map upper)])]) := by
  have run := descr_fields_g l hl [] [] Bool.false Bool.false
  obtain ⟨kU, leafU⟩ := leaf_closed (l.map upper)
  obtain ⟨kL, leafL⟩ := leaf_closed (l.map lower)
  refine ⟨kU, kL, leafU, leafL, ?_⟩
  have revU : Erlang.lists.«reverse/1» (Term.list (l.map upper).reverse) = .ok (Term.list (l.map upper)) := by
    simpa using reverse1_list (l.map upper).reverse
  have revL : Erlang.lists.«reverse/1» (Term.list (l.map lower).reverse) = .ok (Term.list (l.map lower)) := by
    simpa using reverse1_list (l.map lower).reverse
  simp only [Term.list, List.append_nil, Bool.false_or] at run
  have run' : Elixir.Module.Types.Descr.«tuple_descr_fields/5» (Term.list l) .nil .nil (.atom "false") (.atom "false") =
      .ok (Term.tuple #[Term.list (l.map lower).reverse, Term.list (l.map upper).reverse, boolAtom (l.any isDynB),
        boolAtom (l.any fun e => isNoneB (lower e))]) := by simpa [boolAtom] using run
  have hlist : Erlang.erlang.«is_list/1» (Term.list l) = .ok (.atom "true") := by
    cases l <;> simp [Erlang.erlang.«is_list/1»]
  unfold Elixir.Module.Types.Descr.«args_to_domain/1»
  simp only [hlist, Lynx.Except.guard, Elixir.Module.Types.Descr.«tuple/1», Elixir.Module.Types.Descr.«tuple_descr/2»,
    run', Lynx.Except.ok_bind, Elixir.Module.Types.Descr.«tuple_descr_static/2», revU, revL,
    Elixir.Module.Types.Descr.«tuple_new/2», leafU, leafL]
  cases hd : l.any isDynB <;> cases hn : l.any (fun e => isNoneB (lower e)) <;>
    simp [boolAtom, Erlang.erlang.«/=/2», Lynx.Except.andAlso, Erlang.maps.«put/3»]

/-! `fun_normalize/2` on types of the level of functions: the top type, maps of unions of arities, of negations of
arities, or without functions. -/

section
variable {t : Term} {n : Nat}

/-- Functions of arity `a` of a type of the level of functions. -/
def FunT (t : Term) (n : Nat) (T : Term) (a : Nat) (g : List (FunSem.Row (level t n).V)) : Prop :=
  T = .atom "term" ∨ ∃ X, T = .map X ∧ FunIn t n X a g

/-- What `fun_normalize/2` answers at the arity `a`: the lines and domain of the functions of that arity when it
holds some, and otherwise anything but `{:ok, _, _}`, which is `:badfun` exactly when the type holds no function. -/
def NormRes (t : Term) (n H : Nat) (T : Term) (a : Nat) (res : Except Exception Term) : Prop :=
  (∃ dom Q, NormP (EB (level t n).E H) (level t n).den a (FunT t n T a) Q ∧ Q ≠ [] ∧ DomA (level t n).E H dom ∧
      (∀ x, ddenA (level t n).E (level t n).den dom x ↔ ∀ q ∈ Q, ∃ p ∈ semP (level t n).den q, FunSem.InDomR p.1 x) ∧
      res = .ok (.tuple #[.atom "ok", dom, Term.list (Q.reverse.map encP)])) ∨
    ((∀ g, (∀ r ∈ g, FunSem.ValidRow a r) → ¬FunT t n T a g) ∧
      (∀ w, res = .ok w → w = .atom "badfun" ∨ ∃ x y, w = .tuple #[.atom "badarity", x, y]) ∧
      (res = .ok (.atom "badfun") ↔ ∀ (b : Nat) g, (∀ r ∈ g, FunSem.ValidRow b r) → ¬FunT t n T b g))

theorem funIn_union {X R : List (Term × Term)} (hF : mapLookup X (.atom "fun") = some (.tuple #[.atom "union", .map R]))
    (a : Nat) (g : List (FunSem.Row (level t n).V)) :
    FunIn t n X a g ↔ evalR R (.integer a) (valF (level t n).E (level t n).den g) = Bool.true := by
  simp [FunIn, hF, arityOf, evalR]

/-- `fun_normalize/2` on maps whose function type is not a negation. -/
theorem normalize_noneg {H : Nat} (one : 1 ≤ H) {X : List (Term × Term)} (hX : DE (level t n).E (.map X))
    (hlX : lh (.map X) < H) (nneg : ∀ R, mapLookup X (.atom "fun") ≠ some (.tuple #[.atom "negation", R])) (a : Nat) :
    ∃ res, (∀ m, (level t n).K + 14 ≤ m → Elixir.Module.Types.Descr.«fun_normalize/2» (D m) (.map X) (.integer a) = res) ∧
      NormRes t n H (.map X) a res := by
  have sX := de_map hX
  have fe : FunElem (EB (level t n).E H) (level t n).den ((level t n).K + 6) (.map []) :=
    (felem (level t n).ef (level t n).ef.subc one (safeN_nil H)).mono (by omega)
  have fd := fdom (level t n).ef one (safeT_nil (H + 1))
  have cg : DenCongr (level t n).E (level t n).den := (level t n).ef.congrE
  have funT : ∀ b g, FunT t n (.map X) b g ↔ FunIn t n X b g := fun b g =>
    ⟨fun h => h.elim (fun h => by cases h) fun ⟨Y, e, h⟩ => by simp only [Term.map.injEq] at e; subst e; exact h,
     fun h => Or.inr ⟨X, rfl, h⟩⟩
  cases hF : mapLookup X (.atom "fun") with
  | none =>
    refine ⟨.ok (.atom "badfun"), fun m _ => ?_, Or.inr ⟨fun g _ h => ?_, fun w e => Or.inl (Except.ok.inj e).symm,
      ⟨fun _ b g _ h => ?_, fun _ => rfl⟩⟩⟩
    · rw [Elixir.Module.Types.Descr.«fun_normalize/2».eq_def]; simp [getMapKeys_single, hF]
    · obtain ⟨F, hF', -⟩ := (funT a g).mp h; rw [hF] at hF'; cases hF'
    · obtain ⟨F, hF', -⟩ := (funT b g).mp h; rw [hF] at hF'; cases hF'
  | some F =>
    rcases sX.fields "fun" F hF with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, fF⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> try (simp at e; done)
    obtain ⟨pos, R, rfl, -, bR, kR⟩ := fF
    cases pos
    case false => exact absurd hF (nneg _)
    simp only [ite_true] at hF
    have hR := arityBdds_of hlX hF bR kR
    obtain ⟨res, run, cs⟩ := normalize_union fe fd cg (fun a h => h.1) hF hR a
    refine ⟨.ok res, fun m hm => run m (by omega), ?_⟩
    rcases cs with ⟨b, dom, Q, hb, nQ, ne, hdom, sdom, rfl⟩ | ⟨dead, bf, sh⟩
    · refine Or.inl ⟨dom, Q, nQ.toP.congr (fun g _ => ?_), ne, hdom, sdom, rfl⟩
      rw [funT, funIn_union hF]; simp [evalR, hb]
    · refine Or.inr ⟨fun g vg h => ?_, fun w e => ?_, ?_⟩
      · rw [funT, funIn_union hF, dead g vg] at h; cases h
      · rcases sh with rfl | ⟨o, rfl⟩
        · exact Or.inl (Except.ok.inj e).symm
        · exact Or.inr ⟨_, _, (Except.ok.inj e).symm⟩
      · simp only [Except.ok.injEq]
        rw [bf]
        refine forall_congr' fun b => forall_congr' fun g => imp_congr_right fun vg => ?_
        rw [funT, funIn_union hF]
        cases evalR R (.integer b) (valF (level t n).E (level t n).den g) <;> simp

theorem lh_top (a : Nat) :
    lh (.map [(.atom "fun", .tuple #[.atom "union", .map [(.integer a, .atom "bdd_top")]])]) ≤ 1 := by
  refine lh_map_le.mpr fun e me => ?_
  have := mem_of_mem_mapEntries me
  simp only [List.mem_singleton] at this
  subst this
  rw [lh_union]
  refine lh_map_le.mpr fun e' me' => ?_
  have := mem_of_mem_mapEntries me'
  simp only [List.mem_singleton] at this
  subst this
  simp [lh]

theorem top_noneg (a : Nat) (R : Term) :
    mapLookup [(.atom "fun", .tuple #[.atom "union", .map [(.integer a, .atom "bdd_top")]])] (.atom "fun") ≠
      some (.tuple #[.atom "negation", R]) := by
  simp [mapLookup]

/-- `fun_normalize/2` on the top type normalizes the top function of the arity. -/
theorem normalize_term {H : Nat} (two : 2 ≤ H) (a : Nat) :
    ∃ res, (∀ m, (level t n).K + 14 ≤ m →
      Elixir.Module.Types.Descr.«fun_normalize/2» (D m) (.atom "term") (.integer a) = res) ∧
      NormRes t n H (.atom "term") a res := by
  obtain ⟨res, run, cs⟩ := normalize_noneg (t := t) (n := n) (H := H) (by omega) (top_de a) (by have := lh_top a; omega)
    (top_noneg a) a
  refine ⟨res, fun m hm => ?_, ?_⟩
  · rw [Elixir.Module.Types.Descr.«fun_normalize/2».eq_def]
    simp [fun_arity_run, run m hm]
  have eqT : ∀ g, FunT t n (.map [(.atom "fun", .tuple #[.atom "union", .map [(.integer a, .atom "bdd_top")]])]) a g ↔
      FunT t n (.atom "term") a g := fun g =>
    ⟨fun _ => Or.inl rfl, fun _ => Or.inr ⟨_, rfl, (funIn_top a a g).mpr rfl⟩⟩
  rcases cs with ⟨dom, Q, nQ, ne, hdom, sdom, rfl⟩ | ⟨dead, -, -⟩
  · exact Or.inl ⟨dom, Q, nQ.congr (fun g _ => eqT g), ne, hdom, sdom, rfl⟩
  · exact absurd ((eqT []).mpr (Or.inl rfl)) (dead [] (by simp))

/-- `fun_normalize/2` on types of the level of functions. -/
theorem normalize_T {H : Nat} (two : 2 ≤ H) {T : Term} (hT : DE (level t n).E T) (hlT : lh T < H) (a : Nat)
    {m : Nat} (hm : (level t n).K + 30 ≤ m) :
    NormRes t n H T a (Elixir.Module.Types.Descr.«fun_normalize/2» (D m) T (.integer a)) := by
  rcases hT with rfl | ⟨X, rfl, sX⟩
  · obtain ⟨res, run, cs⟩ := normalize_term (t := t) (n := n) two a
    rw [run m (by omega)]; exact cs
  have hX : DE (level t n).E (.map X) := Or.inr ⟨X, rfl, sX⟩
  rcases Classical.em (∃ R, mapLookup X (.atom "fun") = some (.tuple #[.atom "negation", R])) with neg | neg
  case inr =>
    obtain ⟨res, run, cs⟩ := normalize_noneg (by omega) hX hlT (fun R h => neg ⟨R, h⟩) a
    rw [run m (by omega)]; exact cs
  obtain ⟨R, hF⟩ := neg
  -- The negation is normalized as its intersection with the top function of the arity.
  obtain ⟨c, hc, rc, sc, lc⟩ := (ef_next t n).inter (top_de (t := t) (n := n) a) hX
  let top : Term := .map [(.atom "fun", .tuple #[.atom "union", .map [(.integer a, .atom "bdd_top")]])]
  -- The intersection holds no tuple, so it is a map, whose functions are those of the map of the arity `a`.
  obtain ⟨C, rfl, sC⟩ : ∃ C, c = .map C ∧ DescrC (FunA (level t n).E) (TField (level t n).E) (LF (level t n).E)
      (MField (level t n).E) C := by
    rcases hc with rfl | h
    · have := ((sc (tpt (t := t) (n := n) [])).mp (denD_term _)).1
      rw [denD_map] at this
      simp [tpt, mapLookup, dn_none] at this
    · exact h
  have inC : ∀ b g (vg : ∀ r ∈ g, FunSem.ValidRow b r), FunIn t n C b g ↔ b = a ∧ FunIn t n X b g := by
    intro b g vg
    rw [← denD_fpt b g vg, sc, denD_fpt b g vg, denD_fpt b g vg, funIn_top b a g]
  have cneg : ∀ R', mapLookup C (.atom "fun") ≠ some (.tuple #[.atom "negation", R']) := by
    intro R' h
    obtain ⟨M, rfl⟩ : ∃ M, R' = .map M := by
      rcases sC.fields "fun" _ h with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, fF⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> try (simp at e; done)
      obtain ⟨pos, M, e, -⟩ := fF
      simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e
      exact ⟨M, e.2⟩
    obtain ⟨b, hb⟩ := fresh_arities M
    have fC : FunIn t n C (max b (a + 1)) [] := by
      refine ⟨_, h, ?_⟩
      simp [arityOf, hb (max b (a + 1)) (by omega)]
    have := ((inC _ [] (by simp)).mp fC).1
    omega
  obtain ⟨res', run', cs'⟩ := normalize_noneg (H := H) (by omega) (Or.inr ⟨C, rfl, sC⟩)
    (lc H (by have := lh_top a; omega) hlT) cneg a
  have funX : ∀ g, (∀ r ∈ g, FunSem.ValidRow a r) → (FunT t n (.map C) a g ↔ FunT t n (.map X) a g) := by
    intro g vg
    constructor
    · rintro (h | ⟨Y, e, h⟩)
      · cases h
      · simp only [Term.map.injEq] at e; subst e; exact Or.inr ⟨X, rfl, ((inC a g vg).mp h).2⟩
    · rintro (h | ⟨Y, e, h⟩)
      · cases h
      · simp only [Term.map.injEq] at e; subst e; exact Or.inr ⟨C, rfl, (inC a g vg).mpr ⟨rfl, h⟩⟩
  -- The negation holds functions of arities it does not mention.
  have someFun : ∃ (b : Nat) (g : List (FunSem.Row (level t n).V)), (∀ r ∈ g, FunSem.ValidRow b r) ∧
      FunT t n (.map X) b g := by
    obtain ⟨M, rfl⟩ : ∃ M, R = .map M := by
      rcases sX.fields "fun" _ hF with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, fF⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> try (simp at e; done)
      obtain ⟨pos, M, e, -⟩ := fF
      simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e
      exact ⟨M, e.2⟩
    obtain ⟨b, hb⟩ := fresh_arities M
    exact ⟨b, [], by simp, Or.inr ⟨X, rfl, _, hF, by simp [arityOf, hb b (Nat.le_refl _)]⟩⟩
  rw [Elixir.Module.Types.Descr.«fun_normalize/2».eq_def]
  simp only [getMapKeys_single, hF, Option.toList, fun_arity_run, Lynx.Except.ok_bind, rc m (by omega),
    run' m (by omega)]
  rcases cs' with ⟨dom, Q, nQ, ne, hdom, sdom, rfl⟩ | ⟨dead, n3, -⟩
  · exact Or.inl ⟨dom, Q, nQ.congr funX, ne, hdom, sdom, by simp⟩
  · -- What the intersection fails with is returned, or a `:badarity` for `:badfun`.
    have notOk : ∀ w, (do
        let r ← res'
        match r with
        | .atom "badfun" => do
          let x ← Elixir.Module.Types.Descr.«fun_negation_arities/1» (D m) (.map X)
          Except.ok (Term.tuple #[.atom "badarity", .atom "negative", x])
        | o => Except.ok o) = .ok w → (∃ x y, w = .tuple #[.atom "badarity", x, y]) ∧ w ≠ .atom "badfun" := by
      intro w e
      cases hr : res' with
      | error err => simp [hr] at e
      | ok r =>
        simp only [hr, Lynx.Except.ok_bind] at e
        split at e
        · cases hz : Elixir.Module.Types.Descr.«fun_negation_arities/1» (D m) (.map X) <;> simp [hz] at e
          subst e
          exact ⟨⟨_, _, rfl⟩, fun h => by cases h⟩
        · simp only [Except.ok.injEq] at e
          subst e
          rename_i nb
          rcases n3 r hr with h | h
          · exact absurd h nb
          · exact ⟨h, nb⟩
    refine Or.inr ⟨fun g vg h => dead g vg ((funX g vg).mpr h), fun w e => Or.inr (notOk _ e).1,
      ⟨fun e => absurd rfl (notOk _ e).2, fun h => ?_⟩⟩
    obtain ⟨b, g, vg, hg⟩ := someFun
    exact absurd hg (h b g vg)

/-- The dynamic type of a type of the level: no lower bound, and the type as upper bound. -/
theorem dyn_gd {c : Term} (hc : DE (level t n).E c) :
    GD t n (.map [(.atom "dynamic", c)]) ∧ lower (.map [(.atom "dynamic", c)]) = .map [] ∧
      upper (.map [(.atom "dynamic", c)]) = c := by
  have lo : lower (.map [(.atom "dynamic", c)]) = .map [] := by
    simp [lower, rmDyn]
  have up : upper (.map [(.atom "dynamic", c)]) = c := by simp [upper, mapLookup]
  refine ⟨⟨Or.inr ⟨_, c, rfl, by simp [mapLookup], de_tc hc, ?_, fun v hv => ?_⟩, ?_, ?_⟩, lo, up⟩
  · simp only [rmDyn, List.filter_cons]; simp; exact descrC_nil
  · exfalso
    rw [denD_map] at hv
    by_cases e : v.1.1 = "dynamic"
    · have := v.2.1; rw [e] at this; simp [names] at this
    · simp [mapLookup, e, dn_none] at hv
  · rw [lo]; exact de_none
  · rw [up]; exact hc

/-- The extended domain `fun_normalize_both/3` builds: the dynamic domain united with a dynamic static domain. -/
theorem dom_union {dd sd : Term} (hdd : DE (level t n).E dd) (hsd : DE (level t n).E sd) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) :
    ∃ c, Elixir.Module.Types.Descr.«bare_union/2» (D m) dd (.map [(.atom "dynamic", sd)]) = .ok c ∧ GD t n c ∧
      (∀ v : PN t n, denD (lower c) v ↔ denD dd v) ∧ (∀ v : PN t n, denD (upper c) v ↔ denD dd v ∨ denD sd v) := by
  obtain ⟨gdd, ldd, udd⟩ := de_gd hdd
  obtain ⟨gs, ls, us⟩ := dyn_gd hsd
  obtain ⟨c, run, gc, lc, uc⟩ := gd_union gdd gs hm
  refine ⟨c, run, gc, fun v => ?_, fun v => ?_⟩
  · rw [lc, ldd, ls]; exact ⟨fun h => h.elim id fun h => absurd h (denN_nil v), Or.inl⟩
  · rw [uc, udd, us]

/-- Argument lists every line of `Q` covers. -/
def Covers (t : Term) (n : Nat) (Q : List (List (Term × List Term × Term))) (x : List (level t n).V) : Prop :=
  ∀ q ∈ Q, ∃ p ∈ semP (level t n).den q, FunSem.InDomR p.1 x

/-- Domains of tuples: types of the level holding tuples only, whose tuples are those of a property. -/
def TupDom (t : Term) (n : Nat) (dom : Term) (P : List (level t n).V → Prop) : Prop :=
  DE (level t n).E dom ∧ (∀ v : PN t n, denD dom v → v.1.1 = "tuple") ∧ ∀ w, denD dom (tpt (t := t) (n := n) w) ↔ P w

/-- What `fun_normalize/3` answers for a function whose static and dynamic parts are `Fs` and `Fd`, at the arity
`a`: the lines of both parts and their extended domain when the static part holds functions of that arity only, or
the dynamic lines with any domain when the static part holds no function, or otherwise a failure that is neither
`{:ok, _}` nor `{:ok, _, _, _}`, as the static part holds functions of other arities or the dynamic part none of
that arity. -/
def NormBoth (t : Term) (n H : Nat) (Fs Fd : Term) (a : Nat) (nb : Except Exception Term) : Prop :=
  (∃ dom Qs Qd, NormP (EB (level t n).E H) (level t n).den a (FunT t n Fs a) Qs ∧ Qs ≠ [] ∧
      NormP (EB (level t n).E H) (level t n).den a (FunT t n Fd a) Qd ∧ Qd ≠ [] ∧ GD t n dom ∧
      TupDom t n (upper dom) (fun w => Covers t n Qs w ∨ Covers t n Qd w) ∧
      (∀ (b : Nat) (g : List (FunSem.Row (level t n).V)), (∀ r ∈ g, FunSem.ValidRow b r) → b ≠ a → ¬FunT t n Fs b g) ∧
      nb = .ok (.tuple #[.atom "ok", dom, Term.list (Qs.reverse.map encP), Term.list (Qd.reverse.map encP)])) ∨
    (∃ dom Qd, (∀ (b : Nat) (g : List (FunSem.Row (level t n).V)), (∀ r ∈ g, FunSem.ValidRow b r) → ¬FunT t n Fs b g) ∧
      NormP (EB (level t n).E H) (level t n).den a (FunT t n Fd a) Qd ∧ Qd ≠ [] ∧ GD t n dom ∧
      (∀ v : PN t n, denD (upper dom) v) ∧
      nb = .ok (.tuple #[.atom "ok", dom, .nil, Term.list (Qd.reverse.map encP)])) ∨
    ((∀ x, nb ≠ .ok (.tuple #[.atom "ok", x])) ∧ (∀ x y z, nb ≠ .ok (.tuple #[.atom "ok", x, y, z])) ∧
      ((∃ (b : Nat) (g : List (FunSem.Row (level t n).V)), (∀ r ∈ g, FunSem.ValidRow b r) ∧ b ≠ a ∧ FunT t n Fs b g) ∨
        ∀ g : List (FunSem.Row (level t n).V), (∀ r ∈ g, FunSem.ValidRow a r) → ¬FunT t n Fd a g))

theorem tupDom_of {H : Nat} {dd : Term} {P : List (level t n).V → Prop} (h : DomA (level t n).E H dd)
    (sem : ∀ x, ddenA (level t n).E (level t n).den dd x ↔ P x) : TupDom t n dd P := by
  refine ⟨domA_de h, fun v hv => ?_, fun w => ?_⟩
  · obtain ⟨⟨D, e, -, only⟩, -⟩ := h
    subst e
    rw [denD_map] at hv
    cases hl : mapLookup D (.atom v.1.1) with
    | none => rw [hl] at hv; simp [dn_none] at hv
    | some _ =>
      have := only _ (by rw [hl]; rfl)
      simpa using this
  · obtain ⟨-, D, rfl, -, -⟩ := h
    rw [← ddenA_tpt]; exact sem w

/-- Functions of a map of a union of arities, by the BDD of each arity. -/
theorem funT_union {X R : List (Term × Term)} (hF : mapLookup X (.atom "fun") = some (.tuple #[.atom "union", .map R]))
    (a : Nat) (g : List (FunSem.Row (level t n).V)) :
    FunT t n (.map X) a g ↔ evalR R (.integer a) (valF (level t n).E (level t n).den g) = Bool.true := by
  rw [← funIn_union hF]
  exact ⟨fun h => h.elim (fun h => by cases h) fun ⟨Y, e, h⟩ => by simp only [Term.map.injEq] at e; subst e; exact h,
    fun h => Or.inr ⟨X, rfl, h⟩⟩

/-- `fun_normalize_both/3` once the static part normalizes to `:badfun`: the dynamic part alone. -/
theorem both_after_badfun {H : Nat} {Fs Fd : Term} {a m : Nat} (hm : (level t n).K + 25 ≤ m)
    (noS : ∀ (b : Nat) (g : List (FunSem.Row (level t n).V)), (∀ r ∈ g, FunSem.ValidRow b r) → ¬FunT t n Fs b g)
    (rD : NormRes t n H Fd a (Elixir.Module.Types.Descr.«fun_normalize/2» (D m) Fd (.integer a))) :
    NormBoth t n H Fs Fd a (do
      let r ← Elixir.Module.Types.Descr.«fun_normalize/2» (D m) Fd (.integer a)
      match r with
      | .tuple ⟨[.atom "ok", dd, da]⟩ => do
        let x ← Elixir.Module.Types.Descr.«dynamic/0»
        let y ← Elixir.Module.Types.Descr.«bare_union/2» (D m) dd x
        Except.ok (Term.tuple #[.atom "ok", y, .nil, da])
      | e => Except.ok e) := by
  rcases rD with ⟨dd, Qd, nQd, neQd, hdd, sdd, rd⟩ | ⟨deadD, shD, -⟩
  · rw [rd]
    obtain ⟨dom, ru, gd, -, ud⟩ := dom_union (domA_de hdd) (Or.inl rfl : DE (level t n).E (.atom "term"))
      (m := m) (by omega)
    refine Or.inr (Or.inl ⟨dom, Qd, noS, nQd, neQd, gd, fun v => (ud v).mpr (Or.inr (denD_term v)), ?_⟩)
    simp [Elixir.Module.Types.Descr.«dynamic/0», ru]
  · have pass : ∀ w, (do
        let r ← Elixir.Module.Types.Descr.«fun_normalize/2» (D m) Fd (.integer a)
        match r with
        | .tuple ⟨[.atom "ok", dd, da]⟩ => do
          let x ← Elixir.Module.Types.Descr.«dynamic/0»
          let y ← Elixir.Module.Types.Descr.«bare_union/2» (D m) dd x
          Except.ok (Term.tuple #[.atom "ok", y, .nil, da])
        | e => Except.ok e) = .ok w → w = .atom "badfun" ∨ ∃ x y, w = .tuple #[.atom "badarity", x, y] := by
      intro w e
      cases hr : Elixir.Module.Types.Descr.«fun_normalize/2» (D m) Fd (.integer a) with
      | error err => simp [hr] at e
      | ok r =>
        rcases shD r hr with rfl | ⟨x, y, rfl⟩ <;> simp [hr] at e <;> subst e
        · exact Or.inl rfl
        · exact Or.inr ⟨x, y, rfl⟩
    refine Or.inr (Or.inr ⟨fun x e => ?_, fun x y z e => ?_, Or.inr deadD⟩)
    · rcases pass _ e with h | ⟨_, _, h⟩ <;> simp at h
    · rcases pass _ e with h | ⟨_, _, h⟩ <;> simp at h

theorem normalize_both_g {H : Nat} (two : 2 ≤ H) {Xs : List (Term × Term)} (hXs : DE (level t n).E (.map Xs))
    (lXs : lh (.map Xs) < H) {Fd : Term} (hFd : DE (level t n).E Fd) (lFd : lh Fd < H)
    (inc : ∀ b g, (∀ r ∈ g, FunSem.ValidRow b r) → FunT t n (.map Xs) b g → FunT t n Fd b g)
    (a : Nat) {m : Nat} (hm : (level t n).K + 40 ≤ m) :
    NormBoth t n H (.map Xs) Fd a
      (Elixir.Module.Types.Descr.«fun_normalize_both/3» (D m) (.map Xs) Fd (.integer a)) := by
  have sX := de_map hXs
  have fdNil : Erlang.erlang.«==/2» Fd (.atom "nil") = .ok (.atom "false") := by
    rcases hFd with rfl | ⟨Y, rfl, -⟩ <;> simp [Erlang.erlang.«==/2»]
  have rD := normalize_T two hFd lFd a (m := m) (by omega)
  cases hlk : mapLookup Xs (.atom "fun") with
  | none =>
    have rS : Elixir.Module.Types.Descr.«fun_normalize/2» (D m) (.map Xs) (.integer a) = .ok (.atom "badfun") := by
      rw [Elixir.Module.Types.Descr.«fun_normalize/2».eq_def]; simp [getMapKeys_single, hlk]
    have noS : ∀ (b : Nat) (g : List (FunSem.Row (level t n).V)), (∀ r ∈ g, FunSem.ValidRow b r) →
        ¬FunT t n (.map Xs) b g := by
      intro b g _ h
      rcases h with h | ⟨Y, e, F', hF', -⟩
      · cases h
      · simp only [Term.map.injEq] at e; subst e; rw [hlk] at hF'; cases hF'
    rw [Elixir.Module.Types.Descr.«fun_normalize_both/3».eq_def]
    simp [getMapKeys_single, hlk, rS, fdNil]
    exact both_after_badfun (by omega) noS rD
  | some F =>
    rcases sX.fields "fun" F hlk with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, fF⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> try (simp at e; done)
    obtain ⟨pos, R, rfl, -, bR, kR⟩ := fF
    cases pos
    case false =>
      -- A negation holds functions of the arities it does not mention.
      simp only [Bool.false_eq_true, ite_false] at hlk
      obtain ⟨b, hb⟩ := fresh_arities R
      have other : FunT t n (.map Xs) (max b (a + 1)) [] :=
        Or.inr ⟨Xs, rfl, _, hlk, by simp [arityOf, hb (max b (a + 1)) (by omega)]⟩
      have shape : ∀ w, Elixir.Module.Types.Descr.«fun_normalize_both/3» (D m) (.map Xs) Fd (.integer a) = .ok w →
          ∃ x, w = .tuple #[.atom "badarity", .atom "negative", x] := by
        intro w e
        rw [Elixir.Module.Types.Descr.«fun_normalize_both/3».eq_def] at e
        simp [getMapKeys_single, hlk] at e
        cases hz : Elixir.Module.Types.Descr.«fun_negation_arities/1» (D m) (.map Xs) <;> simp [hz] at e
        exact ⟨_, e.symm⟩
      refine Or.inr (Or.inr ⟨fun x e => ?_, fun x y z e => ?_, Or.inl ⟨_, [], by simp, by omega, other⟩⟩)
      · obtain ⟨_, h⟩ := shape _ e; simp at h
      · obtain ⟨_, h⟩ := shape _ e; simp at h
    simp only [ite_true] at hlk
    have hR := arityBdds_of lXs hlk bR kR
    have fe : FunElem (EB (level t n).E H) (level t n).den ((level t n).K + 6) (.map []) :=
      (felem (level t n).ef (level t n).ef.subc (by omega) (safeN_nil H)).mono (by omega)
    have fd := fdom (level t n).ef (H := H) (by omega) (safeT_nil (H + 1))
    have cg : DenCongr (level t n).E (level t n).den := (level t n).ef.congrE
    let rest := R.filter fun e => !decide (Term.compareExact (Term.fuel (.integer a) e.1) (.integer a) e.1 = .eq)
    obtain ⟨l, rl, sl⟩ := nonempty_arities_run fe fd cg (fun x h => h.1) (arityBdds_drop hR a)
    have restEq : ∀ (b : Nat) ρ, b ≠ a → evalR rest (.integer b) ρ = evalR R (.integer b) ρ := by
      intro b ρ hb
      simp only [evalR, rest, lookup_drop, Term.integer.injEq]
      rw [ite_eq_right (by omega)]
    have rS := normalize_T two hXs lXs a (m := m) (by omega)
    rcases rS with ⟨sd, Qs, nQs, neQs, hsd, ssd, run⟩ | ⟨deadS, shS, bfS⟩
    · -- The static part holds functions of the arity.
      obtain ⟨q₀, mq₀⟩ := List.exists_mem_of_ne_nil Qs neQs
      obtain ⟨N₀, g₀, vg₀, allP₀, noN₀, live0⟩ := nQs.witness mq₀
      have live₀ := live0 g₀ vg₀ allP₀ noN₀
      obtain ⟨b, hb⟩ : ∃ b, mapLookup R (.integer a) = some b := by
        have := (funT_union hlk a g₀).mp live₀
        cases h : mapLookup R (.integer a) with
        | none => simp [evalR, h] at this
        | some b => exact ⟨b, rfl⟩
      have other : Elixir.Module.Types.Descr.«fun_other_non_empty_arities/2» (D m) (.map Xs) (.integer a) =
          .ok (Term.list l) := by
        unfold Elixir.Module.Types.Descr.«fun_other_non_empty_arities/2»
        simp [getMapKeys_single, hlk, Erlang.maps.«take/2», hb]
        exact rl m (by omega)
      cases l with
      | cons o os =>
        -- Some other arity holds functions.
        obtain ⟨b', g, vg, hb', hg⟩ : ∃ (b' : Nat) (g : List (FunSem.Row (level t n).V)), (∀ r ∈ g, FunSem.ValidRow b' r) ∧
            b' ≠ a ∧ evalR R (.integer b') (valF (level t n).E (level t n).den g) = Bool.true := by
          refine Classical.byContradiction fun none => ?_
          have : o :: os = [] := sl.mpr fun b' g vg => by
            by_cases e : b' = a
            · subst e; simp [evalR, lookup_drop]
            · rw [restEq b' _ e]
              cases h : evalR R (.integer b') (valF (level t n).E (level t n).den g)
              · rfl
              · exact absurd ⟨b', g, vg, e, h⟩ none
          cases this
        have nb : Elixir.Module.Types.Descr.«fun_normalize_both/3» (D m) (.map Xs) Fd (.integer a) =
            .ok (.tuple #[.atom "badarity", .atom "positive", .cons (.integer a) (Term.list (o :: os))]) := by
          rw [Elixir.Module.Types.Descr.«fun_normalize_both/3».eq_def]
          simp [getMapKeys_single, hlk, run, other, Term.list]
        rw [nb]
        exact Or.inr (Or.inr ⟨fun x e => by simp at e, fun x y z e => by simp at e,
          Or.inl ⟨b', g, vg, hb', (funT_union hlk b' g).mpr hg⟩⟩)
      | nil =>
        have noOther : ∀ (b' : Nat) (g : List (FunSem.Row (level t n).V)), (∀ r ∈ g, FunSem.ValidRow b' r) → b' ≠ a →
            ¬FunT t n (.map Xs) b' g := by
          intro b' g vg hb' h
          rw [funT_union hlk, ← restEq b' _ hb', sl.mp rfl b' g vg] at h
          cases h
        rcases rD with ⟨dd, Qd, nQd, neQd, hdd, sdd, rd⟩ | ⟨deadD, -, -⟩
        · obtain ⟨dom, ru, gd, -, ud⟩ := dom_union (domA_de hdd) (domA_de hsd) (m := m) (by omega)
          have sdStat : mapLookup (match sd with | .map Z => Z | _ => []) (.atom "dynamic") = none ∧
              ∃ Z, sd = .map Z := by
            obtain ⟨-, Z, rfl, sZ, -⟩ := hsd
            exact ⟨sZ.static, Z, rfl⟩
          obtain ⟨sdS, Z, rfl⟩ := sdStat
          have td := tupDom_of hdd sdd
          have ts := tupDom_of hsd ssd
          refine Or.inl ⟨dom, Qs, Qd, nQs, neQs, nQd, neQd, gd, ⟨gd.2.2, fun v hv => ?_, fun w => ?_⟩, noOther, ?_⟩
          · rcases (ud v).mp hv with h | h
            · exact td.2.1 v h
            · exact ts.2.1 v h
          · rw [ud, td.2.2, ts.2.2]; exact or_comm
          · rw [Elixir.Module.Types.Descr.«fun_normalize_both/3».eq_def]
            simp [getMapKeys_single, hlk, run, other, Term.list, fdNil, rd, sdS, ru]
        · exact absurd (inc a g₀ vg₀ live₀) (deadD g₀ vg₀)
    · -- The static part holds no function of the arity: some other arity, or none at all.
      have otherArity : ¬Elixir.Module.Types.Descr.«fun_normalize/2» (D m) (.map Xs) (.integer a) = .ok (.atom "badfun") →
          ∃ (b : Nat) (g : List (FunSem.Row (level t n).V)), (∀ r ∈ g, FunSem.ValidRow b r) ∧ b ≠ a ∧
            FunT t n (.map Xs) b g := by
        intro nbf
        rw [bfS] at nbf
        obtain ⟨b, hb⟩ := Classical.not_forall.mp nbf
        obtain ⟨g, hg⟩ := Classical.not_forall.mp hb
        obtain ⟨vg, h⟩ := Classical.not_imp.mp hg
        have h := Classical.not_not.mp h
        refine ⟨b, g, vg, fun e => ?_, h⟩
        subst e
        exact deadS g vg h
      cases hr : Elixir.Module.Types.Descr.«fun_normalize/2» (D m) (.map Xs) (.integer a) with
      | error err =>
        have nb : Elixir.Module.Types.Descr.«fun_normalize_both/3» (D m) (.map Xs) Fd (.integer a) = .error err := by
          rw [Elixir.Module.Types.Descr.«fun_normalize_both/3».eq_def]
          simp [getMapKeys_single, hlk, hr]
        rw [nb]
        refine Or.inr (Or.inr ⟨fun x e => ?_, fun x y z e => ?_, Or.inl (otherArity ?_)⟩)
        · cases e
        · cases e
        · rw [hr]; intro e; cases e
      | ok w =>
        rcases shS w hr with rfl | ⟨x, y, rfl⟩
        · rw [Elixir.Module.Types.Descr.«fun_normalize_both/3».eq_def]
          simp [getMapKeys_single, hlk, hr, fdNil]
          exact both_after_badfun (by omega) (bfS.mp hr) rD
        · have nb : Elixir.Module.Types.Descr.«fun_normalize_both/3» (D m) (.map Xs) Fd (.integer a) =
              .ok (.tuple #[.atom "badarity", x, y]) := by
            rw [Elixir.Module.Types.Descr.«fun_normalize_both/3».eq_def]
            simp [getMapKeys_single, hlk, hr]
          rw [nb]
          refine Or.inr (Or.inr ⟨fun x e => ?_, fun x y z e => ?_, Or.inl (otherArity ?_)⟩)
          · simp at e
          · simp at e
          · rw [hr]; intro e; simp at e

theorem linesL_inj {A B : List (List (Term × List Term × Term))}
    (h : Term.list (A.reverse.map encP) = Term.list (B.reverse.map encP)) : A = B := by
  have e := list_inj h
  have inj : ∀ {A B : List (List (Term × List Term × Term))}, A.map encP = B.map encP → A = B := by
    intro A; induction A with
    | nil => intro B h; cases B <;> simp_all
    | cons x xs ih =>
      intro B h; cases B with
      | nil => simp at h
      | cons y ys => simp only [List.map_cons, List.cons.injEq] at h; rw [encP_inj h.1, ih h.2]
  simpa using inj e

/-- `fun_normalize_both/3` on a static function: its own lines, and its domain as a static one, the same lines for
both parts. -/
theorem normalize_both_s {H : Nat} (two : 2 ≤ H) {X : List (Term × Term)} (hX : DE (level t n).E (.map X))
    (lX : lh (.map X) < H) (a : Nat) {m : Nat} (hm : (level t n).K + 40 ≤ m) :
    NormBoth t n H (.map X) (.map X) a
        (Elixir.Module.Types.Descr.«fun_normalize_both/3» (D m) (.map X) (.atom "nil") (.integer a)) ∧
      ∀ (dom : Term) (Qs Qd : List (List (Term × List Term × Term))),
        Elixir.Module.Types.Descr.«fun_normalize_both/3» (D m) (.map X) (.atom "nil") (.integer a) =
        .ok (.tuple #[.atom "ok", dom, Term.list (Qs.reverse.map encP), Term.list (Qd.reverse.map encP)]) → Qs = Qd := by
  have sX := de_map hX
  cases hlk : mapLookup X (.atom "fun") with
  | none =>
    have nb : Elixir.Module.Types.Descr.«fun_normalize_both/3» (D m) (.map X) (.atom "nil") (.integer a) =
        .ok (.atom "badfun") := by
      have rS : Elixir.Module.Types.Descr.«fun_normalize/2» (D m) (.map X) (.integer a) = .ok (.atom "badfun") := by
        rw [Elixir.Module.Types.Descr.«fun_normalize/2».eq_def]; simp [getMapKeys_single, hlk]
      rw [Elixir.Module.Types.Descr.«fun_normalize_both/3».eq_def]
      simp [getMapKeys_single, hlk, rS, Erlang.erlang.«==/2»]
    rw [nb]
    refine ⟨Or.inr (Or.inr ⟨fun x e => ?_, fun x y z e => ?_, Or.inr fun g _ h => ?_⟩), fun _ _ _ e => ?_⟩
    · simp at e
    · simp at e
    rotate_left
    · simp at e
    · rcases h with h | ⟨Y, e, F, hF, -⟩
      · cases h
      · simp only [Term.map.injEq] at e; subst e; rw [hlk] at hF; cases hF
  | some F =>
    rcases sX.fields "fun" F hlk with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, fF⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> try (simp at e; done)
    obtain ⟨pos, R, rfl, -, bR, kR⟩ := fF
    cases pos
    case false =>
      simp only [Bool.false_eq_true, ite_false] at hlk
      obtain ⟨b, hb⟩ := fresh_arities R
      have other : FunT t n (.map X) (max b (a + 1)) [] :=
        Or.inr ⟨X, rfl, _, hlk, by simp [arityOf, hb (max b (a + 1)) (by omega)]⟩
      have shape : ∀ w, Elixir.Module.Types.Descr.«fun_normalize_both/3» (D m) (.map X) (.atom "nil") (.integer a) =
          .ok w → ∃ x, w = .tuple #[.atom "badarity", .atom "negative", x] := by
        intro w e
        rw [Elixir.Module.Types.Descr.«fun_normalize_both/3».eq_def] at e
        simp [getMapKeys_single, hlk] at e
        cases hz : Elixir.Module.Types.Descr.«fun_negation_arities/1» (D m) (.map X) <;> simp [hz] at e
        exact ⟨_, e.symm⟩
      refine ⟨Or.inr (Or.inr ⟨fun x e => ?_, fun x y z e => ?_, Or.inl ⟨_, [], by simp, by omega, other⟩⟩),
        fun _ _ _ e => ?_⟩
      · obtain ⟨_, h⟩ := shape _ e; simp at h
      · obtain ⟨_, h⟩ := shape _ e; simp at h
      · obtain ⟨_, h⟩ := shape _ e; simp at h
    simp only [ite_true] at hlk
    have hR := arityBdds_of lX hlk bR kR
    have fe : FunElem (EB (level t n).E H) (level t n).den ((level t n).K + 6) (.map []) :=
      (felem (level t n).ef (level t n).ef.subc (by omega) (safeN_nil H)).mono (by omega)
    have fd := fdom (level t n).ef (H := H) (by omega) (safeT_nil (H + 1))
    have cg : DenCongr (level t n).E (level t n).den := (level t n).ef.congrE
    obtain ⟨nb, rnb, cs⟩ := normalize_both_union fe fd cg (fun x h => h.1) hlk hR a
    rw [rnb m (by omega)]
    rcases cs with ⟨b, dom, Q, hb, nQ, neQ, hdom, sdom, others, rfl⟩ | ⟨n2, n4, -, why⟩
    · have nP : NormP (EB (level t n).E H) (level t n).den a (FunT t n (.map X) a) Q :=
        nQ.toP.congr fun g _ => by rw [funT_union hlk]; simp [evalR, hb]
      obtain ⟨gd, -, ud⟩ := de_gd (domA_de hdom)
      have td := tupDom_of hdom sdom
      refine ⟨Or.inl ⟨dom, Q, Q, nP, neQ, nP, neQ, gd, ?_, fun b g vg hb' h => ?_, rfl⟩, fun _ Qs Qd e => ?_⟩
      rotate_left 2
      · simp only [Except.ok.injEq, Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e
        exact (linesL_inj e.2.2.1).symm.trans (linesL_inj e.2.2.2.1)
      · rw [ud]
        exact ⟨td.1, td.2.1, fun w => (td.2.2 w).trans (or_self_iff).symm⟩
      · rw [funT_union hlk, others b g vg hb'] at h; cases h
    · refine ⟨Or.inr (Or.inr ⟨fun x e => n2 x (Except.ok.inj e), fun x y z e => n4 x y z (Except.ok.inj e), ?_⟩),
        fun _ _ _ e => absurd (Except.ok.inj e) (n4 _ _ _)⟩
      rcases why with dead | ⟨b, g, vg, hb, h⟩
      · exact Or.inr fun g vg h => by rw [funT_union hlk, dead g vg] at h; cases h
      · exact Or.inl ⟨b, g, vg, hb, (funT_union hlk b g).mpr h⟩

end

/-! Gradual arguments, of the level below the functions. -/

section
variable {t : Term} {d : Nat}

theorem gd_ga {a : Term} (h : GD t d a) : GA a := h.1.shape

theorem any_empty_g {args : List Term} (h : ∀ a ∈ args, GD t d a) {m : Nat} (hm : (level t d).K + 23 ≤ m) :
    Erlang.lists.«any/2» (D (m + 1)) (.function false "Elixir.Module.Types.Descr" "empty?" 1 #[]) (Term.list args) =
      .ok (boolAtom (args.any fun a => bp (∀ v : PN t d, ¬denD (upper a) v))) :=
  any_list _ _ _ _ _ _ fun a ma => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:empty?/1».pure, empty_upper _ (h a ma).1,
      next_empty (h a ma).2.2 hm]

theorem map_upper_g {args : List Term} (h : ∀ a ∈ args, GD t d a) (m : Nat) :
    Erlang.lists.«map/2» (D (m + 1)) (.function false "Elixir.Module.Types.Descr" "upper_bound" 1 #[]) (Term.list args) =
      .ok (Term.list (args.map upper)) :=
  map_list _ _ _ _ upper _ fun a ma => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:upper_bound/1».pure]
    exact upper_bound_run (h a ma).1.ub

theorem map_lower_g {args : List Term} (h : ∀ a ∈ args, GD t d a) (m : Nat) :
    Erlang.lists.«map/2» (D (m + 1)) (.function false "Elixir.Module.Types.Descr" "lower_bound" 1 #[]) (Term.list args) =
      .ok (Term.list (args.map lower)) :=
  map_list _ _ _ _ lower _ fun a ma => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:lower_bound/1».pure]
    exact lower_bound_run (h a ma).1.shape

theorem all_static_g {args : List Term} (h : ∀ a ∈ args, GD t d a) (m : Nat) :
    Erlang.lists.«all/2» (D (m + 1)) (.function false "Elixir.Module.Types.Descr" "-fun_apply_with_strategy/4-fun-0-" 1 #[])
      (Term.list args) = .ok (boolAtom (!args.any isDynB)) := by
  rw [all_list _ _ _ _ (fun a => !isDynB a) _ fun a ma => ?_]
  · congr 2
    induction args with
    | nil => rfl
    | cons x xs ih => simp only [List.all_cons, List.any_cons, Bool.not_or]; rw [ih (fun a ma => h a (List.mem_cons_of_mem _ ma))]
  rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_apply_with_strategy/4-fun-0-/1».pure]
  rcases (h a ma).1.shape with rfl | ⟨X, rfl⟩
  · rfl
  · cases e : mapLookup X (.atom "dynamic") <;>
      simp [Elixir.Module.Types.Descr.«-fun_apply_with_strategy/4-fun-0-/1», unfold_map, Erlang.erlang.«is_map_key/2»,
        any_key, e, Erlang.erlang.«not/1», boolAtom, isDynB]

end

section
variable {t : Term} {n : Nat}

/-- Tuple points are the points of tuples of values, for every type of the level. -/
theorem pt_tuple_de (v : PN t n) (h : v.1.1 = "tuple") :
    ∃ w, ∀ Z, DE (level t n).E Z → (denD Z v ↔ denD Z (tpt (t := t) (n := n) w)) := by
  obtain ⟨w, hw⟩ := pt_tuple v h
  refine ⟨w, fun Z hZ => ?_⟩
  rcases hZ with rfl | ⟨X, rfl, -⟩
  · exact ⟨fun _ => denD_term _, fun _ => denD_term _⟩
  · rw [hw X, denD_tpt]

/-- Subtyping of tuple domains compares their tuples. -/
theorem tupDom_sub {A B : Term} {P Q : List (level t n).V → Prop} (hA : TupDom t n A P) (dB : DE (level t n).E B)
    (sB : ∀ w, denD B (tpt (t := t) (n := n) w) ↔ Q w) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    Elixir.Module.Types.Descr.«subtype?/2» (D m) A B = .ok (boolAtom (bp (∀ w, P w → Q w))) := by
  have hB : DE (level t n).E B ∧ True ∧ ∀ w, denD B (tpt (t := t) (n := n) w) ↔ Q w := ⟨dB, trivial, sB⟩
  rw [next_sub hA.1 hB.1 hm]
  refine congrArg (fun x => Except.ok (boolAtom x)) (bp_congr ⟨fun h w hw => (hB.2.2 w).mp (h _ ((hA.2.2 w).mpr hw)),
    fun h v hv => ?_⟩)
  obtain ⟨w, hw⟩ := pt_tuple v (hA.2.1 v hv)
  rcases hA.1 with rfl | ⟨X, rfl, -⟩
  · exact absurd (hA.2.1 (fpt 0 [] (by simp)) (denD_term _)) (by simp [fpt])
  rcases hB.1 with rfl | ⟨Y, rfl, -⟩
  · exact denD_term v
  rw [hw] at hv ⊢
  rw [← denD_tpt] at hv ⊢
  exact (hB.2.2 w).mpr (h w ((hA.2.2 w).mp hv))

/-- The tuple of types of the level below, as a domain. -/
theorem tup_dom {H : Nat} (one : 1 ≤ H) {Z : List Term} (hZ : ∀ z ∈ Z, (level t n).E z ∧ lh z < H) :
    ∃ T, Elixir.Module.Types.Descr.«args_to_domain/1» (Term.list Z) = .ok T ∧
      TupDom t n T (fun w => FunSem.InDomR (Z.map (level t n).den) w) ∧ DomA (level t n).E H T := by
  have fd := fdom (level t n).ef one (safeT_nil (H + 1)) (H := H)
  obtain ⟨T, hT, run, sem⟩ := fd.dom Z fun z mz => hZ z mz
  exact ⟨T, run, tupDom_of hT sem, hT⟩

/-- The domain of static arguments is the tuple of them, with the key of its leaf. -/
theorem args_domain_static {l : List Term} (hl : ∀ e ∈ l, GA e) (st : ∀ e ∈ l, isDynB e = Bool.false) {k : Int}
    (leaf : Elixir.Module.Types.Descr.«bdd_leaf_new/2» (.atom "closed") (Term.list l) =
      .ok (.tuple #[.integer k, .atom "closed", Term.list l])) :
    Elixir.Module.Types.Descr.«args_to_domain/1» (Term.list l) =
      .ok (.map [(.atom "tuple", .tuple #[.integer k, .atom "closed", Term.list l])]) := by
  have up : l.map upper = l := by
    refine (List.map_congr_left fun e me => ?_).trans (List.map_id l)
    rcases hl e me with rfl | ⟨X, rfl⟩
    · rfl
    · have := st _ me
      simp only [isDynB, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at this
      simp [upper, this]
  obtain ⟨kU, kL, leafU, leafL, run⟩ := args_domain_g l hl
  have nd : l.any isDynB = Bool.false := List.any_eq_false.mpr fun e me h => by rw [st e me] at h; cases h
  rw [up] at leafU
  rw [leaf] at leafU
  simp only [Except.ok.injEq, Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, Term.integer.injEq] at leafU
  rw [run, nd, up, leafU.1]
  rfl

end

section
variable {t : Term} {d : Nat}

theorem inDomR_mem {V : Type} {den : Term → V → Prop} : ∀ (Z : List Term) (w : List V),
    FunSem.InDomR (Z.map den) w → ∀ z ∈ Z, ∃ v, den z v
  | [], _, _, z, mz => by simp at mz
  | z' :: Z, v :: w, h, z, mz => by
    rcases List.mem_cons.mp mz with rfl | mz
    · exact ⟨v, h.1⟩
    · exact inDomR_mem Z w h.2 z mz
  | _ :: _, [], h, _, _ => h.elim

theorem de_ga {a : Term} (h : DE (level t d).E a) : GA a ∧ isDynB a = Bool.false := by
  rcases h with rfl | ⟨X, rfl, sX⟩
  · exact ⟨Or.inl rfl, rfl⟩
  · exact ⟨Or.inr ⟨X, rfl⟩, by simp [isDynB, sX.static]⟩

/-- The domain of gradual arguments, as a gradual type of the level of functions: its upper bound holds the tuples of
their upper bounds, and its lower bound the tuples of their lower bounds. -/
theorem argsdom_sem {H : Nat} (one : 1 ≤ H) {args : List Term} (hargs : ∀ a ∈ args, GD t d a)
    (hl : ∀ a ∈ args, lh (upper a) < H ∧ lh (lower a) < H) :
    ∃ A, Elixir.Module.Types.Descr.«args_to_domain/1» (Term.list args) = .ok A ∧ GC (level t (d + 1)) A ∧
      DE (level t (d + 1)).E (lower A) ∧
      TupDom t (d + 1) (upper A) (fun w => FunSem.InDomR ((args.map upper).map (level t (d + 1)).den) w) ∧
      TupDom t (d + 1) (lower A) (fun w => FunSem.InDomR ((args.map lower).map (level t (d + 1)).den) w) ∧
      ∃ X, A = .map X ∧ (mapLookup X (.atom "dynamic") = none → args.any isDynB = Bool.false) := by
  have gaArgs : ∀ e ∈ args, GA e := fun e me => gd_ga (hargs e me)
  obtain ⟨kU, kL, leafU, leafL, run⟩ := args_domain_g args gaArgs
  -- The tuples of the upper and of the lower bounds.
  have uE : ∀ z ∈ args.map upper, (level t (d + 1)).E z ∧ lh z < H := by
    intro z mz; obtain ⟨a, ma, rfl⟩ := List.mem_map.mp mz; exact ⟨Or.inl (hargs a ma).2.2, (hl a ma).1⟩
  have lE : ∀ z ∈ args.map lower, (level t (d + 1)).E z ∧ lh z < H := by
    intro z mz; obtain ⟨a, ma, rfl⟩ := List.mem_map.mp mz; exact ⟨Or.inl (hargs a ma).2.1, (hl a ma).2⟩
  have uS : ∀ z ∈ args.map upper, GA z ∧ isDynB z = Bool.false := by
    intro z mz; obtain ⟨a, ma, rfl⟩ := List.mem_map.mp mz; exact de_ga (hargs a ma).2.2
  have lS : ∀ z ∈ args.map lower, GA z ∧ isDynB z = Bool.false := by
    intro z mz; obtain ⟨a, ma, rfl⟩ := List.mem_map.mp mz; exact de_ga (hargs a ma).2.1
  obtain ⟨TU, rTU, dTU, aTU⟩ := tup_dom (t := t) (n := d + 1) one uE
  obtain ⟨TL, rTL, dTL, aTL⟩ := tup_dom (t := t) (n := d + 1) one lE
  rw [args_domain_static (fun z mz => (uS z mz).1) (fun z mz => (uS z mz).2) leafU] at rTU
  rw [args_domain_static (fun z mz => (lS z mz).1) (fun z mz => (lS z mz).2) leafL] at rTL
  cases rTU; cases rTL
  -- Lower bounds are in upper bounds, argument by argument.
  have lowUp : ∀ w, FunSem.InDomR ((args.map lower).map (level t (d + 1)).den) w →
      FunSem.InDomR ((args.map upper).map (level t (d + 1)).den) w := by
    have each : ∀ a ∈ args, ∀ v : PN t d, (level t (d + 1)).den (lower a) v → (level t (d + 1)).den (upper a) v :=
      fun a ma v h => (den_succ (hargs a ma).2.2 v).mpr
        ((hargs a ma).1.inv (toTPN v) ((denD_lower a (toTPN v)).mp ((den_succ (hargs a ma).2.1 v).mp h)))
    clear run leafU leafL dTU dTL aTU aTL uE lE uS lS gaArgs hl
    induction args with
    | nil => intro w h; exact h
    | cons a as ih =>
      intro w h
      cases w with
      | nil => exact h.elim
      | cons v ws =>
        exact ⟨each a List.mem_cons_self v h.1, ih (fun b mb => hargs b (List.mem_cons_of_mem _ mb))
          (fun b mb => each b (List.mem_cons_of_mem _ mb)) ws h.2⟩
  rw [run]
  cases hd : args.any isDynB
  · -- Static arguments: the domain is the tuple of them, its own bounds.
    have eq : args.map lower = args.map upper := by
      refine List.map_congr_left fun a ma => ?_
      have nd : isDynB a = Bool.false := by
        cases h : isDynB a
        · rfl
        · exact absurd (List.any_eq_true.mpr ⟨a, ma, h⟩) (by rw [hd]; simp)
      rcases gaArgs a ma with rfl | ⟨X, rfl⟩
      · rfl
      · simp only [isDynB, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at nd
        simp [lower, upper, nd, rmDyn_static nd]
    obtain ⟨-, lo, up⟩ := de_gd dTU.1
    refine ⟨_, by simp, GC.tc (de_tc dTU.1), by rw [lo]; exact dTU.1, by rw [up]; exact dTU, ?_, _, rfl,
      fun _ => rfl⟩
    rw [lo, eq]; exact dTU
  · simp only [ite_true]
    cases hn : args.any fun e => isNoneB (lower e)
    · -- Gradual arguments with non-empty lower bounds: both tuples.
      simp only [Bool.false_eq_true, ite_false]
      let X : List (Term × Term) := [(.atom "dynamic", .map [(.atom "tuple", .tuple #[.integer kU, .atom "closed",
        Term.list (args.map upper)])]), (.atom "tuple", .tuple #[.integer kL, .atom "closed", Term.list (args.map lower)])]
      have rm : rmDyn X = [(.atom "tuple", .tuple #[.integer kL, .atom "closed", Term.list (args.map lower)])] := by
        simp [X, rmDyn]
      have lo : lower (.map X) = .map [(.atom "tuple", .tuple #[.integer kL, .atom "closed", Term.list (args.map lower)])] := by
        simp only [lower, rm]
      have up : upper (.map X) = .map [(.atom "tuple", .tuple #[.integer kU, .atom "closed", Term.list (args.map upper)])] := by
        simp [upper, X, mapLookup]
      have sL := de_map dTL.1
      refine ⟨.map X, rfl, Or.inr ⟨X, _, rfl, by simp [X, mapLookup], de_tc dTU.1, by rw [rm]; exact sL, fun v hv => ?_⟩,
        by rw [lo]; exact dTL.1, by rw [up]; exact dTU, by rw [lo]; exact dTL, X, rfl, fun h => by simp [X, mapLookup] at h⟩
      rw [← denD_rmDyn, rm] at hv
      have tv := dTL.2.1 v hv
      obtain ⟨w, hw⟩ := pt_tuple v tv
      rw [hw] at hv
      rw [← denD_tpt] at hv
      have := (dTU.2.2 w).mpr (lowUp w ((dTL.2.2 w).mp hv))
      rw [denD_tpt] at this
      exact (hw _).mpr this
    · -- An empty lower bound: the dynamic part only.
      simp only [ite_true]
      obtain ⟨gd, lo, up⟩ := dyn_gd dTU.1
      refine ⟨_, rfl, gd.1, by rw [lo]; exact de_none, by rw [up]; exact dTU, ⟨by rw [lo]; exact de_none,
        fun v hv => by rw [lo] at hv; exact absurd hv (denN_nil v), fun w => ?_⟩, _, rfl, fun h => by simp [mapLookup] at h⟩
      rw [lo]
      refine ⟨fun h => absurd h (denN_nil _), fun h => ?_⟩
      exfalso
      obtain ⟨a, ma, ha⟩ := List.any_eq_true.mp hn
      obtain ⟨v, hv⟩ := inDomR_mem _ w h (lower a) (List.mem_map.mpr ⟨a, ma, rfl⟩)
      have cmp : Term.compare (Term.fuel (lower a) (.map [])) (lower a) (.map []) = .eq := by
        simpa [isNoneB] using ha
      exact (level t (d + 1)).ef.den_none' (Or.inl (hargs a ma).2.1) cmp v hv

/-- A node is united as its expansion. -/
theorem union_node {e : Term} (hn : IsT (level t d).nd e) {Y : List (Term × Term)} (hY : Y ≠ []) (m : Nat) :
    Elixir.Module.Types.Descr.«bare_union/2» (D (m + 1)) e (.map Y) =
      Elixir.Module.Types.Descr.«bare_union/2» (D (m + 1)) (expN e (keyOf (level t d).nd)) (.map Y) := by
  obtain ⟨r, S, rfl⟩ := node_tuple hn
  have ex := expand_isT hn m
  obtain ⟨X, eX, sX⟩ := expN_map (.tuple #[.reference r, .map S, gen]) (keyOf (level t d).nd)
  rw [eX] at ex ⊢
  have yNone : Erlang.erlang.«==/2» (.map Y) (.map []) = .ok (.atom "false") := by
    cases Y with
    | nil => exact absurd rfl hY
    | cons y Y => simp [Erlang.erlang.«==/2»]
  have xNone : Erlang.erlang.«==/2» (.map X) (.map []) = .ok (.atom "false") := by
    have : X ≠ [] := by
      intro h; subst h; simp [expN] at eX
    cases X with
    | nil => exact absurd rfl this
    | cons x X => simp [Erlang.erlang.«==/2»]
  have nNone : Erlang.erlang.«==/2» (.tuple #[.reference r, .map S, gen]) (.map []) = .ok (.atom "false") := by
    have : Term.compare (Term.fuel (.tuple #[.reference r, .map S, gen]) (.map [])) (.tuple #[.reference r, .map S, gen])
        (.map []) ≠ .eq := by
      rw [Term.compare_step]; simp [Compare.compareStep]
    simp [Erlang.erlang.«==/2», this]
  conv => lhs; rw [Elixir.Module.Types.Descr.«bare_union/2».eq_def]
  conv => rhs; rw [Elixir.Module.Types.Descr.«bare_union/2».eq_def]
  simp [nNone, yNone, xNone, ex, unfold_map]

/-- A static result united with a dynamic one: the static one as lower bound, and both as upper bound. -/
theorem union_res {e c : Term} (he : (level t (d + 1)).E e) (hc : DE (level t d).E c) {m : Nat}
    (hm : (level t d).K + 25 ≤ m) :
    ∃ r, Elixir.Module.Types.Descr.«bare_union/2» (D (m + 1)) e (.map [(.atom "dynamic", c)]) = .ok r ∧ GD t d r ∧
      (∀ v : PN t d, denD (lower r) v ↔ (level t (d + 1)).den e v) ∧
      (∀ v : PN t d, denD (upper r) v ↔ (level t (d + 1)).den e v ∨ denD c v) := by
  obtain ⟨c', hc', sem, h⟩ := el_canon he
  obtain ⟨gc', lc', uc'⟩ := de_gd hc'
  obtain ⟨gd, ld, ud⟩ := dyn_gd hc
  obtain ⟨r, run, gr, lr, ur⟩ := gd_union gc' gd (m := m + 1) (by omega)
  refine ⟨r, ?_, gr, fun v => ?_, fun v => ?_⟩
  · rcases h with ⟨-, rfl⟩ | ⟨hn, rfl⟩
    · exact run
    · rw [union_node hn (by simp) m]; exact run
  · rw [lr, lc', ld, sem]; exact ⟨fun h => h.elim id fun h => absurd h (denN_nil v), Or.inl⟩
  · rw [ur, uc', ud, sem]

/-- `fun_apply_static/2` applies lines to argument types of the level below: the image of the live functions on
them. -/
theorem apply_img {H : Nat} (one : 1 ≤ H) {Z : List Term} (hZ : ∀ z ∈ Z, DE (level t d).E z ∧ lh z < H)
    (ne : ∀ z ∈ Z, ∃ v : PN t d, denD z v) {Live : List (FunSem.Row (level t (d + 1)).V) → Prop}
    {Q : List (List (Term × List Term × Term))}
    (nQ : NormP (EB (level t (d + 1)).E H) (level t (d + 1)).den Z.length Live Q) {m : Nat}
    (hm : (level t (d + 1)).K + 7 ≤ m) :
    ∃ r, (level t (d + 1)).E r ∧ lh r < H ∧
      Elixir.Module.Types.Descr.«fun_apply_static/2» (D m) (Term.list Z) (Term.list (Q.reverse.map encP)) = .ok r ∧
      ∀ v : (level t (d + 1)).V, (level t (d + 1)).den r v ↔
        ImgP Z.length Live (FunSem.InDomR (Z.map (level t (d + 1)).den)) v := by
  have fe : FunElem (EB (level t (d + 1)).E H) (level t (d + 1)).den ((level t (d + 1)).K + 6) (.map []) :=
    (felem (level t (d + 1)).ef (level t (d + 1)).ef.subc one (safeN_nil H)).mono (by omega)
  have ne' : ∀ z ∈ Z, ∃ v, (level t (d + 1)).den z v := fun z mz => by
    obtain ⟨v, hv⟩ := ne z mz; exact ⟨v, (den_succ (hZ z mz).1 v).mpr hv⟩
  obtain ⟨r, hr, run, sem⟩ := apply_static_lines fe Z.length Z (fun z mz => ⟨Or.inl (hZ z mz).1, (hZ z mz).2⟩) ne' rfl
    Q.reverse (fun q mq => nQ.pos q (List.mem_reverse.mp mq))
  obtain ⟨w, hw⟩ := inDomR_exists (Z.map (level t (d + 1)).den) fun u mu => by
    obtain ⟨z, mz, rfl⟩ := List.mem_map.mp mu; exact ne' z mz
  refine ⟨r, hr.1, hr.2, run m (by omega), fun v => ?_⟩
  rw [sem, ← app_imageP nQ (fun x hx => by simpa using FunSem.inDomR_length hx) ⟨w, hw⟩ v]
  exact ⟨fun ⟨q, mq, h⟩ => ⟨q, List.mem_reverse.mp mq, h⟩, fun ⟨q, mq, h⟩ => ⟨q, List.mem_reverse.mpr mq, h⟩⟩

/-- Images grow with the live functions and the arguments. -/
theorem imgP_mono {V : Type} {a : Nat} {Live Live' : List (FunSem.Row V) → Prop} {I I' : List V → Prop}
    (hL : ∀ g, (∀ r ∈ g, FunSem.ValidRow a r) → Live g → Live' g) (hI : ∀ x, I x → I' x) {v : V}
    (h : ImgP a Live I v) : ImgP a Live' I' v := by
  obtain ⟨g, vg, lg, x, hx, mr⟩ := h
  exact ⟨g, vg, hL g vg lg, x, hI x hx, mr⟩

/-- Where some line does not cover the arguments, its functions return anything there. -/
theorem img_uncovered {V : Type} {E : Term → Prop} {den : Term → V → Prop} {a : Nat}
    {Live : List (FunSem.Row V) → Prop} {Q : List (List (Term × List Term × Term))} (nQ : NormP E den a Live Q)
    {x : List V} (lx : x.length = a) (nc : ¬∀ q ∈ Q, ∃ p ∈ semP den q, FunSem.InDomR p.1 x) (v : V) :
    ImgP a Live (fun y => y = x) v := by
  obtain ⟨q, hq⟩ := Classical.not_forall.mp nc
  obtain ⟨mq, none⟩ := Classical.not_imp.mp hq
  obtain ⟨N, g, vg, allP, noN, sat⟩ := nQ.witness mq
  let row : FunSem.Row V := (x.map some, some v)
  have vg' : ∀ r ∈ row :: g, FunSem.ValidRow a r := by
    intro r mr
    rcases List.mem_cons.mp mr with rfl | mr
    · exact ⟨by simp [row, lx], fun h => by simp [row] at h⟩
    · exact vg r mr
  refine ⟨row :: g, vg', sat _ vg' (fun p mp r mr => ?_) (fun q' mq' h => noN q' mq' fun r mr =>
    h r (List.mem_cons_of_mem _ mr)), x, rfl, List.mem_cons_self⟩
  rcases List.mem_cons.mp mr with rfl | mr
  · intro hd; exact absurd ⟨p, mp, (FunSem.inDom_real p.1 x).mp hd⟩ none
  · exact allP p mp r mr

end

/-! What `fun_apply_with_strategy/4` computes. -/

section
variable {t : Term} {d : Nat}

/-- Argument lists no live function fails on. -/
def Safe {V : Type} (a : Nat) (Live : List (FunSem.Row V) → Prop) (w : List V) : Prop :=
  ∀ g : List (FunSem.Row V), (∀ r ∈ g, FunSem.ValidRow a r) → Live g → (w.map some, Option.none) ∉ g

/-- Lower bounds are in upper bounds. -/
theorem gd_lu {r : Term} (gr : GD t d r) : SubN t d (lower r) (upper r) :=
  fun v h => gr.1.inv (toTPN v) ((denD_lower r (toTPN v)).mp h)

/-- Subtyping of gradual types compares their bounds. -/
theorem gd_subF {r : Term} (gr : GD t d r) {m : Nat} (hm : (level t d).K + 23 ≤ m) (b : Term) (gb : GD t d b) :
    Elixir.Module.Types.Descr.«subtype?/2» (D m) r b =
      .ok (boolAtom (bp (SubN t d (lower r) (lower b) ∧ SubN t d (upper r) (upper b)))) :=
  gd_sub gr.1 gb.1 gr.2.1 gr.2.2 gb.2.1 gb.2.2 hm

theorem dyn_sub {c : Term} (hc : DE (level t d).E c) {m : Nat} (hm : (level t d).K + 23 ≤ m) (b : Term)
    (gb : GD t d b) :
    Elixir.Module.Types.Descr.«subtype?/2» (D m) (.map [(.atom "dynamic", c)]) b =
      .ok (boolAtom (bp (SubN t d (.map []) (lower b) ∧ SubN t d c (upper b)))) := by
  obtain ⟨g, lo, up⟩ := dyn_gd hc
  rw [gd_subF g hm b gb, lo, up]

/-- The bounds of a result: element types of the level of the arguments holding `Lo` and `Up`, the lower one only in
dynamic mode. -/
def ResSem (t : Term) (d m : Nat) (s r : Term) (Lo Up : (level t (d + 1)).V → Prop) : Prop :=
  ∃ lr ur, Elixir.Module.Types.Descr.«lower_bound/1» (D m) r = .ok lr ∧
    Elixir.Module.Types.Descr.«upper_bound/1» (D m) r = .ok ur ∧ DE (level t d).E lr ∧ DE (level t d).E ur ∧
    (∀ v, denD ur v ↔ Up v) ∧ (s = .atom "false" → ∀ v, denD lr v ↔ Lo v) ∧
    (∀ b, GD t d b → Elixir.Module.Types.Descr.«subtype?/2» (D m) r b =
      .ok (boolAtom (bp (SubN t d lr (lower b) ∧ SubN t d ur (upper b))))) ∧ SubN t d lr ur

theorem any_empty_s {Z : List Term} (h : ∀ z ∈ Z, DE (level t d).E z) {m : Nat} (hm : (level t d).K + 23 ≤ m) :
    Erlang.lists.«any/2» (D (m + 1)) (.function false "Elixir.Module.Types.Descr" "empty?" 1 #[]) (Term.list Z) =
      .ok (boolAtom (Z.any fun z => bp (∀ v : PN t d, ¬denD z v))) :=
  any_list _ _ _ _ _ _ fun z mz => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:empty?/1».pure, next_empty (h z mz) hm]

/-- The inlined `dynamic/1` of `fun_apply_result/5` on an element type of the level above `d`. -/
theorem inline_dyn {e : Term} (he : (level t (d + 1)).E e) (m : Nat) :
    ∃ c, DE (level t d).E c ∧ (∀ v : PN t d, (level t (d + 1)).den e v ↔ denD c v) ∧
      ((match Lynx.Term.getMapKeys [Lynx.Term.atom "dynamic"] e with
        | [x] => (pure (Lynx.Term.map [(Lynx.Term.atom "dynamic", x)]) : Except Lynx.Exception Lynx.Term)
        | _ => match e with
          | Lynx.Term.tuple ⟨[_, _, _]⟩ => do
            let y ← (match e with
              | Lynx.Term.atom "term" => Elixir.Module.Types.Descr.«unfolded_term/0»
              | z@(Lynx.Term.tuple ⟨[_, _, _]⟩) => do
                let w ← Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) z
                Elixir.Module.Types.Descr.«unfold/1» (D (m + 1)) w
              | o => pure o)
            Elixir.Module.Types.Descr.«dynamic/1» (D (m + 1)) y
          | _ => pure (Lynx.Term.map [(Lynx.Term.atom "dynamic", e)])) =
        .ok (.map [(.atom "dynamic", c)])) := by
  obtain ⟨c, hc, sem, h⟩ := el_canon he
  refine ⟨c, hc, sem, ?_⟩
  rcases h with ⟨hd, rfl⟩ | ⟨hn, rfl⟩
  · rcases hd with rfl | ⟨X, rfl, sX⟩
    · simp [getMapKeys]
    · simp [getMapKeys_single, sX.static]
  · obtain ⟨r, S, rfl⟩ := node_tuple hn
    have ex := expand_isT hn m
    obtain ⟨X, eX, sX⟩ := expN_map (.tuple #[.reference r, .map S, gen]) (keyOf (level t d).nd)
    rw [eX] at ex ⊢
    have gt : getMapKeys [Term.atom "dynamic"] (.tuple #[.reference r, .map S, gen]) = [] := by simp [getMapKeys]
    have dX : Elixir.Module.Types.Descr.«dynamic/1» (D (m + 1)) (.map X) = .ok (.map [(.atom "dynamic", .map X)]) := by
      unfold Elixir.Module.Types.Descr.«dynamic/1»; simp [getMapKeys_single, sX]
    simp [gt, ex, unfold_map, dX]

/-- `fun_apply_static/2` on argument types `Z`, united with a dynamic type: the image of the static lines, below the
dynamic type, unless some argument is empty. -/
theorem static_mixed {H : Nat} (two : 2 ≤ H) {Fs : Term} {a : Nat} {q : List (Term × List Term × Term)}
    {Qs' : List (List (Term × List Term × Term))}
    (nQs : NormP (EB (level t (d + 1)).E H) (level t (d + 1)).den a (FunT t (d + 1) Fs a) (q :: Qs'))
    {c : Term} (hc : DE (level t d).E c) {Up : (level t (d + 1)).V → Prop} (upSem : ∀ v, denD c v ↔ Up v)
    {Z : List Term} (hZ : ∀ z ∈ Z, DE (level t d).E z ∧ lh z < H) (lenZ : Z.length = a)
    (inUp : ∀ v, ImgP a (FunT t (d + 1) Fs a) (FunSem.InDomR (Z.map (level t (d + 1)).den)) v → Up v)
    {m : Nat} (hm : (level t (d + 1)).K + 30 ≤ m) :
    ∃ sr r, (Z.any (fun z => bp (∀ v : PN t d, ¬denD z v)) = Bool.false →
        Elixir.Module.Types.Descr.«fun_apply_static/2» (D (m + 1)) (Term.list Z)
          (Term.list (List.map encP (q :: Qs')).reverse) = .ok sr) ∧
      (Z.any (fun z => bp (∀ v : PN t d, ¬denD z v)) = Bool.true → sr = .map []) ∧
      Elixir.Module.Types.Descr.«bare_union/2» (D (m + 1)) sr (.map [(.atom "dynamic", c)]) = .ok r ∧
      ∀ s', ResSem t d (m + 1) s' r
        (ImgP a (FunT t (d + 1) Fs a) (FunSem.InDomR (Z.map (level t (d + 1)).den))) Up := by
  have upC : Elixir.Module.Types.Descr.«upper_bound/1» (D (m + 1)) (.map [(.atom "dynamic", c)]) = .ok c := by
    rw [upper_bound_run (Or.inr ⟨_, rfl, fun Dy e => ?_⟩)]
    · simp [upper, mapLookup]
    · simp [mapLookup] at e; subst e
      rcases hc with h | ⟨Y, h, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨Y, h⟩
  have loC : Elixir.Module.Types.Descr.«lower_bound/1» (D (m + 1)) (.map [(.atom "dynamic", c)]) = .ok (.map []) := by
    rw [lower_bound_run (Or.inr ⟨_, rfl⟩)]; simp [lower, rmDyn]
  have hmS : (level t d).K + 23 ≤ m + 1 := by rw [level_K] at hm ⊢; omega
  cases hE : Z.any (fun z => bp (∀ v : PN t d, ¬denD z v))
  · -- Every argument holds values: the static image, united with the dynamic one.
    have neZ : ∀ z ∈ Z, ∃ v : PN t d, denD z v := fun z mz =>
      Classical.byContradiction fun none => by
        have := List.any_eq_false.mp hE z mz
        rw [bp_true.mpr fun v hv => none ⟨v, hv⟩] at this
        exact this rfl
    obtain ⟨sr, hsr, -, rsr, ssr⟩ := apply_img (Live := FunT t (d + 1) Fs a) (by omega) hZ neZ
      (by rw [lenZ]; exact nQs) (m := m + 1) (by omega)
    rw [lenZ] at ssr
    obtain ⟨r, ru, gr, lr, ur⟩ := union_res hsr hc (m := m) (by rw [level_K] at hm ⊢; omega)
    refine ⟨sr, r, (fun _ => by simpa [List.map_reverse] using rsr), (fun h => by cases h), ru, fun s' => ?_⟩
    refine ⟨lower r, upper r, lower_bound_run gr.1.shape, upper_bound_run gr.1.ub, gr.2.1, gr.2.2,
      fun v => ?_, fun _ v => ?_, gd_subF gr hmS, gd_lu gr⟩
    · rw [ur]
      exact ⟨fun h => h.elim (fun h => inUp v ((ssr v).mp h)) (upSem v).mp,
        fun h => Or.inr ((upSem v).mpr h)⟩
    · rw [lr]; exact ssr v
  · -- Some argument is empty: no static image.
    obtain ⟨z, mz, hz⟩ := List.any_eq_true.mp hE
    have none : ∀ v, ¬ImgP a (FunT t (d + 1) Fs a)
        (FunSem.InDomR (Z.map (level t (d + 1)).den)) v := by
      rintro v ⟨g, -, -, x, hx, -⟩
      obtain ⟨u, hu⟩ := inDomR_mem Z x hx z mz
      exact bp_true.mp hz u ((den_succ (hZ z mz).1 u).mp hu)
    refine ⟨.map [], .map [(.atom "dynamic", c)], (fun h => by cases h), (fun _ => rfl), ?_, fun s' => ?_⟩
    · rw [Elixir.Module.Types.Descr.«bare_union/2».eq_def]; simp [Erlang.erlang.«==/2»]
    · refine ⟨_, _, loC, upC, de_none, hc, upSem, fun _ v => ⟨fun h => absurd h (denN_nil v), fun h => ?_⟩,
        dyn_sub hc hmS, fun v h => absurd h (denN_nil v)⟩
      exact absurd h (none v)


/-- `fun_apply_result/5`: its lower bound holds the image of the static part on the lower bounds of the arguments in
dynamic mode, and its upper bound the image of the dynamic part on their upper bounds. -/
theorem result_sem {H : Nat} (two : 2 ≤ H) {Fs Fd : Term} {Qs Qd : List (List (Term × List Term × Term))}
    {args : List Term} (hargs : ∀ x ∈ args, GD t d x) (hl : ∀ x ∈ args, lh (upper x) < H ∧ lh (lower x) < H)
    (ne : ∀ x ∈ args, ∃ v : PN t d, denD (upper x) v)
    (nQs : NormP (EB (level t (d + 1)).E H) (level t (d + 1)).den args.length (FunT t (d + 1) Fs args.length) Qs)
    (nQd : NormP (EB (level t (d + 1)).E H) (level t (d + 1)).den args.length (FunT t (d + 1) Fd args.length) Qd)
    (neQd : Qd ≠ [])
    (inc : ∀ g, (∀ r ∈ g, FunSem.ValidRow args.length r) → FunT t (d + 1) Fs args.length g →
      FunT t (d + 1) Fd args.length g)
    (allS : Bool) (hall : allS = Bool.true → Qs = Qd ∧ (∀ g, FunT t (d + 1) Fs args.length g ↔ FunT t (d + 1) Fd args.length g) ∧
      ∀ x ∈ args, isDynB x = Bool.false)
    {s : Term} (hs : s = .atom "true" ∨ s = .atom "false") {m : Nat} (hm : (level t (d + 1)).K + 30 ≤ m) :
    ∃ r, Elixir.Module.Types.Descr.«fun_apply_result/5» (D (m + 1)) (Term.list args) (Term.list (Qs.reverse.map encP))
        (Term.list (Qd.reverse.map encP)) (boolAtom allS) s = .ok r ∧
      ResSem t d (m + 1) s r
        (ImgP args.length (FunT t (d + 1) Fs args.length)
          (FunSem.InDomR ((args.map lower).map (level t (d + 1)).den)))
        (ImgP args.length (FunT t (d + 1) Fd args.length)
          (FunSem.InDomR ((args.map upper).map (level t (d + 1)).den))) := by
  have hmd : (level t d).K + 23 ≤ m := by rw [level_K] at hm ⊢; omega
  have uZ : ∀ z ∈ args.map upper, DE (level t d).E z ∧ lh z < H := by
    intro z mz; obtain ⟨x, mx, rfl⟩ := List.mem_map.mp mz; exact ⟨(hargs x mx).2.2, (hl x mx).1⟩
  have lZ : ∀ z ∈ args.map lower, DE (level t d).E z ∧ lh z < H := by
    intro z mz; obtain ⟨x, mx, rfl⟩ := List.mem_map.mp mz; exact ⟨(hargs x mx).2.1, (hl x mx).2⟩
  have uNe : ∀ z ∈ args.map upper, ∃ v : PN t d, denD z v := by
    intro z mz; obtain ⟨x, mx, rfl⟩ := List.mem_map.mp mz; exact ne x mx
  have lenU : (args.map upper).length = args.length := List.length_map ..
  have lenL : (args.map lower).length = args.length := List.length_map ..
  -- Lower bounds are in upper bounds.
  have lowUp : ∀ w, FunSem.InDomR ((args.map lower).map (level t (d + 1)).den) w →
      FunSem.InDomR ((args.map upper).map (level t (d + 1)).den) w := by
    have each : ∀ a ∈ args, ∀ v : PN t d, (level t (d + 1)).den (lower a) v → (level t (d + 1)).den (upper a) v :=
      fun a ma v h => (den_succ (hargs a ma).2.2 v).mpr
        ((hargs a ma).1.inv (toTPN v) ((denD_lower a (toTPN v)).mp ((den_succ (hargs a ma).2.1 v).mp h)))
    clear hl ne uZ lZ uNe lenU lenL nQs nQd inc hall
    induction args with
    | nil => intro w h; exact h
    | cons a as ih =>
      intro w h
      cases w with
      | nil => exact h.elim
      | cons v ws =>
        exact ⟨each a List.mem_cons_self v h.1, ih (fun b mb => hargs b (List.mem_cons_of_mem _ mb))
          (fun b mb => each b (List.mem_cons_of_mem _ mb)) ws h.2⟩
  -- The dynamic image.
  obtain ⟨dr, hdr, ldr, rdr, sdr⟩ := apply_img (Live := FunT t (d + 1) Fd args.length) (by omega) uZ uNe
    (by rw [lenU]; exact nQd) (m := m + 1) (by omega)
  rw [lenU] at sdr
  have mapU := map_upper_g hargs m
  have mapL := map_lower_g hargs m
  rw [List.map_reverse] at rdr
  -- The dynamic image, as the type its dynamic type wraps.
  obtain ⟨c, hc, sc, cases⟩ := el_canon hdr
  cases allS
  case true =>
    obtain ⟨rfl, eqF, st⟩ := hall rfl
    have same : ∀ x ∈ args, upper x = x ∧ lower x = x := by
      intro x mx
      rcases gd_ga (hargs x mx) with rfl | ⟨X, rfl⟩
      · exact ⟨rfl, rfl⟩
      · have := st _ mx
        simp only [isDynB, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at this
        exact ⟨by simp [upper, this], by simp [lower, rmDyn_static this]⟩
    have eU : args.map upper = args := (List.map_congr_left fun x mx => (same x mx).1).trans (List.map_id args)
    have eL : args.map lower = args := (List.map_congr_left fun x mx => (same x mx).2).trans (List.map_id args)
    rw [eU] at rdr sdr
    obtain ⟨c', hc', sc', ub, lb, -, subE⟩ := el_ops hdr m
    unfold Elixir.Module.Types.Descr.«fun_apply_result/5»
    simp [boolAtom, Erlang.erlang.«/=/2», Lynx.Except.andAlso, rdr]
    have cU : List.map ((level t (d + 1)).den ∘ upper) args = List.map (level t (d + 1)).den args := by
      rw [← List.map_map, eU]
    have cL : List.map ((level t (d + 1)).den ∘ lower) args = List.map (level t (d + 1)).den args := by
      rw [← List.map_map, eL]
    simp only [cU, cL]
    exact ⟨c', c', lb, ub, hc', hc', fun v => (sc' v).symm.trans (sdr v), fun _ v => (sc' v).symm.trans
      ((sdr v).trans ⟨fun h => imgP_mono (fun g _ hg => (eqF g).mpr hg) (fun x hx => hx) h,
        fun h => imgP_mono (fun g _ hg => (eqF g).mp hg) (fun x hx => hx) h⟩), subE (by omega), fun _ h => h⟩
  unfold Elixir.Module.Types.Descr.«fun_apply_result/5»
  simp only [boolAtom, Bool.false_eq_true, ite_false]
  simp [Erlang.erlang.«/=/2», Lynx.Except.andAlso, mapU, rdr]
  -- The inlined `dynamic/1` of the dynamic image.
  rcases cases with ⟨hdt | ⟨X, hX, sX⟩, hcEq⟩ | ⟨hn, hcEq⟩
  all_goals first
    | (subst hdt; simp [getMapKeys]; rw [← hcEq])
    | (subst hX; simp [getMapKeys_single, sX.static]; rw [← hcEq])
    | (obtain ⟨r, S, rfl⟩ := node_tuple hn
       have ex := expand_isT hn m
       obtain ⟨X, eX, sX⟩ := expN_map (.tuple #[.reference r, .map S, gen]) (keyOf (level t d).nd)
       rw [eX] at ex hcEq
       have gt : getMapKeys [Term.atom "dynamic"] (.tuple #[.reference r, .map S, gen]) = [] := by simp [getMapKeys]
       have dX : Elixir.Module.Types.Descr.«dynamic/1» (D (m + 1)) (.map X) = .ok (.map [(.atom "dynamic", .map X)]) := by
         unfold Elixir.Module.Types.Descr.«dynamic/1»; simp [getMapKeys_single, sX]
       simp [gt, ex, unfold_map, dX]
       rw [← hcEq])
  all_goals
    have upC : Elixir.Module.Types.Descr.«upper_bound/1» (D (m + 1)) (.map [(.atom "dynamic", c)]) = .ok c := by
      rw [upper_bound_run (Or.inr ⟨_, rfl, fun Dy e => ?_⟩)]
      · simp [upper, mapLookup]
      · simp [mapLookup] at e; subst e
        rcases hc with h | ⟨Y, h, -⟩
        · exact Or.inl h
        · exact Or.inr ⟨Y, h⟩
    have loC : Elixir.Module.Types.Descr.«lower_bound/1» (D (m + 1)) (.map [(.atom "dynamic", c)]) = .ok (.map []) := by
      rw [lower_bound_run (Or.inr ⟨_, rfl⟩)]; simp [lower, rmDyn]
    have upSem : ∀ v, denD c v ↔ ImgP args.length (FunT t (d + 1) Fd args.length)
        (FunSem.InDomR ((args.map upper).map (level t (d + 1)).den)) v := fun v => (sc v).symm.trans (sdr v)
    -- A static image is in the dynamic one.
    have inImg : ∀ {Z : List Term}, (∀ w, FunSem.InDomR (Z.map (level t (d + 1)).den) w →
        FunSem.InDomR ((args.map upper).map (level t (d + 1)).den) w) → ∀ v,
        ImgP args.length (FunT t (d + 1) Fs args.length) (FunSem.InDomR (Z.map (level t (d + 1)).den)) v →
        ImgP args.length (FunT t (d + 1) Fd args.length) (FunSem.InDomR ((args.map upper).map (level t (d + 1)).den)) v :=
      fun hZ v h => imgP_mono inc hZ h
    cases Qs with
    | nil =>
      simp [Term.list, Erlang.erlang.«==/2»]
      refine ⟨_, _, loC, upC, de_none, hc, fun v => by simpa [List.map_map] using upSem v,
        fun _ v => ⟨fun h => absurd h (denN_nil v), fun h => ?_⟩, dyn_sub hc (by omega), fun v h => absurd h (denN_nil v)⟩
      obtain ⟨g, vg, lg, -⟩ := h
      obtain ⟨q, mq, -⟩ := nQs.cover g vg lg
      cases mq
    | cons q Qs' =>
      obtain ⟨h₀, tl, hcons⟩ : ∃ h₀ tl, Term.list ((List.map encP (q :: Qs')).reverse) = .cons h₀ tl := by
        cases e : (List.map encP (q :: Qs')).reverse with
        | nil => simp at e
        | cons h₀ tl => exact ⟨h₀, Term.list tl, by simp [Term.list]⟩
      rw [hcons]
      simp [Erlang.erlang.«==/2»]
      rw [← hcons]
      rcases hs with rfl | rfl
      · obtain ⟨sr, r, rsr, -, ru, sem⟩ := static_mixed two nQs hc upSem uZ lenU (fun v h => inImg (fun w h => h) v h) (m := m) (by omega)
        have noE : (args.map upper).any (fun z => bp (∀ v : PN t d, ¬denD z v)) = Bool.false :=
          List.any_eq_false.mpr fun z mz h => by
            obtain ⟨v, hv⟩ := uNe z mz; exact (bp_true.mp h) v hv
        have anyU := any_empty_s (fun z mz => (uZ z mz).1) hmd
        rw [noE] at anyU
        have rsr' := rsr noE
        simp only [List.map_cons, List.reverse_cons] at rsr'
        simp [anyU, boolAtom, rsr', ru]
        obtain ⟨lr, ur, h₁, h₂, h₃, h₄, h₅, -, h₇, h₈⟩ := sem (.atom "true")
        exact ⟨lr, ur, h₁, h₂, h₃, h₄, fun v => by simpa [List.map_map] using h₅ v, fun h => by simp at h, h₇, h₈⟩
      · obtain ⟨sr, r, rsr, rsr', ru, sem⟩ := static_mixed two nQs hc upSem lZ lenL (fun v h => inImg lowUp v h) (m := m) (by omega)
        have anyL := any_empty_s (fun z mz => (lZ z mz).1) hmd
        simp [mapL]
        cases hE : (args.map lower).any (fun z => bp (∀ v : PN t d, ¬denD z v))
        · rw [hE] at anyL
          have rsr₁ := rsr hE
          simp only [List.map_cons, List.reverse_cons] at rsr₁
          simp [anyL, boolAtom, rsr₁, ru]
          obtain ⟨lr, ur, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := sem (.atom "false")
          exact ⟨lr, ur, h₁, h₂, h₃, h₄, fun v => by simpa [List.map_map] using h₅ v,
            fun h v => by simpa [List.map_map] using h₆ rfl v, h₇, h₈⟩
        · rw [hE] at anyL
          obtain rfl := rsr' hE
          simp [anyL, boolAtom, ru]
          obtain ⟨lr, ur, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := sem (.atom "false")
          exact ⟨lr, ur, h₁, h₂, h₃, h₄, fun v => by simpa [List.map_map] using h₅ v,
            fun h v => by simpa [List.map_map] using h₆ rfl v, h₇, h₈⟩


/-- When the application of a function whose static and dynamic parts are `Fs` and `Fd` succeeds: the upper
bounds of the arguments hold values, the static part holds no function of another arity, the dynamic part holds some
of the arity, and the tuples of the upper bounds of the arguments are safe for one of the parts, or otherwise those of
the lower bounds are, and some tuple of the upper bounds. -/
def AppOK (t : Term) (d : Nat) (Fs Fd : Term) (args : List Term) : Prop :=
  (∀ x ∈ args, ∃ v : PN t d, denD (upper x) v) ∧
  (∀ (b : Nat) (g : List (FunSem.Row (level t (d + 1)).V)), (∀ r ∈ g, FunSem.ValidRow b r) → b ≠ args.length →
    ¬FunT t (d + 1) Fs b g) ∧
  (∃ g : List (FunSem.Row (level t (d + 1)).V), (∀ r ∈ g, FunSem.ValidRow args.length r) ∧
    FunT t (d + 1) Fd args.length g) ∧
  ((∀ w, FunSem.InDomR ((args.map upper).map (level t (d + 1)).den) w →
      Safe args.length (FunT t (d + 1) Fs args.length) w ∨ Safe args.length (FunT t (d + 1) Fd args.length) w) ∨
    ((∀ w, FunSem.InDomR ((args.map lower).map (level t (d + 1)).den) w →
        Safe args.length (FunT t (d + 1) Fs args.length) w ∨ Safe args.length (FunT t (d + 1) Fd args.length) w) ∧
      ∃ w, FunSem.InDomR ((args.map upper).map (level t (d + 1)).den) w ∧
        (Safe args.length (FunT t (d + 1) Fs args.length) w ∨ Safe args.length (FunT t (d + 1) Fd args.length) w)))

/-- Lines hold live functions. -/
theorem norm_live {V : Type} {E : Term → Prop} {den : Term → V → Prop} {a : Nat}
    {Live : List (FunSem.Row V) → Prop} {Q : List (List (Term × List Term × Term))} (nQ : NormP E den a Live Q)
    (ne : Q ≠ []) : ∃ g, (∀ r ∈ g, FunSem.ValidRow a r) ∧ Live g := by
  obtain ⟨q, mq⟩ := List.exists_mem_of_ne_nil Q ne
  obtain ⟨N, -, lv, sat⟩ := nQ.live q mq
  obtain ⟨g, vg, all, none⟩ : ∃ g : List (FunSem.Row V), (∀ r ∈ g, FunSem.ValidRow a r) ∧
      (∀ p ∈ semP den q, ∀ r ∈ g, FunSem.Allows p r) ∧ ∀ q' ∈ semP den N, ¬∀ r ∈ g, FunSem.Allows q' r := by
    refine Classical.byContradiction fun h => lv fun g vg all => ?_
    refine Classical.byContradiction fun h' => h ⟨g, vg, all, fun q' mq' al => h' ⟨q', mq', al⟩⟩
  exact ⟨g, vg, sat g vg all none⟩

/-- Arguments that are not gradual are their own bounds. -/
theorem static_bounds {args : List Term} (hargs : ∀ x ∈ args, GD t d x) (st : ∀ x ∈ args, isDynB x = Bool.false) :
    args.map upper = args ∧ args.map lower = args := by
  have same : ∀ x ∈ args, upper x = x ∧ lower x = x := by
    intro x mx
    rcases gd_ga (hargs x mx) with rfl | ⟨X, rfl⟩
    · exact ⟨rfl, rfl⟩
    · have := st _ mx
      simp only [isDynB, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at this
      exact ⟨by simp [upper, this], by simp [lower, rmDyn_static this]⟩
  exact ⟨(List.map_congr_left fun x mx => (same x mx).1).trans (List.map_id args),
    (List.map_congr_left fun x mx => (same x mx).2).trans (List.map_id args)⟩

/-- The successes of `fun_normalize_both/3`, as one shape: no static lines when the static part holds no function. -/
theorem normBoth_common {H : Nat} {Fs Fd : Term} {a : Nat} {nb : Except Exception Term}
    (h : NormBoth t (d + 1) H Fs Fd a nb) (ok : ∃ y z w, nb = .ok (.tuple #[.atom "ok", y, z, w])) :
    ∃ dom Qs Qd, NormP (EB (level t (d + 1)).E H) (level t (d + 1)).den a (FunT t (d + 1) Fs a) Qs ∧
      NormP (EB (level t (d + 1)).E H) (level t (d + 1)).den a (FunT t (d + 1) Fd a) Qd ∧ Qd ≠ [] ∧
      GD t (d + 1) dom ∧ (∀ w, denD (upper dom) (tpt (t := t) (n := d + 1) w) ↔ Covers t (d + 1) Qs w ∨
        Covers t (d + 1) Qd w) ∧
      (∀ (b : Nat) (g : List (FunSem.Row (level t (d + 1)).V)), (∀ r ∈ g, FunSem.ValidRow b r) → b ≠ a →
        ¬FunT t (d + 1) Fs b g) ∧
      nb = .ok (.tuple #[.atom "ok", dom, Term.list (Qs.reverse.map encP), Term.list (Qd.reverse.map encP)]) := by
  rcases h with ⟨dom, Qs, Qd, nQs, -, nQd, neQd, gd, td, other, rfl⟩ | ⟨dom, Qd, none, nQd, neQd, gd, all, rfl⟩ |
    ⟨-, n4, -⟩
  · exact ⟨dom, Qs, Qd, nQs, nQd, neQd, gd, td.2.2, other, rfl⟩
  · refine ⟨dom, [], Qd, ⟨by simp, by simp, fun g vg hg => absurd hg (none a g vg), by simp⟩, nQd, neQd, gd,
      fun w => ⟨fun _ => Or.inl (by simp [Covers]), fun _ => all _⟩, fun b g vg _ => none b g vg, rfl⟩
  · obtain ⟨y, z, w, e⟩ := ok
    exact absurd e (n4 y z w)

set_option maxHeartbeats 1000000 in
theorem strategy_core {H : Nat} (two : 2 ≤ H) {Xs : List (Term × Term)} {fd Fd : Term} (fdNil : Bool)
    (hfdNil : Erlang.erlang.«==/2» fd (.atom "nil") = .ok (boolAtom fdNil))
    {args : List Term} (hargs : ∀ x ∈ args, GD t d x) (hl : ∀ x ∈ args, lh (upper x) < H ∧ lh (lower x) < H)
    (ne : ∀ x ∈ args, ∃ v : PN t d, denD (upper x) v)
    {dom : Term} {Qs Qd : List (List (Term × List Term × Term))}
    (nQs : NormP (EB (level t (d + 1)).E H) (level t (d + 1)).den args.length (FunT t (d + 1) (.map Xs) args.length) Qs)
    (nQd : NormP (EB (level t (d + 1)).E H) (level t (d + 1)).den args.length (FunT t (d + 1) Fd args.length) Qd)
    (neQd : Qd ≠ []) (gd : GD t (d + 1) dom)
    (domPts : ∀ w, denD (upper dom) (tpt (t := t) (n := d + 1) w) ↔ Covers t (d + 1) Qs w ∨ Covers t (d + 1) Qd w)
    (inc : ∀ g, (∀ r ∈ g, FunSem.ValidRow args.length r) → FunT t (d + 1) (.map Xs) args.length g →
      FunT t (d + 1) Fd args.length g)
    (same : fdNil && !args.any isDynB = Bool.true → Qs = Qd ∧
      ∀ g, FunT t (d + 1) (.map Xs) args.length g ↔ FunT t (d + 1) Fd args.length g)
    {s : Term} (hs : s = .atom "true" ∨ s = .atom "false") {m : Nat} (hm : (level t (d + 1)).K + 40 ≤ m)
    (hnb : Elixir.Module.Types.Descr.«fun_normalize_both/3» (D (m + 1)) (.map Xs) fd (.integer args.length) =
      .ok (.tuple #[.atom "ok", dom, Term.list (Qs.reverse.map encP), Term.list (Qd.reverse.map encP)])) :
    let P := fun w => Safe args.length (FunT t (d + 1) (.map Xs) args.length) w ∨
      Safe args.length (FunT t (d + 1) Fd args.length) w
    let ok := (∀ w, FunSem.InDomR ((args.map upper).map (level t (d + 1)).den) w → P w) ∨
      ((fdNil && !args.any isDynB) = Bool.false ∧ (∀ w, FunSem.InDomR ((args.map lower).map (level t (d + 1)).den) w → P w) ∧
        ∃ w, FunSem.InDomR ((args.map upper).map (level t (d + 1)).den) w ∧ P w)
    (ok → ∃ r, Elixir.Module.Types.Descr.«fun_apply_with_strategy/4» (D (m + 1)) (.map Xs) fd (Term.list args) s =
        .ok (.tuple #[.atom "ok", r]) ∧
      ResSem t d (m + 1) s r
        (ImgP args.length (FunT t (d + 1) (.map Xs) args.length) (FunSem.InDomR ((args.map lower).map (level t (d + 1)).den)))
        (ImgP args.length (FunT t (d + 1) Fd args.length) (FunSem.InDomR ((args.map upper).map (level t (d + 1)).den)))) ∧
    (¬ok → ∀ r, Elixir.Module.Types.Descr.«fun_apply_with_strategy/4» (D (m + 1)) (.map Xs) fd (Term.list args) s ≠
      .ok (.tuple #[.atom "ok", r])) := by
  intro P ok
  have hmd : (level t d).K + 23 ≤ m := by rw [level_K] at hm ⊢; omega
  have anyU := any_empty_g hargs hmd
  have noE : args.any (fun a => bp (∀ v : PN t d, ¬denD (upper a) v)) = Bool.false :=
    List.any_eq_false.mpr fun x mx h => by obtain ⟨v, hv⟩ := ne x mx; exact (bp_true.mp h) v hv
  rw [noE] at anyU
  obtain ⟨A, rA, gA, lA, tUA, tLA, X, rfl, sX⟩ := argsdom_sem (H := H) (by omega) hargs hl
  have allE := all_static_g hargs m
  have h15 : ∀ x y bb : Bool, Lynx.Except.andAlso (Except.ok (boolAtom x)) (Except.ok (boolAtom y)) bb =
      .ok (boolAtom (x && y)) := by
    intro x y bb; cases x <;> cases y <;> rfl
  have subG := tupDom_sub tUA gd.2.2 domPts (m := m + 1) (by omega)
  have lowIn : ∀ w, FunSem.InDomR ((args.map lower).map (level t (d + 1)).den) w →
      FunSem.InDomR ((args.map upper).map (level t (d + 1)).den) w := fun w h =>
    (tUA.2.2 w).mp (gA.inv (toTPN _) ((denD_lower (.map X) (toTPN _)).mp ((tLA.2.2 w).mpr h)))
  -- Compatibility: the tuples of the lower bounds are in the domain, and some tuple of the upper bounds.
  obtain ⟨cb, compatE, cbSem⟩ : ∃ cb : Bool, Elixir.Module.Types.Descr.«compatible?/2» (D (m + 1)) (.map X) dom =
      .ok (boolAtom cb) ∧ (cb = Bool.true ↔
        (∀ w, FunSem.InDomR ((args.map lower).map (level t (d + 1)).den) w → Covers t (d + 1) Qs w ∨ Covers t (d + 1) Qd w) ∧
        ∃ w, FunSem.InDomR ((args.map upper).map (level t (d + 1)).den) w ∧ (Covers t (d + 1) Qs w ∨ Covers t (d + 1) Qd w)) := by
    have eE := next_empty tLA.1 (m := m + 1) (by omega)
    have eS := tupDom_sub tLA gd.2.2 domPts (m := m + 1) (by omega)
    rw [← sstatic_sub (de_tc tLA.1) (de_tc gd.2.2) (by omega)] at eS
    have eJ := next_disj tUA.1 gd.2.2 (m := m + 1) (by omega)
    have run := compat_run (D (m + 1)) (Or.inr ⟨X, rfl⟩) gd.1.ub eE eS eJ
    refine ⟨_, run, ?_⟩
    by_cases E : ∀ v : PN t (d + 1), ¬denD (lower (.map X)) v
    · rw [bp_true.mpr E]
      have noL : ∀ w, ¬FunSem.InDomR ((args.map lower).map (level t (d + 1)).den) w :=
        fun w h => E _ ((tLA.2.2 w).mpr h)
      constructor
      · intro h
        refine ⟨fun w hw => absurd hw (noL w), ?_⟩
        refine Classical.byContradiction fun none => ?_
        have : bp (∀ v : PN t (d + 1), denD (upper (.map X)) v → denD (upper dom) v → False) = Bool.true :=
          bp_true.mpr fun v h₁ h₂ => by
            obtain ⟨w, hw⟩ := pt_tuple_de v (tUA.2.1 v h₁)
            rw [hw _ tUA.1] at h₁
            rw [hw _ gd.2.2] at h₂
            exact none ⟨w, (tUA.2.2 w).mp h₁, (domPts w).mp h₂⟩
        rw [this] at h; cases h
      · rintro ⟨-, w, hU, hP⟩
        rw [bp_false.mpr fun J => J _ ((tUA.2.2 w).mpr hU) ((domPts w).mpr hP)]
        rfl
    · rw [bp_false.mpr E]
      obtain ⟨v, hv⟩ : ∃ v : PN t (d + 1), denD (lower (.map X)) v :=
        Classical.byContradiction fun none => E fun v h => none ⟨v, h⟩
      obtain ⟨w, hw⟩ := pt_tuple_de v (tLA.2.1 v hv)
      rw [hw _ tLA.1] at hv
      have lw := (tLA.2.2 w).mp hv
      constructor
      · intro h
        have hS := bp_true.mp h
        exact ⟨hS, w, lowIn w lw, hS w lw⟩
      · rintro ⟨h, -⟩
        exact bp_true.mpr h
  unfold Elixir.Module.Types.Descr.«fun_apply_with_strategy/4»
  simp [anyU, boolAtom_false, length_list, hnb, rA, hfdNil, allE, h15]
  have gT : getMapKeys [Term.atom "dynamic"] (Term.atom "term") = [] := by simp [getMapKeys]
  rcases gd.1.shape with hdt | ⟨Y, hY⟩
  all_goals first
    | (subst hdt
       cases hX : mapLookup X (.atom "dynamic") <;> simp [getMapKeys_single, hX, gT] <;>
         simp only [upper, hX, Option.getD_some, Option.getD_none] at subG <;> rw [subG])
    | (subst hY
       cases hX : mapLookup X (.atom "dynamic") <;> cases hY' : mapLookup Y (.atom "dynamic") <;>
         simp [getMapKeys_single, hX, hY'] <;>
         simp only [upper, hX, hY', Option.getD_some, Option.getD_none] at subG <;> rw [subG])
  all_goals
    -- The upper bounds of the arguments are in the domain, as no live function fails on them.
    have covers : ∀ w, FunSem.InDomR ((args.map upper).map (level t (d + 1)).den) w →
        (Covers t (d + 1) Qs w ∨ Covers t (d + 1) Qd w ↔ P w) := fun w hw => by
      have lw : w.length = args.length := by simpa using FunSem.inDomR_length hw
      exact or_congr (dom_safeP nQs w lw) (dom_safeP nQd w lw)
    have coversL : ∀ w, FunSem.InDomR ((args.map lower).map (level t (d + 1)).den) w →
        (Covers t (d + 1) Qs w ∨ Covers t (d + 1) Qd w ↔ P w) := fun w hw => by
      have lw : w.length = args.length := by simpa using FunSem.inDomR_length hw
      exact or_congr (dom_safeP nQs w lw) (dom_safeP nQd w lw)
    have hall : (fdNil && !args.any isDynB) = Bool.true → Qs = Qd ∧
        (∀ g, FunT t (d + 1) (.map Xs) args.length g ↔ FunT t (d + 1) Fd args.length g) ∧
        ∀ x ∈ args, isDynB x = Bool.false := fun h => by
      refine ⟨(same h).1, (same h).2, fun x mx => ?_⟩
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      exact List.any_eq_false.mp h.2 x mx |> Bool.eq_false_iff.mpr
    by_cases hsub : ∀ w, FunSem.InDomR (List.map (level t (d + 1)).den (List.map upper args)) w →
        Covers t (d + 1) Qs w ∨ Covers t (d + 1) Qd w
    · rw [bp_true.mpr hsub]
      have okH : ok := Or.inl fun w hw => (covers w hw).mp (hsub w hw)
      obtain ⟨r, rr, sr⟩ := result_sem two hargs hl ne nQs nQd neQd inc (fdNil && !args.any isDynB) hall hs
        (m := m) (by omega)
      refine ⟨fun _ => ⟨r, by simp only [List.map_reverse] at rr ⊢; rw [rr]; rfl, by simpa only [List.map_map] using sr⟩,
        fun h => absurd okH h⟩
    · rw [bp_false.mpr hsub]
      simp [compatE]
      -- Some upper bound escapes the domain, so the dynamic image is everything.
      have upAll : ∀ v, ImgP args.length (FunT t (d + 1) Fd args.length)
          (FunSem.InDomR ((args.map upper).map (level t (d + 1)).den)) v := by
        obtain ⟨w, hw⟩ := Classical.not_forall.mp hsub
        obtain ⟨hU, hP⟩ := Classical.not_imp.mp hw
        have lw : w.length = args.length := by simpa using FunSem.inDomR_length hU
        intro v
        exact imgP_mono (fun g _ h => h) (fun x hx => by rw [hx]; simpa using hU)
          (img_uncovered nQd lw (fun h => hP (Or.inr h)) v)
      have upT : ∀ v, denD (.atom "term") v ↔ ImgP args.length (FunT t (d + 1) Fd args.length)
          (FunSem.InDomR ((args.map upper).map (level t (d + 1)).den)) v := fun v => ⟨fun _ => upAll v, fun _ => denD_term v⟩
      have dynR : ∀ s' (Lo : (level t (d + 1)).V → Prop), (s' = .atom "false" → ∀ v, ¬Lo v) →
          ResSem t d (m + 1) s' (.map [(.atom "dynamic", .atom "term")]) Lo
            (ImgP args.length (FunT t (d + 1) Fd args.length)
              (FunSem.InDomR (List.map ((level t (d + 1)).den ∘ upper) args))) := by
        intro s' Lo hLo
        have ub : Elixir.Module.Types.Descr.«upper_bound/1» (D (m + 1)) (.map [(.atom "dynamic", .atom "term")]) =
            .ok (.atom "term") := by
          unfold Elixir.Module.Types.Descr.«upper_bound/1»; simp [getMapKeys_single, mapLookup]
        have lb : Elixir.Module.Types.Descr.«lower_bound/1» (D (m + 1)) (.map [(.atom "dynamic", .atom "term")]) =
            .ok (.map []) := by
          rw [lower_bound_run (Or.inr ⟨_, rfl⟩)]; simp [lower, rmDyn]
        refine ⟨.map [], .atom "term", lb, ub, de_none, Or.inl rfl, fun v => by simpa only [List.map_map] using upT v,
          fun h v => ⟨fun h' => absurd h' (denN_nil v), fun h' => absurd h' (hLo h v)⟩, dyn_sub (Or.inl rfl) (by omega),
          fun v h => absurd h (denN_nil v)⟩
      cases hc : (fdNil && !args.any isDynB || !cb)
      · -- Compatible arguments of a gradual application.
        have hA : (fdNil && !args.any isDynB) = Bool.false := (Bool.or_eq_false_iff.mp hc).1
        have hcb : cb = Bool.true := by simpa using (Bool.or_eq_false_iff.mp hc).2
        have okH : ok := by
          obtain ⟨hL, w, hU, hP⟩ := cbSem.mp hcb
          exact Or.inr ⟨hA, fun w hw => (coversL w hw).mp (hL w hw), w, hU, (covers w hU).mp hP⟩
        refine ⟨fun _ => ?_, fun h => absurd okH h⟩
        rcases hs with rfl | rfl
        · simp [Erlang.erlang.«/=/2», Lynx.Except.andAlso, Elixir.Module.Types.Descr.«dynamic/0»]
          exact dynR _ _ (fun h => by simp at h)
        · simp [Erlang.erlang.«/=/2», Lynx.Except.andAlso, Elixir.Module.Types.Descr.«dynamic/0»,
            map_lower_g hargs m]
          have lZ : ∀ z ∈ args.map lower, DE (level t d).E z ∧ lh z < H := by
            intro z mz; obtain ⟨x, mx, rfl⟩ := List.mem_map.mp mz; exact ⟨(hargs x mx).2.1, (hl x mx).2⟩
          have lenL : (args.map lower).length = args.length := List.length_map ..
          cases Qs with
          | nil =>
            simp [Term.list, Erlang.erlang.«==/2»]
            refine dynR _ _ fun _ v h => ?_
            obtain ⟨g, vg, lg, -⟩ := h
            obtain ⟨q, mq, -⟩ := nQs.cover g vg lg
            cases mq
          | cons q Qs' =>
            obtain ⟨h₀, tl, hcons⟩ : ∃ h₀ tl, Term.list ((List.map encP (q :: Qs')).reverse) = .cons h₀ tl := by
              cases e : (List.map encP (q :: Qs')).reverse with
              | nil => simp at e
              | cons h₀ tl => exact ⟨h₀, Term.list tl, by simp [Term.list]⟩
            rw [hcons]
            simp [Erlang.erlang.«==/2»]
            rw [← hcons]
            obtain ⟨sr, r, rsr, rsr', ru, sem⟩ := static_mixed two nQs (Or.inl rfl) upT lZ lenL
              (fun v h => imgP_mono inc lowIn h) (m := m) (by omega)
            have anyL := any_empty_s (fun z mz => (lZ z mz).1) hmd
            cases hE : (args.map lower).any (fun z => bp (∀ v : PN t d, ¬denD z v))
            · rw [hE] at anyL
              have rsr₁ := rsr hE
              simp only [List.map_cons, List.reverse_cons] at rsr₁
              simp [anyL, boolAtom, rsr₁, ru]
              obtain ⟨lr, ur, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := sem (.atom "false")
              exact ⟨lr, ur, h₁, h₂, h₃, h₄, fun v => by simpa [List.map_map] using h₅ v,
                fun h v => by simpa [List.map_map] using h₆ rfl v, h₇, h₈⟩
            · rw [hE] at anyL
              simp [anyL, boolAtom]
              refine dynR _ _ fun _ v h => ?_
              obtain ⟨z, mz, hz⟩ := List.any_eq_true.mp hE
              obtain ⟨g, -, -, x, hx, -⟩ := h
              obtain ⟨u, hu⟩ := inDomR_mem _ x (by simpa only [List.map_map] using hx) z mz
              exact bp_true.mp hz u ((den_succ (lZ z mz).1 u).mp hu)
      · simp [Erlang.erlang.«/=/2», Lynx.Except.andAlso]
        have nok : ¬ok := by
          rintro (h | ⟨hA, hL, w, hU, hP⟩)
          · exact hsub fun w hw => (covers w hw).mpr (h w hw)
          · have hcb := cbSem.mpr ⟨fun w hw => (coversL w hw).mpr (hL w hw), w, hU, (covers w hU).mpr hP⟩
            rw [hA, hcb] at hc
            cases hc
        have bad : ∀ (x : Except Exception Term) r, (do let y ← x; Except.ok (Term.tuple #[.atom "badarg", y, .atom "false"])) ≠
            Except.ok (Term.tuple #[.atom "ok", r]) := by
          intro x r; cases x <;> simp [bind, Except.bind]
        exact ⟨fun h => absurd h nok, fun _ r => bad _ r⟩

/-- `fun_apply_with_strategy/4` succeeds exactly on the conditions of `AppOK`, with the images of the lower bounds of
the arguments by the static part and of their upper bounds by the dynamic part as the bounds of its result. -/
theorem strategy_gsem {H : Nat} (two : 2 ≤ H) {Xs : List (Term × Term)} (hXs : DE (level t (d + 1)).E (.map Xs))
    (lXs : lh (.map Xs) < H) {fd Fd : Term} (fdNil : Bool)
    (mode : (fdNil = Bool.true ∧ fd = .atom "nil" ∧ Fd = .map Xs) ∨
      (fdNil = Bool.false ∧ fd = Fd ∧ DE (level t (d + 1)).E Fd ∧ lh Fd < H ∧
        ∀ b g, (∀ r ∈ g, FunSem.ValidRow b r) → FunT t (d + 1) (.map Xs) b g → FunT t (d + 1) Fd b g))
    {args : List Term} (hargs : ∀ x ∈ args, GD t d x) (hl : ∀ x ∈ args, lh (upper x) < H ∧ lh (lower x) < H)
    {s : Term} (hs : s = .atom "true" ∨ s = .atom "false") {m : Nat} (hm : (level t (d + 1)).K + 40 ≤ m) :
    (AppOK t d (.map Xs) Fd args → ∃ r, Elixir.Module.Types.Descr.«fun_apply_with_strategy/4» (D (m + 1)) (.map Xs) fd
        (Term.list args) s = .ok (.tuple #[.atom "ok", r]) ∧
      ResSem t d (m + 1) s r
        (ImgP args.length (FunT t (d + 1) (.map Xs) args.length) (FunSem.InDomR ((args.map lower).map (level t (d + 1)).den)))
        (ImgP args.length (FunT t (d + 1) Fd args.length) (FunSem.InDomR ((args.map upper).map (level t (d + 1)).den)))) ∧
    (¬AppOK t d (.map Xs) Fd args → ∀ r, Elixir.Module.Types.Descr.«fun_apply_with_strategy/4» (D (m + 1)) (.map Xs) fd
      (Term.list args) s ≠ .ok (.tuple #[.atom "ok", r])) := by
  have hmd : (level t d).K + 23 ≤ m := by rw [level_K] at hm ⊢; omega
  have hfdNil : Erlang.erlang.«==/2» fd (.atom "nil") = .ok (boolAtom fdNil) := by
    rcases mode with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, hFd, -⟩
    · rfl
    · rcases hFd with rfl | ⟨Y, rfl, -⟩ <;> simp [Erlang.erlang.«==/2»]
  have anyU := any_empty_g hargs hmd
  by_cases nne : ¬∀ x ∈ args, ∃ v : PN t d, denD (upper x) v
  · have ne := nne
    have e : args.any (fun a => bp (∀ v : PN t d, ¬denD (upper a) v)) = Bool.true := by
      obtain ⟨x, hx⟩ := Classical.not_forall.mp ne
      obtain ⟨mx, hx⟩ := Classical.not_imp.mp hx
      exact List.any_eq_true.mpr ⟨x, mx, bp_true.mpr fun v h => hx ⟨v, h⟩⟩
    rw [e] at anyU
    refine ⟨fun h => absurd h.1 ne, fun r => ?_⟩
    unfold Elixir.Module.Types.Descr.«fun_apply_with_strategy/4»
    simp [anyU, boolAtom_true]
  have ne := Classical.not_not.mp nne
  have noE : args.any (fun a => bp (∀ v : PN t d, ¬denD (upper a) v)) = Bool.false :=
    List.any_eq_false.mpr fun x mx h => by obtain ⟨v, hv⟩ := ne x mx; exact (bp_true.mp h) v hv
  rw [noE] at anyU
  have NB : NormBoth t (d + 1) H (.map Xs) Fd args.length
        (Elixir.Module.Types.Descr.«fun_normalize_both/3» (D (m + 1)) (.map Xs) fd (.integer args.length)) ∧
      (fdNil = Bool.true → ∀ (dom : Term) (Qs Qd : List (List (Term × List Term × Term))),
        Elixir.Module.Types.Descr.«fun_normalize_both/3» (D (m + 1)) (.map Xs) fd (.integer args.length) =
          .ok (.tuple #[.atom "ok", dom, Term.list (Qs.reverse.map encP), Term.list (Qd.reverse.map encP)]) → Qs = Qd) := by
    rcases mode with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, hFd, lFd, inc⟩
    · obtain ⟨h₁, h₂⟩ := normalize_both_s two hXs lXs args.length (m := m + 1) (by omega)
      exact ⟨h₁, fun _ => h₂⟩
    · exact ⟨normalize_both_g two hXs lXs hFd lFd inc _ (by omega), fun h => by cases h⟩
  by_cases okNB : ∃ y z w, Elixir.Module.Types.Descr.«fun_normalize_both/3» (D (m + 1)) (.map Xs) fd
      (.integer args.length) = .ok (.tuple #[.atom "ok", y, z, w])
  · obtain ⟨dom, Qs, Qd, nQs, nQd, neQd, gd, domPts, other, hnb⟩ := normBoth_common NB.1 okNB
    have inc : ∀ g, (∀ r ∈ g, FunSem.ValidRow args.length r) → FunT t (d + 1) (.map Xs) args.length g →
        FunT t (d + 1) Fd args.length g := by
      rcases mode with ⟨-, -, rfl⟩ | ⟨-, -, -, -, inc⟩
      · exact fun _ _ h => h
      · exact inc _
    have fdT : (fdNil && !args.any isDynB) = Bool.true → fdNil = Bool.true ∧ ∀ x ∈ args, isDynB x = Bool.false := by
      intro h
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      exact ⟨h.1, fun x mx => Bool.eq_false_iff.mpr (List.any_eq_false.mp h.2 x mx)⟩
    have same : (fdNil && !args.any isDynB) = Bool.true → Qs = Qd ∧
        ∀ g, FunT t (d + 1) (.map Xs) args.length g ↔ FunT t (d + 1) Fd args.length g := by
      intro h
      have hn := (fdT h).1
      refine ⟨NB.2 hn _ _ _ hnb, ?_⟩
      rcases mode with ⟨-, -, rfl⟩ | ⟨e, -⟩
      · exact fun _ => Iff.rfl
      · rw [e] at hn; cases hn
    obtain ⟨hOK, hNot⟩ := strategy_core two fdNil hfdNil hargs hl ne nQs nQd neQd gd domPts inc same hs hm hnb
    have live := norm_live nQd neQd
    have equiv : AppOK t d (.map Xs) Fd args ↔
        ((∀ w, FunSem.InDomR ((args.map upper).map (level t (d + 1)).den) w →
            Safe args.length (FunT t (d + 1) (.map Xs) args.length) w ∨ Safe args.length (FunT t (d + 1) Fd args.length) w) ∨
          ((fdNil && !args.any isDynB) = Bool.false ∧
            (∀ w, FunSem.InDomR ((args.map lower).map (level t (d + 1)).den) w →
              Safe args.length (FunT t (d + 1) (.map Xs) args.length) w ∨
                Safe args.length (FunT t (d + 1) Fd args.length) w) ∧
            ∃ w, FunSem.InDomR ((args.map upper).map (level t (d + 1)).den) w ∧
              (Safe args.length (FunT t (d + 1) (.map Xs) args.length) w ∨
                Safe args.length (FunT t (d + 1) Fd args.length) w))) := by
      constructor
      · rintro ⟨-, -, -, h | ⟨hL, hU⟩⟩
        · exact Or.inl h
        · cases hA : (fdNil && !args.any isDynB)
          · exact Or.inr ⟨rfl, hL, hU⟩
          · obtain ⟨eU, eL⟩ := static_bounds hargs (fdT hA).2
            refine Or.inl fun w hw => hL w ?_
            rw [eL]; rw [eU] at hw; exact hw
      · rintro (h | ⟨-, hL, hU⟩)
        · exact ⟨ne, other, live, Or.inl h⟩
        · exact ⟨ne, other, live, Or.inr ⟨hL, hU⟩⟩
    exact ⟨fun h => hOK (equiv.mp h), fun h => hNot (mt equiv.mpr h)⟩
  · rcases NB.1 with ⟨_, _, _, _, _, _, _, _, _, _, e⟩ | ⟨_, _, _, _, _, _, _, e⟩ | ⟨n2, n4, why⟩
    · exact absurd ⟨_, _, _, e⟩ okNB
    · exact absurd ⟨_, _, _, e⟩ okNB
    refine ⟨fun h => ?_, fun _ r => ?_⟩
    · rcases why with ⟨b, g, vg, hb, hg⟩ | dead
      · exact (h.2.1 b g vg hb hg).elim
      · obtain ⟨g, vg, hg⟩ := h.2.2.1
        exact (dead g vg hg).elim
    · unfold Elixir.Module.Types.Descr.«fun_apply_with_strategy/4»
      simp only [pure_bind]
      simp only [anyU]
      simp [boolAtom_false, length_list]
      generalize Elixir.Module.Types.Descr.«fun_normalize_both/3» (D (m + 1)) (.map Xs) fd (.integer args.length) = nb
        at n2 okNB ⊢
      cases nb with
      | error e => simp [bind, Except.bind]
      | ok v =>
        simp only [bind, Except.bind]
        split
        · exact (okNB ⟨_, _, _, rfl⟩).elim
        · intro e; exact n2 r e

/-- Functions of a type are its function points. -/
theorem funT_fpt {T : Term} (hT : DE (level t (d + 1)).E T) (a : Nat) (g : List (FunSem.Row (level t (d + 1)).V))
    (vg : ∀ r ∈ g, FunSem.ValidRow a r) : FunT t (d + 1) T a g ↔ denD T (fpt (t := t) (n := d + 1) a g vg) := by
  rcases hT with rfl | ⟨X, rfl, -⟩
  · exact ⟨fun _ => denD_term _, fun _ => Or.inl rfl⟩
  · rw [denD_fpt]
    constructor
    · rintro (h | ⟨Y, e, h⟩)
      · cases h
      · simp only [Term.map.injEq] at e; subst e; exact h
    · exact fun h => Or.inr ⟨X, rfl, h⟩

/-- All functions of an arity give every value on arguments. -/
theorem img_top {V : Type} {a : Nat} {Live : List (FunSem.Row V) → Prop} {I : List V → Prop}
    (top : ∀ g, (∀ r ∈ g, FunSem.ValidRow a r) → Live g) {w : List V} (hw : I w) (lw : w.length = a) (v : V) :
    ImgP a Live I v := by
  have vg : ∀ r ∈ [(w.map some, some v)], FunSem.ValidRow a r := by
    intro r mr
    simp only [List.mem_singleton] at mr
    subst mr
    exact ⟨by simp [lw], fun h => by simp at h⟩
  exact ⟨_, vg, top _ vg, w, hw, List.mem_singleton_self _⟩

/-- `dynamic_fun_top?/1` recognizes types holding every function. -/
theorem dyn_top {Dy : Term} (hD : DE (level t (d + 1)).E Dy) :
    ∃ tb, Elixir.Module.Types.Descr.«dynamic_fun_top?/1» Dy = .ok (boolAtom tb) ∧
      (tb = Bool.true → ∀ a g, FunT t (d + 1) Dy a g) := by
  rcases hD with rfl | ⟨Y, rfl, sY⟩
  · exact ⟨Bool.true, rfl, fun _ _ _ => Or.inl rfl⟩
  · cases hY : mapLookup Y (.atom "fun") with
    | none =>
      refine ⟨Bool.false, ?_, fun h => by cases h⟩
      unfold Elixir.Module.Types.Descr.«dynamic_fun_top?/1»
      simp [getMapKeys_single, hY]
    | some F =>
      rcases sY.fields "fun" F hY with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, fF⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> try (simp at e; done)
      obtain ⟨pos, R, rfl, -⟩ := fF
      cases pos
      · cases R with
        | nil =>
          refine ⟨Bool.true, ?_, fun _ a g => Or.inr ⟨Y, rfl, _, hY, by simp [arityOf, mapLookup]⟩⟩
          unfold Elixir.Module.Types.Descr.«dynamic_fun_top?/1»
          simp [getMapKeys_single, hY, Erlang.erlang.«==/2»]
        | cons r R =>
          refine ⟨Bool.false, ?_, fun h => by cases h⟩
          unfold Elixir.Module.Types.Descr.«dynamic_fun_top?/1»
          simp [getMapKeys_single, hY, Erlang.erlang.«==/2»]
      · refine ⟨Bool.false, ?_, fun h => by cases h⟩
        unfold Elixir.Module.Types.Descr.«dynamic_fun_top?/1»
        simp [getMapKeys_single, hY]

/-- `fun_apply/3` on a gradual function succeeds exactly when its lower bound holds functions only and `AppOK` holds
for its bounds, with the images of the bounds of the arguments by the bounds of the function as the bounds of its
result. -/
theorem apply_gsem {H : Nat} (two : 2 ≤ H) {f : Term} (hf : GD t (d + 1) f) (lf : lh (lower f) < H ∧ lh (upper f) < H)
    {args : List Term} (hargs : ∀ x ∈ args, GD t d x) (hl : ∀ x ∈ args, lh (upper x) < H ∧ lh (lower x) < H)
    {s : Term} (hs : s = .atom "true" ∨ s = .atom "false") {m : Nat} (hm : (level t (d + 1)).K + 40 ≤ m) :
    ((∀ v : PN t (d + 1), v.1.1 ≠ "fun" → ¬denD (lower f) v) ∧ AppOK t d (lower f) (upper f) args →
      ∃ r, Elixir.Module.Types.Descr.«fun_apply/3» (D (m + 1)) f (Term.list args) s = .ok (.tuple #[.atom "ok", r]) ∧
        ResSem t d (m + 1) s r
          (ImgP args.length (FunT t (d + 1) (lower f) args.length)
            (FunSem.InDomR ((args.map lower).map (level t (d + 1)).den)))
          (ImgP args.length (FunT t (d + 1) (upper f) args.length)
            (FunSem.InDomR ((args.map upper).map (level t (d + 1)).den)))) ∧
    (¬((∀ v : PN t (d + 1), v.1.1 ≠ "fun" → ¬denD (lower f) v) ∧ AppOK t d (lower f) (upper f) args) →
      ∀ r, Elixir.Module.Types.Descr.«fun_apply/3» (D (m + 1)) f (Term.list args) s ≠ .ok (.tuple #[.atom "ok", r])) := by
  have hmd : (level t d).K + 23 ≤ m := by rw [level_K] at hm ⊢; omega
  rcases hf.1.shape with rfl | ⟨X, rfl⟩
  · have bad : ¬∀ v : PN t (d + 1), v.1.1 ≠ "fun" → ¬denD (lower (.atom "term")) v :=
      fun h => h (tpt []) (by simp [tpt]) (denD_term _)
    refine ⟨fun h => absurd h.1 bad, fun _ r => ?_⟩
    rw [Elixir.Module.Types.Descr.«fun_apply/3».eq_def]; simp
  cases hD : mapLookup X (.atom "dynamic") with
  | none =>
    have eL : lower (.map X) = .map X := by simp [lower, rmDyn_static hD]
    have eU : upper (.map X) = .map X := by simp [upper, hD]
    have hX : DE (level t (d + 1)).E (.map X) := eL ▸ hf.2.1
    rw [eL, eU]
    rw [eL] at lf
    rw [apply_head hD _ (fun_only_run hX (m := m + 1) (by omega))]
    obtain ⟨h₁, h₂⟩ := strategy_gsem two hX lf.1 Bool.true (Or.inl ⟨rfl, rfl, rfl⟩) hargs hl hs hm
    by_cases fo : ∀ v : PN t (d + 1), v.1.1 ≠ "fun" → ¬denD (.map X) v
    · simp only [bp_true.mpr fo, ite_true]
      exact ⟨fun h => h₁ h.2, fun h => h₂ fun a => h ⟨fo, a⟩⟩
    · simp only [bp_false.mpr fo, Bool.false_eq_true, ite_false]
      exact ⟨fun h => absurd h.1 fo, fun _ r e => by cases e⟩
  | some Dy =>
    have eU : upper (.map X) = Dy := by simp [upper, hD]
    have hS : DE (level t (d + 1)).E (lower (.map X)) := hf.2.1
    have hDy : DE (level t (d + 1)).E Dy := eU ▸ hf.2.2
    have inc : ∀ b g, (∀ r ∈ g, FunSem.ValidRow b r) → FunT t (d + 1) (lower (.map X)) b g → FunT t (d + 1) Dy b g := by
      intro b g vg h
      rw [funT_fpt hS b g vg] at h
      rw [funT_fpt hDy b g vg, ← eU]
      exact hf.1.inv (toTPN _) ((denD_lower (.map X) (toTPN _)).mp h)
    have take : Erlang.maps.«take/2» (.atom "dynamic") (.map X) = .ok (.tuple #[Dy, lower (.map X)]) := by
      simp [Erlang.maps.«take/2», hD, lower, rmDyn]
    rw [eU]
    rw [eU] at lf
    rw [Elixir.Module.Types.Descr.«fun_apply/3».eq_def]
    simp only [take, Lynx.Except.ok_bind]
    have eL : lower (.map X) = .map (rmDyn X) := rfl
    rw [eL] at hS inc lf ⊢
    generalize rmDyn X = S at hS inc lf ⊢
    obtain ⟨tb, htb, top⟩ := dyn_top hDy
    simp only [htb]
    by_cases sc : S = [] ∧ tb = Bool.true
    · -- The dynamic part holds every function, and the static part none.
      obtain ⟨rfl, rfl⟩ := sc
      have anyU := any_empty_g hargs hmd
      have fa : ((∀ v : PN t (d + 1), v.1.1 ≠ "fun" → ¬denD (.map []) v) ∧ AppOK t d (.map []) Dy args) ↔
          AppOK t d (.map []) Dy args := ⟨And.right, fun h => ⟨fun v _ => denN_nil v, h⟩⟩
      rw [fa]
      simp [Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«/=/2»]
      have noS : ∀ (b : Nat) g, ¬FunT t (d + 1) (.map []) b g := by
        rintro b g (h | ⟨Y, e, F, hF, -⟩)
        · cases h
        · simp only [Term.map.injEq] at e; subst e; simp [mapLookup] at hF
      by_cases ne : ∀ x ∈ args, ∃ v : PN t d, denD (upper x) v
      · have noE : args.any (fun a => bp (∀ v : PN t d, ¬denD (upper a) v)) = Bool.false :=
          List.any_eq_false.mpr fun x mx h => by obtain ⟨v, hv⟩ := ne x mx; exact (bp_true.mp h) v hv
        rw [noE] at anyU
        obtain ⟨w, hw⟩ := inDomR_exists ((args.map upper).map (level t (d + 1)).den) fun u mu => by
          obtain ⟨z, mz, rfl⟩ := List.mem_map.mp mu
          obtain ⟨x, mx, rfl⟩ := List.mem_map.mp mz
          obtain ⟨v, hv⟩ := ne x mx
          exact ⟨v, (den_succ (hargs x mx).2.2 v).mpr hv⟩
        have lw : w.length = args.length := by simpa using FunSem.inDomR_length hw
        have okH : AppOK t d (.map []) Dy args :=
          ⟨ne, fun b g _ _ => noS b g, ⟨[], by simp, top rfl _ _⟩,
            Or.inl fun w _ => Or.inl fun g _ h => absurd h (noS _ g)⟩
        refine ⟨fun _ => ⟨.map [(.atom "dynamic", .atom "term")], ?_, ?_⟩, fun h => absurd okH h⟩
        · simp [anyU, boolAtom, Elixir.Module.Types.Descr.«dynamic/0»]
        · have ub : Elixir.Module.Types.Descr.«upper_bound/1» (D (m + 1)) (.map [(.atom "dynamic", .atom "term")]) =
              .ok (.atom "term") := by
            unfold Elixir.Module.Types.Descr.«upper_bound/1»; simp [getMapKeys_single, mapLookup]
          have lb : Elixir.Module.Types.Descr.«lower_bound/1» (D (m + 1)) (.map [(.atom "dynamic", .atom "term")]) =
              .ok (.map []) := by
            rw [lower_bound_run (Or.inr ⟨_, rfl⟩)]; simp [lower, rmDyn]
          refine ⟨.map [], .atom "term", lb, ub, de_none, Or.inl rfl,
            fun v => ⟨fun _ => by simpa only [List.map_map] using img_top (fun g _ => top rfl args.length g) hw lw v,
              fun _ => denD_term v⟩,
            fun _ v => ⟨fun h => absurd h (denN_nil v), fun h => ?_⟩, dyn_sub (Or.inl rfl) (by omega),
              fun v h => absurd h (denN_nil v)⟩
          obtain ⟨g, -, hg, -⟩ := h
          exact absurd hg (noS _ g)
      · have e : args.any (fun a => bp (∀ v : PN t d, ¬denD (upper a) v)) = Bool.true := by
          obtain ⟨x, hx⟩ := Classical.not_forall.mp ne
          obtain ⟨mx, hx⟩ := Classical.not_imp.mp hx
          exact List.any_eq_true.mpr ⟨x, mx, bp_true.mpr fun v h => hx ⟨v, h⟩⟩
        rw [e] at anyU
        refine ⟨fun h => absurd h.1 ne, fun _ r => ?_⟩
        simp [anyU, boolAtom]
    · have nsc : ∀ bb, Lynx.Except.andAlso (Erlang.erlang.«==/2» (.map S) (.map [])) (.ok (boolAtom tb)) bb =
          .ok (.atom "false") := by
        intro bb
        cases S with
        | nil => cases tb <;> simp_all [Erlang.erlang.«==/2», Lynx.Except.andAlso]
        | cons x S => simp [Erlang.erlang.«==/2», Lynx.Except.andAlso]
      simp only [nsc]
      obtain ⟨h₁, h₂⟩ := strategy_gsem two hS lf.1 Bool.false (Or.inr ⟨rfl, rfl, hDy, lf.2, inc⟩) hargs hl hs hm
      have foRun := fun_only_run hS (m := m + 1) (by omega)
      by_cases fo : ∀ v : PN t (d + 1), v.1.1 ≠ "fun" → ¬denD (.map S) v
      · rw [bp_true.mpr fo] at foRun
        have fa : ((∀ v : PN t (d + 1), v.1.1 ≠ "fun" → ¬denD (.map S) v) ∧ AppOK t d (.map S) Dy args) ↔
            AppOK t d (.map S) Dy args := ⟨And.right, fun h => ⟨fo, h⟩⟩
        rw [fa]
        simp [Erlang.erlang.«/=/2», Lynx.Except.andAlso, foRun]
        exact ⟨fun h => by simpa only [List.map_map] using h₁ h, fun h => h₂ h⟩
      · rw [bp_false.mpr fo] at foRun
        refine ⟨fun h => absurd h.1 fo, fun _ r => ?_⟩
        simp [Erlang.erlang.«/=/2», Lynx.Except.andAlso, foRun]

/-! The predicates of the gradual laws. -/

/-- Lists related element by element. -/
inductive Pairwise2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Pairwise2 R [] []
  | cons {a : α} {b : β} {l : List α} {l' : List β} : R a b → Pairwise2 R l l' → Pairwise2 R (a :: l) (b :: l')

theorem gradual_arguments_ok {n m : Nat} (hm : (level t n).K + 15 ≤ m) :
    ∀ {args : Term}, «gradual_arguments?/2» (D m) args (.tuple #[.integer n, t]) = .ok (.atom "true") →
      ∃ l, args = Term.list l ∧ ∀ a ∈ l, GD t n a
  | .cons a rest, h => by
    unfold «gradual_arguments?/2» at h
    obtain ⟨h₁, h₂⟩ := (Lynx.Except.andAlso_eq_true _ _ _).mp h
    obtain ⟨l, rfl, hl⟩ := gradual_arguments_ok hm h₂
    refine ⟨a :: l, rfl, fun x mx => ?_⟩
    rcases List.mem_cons.mp mx with rfl | mx
    · exact arrows_gradual_ok hm h₁
    · exact hl x mx
  | .nil, _ => ⟨[], rfl, by simp⟩
  | .atom _, h | .integer _, h | .float _, h | .tuple _, h | .map _, h | .pid _, h
  | .reference _, h | .function .., h | .bitstring .., h => by
    unfold «gradual_arguments?/2» at h; simp at h

theorem and_true_atoms {p q : Bool} {b : Bool} (h : Lynx.Except.andAlso (.ok (boolAtom p)) (.ok (boolAtom q)) b =
    .ok (.atom "true")) : p = Bool.true ∧ q = Bool.true := by
  cases p <;> cases q <;> simp_all [boolAtom, Lynx.Except.andAlso]

theorem precise_ok {n m : Nat} (hm : (level t n).K + 23 ≤ m) {a b : Term} (ga : GD t n a) (gb : GD t n b)
    (h : «precise?/2» (D m) a b = .ok (.atom "true")) :
    SubN t n (lower b) (lower a) ∧ SubN t n (upper a) (upper b) := by
  unfold «precise?/2» at h
  simp only [lower_bound_run ga.1.shape, lower_bound_run gb.1.shape, upper_bound_run ga.1.ub,
    upper_bound_run gb.1.ub, Lynx.Except.ok_bind, next_sub gb.2.1 ga.2.1 hm, next_sub ga.2.2 gb.2.2 hm] at h
  obtain ⟨h₁, h₂⟩ := and_true_atoms h
  exact ⟨bp_true.mp h₁, bp_true.mp h₂⟩

theorem materializes_ok {n m : Nat} (hm : (level t n).K + 23 ≤ m) {g a : Term} (hg : DE (level t n).E g)
    (ga : GD t n a) (h : «materializes?/2» (D m) g a = .ok (.atom "true")) :
    SubN t n (lower a) g ∧ SubN t n g (upper a) := by
  unfold «materializes?/2» at h
  simp only [lower_bound_run ga.1.shape, upper_bound_run ga.1.ub, Lynx.Except.ok_bind,
    next_sub ga.2.1 hg hm, next_sub hg ga.2.2 hm] at h
  obtain ⟨h₁, h₂⟩ := and_true_atoms h
  exact ⟨bp_true.mp h₁, bp_true.mp h₂⟩

theorem all_precise_ok {n m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∀ {l l' : List Term}, (∀ a ∈ l, GD t n a) → (∀ b ∈ l', GD t n b) →
      «all_precise?/2» (D m) (Term.list l) (Term.list l') = .ok (.atom "true") →
      Pairwise2 (fun a b => SubN t n (lower b) (lower a) ∧ SubN t n (upper a) (upper b)) l l'
  | [], [], _, _, _ => .nil
  | a :: l, b :: l', gl, gl', h => by
    unfold «all_precise?/2» at h
    obtain ⟨h₁, h₂⟩ := (Lynx.Except.andAlso_eq_true _ _ _).mp h
    exact .cons (precise_ok hm (gl a List.mem_cons_self) (gl' b List.mem_cons_self) h₁)
      (all_precise_ok hm (fun x mx => gl x (List.mem_cons_of_mem _ mx)) (fun x mx => gl' x (List.mem_cons_of_mem _ mx)) h₂)
  | [], _ :: _, _, _, h | _ :: _, [], _, _, h => by unfold «all_precise?/2» at h; simp at h

theorem all_materialize_ok {n m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∀ {l l' : List Term}, (∀ a ∈ l, DE (level t n).E a) → (∀ b ∈ l', GD t n b) →
      «all_materialize?/2» (D m) (Term.list l) (Term.list l') = .ok (.atom "true") →
      Pairwise2 (fun g a => SubN t n (lower a) g ∧ SubN t n g (upper a)) l l'
  | [], [], _, _, _ => .nil
  | a :: l, b :: l', gl, gl', h => by
    unfold «all_materialize?/2» at h
    obtain ⟨h₁, h₂⟩ := (Lynx.Except.andAlso_eq_true _ _ _).mp h
    exact .cons (materializes_ok hm (gl a List.mem_cons_self) (gl' b List.mem_cons_self) h₁)
      (all_materialize_ok hm (fun x mx => gl x (List.mem_cons_of_mem _ mx))
        (fun x mx => gl' x (List.mem_cons_of_mem _ mx)) h₂)
  | [], _ :: _, _, _, h | _ :: _, [], _, _, h => by unfold «all_materialize?/2» at h; simp at h

theorem uppers_in_ok {n m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∀ {l l' : List Term}, (∀ a ∈ l, GD t n a) → (∀ b ∈ l', GD t n b) →
      «uppers_in?/2» (D m) (Term.list l) (Term.list l') = .ok (.atom "true") →
      Pairwise2 (fun a b => SubN t n (upper a) (upper b)) l l'
  | [], [], _, _, _ => .nil
  | a :: l, b :: l', gl, gl', h => by
    unfold «uppers_in?/2» at h
    have ga := gl a List.mem_cons_self
    have gb := gl' b List.mem_cons_self
    simp only [upper_bound_run ga.1.ub, upper_bound_run gb.1.ub, Lynx.Except.ok_bind,
      next_sub ga.2.2 gb.2.2 hm] at h
    obtain ⟨h₁, h₂⟩ := (Lynx.Except.andAlso_eq_true _ _ _).mp h
    refine .cons (bp_true.mp (by simpa [boolAtom] using h₁)) (uppers_in_ok hm (fun x mx => gl x (List.mem_cons_of_mem _ mx))
      (fun x mx => gl' x (List.mem_cons_of_mem _ mx)) h₂)
  | [], _ :: _, _, _, h | _ :: _, [], _, _, h => by unfold «uppers_in?/2» at h; simp at h

/-- Argument tuples grow with their types. -/
theorem inDomR_mono {V : Type} : ∀ {P Q : List (V → Prop)}, Pairwise2 (fun p q => ∀ v, p v → q v) P Q →
    ∀ {w : List V}, FunSem.InDomR P w → FunSem.InDomR Q w
  | [], [], .nil, [], _ => trivial
  | _ :: _, _ :: _, .cons hpq rest, _ :: _, h => ⟨hpq _ h.1, inDomR_mono rest h.2⟩
  | [], [], .nil, _ :: _, h => h.elim
  | _ :: _, _ :: _, .cons _ _, [], h => h.elim

/-- Pointwise inclusions of argument types, as the tuples they hold. -/
theorem inDomR_sub {l l' : List Term} {f f' : Term → Term} (hl : ∀ a ∈ l, DE (level t d).E (f a))
    (hl' : ∀ b ∈ l', DE (level t d).E (f' b)) (h : Pairwise2 (fun a b => SubN t d (f a) (f' b)) l l') {w} :
    FunSem.InDomR ((l.map f).map (level t (d + 1)).den) w → FunSem.InDomR ((l'.map f').map (level t (d + 1)).den) w := by
  apply inDomR_mono
  simp only [List.map_map]
  induction h with
  | nil => exact .nil
  | cons hab rest ih =>
    rename_i a b l l'
    refine .cons (fun v hv => ?_) (ih (fun x mx => hl x (List.mem_cons_of_mem _ mx))
      (fun x mx => hl' x (List.mem_cons_of_mem _ mx)))
    have ha := hl a List.mem_cons_self
    have hb := hl' b List.mem_cons_self
    exact (den_succ hb v).mpr (hab v ((den_succ ha v).mp hv))

/-- When the application of a gradual function to gradual arguments succeeds: its lower bound holds functions only,
and `AppOK` holds for its bounds. -/
def AppC (t : Term) (d : Nat) (f : Term) (l : List Term) : Prop :=
  (∀ v : PN t (d + 1), v.1.1 ≠ "fun" → ¬denD (lower f) v) ∧ AppOK t d (lower f) (upper f) l

/-- The image of the lower bounds of the arguments by the lower bound of the function. -/
def LoI (t : Term) (d : Nat) (f : Term) (l : List Term) : (level t (d + 1)).V → Prop :=
  ImgP l.length (FunT t (d + 1) (lower f) l.length) (FunSem.InDomR ((l.map lower).map (level t (d + 1)).den))

/-- The image of the upper bounds of the arguments by the upper bound of the function. -/
def UpI (t : Term) (d : Nat) (f : Term) (l : List Term) : (level t (d + 1)).V → Prop :=
  ImgP l.length (FunT t (d + 1) (upper f) l.length) (FunSem.InDomR ((l.map upper).map (level t (d + 1)).den))

/-- `fun_apply/3` on gradual functions and arguments of the laws: it succeeds on `AppC` in both modes, with
`LoI` and `UpI` as the bounds of its result. -/
theorem apply_law {f : Term} {l : List Term} (hf : GD t (d + 1) f) (hl : ∀ a ∈ l, GD t d a) {s : Term}
    (hs : s = .atom "true" ∨ s = .atom "false") {m : Nat} (hm : (level t (d + 1)).K + 41 ≤ m) :
    (AppC t d f l → ∃ r, Elixir.Module.Types.Descr.«fun_apply/3» (D m) f (Term.list l) s = .ok (.tuple #[.atom "ok", r]) ∧
      ResSem t d m s r (LoI t d f l) (UpI t d f l)) ∧
    (¬AppC t d f l → ∀ r, Elixir.Module.Types.Descr.«fun_apply/3» (D m) f (Term.list l) s ≠
      .ok (.tuple #[.atom "ok", r])) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  let L := l.map upper ++ l.map lower
  let H := max (lh (lower f)) (lh (upper f)) + (L.map lh).foldr max 0 + 2
  have bl : ∀ a ∈ l, lh (upper a) < H ∧ lh (lower a) < H := fun a ma =>
    ⟨by have := lh_le_max L (upper a) (List.mem_append_left _ (List.mem_map_of_mem ma)); omega,
      by have := lh_le_max L (lower a) (List.mem_append_right _ (List.mem_map_of_mem ma)); omega⟩
  exact apply_gsem (H := H) (by omega) hf ⟨by omega, by omega⟩ hl bl hs (by omega)

theorem pairwise2_length {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β} (h : Pairwise2 R l l') :
    l.length = l'.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem boolean_mode {s : Term} (h : Erlang.erlang.«is_boolean/1» s = .ok (.atom "true")) :
    s = .atom "true" ∨ s = .atom "false" := by
  cases s <;> simp [Erlang.erlang.«is_boolean/1»] at h
  rename_i a
  by_cases e : a = "true"
  · exact Or.inl (by rw [e])
  · by_cases e' : a = "false"
    · exact Or.inr (by rw [e'])
    · simp_all

theorem pairwise2_imp {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) {l : List α} {l' : List β}
    (p : Pairwise2 R l l') : Pairwise2 S l l' := by
  induction p with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (h _ _ hab) ih

theorem pairwise2_imp_mem {α β : Type} {R S : α → β → Prop} {l : List α} {l' : List β}
    (h : ∀ a ∈ l, ∀ b, R a b → S a b) (p : Pairwise2 R l l') : Pairwise2 S l l' := by
  induction p with
  | nil => exact .nil
  | cons hab _ ih =>
    exact .cons (h _ List.mem_cons_self _ hab) (ih fun a ma => h a (List.mem_cons_of_mem _ ma))

/-- Functions of a type grow with it. -/
theorem funT_mono {T T' : Term} (hT : DE (level t (d + 1)).E T) (hT' : DE (level t (d + 1)).E T')
    (sub : SubN t (d + 1) T T') {a : Nat} {g : List (FunSem.Row (level t (d + 1)).V)} (vg : ∀ r ∈ g, FunSem.ValidRow a r)
    (h : FunT t (d + 1) T a g) : FunT t (d + 1) T' a g :=
  (funT_fpt hT' a g vg).mpr (sub _ ((funT_fpt hT a g vg).mp h))

theorem pairwise2_swap {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β} (p : Pairwise2 R l l') :
    Pairwise2 (fun b a => R a b) l' l := by
  induction p with
  | nil => exact .nil
  | cons hab _ ih => exact .cons hab ih

theorem pairwise2_refl {α : Type} {R : α → α → Prop} : ∀ {l : List α}, (∀ a ∈ l, R a a) → Pairwise2 R l l
  | [], _ => .nil
  | a :: _, h => .cons (h a List.mem_cons_self) (pairwise2_refl fun x mx => h x (List.mem_cons_of_mem _ mx))

theorem pairwise2_right {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β} (p : Pairwise2 R l l') :
    ∀ b ∈ l', ∃ a ∈ l, R a b := by
  induction p with
  | nil => intro b mb; cases mb
  | cons hab _ ih =>
    intro b mb
    rcases List.mem_cons.mp mb with rfl | mb
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ma, h⟩ := ih b mb; exact ⟨a, List.mem_cons_of_mem _ ma, h⟩

theorem safe_anti {V : Type} {a : Nat} {L L' : List (FunSem.Row V) → Prop}
    (h : ∀ g, (∀ r ∈ g, FunSem.ValidRow a r) → L' g → L g) {w : List V} (s : Safe a L w) : Safe a L' w :=
  fun g vg hg => s g vg (h g vg hg)

/-- The tuples of the lower bounds of gradual arguments are tuples of their upper bounds. -/
theorem low_up {l : List Term} (hl : ∀ a ∈ l, GD t d a) {w : List (level t (d + 1)).V}
    (h : FunSem.InDomR ((l.map lower).map (level t (d + 1)).den) w) :
    FunSem.InDomR ((l.map upper).map (level t (d + 1)).den) w :=
  inDomR_sub (fun a ma => (hl a ma).2.1) (fun a ma => (hl a ma).2.2)
    (pairwise2_refl fun a ma => gd_lu (hl a ma)) h

/-- Applications succeed on less precise functions and arguments. -/
theorem appC_mono {f f₂ : Term} (hf : GD t (d + 1) f) (hf₂ : GD t (d + 1) f₂)
    (pf : SubN t (d + 1) (lower f₂) (lower f) ∧ SubN t (d + 1) (upper f) (upper f₂)) {l l₂ : List Term}
    (hl : ∀ a ∈ l, GD t d a) (hl₂ : ∀ a ∈ l₂, GD t d a)
    (pa : Pairwise2 (fun a b => SubN t d (lower b) (lower a) ∧ SubN t d (upper a) (upper b)) l l₂)
    (C : AppC t d f l) : AppC t d f₂ l₂ := by
  obtain ⟨fo, ne, other, ⟨g₀, vg₀, live⟩, dom⟩ := C
  have len := pairwise2_length pa
  have lowF : ∀ a g, (∀ r ∈ g, FunSem.ValidRow a r) → FunT t (d + 1) (lower f₂) a g → FunT t (d + 1) (lower f) a g :=
    fun a g vg h => funT_mono hf₂.2.1 hf.2.1 pf.1 vg h
  have upF : ∀ a g, (∀ r ∈ g, FunSem.ValidRow a r) → FunT t (d + 1) (upper f) a g → FunT t (d + 1) (upper f₂) a g :=
    fun a g vg h => funT_mono hf.2.2 hf₂.2.2 pf.2 vg h
  have luF : ∀ a g, (∀ r ∈ g, FunSem.ValidRow a r) → FunT t (d + 1) (lower f) a g → FunT t (d + 1) (upper f) a g :=
    fun a g vg h => funT_mono hf.2.1 hf.2.2 (gd_lu hf) vg h
  -- Tuples safe for either bound of `f` are safe for the lower bound of `f₂`.
  have P : ∀ w, (Safe l.length (FunT t (d + 1) (lower f) l.length) w ∨ Safe l.length (FunT t (d + 1) (upper f) l.length) w) →
      Safe l₂.length (FunT t (d + 1) (lower f₂) l₂.length) w ∨ Safe l₂.length (FunT t (d + 1) (upper f₂) l₂.length) w := by
    intro w h
    rw [← len]
    refine Or.inl ?_
    rcases h with h | h
    · exact safe_anti (fun g vg hg => lowF _ g vg hg) h
    · exact safe_anti (fun g vg hg => luF _ g vg (lowF _ g vg hg)) h
  have upIn : ∀ w, FunSem.InDomR ((l.map upper).map (level t (d + 1)).den) w →
      FunSem.InDomR ((l₂.map upper).map (level t (d + 1)).den) w := fun w h =>
    inDomR_sub (fun a ma => (hl a ma).2.2) (fun a ma => (hl₂ a ma).2.2) (pairwise2_imp (fun _ _ h => h.2) pa) h
  have lowIn : ∀ w, FunSem.InDomR ((l₂.map lower).map (level t (d + 1)).den) w →
      FunSem.InDomR ((l.map lower).map (level t (d + 1)).den) w := fun w h =>
    inDomR_sub (fun a ma => (hl₂ a ma).2.1) (fun a ma => (hl a ma).2.1)
      (pairwise2_swap (pairwise2_imp (fun _ _ h => h.1) pa)) h
  -- Some tuple of the upper bounds of the arguments.
  obtain ⟨w₀, hw₀⟩ := inDomR_exists ((l.map upper).map (level t (d + 1)).den) fun u mu => by
    obtain ⟨z, mz, rfl⟩ := List.mem_map.mp mu
    obtain ⟨x, mx, rfl⟩ := List.mem_map.mp mz
    obtain ⟨v, hv⟩ := ne x mx
    exact ⟨v, (den_succ (hl x mx).2.2 v).mpr hv⟩
  refine ⟨fun v hv h => fo v hv (pf.1 v h), fun b mb => ?_, fun b g vg hb h => other b g vg (by rw [len]; exact hb)
    (lowF b g vg h), ⟨g₀, by rw [← len]; exact vg₀, by rw [← len]; exact upF _ g₀ vg₀ live⟩, ?_⟩
  · obtain ⟨a, ma, -, h⟩ := pairwise2_right pa b mb
    obtain ⟨v, hv⟩ := ne a ma
    exact ⟨v, h v hv⟩
  · refine Or.inr ⟨fun w hw => P w ?_, ?_⟩
    · rcases dom with h | ⟨h, -⟩
      · exact h w (low_up hl (lowIn w hw))
      · exact h w (lowIn w hw)
    · rcases dom with h | ⟨-, w, hw, hP⟩
      · exact ⟨w₀, upIn w₀ hw₀, P w₀ (h w₀ hw₀)⟩
      · exact ⟨w, upIn w hw, P w hP⟩

end

end Elixir.STTDescrProofsTest.Nest
