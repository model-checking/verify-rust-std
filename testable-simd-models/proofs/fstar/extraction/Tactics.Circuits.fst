/// This module defines a tactic for normalize circuit.
/// See section "What is a circuit?" in the documentation of the tactic `flatten_circuit`.

module Tactics.Circuits
open FStar.Tactics

/// A record that holds debugging methods.
/// This is useful for doing conditional debugging with context.
noeq type dbg = {
    print: (message:string) -> Tac unit;
    dump: (message:string) -> Tac unit;
    fail: #a:Type -> (message:string) -> Tac a;
    raw_sub: (subheader:string) -> Tac dbg;
    sub: (subheader:string) -> #t:Type -> (dbg -> Tac t) -> Tac t;
}

/// Make a no-op debugger
let rec mk_noop_dbg (): Tac dbg = {
    print = (fun _ -> ());
    dump = (fun _ -> ());
    fail = (fun msg -> fail msg);
    raw_sub = (fun _ -> mk_noop_dbg ());
    sub = (fun _ f -> f (mk_noop_dbg ()));
}

/// Helper that creates a effectful active debugger.
let rec mk_dbg_with (header: string): Tac dbg =
  let format msg = "[" ^ header ^ "] " ^ msg in
  let raw_sub subheader = mk_dbg_with (if header = "" then subheader else header ^ ":" ^ subheader) in
  {
    print = (fun msg -> print (format msg));
    dump = (fun msg -> dump (format msg));
    fail = (fun msg -> fail (format msg));
    raw_sub;
    sub = (fun subheader f -> 
      let time0 = curms () in
      let d = raw_sub subheader in
      d.print "> enter";
      let result = f d in
      let time = curms () - time0 in
      d.print ("< exit ("^string_of_int (time / 1000) ^ "." ^ string_of_int ((time/100)%10) ^ "s"^")");
      result
    )
  }

/// Make a debugger if `--ext debug_circuit_norm` is set 
/// (e.g. with `OTHERFLAGS="--ext debug_circuit_norm"`)
let mk_dbg (header: string): Tac dbg
    = let ext_key = "debug_circuit_norm" in
      let debug_mode = FStar.Stubs.Tactics.V2.Builtins.ext_enabled ext_key in
      if debug_mode then (mk_dbg_with ext_key).raw_sub header else mk_noop_dbg ()

let run_dbg (header: string) #t (f: dbg -> Tac t): Tac t = f (mk_dbg "")

let discharge_smt_goals_now () = iterAllSMT smt_sync

/// Expects `phi` to be of the shape `squash (lhs == rhs)`, returns `(<lhs>, <rhs>)`.
let expect_eq (phi: formula): Tac (term & term) =
  match phi with
  | FStar.Reflection.V1.Formula.Comp (FStar.Reflection.V1.Formula.Eq _) lhs rhs -> (lhs, rhs)
  | _ -> fail ("Expected [_ == _], got ["^formula_to_string phi^"]")

/// Running `rewrite_subterm_in_goal subterm tactic` on a goal where `subterm`
/// appears will call once `tactic` with a goal `squash (subterm == ?u)`.
/// `tactic` needs to fill the unification variable `?u` (e.g. using a `trefl`).
let rewrite_subterm_in_goal (subterm: term) (tactic: dbg -> Tac unit) (d: dbg): Tac unit
  = d.sub "rewrite_subterm_in_goal" (fun d ->
        ctrl_rewrite TopDown (fun t ->
            // Go top down until we reach `subterm`, and stop.
            if term_eq t subterm then (true, Abort) else (false, Continue)
        ) (fun _ -> d.sub "tactic" (fun d -> d.dump "rewrite this subterm"; tactic d))
    )

/// Helper for function `is_closed_term`
private exception IsClosedTerm of bool

/// Is the goal a closed term?
let is_closed_term (): Tac bool =
  try
    let _ = repeat clear_top in
    raise (IsClosedTerm (Nil? (cur_binders ())))
  with | IsClosedTerm e -> e | e -> raise e

/// Normalize fully (zeta_full) match closed-term scrutinees, effectively getting rid of (visible) control flow (unless terms are open).
let full_norm_scrutinees (d: dbg) =
    d.sub "full_norm_scrutinees" (fun d ->
        let norm_scrutinee_in_goal () =
            let goal = cur_goal () in
            let goal_phi = term_as_formula goal in
            let (lhs, _) = expect_eq goal_phi in
            (match inspect lhs with
            | Tv_Match scrut ret brs ->
                rewrite_subterm_in_goal scrut (fun d -> 
                    if is_closed_term () then (
                        norm [primops; iota; delta; zeta_full];
                        d.dump "`match` rewritten (norm)"
                    ) else d.dump "`match` **not** rewritten: the goal is not a closed term!";
                    trefl ()
                ) d;
                discharge_smt_goals_now ()
            | _ -> ());
            trefl ()
        in
        let one_round (): Tac unit =
            ctrl_rewrite TopDown (fun t ->
                let is_match = (match inspect t with | Tv_Match _ _ _ -> true | _ -> false) in
                (is_match, Continue)
            ) norm_scrutinee_in_goal
        in
        d.print "round 1";
        one_round ();
        d.print "round 2";
        one_round ()
    )

/// Returns the list ``[`f1; ...; `fN]`` of all reachable top-levels `f1` ... `fN` tagged with attribute `attr`.
let top_levels_of_attr (attr: term): Tac (list term) = 
    FStar.List.Tot.map
        (fun f -> pack_ln (Tv_FVar f)) 
        (lookup_attr attr (top_env ()))

/// Rewrite the goal, lifting _source functions_ that operates on _source types_ `Si` to a set of equivalent _destination functions_ operating on _destination types_ `Di`.
/// ## Definition
///
/// The _source types_ are denoted `S` or `Si`.
/// The _destination types_ are denoted `D` or `Dj`.
/// The _source functions_ are denoted `fS` or `fSi`.
/// The _destination functions_ are denoted `fD` or `fDi`.
/// `i` and `j` are used to range over sets of functions or types.
///
/// When a source type `S` can be transformed into a destination type `D`, we require:
///  - two _transformation functions_ `S_to_D: S -> D` and `S_to_D: S -> D` and,
///  - two lemma showing the two _transformations functions_ are inverse:
///     -  `S_D_lemma:  x:S -> (x == D_to_S (S_to_D x))` and
///     -  `D_S_lemma: x:D -> (x == S_to_D (D_to_S x))`.
///
/// For each source function `fS` of type `Si -> Sj` we require:
///   - a destination function `fD` of type `Di -> Dj`
///   - a lemma `fS_lemma: x:S -> (fS x == D_to_S (fD (S_to_D x)))`.
///
/// Additionally, direct transformations of destination types `Di_to_Dj: Di -> Dj` can be provided.
/// For each `Di_to_Dj` we require a lemma `Di_to_Dj_lemma: x:Di -> (S_to_Dj (Di_to_S x) == Di_to_Dj x)`, that is, the following diagram commutes:
/// ```mermaid
/// graph LR;
/// 	`Di`-->|`Di_to_S`|`S`;
/// 	`S`-->|`S_to_Dj`|`Dj`;
/// 	`Di`-->|`Di_to_Dj`|`Dj`;
/// ```
///
/// ## Example
/// Let a source type `S` and two destination type `D1` and `D2`.
/// Let two source functions: `fS: S -> S` and `gS: S -> S`.
/// Let two destination functions:
///  - `fD: D1 -> D2`
///  - `gD: D1 -> D1`
/// Let `D2_to_D1` a direct transformation from `D2` to `D1`.
///
/// Let's assume all the requirement from above are met.
/// Given `x:S`, the tactic will rewrite the goal `gS (gS (fS x))` into:
/// ```
/// D1_to_S (gD (S_to_D1 (
///     D1_to_S (gD (S_to_D1 (
///          D2_to_S (fD (S_to_D1 x))
///        )))
/// )))
/// ```
/// And then into:
/// ```
/// D1_to_S (gD (gD (D2_to_D1 (fD (S_to_D1 x)))))
/// ```
let rewrite_with_lifts (lift_lemmas: list term) (simpl_lemmas: list term) (d: dbg): Tac unit =
    d.sub "rewrite_with_lifts" (fun d -> 
        l_to_r lift_lemmas;
        d.dump "lift lemmas applied";
        
        l_to_r simpl_lemmas;
        d.dump "simpl_lemmas lemmas applied"
    )

/// Test if the term `t` is of the shape `f arg1 ... arg<arity>`. 
/// If `arity` is not given, it is computed automatically.
let is_application_of (f: string) (#[(
        let f = pack_fv (explode_qn f) in
        let f_term = pack_ln (FStar.Stubs.Reflection.V1.Data.Tv_FVar f) in
        let list, _ = collect_arr (tc (top_env ()) f_term) in
        let arity = List.Tot.length list in
        exact (`(`@arity))
    )]arity: int) (t: term): Tac bool =
    let f = pack_fv (explode_qn f) in
    let hd, args = collect_app t in
    if List.Tot.length args <> arity 
    then false
    else match inspect hd with
    | Tv_UInst fv _ | Tv_FVar fv -> inspect_fv fv = inspect_fv f
    | _ -> false


/// `mk_app` variant with `binder`s instead of `argv`s.
let mk_app_bs (t: term) (bs: list binder): Tac term
  = let args = map (fun b -> (binder_to_term b, (inspect_binder b).binder_qual)) bs in
    mk_app t args

/// Given a lemma `i1 -> ... -> iN -> Lemma (lhs == rhs)`, this tactic
/// produces a lemma `i1 -> ... -> iN -> Lemma (lhs == rhs')` where
/// `rhs'` is given by the tactic call `f <rhs>`.
let map_lemma_rhs (f: term -> Tac term) (lemma: term) (d: dbg): Tac term
  = let typ = tc (top_env ()) lemma in
    let inputs, comp = collect_arr_bs typ in
    let post =
      match inspect_comp comp with
      | C_Lemma pre post _ ->
        if not (term_eq pre (`True)) then d.fail "Expected a lemma without precondition";
        post
      | _ -> d.fail "Expected a lemma"
    in
    let post_bd, post_body = match inspect post with
        | Tv_Abs bd body -> (bd, body)
        | _ -> d.fail "Expected `fun _ -> _`"
    in
    let (lhs, rhs) = match collect_app post_body with
      | _, [_; (lhs, _); (rhs, _)] -> (lhs, rhs)
      | _ -> d.fail "expected lhs == rhs"
    in
    let lemma_body = mk_abs inputs (mk_app_bs lemma inputs) in
    let post = mk_abs [post_bd] (mk_e_app (`eq2) [lhs; f rhs]) in
    let lemma_typ = mk_arr inputs (pack_comp (C_Lemma (`True) post (`[]))) in
    let lemma = pack (Tv_AscribedT lemma_body lemma_typ None false) in
    lemma

/// Helper to mark terms. This is an identity function.
/// It is used to normalize terms selectively in two passes:
///  1. browse the term, mark the subterms you want to target
///  2. use `ctrl_rewrite`, doing something only for `mark_to_normalize_here #_ _` terms.
private let mark_to_normalize_here #t (x: t): t = x

let flatten_circuit_aux
  (namespace_always_norm: list string)
  (lift_lemmas: list term) (simpl_lemmas: list term)
  (eta_match_lemmas: list term)
  d
  =
    d.sub "postprocess_tactic" (fun d ->
        norm [primops; iota; delta_namespace ["Libcrux_intrinsics"]; zeta_full];
        d.dump "definitions unfolded";

        rewrite_with_lifts lift_lemmas simpl_lemmas d;

        let eta_match_lemmas =
            map
                (fun t ->
                    map_lemma_rhs (fun rhs -> mk_e_app (`mark_to_normalize_here) [rhs]) t d
                )
                eta_match_lemmas
        in
        l_to_r eta_match_lemmas;
        d.dump "eta-match expansion done";

        let control t = (is_application_of (`%mark_to_normalize_here) t, Continue) in
        let rewritter d =
          let normalize_routine () =
            let open FStar.List.Tot in
            norm [primops; iota; zeta_full; delta_namespace (
                 namespace_always_norm
            @ ["FStar.FunctionalExtensionality"; `%mark_to_normalize_here]
              )]
          in
          normalize_routine ();
          d.dump "normalize the scrutinees in the following expression";
          full_norm_scrutinees d;
          normalize_routine ();
          d.dump "after normalization of scrutinees";
          trefl ()
        in
        ctrl_rewrite BottomUp control (fun _ -> d.sub "bottom-up-rewritter" rewritter);

        let sgs = smt_goals () in
        set_smt_goals [];
        d.dump "after full normalization";
        set_smt_goals sgs;

        ()
    )


/// `flatten_circuit` works on a goal `squash (c == ?u)` such that `c`
/// is a circuit.
///
/// # What is a circuit?
///
/// We consider that `c` is a circuit when `c` involves transforming
/// one or multiple statically-finite collection(s) into one or
/// multiple other statically-finite collections.
///
/// A statically-finite collection is a data structure that contains a
/// collection of items indexable on a domain `D` which is statically
/// known.
///
/// For example, a Rust array `[u8; 12]` is a finitely-indexable data
/// structure, whereas `[u8; N]` where `N` is a const generic is
/// *not*.
///
/// # Arguments
///
/// We assume the reader is familiar with the terms introduced in the
/// documentation of the tactic `rewrite_with_lifts`.
///
/// - `namespace_always_norm`: a list of top-level identifiers to
/// *always* normalize fully. This should include (1) direct
/// transformers (2) any function involved in indexing of the
/// data-strucure (e.g. `(.[])`).
/// - `lift_lemmas`, `simpl_lemmas`: see `rewrite_with_lifts`
/// - `eta_match_lemmas`: lemmas to eta-match expand collections.
///
/// ## "eta match expand"
/// Given `x` and `index` our indexing operation, assuming `x`
/// can be indexed from `0` to `N`, we say the following expression
/// is the "eta match"-expansion of `x`:
/// ```
/// fun i -> match i with
///        | 0 -> index x 0
///        | 1 -> index x 1
///        | ...
///        | N -> index x N
/// ```
let flatten_circuit
  (namespace_always_norm: list string)
  (lift_lemmas: list term) (simpl_lemmas: list term)
  (eta_match_lemmas: list term) =
  let run d =
    flatten_circuit_aux
        namespace_always_norm
        lift_lemmas simpl_lemmas
        eta_match_lemmas d;
    trefl ()
  in
  let disable_ext_flag =
    // Disabling the flatten circuit tactic in lax/admit mode is usually a bad idea:
    //  - if there are no checked file, dependencies will be checked in lax mode
    //  - then, if we want to apply the circuit flattening tactic on a function `A.f`
    //    that happens to use a function `B.g` and expect it to be flattened,
    //    then `B.g` actually not be flattened since it was lax checked
    FStar.Stubs.Tactics.V2.Builtins.ext_enabled "disable_circuit_norm"
  in
  let is_lax_on = lax_on () in
  if is_lax_on && disable_ext_flag
  then trefl ()
  else run (mk_dbg "")
