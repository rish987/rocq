(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Parsing of vernacular. *)

open Pp
open CErrors
open Util
open Vernacexpr
open Vernacprop

(* The functions in this module may raise (unexplainable!) exceptions.
   Use the module Coqtoplevel, which catches these exceptions
   (the exceptions are explained only at the toplevel). *)

let checknav { CAst.loc; v = { expr } }  =
  if is_navigation_vernac expr && not (is_reset expr) then
    CErrors.user_err ?loc (str "Navigation commands forbidden in files.")

(* Echo from a buffer based on position.
   XXX: Should move to utility file. *)
let vernac_echo ?loc in_chan = let open Loc in
  Option.iter (fun loc ->
      let len = loc.ep - loc.bp in
      seek_in in_chan loc.bp;
      Feedback.msg_notice @@ str @@ really_input_string in_chan len
    ) loc


type time_output =
  | ToFeedback
  | ToChannel of Format.formatter

let make_time_output = function
  | Coqargs.ToFeedback -> ToFeedback
  | ToFile f ->
    let ch = open_out f in
    let fch = Format.formatter_of_out_channel ch in
    let close () =
      Format.pp_print_flush fch ();
      close_out ch
    in
    at_exit close;
    ToChannel fch

module State = struct

  type t = {
    doc : Stm.doc;
    sid : Stateid.t;
    proof : Proof.t option;
    time : time_output option;
  }

end

let emit_time state com tstart tend =
  match state.State.time with
  | None -> ()
  | Some time ->
    let pp = Topfmt.pr_cmd_header com ++ System.fmt_time_difference tstart tend in
    match time with
    | ToFeedback -> Feedback.msg_notice pp
    | ToChannel ch -> Pp.pp_with ch (pp ++ fnl())

(* rocq2lean: per-declaration SOURCE TEXT spans (byte offsets into the .v file
   being compiled), for the `.r2lmeta.json` `declaration_sources` key. The
   downstream consumer (rocq2lean) annotates every emitted Lean declaration with a
   comment quoting its ORIGINAL Rocq source, including the tactic proof -- which
   exists nowhere else: a `Qed`-opaque theorem has no kernel body to print, unlike
   `coinductive_sources`/`cofixpoint_sources` (which print the ENVIRONMENT, not
   the source text, and only for those two decl shapes).

   PURELY SYNTACTIC, no kernel/env access needed: a `Theorem`/`Instance`/… vernac
   and its CLOSING `Qed`/`Defined`/`Admitted` are two SEPARATE vernac_control
   commands (the tactic lines between them are more commands still), so this pairs
   the OPENING command's start position with the CLOSING command's end position
   across this loop. `r2l_open_proof` tracks the one pending pair; every branch
   that could otherwise leave it stale (an `Abort`, or a self-contained
   declaration seen while it is still set -- malformed input, or a `Program`
   obligation this hook does not track) clears it FIRST, so a later `Qed` can
   never attach to the WRONG declaration's start position -- the exact
   "slice-bleed" failure mode the Lean-side discharge recovery hit once
   (`d8cb94f`). Reset once per compilation by `r2l_reset_decl_spans`. *)
let r2l_decl_spans : (string * int * int) list ref = ref []
let r2l_open_proof : (string list * int) option ref = ref None

(* rocq2lean: the COPY twin of `r2l_decl_spans`, for the `declaration_copy_sources`
   key. A declaration that Rocq MATERIALISED — through `Include M.`, `Module M := F(X).`
   or `Declare Module M : S.` — has no vernac of its own, so the syntactic accumulator
   above can never see it: nobody ever typed `succ_wd_obligation_1`. Measured on the
   published corpus, that is 36% of every translated declaration, and 72% of those come
   from four files (BinInt, PeanoNat, BinNat, Integers) whose entire content arrives
   through a handful of `Include`s.

   The vernac that CAUSED them is the honest attribution, and it is recoverable the same
   way `declaration_order` recovers their existence: from the KERNEL, not the syntax.
   `r2l_pending_copy` holds `(bp, ep, structure length)` captured BEFORE such a command
   runs; `r2l_note_vernac_post`, called once the command has been executed, asks
   `Global.r2l_structure_added` what appeared beyond that length and records each name
   against the command's own span. The span is emitted as raw `.v` text exactly like
   `declaration_sources`, so the consumer's existing text-location pass gives it a line
   number for free.

   Deliberately NOT diffed: `End M.` (it pops a whole module into one field, whose
   contents already have their own real rows) and every other command (a `Definition`
   is covered by the syntactic path, which is strictly better — it quotes the
   declaration itself rather than the thing that copied it). *)
let r2l_copy_spans : (string * int * int) list ref = ref []

(* `(bp, ep, structure length, r2l_decl_spans length, is_copy)` for the command
   currently being interpreted, or `None` when it is not one this hook diffs.
   `is_copy` chooses which accumulator the discovered names land in — see
   `r2l_diffed` for why the same diff answers two different questions. *)
let r2l_pending_copy : (int * int * int * int * bool) option ref = ref None

let r2l_reset_decl_spans () =
  r2l_decl_spans := [];
  r2l_open_proof := None;
  r2l_copy_spans := [];
  r2l_pending_copy := None

let r2l_take_decl_spans () =
  let l = List.rev !r2l_decl_spans in
  r2l_decl_spans := [];
  l

let r2l_take_copy_spans () =
  let l = List.rev !r2l_copy_spans in
  r2l_copy_spans := [];
  l

(* Which commands get the structure diff, and which accumulator their findings go to.

   `Some true` — COPIES, whose real source is in ANOTHER file: `Include M.`,
   `Module M := F(X).`, `Declare Module M : S.`. `Module M.` (no body) merely OPENS a
   module — its contents arrive as their own vernacs — so only a BOUND module counts.

   `Some false` — a declaration's OWN source that the syntactic path missed. The
   syntactic path assumes a `Definition`/`Instance`/`Theorem` declares exactly the names
   it writes down, and that a bodyless `Instance`/`Theorem` is closed by a later `Qed`.
   `Program` breaks both: `Program Instance succ_wd : Proper (eq==>eq) S.` under an
   `Obligation Tactic` discharges itself on the spot, so no `Qed` ever arrives (the
   pending marker is dropped by the anti-bleed guard) AND it silently adds a second
   constant, `succ_wd_obligation_1`, that nobody wrote. Both are recovered here, against
   the command's OWN span — which really is their source — so they belong in
   `declaration_sources`, not in the copy key.

   This is SELF-GUARDING for the ordinary case: a `Theorem` that genuinely opens a proof
   adds nothing to the environment until its `Qed`, so the diff is empty and the
   syntactic path (which quotes the whole tactic script, far better) stays in charge.
   Any name this command already recorded syntactically is filtered out in
   `r2l_note_vernac_post`, so no name can ever get two rows.

   NOT diffed, deliberately: `End M.` (pops a whole module into one field, whose
   contents already have their own rows — recursing would re-attribute every one of
   them to the `End`), `Qed` (the syntactic path pairs it with the opening command,
   which is the useful span), and `Inductive` (its `_rect`/`_ind`/`_rec`/`_sind` are
   better served by the consumer's "auto-generated from `<the inductive>`" message than
   by quoting the inductive's text as if it were the eliminator's own source). *)
let r2l_diffed (e : Vernacexpr.vernac_expr) : bool option =
  let open Vernacexpr in
  match e with
  | VernacSynterp (VernacInclude _) -> Some true
  | VernacSynterp (VernacDefineModule (_, _, _, _, body)) ->
    if body <> [] then Some true else None
  | VernacSynterp (VernacDeclareModule _) -> Some true
  | VernacSynPure (VernacStartTheoremProof _)
  | VernacSynPure (VernacInstance _)
  | VernacSynPure (VernacDeclareInstance _)
  | VernacSynPure (VernacDefinition _)
  | VernacSynPure (VernacFixpoint _)
  | VernacSynPure (VernacCoFixpoint _) -> Some false
  | _ -> None

(* The name(s) a vernac_expr declares, and whether it OPENS an interactive proof
   (its constant is added only when a LATER `Qed`/`Defined`/`Admitted` closes it)
   or is SELF-CONTAINED (its own span is the whole answer). `None` for a vernac
   this hook does not track -- every other command passes through untouched.
   EVERY member of a mutual `with`-group/block is kept (`Fixpoint f … with g …`,
   `Theorem f : … with g : …`, a mutual `Inductive`) — all sharing the ONE span
   this whole vernac has, so a later member is not left with no comment at all. *)
let r2l_decl_names_opens_proof (e : Vernacexpr.vernac_expr) : (string list * bool) option =
  let open Vernacexpr in
  let lname_id (l : Names.lname) = match l.CAst.v with
    | Names.Name id -> Some (Names.Id.to_string id)
    | Names.Anonymous -> None in
  let lident_id (l : Names.lident) = Some (Names.Id.to_string l.CAst.v) in
  let some_names ns opens = match List.filter_map (fun x -> x) ns with
    | [] -> None
    | ns -> Some (ns, opens) in
  match e with
  | VernacSynPure (VernacStartTheoremProof (_, ps)) ->
    some_names (List.map (fun ((id, _), _) -> lident_id id) ps) true
  | VernacSynPure (VernacInstance (name_decl, _, _, body, _)) ->
    let (l, _) = name_decl in
    Option.bind (lname_id l) (fun n -> Some ([n], (match body with None -> true | Some _ -> false)))
  | VernacSynPure (VernacDeclareInstance ((id, _), _, _, _)) ->
    Option.bind (lident_id id) (fun n -> Some ([n], true))
  | VernacSynPure (VernacDefinition (_, name_decl, _)) ->
    let (l, _) = name_decl in
    Option.bind (lname_id l) (fun n -> Some ([n], false))
  | VernacSynPure (VernacFixpoint (_, (_, rs))) ->
    some_names (List.map (fun r -> lident_id r.fname) rs) false
  | VernacSynPure (VernacCoFixpoint (_, rs)) ->
    some_names (List.map (fun r -> lident_id r.fname) rs) false
  | VernacSynPure (VernacInductive (_, blocks)) ->
    some_names (List.map (fun ((((_, (l, _)), _, _, _), _)) -> lident_id l) blocks) false
  | VernacSynPure (VernacAssumption (_, _, wc_list)) ->
    (* `Axiom a b : T.` names several constants of ONE type in one vernac. *)
    let names = List.concat (List.map (fun (_, (idl, _)) ->
        List.map (fun (id, _) -> lident_id id) idl) wc_list) in
    some_names names false
  | _ -> None

(* Recorded before `Stm.add`/`Stm.observe` even run: this is a SYNTACTIC
   classification of `com`, independent of whether interpretation goes on to
   succeed. On a `.vo`-building compile a failed interpretation aborts the whole
   process before `ccompile.ml` ever reads `r2l_take_decl_spans`, so an
   optimistically-recorded span from a command that then failed is simply never
   read. LOUD on the rare internal-shape surprise (an unforeseen AST variant),
   never silent: same discipline as every other `_sources` hook -- this key's
   whole purpose is showing the downstream proof-filling AI what a `sorry`
   replaced, and a swallowed exception here would drop that silently, file-wide. *)
let r2l_note_vernac (com : Vernacexpr.vernac_control) =
  let open Vernacexpr in
  (* The BEFORE half of the structure diff (see `r2l_copy_spans`). Cleared for every
     other command so a length can never be carried across to the wrong one. *)
  (try
     r2l_pending_copy :=
       (match com.CAst.loc, r2l_diffed com.CAst.v.expr with
        | Some loc, Some is_copy ->
          Some (loc.Loc.bp, loc.Loc.ep, Global.r2l_structure_len (),
                List.length !r2l_decl_spans, is_copy)
        | _, _ -> None)
   with e ->
     r2l_pending_copy := None;
     Printf.eprintf "rocq2lean: r2l_note_vernac (copy pre-hook) FAILED -- the \
declarations this command materialises will carry no provenance: %s\n%!"
       (Printexc.to_string e));
  match com.CAst.loc with
  | None -> ()
  | Some loc ->
    (try
       match com.CAst.v.expr with
       | VernacSynPure (VernacEndProof _) ->
         (match !r2l_open_proof with
          | Some (names, bp) ->
            List.iter (fun name ->
              r2l_decl_spans := (name, bp, loc.Loc.ep) :: !r2l_decl_spans) names;
            r2l_open_proof := None
          | None -> ())
       | VernacSynPure VernacAbort | VernacSynPure VernacAbortAll ->
         r2l_open_proof := None
       | e ->
         (match r2l_decl_names_opens_proof e with
          | Some (names, true) -> r2l_open_proof := Some (names, loc.Loc.bp)
          | Some (names, false) ->
            (* A self-contained declaration seen while a proof is still marked
               open is malformed input or an untracked `Program` obligation --
               either way the stale start cannot belong to THIS name, so drop
               it rather than let a later `Qed` attach it here. *)
            r2l_open_proof := None;
            List.iter (fun name ->
              r2l_decl_spans := (name, loc.Loc.bp, loc.Loc.ep) :: !r2l_decl_spans) names
          | None -> ())
     with e ->
       Printf.eprintf "rocq2lean: r2l_note_vernac FAILED -- this declaration's \
source-text comment will be missing: %s\n%!" (Printexc.to_string e))

(* The AFTER half of the structure diff (see `r2l_copy_spans`). Runs once the command
   has actually been forced, so the safe environment already holds whatever it added.
   A no-op — and specifically NOT a wrong row — whenever the diff shows no growth,
   which is what happens if the command is ever left unforced. *)
let r2l_note_vernac_post () =
  match !r2l_pending_copy with
  | None -> ()
  | Some (bp, ep, n0, d0, is_copy) ->
    r2l_pending_copy := None;
    (try
       (* Names this same command already recorded syntactically (the rows pushed past
          `d0`). Filtered out so a `Definition f` can never end up with two rows — the
          syntactic one is authoritative, the diff is only ever a backstop for what it
          could not see (a `Program` obligation, an `Include`d member). *)
       let own =
         (* `r2l_decl_spans` is a stack, most recent FIRST, so this vernac's own rows
            are the leading `length - d0`. *)
         let rec firstn n l =
           if n <= 0 then [] else match l with [] -> [] | x :: t -> x :: firstn (n - 1) t in
         let cur = !r2l_decl_spans in
         List.map (fun (n, _, _) -> n) (firstn (List.length cur - d0) cur) in
       List.iter (fun (_kind, name) ->
         if not (List.mem name own) then begin
           if is_copy then r2l_copy_spans := (name, bp, ep) :: !r2l_copy_spans
           else r2l_decl_spans := (name, bp, ep) :: !r2l_decl_spans
         end)
         (Global.r2l_structure_added n0)
     with e ->
       Printf.eprintf "rocq2lean: r2l_note_vernac_post FAILED -- the declarations this \
command materialises will carry no provenance: %s\n%!" (Printexc.to_string e))

let interp_vernac ~check ~state ({CAst.loc;_} as com) =
  r2l_note_vernac com;
  let open State in
    try
      let doc, nsid, ntip = Stm.add ~doc:state.doc ~ontop:state.sid (not !Flags.quiet) com in

      (* Main STM interaction *)
      if ntip <> Stm.NewAddTip then
        anomaly (str "vernac.ml: We got an unfocus operation on the toplevel!");

      (* Force the command  *)
      let () = if check then Stm.observe ~doc nsid in
      r2l_note_vernac_post ();
      let new_proof = Vernacstate.Declare.give_me_the_proof_opt () [@ocaml.warning "-3"] in
      { state with doc; sid = nsid; proof = new_proof; }
    with reraise ->
      let (reraise, info) = Exninfo.capture reraise in
      let info =
        (* Set the loc to the whole command if no loc *)
        match Loc.get_loc info, loc with
        | None, Some loc -> Loc.add_loc info loc
        | Some _, _ | _, None  -> info
      in
      Exninfo.iraise (reraise, info)

(* Load a vernac file. CErrors are annotated with file and location *)
let load_vernac_core ~echo ~check ~state ?source file =
  (* Keep in sync *)
  let in_chan = open_utf8_file_in file in
  let in_echo = if echo then Some (open_utf8_file_in file) else None in
  let input_cleanup () = close_in in_chan; Option.iter close_in in_echo in

  let source = Option.default (Loc.InFile {dirpath=None; file}) source in
  let in_pa = Procq.Parsable.make ~loc:Loc.(initial source)
      (Gramlib.Stream.of_channel in_chan) in
  let open State in

  (* ids = For beautify, list of parsed sids *)
  let rec loop state ids =
    let tstart = System.get_time () in
    match
      NewProfile.profile "parse_command" (fun () ->
          Stm.parse_sentence
            ~doc:state.doc ~entry:Pvernac.main_entry state.sid in_pa)
        ()
    with
    | None ->
      input_cleanup ();
      state, ids, Procq.Parsable.comments in_pa
    | Some ast ->
      (* Printing of AST for -compile-verbose *)
      Option.iter (vernac_echo ?loc:ast.CAst.loc) in_echo;

      checknav ast;

      let state =
        try_finally
          (fun () ->
             NewProfile.profile "command"
               ~args:(fun () ->
                   let lnum = match ast.loc with
                     | None -> "unknown"
                     | Some loc -> string_of_int loc.line_nb
                   in
                   [("cmd", `String (Pp.string_of_ppcmds (Topfmt.pr_cmd_header ast)));
                    ("line", `String lnum)])
               (fun () ->
             Flags.silently (interp_vernac ~check ~state) ast) ())
          ()
          (fun () ->
             let tend = System.get_time () in
             (* The -time option is only supported from console-based clients
                due to the way it prints. *)
             emit_time state ast tstart tend)
          ()
      in

      (loop [@ocaml.tailcall]) state (state.sid :: ids)
  in
  try loop state []
  with any ->   (* whatever the exception *)
    let (e, info) = Exninfo.capture any in
    input_cleanup ();
    Exninfo.iraise (e, info)

let process_expr ~state loc_ast =
  try interp_vernac ~check:true ~state loc_ast
  with reraise ->
    let reraise, info = Exninfo.capture reraise in

    (* Exceptions don't carry enough state to print themselves (typically missing the nametab)
       so we need to print before resetting to an older state. See eg #16745 *)
    let reraise = UserError (CErrors.iprint (reraise, info)) in
    (* Keep just the loc in the info as it's printed separately *)
    let info = Option.cata (Loc.add_loc Exninfo.null) Exninfo.null (Loc.get_loc info) in

    ignore(Stm.edit_at ~doc:state.doc state.sid);
    Exninfo.iraise (reraise, info)

let process_expr ~state loc_ast =
  let tstart = System.get_time () in
  try_finally (fun () -> process_expr ~state loc_ast)
    ()
    (fun () ->
       let tend = System.get_time () in
       emit_time state loc_ast tstart tend)
    ()

(******************************************************************************)
(* Beautify-specific code                                                     *)
(******************************************************************************)

(* vernac parses the given stream, executes interpfun on the syntax tree it
 * parses, and is verbose on "primitives" commands if verbosely is true *)
let beautify_suffix = ".beautified"

let set_formatter_translator ch =
  let out s b e = output_substring ch s b e in
  let ft = Format.make_formatter out (fun () -> flush ch) in
  Format.pp_set_max_boxes ft max_int;
  ft

let pr_new_syntax ?loc ft_beautify ocom =
  let loc = Option.append loc (Option.bind ocom (fun x -> x.CAst.loc)) in
  let loc = Option.cata Loc.unloc (0,0) loc in
  let before = comment (Pputils.extract_comments (fst loc)) in
  let com = Option.cata (fun com -> Ppvernac.pr_vernac com ++ fnl()) (mt ()) ocom in
  let after = comment (Pputils.extract_comments (snd loc)) in
  if !Flags.beautify_file then
    (Pp.pp_with ft_beautify (hov 0 (before ++ com ++ after));
     Format.pp_print_flush ft_beautify ())
  else
    Feedback.msg_info (hov 4 (str"New Syntax:" ++ fnl() ++ (hov 0 com)))

(* load_vernac with beautify *)
let beautify_pass ~doc ~comments ~ids ~filename =
  let ft_beautify, close_beautify =
    if !Flags.beautify_file then
      let chan_beautify = open_out (filename^beautify_suffix) in
      set_formatter_translator chan_beautify, fun () -> close_out chan_beautify;
    else
      !Topfmt.std_ft, fun () -> ()
  in
  (* The interface to the comment printer is imperative, so we first
     set the comments, then we call print. This has to be done for
     each file. *)
  Pputils.beautify_comments := comments;
  List.iter (fun id -> pr_new_syntax ft_beautify (Stm.get_ast ~doc id)) ids;

  (* Is this called so comments at EOF are printed? *)
  pr_new_syntax ~loc:(Loc.make_loc (max_int,max_int)) ft_beautify None;
  close_beautify ()

(* Main driver for file loading. For now, we only do one beautify
   pass. *)
let load_vernac ~echo ~check ~state ?source filename =
  let ostate, ids, comments = load_vernac_core ~echo ~check ~state ?source filename in
  (* Pass for beautify *)
  if !Flags.beautify then beautify_pass ~doc:ostate.State.doc ~comments ~ids:(List.rev ids) ~filename;
  (* End pass *)
  ostate
