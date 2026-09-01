(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Coqargs
open Coqcargs
open Common_compile

(******************************************************************************)
(* File Compilation                                                           *)
(******************************************************************************)

let create_empty_file filename =
  let f = open_out filename in
  close_out f

let source ldir file = Loc.InFile {
    dirpath=Some (Names.DirPath.to_string ldir);
    file = file;
  }

(* Compile a vernac file *)
let compile opts stm_options injections copts ~echo ~f_in ~f_out =
  let open Vernac.State in
  let output_native_objects = match opts.config.native_compiler with
    | NativeOff -> false | NativeOn {ondemand} -> not ondemand
  in
  let mode = copts.compilation_mode in
  let ext_in, ext_out =
     match mode with
     | BuildVo -> ".v", ".vo"
     | BuildVos -> ".v", ".vos"
     | BuildVok -> ".v", ".vok"
  in
  let long_f_dot_in, long_f_dot_out =
    ensure_exists_with_prefix ~src:f_in ~tgt:f_out ~src_ext:ext_in ~tgt_ext:ext_out in
  let dump_empty_vos () =
    let long_f_dot_vos = (safe_chop_extension long_f_dot_out) ^ ".vos" in
    create_empty_file long_f_dot_vos in
  let dump_empty_vok () =
    let long_f_dot_vok = (safe_chop_extension long_f_dot_out) ^ ".vok" in
    create_empty_file long_f_dot_vok in
  match mode with
  | BuildVo | BuildVok ->
      let doc, sid = Topfmt.(in_phase ~phase:LoadingPrelude)
          Stm.new_doc
          Stm.{ doc_type = VoDoc long_f_dot_out; injections; } in
      let state = { doc; sid; proof = None; time = Option.map Vernac.make_time_output opts.config.time } in
      let state = Load.load_init_vernaculars opts ~state in
      let ldir = Stm.get_ldir ~doc:state.doc in
      Aux_file.(start_aux_file
        ~aux_file:(aux_file_name_for long_f_dot_out)
        ~v_file:long_f_dot_in);

      Dumpglob.push_output copts.glob_out;
      Dumpglob.start_dump_glob ~vfile:long_f_dot_in ~vofile:long_f_dot_out;
      Dumpglob.dump_string ("F" ^ Names.DirPath.to_string ldir ^ "\n");

      let wall_clock1 = Unix.gettimeofday () in
      let check = Stm.AsyncOpts.(stm_options.async_proofs_mode = APoff) in
      let source = source ldir long_f_dot_in in
      (* rocq2lean: clear any leftover per-declaration source-span state before
         this compilation's own vernac loop runs (see `declaration_sources` below;
         a leftover open-proof marker from an earlier compilation in the SAME
         process would otherwise bleed its stale start position into this file's
         first `Qed`). *)
      Vernac.r2l_reset_decl_spans ();
      let state = Vernac.load_vernac ~echo ~check ~state ~source long_f_dot_in in
      let fullstate = Stm.finish ~doc:state.doc in
      ensure_no_pending_proofs ~filename:long_f_dot_in fullstate;
      let () = Stm.join ~doc:state.doc in
      let wall_clock2 = Unix.gettimeofday () in
      (* In .vo production, dump a complete .vo file. *)
      if mode = BuildVo
        then Library.save_library_to ~output_native_objects Library.ProofsTodoNone ldir long_f_dot_out;
      (* rocq2lean: alongside the .vo, dump translation-relevant metadata (when
         ROCQ2LEAN_META is set). Currently the coercion-insertion sites recorded
         by the (patched) pretyper during this whole file's real compilation, so
         the translator can splice the coercions Rocq inserts — full context
         (section variables, every definition) is naturally in scope here, unlike
         a per-statement re-intern. Extensible: add more keys to this JSON. *)
      (if mode = BuildVo && Sys.getenv_opt "ROCQ2LEAN_META" <> None then
         try
           let sites = Coercion.take_coercion_sites () in
           let meta_file = safe_chop_extension long_f_dot_out ^ ".r2lmeta.json" in
           (* JSON string escaper. MUST cover every character JSON forbids raw
              inside a string, not just the quote and backslash: a stray control
              char (a newline from the pretty-printer wrapping a long type, a tab
              in a comment) makes the WHOLE document unparseable, and the consumer
              swallows that failure and proceeds with NO metadata for the file.
              Applies to every string emitted here, including the identifiers
              inside the structured globs (jstr routes through this). *)
           let esc s =
             let b = Buffer.create (String.length s + 2) in
             String.iter (fun c -> match c with
               | '"'  -> Buffer.add_string b "\\\""
               | '\\' -> Buffer.add_string b "\\\\"
               | '\n' -> Buffer.add_string b "\\n"
               | '\r' -> Buffer.add_string b "\\r"
               | '\t' -> Buffer.add_string b "\\t"
               | '\b' -> Buffer.add_string b "\\b"
               | '\012' -> Buffer.add_string b "\\f"
               | c when Char.code c < 0x20 || Char.code c = 0x7f ->
                 Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
               | c    -> Buffer.add_char b c) s;
             Buffer.contents b in
           let buf = Buffer.create 256 in
           (* rocq2lean: every MutInd this file's emitted metadata REFERENCES, keyed
              by the string the consumer reconstructs from the serialized kername
              (`".".intercalate (globIds <MutInd>)`, i.e. [file dirpath INNERMOST-
              first…, submodules…, label] — `LF.Imp.com` ↦ `Imp.LF.com`). Populated
              as a side effect of serializing/naming refs (see `r2l_note_mind` in
              `jmutind` and `r2l_note_gref` at the gref-name sites), so its scope is
              exactly "inductives REFERENCED by this file" — NOT the whole loaded
              environment (the corelib closure would be thousands of entries per
              file). Drained at the end into the `inductive_ctor_names` key. *)
           let r2l_minds : (string, Names.MutInd.t) Hashtbl.t = Hashtbl.create 97 in
           (* The consumer's key: flatten the USER kername's `Id`/`Label` leaves in
              serialization order, exactly as `Rocq2Lean.Translate.globIds` does
              (`MPfile` contributes `DirPath.repr`, innermost-first; `MPdot` appends
              its label; `MPbound` is serialized as a plain string and so contributes
              NO id leaf). Canonical half is deliberately ignored — `globIds` keeps
              only the user name for a `MutInd` KerPair. *)
           let r2l_mind_key mi =
             let kn = Names.MutInd.user mi in
             let mp, lbl = Names.KerName.repr kn in
             let rec ids = function
               | Names.ModPath.MPfile dp ->
                   List.map Names.Id.to_string (Names.DirPath.repr dp)
               | Names.ModPath.MPbound _ -> []
               | Names.ModPath.MPdot (mp, l) -> ids mp @ [Names.Label.to_string l] in
             String.concat "." (ids mp @ [Names.Label.to_string lbl]) in
           let r2l_note_mind mi =
             let k = r2l_mind_key mi in
             if not (Hashtbl.mem r2l_minds k) then Hashtbl.add r2l_minds k mi in
           (* rocq2lean: the CONSTANT twin of `r2l_minds`, keyed the same way
              (`".".intercalate (globIds <Constant>)`, no `#idx` suffix — a constant is
              not a block). Drained into `referenced_sorts`, which needs the codomain
              sort of every referenced gref, not just of the inductives: deciding
              whether `prod (is_true (R z z)) (…)` is a Prop instance turns on
              `is_true : bool -> Prop`, a CROSS-FILE constant that no file-local key
              (`constant_sorts`, `detyped_type_globs`) can supply. *)
           let r2l_consts : (string, Names.Constant.t) Hashtbl.t = Hashtbl.create 97 in
           let r2l_kername_key kn =
             let mp, lbl = Names.KerName.repr kn in
             let rec ids = function
               | Names.ModPath.MPfile dp ->
                   List.map Names.Id.to_string (Names.DirPath.repr dp)
               | Names.ModPath.MPbound _ -> []
               | Names.ModPath.MPdot (mp, l) -> ids mp @ [Names.Label.to_string l] in
             String.concat "." (ids mp @ [Names.Label.to_string lbl]) in
           let r2l_note_const c =
             let k = r2l_kername_key (Names.Constant.user c) in
             if not (Hashtbl.mem r2l_consts k) then Hashtbl.add r2l_consts k c in
           let r2l_note_gref = function
             | Names.GlobRef.IndRef (mi, _)
             | Names.GlobRef.ConstructRef ((mi, _), _) -> (try r2l_note_mind mi with _ -> ())
             | Names.GlobRef.ConstRef c -> (try r2l_note_const c with _ -> ())
             | _ -> () in
           (* rocq2lean: a GlobRef's FULLY QUALIFIED name. `Printer.pr_global` gives
              the nametab's SHORTEST name (`ANum`), which the consumer can neither
              match against a fully-qualified alignment key nor tell apart from a
              same-short-named declaration elsewhere — the same bareness defect
              already fixed for `binder_types`/`resolved_types`. Constructors are
              named Lean-style (UNDER the inductive: `…BinNums.Z.Z0`), matching
              `ref_resolutions`, because that is the form the translator resolves. *)
           let r2l_gref_name env = function
             | Names.GlobRef.VarRef id -> Names.Id.to_string id
             | Names.GlobRef.ConstRef c -> Names.Constant.to_string c
             | Names.GlobRef.IndRef (mind, i) ->
                 let mib = Environ.lookup_mind mind env in
                 Names.ModPath.to_string (Names.MutInd.modpath mind) ^ "." ^
                 Names.Id.to_string mib.Declarations.mind_packets.(i).Declarations.mind_typename
             | Names.GlobRef.ConstructRef ((mind, i), j) ->
                 let mib = Environ.lookup_mind mind env in
                 Names.ModPath.to_string (Names.MutInd.modpath mind) ^ "." ^
                 Names.Id.to_string mib.Declarations.mind_packets.(i).Declarations.mind_typename ^ "." ^
                 Names.Id.to_string mib.Declarations.mind_packets.(i).Declarations.mind_consnames.(j-1) in
           Buffer.add_string buf "{\"coercions\":[";
           let first = ref true in
           let coe_env = Global.env () in
           List.iter (fun (loc, gref) ->
             match loc with
             | Some l ->
               let (bp, ep) = Loc.unloc l in
               r2l_note_gref gref;
               let nm = (try r2l_gref_name coe_env gref
                         with _ -> Pp.string_of_ppcmds (Printer.pr_global gref)) in
               if not !first then Buffer.add_char buf ',';
               first := false;
               Buffer.add_string buf
                 (Printf.sprintf "[%d,%d,\"%s\"]" bp ep (esc nm))
             | None -> ()) sites;
           (* rocq2lean: generalizing-binder generated vars per span —
              [bp, ep, is_impl(0/1), ["A","R",...]]. *)
           Buffer.add_string buf "],\"generalizing_binders\":[";
           let gbs = Constrintern.take_generalizing_binders () in
           let first = ref true in
           List.iter (fun (loc, is_impl, ids) ->
             match loc with
             | Some l when ids <> [] ->
               let (bp, ep) = Loc.unloc l in
               if not !first then Buffer.add_char buf ',';
               first := false;
               let idstr = String.concat ","
                 (List.map (fun id -> Printf.sprintf "\"%s\"" (esc (Names.Id.to_string id))) ids) in
               Buffer.add_string buf
                 (Printf.sprintf "[%d,%d,%d,[%s]]" bp ep (if is_impl then 1 else 0) idstr)
             | _ -> ()) gbs;
           (* rocq2lean: per-occurrence RESOLVED reference names — [bp, ep,
              "<full kernel name>"] for every reference in this file's interned
              terms, INCLUDING notation-expanded heads (`x + y` → `Z.add`). The
              authoritative resolution Coq computed (module/scope machinery Lean
              lacks), so the translator qualifies a ref by Coq's own verdict
              rather than guessing (the `Z`-module-vs-inductive collision). Deduped
              by span. Source: `Constrintern.take_ref_resolutions`. *)
           Buffer.add_string buf "],\"ref_resolutions\":[";
           (* rocq2lean: how many occurrences could NOT be named (see below). Emitted
              into the sidecar as `ref_resolutions_skipped` so a consumer can tell
              "this file has no unresolvable refs" from "the emitter gave up". *)
           let ref_res_skipped = ref 0 in
           (try
              let env = Global.env () in
              let gref_name = function
                | Names.GlobRef.VarRef id -> Names.Id.to_string id
                | Names.GlobRef.ConstRef c -> Names.Constant.to_string c
                | Names.GlobRef.IndRef (mind, i) ->
                    let mib = Environ.lookup_mind mind env in
                    Names.ModPath.to_string (Names.MutInd.modpath mind) ^ "." ^
                    Names.Id.to_string mib.Declarations.mind_packets.(i).Declarations.mind_typename
                | Names.GlobRef.ConstructRef ((mind, i), j) ->
                    (* Coq names ctors at MODULE level (`…BinNums.Z0`), but Lean
                       (and this translator) puts them UNDER the inductive type
                       (`…BinNums.Z.Z0`). Emit the Lean-style name so the
                       consumer resolves it. *)
                    let mib = Environ.lookup_mind mind env in
                    Names.ModPath.to_string (Names.MutInd.modpath mind) ^ "." ^
                    Names.Id.to_string mib.Declarations.mind_packets.(i).Declarations.mind_typename ^ "." ^
                    Names.Id.to_string mib.Declarations.mind_packets.(i).Declarations.mind_consnames.(j-1) in
              let seen = Hashtbl.create 997 in
              let firstr = ref true in
              List.iter (fun (loc, gref) ->
                match loc with
                | Some l ->
                  let (bp, ep) = Loc.unloc l in
                  r2l_note_gref gref;
                  if not (Hashtbl.mem seen (bp, ep)) then begin
                    (* rocq2lean: NAME THE REF FIRST, and catch PER ENTRY.
                       `gref_name` calls `Environ.lookup_mind`, which RAISES for an
                       inductive declared inside a FUNCTOR BODY (`Module M (X : S).
                       Inductive box … End M.`): the block's kername lives under an
                       MPbound modpath and is absent from the final global env.
                       Two rules this code got wrong before, and must keep:
                         (a) the separator comma is written only when an entry is
                             actually appended, so a failure can never strand a
                             comma — the old code wrote `,` BEFORE evaluating
                             `gref_name`, and the raise then truncated the array
                             mid-write, leaving `…],]` → the WHOLE sidecar was
                             unparseable JSON → the file translated to NOTHING
                             (7 of 254 VST-closure files; `compcert/lib/Integers`
                             alone = 1,679 declarations);
                         (b) a failure skips exactly ONE occurrence instead of
                             abandoning the array, and is LOUD (stderr + a count in
                             the sidecar) — a silent skip is how this class of bug
                             hides. *)
                    match (try Some (gref_name gref) with e ->
                             incr ref_res_skipped;
                             Printf.eprintf
                               "rocq2lean: ref_resolutions: cannot name the ref at \
                                %d-%d (skipped): %s\n"
                               bp ep (Printexc.to_string e);
                             None) with
                    | None -> ()
                    | Some nm ->
                      Hashtbl.add seen (bp, ep) ();
                      if not !firstr then Buffer.add_char buf ',';
                      firstr := false;
                      Buffer.add_string buf
                        (Printf.sprintf "[%d,%d,\"%s\"]" bp ep (esc nm))
                  end
                | None -> ()) (Constrintern.take_ref_resolutions ())
            with e ->
              Printf.eprintf "rocq2lean: ref_resolutions key FAILED: %s\n"
                (Printexc.to_string e));
           (* rocq2lean: RESOLVED types of SOURCE binders, keyed by source span.
              For an UNTYPED binder (`Definition valid_binary x := …`), Coq infers
              `x : spec_float` during pretyping; recorded by span so the translator
              fills the binder by its OWN loc — no telescope alignment. Source:
              `Constrintern.take_binder_types` (populated in `comDefinition`). *)
           Buffer.add_string buf
             (Printf.sprintf "],\"ref_resolutions_skipped\":%d,\"binder_types\":["
                !ref_res_skipped);
           (try
              let seenb = Hashtbl.create 997 in
              let firstb = ref true in
              List.iter (fun (loc, str) ->
                match loc with
                | Some l ->
                  let (bp, ep) = Loc.unloc l in
                  if not (Hashtbl.mem seenb (bp, ep)) then begin
                    Hashtbl.add seenb (bp, ep) ();
                    if not !firstb then Buffer.add_char buf ',';
                    firstb := false;
                    Buffer.add_string buf
                      (Printf.sprintf "[%d,%d,\"%s\"]" bp ep (esc str))
                  end
                | None -> ()) (Constrintern.take_binder_types ())
            with _ -> ());
           (* rocq2lean: per-constant implicit-argument mask, the AUTHORITATIVE
              source (Coq's computed implicits from Set Implicit Arguments /
              Arguments / section discharge) — replaces the translator's heuristic
              mask machinery. Only this file's constants (modpath = MPfile ldir),
              and only those with ≥1 implicit (all-explicit = the default). Each
              entry: ["<full name>", [["<binder name>",k], …]] — the FULL leading-
              binder telescope (names + implicit code) so the translator aligns
              BY NAME (handles section-discharged vars, trailing return-pis, and
              reordering; a bare positional mask mis-slots). Anonymous binders
              (unnamed return-pis) get "_". k: 0=Explicit, 1=rigid-implicit,
              2=flex-only (keep explicit — canonical structures), 3=manual. *)
           Buffer.add_string buf "],\"implicit_args\":[";
           (try
              let env = Global.env () in
              let this_mp = Names.ModPath.MPfile ldir in
              let firstc = ref true in
              Environ.fold_constants (fun c cb () ->
                if Names.ModPath.equal (Names.Constant.modpath c) this_mp then
                  match Impargs.implicits_of_global (Names.GlobRef.ConstRef c) with
                  | (_, statuses) :: _ when List.exists Impargs.is_status_implicit statuses ->
                    (* Mirror the pet fork's `implicit_code` EXACTLY: 0=explicit,
                       1=rigid-implicit, 2=flex-only, 3=manual, via `impl_expl`. *)
                    (* rocq2lean: low digit = impl_expl (0=explicit,1=rigid,
                       2=flex,3=manual); +10 when MAXIMAL insertion (Coq `{{x}}`
                       / `Set Maximal Implicit Insertion`). Lets the translator
                       emit Lean `{x}` (maximal) vs strict `⦃x⦄` (non-maximal),
                       the analog of Coq's cumulative insertion rule. *)
                    let code (s : Impargs.implicit_status) = match s with
                      | None -> 0
                      | Some info ->
                        let base = (match info.Impargs.impl_expl with
                         | Impargs.DepRigid _ | Impargs.DepFlexAndRigid _ -> 1
                         | Impargs.DepFlex _ -> 2
                         | Impargs.Manual -> 3) in
                        base + (if Impargs.maximal_insertion_of s then 10 else 0) in
                    (* Binder names from the type's prod telescope, position-aligned
                       with the Impargs statuses. *)
                    (* `decompose_prod` returns binders INNERMOST-first; reverse
                       to outermost-first so they align with the Impargs statuses. *)
                    let (bnds, _) = Term.decompose_prod cb.Declarations.const_type in
                    let names = List.rev_map (fun (annot, _) ->
                      match Context.binder_name annot with
                      | Names.Name id -> Names.Id.to_string id
                      | Names.Anonymous -> "_") bnds in
                    let rec zip ns cs = match ns, cs with
                      | n :: ns', s :: cs' -> (n, code s) :: zip ns' cs'
                      | _, _ -> [] in
                    if not !firstc then Buffer.add_char buf ',';
                    firstc := false;
                    let pairs = String.concat ","
                      (List.map (fun (n, k) -> Printf.sprintf "[\"%s\",%d]" (esc n) k)
                         (zip names statuses)) in
                    Buffer.add_string buf
                      (Printf.sprintf "[\"%s\",[%s]]" (esc (Names.Constant.to_string c)) pairs)
                  | _ -> ()) env ()
            with _ -> ());
           (* rocq2lean: per-CONSTRUCTOR implicit mask. Constructors aren't in
              fold_constants; iterate the inductive block's packets. Codes are
              positional over the ctor's full arg list (params ++ fields), which
              is the order `ctorAlignsWith` lays out — so a ctor's align matches
              Coq's actual (Set-Implicit-Arguments) ctor implicitness, not the
              inductive params. ["<ctor name>", [k0,k1,…]]. *)
           Buffer.add_string buf "],\"constructor_implicit_args\":[";
           (try
              let env = Global.env () in
              let this_mp = Names.ModPath.MPfile ldir in
              let firstk = ref true in
              let code (s : Impargs.implicit_status) = match s with
                | None -> 0
                | Some info -> (match info.Impargs.impl_expl with
                    | Impargs.DepRigid _ | Impargs.DepFlexAndRigid _ -> 1
                    | Impargs.DepFlex _ -> 2
                    | Impargs.Manual -> 3) in
              Environ.fold_inductives (fun mind mib () ->
                if Names.ModPath.equal (Names.MutInd.modpath mind) this_mp then
                  Array.iteri (fun i oib ->
                    Array.iteri (fun j _ ->
                      let cstr = ((mind, i), j + 1) in
                      match Impargs.implicits_of_global (Names.GlobRef.ConstructRef cstr) with
                      | (_, statuses) :: _ when List.exists Impargs.is_status_implicit statuses ->
                        let name = Pp.string_of_ppcmds
                          (Printer.pr_global (Names.GlobRef.ConstructRef cstr)) in
                        if not !firstk then Buffer.add_char buf ',';
                        firstk := false;
                        let codes = String.concat ","
                          (List.map (fun s -> string_of_int (code s)) statuses) in
                        Buffer.add_string buf
                          (Printf.sprintf "[\"%s\",[%s]]" (esc name) codes)
                      | _ -> ()) oib.Declarations.mind_consnames)
                    mib.Declarations.mind_packets) env ()
            with _ -> ());
           (* rocq2lean: per-constant leading-binder telescope from the DISCHARGED
              `const_type` — the authoritative signal for section-var discharge.
              After `End Section`, `const_type` = ∀ (discharged section vars)
              (source binders), …, so its leading binders are [discharged…] ++
              [source…]. The translator prepends the discharged prefix as binders
              (types from its tracked section `variable`s BY NAME), replacing the
              fragile theorem-only `@foo` pp elaboration for defs/theorems/fixpoints
              alike. Emitted for EVERY this-file constant; non-section constants
              have an empty discharged prefix → no-op. Each binder is
              ["<name>", <impl_code>] where impl_code (same encoding as
              implicit_args: 0=explicit, 1=rigid, 2=flex, 3=manual, +10 if maximal)
              is Coq's AUTHORITATIVE implicit status for that binder — so the
              consumer prepends with the RIGHT kind ({} / ⦃⦄ / explicit) with NO
              guessing and NO verify-gate. Names/statuses from the same
              `decompose_prod`+`implicits_of_global` the implicit_args block uses;
              Anonymous → "_". *)
           Buffer.add_string buf "],\"discharged_telescopes\":[";
           (try
              let env = Global.env () in
              let this_mp = Names.ModPath.MPfile ldir in
              let firstd = ref true in
              let code (s : Impargs.implicit_status) = match s with
                | None -> 0
                | Some info ->
                  let base = (match info.Impargs.impl_expl with
                   | Impargs.DepRigid _ | Impargs.DepFlexAndRigid _ -> 1
                   | Impargs.DepFlex _ -> 2
                   | Impargs.Manual -> 3) in
                  base + (if Impargs.maximal_insertion_of s then 10 else 0) in
              Environ.fold_constants (fun c cb () ->
                if Names.ModPath.equal (Names.Constant.modpath c) this_mp then begin
                  let (bnds, _) = Term.decompose_prod cb.Declarations.const_type in
                  (* decompose_prod is innermost-first; reverse to outermost-first *)
                  let names = List.rev_map (fun (annot, _) ->
                    match Context.binder_name annot with
                    | Names.Name id -> Names.Id.to_string id
                    | Names.Anonymous -> "_") bnds in
                  (* Impargs statuses are position-aligned with the leading binders
                     (outermost-first); pad with explicit (0) past the known ones. *)
                  let statuses = match Impargs.implicits_of_global (Names.GlobRef.ConstRef c) with
                    | (_, ss) :: _ -> ss | [] -> [] in
                  let rec zip ns ss = match ns, ss with
                    | n :: ns', s :: ss' -> (n, code s) :: zip ns' ss'
                    | n :: ns', [] -> (n, 0) :: zip ns' []
                    | [], _ -> [] in
                  let pairs = zip names statuses in
                  if pairs <> [] then begin
                    if not !firstd then Buffer.add_char buf ',';
                    firstd := false;
                    let ns = String.concat ","
                      (List.map (fun (n, k) -> Printf.sprintf "[\"%s\",%d]" (esc n) k) pairs) in
                    Buffer.add_string buf
                      (Printf.sprintf "[\"%s\",[%s]]" (esc (Names.Constant.to_string c)) ns)
                  end
                end) env ()
            with _ -> ());
           (* rocq2lean: per-constant FULL resolved type from the DEFINITIVE kernel
              `const_type`, keyed by name. The translator uses this to fill the
              RETURN type of a definition whose source omits one (`Definition le
              x y := (x ?= y) …` — no `: Prop`): without a return type the
              stub+drop pass can't `sorry` it (nothing to infer against) so it
              DROPS, and every reference to it (a Reals-stub axiom's `Z.le n m`)
              then drops too. Consumer strips the def's own leading binders (by
              arity) to get the codomain. Printed Set-Printing-All-ish (implicits
              explicit, notations off) like `binder_types`, so it re-parses
              unambiguously; newlines flattened to keep the JSON string valid. *)
           Buffer.add_string buf "],\"resolved_types\":[";
           (try
              let env = Global.env () in
              let this_mp = Names.ModPath.MPfile ldir in
              (* A constant defined inside `Module Z` (BinIntDef's `Z.le`) has modpath
                 `MPdot(MPfile …, "Z")`, NOT the bare file MPfile — so walk to the FILE
                 root and compare, else every module-nested def is missed. *)
              let rec mp_root = function
                | Names.ModPath.MPdot (mp, _) -> mp_root mp
                | mp -> mp in
              let evd = Evd.from_env env in
              let open Constrextern in
              let sv = (!print_implicits, !print_no_symbol, !print_coercions, !print_parentheses) in
              print_implicits := true; print_no_symbol := true;
              print_coercions := true; print_parentheses := true;
              (* Print every reference FULLY QUALIFIED (`Corelib.Init.Datatypes.bool`,
                 not the nametab's shortest `bool`). A synthesized axiom's type is
                 re-parsed with NO per-occurrence intern resolution, so a bare `bool`/
                 `positive`/`prod` head has nothing to resolve against and drops
                 (Lean has `Bool`/`Prod`, not `bool`/`prod`); the full path resolves
                 to the ground corelib constant (or a fully-qualified config align). *)
              let saved_ref = get_extern_reference () in
              set_extern_reference (fun ?loc vars r ->
                try Libnames.qualid_of_path ?loc (Nametab.path_of_global r)
                with _ -> saved_ref ?loc vars r);
              let firstt = ref true in
              Environ.fold_constants (fun c cb () ->
                if Names.ModPath.equal (mp_root (Names.Constant.modpath c)) this_mp then begin
                  try
                    let ty = EConstr.of_constr cb.Declarations.const_type in
                    let raw = Pp.string_of_ppcmds (Printer.pr_econstr_env env evd ty) in
                    let str = String.map (fun ch -> if ch = '\n' || ch = '\r' then ' ' else ch) raw in
                    if not !firstt then Buffer.add_char buf ',';
                    firstt := false;
                    Buffer.add_string buf
                      (Printf.sprintf "[\"%s\",\"%s\"]" (esc (Names.Constant.to_string c)) (esc str))
                  with _ -> ()
                end) env ();
              set_extern_reference saved_ref;
              let (a,b,cc,d) = sv in
              print_implicits := a; print_no_symbol := b; print_coercions := cc; print_parentheses := d
            with _ -> ());
           (* rocq2lean PROTOTYPE: DETYPED glob_constr of each transparent
              this-file constant's BODY, serialized in EXACTLY the shape
              `petanque/intern` emits (serlib `glob_constr_to_yojson`) so the
              translator's `translateGlob` consumes it verbatim. Context-free
              (from the real compile's kernel term) — immune to the pet-at-scale
              intern drop that loses e.g. `Bool.le`'s `_ = _`. Each entry:
              ["<full const name>", <bodyGlobJSON>]. NOTE: detype materialises
              ALL arguments (an implicit type arg becomes an explicit GRef, not
              the `GHole GImplicitArg` intern emits) and drops source locs
              (loc:null). *)
              (* rocq2lean: EXPLICIT CUMULATIVITY (Assaf, "A Calculus of
                 Constructions with Explicit Subtyping", TYPES 2014).

                 Coq's `Prop ⊆ Type` is SUBTYPING, applied silently by the kernel
                 (`Typeops.type_of_apply` → `conv_leq`, whose sort case is
                 `Conversion`'s `CUMUL -> check_leq`). Lean has no subtyping at all,
                 so once we render universe levels faithfully every such use is a hard
                 error. This pass makes each one EXPLICIT in the term BEFORE detyping,
                 so the glob carries it and the translator needs no new logic.

                 We do NOT hook conversion: it is memoized and short-circuits (an
                 argument that converts syntactically never reaches the sort
                 comparison), it is called speculatively, and it has no positional
                 handle. A type-directed traversal is deterministic and positional.

                 Two markers, fabricated (they need not exist in the environment --
                 nothing typechecks the OUTPUT, we only detype it). Crucially the
                 markers are never fed back into typing: `Retyping`/`whd_all` always
                 see the ORIGINAL subterms, and the rewritten ones only accumulate in
                 the output. R2L.lift is Assaf's ↑ (a Prop used as a Type); R2L.up
                 injects an element into a lifted type. *)
              let r2l_mp =
                Names.ModPath.MPfile (Names.DirPath.make [Names.Id.of_string "R2L"]) in
              let r2l_lift_c =
                Names.Constant.make1 (Names.KerName.make r2l_mp (Names.Label.make "lift")) in
              let r2l_up_c =
                Names.Constant.make1 (Names.KerName.make r2l_mp (Names.Label.make "up")) in
              let r2l_down_c =
                Names.Constant.make1 (Names.KerName.make r2l_mp (Names.Label.make "down")) in
              let r2l_lifts = ref 0 and r2l_ups = ref 0 and r2l_fails = ref 0 in
              let r2l_downs = ref 0 in
              let r2l_scruts = ref 0 in
              let r2l_projs = ref 0 in
              let r2l_apps = ref 0 in
              let r2l_explicitate env evd c0 =
                let open EConstr in
                let _mk_lift a = mkApp (UnsafeMonomorphic.mkConst r2l_lift_c, [| a |]) in
                let _mk_up t a = mkApp (UnsafeMonomorphic.mkConst r2l_up_c, [| t; a |]) in
                let _mk_down t a = mkApp (UnsafeMonomorphic.mkConst r2l_down_c, [| t; a |]) in
                let _is_propish s = Sorts.is_prop s || Sorts.is_sprop s in
                let rec go env c =
                  match kind evd c with
                  (* EXPLICIT CUMULATIVITY: RETIRED (2026-08-12).

                     This branch inserted R2L.lift / R2L.up / R2L.down at every use of
                     Coq's Prop <= Type, per Assaf. It worked -- cumulativity sites went
                     553 -> 0 -- but it was the wrong construction for Lean, and the
                     translator now renders the markers as identities anyway.

                     Assaf's lift acts on universe CODES, in a Tarski presentation whose
                     full-reflection equations give T(lift a) = T(a): decoding a lifted
                     code yields the SAME type, so TERMS are never coerced. Lean has no
                     such definitional equation -- PLift A is an inductive genuinely
                     distinct from A -- so every lift forced up/down on elements, and
                     because types mention earlier arguments those wrappers propagated
                     through the whole telescope. Patching one argument satisfied it and
                     broke the next (measured: cluster 116 -> 66, mismatch total pinned
                     at 215).

                     The replacement adjusts the DECLARATION instead: a Coq `Type` in
                     binder position renders as `Sort _`, which admits exactly what Coq's
                     cumulativity admits there, so Coq's term goes through verbatim.
                     corelib 463 -> 388, cluster 116 -> 4, PLift in output 95 -> 0.

                     Kept below: the Case scrutinee ascription, unrelated, and still the
                     source of index terms. *)
                  | Constr.Proj (pr, rel, arg) when not (Names.Projection.unfolded pr) ->
                    (* PRIMITIVE PROJECTIONS. Rocq's detyper turns a kernel `Proj` into
                       an APPLICATION OF THE PROJECTION CONSTANT (`noparams ()`), so the
                       body Rocq gives the projection constant itself detypes to
                       `fun t => find_duplicate_quotients t` -- a literal SELF-REFERENCE
                       that cannot be translated, and nothing in the glob links the
                       constant to the field it projects except its POSITION.
                       Recovering the field by position is exactly what this codebase
                       has been burned by, so recover it from Rocq instead: with the
                       projection marked UNFOLDED and `Printing Unfolded Projection As
                       Match` set (both done here), the detyper emits the faithful
                       `match c with | Build_t _ x _ => x` and names the bound variable
                       with the projection's REAL label (`Projection.label`). Same term,
                       no self-reference, no positional inference. *)
                    incr r2l_projs;
                    mkProj (Names.Projection.unfold pr, rel,
                            Termops.map_constr_with_full_binders env evd push_rel go env arg)
                  | Constr.App _ ->
                    Termops.map_constr_with_full_binders env evd push_rel go env c
                  | Constr.Case _ ->
                    (* SCRUTINEE TYPE for an INDEXED match. Lean needs the index TERMS
                       as discriminants so each branch can refine them, and the glob
                       does not carry them -- the `in`-clause (`aliastyp`) names the
                       index binders but not their values. The translator used to
                       recover them by elaborating the scrutinee in the live Lean
                       environment, `inferType`ing it and DELABORATING the index args
                       back to syntax; that round trip is what exposed it to Lean's
                       `sorry`s and to unbound universe names.
                       Ascribing the scrutinee with the type it ALREADY has is a
                       semantic no-op that survives detyping as a `GCast`, so the type
                       -- and hence its index arguments -- arrives as an ordinary glob
                       the translator can render through its normal path. Only for
                       inductives that actually have indices; anywhere else it is
                       noise. *)
                    let c' =
                      Termops.map_constr_with_full_binders env evd push_rel go env c in
                    (match kind evd c' with
                     | Constr.Case (ci, u, pms, p, iv, scrut, brs) ->
                       (try
                          let (_, oib) = Inductive.lookup_mind_specif env ci.Constr.ci_ind in
                          if oib.Declarations.mind_nrealargs = 0 then c'
                          else
                            let sty = Retyping.get_type_of env evd scrut in
                            incr r2l_scruts;
                            mkCase (ci, u, pms, p, iv,
                                    mkCast (scrut, Constr.DEFAULTcast, sty), brs)
                        with _ -> c')
                     | _ -> c')
                  | _ ->
                    (* EVERY other node, with the environment maintained correctly
                       through ALL binder forms -- `Case` branches and `Fix` included.
                       Hand-rolling only Lambda/Prod/LetIn left the env wrong under
                       every match and every recursive function, so `Retyping` threw
                       there and the whole application was skipped: 1252 retype
                       failures in `Init/Logic` alone, i.e. exactly the sites that
                       stayed unlifted. *)
                    Termops.map_constr_with_full_binders env evd push_rel go env c
                in
                try go env c0 with _ -> incr r2l_fails; c0 in
           (* rocq2lean: UNIVERSE VALUATION for Coq's MONOMORPHIC levels.

              Coq's default is monomorphic: each `Type` mints a fresh GLOBAL level,
              shared across the library, and the constraints live in one global graph
              that Coq MINIMIZES. Those levels are NOT per-declaration parameters --
              measured over a 12-module corelib closure, 863 level names denote three
              actual levels (`Set < Type.0 < Type.1`, 855 names collapsed onto
              `Type.0`). Rendering them as Lean universe parameters manufactures
              distinctions Coq does not make; rendering them all as a bare sort
              collapses the one edge that IS strict.

              So emit each level's VALUE: the length of the longest chain of `Lt`
              constraints from `Set`, which is exactly how `Print Sorted Universes`
              assigns them (`sort_universes` in vernac/vernacentries.ml, replicated
              here because it is not exported). The consumer maps Coq level n to
              Lean `Type n` -- Coq's `Set` is Lean's `Type 0`. *)
           (* rocq2lean: a POLYMORPHIC declaration's OWN universe constraints.

              A polymorphic declaration quantifies over `Var 0 … Var (n-1)` and carries
              the constraints between them (`AbstractContext`); they are INFERRED by the
              kernel, not written. Unlike the monomorphic levels — which are global,
              minimized, and rendered at a concrete level — these are real binders, and
              Lean has no way to state a constraint on a universe PARAMETER.

              The encoding that needs no such mechanism: for `Var i <= Var j`, render
              `u_j` as `max u_j u_i` everywhere. The constraint then holds
              definitionally, and the declaration stays exactly as general as Coq's,
              since any Coq-admissible instantiation already satisfies it (so the max
              equals `u_j` there).

              Entry: ["<const>", [[i, "<=" | "<", j], …]] over de Bruijn INDICES, which
              is what `Var i` in the serialized sorts already refers to. *)
           Buffer.add_string buf "],\"poly_constraints\":[";
           let firstpc = ref true in
           let jpolycstrs name auctx =
             let cstrs = UVars.AbstractContext.repr auctx |> UVars.UContext.constraints in
             if not (Univ.Constraints.is_empty cstrs) then begin
               let idx_of l =
                 match Univ.Level.var_index l with Some i -> Some i | None -> None in
               let items = Univ.Constraints.fold (fun (l, d, r) acc ->
                   match idx_of l, idx_of r with
                   | Some i, Some j ->
                     let ds = (match d with
                         | Univ.Lt -> "<" | Univ.Le -> "<=" | Univ.Eq -> "=") in
                     (Printf.sprintf "[%d,\"%s\",%d]" i ds j) :: acc
                   | _ -> acc) cstrs [] in
               if items <> [] then begin
                 if not !firstpc then Buffer.add_char buf ',';
                 firstpc := false;
                 Buffer.add_string buf
                   (Printf.sprintf "[\"%s\",[%s]]" (esc name) (String.concat "," items))
               end
             end in
           let rec pc_mp_root = function
             | Names.ModPath.MPdot (mp, _) -> pc_mp_root mp
             | mp -> mp in
           let pc_this_mp = Names.ModPath.MPfile ldir in
           (try
              Environ.fold_constants (fun c cb () ->
                  if Names.ModPath.equal (pc_mp_root (Names.Constant.modpath c)) pc_this_mp then
                    match cb.Declarations.const_universes with
                    | Declarations.Polymorphic auctx ->
                      jpolycstrs (Names.Constant.to_string c) auctx
                    | _ -> ()) (Global.env ()) ()
            with _ -> ());
           Buffer.add_string buf "],\"universe_valuation\":[";
           let firstuv = ref true in
           (try
              let g = UGraph.repr (Global.universes ()) in
              let open Univ in
              let rec normalize u = match Level.Map.find u g with
                | UGraph.Alias u -> normalize u
                | UGraph.Node _ -> u in
              let get_next u = match Level.Map.find u g with
                | UGraph.Alias _ -> Level.Map.empty
                | UGraph.Node ltle -> ltle in
              let rec traverse accu todo = match todo with
                | [] -> accu
                | (u, n) :: todo ->
                  let n = match Level.Map.find u accu with
                    | m -> if m < n then Some n else None
                    | exception Not_found -> Some n in
                  (match n with
                   | None -> traverse accu todo
                   | Some n ->
                     let accu = Level.Map.add u n accu in
                     let fold v lt todo =
                       let v = normalize v in
                       if lt then (v, n + 1) :: todo else (v, n) :: todo in
                     let todo = Level.Map.fold fold (get_next u) todo in
                     traverse accu todo) in
              let levels = traverse Level.Map.empty [normalize Level.set, 0] in
              Level.Map.iter (fun u _ ->
                  let v = try Level.Map.find (normalize u) levels with Not_found -> 0 in
                  if not !firstuv then Buffer.add_char buf ',';
                  firstuv := false;
                  Buffer.add_string buf
                    (Printf.sprintf "[\"%s\",%d]" (esc (Level.to_string u)) v)) g
            with _ -> ());
           (* rocq2lean: MONOMORPHIC universe CONSTRAINT EDGES.

              `universe_valuation` above emits the SOLUTION Coq's minimiser happened
              to pick. From a valuation alone you cannot tell "Coq PROVED these two
              levels related" from "they independently came out at the same number",
              so a consumer that wants to keep a level as general as Coq did has
              nothing to go on. The edges are that missing evidence.

              Read from the SAME global graph as the valuation
              (`UGraph.repr (Global.universes ())`) and filtered to the edges with at
              least ONE endpoint among THIS file's own levels (a `Level.name` whose
              DirPath is `ldir`). Without that filter the key is the entire global
              graph -- thousands of edges, almost all of them about other files. A
              cross-file edge (the other endpoint a `Corelib.…` level, or `Set`) is
              KEPT and named in full, since that is exactly the interesting case.

              `UGraph.node` distinguishes three things and all three are emitted as
              themselves:
                `Node ltle` -- ltle maps v to `true` for `u < v`, `false` for `u <= v`
                `Alias v`   -- u and v are the SAME graph node, i.e. `u = v`
              `<=` is a strictly weaker claim than `=`; collapsing them would
              reintroduce precisely the guess this key exists to remove.

              Entry: ["<level>", "<" | "<=" | "=", "<level>"], read left-to-right --
              the LEFT level is the lower one. *)
           Buffer.add_string buf "],\"mono_constraints\":[";
           let firstmc = ref true in
           (try
              let g = UGraph.repr (Global.universes ()) in
              let open Univ in
              let is_local l = match Level.name l with
                | Some ug ->
                  let dp, _, _ = UGlobal.repr ug in
                  Names.DirPath.equal dp ldir
                | None -> false in
              let emit u d v =
                if is_local u || is_local v then begin
                  if not !firstmc then Buffer.add_char buf ',';
                  firstmc := false;
                  Buffer.add_string buf
                    (Printf.sprintf "[\"%s\",\"%s\",\"%s\"]"
                       (esc (Level.to_string u)) d (esc (Level.to_string v)))
                end in
              Level.Map.iter (fun u node -> match node with
                  | UGraph.Alias v -> emit u "=" v
                  | UGraph.Node ltle ->
                    Level.Map.iter
                      (fun v lt -> emit u (if lt then "<" else "<=") v) ltle) g
            with e ->
              Printf.eprintf "rocq2lean: mono_constraints key FAILED -- the consumer \
sees the universe VALUATION with no evidence of which levels Coq actually related, \
and will pin levels Coq would have widened: %s\n%!" (Printexc.to_string e));
           (* rocq2lean: make the detyper render an UNFOLDED primitive projection as a
              `match` (see the `Proj` branch of `r2l_explicitate`). Off by default,
              which is what left a projection constant's own body as a self-reference. *)
           (try Goptions.set_bool_option_value
                  ["Printing"; "Unfolded"; "Projection"; "As"; "Match"] true
            with e ->
              Printf.eprintf "rocq2lean: could not enable `Printing Unfolded Projection \
As Match` -- primitive projections will detype as self-referential applications: \
%s\n%!" (Printexc.to_string e));
           (* rocq2lean: CUMULATIVITY SITES -- the places where Rocq's kernel
              actually USED subtyping, i.e. accepted `Type@{i} <= Type@{j}` (or
              `Prop`/`Set` <= `Type`) with the two sorts NOT equal, rather than
              requiring equality. Lean has no cumulativity at all, so each of these
              is a position the translation can break; today they are found only
              BACKWARDS, from a Lean elaboration error, and an error says where it
              BROKE, not where the coercion HAPPENED.

              RECORD ONLY. An earlier fork pass (dc25002 -> 000f386, RETIRED at
              cf2930a) INSERTED explicit lifts at exactly these positions and
              cascaded through whole telescopes. Nothing here rewrites a term: the
              traversal below is a pure observer.

              We deliberately do NOT hook `kernel/conversion.ml`. Its CUMUL path is
              memoized, short-circuits when the two sides converge syntactically,
              and is called speculatively with backtracking -- a hook there yields a
              list that is at once INCOMPLETE (a memo hit skips the comparison) and
              FALSE-POSITIVE (a backtracked attempt logged as a real use). Instead a
              type-directed traversal REPLAYS the kernel's own CUMUL sites
              (`Typeops.type_of_apply` at typeops.ml:243, `type_of_parameters` at
              :269, `check_branch_types` at :453, the Fix body check at :583, the
              LetIn body check at :911, and each declaration's body-vs-declared-type
              check) and asks TWO questions per site, in this order:

              NOT covered, so the key UNDER-reports rather than over-reports: the
              `CaseInvert` scrutinee check (:735) and `check_context` on section
              contexts. `not_leq` in the stderr summary is the other coverage
              signal -- it counts sites where our reconstruction of the expected
              type failed to match the kernel's, and is 0 on all 60 VST modules
              measured.

                `Conversion.conv`     (CONV)  -- if the actual and expected types are
                                                already CONVERTIBLE AS EQUALS then
                                                cumulativity was NOT used and nothing
                                                is recorded. This is the test that
                                                keeps the key from crying wolf on an
                                                equality that merely travelled the
                                                same kernel code path.
                `Conversion.conv_leq` (CUMUL) -- if only this one succeeds, the
                                                kernel DID use subtyping here.

              The responsible universes are then located by a parallel walk of the
              two types which yields every pair of sorts that are unequal under
              `UGraph.check_eq_sort` but related by `check_leq_sort`. So every level
              pair emitted is a STRICT use by construction, and the walk's PATH says
              whether the strictness sits in a Pi domain, a Pi codomain, or an
              inductive's universe instance.

              The traversal is `Termops.map_constr_with_full_binders` used as an
              ITERATOR (the mapped term is discarded). Hand-rolling the binder cases
              is precisely what made the retired pass skip 1252 sites in `Init/Logic`
              alone: a wrong env under `Case` branches and `Fix` made `Retyping`
              throw and the enclosing application was abandoned.

              Entry, 8 fields:
                ["<decl>", "<region>", "<shape>", <argpos>, "<head>", "<path>",
                 "<lower sort>", "<upper sort>"]
                decl    full kername of the enclosing declaration (or
                        `<modpath>.<indname>` for an inductive)
                region  which part of it: "body" | "type" | "arity" | "ctor:<name>"
                shape   the kernel site: app_arg | ind_param | ind_index |
                        ctor_param | ctor_field | case_branch | letin | cast |
                        fix_body | cofix_body | decl_body
                argpos  0-based argument index, or -1 where there is none
                head    the applied head (Const:/Ind:/Ctor:/Var:/Rel:/?) -- this is
                        what makes the list RANKABLE by callee
                path    where inside the two types the sorts differ: "" is the types
                        themselves, then ".dom" (Pi domain, CONTRAVARIANT -- the
                        expected type's domain is the lower one), ".cod" (Pi
                        codomain), ".argN", ".univN" (universe instance slot N)
                lower   the sort Rocq had
                upper   the sort Rocq demanded

              A site whose levels could not be located is emitted once with path
              "?" and both sorts "?" rather than dropped, and counted; see the
              stderr summary below. *)
           Buffer.add_string buf "],\"cumulativity_sites\":[";
           let firstcs = ref true in
           let cs_emitted = ref 0 and cs_unlocated = ref 0 in
           let cs_retype_fail = ref 0 and cs_scan_fail = ref 0 in
           let cs_arity_fail = ref 0 and cs_conv_raised = ref 0 in
           let cs_not_leq = ref 0 and cs_checks = ref 0 in
           let cs_template = ref 0 in
           let cs_t0 = Sys.time () in
           (try
              let genv = Global.env () in
              let cs_evd = Evd.from_env genv in
              let evd = cs_evd in
              let this_mp = Names.ModPath.MPfile ldir in
              let rec mp_root = function
                | Names.ModPath.MPdot (mp, _) -> mp_root mp
                | mp -> mp in
              let sort_str s = Pp.string_of_ppcmds (Sorts.raw_pr s) in
              let emit decl region shape argpos head path lo up =
                incr cs_emitted;
                if not !firstcs then Buffer.add_char buf ',';
                firstcs := false;
                Buffer.add_string buf
                  (Printf.sprintf "[\"%s\",\"%s\",\"%s\",%d,\"%s\",\"%s\",\"%s\",\"%s\"]"
                     (esc decl) (esc region) (esc shape) argpos (esc head)
                     (esc path) (esc lo) (esc up)) in
              (* Parallel walk of (actual, expected). Yields (path, lower, upper) for
                 each position whose two sorts are related by <= but NOT by =. Both
                 sides are weak-head normalised, since a cumulative step can hide
                 behind a definition. Only ever reached once the site is already
                 known to be a cumulative use, so its cost is paid on real hits. *)
              let rec cs_diff env path a e acc =
                if List.length acc > 24 then acc else
                let a = Reductionops.whd_all env evd a in
                let e = Reductionops.whd_all env evd e in
                match EConstr.kind evd a, EConstr.kind evd e with
                | Constr.Sort s1, Constr.Sort s2 ->
                  let s1 = EConstr.ESorts.kind evd s1 in
                  let s2 = EConstr.ESorts.kind evd s2 in
                  let g = Environ.universes env in
                  if UGraph.check_eq_sort g s1 s2 then acc
                  else if UGraph.check_leq_sort g s1 s2 then (path, s1, s2) :: acc
                  else acc
                | Constr.Prod (na, a1, b1), Constr.Prod (_, a2, b2) ->
                  (* CONTRAVARIANT in the domain: the EXPECTED type's domain is the
                     lower one, so the pair is emitted in that order and the path is
                     tagged ".dom" so a consumer does not read it backwards. *)
                  let acc = cs_diff env (path ^ ".dom") a2 a1 acc in
                  let env' =
                    EConstr.push_rel
                      (Context.Rel.Declaration.LocalAssum (na, a1)) env in
                  cs_diff env' (path ^ ".cod") b1 b2 acc
                | Constr.App (h1, ar1), Constr.App (h2, ar2)
                  when Array.length ar1 = Array.length ar2 ->
                  let acc = ref (cs_diff env (path ^ ".hd") h1 h2 acc) in
                  Array.iteri (fun i x ->
                      acc := cs_diff env (Printf.sprintf "%s.arg%d" path i)
                               x ar2.(i) !acc) ar1;
                  !acc
                | Constr.Ind (i1, u1), Constr.Ind (i2, u2)
                  when Names.Ind.CanOrd.equal i1 i2 ->
                  cs_diff_instance env path (EConstr.EInstance.kind evd u1)
                    (EConstr.EInstance.kind evd u2) acc
                | Constr.Const (c1, u1), Constr.Const (c2, u2)
                  when Names.Constant.CanOrd.equal c1 c2 ->
                  cs_diff_instance env path (EConstr.EInstance.kind evd u1)
                    (EConstr.EInstance.kind evd u2) acc
                | _ -> acc
              (* An inductive's or constant's UNIVERSE INSTANCE. Rocq's cumulative
                 inductives compare instances with <=, so a strict step can live
                 entirely here with no Sort node anywhere in either type. *)
              and cs_diff_instance env path u1 u2 acc =
                let (_, l1) = UVars.Instance.to_array u1 in
                let (_, l2) = UVars.Instance.to_array u2 in
                if Array.length l1 <> Array.length l2 then acc
                else begin
                  let g = Environ.universes env in
                  let acc = ref acc in
                  Array.iteri (fun i x ->
                      let s1 = Sorts.sort_of_univ (Univ.Universe.make x) in
                      let s2 = Sorts.sort_of_univ (Univ.Universe.make l2.(i)) in
                      if not (UGraph.check_eq_sort g s1 s2)
                      && UGraph.check_leq_sort g s1 s2 then
                        acc := (Printf.sprintf "%s.univ%d" path i, s1, s2) :: !acc)
                    l1;
                  !acc
                end in
              (* ONE kernel CUMUL site. `actual` is what Rocq had, `expected` is what
                 the position demanded. *)
              let cs_check env decl region shape argpos head actual expected =
                incr cs_checks;
                if EConstr.eq_constr evd actual expected then () else
                let a = EConstr.Unsafe.to_constr actual in
                let e = EConstr.Unsafe.to_constr expected in
                let conv_res =
                  try `R (Conversion.conv env a e)
                  with ex -> `Raised ex in
                match conv_res with
                | `R (Result.Ok ()) -> ()                    (* equal: not a use *)
                | `Raised _ -> incr cs_conv_raised
                | `R (Result.Error ()) ->
                  let leq_res =
                    try `R (Conversion.conv_leq env a e)
                    with ex -> `Raised ex in
                  (match leq_res with
                   | `Raised _ -> incr cs_conv_raised
                   | `R (Result.Error ()) ->
                     (* Neither convertible nor a subtype: our reconstruction of the
                        expected type does not match the kernel's (template
                        polymorphism, an unfolded projection, ...). NOT a
                        cumulativity site, and counted so the key's coverage is
                        auditable rather than assumed. *)
                     incr cs_not_leq;
                     if Sys.getenv_opt "R2L_TRACE_CUM_NOTLEQ" <> None
                        && !cs_not_leq <= 8 then
                       Printf.eprintf "rocq2lean: cumulativity_sites NOT_LEQ #%d %s \
%s/%s[%d] head=%s\n  actual   = %s\n  expected = %s\n%!" !cs_not_leq decl region
                         shape argpos head
                         (Pp.string_of_ppcmds (Constr.debug_print a))
                         (Pp.string_of_ppcmds (Constr.debug_print e))
                   | `R (Result.Ok ()) ->
                     let sites =
                       try cs_diff env "" actual expected []
                       with ex ->
                         Printf.eprintf "rocq2lean: cumulativity_sites could not \
locate the levels of a CONFIRMED cumulative use in %s (%s/%s); it is emitted with \
sort \"?\", so the site is counted but not attributable: %s\n%!"
                           decl region shape (Printexc.to_string ex);
                         [] in
                     if sites = [] then begin
                       incr cs_unlocated;
                       emit decl region shape argpos head "?" "?" "?"
                     end else
                       List.iter (fun (p, s1, s2) ->
                           emit decl region shape argpos head p
                             (sort_str s1) (sort_str s2)) sites) in
              (* APPLICATION: replay `Typeops.type_of_apply` -- walk the head's type
                 as a telescope, checking each argument's own type against the
                 domain it lands in, then substituting. Distinguishes an inductive's
                 PARAMETERS from its INDICES and a constructor's parameters from its
                 FIELDS, since those classes are fixable wholesale and an ordinary
                 application argument is not. *)
              let cs_app env decl region c =
                match EConstr.kind evd c with
                | Constr.App (f, args) ->
                  let head, nparams, kind_of_head, is_template =
                    match EConstr.kind evd f with
                    | Constr.Const (kn, _) ->
                      ("Const:" ^ Names.Constant.to_string kn, -1, `Other, false)
                    | Constr.Ind (ind, _) ->
                      let (mib, oib) = Inductive.lookup_mind_specif env ind in
                      ("Ind:" ^ Names.ModPath.to_string (Names.MutInd.modpath (fst ind))
                       ^ "." ^ Names.Id.to_string oib.Declarations.mind_typename,
                       mib.Declarations.mind_nparams, `Ind,
                       mib.Declarations.mind_template <> None)
                    | Constr.Construct (((mind, i), j), _) ->
                      let (mib, oib) = Inductive.lookup_mind_specif env (mind, i) in
                      ("Ctor:" ^ Names.ModPath.to_string (Names.MutInd.modpath mind)
                       ^ "." ^ Names.Id.to_string oib.Declarations.mind_typename
                       ^ "." ^ Names.Id.to_string oib.Declarations.mind_consnames.(j-1),
                       mib.Declarations.mind_nparams, `Ctor,
                       mib.Declarations.mind_template <> None)
                    | Constr.Var id -> ("Var:" ^ Names.Id.to_string id, -1, `Other, false)
                    | Constr.Rel n -> (Printf.sprintf "Rel:%d" n, -1, `Other, false)
                    | _ -> ("?", -1, `Other, false) in
                  let shape_of i =
                    match kind_of_head with
                    | `Ind -> if i < nparams then "ind_param" else "ind_index"
                    | `Ctor -> if i < nparams then "ctor_param" else "ctor_field"
                    | `Other -> "app_arg" in
                  (* TEMPLATE POLYMORPHISM. A template inductive's parameter types
                     are NOT what its declaration says: the kernel SUBSTITUTES each
                     template level with the sort of the argument actually supplied
                     (`Typeops.make_param_univs` feeding
                     `type_of_inductive_knowing_parameters`), so NO subtyping is
                     required at those positions at all. Checking against the
                     declared arity instead makes every `eq`/`prod`/`sigT`/`sig`/
                     `option` application look like a cumulative use -- on
                     `veric/compcert_rmaps` that alone accounted for most of the
                     first run's 2273 rows, i.e. the key would have been mostly
                     wolf. Ask Retyping for the arity KNOWING THE PARAMETERS, which
                     is the pretyping-level spelling of what the kernel does. *)
                  (match (try Some (if is_template then
                                      Retyping.type_of_global_reference_knowing_parameters
                                        env evd f args
                                    else Retyping.get_type_of env evd f)
                          with _ -> incr cs_retype_fail; None) with
                   | None -> ()
                   | Some fty0 ->
                     if is_template then incr cs_template;
                     let fty = ref fty0 in
                     Array.iteri (fun i arg ->
                         match EConstr.kind evd (Reductionops.whd_all env evd !fty) with
                         | Constr.Prod (_, dom, cod) ->
                           (match (try Some (Retyping.get_type_of env evd arg)
                                   with _ -> incr cs_retype_fail; None) with
                            | None -> ()
                            | Some aty ->
                              cs_check env decl region (shape_of i) i head aty dom);
                           fty := EConstr.Vars.subst1 arg cod
                         | _ -> incr cs_arity_fail) args)
                | _ -> () in
              (* The iterator. `map_constr_with_full_binders` maintains the env
                 through EVERY binder form including Case branches and Fix; the
                 mapped term it returns is thrown away. *)
              let cs_scan env decl region c0 =
                let rec go env c =
                  (match EConstr.kind evd c with
                   | Constr.App _ -> cs_app env decl region c
                   | Constr.LetIn (_, b, t, _) ->
                     (match (try Some (Retyping.get_type_of env evd b)
                             with _ -> incr cs_retype_fail; None) with
                      | None -> () | Some bt ->
                        cs_check env decl region "letin" (-1) "" bt t)
                   | Constr.Cast (x, _, t) ->
                     (match (try Some (Retyping.get_type_of env evd x)
                             with _ -> incr cs_retype_fail; None) with
                      | None -> () | Some xt ->
                        cs_check env decl region "cast" (-1) "" xt t)
                   | Constr.Case (ci, u, pms, p, iv, scrut, brs) ->
                     (* MATCH BRANCHES: `Typeops.check_branch_types` compares each
                        branch's type against the motive instantiated at that
                        constructor with `conv_leq`, so a dependent elimination whose
                        motive lands in a HIGHER sort than a branch produces is a
                        cumulative use with no Sort node visible in the source. Build
                        the expected branch types the way the kernel does
                        (`Inductive.build_branches_type` on the EXPANDED case, whose
                        return clause is already the lambda over indices+scrutinee
                        that function wants). *)
                     (match (try
                               let (_, (pret, _), _, _, ebrs) =
                                 EConstr.expand_case env evd
                                   (ci, u, pms, p, iv, scrut, brs) in
                               let specif =
                                 Inductive.lookup_mind_specif env ci.Constr.ci_ind in
                               let ku = EConstr.EInstance.kind evd u in
                               let kpms =
                                 Array.to_list
                                   (Array.map EConstr.Unsafe.to_constr pms) in
                               let lbr =
                                 Inductive.build_branches_type
                                   (ci.Constr.ci_ind, ku) specif kpms
                                   (EConstr.Unsafe.to_constr pret) in
                               Some (ebrs, lbr)
                             with _ -> incr cs_arity_fail; None) with
                      | None -> ()
                      | Some (ebrs, lbr) ->
                        if Array.length ebrs = Array.length lbr then
                          Array.iteri (fun i br ->
                              match (try Some (Retyping.get_type_of env evd br)
                                     with _ -> incr cs_retype_fail; None) with
                              | None -> () | Some brt ->
                                cs_check env decl region "case_branch" i
                                  (Names.MutInd.to_string (fst ci.Constr.ci_ind))
                                  brt (EConstr.of_constr lbr.(i))) ebrs
                        else incr cs_arity_fail)
                   | Constr.Fix (_, (nas, tys, bds))
                   | Constr.CoFix (_, (nas, tys, bds)) ->
                     let shape = (match EConstr.kind evd c with
                         | Constr.Fix _ -> "fix_body" | _ -> "cofix_body") in
                     let n = Array.length tys in
                     let env' = EConstr.push_rec_types (nas, tys, bds) env in
                     Array.iteri (fun i bd ->
                         match (try Some (Retyping.get_type_of env' evd bd)
                                with _ -> incr cs_retype_fail; None) with
                         | None -> () | Some bt ->
                           cs_check env' decl region shape i "" bt
                             (EConstr.Vars.lift n tys.(i))) bds
                   | _ -> ());
                  ignore (Termops.map_constr_with_full_binders
                            env evd EConstr.push_rel go env c);
                  c in
                try ignore (go env c0) with ex ->
                  incr cs_scan_fail;
                  Printf.eprintf "rocq2lean: cumulativity_sites traversal ABORTED in \
%s (%s) -- every site in that declaration is MISSING from the key: %s\n%!"
                    decl region (Printexc.to_string ex) in
              (* A POLYMORPHIC declaration's own `Var i` levels are not in the global
                 graph, so conversion cannot see them; push the abstract context or
                 every check on such a declaration raises and is lost. *)
              let cs_env_for = function
                | Declarations.Polymorphic auctx ->
                  Environ.push_context ~strict:false
                    (UVars.AbstractContext.repr auctx) genv
                | _ -> genv in
              Environ.fold_constants (fun c cb () ->
                  if Names.ModPath.equal
                      (mp_root (Names.Constant.modpath c)) this_mp then begin
                    let decl = Names.Constant.to_string c in
                    let env = cs_env_for cb.Declarations.const_universes in
                    (match cb.Declarations.const_body with
                     | Declarations.Def body ->
                       let body = EConstr.of_constr body in
                       (* The declaration's OWN body-vs-declared-type CUMUL check.
                          This is the site that a `Definition f@{u v | u < v} :
                          Type@{u} -> Type@{v} := fun T => T` lands on: the body has
                          type `Type@{u} -> Type@{u}`, the declared type demands
                          `Type@{u} -> Type@{v}`, and only the codomain differs. *)
                       (match (try Some (Retyping.get_type_of env evd body)
                               with _ -> incr cs_retype_fail; None) with
                        | None -> () | Some bt ->
                          cs_check env decl "body" "decl_body" (-1) "" bt
                            (EConstr.of_constr cb.Declarations.const_type));
                       cs_scan env decl "body" body
                     | _ -> ());
                    cs_scan env decl "type"
                      (EConstr.of_constr cb.Declarations.const_type)
                  end) genv ();
              Environ.fold_inductives (fun mind mib () ->
                  if Names.ModPath.equal
                      (mp_root (Names.MutInd.modpath mind)) this_mp then begin
                    let env = cs_env_for mib.Declarations.mind_universes in
                    let univ = match mib.Declarations.mind_universes with
                      | Declarations.Polymorphic auctx ->
                        UVars.make_abstract_instance auctx
                      | _ -> UVars.Instance.empty in
                    Array.iteri (fun i oib ->
                        let base =
                          Names.ModPath.to_string (Names.MutInd.modpath mind) ^ "."
                          ^ Names.Id.to_string oib.Declarations.mind_typename in
                        (match (try Some (Inductive.type_of_inductive ((mib, oib), univ))
                                with _ -> incr cs_scan_fail; None) with
                         | None -> () | Some t ->
                           cs_scan env base "arity" (EConstr.of_constr t));
                        (match (try Some (Inductive.type_of_constructors
                                            ((mind, i), univ) (mib, oib))
                                with _ -> incr cs_scan_fail; None) with
                         | None -> () | Some ctys ->
                           Array.iteri (fun j cty ->
                               cs_scan env base
                                 ("ctor:" ^ Names.Id.to_string
                                    oib.Declarations.mind_consnames.(j))
                                 (EConstr.of_constr cty)) ctys))
                      mib.Declarations.mind_packets
                  end) genv ();
              if !cs_retype_fail > 0 || !cs_scan_fail > 0 || !cs_arity_fail > 0
                 || !cs_conv_raised > 0 then
                Printf.eprintf "rocq2lean: cumulativity_sites is INCOMPLETE for %s -- \
%d site(s) emitted from %d checks, but retype_fail=%d scan_fail=%d arity_fail=%d \
conv_raised=%d: a cumulative use in any of those positions is MISSING from the key, \
so a consumer ranking cumulative uses UNDER-counts them (not_leq=%d unlocated=%d)\n%!"
                  (Names.DirPath.to_string ldir) !cs_emitted !cs_checks
                  !cs_retype_fail !cs_scan_fail !cs_arity_fail !cs_conv_raised
                  !cs_not_leq !cs_unlocated;
              (if Sys.getenv_opt "R2L_TRACE_CUM" <> None then
                 Printf.eprintf "rocq2lean: cumulativity_sites %s: emitted=%d \
checks=%d not_leq=%d unlocated=%d retype_fail=%d scan_fail=%d arity_fail=%d \
conv_raised=%d template_heads=%d cpu=%.3fs\n%!" (Names.DirPath.to_string ldir)
                   !cs_emitted !cs_checks !cs_not_leq !cs_unlocated !cs_retype_fail
                   !cs_scan_fail !cs_arity_fail !cs_conv_raised !cs_template
                   (Sys.time () -. cs_t0))
            with e ->
              Printf.eprintf "rocq2lean: cumulativity_sites key FAILED -- the consumer \
gets an EMPTY list and will read that as \"Rocq used no cumulativity here\", which is \
the one wrong conclusion this key exists to prevent: %s\n%!"
                (Printexc.to_string e));
           Buffer.add_string buf "],\"detyped_globs\":[";
           (try
              let env = Global.env () in
              let this_mp = Names.ModPath.MPfile ldir in
              let rec mp_root = function
                | Names.ModPath.MPdot (mp, _) -> mp_root mp
                | mp -> mp in
              let evd = Evd.from_env env in
              (* --- serlib-format glob_constr -> JSON (matched against a real
                 petanque/intern capture of `Bool.le`) --- *)
              let jstr s = "\"" ^ esc s ^ "\"" in
              let jarr l = "[" ^ String.concat "," l ^ "]" in
              let jid id = jarr [jstr "Id"; jstr (Names.Id.to_string id)] in
              let jlbl l = jarr [jstr "Id"; jstr (Names.Label.to_string l)] in
              let jdirpath dp =
                jarr [jstr "DirPath"; jarr (List.map jid (Names.DirPath.repr dp))] in
              let rec jmodpath = function
                | Names.ModPath.MPfile dp -> jarr [jstr "MPfile"; jdirpath dp]
                | Names.ModPath.MPbound _ as mp ->
                    jarr [jstr "MPbound"; jstr (Names.ModPath.to_string mp)]
                | Names.ModPath.MPdot (mp, l) ->
                    jarr [jstr "MPdot"; jmodpath mp; jlbl l] in
              let jkername kn =
                let mp, l = Names.KerName.repr kn in
                jarr [jstr "KerName"; jmodpath mp; jlbl l] in
              let jconstant c =
                r2l_note_const c;
                let cu = Names.Constant.user c and cc = Names.Constant.canonical c in
                if Names.KerName.equal cu cc
                then jarr [jstr "Constant"; jkername cu; "null"]
                else jarr [jstr "Constant"; jkername cu; jkername cc] in
              let jmutind mi =
                r2l_note_mind mi;
                let cu = Names.MutInd.user mi and cc = Names.MutInd.canonical mi in
                if Names.KerName.equal cu cc
                then jarr [jstr "MutInd"; jkername cu; "null"]
                else jarr [jstr "MutInd"; jkername cu; jkername cc] in
              let jind (mi, i) = jarr [jmutind mi; string_of_int i] in
              let jconstruct (ind, j) = jarr [jind ind; string_of_int j] in
              let jgref = function
                | Names.GlobRef.VarRef id -> jarr [jstr "VarRef"; jid id]
                | Names.GlobRef.ConstRef c -> jarr [jstr "ConstRef"; jconstant c]
                | Names.GlobRef.IndRef ind -> jarr [jstr "IndRef"; jind ind]
                | Names.GlobRef.ConstructRef cs -> jarr [jstr "ConstructRef"; jconstruct cs] in
              let jname = function
                | Names.Name.Anonymous -> jarr [jstr "Anonymous"]
                | Names.Name.Name id -> jarr [jstr "Name"; jid id] in
              let jbk = function
                | Glob_term.Explicit -> jarr [jstr "Explicit"]
                | Glob_term.MaxImplicit -> jarr [jstr "MaxImplicit"]
                | Glob_term.NonMaxImplicit -> jarr [jstr "NonMaxImplicit"] in
              (* rocq2lean: hoisted out of the `GSort` branch so `GRef`'s universe
                 INSTANCE can be serialized in exactly the same shape (see `juinst`). *)
              let jsortname = function
                | Glob_term.GSProp        -> jstr "SProp"
                | Glob_term.GProp         -> jstr "Prop"
                | Glob_term.GSet          -> jstr "Set"
                | Glob_term.GUniv l       -> jstr (Univ.Level.to_string l)
                | Glob_term.GRawUniv l    -> jstr (Univ.Level.to_string l)
                | Glob_term.GLocalUniv id -> jstr (Names.Id.to_string id.CAst.v) in
              (* rocq2lean: the UNIVERSE INSTANCE at a `GRef` occurrence.
                 `GRef` is `GlobRef.t * glob_instance option`, and the second
                 component was being thrown away wholesale -- so every occurrence of a
                 universe-polymorphic constant reached the consumer with its instance
                 erased, and the only thing left to do with it was to let Lean guess.
                 Lean's universe unifier is essentially syntactic and will not INVENT a
                 `max` for a metavariable, which is exactly the "stuck at solving
                 universe constraint" shape in CMorphisms.

                 `glob_instance = glob_quality list * glob_level list`; a `glob_level`
                 is `glob_sort_name glob_sort_gen`, i.e. `UAnonymous` (nothing to name)
                 or `UNamed <sort name>`. Emitted as
                   null | [[<quality>, ...], [<level>, ...]]
                 where a level is `null` (anonymous) or `[<name>, 0]`. The `0` is the
                 GSort levels' INCREMENT slot, kept so the consumer shares one decoder;
                 an instance level never carries an increment (an instance holds ATOMIC
                 levels -- Coq expresses `max` through constraints, not here).

                 As with `GSort`, `Detyping.detype_instance` returns `None` unless
                 `Detyping.print_universes` is set -- which the sidecar already does. *)
              let jquality = function
                | Glob_term.GQConstant q ->
                    jstr (Sorts.Quality.Constants.pr q |> Pp.string_of_ppcmds)
                | Glob_term.GQualVar (Glob_term.GLocalQVar id) ->
                    (match id.CAst.v with
                     | Names.Name.Anonymous -> jstr "_"
                     | Names.Name.Name i -> jstr (Names.Id.to_string i))
                | Glob_term.GQualVar (Glob_term.GQVar q)
                | Glob_term.GQualVar (Glob_term.GRawQVar q) ->
                    jstr (Sorts.QVar.to_string q) in
              let jglevel = function
                | Glob_term.UAnonymous _ -> "null"
                | Glob_term.UNamed n -> jarr [jsortname n; "0"] in
              let juinst = function
                | None -> "null"
                | Some (qs, us) ->
                    jarr [jarr (List.map jquality qs); jarr (List.map jglevel us)] in
              let wrap node = "{\"v\":" ^ node ^ ",\"loc\":null}" in
              let rec jg gc = wrap (jnode (DAst.get gc))
              and jnode = function
                | Glob_term.GRef (gr, u) -> jarr [jstr "GRef"; jgref gr; juinst u]
                | Glob_term.GVar id -> jarr [jstr "GVar"; jid id]
                | Glob_term.GApp (f, args) ->
                    jarr [jstr "GApp"; jg f; jarr (List.map jg args)]
                | Glob_term.GLambda (na, _, bk, t, b) ->
                    jarr [jstr "GLambda"; jname na; "null"; jbk bk; jg t; jg b]
                | Glob_term.GProd (na, _, bk, t, b) ->
                    jarr [jstr "GProd"; jname na; "null"; jbk bk; jg t; jg b]
                | Glob_term.GLetIn (na, _, d, ty, b) ->
                    let tyj = match ty with None -> "null" | Some t -> jg t in
                    jarr [jstr "GLetIn"; jname na; "null"; jg d; tyj; jg b]
                | Glob_term.GCases (_, rtn, tomatch, clauses) ->
                    (* rocq2lean: the `in I _ … c0` clause (`aliastyp`), alongside the
                       alias. It BINDS the index variables the return predicate mentions,
                       and dropping it left them FREE in the serialized motive — the
                       consumer then had to guess which free `GVar`s were index binders and
                       match them to positions by first occurrence, which is right for an
                       eliminator's `P i₁ … iₘ` but mis-assigns silently for a motive that
                       mentions its indices out of order. Serialized as
                       `[inductive, [names…]]`, so the consumer reads the binders and their
                       ORDER directly. *)
                    let jaliastyp = function
                      | None -> "null"
                      | Some at ->
                        let (ind, nas) = at.CAst.v in
                        jarr [jind ind; jarr (List.map jname nas)] in
                    (* rocq2lean: the SCRUTINEE'S TYPE, as a third element. The
                       explicitation pass ascribes an indexed match's scrutinee with the
                       type it already has (a semantic no-op), so the type is available
                       here as a `GCast`. `jg` renders `GCast` TRANSPARENTLY -- which is
                       what we want for the scrutinee itself, and is also why the
                       ascription is invisible unless read out explicitly, as here.
                       Gives the translator the index TERMS (the type's arguments past
                       `nparams`) directly, instead of elaborating the scrutinee in the
                       live Lean environment and delaborating them back. *)
                    let jtom (scrut, (na, aty)) =
                      let sty =
                        match DAst.get scrut with
                        | Glob_term.GCast (_, _, t) -> jg t
                        | _ -> "null" in
                      jarr [jg scrut; jarr [jname na; jaliastyp aty]; sty] in
                    let jclause cl =
                      let (ids, pats, body) = cl.CAst.v in
                      "{\"v\":" ^ jarr [ jarr (List.map jid ids);
                                         jarr (List.map jpat pats); jg body ]
                        ^ ",\"loc\":null}" in
                    (* rocq2lean: the RETURN PREDICATE (the dependent-match motive).
                       Coq's `match H in I _ _ _ c0 return T c0 with` types each branch
                       against the motive AT THAT BRANCH'S INDEX, which is how the absurd
                       branches of an inversion get discharged. Lean cannot re-synthesise
                       it, and beta-applying it to one index (what the consumer did while
                       this slot was `null`) pins ONE type for the whole match, so the
                       branches — which genuinely have different types — cannot all check.
                       `raw_print` above already makes detyping reconstruct the motive
                       instead of dropping it as synthesisable, so it is here to serialize;
                       we were discarding it. Consumer emits Lean's `(motive := …)`. *)
                    jarr [jstr "GCases"; jarr [jstr "RegularStyle"];
                          (match rtn with None -> "null" | Some p -> jg p);
                          jarr (List.map jtom tomatch); jarr (List.map jclause clauses)]
                | Glob_term.GIf (c, (na, _), t, e) ->
                    jarr [jstr "GIf"; jg c; jarr [jname na; "null"]; jg t; jg e]
                | Glob_term.GLetTuple (nas, (na, _), sc, b) ->
                    jarr [jstr "GLetTuple"; jarr (List.map jname nas);
                          jarr [jname na; "null"]; jg sc; jg b]
                | Glob_term.GSort (_, u) ->
                    (* rocq2lean: keep the sort family so the consumer renders the right
                       Lean sort (Prop/Type), instead of defaulting everything to Type. *)
                    let sname = (match u with
                      | Glob_term.UNamed [(Glob_term.GProp, _)]  -> "Prop"
                      | Glob_term.UNamed [(Glob_term.GSProp, _)] -> "SProp"
                      | Glob_term.UNamed [(Glob_term.GSet, _)]   -> "Set"
                      | _                                        -> "Type") in
                    (* rocq2lean: the UNIVERSE, as a THIRD element (additive -- consumers
                       reading arr[1] as the family string are unaffected).
                       `Type@{i}` and `Type@{i+1}` are BOTH the bare family "Type", so
                       without this they are indistinguishable: Coq's `Let U := Type` is
                       `U : Type@{i+1} := Type@{i}`, and both slots serialized identically.
                       Note `Detyping.detype_sort` only KEEPS the level when
                       `Detyping.print_universes` is set -- otherwise it returns the
                       anonymous `glob_Type_sort` and there is nothing here to serialize.
                       Shape: null (anonymous/flexible) | [[name, increment], ...] (a max). *)
                    (* `jsortname` is hoisted above (shared with `GRef`'s instance). *)
                    let juniv = (match u with
                      | Glob_term.UAnonymous _ -> "null"
                      | Glob_term.UNamed l ->
                        jarr (List.map
                                (fun (n, i) -> jarr [jsortname n; string_of_int i]) l)) in
                    jarr [jstr "GSort"; jstr sname; juniv]
                | Glob_term.GHole _ -> jarr [jstr "GHole"; jarr [jstr "GInternalHole"]]
                | Glob_term.GProj (_, args, c) ->
                    jarr (jstr "GApp" :: jg c :: [jarr (List.map jg args)])
                (* rocq2lean: PRIMITIVE LITERALS. These used to be dropped as an
                   anonymous GHole — the SAME tag as a genuine hole, so the consumer
                   could not even detect the loss — and `63%uint63` reached the
                   translator as `_`. That was 69 of corelib's 200 elaboration
                   errors, and a silent-mistranslation hazard wherever Lean managed
                   to solve the hole. Emit them structurally instead.
                   `Uint63.to_string` is the exact UNSIGNED decimal (the signed
                   reading of e.g. `lsl 1 62` would be wrong). `Float64.to_string`
                   is "%.17g", which round-trips binary64, and yields
                   "nan"/"infinity"/"neg_infinity" for the specials; the hex form
                   rides along as an exact audit trail. *)
                | Glob_term.GInt i ->
                    jarr [jstr "GInt"; jstr (Uint63.to_string i)]
                | Glob_term.GFloat f ->
                    jarr [jstr "GFloat"; jstr (Float64.to_string f);
                                         jstr (Float64.to_hex_string f)]
                | Glob_term.GString s ->
                    (* HEX, not `jstr` on the raw bytes: a Coq pstring is a BYTE
                       string, and `esc` above passes bytes >= 0x80 through raw —
                       which emits invalid UTF-8 and can make the WHOLE metadata
                       file unparseable, whereupon the consumer swallows the parse
                       failure and proceeds with NO metadata for the file. *)
                    let bs = Pstring.to_string s in
                    let hex = String.concat "" (List.init (String.length bs)
                                (fun k -> Printf.sprintf "%02x" (Char.code bs.[k]))) in
                    jarr [jstr "GString"; jstr hex]
                (* rocq2lean: FIXPOINT bodies. A `Fixpoint`'s constant body is a
                   kernel `Fix`, which detypes to `GRec` — and the catch-all below
                   used to serialize it as a HOLE, so EVERY recursive definition
                   arrived at the translator with an empty body and had to keep
                   rendering from source syntax. Shape (serlib order):
                   GRec of glob_fix_kind * Id.t array * glob_decl list array
                           * glob_constr array (types) * glob_constr array (bodies),
                   glob_decl_g = Name.t * relevance_info * binding_kind
                                 * glob_constr option * glob_constr. *)
                | Glob_term.GRec (fk, ids, decls, types, bodies) ->
                    let jfk = (match fk with
                      | Glob_term.GFix (ra, i) ->
                          jarr [jstr "GFix";
                                jarr [ jarr (Array.to_list (Array.map (function
                                         | None -> "null"
                                         | Some k -> string_of_int k) ra));
                                       string_of_int i ]]
                      | Glob_term.GCoFix i -> jarr [jstr "GCoFix"; string_of_int i]) in
                    (* glob_decl_g carries relevance_info 2nd, emitted as null —
                       same convention as GLambda/GProd above. *)
                    let jdecl (na, _, bk, bo, ty) =
                      jarr [jname na; "null"; jbk bk;
                            (match bo with None -> "null" | Some b -> jg b); jg ty] in
                    jarr [jstr "GRec"; jfk;
                          jarr (Array.to_list (Array.map jid ids));
                          jarr (Array.to_list (Array.map
                            (fun ds -> jarr (List.map jdecl ds)) decls));
                          jarr (Array.to_list (Array.map jg types));
                          jarr (Array.to_list (Array.map jg bodies))]
                (* rocq2lean: a CAST is a typing annotation, not content — Lean
                   re-infers, so serialize straight through to the inner term. The
                   catch-all below used to flatten it to a hole, which is how a
                   COERCION application (`Coercion Aexp_of_aexp` + `Arguments … /`)
                   in PLF's assertion notations came out as the unparseable `@_ st`. *)
                | Glob_term.GCast (c, _, _) -> jnode (DAst.get c)
                (* rocq2lean: the remaining unhandled nodes stay holes, but each
                   carries a DISTINGUISHING tag so the next one to matter can be
                   identified from the sidecar instead of guessed at. The consumer
                   matches on the "GHole" head only and ignores this payload. *)
                | Glob_term.GEvar _ -> jarr [jstr "GHole"; jarr [jstr "R2LUnsupported_GEvar"]]
                | Glob_term.GPatVar _ -> jarr [jstr "GHole"; jarr [jstr "R2LUnsupported_GPatVar"]]
                | Glob_term.GGenarg _ -> jarr [jstr "GHole"; jarr [jstr "R2LUnsupported_GGenarg"]]
                | Glob_term.GArray _ -> jarr [jstr "GHole"; jarr [jstr "R2LUnsupported_GArray"]]
                (* No catch-all: the match is EXHAUSTIVE, so a future glob node added
                   upstream is a compile error here rather than a silent hole. That
                   silent hole is exactly what hid `GRec` (every fixpoint body) and
                   `GCast` (PLF's coercion-headed assertions). *)
              and jpat p =
                match DAst.get p with
                | Glob_term.PatVar na ->
                    "{\"v\":" ^ jarr [jstr "PatVar"; jname na] ^ ",\"loc\":null}"
                | Glob_term.PatCstr (cstr, subs, na) ->
                    "{\"v\":" ^ jarr [jstr "PatCstr"; jconstruct cstr;
                                      jarr (List.map jpat subs); jname na]
                      ^ ",\"loc\":null}" in
              let firstg = ref true in
              Environ.fold_constants (fun c cb () ->
                if Names.ModPath.equal (mp_root (Names.Constant.modpath c)) this_mp then
                  match cb.Declarations.const_body with
                  | Declarations.Def body ->
                    (try
                       (* rocq2lean: force RAW-PRINT detype so a 2-ctor
                          match (e.g. bool) is emitted as a real `GCases`
                          (RegularStyle, carrying the constructor names via
                          `PatCstr` ConstructRefs) rather than Coq's if-sugar
                          `GIf` — the latter renders to a Lean `if` that needs
                          a `Decidable` instance the ground-translated `bool`
                          lacks, so `Bool.le` & its ~1232 refs fail to
                          elaborate. `raw_print` also bypasses the
                          factorize/default-clause synthesis (detype_eqns'
                          build_tree path), giving clean per-constructor
                          clauses that match `petanque/intern`'s glob — the
                          shape the translator's `translateGlob` was built for.
                          Non-`match` node shapes are unaffected. *)
                       let gc =
                         Flags.with_options [Flags.raw_print; Detyping.print_universes]
                           (Detyping.detype Detyping.Now env evd)
                           (r2l_explicitate env evd (EConstr.of_constr body)) in
                       let j = jg gc in
                       if not !firstg then Buffer.add_char buf ',';
                       firstg := false;
                       Buffer.add_string buf
                         (Printf.sprintf "[\"%s\",%s]" (esc (Names.Constant.to_string c)) j)
                     with _ -> ())
                  | _ -> ()) env ();
              (* rocq2lean: TYPE globs — detype each this-file constant's
                 `const_type` (its STATEMENT), for EVERY constant regardless of
                 body kind. Theorems/lemmas have opaque (proof) bodies, so they
                 emit NO `detyped_globs` entry, yet their `const_type` IS the
                 statement we want — this recovers theorem statements that DROP
                 on a notation the fragile per-statement live-intern couldn't
                 render (`_ = _`, `~ _`, sig, …). Same serializer (`jg`), same
                 `raw_print` (dependent types can carry `match`es). *)
              Buffer.add_string buf "],\"detyped_type_globs\":[";
              let firstt = ref true in
              Environ.fold_constants (fun c cb () ->
                if Names.ModPath.equal (mp_root (Names.Constant.modpath c)) this_mp then
                  (try
                     let gc =
                       Flags.with_options [Flags.raw_print; Detyping.print_universes]
                         (Detyping.detype Detyping.Now env evd)
                         (r2l_explicitate env evd
                            (EConstr.of_constr cb.Declarations.const_type)) in
                     let j = jg gc in
                     if not !firstt then Buffer.add_char buf ',';
                     firstt := false;
                     Buffer.add_string buf
                       (Printf.sprintf "[\"%s\",%s]" (esc (Names.Constant.to_string c)) j)
                   with _ -> ())) env ();
              (* rocq2lean: detyped INDUCTIVES — arity + per-constructor types, so a
                 Record/inductive that DROPS on an unrenderable field notation
                 (Morphisms `respectful` `_ ==> _`, …) can be rendered FAITHFULLY from
                 the kernel. `fold_constants` misses inductives (not constants), so fold
                 the inductive blocks. Types are FULL (params as leading ∀-binders, via
                 `type_of_inductive`/`type_of_constructors`); the consumer strips the
                 first <nparams> to form the Lean `inductive` header. Entry:
                 ["<full ind name>", <nparams>, <arityGlob>, [["<ctor>",<ctorTyGlob>],…]].
                 Compare the modpath's FILE ROOT (`mp_root`), exactly as the constant
                 folds do: an inductive declared inside a `Module` (SF's `Module
                 BreakImp.` → `LF.Imp.BreakImp.ceval`, BinNums' `Module Z`) has modpath
                 `MPdot(MPfile …, "BreakImp")`, so a direct comparison silently omits
                 every module-nested inductive — and its consumers (`recoverCtorBinders`,
                 `recoverInductiveParams`) then leave the constructor binders as HOLES,
                 which Lean unifies to the wrong type. *)
              Buffer.add_string buf "],\"detyped_inductives\":[";
              let firsti = ref true in
              Environ.fold_inductives (fun mind mib () ->
                if Names.ModPath.equal (mp_root (Names.MutInd.modpath mind)) this_mp then
                  Array.iteri (fun i oib ->
                    (try
                       (* A POLYMORPHIC inductive needs an instance of its OWN universe
                          context; `Instance.empty` only fits a monomorphic one, and
                          `type_of_inductive` raises otherwise -- which the enclosing
                          `try` swallowed, silently dropping EVERY polymorphic inductive
                          from the sidecar. `Set Universe Polymorphism` in
                          CRelationClasses meant `PreOrder`/`PER`/`Equivalence`/
                          `StrictOrder`/`RewriteRelation` never reached the translator at
                          all, so each fell back to a parameterless `axiom X : Type` and
                          every use became "Function expected at PreOrder" -- ~45 errors
                          from five missing entries. *)
                       let univ =
                         match mib.Declarations.mind_universes with
                         | Declarations.Polymorphic auctx ->
                           UVars.make_abstract_instance auctx
                         | _ -> UVars.Instance.empty in
                       let ind_ty = Inductive.type_of_inductive ((mib, oib), univ) in
                       let ctor_tys = Inductive.type_of_constructors ((mind, i), univ) (mib, oib) in
                       let ind_name =
                         Names.ModPath.to_string (Names.MutInd.modpath mind) ^ "."
                         ^ Names.Id.to_string oib.Declarations.mind_typename in
                       let dj t = jg (Flags.with_options [Flags.raw_print; Detyping.print_universes]
                                        (Detyping.detype Detyping.Now env evd)
                                        (r2l_explicitate env evd (EConstr.of_constr t))) in
                       let arity_g = dj ind_ty in
                       let ctors_j = String.concat "," (Array.to_list (Array.mapi (fun j cty ->
                         Printf.sprintf "[\"%s\",%s]"
                           (esc (Names.Id.to_string oib.Declarations.mind_consnames.(j)))
                           (dj cty)) ctor_tys)) in
                       if not !firsti then Buffer.add_char buf ',';
                       firsti := false;
                       Buffer.add_string buf
                         (Printf.sprintf "[\"%s\",%d,%s,[%s]]"
                            (esc ind_name) mib.Declarations.mind_nparams arity_g ctors_j)
                     with _ -> ()))
                    mib.Declarations.mind_packets) env ();
              (* rocq2lean: whole INTERNED glob of each top-level expression the real
                 compile interned, keyed by source span [bp, ep, <glob>]. The compile-
                 time reliable expansion AST (notations expanded, scopes resolved) that
                 replaces the pet fork's fragile per-statement intern. Same serializer
                 (`jg`) as the detyped globs — but these are INTERNED (source→glob), so
                 they keep parsed sorts + source structure, unlike detype. *)
              Buffer.add_string buf "],\"interned_globs\":[";
              let firstn = ref true in
              List.iter (fun (loc, g) ->
                match loc with
                | Some l ->
                    (try
                       let (bp, ep) = Loc.unloc l in
                       let j = jg g in
                       if not !firstn then Buffer.add_char buf ',';
                       firstn := false;
                       Buffer.add_string buf (Printf.sprintf "[%d,%d,%s]" bp ep j)
                     with _ -> ())
                | None -> ()) (Constrintern.take_interned_globs ());
              (* rocq2lean: STRUCTURED twin of `binder_types` — the per-SPAN resolved
                 type of each source binder, as a detyped glob instead of a printed
                 string [bp, ep, <glob>]. Recorded by `comDefinition` in the same env
                 as the string form (see `record_binder_type_glob`). The string key is
                 kept alongside during the consumer migration. Deduped by span, like
                 `binder_types`. *)
              Buffer.add_string buf "],\"binder_type_globs\":[";
              let seenbg = Hashtbl.create 997 in
              let firstbg = ref true in
              List.iter (fun (loc, g) ->
                match loc with
                | Some l ->
                    (try
                       let (bp, ep) = Loc.unloc l in
                       if not (Hashtbl.mem seenbg (bp, ep)) then begin
                         Hashtbl.add seenbg (bp, ep) ();
                         let j = jg g in
                         if not !firstbg then Buffer.add_char buf ',';
                         firstbg := false;
                         Buffer.add_string buf (Printf.sprintf "[%d,%d,%s]" bp ep j)
                       end
                     with _ -> ())
                | None -> ()) (Constrintern.take_binder_type_globs ());
              (* rocq2lean: per-CONSTRUCTOR FIELD TELESCOPES, for every inductive this
                 file REFERENCES but does not itself define. `detyped_inductives`
                 (above) gives this for a file's OWN declarations; a wrapper declared
                 elsewhere (`And` from Corelib, seen from CompCert's `Smallstep.v`) has
                 none there, and the only other route to its constructor's field types
                 was introspecting the ALREADY-ELABORATED Lean declaration via a live
                 extraction environment (`[settings] incremental_elaboration`), which
                 most fixtures do not turn on. This closes that gap the same way
                 `referenced_nparams`/`inductive_ctor_names` already do: read it off
                 Coq's OWN loaded environment instead. Lives HERE (inside this shared
                 `jg`/`env`/`evd` scope), not alongside its `r2l_minds` siblings below,
                 because it is the only one of them that needs to DETYPE anything —
                 `jg` is local to this `try`.

                 Same per-row computation as `detyped_inductives`'s ctor half (full
                 ctor type, PARAMS-then-FIELDS as leading ∀-binders, its own universe
                 instance) — just pointed at `r2l_minds` (referenced, not
                 declared-here) and keyed the SAME RAW way `referenced_nparams` /
                 `inductive_ctor_names` / `referenced_sorts` are: `<globKey>#<blockIdx>`,
                 globIds order (innermost-first), UN-REVERSED. That is deliberate, not
                 an oversight: this key's one consumer (`nestFieldPlan?`'s sidecar
                 fallback) already holds the wrapper's `GRef`/`IndRef` glob NODE at the
                 use site (`headJ` in `globWrapperApp?`) and derives the same raw
                 string straight from it (`globRefSortKey?`'s computation) — no
                 Lean-name reconstruction, so no boundary to guess and no
                 `sidecarKeySpellings` needed for THIS particular lookup (unlike
                 `referenced_nparams`, whose consumer instead starts from an
                 already-elaborated Lean name and must guess the DirPath/module-label
                 boundary back).

                 Entry: [<globKey>#<blockIdx>, <nparams>, [["<ctor>",<ctorTyGlob>],…]].
                 Nparams is carried IN the row (not just cross-referenced against
                 `referenced_nparams`) so this key answers on its own — the fork rule
                 of one key failing closed independent of any other.

                 LOUD, not a bare `try…with _ -> ()`: a swallowed failure here would
                 leave `nestFieldPlan?`'s sidecar fallback silently unable to find a
                 wrapper's field structure, which is exactly the bug this key exists
                 to fix — so a lookup or detyping failure for one inductive is
                 reported to stderr and skips only THAT entry, not the whole key. *)
              Buffer.add_string buf "],\"referenced_ctor_types\":[";
              let firstrct = ref true in
              Hashtbl.iter (fun key mi ->
                match (try Some (Environ.lookup_mind mi env) with e ->
                         Printf.eprintf
                           "rocq2lean: referenced_ctor_types: lookup_mind %s failed: %s\n"
                           key (Printexc.to_string e); None) with
                | None -> ()
                | Some mib ->
                  let univ =
                    match mib.Declarations.mind_universes with
                    | Declarations.Polymorphic auctx -> UVars.make_abstract_instance auctx
                    | _ -> UVars.Instance.empty in
                  Array.iteri (fun i oib ->
                    match
                      (try
                         let ctor_tys =
                           Inductive.type_of_constructors ((mi, i), univ) (mib, oib) in
                         let dj t =
                           jg (Flags.with_options [Flags.raw_print; Detyping.print_universes]
                                 (Detyping.detype Detyping.Now env evd)
                                 (r2l_explicitate env evd (EConstr.of_constr t))) in
                         let ctors_j = String.concat "," (Array.to_list (Array.mapi
                           (fun j cty ->
                              Printf.sprintf "[\"%s\",%s]"
                                (esc (Names.Id.to_string
                                        oib.Declarations.mind_consnames.(j)))
                                (dj cty))
                           ctor_tys)) in
                         Some ctors_j
                       with e ->
                         Printf.eprintf
                           "rocq2lean: referenced_ctor_types: %s#%d ctor detyping \
failed: %s\n" key i (Printexc.to_string e);
                         None)
                    with
                    | None -> ()
                    | Some ctors_j ->
                      if not !firstrct then Buffer.add_char buf ',';
                      firstrct := false;
                      Buffer.add_string buf
                        (Printf.sprintf "[\"%s#%d\",%d,[%s]]"
                           (esc key) i mib.Declarations.mind_nparams ctors_j))
                    mib.Declarations.mind_packets) r2l_minds
            (* rocq2lean: LOUD, and SHAPE-PRESERVING. This one guard spans SIX keys,
               and the `Buffer.add_string` calls that OPEN the last five live inside it
               -- so a failure in the shared setup above (env / evd / the `jg`
               serializer) used to skip those openers and make `detyped_type_globs`,
               `detyped_inductives`, `interned_globs`, `binder_type_globs` and
               `referenced_ctor_types` VANISH from the document, which stayed
               syntactically valid the whole time. The consumer's only symptom was
               five silently-absent keys. Emit them empty so the shape is preserved,
               and say what happened. *)
            with e ->
              Printf.eprintf "rocq2lean: detyped-glob keys ABORTED (the remaining five \
are emitted EMPTY): %s\n%!" (Printexc.to_string e);
              Buffer.add_string buf
                "],\"detyped_type_globs\":[],\"detyped_inductives\":[],\"interned_globs\":[],\"binder_type_globs\":[],\"referenced_ctor_types\":[");
           (* rocq2lean: SPAN-FREE ordered CONSTRUCTOR NAMES per referenced inductive.
              Every other ctor-naming key here is per-OCCURRENCE and SPAN-keyed
              (`ref_resolutions`), which is unusable for a DETYPED glob's
              `ConstructRef`: detype drops locs, so there is no span to match and the
              consumer is left with (inductive kername, 1-based INDEX) and no name —
              and mapping Coq's index onto Lean's n-th constructor is unsound the
              moment the two declaration orders differ (`bool := true | false` vs
              `Bool := false | true`). `Environ.lookup_mind` on the LOADED environment
              gives Coq's OWN `mind_consnames` in Coq's OWN order for ANY inductive in
              scope — opam-dep (`Corelib.Init.Datatypes.bool`) and module-nested
              (`LF.Imp.BreakImp.com`) alike, and crucially for inductives defined in
              ANOTHER file (which `detyped_inductives`, filtered to `mp_root =
              this_mp`, can never carry). So the consumer indexes COQ's names to get
              Coq's name, then resolves THAT by name.

              Shape: one entry per (block, member) — `["<globKey>#<blockIdx>",
              ["c1","c2",…]]`, where `<globKey>` is already in the consumer's own
              `".".intercalate (globIds <MutInd>)` form and `<blockIdx>` selects the
              member of a mutual block. That is verbatim the key
              `Rocq2Lean.Translate`'s `constructRefCtors` is looked up by, so no
              conversion is needed on the Lean side. Scope: the `r2l_minds` table —
              inductives this file's metadata REFERENCES, not the whole env. *)
           Buffer.add_string buf "],\"inductive_ctor_names\":[";
           (try
              let env = Global.env () in
              let firstic = ref true in
              Hashtbl.iter (fun key mi ->
                try
                  let mib = Environ.lookup_mind mi env in
                  Array.iteri (fun i oib ->
                    let names = String.concat ","
                      (Array.to_list (Array.map (fun id ->
                         Printf.sprintf "\"%s\"" (esc (Names.Id.to_string id)))
                         oib.Declarations.mind_consnames)) in
                    if not !firstic then Buffer.add_char buf ',';
                    firstic := false;
                    Buffer.add_string buf
                      (Printf.sprintf "[\"%s#%d\",[%s]]" (esc key) i names))
                    mib.Declarations.mind_packets
                with _ -> ()) r2l_minds
            with _ -> ());
           (* rocq2lean: Coq's PARAMETER COUNT for every inductive this file REFERENCES.
              `detyped_inductives` carries nparams only for inductives DEFINED here, so a
              dependent match on a CROSS-FILE inductive (`bool` inside `Decimal`) left the
              consumer unable to split the scrutinee's type args into params vs indices,
              and `dependentMatchRedex?` had to fail closed. Lean's own `numParams` is NOT
              a substitute: the split must match COQ's view (the motive's binder names come
              from Coq's `in`-clause) and the translation can demote a Coq parameter into a
              Lean index. Keyed exactly like `inductive_ctor_names` above — note that is
              globIds order (innermost-first), which the consumer must REVERSE to match a
              Lean name. *)
           Buffer.add_string buf "],\"referenced_nparams\":[";
           (try
              let env = Global.env () in
              let firstnp = ref true in
              Hashtbl.iter (fun key mi ->
                try
                  let mib = Environ.lookup_mind mi env in
                  Array.iteri (fun i _oib ->
                    if not !firstnp then Buffer.add_char buf ',';
                    firstnp := false;
                    Buffer.add_string buf
                      (Printf.sprintf "[\"%s#%d\",%d]" (esc key) i
                         mib.Declarations.mind_nparams))
                    mib.Declarations.mind_packets
                with _ -> ()) r2l_minds
            with _ -> ());
           (* rocq2lean: TEMPLATE POLYMORPHISM, for every inductive this file REFERENCES.
              Rocq's `sig`/`sigT`/`prod`/… are ONE declaration whose result sort is
              recomputed per occurrence from the sorts of the actual parameters, so
              `{x : A | P x}` is `Prop` when `A : Prop` and `Type@{A.u0}` otherwise.
              Lean has no such thing: a declaration has ONE type, and Lean REJECTS the
              template supremum outright ("the resulting universe is not `Prop`, but it
              may be `Prop` for some parameter values"), forcing the `max 1` floor. At a
              Prop instance we are therefore exactly one level too high. The translator
              repairs that by emitting a SEPARATE Prop-sorted mirror declaration, but it
              may only do so where Rocq itself says "template" — sort INFERENCE over the
              constructor fields is NOT a substitute (`sumbool`'s fields are all proofs,
              yet it is a non-singleton `Set` that must keep large elimination).
              Emitted as [key#blockIdx, [per-param 0|1], propInstance, "<concl sort>"],
              keyed exactly like `referenced_nparams` above (globIds order, consumer
              reverses). The per-param mask is `template_param_arguments`: 1 where that
              LocalAssum parameter binds a quality or universe level, i.e. exactly the
              parameters the Prop instance sends to `Prop`. Non-template blocks emit NO
              entry at all.

              `propInstance` is the field that decides whether a mirror is SOUND, and it
              is computed HERE rather than by string-matching the printed sort, because
              the distinction is invisible in the parameter mask. Template blocks split
              into three kinds, and only the first has a Prop instance:
                sig/sig2/sigT/sigT2/prod  concl `QSort(β0, …)` — the sort QUALITY itself
                                          is abstracted, so instantiating it at Prop makes
                                          the whole thing Prop.  MIRROR.
                list/option/sum           concl `Type(max(Set, …))` — quality is a
                                          CONSTANT QType with a `Set` FLOOR, so the Prop
                                          instance is still `Set`, never Prop. NO mirror
                                          (a `list` in Prop would be flatly unsound).
                eq/ex                     concl `Prop` already; nothing to repair.
              So `propInstance` = "the concl's quality is a QVar", i.e. template-abstracted.
              `sumbool` is not template AT ALL and thus emits no entry — which is exactly
              why the gate must be Rocq's answer and never sort inference over the ctor
              fields (its fields are all proofs, yet it is a non-singleton `Set` that must
              keep large elimination). *)
           Buffer.add_string buf "],\"template_polymorphic\":[";
           (try
              let env = Global.env () in
              let firsttp = ref true in
              Hashtbl.iter (fun key mi ->
                (* No silent `with _ -> ()`: a swallowed failure here becomes a MISSING
                   entry, and a missing entry silently disables the mirror for that
                   inductive — a symptom that would surface far from its cause. *)
                match (try Some (Environ.lookup_mind mi env) with e ->
                         Printf.eprintf
                           "rocq2lean: template_polymorphic: lookup_mind %s failed: %s\n"
                           key (Printexc.to_string e); None) with
                | None -> ()
                | Some mib ->
                  (match mib.Declarations.mind_template with
                   | None -> ()
                   | Some tu ->
                     let mask = String.concat ","
                       (List.map (function None -> "0" | Some _ -> "1")
                          tu.Declarations.template_param_arguments) in
                     let concl =
                       Pp.string_of_ppcmds
                         (Sorts.debug_print tu.Declarations.template_concl) in
                     let prop_instance =
                       if Sorts.Quality.is_var
                            (Sorts.quality tu.Declarations.template_concl)
                       then 1 else 0 in
                     Array.iteri (fun i _oib ->
                       if not !firsttp then Buffer.add_char buf ',';
                       firsttp := false;
                       Buffer.add_string buf
                         (Printf.sprintf "[\"%s#%d\",[%s],%d,\"%s\"]"
                            (esc key) i mask prop_instance (esc concl)))
                       mib.Declarations.mind_packets)) r2l_minds
            with e ->
              Printf.eprintf "rocq2lean: template_polymorphic key FAILED: %s\n"
                (Printexc.to_string e));
           (* rocq2lean: the CODOMAIN SORT FAMILY of every gref this file REFERENCES —
              peel the `∀`s off the constant's type / the inductive's arity and report the
              sort you land on ("Prop"/"SProp"/"Set"/"Type"), or nothing at all when the
              codomain is not a sort (a theorem's type lands on a PROPOSITION, not on a
              sort — applying it yields a proof, so the absence is the correct answer and
              the consumer must fail closed on it).

              This is what lets the consumer decide, WITHOUT a live Lean environment,
              whether a template inductive's occurrence is at a Prop instance: it walks
              the argument's glob down to a head gref and reads that head's codomain sort.
              Both existing sorts of key are file-local and so cannot do it —
              `constant_sorts` reports the sort of a constant's WHOLE type (`Type` for
              `is_true : bool -> Prop`, the opposite of what is asked) and only for
              constants DECLARED here, and `detyped_type_globs` is likewise this file's
              own. The decisive cases are all cross-file: `is_true` from `Datatypes` seen
              from `ssrbool`, `eq` from `Logic` seen from `Specif`.

              Keys are the RAW globIds form (innermost-first), `"<key>#<blockIdx>"` for an
              inductive and bare for a constant, so a consumer holding a glob `GRef` node
              matches by `".".intercalate (globIds …)` with no reversal. *)
           Buffer.add_string buf "],\"referenced_sorts\":[";
           (try
              let env = Global.env () in
              let firstrs = ref true in
              let fam s =
                if Sorts.is_sprop s then Some "SProp"
                else if Sorts.is_prop s then Some "Prop"
                else if Sorts.is_set s then Some "Set"
                else match Sorts.quality s with
                  | Sorts.Quality.QConstant Sorts.Quality.QType -> Some "Type"
                  (* A quality VARIABLE (template/sort-polymorphic) has no fixed answer;
                     say nothing rather than guess `Type`. *)
                  | _ -> None in
              let rec codom t =
                match Constr.kind t with
                | Constr.Prod (_, _, b) -> codom b
                | Constr.LetIn (_, _, _, b) -> codom b
                | Constr.Cast (c, _, _) -> codom c
                | Constr.Sort s -> fam s
                | _ -> None in
              let emit k v =
                if not !firstrs then Buffer.add_char buf ',';
                firstrs := false;
                Buffer.add_string buf
                  (Printf.sprintf "[\"%s\",\"%s\"]" (esc k) (esc v)) in
              Hashtbl.iter (fun key mi ->
                match (try Some (Environ.lookup_mind mi env) with e ->
                         Printf.eprintf
                           "rocq2lean: referenced_sorts: lookup_mind %s failed: %s\n"
                           key (Printexc.to_string e); None) with
                | None -> ()
                | Some mib ->
                  Array.iteri (fun i oib ->
                    match fam oib.Declarations.mind_sort with
                    | None -> ()
                    | Some f -> emit (Printf.sprintf "%s#%d" key i) f)
                    mib.Declarations.mind_packets) r2l_minds;
              Hashtbl.iter (fun key c ->
                match (try Some (Environ.lookup_constant c env) with e ->
                         Printf.eprintf
                           "rocq2lean: referenced_sorts: lookup_constant %s failed: %s\n"
                           key (Printexc.to_string e); None) with
                | None -> ()
                | Some cb ->
                  (match codom cb.Declarations.const_type with
                   | None -> ()
                   | Some f -> emit key f)) r2l_consts
            with e ->
              Printf.eprintf "rocq2lean: referenced_sorts key FAILED: %s\n"
                (Printexc.to_string e));
           (* rocq2lean: DECLARED COERCIONS with their SOURCE and TARGET classes, resolved.
              The translator otherwise has to read `Coercion tm_var : string >-> tm.` off the
              SURFACE vernac, where `string`/`tm` are BARE qualids with no qualification and
              no per-occurrence resolution verdict — so since fully-qualified config keys
              became mandatory they matched nothing and were emitted verbatim, giving an
              `instance : Coe string tm` that does not elaborate (which disabled the whole
              coercion mechanism, including the `Coe aexp Aexp` that Coq's own inserted
              coercions depend on). `Coercionops` HAS the resolved classes, so publish them
              rather than making the consumer re-derive them from the function's signature.
              Each entry: [<function name>, <source class>, <target class>], where a class is
              a fully-qualified constant/inductive name, or "Sortclass"/"Funclass" for Coq's
              two non-nominal classes. Filtered to coercions whose FUNCTION belongs to this
              file, so a file gets only what it declares. *)
           Buffer.add_string buf "],\"coercion_classes\":[";
           (try
              let gref_name = function
                | Names.GlobRef.ConstRef c -> Some (Names.Constant.to_string c)
                (* Build from the MODPATH plus the packet's own typename. `MutInd.to_string`
                   already ends in the block's label, so appending the typename doubled it
                   (`PLF.Stlc.STLC.tm.tm`); and for a MUTUAL block the i-th packet's name is
                   not that label at all. Constructors come out type-qualified
                   (`…tm.tm_var`), matching `inductive_ctor_names`/`ref_resolutions`. *)
                | Names.GlobRef.IndRef (m, i) ->
                    let mib = Global.lookup_mind m in
                    Some (Names.ModPath.to_string (Names.MutInd.modpath m) ^ "."
                          ^ Names.Id.to_string mib.Declarations.mind_packets.(i).Declarations.mind_typename)
                | Names.GlobRef.ConstructRef ((m, i), j) ->
                    let mib = Global.lookup_mind m in
                    let pkt = mib.Declarations.mind_packets.(i) in
                    Some (Names.ModPath.to_string (Names.MutInd.modpath m) ^ "."
                          ^ Names.Id.to_string pkt.Declarations.mind_typename ^ "."
                          ^ Names.Id.to_string pkt.Declarations.mind_consnames.(j - 1))
                | Names.GlobRef.VarRef _ -> None in
              (* A class is a fully-qualified constant/inductive name, or one of Coq's two
                 non-nominal classes. `Sortclass` is load-bearing for the translator: it must
                 render as Lean's `Prop` sort keyword, not as an identifier. *)
              let cl_name = function
                | Coercionops.CL_SORT -> Some "Sortclass"
                | Coercionops.CL_FUN -> Some "Funclass"
                | Coercionops.CL_CONST c -> Some (Names.Constant.to_string c)
                | Coercionops.CL_IND ind -> gref_name (Names.GlobRef.IndRef ind)
                | Coercionops.CL_PROJ pr ->
                    Some (Names.Constant.to_string (Names.Projection.Repr.constant pr))
                | Coercionops.CL_SECVAR _ -> None in
              let firstc = ref true in
              List.iter (fun (gr, src, tgt) ->
                match gref_name gr, cl_name src, cl_name tgt with
                | Some f, Some s, Some t ->
                    if not !firstc then Buffer.add_char buf ',';
                    firstc := false;
                    Buffer.add_string buf
                      (Printf.sprintf "[\"%s\",\"%s\",\"%s\"]" (esc f) (esc s) (esc t))
                | _ -> ()) (ComCoercion.r2l_take_declared_coercions ())
            with _ -> ());
           (* rocq2lean: the SORT of each constant's TYPE (`Prop`/`Set`/`Type`/`SProp`),
              for `computeDefIsProof` / `computeThmIsType`. Those are the heaviest
              remaining LIVE pet consumers -- one `petanque/elaborate` query per definition
              and per theorem -- and no other key carries a sort, so they could not be
              migrated to the sidecar.

              This is `Retyping.get_sort_of` on the constant's `const_type`, i.e. the sort
              of the TYPE, which is exactly the question the consumers ask: a PROOF has
              type `P : Prop`, whereas a PREDICATE has type `nat -> Prop : Type`. Reading
              it off the type's own sort therefore distinguishes the two by construction,
              where peeling to a codomain does not -- conflating them once stubbed every
              predicate in the library and took SF LF from 18 to 77 errors.

              Same `mp_root` filter and the same `fold_constants` walk as
              `resolved_types`, so the keys are index-comparable. *)
           Buffer.add_string buf "],\"constant_sorts\":[";
           (try
              let env = Global.env () in
              let this_mp = Names.ModPath.MPfile ldir in
              let rec mp_root = function
                | Names.ModPath.MPdot (mp, _) -> mp_root mp
                | mp -> mp in
              let evd = Evd.from_env env in
              let firsts = ref true in
              Environ.fold_constants (fun c cb () ->
                if Names.ModPath.equal (mp_root (Names.Constant.modpath c)) this_mp then begin
                  try
                    let ty = EConstr.of_constr cb.Declarations.const_type in
                    let s = Retyping.get_sort_of env evd ty in
                    let nm = match EConstr.ESorts.kind evd s with
                      | Sorts.SProp   -> "SProp"
                      | Sorts.Prop    -> "Prop"
                      | Sorts.Set     -> "Set"
                      | Sorts.Type _  -> "Type"
                      | Sorts.QSort _ -> "QSort" in
                    if not !firsts then Buffer.add_char buf ',';
                    firsts := false;
                    Buffer.add_string buf
                      (Printf.sprintf "[\"%s\",\"%s\"]" (esc (Names.Constant.to_string c)) nm)
                  with _ -> ()
                end) env ()
            with _ -> ());
           (* rocq2lean: `Include`d / functor-instantiated declarations and their ORIGIN.

              An `Include M` does not re-elaborate `M`'s contents: it splices them in by
              module-level SUBSTITUTION, so `Stdlib.Arith.PeanoNat.Nat.iter` is a new
              kername for the very constant `Corelib.Init.Nat.iter` names. Rocq keeps
              both halves in the `KerPair` -- the USER name is where you wrote it, the
              CANONICAL name is where it was defined -- and converts the two by delta,
              which is why `Locate` says "syntactically equal to" and `reflexivity`
              proves them equal.

              The translator had no way to see this. Boot mode re-derives the included
              copy from its body, so Lean gets TWO independent definitions with
              identical bodies -- and for a structurally recursive one `isDefEq` cannot
              unfold `Nat.rec` on a variable, so they are simply different types to
              Lean. That is `PeanoNat.iter_rect`'s residual pair, and the
              `Op_plus`/`Op_sub`/`Op_mul` family. With the origin in hand the consumer
              can emit the copy as a TRANSPARENT ALIAS (`def iter := Corelib.Init.Nat.iter`)
              and every reference converges on one definition again.

              Emitted only where user <> canonical -- an ordinarily-declared constant has
              them equal, so the key holds exactly this file's aliased declarations.
              Rows: ["const"|"ind", "<user kername>", "<canonical kername>"], both in the
              same dotted spelling `resolved_types` / `declaration_order` use. *)
           Buffer.add_string buf "],\"constant_aliases\":[";
           (try
              let this_mp = Names.ModPath.MPfile ldir in
              let rec mp_root = function
                | Names.ModPath.MPdot (mp, _) -> mp_root mp
                | mp -> mp in
              let firsta = ref true in
              let emit kind u c =
                (* KerName equality on the STRINGS, not `KerName.equal`: we compare what
                   the consumer will see, so a pair that prints the same is never
                   reported as an alias. *)
                let us = Names.KerName.to_string u in
                let cs = Names.KerName.to_string c in
                if us <> cs then begin
                  if not !firsta then Buffer.add_char buf ',';
                  firsta := false;
                  Buffer.add_string buf
                    (Printf.sprintf "[\"%s\",\"%s\",\"%s\"]" kind (esc us) (esc cs))
                end in
              let env = Global.env () in
              Environ.fold_constants (fun c _ () ->
                if Names.ModPath.equal (mp_root (Names.Constant.modpath c)) this_mp then
                  emit "const" (Names.Constant.user c) (Names.Constant.canonical c))
                env ();
              Environ.fold_inductives (fun mind _ () ->
                if Names.ModPath.equal (mp_root (Names.MutInd.modpath mind)) this_mp then
                  emit "ind" (Names.MutInd.user mind) (Names.MutInd.canonical mind))
                env ()
            with e ->
              Printf.eprintf "rocq2lean: constant_aliases key FAILED: %s\n%!"
                (Printexc.to_string e));
           (* rocq2lean: which of this unit's inductive blocks are COINDUCTIVE, and
              whether each is RECURSIVE.

              `declaration_order` tags every inductive block `"ind"` and
              `detyped_inductives` carries no finiteness field, so a `CoInductive`
              reached the translator indistinguishable from an `Inductive` and was
              emitted as a Lean `inductive` -- a SILENT semantics change (Lean's
              `inductive` is the LEAST fixpoint: Coq's inhabited `stream A` becomes a
              provably EMPTY Lean type). Nothing downstream could detect the loss.

              Shape: `[["<kername>", 0|1], ...]`, the flag being 1 when the block is
              RECURSIVE. Both facts are needed, because they get different treatments:
              a recursive coinductive has no Lean rendering and must be REFUSED, while
              a NON-recursive one (`CoInductive apply_subrelation : Prop :=
              do_subrelation.`) is a constant functor, whose least and greatest
              fixpoints coincide -- so the Lean `inductive` is exactly right there and
              refusing it would be a false gap.

              Recursivity is decided on `Inductive.type_of_constructors`, i.e. the
              constructor types with the block's inductives SUBSTITUTED IN. It cannot
              be read off `mind_nf_lc`, where a self-reference is a de Bruijn `Rel`
              into the arity context and no `Ind` node appears at all.

              Each block is named BOTH ways its consumers key it: by the MutInd LABEL
              (the `declaration_order` form, from `Global.r2l_structure_order`) and by
              each packet's `mind_typename` (the `detyped_inductives` form). For a
              single non-mutual inductive these coincide and only one row is emitted. *)
           Buffer.add_string buf "],\"coinductives\":[";
           (try
              let env = Global.env () in
              let this_mp = Names.ModPath.MPfile ldir in
              let rec mp_root = function
                | Names.ModPath.MPdot (mp, _) -> mp_root mp
                | mp -> mp in
              let mentions mind c =
                let rec go c = match Constr.kind c with
                  | Constr.Ind ((mi, _), _) when Names.MutInd.CanOrd.equal mi mind -> true
                  | Constr.Construct (((mi, _), _), _) when Names.MutInd.CanOrd.equal mi mind -> true
                  | _ -> Constr.fold (fun acc t -> acc || go t) false c in
                go c in
              let firstco = ref true in
              let emit name rc =
                if not !firstco then Buffer.add_char buf ',';
                firstco := false;
                Buffer.add_string buf
                  (Printf.sprintf "[\"%s\",%d]" (esc name) (if rc then 1 else 0)) in
              Environ.fold_inductives (fun mind mib () ->
                if Names.ModPath.equal (mp_root (Names.MutInd.modpath mind)) this_mp
                   && mib.Declarations.mind_finite = Declarations.CoFinite then begin
                  let univ =
                    match mib.Declarations.mind_universes with
                    | Declarations.Polymorphic auctx -> UVars.make_abstract_instance auctx
                    | _ -> UVars.Instance.empty in
                  (* Fail CLOSED: if the constructor types cannot be recovered we must
                     claim RECURSIVE, so the consumer refuses rather than silently
                     emitting a least-fixpoint `inductive`. *)
                  let rc =
                    try
                      (* Only the constructor's ARGUMENTS count. Its CONCLUSION is the
                         inductive itself by construction (`do_marker : marker`), so
                         testing the whole type calls EVERY coinductive recursive. *)
                      let arg_mentions cty =
                        let (ctx, _concl) = Term.decompose_prod_decls cty in
                        List.exists (fun d ->
                          mentions mind (Context.Rel.Declaration.get_type d)
                          || (match Context.Rel.Declaration.get_value d with
                              | Some b -> mentions mind b
                              | None -> false)) ctx in
                      Array.to_list mib.Declarations.mind_packets
                      |> List.mapi (fun i oib -> (i, oib))
                      |> List.exists (fun (i, oib) ->
                           Array.exists arg_mentions
                             (Inductive.type_of_constructors ((mind, i), univ) (mib, oib)))
                    with _ -> true in
                  let mp = Names.ModPath.to_string (Names.MutInd.modpath mind) in
                  let lbl = mp ^ "." ^ Names.Label.to_string (Names.MutInd.label mind) in
                  emit lbl rc;
                  Array.iter (fun oib ->
                    let tn = mp ^ "." ^ Names.Id.to_string oib.Declarations.mind_typename in
                    if tn <> lbl then emit tn rc) mib.Declarations.mind_packets
                end) env ()
            (* rocq2lean: LOUD. A truncated `coinductives` array makes a recursive
               `CoInductive` indistinguishable from an `Inductive`, so the consumer
               emits Lean's LEAST fixpoint where Rocq means the greatest -- a different
               type (Rocq's inhabited `stream A` becomes provably EMPTY) that still
               elaborates. Refusing is this key's whole purpose, so its failure can
               never be silent. The per-block recursivity test already fails CLOSED
               (`with _ -> true`); this is the array-level counterpart. *)
            with e ->
              Printf.eprintf "rocq2lean: coinductives key FAILED -- a recursive \
CoInductive in this file may be emitted as a Lean `inductive`: %s\n%!"
                (Printexc.to_string e));
           (* rocq2lean: ROCQ'S OWN RENDERING of every coinductive block in this file,
              printed by the kernel's own printer (`Printmod.pr_mutual_inductive_body`,
              i.e. exactly what `Print <T>` shows).

              WHY IT IS IN THE SIDECAR AT ALL. A recursive `CoInductive` has no Lean
              declaration form, so the consumer AXIOMATIZES it (the type, its
              constructors, a non-recursive dependent `casesOn`, its iota rules). Those
              axioms say nothing about what they replaced, and the downstream
              proof-filling AI has to reconstruct exactly that. The consumer emits this
              string as a comment in front of the block.

              It comes from the ENVIRONMENT, not from the `.v` file: rocq2lean does not
              parse surface syntax and must not start
              (`docs/investigations/surface-syntax-audit.md`). Reading the kernel and
              printing it is not a surface-syntax dependency.

              ADDITIVE KEY, on purpose: extending `coinductives`' row from 2 to 3
              elements would have broken its exact-arity Lean decoder, and THAT decoder
              is what decides whether a coinductive is recognised at all -- a miss there
              emits Lean's least fixpoint for Rocq's greatest, silently. A new key cannot
              do that: an old sidecar simply yields no comment.

              Keyed BOTH ways its consumer can spell a block, exactly as `coinductives`
              is: by the MutInd LABEL and by each packet's `mind_typename`. *)
           Buffer.add_string buf "],\"coinductive_sources\":[";
           (try
              let env = Global.env () in
              let this_mp = Names.ModPath.MPfile ldir in
              let rec mp_root = function
                | Names.ModPath.MPdot (mp, _) -> mp_root mp
                | mp -> mp in
              let firstcs = ref true in
              let emit name txt =
                if not !firstcs then Buffer.add_char buf ',';
                firstcs := false;
                Buffer.add_string buf
                  (Printf.sprintf "[\"%s\",\"%s\"]" (esc name) (esc txt)) in
              Environ.fold_inductives (fun mind mib () ->
                if Names.ModPath.equal (mp_root (Names.MutInd.modpath mind)) this_mp
                   && mib.Declarations.mind_finite = Declarations.CoFinite then begin
                  (* LOUD per block: a printer failure here loses the comment for THIS
                     coinductive only, and a silent loss is indistinguishable from
                     "this file has no coinductive". No bare `with _ -> ()`. *)
                  match
                    (try Some (Pp.string_of_ppcmds
                                 (Printmod.pr_mutual_inductive_body env mind mib None))
                     with e ->
                       Printf.eprintf "rocq2lean: coinductive_sources: could not PRINT \
%s -- its axiomatization will carry no comment showing what it replaced: %s\n%!"
                         (Names.MutInd.to_string mind) (Printexc.to_string e);
                       None)
                  with
                  | None -> ()
                  | Some txt ->
                    let mp = Names.ModPath.to_string (Names.MutInd.modpath mind) in
                    let lbl = mp ^ "." ^ Names.Label.to_string (Names.MutInd.label mind) in
                    emit lbl txt;
                    Array.iter (fun oib ->
                      let tn = mp ^ "." ^ Names.Id.to_string oib.Declarations.mind_typename in
                      if tn <> lbl then emit tn txt) mib.Declarations.mind_packets
                end) env ()
            with e ->
              Printf.eprintf "rocq2lean: coinductive_sources key FAILED -- every \
axiomatized CoInductive in this file will carry no comment showing what it replaced: \
%s\n%!" (Printexc.to_string e));
           (* rocq2lean: ROCQ'S OWN RENDERING of every `CoFixpoint` in this file, for the
              same reason and the same consumer. Lean has no `cofix` term, so a
              `CoFixpoint` is emitted with its true TYPE and an unproven body -- a
              handoff, not a translation -- and nothing in the output says what the body
              was.

              This is the POST-ELABORATION body (the kernel `cofix` term), which is what
              the environment holds; it is not the surface syntax and the consumer's
              comment says so. Detected by a `CoFix` node in the body, so it needs no
              vernac-level flag. *)
           Buffer.add_string buf "],\"cofixpoint_sources\":[";
           (try
              let env = Global.env () in
              let sigma = Evd.from_env env in
              let this_mp = Names.ModPath.MPfile ldir in
              let rec mp_root = function
                | Names.ModPath.MPdot (mp, _) -> mp_root mp
                | mp -> mp in
              let rec has_cofix c = match Constr.kind c with
                | Constr.CoFix _ -> true
                | _ -> Constr.fold (fun acc t -> acc || has_cofix t) false c in
              let firstcf = ref true in
              Environ.fold_constants (fun cst cb () ->
                if Names.ModPath.equal (mp_root (Names.Constant.modpath cst)) this_mp then
                  match cb.Declarations.const_body with
                  | Declarations.Def c when has_cofix c ->
                    (match
                       (try
                          Some (Printf.sprintf "CoFixpoint %s : %s :=\n%s"
                                  (Names.Label.to_string (Names.Constant.label cst))
                                  (Pp.string_of_ppcmds
                                     (Printer.pr_constr_env env sigma cb.Declarations.const_type))
                                  (Pp.string_of_ppcmds (Printer.pr_constr_env env sigma c)))
                        with e ->
                          Printf.eprintf "rocq2lean: cofixpoint_sources: could not PRINT \
%s -- its stub will carry no comment showing what its body was: %s\n%!"
                            (Names.Constant.to_string cst) (Printexc.to_string e);
                          None)
                     with
                     | None -> ()
                     | Some txt ->
                       if not !firstcf then Buffer.add_char buf ',';
                       firstcf := false;
                       Buffer.add_string buf
                         (Printf.sprintf "[\"%s\",\"%s\"]"
                            (esc (Names.Constant.to_string cst)) (esc txt)))
                  | _ -> ()) env ()
            with e ->
              Printf.eprintf "rocq2lean: cofixpoint_sources key FAILED -- every \
CoFixpoint stub in this file will carry no comment showing what its body was: %s\n%!"
                (Printexc.to_string e));
           (* rocq2lean: constants/inductives in DECLARATION ORDER (see
              `Global.r2l_structure_order`). Every other key walks
              `Environ.fold_constants`, which yields the environment's map order, not
              source order -- so the consumer had no way to place a declaration that has
              no source AST (an `Include`d inductive, an auto-generated scheme) BEFORE
              its users. The walk is rooted at this unit's own modpath, so unlike
              `resolved_types` it needs no prefix filter to keep a `Require`d unit out. *)
           (* Row shape: ["const"|"ind", <kername>, <block index>, <block kername>].
              The last two are meaningful only for `"ind"`: a MUTUAL inductive block
              contributes ONE ROW PER MEMBER, all sharing `<block kername>` and
              distinguished by `<block index>`, so the consumer can regroup them into
              a single Lean `mutual … end`. A `"const"` row carries `0, ""`. *)
           Buffer.add_string buf "],\"declaration_order\":[";
           (try
              let firstd = ref true in
              List.iter (fun (kind, name, bidx, bname) ->
                if not !firstd then Buffer.add_char buf ',';
                firstd := false;
                Buffer.add_string buf
                  (Printf.sprintf "[\"%s\",\"%s\",%d,\"%s\"]"
                     (esc kind) (esc name) bidx (esc bname)))
                (Global.r2l_structure_order ())
            with e ->
              Printf.eprintf "rocq2lean: declaration_order key FAILED: %s\n"
                (Printexc.to_string e));
           (* rocq2lean: the RAW .v SOURCE TEXT for every top-level declaration this
              file's vernac loop recognised (`Vernac.r2l_note_vernac`), spanning from
              the declaring keyword through a `Qed`/`Defined`/`Admitted` when there is
              one -- the tactic PROOF exists nowhere else once compiled: a
              `Qed`-opaque theorem has no kernel body to print, unlike
              `coinductive_sources`/`cofixpoint_sources` above (which print the
              ENVIRONMENT, not source text, and only for those two decl shapes).
              Row shape: `[name, source]`; `name` is the SHORT (unqualified)
              identifier the vernac declared, matched the same way the consumer
              already matches `coinductive_sources`/`cofixpoint_sources` by short
              name -- positionally/in file order, so a repeated short name (two
              `Section`s each defining `foo`) still pairs up in encounter order
              rather than colliding. *)
           Buffer.add_string buf "],\"declaration_sources\":[";
           (try
              let spans = Vernac.r2l_take_decl_spans () in
              if spans <> [] then begin
                let ic = open_in_bin long_f_dot_in in
                let len = in_channel_length ic in
                let src = really_input_string ic len in
                close_in ic;
                let firsts = ref true in
                List.iter (fun (name, bp, ep) ->
                  if bp >= 0 && ep <= len && bp <= ep then begin
                    if not !firsts then Buffer.add_char buf ',';
                    firsts := false;
                    Buffer.add_string buf
                      (Printf.sprintf "[\"%s\",\"%s\"]"
                         (esc name) (esc (String.sub src bp (ep - bp))))
                  end else
                    Printf.eprintf "rocq2lean: declaration_sources: span for %s out \
of range (bp=%d ep=%d len=%d) -- skipped\n%!" name bp ep len)
                  spans
              end
            with e ->
              Printf.eprintf "rocq2lean: declaration_sources key FAILED -- every \
declaration in this file will carry no ORIGINAL-SOURCE comment: %s\n%!"
                (Printexc.to_string e));
           Buffer.add_string buf "]}";
           (* rocq2lean: explicit-cumulativity counters (R2L_TRACE_LIFT). *)
           if Option.has_some (Sys.getenv_opt "R2L_TRACE_LIFT") then
             Printf.eprintf "[R2L-LIFT] %s: lifts=%d ups=%d downs=%d scruts=%d apps=%d projs=%d retype_fail=%d\n%!"
               meta_file !r2l_lifts !r2l_ups !r2l_downs !r2l_scruts !r2l_apps !r2l_projs !r2l_fails;
           let oc = open_out meta_file in
           output_string oc (Buffer.contents buf); close_out oc
         (* rocq2lean: LOUD. This is the outermost guard over the whole sidecar,
            including the write itself — a swallowed failure here means NO
            `.r2lmeta.json` at all, and the consumer's only symptom is a file that
            translates to nothing. Never make it silent. *)
         with e ->
           Printf.eprintf "rocq2lean: METADATA SIDECAR ABORTED for %s: %s\n%!"
             (safe_chop_extension long_f_dot_out ^ ".r2lmeta.json")
             (Printexc.to_string e));
      Aux_file.record_in_aux_at "vo_compile_time"
        (Printf.sprintf "%.3f" (wall_clock2 -. wall_clock1));
      Aux_file.stop_aux_file ();
      (* Additionally, dump an empty .vos file to make sure that
        stale ones are never loaded *)
      if mode = BuildVo then
        dump_empty_vos();
      (* In both .vo, and .vok production mode, dump an empty .vok file to
         indicate that proofs are ok. *)
      dump_empty_vok();
      Dumpglob.end_dump_glob ()

  | BuildVos ->
      let doc, sid = Topfmt.(in_phase ~phase:LoadingPrelude)
          Stm.new_doc
          Stm.{ doc_type = VosDoc long_f_dot_out; injections;
              } in

      let state = { doc; sid; proof = None; time = Option.map Vernac.make_time_output opts.config.time } in
      let state = Load.load_init_vernaculars opts ~state in
      let ldir = Stm.get_ldir ~doc:state.doc in
      let source = source ldir long_f_dot_in in
      let state = Vernac.load_vernac ~echo ~check:false ~source ~state long_f_dot_in in
      let state = Stm.finish ~doc:state.doc in
      ensure_no_pending_proofs state ~filename:long_f_dot_in;
      let () = Stm.snapshot_vos ~doc ~output_native_objects ldir long_f_dot_out in
      Stm.reset_task_queue ();
      ()

let compile opts stm_opts copts injections ~echo ~f_in ~f_out =
  ignore(CoqworkmgrApi.get 1);
  compile opts stm_opts injections copts ~echo ~f_in ~f_out;
  CoqworkmgrApi.giveback 1

let compile_file opts stm_opts copts injections (f_in, echo) =
  let f_out = copts.compilation_output_name in
  if !Flags.beautify then
    Flags.with_option Flags.beautify_file
      (fun f_in -> compile opts stm_opts copts injections ~echo ~f_in ~f_out) f_in
  else
    compile opts stm_opts copts injections ~echo ~f_in ~f_out

let compile_file opts stm_opts copts injections =
  Option.iter (compile_file opts stm_opts copts injections) copts.compile_file
