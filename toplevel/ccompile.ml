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
           let esc s =
             let b = Buffer.create (String.length s + 2) in
             String.iter (fun c -> match c with
               | '"'  -> Buffer.add_string b "\\\""
               | '\\' -> Buffer.add_string b "\\\\"
               | c    -> Buffer.add_char b c) s;
             Buffer.contents b in
           let buf = Buffer.create 256 in
           Buffer.add_string buf "{\"coercions\":[";
           let first = ref true in
           List.iter (fun (loc, gref) ->
             match loc with
             | Some l ->
               let (bp, ep) = Loc.unloc l in
               if not !first then Buffer.add_char buf ',';
               first := false;
               Buffer.add_string buf
                 (Printf.sprintf "[%d,%d,\"%s\"]" bp ep
                    (esc (Pp.string_of_ppcmds (Printer.pr_global gref))))
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
                  if not (Hashtbl.mem seen (bp, ep)) then begin
                    Hashtbl.add seen (bp, ep) ();
                    if not !firstr then Buffer.add_char buf ',';
                    firstr := false;
                    Buffer.add_string buf
                      (Printf.sprintf "[%d,%d,\"%s\"]" bp ep (esc (gref_name gref)))
                  end
                | None -> ()) (Constrintern.take_ref_resolutions ())
            with _ -> ());
           (* rocq2lean: RESOLVED types of SOURCE binders, keyed by source span.
              For an UNTYPED binder (`Definition valid_binary x := …`), Coq infers
              `x : spec_float` during pretyping; recorded by span so the translator
              fills the binder by its OWN loc — no telescope alignment. Source:
              `Constrintern.take_binder_types` (populated in `comDefinition`). *)
           Buffer.add_string buf "],\"binder_types\":[";
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
           (* rocq2lean: per-constant leading-binder telescope NAMES from the
              DISCHARGED `const_type` — the authoritative signal for section-var
              discharge. After `End Section`, `const_type` = ∀ (discharged section
              vars) (source binders), …, so its leading binder names are
              [discharged…] ++ [source…]. The translator computes k = (telescope
              leading) − (source leading) and prepends the first k as EXPLICIT
              binders (types recovered from its tracked section `variable`s BY
              NAME), replacing the fragile theorem-only `@foo` pp elaboration for
              defs/theorems/fixpoints alike. Emitted for EVERY this-file constant;
              non-section constants have k=0 (telescope == source) → no-op. Names
              from the same `decompose_prod`+`binder_name` the implicit_args block
              uses; Anonymous → "_". *)
           Buffer.add_string buf "],\"discharged_telescopes\":[";
           (try
              let env = Global.env () in
              let this_mp = Names.ModPath.MPfile ldir in
              let firstd = ref true in
              Environ.fold_constants (fun c cb () ->
                if Names.ModPath.equal (Names.Constant.modpath c) this_mp then begin
                  let (bnds, _) = Term.decompose_prod cb.Declarations.const_type in
                  (* decompose_prod is innermost-first; reverse to outermost-first *)
                  let names = List.rev_map (fun (annot, _) ->
                    match Context.binder_name annot with
                    | Names.Name id -> Names.Id.to_string id
                    | Names.Anonymous -> "_") bnds in
                  if names <> [] then begin
                    if not !firstd then Buffer.add_char buf ',';
                    firstd := false;
                    let ns = String.concat ","
                      (List.map (fun n -> Printf.sprintf "\"%s\"" (esc n)) names) in
                    Buffer.add_string buf
                      (Printf.sprintf "[\"%s\",[%s]]" (esc (Names.Constant.to_string c)) ns)
                  end
                end) env ()
            with _ -> ());
           Buffer.add_string buf "]}";
           let oc = open_out meta_file in
           output_string oc (Buffer.contents buf); close_out oc
         with _ -> ());
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
