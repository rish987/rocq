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
                let cu = Names.Constant.user c and cc = Names.Constant.canonical c in
                if Names.KerName.equal cu cc
                then jarr [jstr "Constant"; jkername cu; "null"]
                else jarr [jstr "Constant"; jkername cu; jkername cc] in
              let jmutind mi =
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
              let wrap node = "{\"v\":" ^ node ^ ",\"loc\":null}" in
              let rec jg gc = wrap (jnode (DAst.get gc))
              and jnode = function
                | Glob_term.GRef (gr, _) -> jarr [jstr "GRef"; jgref gr; "null"]
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
                | Glob_term.GCases (_, _, tomatch, clauses) ->
                    let jtom (scrut, (na, _)) =
                      jarr [jg scrut; jarr [jname na; "null"]] in
                    let jclause cl =
                      let (ids, pats, body) = cl.CAst.v in
                      "{\"v\":" ^ jarr [ jarr (List.map jid ids);
                                         jarr (List.map jpat pats); jg body ]
                        ^ ",\"loc\":null}" in
                    jarr [jstr "GCases"; jarr [jstr "RegularStyle"]; "null";
                          jarr (List.map jtom tomatch); jarr (List.map jclause clauses)]
                | Glob_term.GIf (c, (na, _), t, e) ->
                    jarr [jstr "GIf"; jg c; jarr [jname na; "null"]; jg t; jg e]
                | Glob_term.GLetTuple (nas, (na, _), sc, b) ->
                    jarr [jstr "GLetTuple"; jarr (List.map jname nas);
                          jarr [jname na; "null"]; jg sc; jg b]
                | Glob_term.GSort _ -> jarr [jstr "GSort"; "null"]
                | Glob_term.GHole _ -> jarr [jstr "GHole"; jarr [jstr "GInternalHole"]]
                | Glob_term.GProj (_, args, c) ->
                    jarr (jstr "GApp" :: jg c :: [jarr (List.map jg args)])
                | Glob_term.GInt _ | Glob_term.GFloat _ | Glob_term.GString _ ->
                    jarr [jstr "GHole"; jarr [jstr "GInternalHole"]]
                | _ -> jarr [jstr "GHole"; jarr [jstr "GInternalHole"]]
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
                         Flags.with_option Flags.raw_print
                           (Detyping.detype Detyping.Now env evd)
                           (EConstr.of_constr body) in
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
                       Flags.with_option Flags.raw_print
                         (Detyping.detype Detyping.Now env evd)
                         (EConstr.of_constr cb.Declarations.const_type) in
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
                 ["<full ind name>", <nparams>, <arityGlob>, [["<ctor>",<ctorTyGlob>],…]]. *)
              Buffer.add_string buf "],\"detyped_inductives\":[";
              let firsti = ref true in
              Environ.fold_inductives (fun mind mib () ->
                if Names.ModPath.equal (Names.MutInd.modpath mind) this_mp then
                  Array.iteri (fun i oib ->
                    (try
                       let univ = UVars.Instance.empty in
                       let ind_ty = Inductive.type_of_inductive ((mib, oib), univ) in
                       let ctor_tys = Inductive.type_of_constructors ((mind, i), univ) (mib, oib) in
                       let ind_name =
                         Names.ModPath.to_string (Names.MutInd.modpath mind) ^ "."
                         ^ Names.Id.to_string oib.Declarations.mind_typename in
                       let dj t = jg (Flags.with_option Flags.raw_print
                                        (Detyping.detype Detyping.Now env evd)
                                        (EConstr.of_constr t)) in
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
                    mib.Declarations.mind_packets) env ()
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
