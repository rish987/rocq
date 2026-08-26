(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type time_output

val make_time_output : Coqargs.time_config -> time_output

(** Parsing of vernacular. *)
module State : sig

  type t = {
    doc : Stm.doc;
    sid : Stateid.t;
    proof : Proof.t option;
    time : time_output option;
  }

end

(** [process_expr sid cmd] Executes vernac command [cmd]. Callers are
    expected to handle and print errors in form of exceptions, however
    care is taken so the state machine is left in a consistent
    state. *)
val process_expr : state:State.t -> Vernacexpr.vernac_control -> State.t

(** [load_vernac echo sid file] Loads [file] on top of [sid], will
    echo the commands if [echo] is set. Callers are expected to handle
    and print errors in form of exceptions. *)
val load_vernac : echo:bool -> check:bool ->
  state:State.t -> ?source:Loc.source -> string -> State.t

(* rocq2lean: per-declaration SOURCE TEXT spans (byte offsets into the .v file
   being compiled), for the `.r2lmeta.json` `declaration_sources` key -- see the
   long comment above `r2l_note_vernac` in vernac.ml. Each entry is
   `(name, bp, ep)`: `name` is the short (unqualified) identifier the vernac
   declares; `bp`/`ep` are BYTE offsets, inclusive of a `Theorem`'s tactic proof
   through its closing `Qed`/`Defined`/`Admitted`. *)
val r2l_reset_decl_spans : unit -> unit
val r2l_take_decl_spans : unit -> (string * int * int) list
