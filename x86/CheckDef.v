(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Oct 16, 2019 *)
(* *******************  *)

(** * Check if the definition is a local or global one *)

Require Import Coqlib Integers AST Maps.


(** Local definitions include string literals and built-in functions *)

Parameter is_def_builtin: ident -> bool.

Parameter is_def_string_literal: ident -> bool.

Parameter is_def_static: ident -> bool.

Parameter is_def_float_literal : ident -> bool.

Definition is_def_local id :=
  is_def_static id || 
  is_def_string_literal id ||
  is_def_float_literal id.
