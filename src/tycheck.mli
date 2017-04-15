(* file name: tycheck.mli
   created by: Daniel Winograd-Cort
   Created: 8/24/2016
*)
open Types

module TypeSub : sig
  open Support.FileInfo
  
  val check_type_sub   : info -> ty -> ty -> unit checker
  val find_super_type  : info -> ty -> ty -> ty checker
  val check_type_equal : info -> ty -> ty -> unit checker
  
  val check_fuzz_shape   : info -> ty -> ty checker
  val check_tensor_shape : info -> ty -> (ty * ty) checker
  val check_union_shape  : info -> ty -> (ty * ty) checker
end

val type_of : term -> (ty * si list) checker
val get_type : bool -> term -> ty
val ty_normalize_app : ty -> ty checker
