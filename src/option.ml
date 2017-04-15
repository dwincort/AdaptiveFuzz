(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)

(* Very simple utility functions *)
let map f = function
        | None -> None
        | Some v -> Some (f v)

let default d = function
  | None   -> d
  | Some v -> v

let map_default f d = function
  | None   -> d
  | Some v -> f v

let is_some = function
  | None   -> false
  | Some _ -> true

let obind o f = match o with
  | None -> None
  | Some x -> f x

let opt_bind_list lst =
  let rec inner l res = match l with
    | [] -> Some (List.rev res)
    | None::_ -> None
    | (Some x)::l' -> inner l' (x::res)
  in inner lst []
