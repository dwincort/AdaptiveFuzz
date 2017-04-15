(* file name: composedp.ml
   created by: Daniel Winograd-Cort
   Created: 3/2/2016
   
   Description:
   This file contains implementations of the differential privacy 
   composition theorems as well as an algorithm that attempts to 
   determine the best way to compose a sequence of (delta, epsilon) 
   pairs.
*)

open Types

let pi = 4. *. atan 1.

(*  A filterFun represents a composition theorem/privacy filter.  It is a 
    function that takes a global ed budget and a list of ed values, and it
    returns None if the budget is not satisfied, or Some estimate where
    estimate is an estimate of the remaining budget. *)

type filterFun = ed -> ed list -> ed option

(* Simple composition just adds up the delta and epsilon values. *)
let simpleFilter : filterFun = fun (eg,dg) edlst ->
  let (esum,dsum) = List.fold_left (fun (e1,d1) (e2,d2) -> (e1 +. e2, d1 +. d2)) (0.0,0.0) edlst
  in if esum <= eg && dsum <= dg then Some (eg -. esum, dg -. dsum) else None

(* Advanced adaptive privacy filter as described in:
"Privacy Odometers and Filters: Pay-as-you-Go Composition"
by Ryan Rogers, Aaron Roth, Jonathan Ullman, Salil Vadhan.
URL: http://arxiv.org/abs/1605.08294v2
*)
let advancedFilter : filterFun = fun (eg,dg) lst ->
  let sum = List.fold_left (+.) 0.0                             in
  let sumD = sum (List.map snd lst)                             in
  let sumEsquared = sum (List.map (fun (e,_) -> e *. e) lst)    in
  let weirdConst = 28.04 *. log (2.0 /. dg)                     in
  let firstpart = sum (List.map (fun (e,_) -> e *. (exp e -. 1.0) /. 2.0) lst)      in
  let apart = sumEsquared +. (eg *. eg /. weirdConst)           in
  let bpart = 1.0 +. 0.5 *. log (weirdConst *. sumEsquared /. (eg *. eg) +. 1.0)    in
  let secondpart = sqrt (2.0 *. apart *. bpart *. log (2.0 /. dg))                  in
  let k = firstpart +. secondpart               in
  if k <= eg && sumD <= dg /. 2.0 && dg <= exp (-1.0) then Some (eg -. k, 0.0) else None

(* Tries both the simple and advanced filter and returns the one with the
   best estimate. *)
let simpleOrAdvancedFilter : filterFun = fun budget edlst ->
  match advancedFilter budget edlst, simpleFilter budget edlst with
    | (Some (e1,d1) as ed1), (Some (e2,d2) as ed2) -> if e1 > e2 then ed1 else ed2
(*    (Support.Error.message 0 Support.Options.Interpreter Support.FileInfo.dummyinfo "Using 1" ; ed1)
    else (Support.Error.message 0 Support.Options.Interpreter Support.FileInfo.dummyinfo "Using 2: %f, %f" e1 e2 ; ed2)*)
    | ed, None -> ed
    | None, ed -> ed
