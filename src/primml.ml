(* file name: primml.ml
   created by: Daniel Winograd-Cort
   Last modified: 12/20/2015
   
   Description:
   This file contains code for interpreting SFuzz primitives as if they were direct ocaml functions.
*)


type ('a,'b) either = | Left of 'a
                      | Right of 'b


type any = Any : 'a -> any
type curatorMemory = ((float * float * string * (any option)) option) list

let curatormem = ref ([] : curatorMemory)

let hd lst = match lst with
  | x::_ -> x
  | [] -> failwith "hd error"

let rec updateNth (lst : 'a list) (index : int) (f : 'a -> 'a) : 'a list =
  match lst, index with
  | [],_ -> []
  | x::xs, 0 -> f x :: xs
  | x::xs, n -> x :: updateNth xs (n-1) f

let gen_numnumopt o = match o with
  | None   -> Printf.printf "%s" "None;"
  | Some (d1,d2) -> Printf.printf "Some(%F,%F);" d1 d2
let gen_cmem lst = Printf.printf "%s" "::: "; List.iter gen_numnumopt lst

(* Returns a file as a list of strings in reverse *)
let fileLines (maxLines : int) (filename : string) = 
  let lines = ref [] in
  let chan = open_in filename in
  try
    for i=1 to maxLines; do
      lines := input_line chan :: !lines
    done;
    close_in chan;
    !lines
  with End_of_file ->
    close_in chan;
    !lines

let stringToFloat (s : string) : float = 
  try
    float_of_string s
  with Failure _ ->
    Printf.eprintf "primml.ml: float_of_string failed to parse: %s.  Providing 0 instead.\n" s;
    0.

(* &-pair destruction *)
let _fst (x,y) = x
let _snd (x,y) = y

(* Logical Operators *)

let _lor = (||)
let _land = (&&)
let _eq = (=)

(* Numerical Comparison Operators *)
let _lt = ( < )
let _gt = ( > )
let _lte = ( <= )
let _gte = ( >= )

(* Numerical Computation Operators *)
let _add = ( +. )
let _sub = ( -. )
let _mul = ( *. )
let _div = ( /. )

let div2 = (fun n -> n /. 2.0)
let div3 = (fun n -> n /. 3.0)
let _exp = ( exp )
let _abs = ( abs_float )
let cswp = (fun (x,y) -> if x < y then (x,y) else (y,x))

(* Integer primitives *)
let _iadd = ( + )
let _isub = ( - )
let _imul = ( * )
let _idiv = ( / )
let rec intToPeano n = if n <= 0.0 then Obj.magic (Left ()) else Obj.magic (Right (intToPeano (n -. 1.0)))
let rec peanoToInt x = match Obj.magic x with
        | Left () -> 0.
        | Right y -> 1. +. peanoToInt y

(* clip creation *)
let clip c = if c > 1.0 then 1.0 else if c < 0.0 then 0.0 else c
let fromClip c = c

(* String operations *)
let string_cc = (^)

(* Show functions *)
let showNum = fun n -> if n = floor n then string_of_int (truncate n) else string_of_float n
let showInt = string_of_int
let showBag (b : 'a list) (showA : 'a -> string) : string = String.concat "," (List.rev (List.rev_map showA b))
let showVec (v : 'a array) (showA : 'a -> string) : string = "[" ^ (Array.fold_right (fun x -> fun xs -> showA x ^ "," ^ xs) v "]")

(* Vector and list transform
   "List" represents the fuzz list, which is a magic'd tuple
   "InternalList" represents ocaml list
   "Vector" represents ocaml array *)
let rec listToInternalList lst = match Obj.magic lst with
        | Left () -> []
        | Right (x,lst') -> x::(listToInternalList lst')
let rec internalListToList v = match v with
        | [] -> Obj.magic (Left ())
        | x::xs -> Obj.magic (Right (x, internalListToList xs))
let listToVector lst = Array.of_list (listToInternalList lst)
let vectorToList v = internalListToList (Array.to_list v)

(* Testing Utilities *)
let _assert  _ = failwith "assert not available in Red Zone"
let assertEq _ = failwith "assertEq not available in Red Zone"
let print    s = (*failwith "print not available in Red Zone"*)  Printf.eprintf "%s\n" s 

(* Probability monad operations *)
let _return (x : 'a) : unit -> 'a = fun _ -> x
let loadDB _ = failwith "loadDB not available in Red Zone"

(* Red zone activation primitives *)
let tyCheckFuzz _ = failwith "tyCheckFuzz not available in Red Zone"
let runRedZone  _ = failwith "runRedZone not available in Red Zone"

let getDelta   _ = failwith "getDelta not available in Red Zone"
let getEpsilon _ = failwith "getEpsilon not available in Red Zone"

(* Bag primitives *)
let emptybag = []
let addtobag x b = x::b
let bagjoin = List.append
let bagsize l = float_of_int (List.length l)

let bagmap f b = List.rev (List.rev_map f b)

let bagsum = List.fold_left (+.) 0.0
let bagsumL b = 
    let rec sumUp xs ys = match xs,ys with
            | x::xs,y::ys -> (x +. y)::sumUp xs ys
            | xs,[] -> xs
            | [],ys -> ys
    in List.fold_left sumUp [] (List.rev_map listToInternalList b)
let bagsumV n b = 
    let res = Array.make (truncate n) 0.0 in
    let sumUp = Array.iteri (fun i -> fun x -> Array.set res i (x +. res.(i)))
    in List.iter sumUp b; res

let bagsplit f b = List.partition

(* Differential Privacy mechanisms *)
let addNoiseP (eps : float) (n : float) : float = n +. Math.lap (1.0 /. eps)
let addNoise (eps : float) (n : float) : unit -> float = fun () -> addNoiseP eps n

let reportNoisyMaxP (eps : float) (k : float) (quality : 'r -> 'db -> float) (rbag : 'r list) (db : 'db) : 'r =
  let problist = List.rev_map (fun r -> (r, quality r db +. Math.lap (k /. eps))) rbag in
(*    Printf.eprintf
      "--- reportNoisyMax: Probabilities are: %s" (String.concat ",\n" (List.map (fun x -> "("^string_of_float (Obj.magic (fst x))^","^string_of_float (snd x)^")") problist));*)
  fst (List.fold_left 
        (fun best r -> if abs_float (snd r) > abs_float (snd best) then r else best)
        (hd rbag, 0.0) problist)
let reportNoisyMax (eps : float) (k : float) (quality : 'r -> 'db -> float) (rbag : 'r list) (db : 'db) : unit -> 'r =
    fun () -> reportNoisyMaxP eps k quality rbag db

let expMechP (eps : float) (k : float) (quality : 'r -> 'db -> float) (rbag : 'r list) (db : 'db) : 'r =
  let reslist = List.rev_map (fun r -> (r, exp (eps *. (quality r db) /. (2.0 *. k)))) rbag in
  let total = List.fold_left (+.) 0.0 (List.map snd reslist) in
  let rec sampleLst (p : float) (lst : ('a * float) list) : 'a =
    match lst with
    | [] -> fst (hd lst) (* Guaranteed to fail! What else can we do? *)
    | (a,x)::xs -> if p < x then a else sampleLst (p -. x) xs
  in sampleLst (Math.randFloat total) (List.sort (fun a b -> truncate (snd b -. snd a)) reslist)
let expMech (eps : float) (k : float) (quality : 'r -> 'db -> float) (rbag : 'r list) (db : 'db) : unit -> 'r = 
    fun () -> expMechP eps k quality rbag db

let aboveThresholdP (eps : float) (k : float) (t : float) (db : 'db) : int = 
  let index = List.length (!curatormem) in
  let dbfilename = "database"^string_of_int index^".cmem" in
  let oc = open_out dbfilename in
  Marshal.to_channel oc db [];
  close_out oc;
  curatormem := List.append !curatormem [Some (t +. Math.lap (2.0 /. (eps *. k)), eps, dbfilename, Some (Any db))];
  index
let aboveThreshold (eps : float) (k : float) (t : float) (db : 'db) : unit -> int = 
  fun () -> aboveThresholdP eps k t db

let queryAT (token : int) (f : 'db -> float) : bool option =
  let dbopt = begin match List.nth (!curatormem) token with
            | None -> None
            | Some (t,e,_, Some (Any db)) -> Some (t,e,Obj.magic db)
            | Some (t,e,dbfilename, None) ->
                let ic = open_in dbfilename in
                let db = Marshal.from_channel ic in
                close_in ic;
                Some (t,e,db)
  end in Option.map (fun (t,e,db) ->
    if (f db) +. Math.lap (4.0 /. e) >= t then
      (curatormem := updateNth !curatormem token (fun _ -> None); true)
    else false) dbopt

      

(* Load data from external file *)
let bagFromFile     _ = failwith "bagFromFile not available in Red Zone"
let listFromFile    _ = failwith "listFromFile not available in Red Zone"
let listbagFromFile _ = failwith "listbagFromFile not available in Red Zone"
let vectorbagFromFile (maxsize : float) (fn : string) (rexp : string) : (float array) list = 
    let lines = fileLines (truncate maxsize) fn in
    let lineFun line = Array.of_list (List.map stringToFloat (Str.split (Str.regexp rexp) line))
    in List.rev_map lineFun lines

let readCmemFromFile (maxsize : int) (fn : string) : curatorMemory =
    let lines = fileLines maxsize fn in
    let lineFun line = match Str.split (Str.regexp_string ",") line with
          | t::e::fn::[] -> Some (float_of_string t, float_of_string e, fn, None)
          | _ -> None (* FIXME This probably shouldn't be a silent error *)
    in List.map lineFun lines

let rec print_cmem oc = function 
  | [] -> ()
  | None::tl -> Printf.fprintf oc "None\n"; print_cmem oc tl
  | (Some(t,e,fn,_))::tl -> Printf.fprintf oc "%F,%F,%s\n" t e fn; print_cmem oc tl

let writeCmemToFile (fn : string) (cmem : curatorMemory) : unit =
    let oc = open_out fn in
    print_cmem oc cmem;
    close_out oc

(* Vectors *)
let vsize v = float_of_int (Array.length v)
let vmap = Array.map
let vsum = Array.fold_left (+.) 0.0
let vcons (x : 'a) (xs : 'a array) : 'a array = Array.of_list (x::(Array.to_list xs))
let vuncons (v : 'a array) : (unit, 'a * 'a array) either = 
  match Array.to_list v with
    | [] -> Left ()
    | x::xs -> Right (x, Array.of_list xs)

let vindex (def : 'a) (i : float) (v : 'a array) : 'a = 
  try
    Array.get v (truncate i)
  with Invalid_argument s -> def

let vperformAt (i : float) (f : 'a -> 'b) (v : 'a array) : 'b array = 
  let res = Array.copy v  in
  try
    let i = truncate i      in
    Array.set res i (f v.(i)); res
  with Invalid_argument s -> res

let vfilter (test : 'a -> bool) (f : 'a -> 'b) (v : 'a array) : 'b array =
  let rec lfilter lst = match lst with
    | [] -> []
    | x::xs -> if test x then f x :: lfilter xs else lfilter xs
  in Array.of_list (lfilter (Array.to_list v))

let vzipwith (f : 'a -> 'b -> 'c) (v1 : 'a array) (v2 : 'b array) : 'c array =
  let l = min (Array.length v1) (Array.length v2)
  in Array.init l (fun i -> f v1.(i) v2.(i))
  


let vectorIP  (v1 : float array) (v2 : float array) : float = 
  let res = ref 0.0 in
  try
    Array.iteri (fun i -> fun x -> res := !res +. x +. v2.(i)) v1;
    !res
  with Invalid_argument s -> !res

