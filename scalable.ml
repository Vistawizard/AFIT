(** A naive implementation of big integers

This module aims at creating a set of big integers naively. Such data
types will be subsequently called bitarrays. A bitarray is a list of
zeros and ones ; first integer representing the sign bit. In this
contexte zero is reprensented by the empty list []. The list is to
be read from left to right ; this is the opposite convention to the
one you usually write binary decompositions with. After the sign bit
the first encountered bit is the coefficient in front of two to
the power zero. This convention has been chosen to ease writing
down code.

 *)
(** Creates a bitarray from a built-in integer.
    @param x built-in integer.
*)

let _power x n =
    if n = 0 then 1
    else
    let rec aux x n = match n with
        0 -> 1
        |n -> if n = 1 then x
                else
                if n mod 2 = 0 then aux (x * x) (n / 2)
                else
                    x * aux (x * x) (n / 2)
    in
    aux x n;;

let from_int x =
    let s = abs(x) in
    let rec aux x res = match x with
        0 -> res
        |e -> let res = (e mod 2) :: res in aux (e/2) res
    in
    if x > 0 then 0::aux s []
    else
    if x < 0 then 1::aux s []
    else [];;

(** Transforms bitarray of built-in size to built-in integer.
    UNSAFE: possible integer overflow.
    @param bA bitarray object.
 *)
let to_int bA = 
    let rec aux bA n = match bA with
        [] -> 0
        |i::e::bA when n = 0 -> if i = 0 then e + aux bA 1
        else
            (-e) + (-1) * (aux bA 1)
        |i::bA -> i * (_power 2 n) + aux bA (n+1)
    in
    aux bA 0 ;;

(** Prints bitarray as binary number on standard output.
    @param bA a bitarray.
  *)
let print_b bA = 
    let rec aux bA s = match bA with
    [] -> ""
    |e::bA when s = 0 -> if e = 0 then "$" ^ aux bA (s+1)
        else
        aux bA (s+1)
    |e::bA -> aux bA (s+1)^string_of_int(e)
    in
    print_string(aux bA 0);;

(** Toplevel directive to use print_b as bitarray printer.
    CAREFUL: print_b is then list int printer.
    UNCOMMENT FOR TOPLEVEL USE.
*)
(* #install_printer print_b *)

(** Internal comparisons on bitarrays and naturals. Naturals in this
    context are understood as bitarrays missing a bit sign and thus
    assumed to be non-negative.
*)

(** Comparing naturals. Output is 1 if first argument is bigger than
    second -1 otherwise.
    @param nA A natural, a bitarray having no sign bit.
        Assumed non-negative.
    @param nB A natural.
 *)
let rec compare_n nA nB = 
    if List.length nA < List.length nB then (-1)
    else
    if List.length nA > List.length nB then 1
    else
    let rec aux nA nB = match (nA,nB) with
        (e1::nA,e2::nB) -> if  e1 = e2 then aux nA nB
        else
        if e1 > e2 then 1
        else
        (-1)
        |_ -> 0
    in
    aux nA nB;;

(** Bigger inorder comparison operator on naturals. Returns true if
    first argument is bigger than second and false otherwise.
    @param nA natural.
    @param nB natural.
 *)
let (>>!) nA nB = if compare_n nA nB = 1 then true else false;;

(** Smaller inorder comparison operator on naturals. Returns true if
    first argument is smaller than second and false otherwise.
    @param nA natural.
    @param nB natural.
 *)
let (<<!) nA nB = if compare_n nA nB = (-1) then true else false;;

(** Bigger or equal inorder comparison operator on naturals. Returns
    true if first argument is bigger or equal to second and false
    otherwise.
    @param nA natural.
    @param nB natural.
 *)
let (>=!) nA nB = if compare_n nA nB = (-1) then false else true;;

(** Smaller or equal inorder comparison operator on naturals. Returns
    true if first argument is smaller or equal to second and false
    otherwise.
    @param nA natural.
    @param nB natural.
 *)
let (<=!) nA nB = if compare_n nA nB = 1 then false else true;;

(** Comparing two bitarrays. Output is 1 if first argument is bigger
    than second -1 otherwise.
    @param bA A bitarray.
    @param bB A bitarray.
*)
let compare_b bA bB = match (bA,bB) with
    ([],[])-> 0
    |(e::l,[]) -> if e = 1 then (-1) else 1
    |([],e::l) -> if e = 0 then (-1) else 1
    |(e::l),(e1::l1) -> if e = e1 then
        match e with
        |0 -> compare_n l l1
        |_-> (compare_n l l1)* (-1)
    else
    if e < e1 then 1
    else
        (-1);;

(** Bigger inorder comparison operator on bitarrays. Returns true if
    first argument is bigger than second and false otherwise.
    @param nA natural.
    @param nB natural.
 *)
let (>>) bA bB = match compare_b bA bB with
    1 -> true
    |_ -> false ;;

(** Smaller inorder comparison operator on bitarrays. Returns true if
    first argument is smaller than second and false otherwise.
    @param nA natural.
    @param nB natural.
 *)
let (<<) bA bB = match compare_b bA bB with
    (-1) -> true
    |_ -> false ;;

(** Bigger or equal inorder comparison operator on bitarrays. Returns
    true if first argument is bigger or equal to second and false
    otherwise.
    @param nA natural.
    @param nB natural.
 *)
let (>>=) bA bB = match compare_n bA bB with
    0|1 -> true
    |_ -> false ;;

(** Smaller or equal inorder comparison operator on naturals. Returns
    true if first argument is smaller or equal to second and false
    otherwise.
    @param nA natural.
    @param nB natural.
 *)
let (<<=) bA bB = match compare_n bA bB with
    1 -> false
    |_ -> true;;


(** Sign of a bitarray.
    @param bA Bitarray.
*)
let sign_b = function
    [] -> 1
    |e::l -> if e = 0 then 1 else -1;;

(** Absolute value of bitarray.
    @param bA Bitarray.
*)
let abs_b = function
    [] -> []
    |e::l -> 0::l

(** Quotient of integers smaller than 4 by 2.
    @param a Built-in integer smaller than 4.
*)
let _quot_t a = if a < 2 then 0 else 1

(** Modulo of integer smaller than 4 by 2.
    @param a Built-in integer smaller than 4.
*)
let _mod_t a = if a = 1 || a = 3 then 1 else 0

(** Division of integer smaller than 4 by 2.
    @param a Built-in integer smaller than 4.
*)
let _div_t a = (_quot_t a, _mod_t a)

(** Addition of two naturals.
    @param nA Natural.
    @param nB Natural.
*)
let add_n nA nB = 
    let rec aux nA nB res = match (nA,nB) with
        ([],[])  -> if res = 1 then [1] else []
    |([],e::l) -> if e + res > 1 then 0::(aux [] l 1) else (res + e)::l
    |(e::l,[]) -> if e + res > 1 then 0::(aux l [] 1) else (res + e)::l
    |(e::l,e1::l1) when e + e1 + res <= 1 -> e + e1 + res::(aux l l1 0)
    |(e::l,e1::l1) when e + e1 + res > 1 -> if e1 + e + res = 2 then 0::(aux l l1 1)
        else
        1::(aux l l1 1)
    |(_,_)-> []
    in
    aux  nA nB 0;;

(** Difference of two naturals.
    UNSAFE: First entry is assumed to be bigger than second.
    @param nA Natural.
    @param nB Natural.
*)
let rev li =
    let rec rv ac = function
        [] -> ac
        |e::l -> rv (e::ac) l
    in
    rv [] li ;;

let cristal li =
    let rec clear li = match li with
        []-> []
        |e::l-> if e = 0 then clear li
                else
                    e::l
    in rev (clear(rev li));;

let diff_n nA nB = 
    let rec aux nA nB q = match (nA,nB) with
        ([],[]) -> []
        | ([],e2::l2) -> invalid_arg "nB cannot be greater than nA"
        | (e::l,[]) when  e-q >= 0 -> (e-q)::aux l nB  0
        | (e::l,[]) when q = 1-> (2-q)::aux l nB  1
        | (e::l,[]) -> 1::aux l nB  0
        | (e::l,e2::l2) when e-e2-q = (-2) -> 0 :: aux l l2  1
        | (e::l,e2::l2) when e-e2-q = (-1) -> 1 :: aux l l2  1
        | (e::l,e2::l2) when e-e2-q = (0) -> 0 :: aux l l2  0
        | (e::l,e2::l2) when e-e2-q = (1) -> 1 :: aux l l2  0
        |(_,_)->[]
    in
        cristal(aux nA nB 0);;

(** Addition of two bitarrays.
    @param bA Bitarray.
    @param bB Bitarray.
 *)
let add_b bA bB = match (bA,bB) with
    |(bA,[])-> bA
    |([],bB)-> bB
    |(s::t,s1::t1) when sign_b bA = (-1) && sign_b bB = (-1) -> 1::add_n t t1
    |(s::t,s1::t1) when sign_b bA =  1  && sign_b bB =  1  -> 0::add_n t t1
    |(s::t,s1::t1) when sign_b bA = (-1) && sign_b bB = 1 && compare_n t t1 = 1 ->  1::diff_n t t1
    |(s::t,s1::t1) when sign_b bA = (-1) && sign_b bB = 1 && compare_n t t1 = (-1) -> 0::diff_n t1 t
    |(s::t,s1::t1) when compare_n t t1 = 1 -> 0::diff_n t t1
    |(s::t,s1::t1) when compare_n t t1 = (-1)-> 1::diff_n  t1 t
    |(s::t,s1::t1)-> [] ;;

(** Difference of two bitarrays.
    @param bA Bitarray.
    @param bB Bitarray.
*)
let diff_b bA bB = []

(** Shifts bitarray to the left by a given natural number.
    @param bA Bitarray.
    @param d Non-negative integer.
*)
let rec shift bA d = match (bA,d) with
    (l,0) -> l
    |([],d) -> []
    |(e::l,d) -> shift(e::0::l) (d-1 );;

(** Multiplication of two bitarrays.
    @param bA Bitarray.
    @param bB Bitarray.
*)
let mult_b bA bB = 
    let rec aux bA bB n = match (bA,bB) with
    |([],[]) -> []
    |(e::l,[])|([],e::l)-> []
    |(l,e1::l1) -> if e1=0 then aux l l1 (n+1)
        else
        add_b (shift l n) (aux l l1 (n+1))
    in
    match (bA,bB) with
    |(e::l,[])|([],e::l)-> []
    |(e::l,e1::l1) when sign_b bA = sign_b bB -> aux (0::l) (l1) 0
    |(e::l,e1::l1) -> aux (1::l) (l1) 0
    |([],[])->[] ;;

(** Quotient of two bitarrays.
    @param bA Bitarray you want to divide by second argument.
    @param bB Bitarray you divide by. Non-zero!
*)
let quot_n nA nB =
    let rec aux nA nB i = if compare_n nA nB = (-1) then i 
    else
        aux (diff_n nA nB) nB (add_n i [1])
    in
    aux nA nB [];;

let quot_b bA bB = match (bA,bB) with
    |(e1::bA,e2::bB) when e1 = e2 -> if compare_n bA bB = (-1) then []
        else
        0::(quot_n (bA) (bB))
    |(e1::bA,e2::bB) -> if mult_b (quot_n bA bB) bB = bA then 1::(quot_n (bA) (bB))
        else
        1::(add_n (quot_n bA bB) [1])
    |_ -> [];;

(** Modulo of a bitarray against a positive one.
    @param bA Bitarray the modulo of which you're computing.
    @param bB Bitarray which is modular base.
 *)
let mod_b bA bB = diff_b bA (mult_b bB (quot_b bA bB));;

(** Integer division of two bitarrays.
    @param bA Bitarray you want to divide.
    @param bB Bitarray you wnat to divide by.
*)
let div_b bA bB = ([], [])
