(** Power function implementations for builtin integers *)

open Builtin
open Basic_arithmetics

(** Naive power function. Linear complexity
    @param x base
    @param n exponent
 *)
let pow x n = 
let rec pow_rec z nfois =

    if nfois=0 then 1 

    else   z*pow_rec z (nfois-1)
     in  pow_rec x n
;;


(** Fast integer exponentiation function. Logarithmic complexity.
    @param x base
    @param n exponent
 *)
let rec power x n = 
if n = 0 then 1
  else if n=1 then x
  else if n mod 2 = 0 then power (x*x) (quot n 2)
  else x * power (x*x) (quot(n-1) 2);;

(** Fast modular exponentiation function. Logarithmic complexity.
    @param x base
    @param n exponent
    @param m modular base
 *)
let mod_power x n m =
  let rec mod_power_rec x n m =
    let b = if n = 0
            then 1
            else let a = mod_power_rec x (n/2) m
                 in if n mod 2 = 0
                    then (a*a) mod m
                    else (((a*a) mod m ) * x) mod m in
    if x < 0 && n mod 2 = 1
    then b + m
    else b
  in mod_power_rec x n m;;

(** Fast modular exponentiation function mod prime. Logarithmic complexity.
    It makes use of the Little Fermat Theorem.
    @param x base
    @param n exponent
    @param p prime modular base
 *)
let prime_mod_power x n p = if x= 0 then 0
  else mod_power x (modulo n (p-1)) p  ;;