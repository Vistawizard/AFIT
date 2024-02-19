(** Factoring Builtin int primes *)

open Builtin
open Basic_arithmetics

(** Factors product of two primes.
    @param key is public key of an RSA cryptosystem.
 *)
let break key = let (n,p) = key in
		let rec broken e =
		  if e>n then (0,0)
		  else if n mod e =0 then (e,n/e)
		  else broken (e+1)
		in broken 2;
