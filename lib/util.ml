let rec list_repeat v num =
  if num <= 0 then []
  else v :: list_repeat v (num-1)

(* Similar to last and init from Haskell. TODO: improve efficiency. *)
let list_last l =
  List.hd (List.rev l)
let list_init l =
  List.rev (List.tl (List.rev l))

(** Return a list of integers from lower_bound (include) to upper_bound (exclude).
    For example: list_range 0 4 = [0, 1, 2, 3] *)
let list_range lower_bound upper_bound =
  let rec f remaining last result =
    if remaining <= 0 then result
    else f (remaining - 1) (last - 1) (last - 1 :: result)
  in
  f (upper_bound - lower_bound) upper_bound []

(** Run job 0; job 1; ... job (n-1) *)
let repeat_n job n =
  let rec repeat_from i =
    if i < n then begin
      job i;
      repeat_from (i+1)
    end
  in
  repeat_from 0
