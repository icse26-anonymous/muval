(* from https://github.com/ocaml-multicore/effects-examples/blob/master/pipes.ml *)

(** Deep encoding of pipes.
    The example is adapted from Kammar et al. (2013) **)
    open Effect
    open Effect.Deep
    
    (* We specialise our pipes to work only with integers *)
    type _ Effect.t += Await : int Effect.t
    let await () = perform Await
    
    type _ Effect.t += Yield : int -> unit Effect.t
    let yield s = perform (Yield s)
    
    type prod = Prod of (unit -> (cons -> unit))
    and cons  = Cons of (int -> (prod -> unit))
    
    let flip f = fun y x -> f x y
    
    (* Parameterised handler that takes a consumer as parameter *)
    let up m =
      match_with m () {
        retc = (fun v -> fun _ -> v);
        exnc = raise;
        effc = fun (type a) (e : a Effect.t) ->
          match e with
          | Yield s -> Some (fun (k : (a, _) continuation) ->
            fun (Cons cons) ->
              cons s (Prod (fun () -> continue k ())))
          | _ -> None
      }
    
    (* Refine up to accept the parameter first rather than the computation. It's
       more convenient when combining handlers. *)
    let up = flip up
    
    (* Parameterised handler that takes a producer as parameter *)
    let down m =
      match_with m () {
        retc = (fun v -> fun _ -> v);
        exnc = raise;
        effc = fun (type a) (e : a Effect.t) ->
          match e with
          | Await -> Some (fun (k : (a, _) continuation) ->
            fun (Prod prod) ->
              prod () (Cons (fun s -> continue k s)))
          | _ -> None
      }
    
    let down = flip down
    
    (** Some convenient combinators **)
    let (<+<) d u = fun () -> down (Prod (fun () cons -> up cons u)) d
    let (>+>) d u = u <+< d
    
    
    (** Some producers and consumers **)
    (* Produces an infinite stream of integers starting from [n] *)
    let rec produceFrom : int -> unit -> unit
      = fun n () ->
        yield n;
        produceFrom (n+1) ()
    
    (* Accumulates elements from an integer stream until the sum is
       greater than or equal to [n]. Moreover, it produces a singleton
       integer stream *)
    let sumTo : int -> (unit -> unit) =
      let rec sumTo' acc lim =
        if acc >= lim then
          yield acc
        else
          let x = await () in
          sumTo' (acc+x) lim
      in
      fun n () -> sumTo' 0 n
    
    (* Skips [n] elements of an arbitrary stream *)
    let rec skip : int -> (unit -> unit) =
      fun n () ->
        if n <= 0 then
          ( yield (await ())
          ; skip 0 () )
        else
          ( ignore (await ())
          ; skip (n-1) () )
    
    (* Prints a stream of integers *)
    let rec printer : unit -> unit
      = fun () ->
        Printf.printf "%d\n" (await ());
        printer ()
    
    (* Wiring everything together *)
    let example =
       produceFrom 0
      >+>
       skip 99
      >+>
       sumTo 100
      >+>
       printer
    
    let _ = example ()