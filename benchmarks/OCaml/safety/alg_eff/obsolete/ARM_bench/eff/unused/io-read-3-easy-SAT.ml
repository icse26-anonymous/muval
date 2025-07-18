type[@boxed] 'a eff =
| Read : int eff

type ('a, 'b) continuation = K
type 'a effect_handler = { effc: 'b. 'b eff -> (('b,'a) continuation -> 'a) option }
type ('a,'b) handler = {
  retc: 'a -> 'b;
  exnc: exn -> 'b;
  effc: 'c.'c eff -> (('c,'b) continuation -> 'b) option
}
external perform : 'a eff -> 'a = "unknown"
external try_with : ('a -> 'b) -> 'a -> 'b effect_handler -> 'b = "unknown"
external match_with : ('a -> 'b) -> 'a -> ('b, 'c) handler -> 'c = "unknown"
external continue : ('a, 'b) continuation -> 'a -> 'b = "unknown"

(* from Andrej Bauer and Matija Pretnar. Programming with algebraic effects and handlers. 2015. *)

type result = Ok | Err

let[@annot_MB "
  int list -> (unit -> ({Read: s} |> result / s3 => s3)) -> result
"] read_from_list lst (body: unit -> result) =
  match_with body () {
    retc = (fun x -> fun _ -> x);
    exnc = raise;
    effc = fun (type a) (e: a eff) -> match e with
      | Read -> Some (fun (k: (a, _) continuation) ->
          function
          | (s :: lst' : int list) -> continue k s lst'
          | [] -> Err
        )
  } lst

let read_1 l =
  read_from_list l (fun () ->
    let _ = perform Read in Ok
  )

[@@@assert "typeof(read_1) <: {z: int list | z = []} -> {z:result | z = Err}"]
