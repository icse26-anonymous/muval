open Core
open Common.Util

type br_choice =
  | Default
  (* implented *)
  | FFP
  (* implented *)
  | MOMS
  (* half implented *)
  | VSIDS of int
(* implented *) [@@deriving yojson]

type t = { dim_reduction : bool; verbose : bool; br_choice : br_choice }
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg = Ok cfg

let load_ext_file = function
  | ExtFile.Instance x -> Ok (ExtFile.Instance x)
  | Filename filename -> (
      let open Or_error in
      try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
      match of_yojson raw_json with
      | Ok x -> instantiate_ext_files x >>= fun x -> Ok (ExtFile.Instance x)
      | Error msg ->
          error_string
          @@ sprintf "Invalid ZundaSat Configuration (%s): %s" filename msg)
