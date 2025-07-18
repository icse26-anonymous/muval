open Core
open Common.Util

type mode =
  | PDR
  | StratSynth of {
      pcsp_solver : PCSPSolver.Config.t ext_file;
      determinize : bool;
    }
[@@deriving yojson]

type t = { mode : mode; verbose : bool } [@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg =
  let open Or_error in
  match cfg.mode with
  | PDR -> Ok cfg
  | StratSynth ss_cfg ->
      PCSPSolver.Config.load_ext_file ss_cfg.pcsp_solver >>= fun pcsp_solver ->
      Ok { cfg with mode = StratSynth { ss_cfg with pcsp_solver } }

let load_ext_file = function
  | ExtFile.Instance x -> Ok (ExtFile.Instance x)
  | Filename filename -> (
      let open Or_error in
      try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
      match of_yojson raw_json with
      | Ok x -> instantiate_ext_files x >>= fun x -> Ok (ExtFile.Instance x)
      | Error msg ->
          error_string
          @@ sprintf "Invalid PQSat Configuration (%s): %s" filename msg)
