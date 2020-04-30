(* Frama-C journal generated at 22:56 the 30/04/2020 *)

exception Unreachable
exception Exception of string

(* Run the user commands *)
let run () =
  Dynamic.Parameter.String.set "-load" "floyd_triangle_parsed";
  Project.load_all "floyd_triangle_parsed";
  Dynamic.Parameter.Bool.set "-rte" true;
  !Db.RteGen.compute ();
  Project.set_keep_current false;
  Dynamic.Parameter.Bool.set "-wp-rte" true;
  Dynamic.Parameter.Bool.set "-wp-rte" false;
  ()

(* Main *)
let main () =
  Journal.keep_file "./.frama-c/frama_c_journal.ml";
  try run ()
  with
  | Unreachable -> Kernel.fatal "Journal reaches an assumed dead code" 
  | Exception s -> Kernel.log "Journal re-raised the exception %S" s
  | exn ->
    Kernel.fatal
      "Journal raised an unexpected exception: %s"
      (Printexc.to_string exn)

(* Registering *)
let main : unit -> unit =
  Dynamic.register
    ~plugin:"Frama_c_journal.ml"
    "main"
    (Datatype.func Datatype.unit Datatype.unit)
    ~journalize:false
    main

(* Hooking *)
let () = Cmdline.run_after_loading_stage main; Cmdline.is_going_to_load ()
