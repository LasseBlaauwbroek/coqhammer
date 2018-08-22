(* Proofview.tclTIMEOUT is incorrect because of a bug in OCaml
   runtime. This file contains a more correct version, but it may
   still fail to work sometimes. See:

   https://caml.inria.fr/mantis/view.php?id=7709
   https://caml.inria.fr/mantis/view.php?id=4127
   https://github.com/coq/coq/issues/7430
   https://github.com/coq/coq/issues/7408

*)

let my_timeout n f x e =
  let killed = ref false in
  let exited = ref false in
  let watchdog () =
    let rec kill_main_thread () =
      try
        while not !killed do
          exited := true;
          Control.interrupt := true;
          Msg.error "Coq/OCaml bug: timeout failed!";
          Unix.sleep 1
        done
      with Sys.Break ->
        begin
          prerr_endline "OCaml bug: Sys.Break in watchdog";
          kill_main_thread ()
        end
    in
    Unix.sleep (n + 1);
    kill_main_thread ()
  in
  (* This will fail if the main thread loops without executing
     operations which allow switching to the watchdog thread. *)
  let _ = Thread.create watchdog ()
  in
  let timeout_handler _ = raise e in
  let psh = Sys.signal Sys.sigalrm (Sys.Signal_handle timeout_handler) in
  let _ = Unix.alarm n in
  let restore_timeout () =
    let _ = Unix.alarm 0 in
    Sys.set_signal Sys.sigalrm psh
  in
  try
    let res = f x in
    killed := true;
    restore_timeout ();
    res
  with
  | Sys.Break ->
     let () = killed := true in
     restore_timeout ();
     (** Just in case, it could be a regular Ctrl+C *)
     if not !exited then raise Sys.Break
     else raise e
  | e ->
     let () = killed := true in
     let e = Backtrace.add_backtrace e in
     restore_timeout ();
     Exninfo.iraise e

let tclTIMEOUT n t =
  (* Control.set_timeout { Control.timeout = my_timeout }; *) (* comment this line out for Coq 8.8.0 *)
  Proofview.tclTIMEOUT n t
