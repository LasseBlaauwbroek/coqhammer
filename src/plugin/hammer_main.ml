open Hammer_errors

open Util
open Names
open Term
open Constr
open Context

open Ltac_plugin

module Utils = Hhutils

(***************************************************************************************)

let mk_id x = Hh_term.Id x
let mk_app x y = Hh_term.Comb(x, y)
let mk_comb (x, y) = mk_app x y

let tuple (l : Hh_term.hhterm list) =
  match l with
  | [] -> failwith "tuple: empty list"
  | [h] -> h
  | h :: t ->
    List.fold_left mk_app h t

let hhterm_of_global glob =
  mk_id (Libnames.string_of_path (Nametab.path_of_global (Globnames.canonical_gr glob)))

let hhterm_of_sort s = match Sorts.family s with
  | InSProp -> mk_id "$Prop"
  | InProp -> mk_id "$Prop"
  | InSet  -> mk_id "$Set"
  | InType -> mk_id "$Type"

let hhterm_of_constant c =
  tuple [mk_id "$Const"; hhterm_of_global (Names.GlobRef.ConstRef c)]

let hhterm_of_inductive i =
  tuple [mk_id "$Ind"; hhterm_of_global (Names.GlobRef.IndRef i);
         mk_id (string_of_int (Inductiveops.inductive_nparams (Global.env()) i))]

let hhterm_of_construct cstr =
  tuple [mk_id "$Construct"; hhterm_of_inductive (fst cstr);
         hhterm_of_global (Names.GlobRef.ConstructRef cstr)]

let hhterm_of_var v =
  tuple [mk_id "$Var"; hhterm_of_global (Names.GlobRef.VarRef v)]

let hhterm_of_intarray a =
  tuple ((mk_id "$IntArray") :: (List.map mk_id (List.map string_of_int (Array.to_list a))))

let hhterm_of_caseinfo ci =
  let {ci_ind = ci_ind; ci_npar = ci_npar; ci_cstr_ndecls = ci_cstr_ndecls;
       ci_cstr_nargs = ci_cstr_nargs; ci_pp_info = ci_pp_info} = ci
  in
  tuple [mk_id "$CaseInfo"; hhterm_of_inductive ci_ind;
         mk_id (string_of_int ci_npar);
         hhterm_of_intarray ci_cstr_ndecls;
         hhterm_of_intarray ci_cstr_nargs]

(* Unsafe *)
let hhterm_of_name name = match name.binder_name with
  | Name.Name id -> tuple [mk_id "$Name"; mk_id (Id.to_string id)]
  | Name.Anonymous  -> tuple [mk_id "$Name"; mk_id "$Anonymous"]

let hhterm_of_namearray a =
  tuple ((mk_id "$NameArray") :: (List.map hhterm_of_name (Array.to_list a)))

let hhterm_of_bool b =
  if b then mk_app (mk_id "$Bool") (mk_id "$True")
  else mk_app (mk_id "$Bool") (mk_id "$False")

let rec hhterm_of (t : Constr.t) : Hh_term.hhterm =
  match Constr.kind t with
  | Rel n -> tuple [mk_id "$Rel"; mk_id (string_of_int n)]
  | Meta n -> raise (HammerError "Metavariables not supported.")
  | Var v -> hhterm_of_var v
  | Sort s -> tuple [mk_id "$Sort"; hhterm_of_sort s]
  | Cast (ty1,ck,ty2) -> tuple [mk_id "$Cast"; hhterm_of ty1; hhterm_of ty2]
  | Prod (na,ty,c)    ->
     tuple [mk_id "$Prod"; hhterm_of_name na; hhterm_of ty; hhterm_of c]
  | Lambda (na,ty,c)  ->
     tuple [mk_id "$Lambda"; hhterm_of_name na; hhterm_of ty; hhterm_of c]
  | LetIn (na,b,ty,c) ->
     tuple [mk_id "$LetIn"; hhterm_of_name na; hhterm_of b; hhterm_of ty; hhterm_of c]
  | App (f,args)      ->
     tuple [mk_id "$App"; hhterm_of f; hhterm_of_constrarray args]
  | Const (c,u)       -> hhterm_of_constant c
  | Proj (p,c)        -> tuple [mk_id "$Proj";
                                hhterm_of_constant (Projection.constant p);
                                hhterm_of_bool (Projection.unfolded p);
                                hhterm_of c]
  | Evar (evk,cl)     -> raise (HammerError "Existential variables not supported.")
  | Ind (ind,u)       -> hhterm_of_inductive ind
  | Construct (ctr,u) -> hhterm_of_construct ctr
  | Case (ci,p,c,bl)  ->
      tuple ([mk_id "$Case"; hhterm_of_caseinfo ci ; hhterm_of p;
        hhterm_of c; hhterm_of_constrarray bl])
  | Fix (nvn,recdef) -> tuple [mk_id "$Fix";
                               hhterm_of_intarray (fst nvn);
                               mk_id (string_of_int (snd nvn));
                               hhterm_of_precdeclaration recdef]
  | CoFix (n,recdef) -> tuple [mk_id "$CoFix";
                               mk_id (string_of_int n);
                               hhterm_of_precdeclaration recdef]
  | Int _            -> raise (HammerError "Primitive integers not supported.")
  | Float _          -> raise (HammerError "Primitive floats not supported.")

and hhterm_of_constrarray a =
  tuple ((mk_id "$ConstrArray") :: List.map hhterm_of (Array.to_list a))
and hhterm_of_precdeclaration (a,b,c) =
  tuple [(mk_id "$PrecDeclaration") ; hhterm_of_namearray a;
         hhterm_of_constrarray b; hhterm_of_constrarray c]

let get_type_of env evmap t =
  EConstr.to_constr evmap (Retyping.get_type_of env evmap (EConstr.of_constr t))

(* only for constants *)
let hhproof_of c =
  begin match Global.body_of_constant Library.indirect_accessor c with
  | Some (b, _, _) -> hhterm_of b
  | None -> mk_id "$Axiom"
  end

let hhdef_of_global env sigma glob_ref : (string * Hh_term.hhdef) =
  let glob_ref = Globnames.canonical_gr glob_ref in
  let ty = fst (Typeops.type_of_global_in_context env glob_ref) in
  let kind = get_type_of env sigma ty in
  let const = match glob_ref with
    | Names.GlobRef.ConstRef c -> hhterm_of_constant c
    | Names.GlobRef.IndRef i   -> hhterm_of_inductive i
    | Names.GlobRef.ConstructRef cstr -> hhterm_of_construct cstr
    | Names.GlobRef.VarRef v -> hhterm_of_var v
  in
  let filename_aux = match glob_ref with
    | Names.GlobRef.ConstRef c -> Constant.to_string c
    | Names.GlobRef.IndRef i   -> MutInd.to_string (fst i)
    | Names.GlobRef.ConstructRef cstr -> MutInd.to_string ((Hhlib.comp fst fst) cstr)
    | Names.GlobRef.VarRef v -> Id.to_string v
  in
  let term = match glob_ref with
    | Names.GlobRef.ConstRef c -> lazy (hhproof_of c)
    | _ -> lazy (mk_id "$Axiom")
  in
  let opaque = match glob_ref with
    | Names.GlobRef.ConstRef c -> Declareops.is_opaque (Global.lookup_constant c)
    | _ -> true
  in
  let filename =
     let l = Str.split (Str.regexp "\\.") filename_aux in
     Filename.dirname (String.concat "/" l)
  in
  (filename, (const, opaque, hhterm_of kind, lazy (hhterm_of ty), term))

let hhdef_of_hyp env sigma (id, maybe_body, ty) =
  let kind = get_type_of env sigma ty in
  let body =
    match maybe_body with
    | Some b -> lazy (hhterm_of b)
    | None -> lazy (mk_id "$Axiom")
  in
  let opaque =
    match maybe_body with
    | Some b -> false
    | None -> true
  in
  (mk_comb(mk_id "$Const", mk_id (Id.to_string id)), opaque, hhterm_of kind, lazy (hhterm_of ty), body)

let get_hyps gl =
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let make_good =
    function
    | Context.Named.Declaration.LocalAssum(x, y) ->
       (x.binder_name, None, EConstr.to_constr sigma y)
    | Context.Named.Declaration.LocalDef(x, y, z) ->
       (x.binder_name, Some (EConstr.to_constr sigma y), EConstr.to_constr sigma z)
  in
  List.map (Hhlib.comp (hhdef_of_hyp env sigma) make_good) (Proofview.Goal.hyps gl)

let get_goal gl =
  (mk_comb(mk_id "$Const", mk_id "_HAMMER_GOAL"),
   true,
   mk_comb(mk_id "$Sort", mk_id "$Prop"),
   lazy (hhterm_of (EConstr.to_constr (Proofview.Goal.sigma gl) (Proofview.Goal.concl gl))),
   lazy (mk_comb(mk_id "$Const", mk_id "_HAMMER_GOAL")))

let string_of t = Hh_term.string_of_hhterm (hhterm_of t)

let string_of_hhdef_2 (filename, (const, hkind, hty, hterm)) =
  (filename,
   "tt(" ^ Hh_term.string_of_hhterm const ^ "," ^
     Hh_term.string_of_hhterm hkind ^ "," ^ Hh_term.string_of_hhterm (Lazy.force hty) ^ "," ^
     Hh_term.string_of_hhterm (Lazy.force hterm) ^ ").")

let string_of_goal gl =
  string_of (EConstr.to_constr (Proofview.Goal.sigma gl) (Proofview.Goal.concl gl))

let my_search env =
  let save_in_list refl glob_ref env c = refl := glob_ref :: !refl in
  let ans = ref [] in
  let filter_modules glob_ref =
    Opt.FilterSet.for_all (fun m -> not (Utils.match_globref m glob_ref))
      (Opt.HammerFilterTable.v ())
  in
  let filter glob_ref env typ =
    (if !Opt.search_blacklist then
       Search.blacklist_filter glob_ref env typ
     else
       true)
    &&
    filter_modules glob_ref
  in
  let iter glob_ref env typ =
    if filter glob_ref env typ then save_in_list ans glob_ref env typ
  in
  let () = Search.generic_search None iter in
  List.filter
    begin fun glob_ref ->
      try
        ignore (Typeops.type_of_global_in_context env glob_ref);
        true
      with _ ->
        false
    end
    (List.rev !ans)

let unique_hhdefs hhdefs =
  let hash = Hashtbl.create 128 in
  List.filter
    begin fun (_, def) ->
      let name = Hh_term.get_hhdef_name def in
      if Hashtbl.mem hash name then
        false
      else
        begin
          Hashtbl.add hash name true;
          true
        end
    end
    hhdefs

let get_defs env sigma : Hh_term.hhdef list =
  List.map snd (unique_hhdefs
                  (List.map (hhdef_of_global env sigma) (my_search env)))

let ltac_timeout tm tac (args: Tacinterp.Value.t list) =
  Timeout.ptimeout tm (Utils.ltac_eval tac args)

let globref_to_econstr r =
  match r with
  | Names.GlobRef.VarRef(v) -> EConstr.mkVar v
  | Names.GlobRef.ConstRef(c) -> EConstr.mkConst c
  | Names.GlobRef.IndRef(i) -> EConstr.mkInd i
  | Names.GlobRef.ConstructRef(cr) -> EConstr.mkConstruct cr

let globref_to_const r =
  match r with
  | Names.GlobRef.ConstRef(c) -> c
  | _ -> failwith "globref: not a constant"

let globref_to_inductive r =
  match r with
  | Names.GlobRef.IndRef(i) -> i
  | _ -> failwith "globref: not an inductive type"

let mk_lst_str pref lst =
  let get_name x =
    Hhlib.drop_prefix x "Top."
  in
  match lst with
  | [] -> ""
  | h :: t -> pref ^ " " ^ List.fold_right (fun x a -> get_name x ^ ", " ^ a) t (get_name h)

let get_tac_args env sigma info =
  let deps = info.Provers.deps in
  let defs = info.Provers.defs in
  let inverts =
    Hhlib.sort_uniq Stdlib.compare (info.Provers.inversions @ info.Provers.cases)
  in
  let map_locate =
    List.map
      begin fun s ->
        try
          Nametab.locate (Libnames.qualid_of_string s)
        with Not_found ->
          Names.GlobRef.VarRef(Id.of_string s)
      end
  in
  let (deps, defs, inverts) = (map_locate deps, map_locate defs, map_locate inverts) in
  let filter_vars =
    List.filter (fun r -> match r with Names.GlobRef.VarRef(_) -> true | _ -> false)
  in
  let filter_nonvars =
    List.filter (fun r -> match r with Names.GlobRef.VarRef(_) -> false | _ -> true)
  in
  let filter_consts =
    List.filter (fun r -> match r with Names.GlobRef.ConstRef(_) -> true | _ -> false)
  in
  let (vars, deps) = (filter_vars deps, filter_nonvars deps) in
  let (deps, defs, inverts) =
    (List.map globref_to_econstr deps,
     List.map globref_to_const (filter_consts defs),
     List.map globref_to_inductive inverts)
  in
  (deps, defs, inverts)

let check_goal_prop gl =
  let env = Proofview.Goal.env gl in
  let evmap = Proofview.Goal.sigma gl in
  let tp =
    EConstr.to_constr evmap (Retyping.get_type_of env evmap (Proofview.Goal.concl gl))
  in
  match Constr.kind tp with
  | Sort s -> Sorts.family s = InProp
  | _ -> false

(***************************************************************************************)


(***************************************************************************************)

let provers_detected = ref false

let dirpath = Global.current_dirpath ()
let print_fol_tac () =
  Proofview.Goal.enter @@ fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let goal = get_goal gl in
  let hyps = get_hyps gl in
  let deps = get_defs env sigma in
  let deps1 = Features.predict hyps deps goal in
  Feedback.msg_warning Pp.(str "Extracted");
  CErrors.user_err Pp.(str "Error");
  let file =
    try Loadpath.try_locate_absolute_library dirpath with
    | CErrors.UserError _ ->
      let doc = Stm.get_doc 0 in
      match Stm.(get_ast ~doc (get_current_state ~doc)) with
      | Some CAst.{ loc = Some Loc.{ fname = InFile f; _ }; _ } ->
        let f = CUnix.remove_path_dot f in
        if Filename.is_relative f then CUnix.correct_path f (Sys.getcwd ()) else f
      | _ -> Feedback.msg_warning Pp.(str "Source file location could not be found"); "test.p"
  in
  Feedback.msg_warning Pp.(str "File");
  let dir = Filename.remove_extension file ^ "_fol/" in
  Feedback.msg_warning Pp.(str "Dir");
  if not @@ Sys.file_exists dir then
    Unix.mkdir dir 0o755;
  Feedback.msg_warning Pp.(str "Create dir");
  let [@warning "-8"] proof_name = Vernacstate.Proof_global.get_current_proof_name () in
  Feedback.msg_warning Pp.(str "proof name");
  let path = Lib.make_path proof_name in
  Feedback.msg_warning Pp.(str "path");
  let file = dir ^ Libnames.string_of_path path ^ ".p" in
  Feedback.msg_warning (Pp.str file);
  Provers.write_atp_file file deps1 hyps deps goal;
  Proofview.tclUNIT ()

open Tactician_ltac1_record_plugin__Tactic_learner

let get_tactic (s : string) =
  try
    (Tacenv.locate_tactic (Libnames.qualid_of_string s))
  with Not_found ->
    failwith ("tactic not found: " ^ s)

let get_tacexpr tac args =
  Tacexpr.TacArg(CAst.make
                   Tacexpr.(TacCall(CAst.make
                                      (Locus.ArgArg(None, get_tactic tac),
                                       args))))


module HLearner : TacticianOnlineLearnerType = functor (TS : TacticianStructures) -> struct
  open TS

  type model = unit

  let extra_tactic () = { confidence = 1.; focus = 0
                        ; tactic = tactic_make
                              (get_tacexpr "Hammer.Plugin.Hammer.fol" []) }
  let empty () = ()
  let learn () _ _ _ = ()
  let predict m s =
    IStream.cons (extra_tactic ()) IStream.empty
  let evaluate db _ _ = 0., db
end

let () = register_online_learner "Hplugin learner" (module HLearner)
