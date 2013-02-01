open Term
open Termops
open Environ
open Declarations
open Entries
open Pp
open Names
open Libnames
open Nameops
open Util
open Closure
open RedFlags
open Tacticals
open Typing
open Tacmach
open Tactics
open Nametab
open Declare
open Decl_kinds
open Tacred
open Proof_type
open Vernacinterp
open Pfedit
open Topconstr
open Glob_term
open Pretyping
open Safe_typing
open Constrintern
open Hiddentac
open Namegen

open Equality
open Auto
open Eauto

open Genarg

let prgoal g = msgnl (Printer.pr_goal ( g));;

let hyp_ids = List.map id_of_string ["x";"v";"k";"def";"p";"h";"n";"h'"; 
				     "anonymous"; "teq"; "rec_res";
				     "hspec";"heq"; "hrec"; "hex"];;

let hyp_id n l = List.nth l n;;

let (x_id:(identifier list)->identifier) = hyp_id 0;;
let (v_id:(identifier list)->identifier) = hyp_id 1;;
let (k_id:(identifier list)->identifier) = hyp_id 2;;
let (def_id:(identifier list)->identifier) = hyp_id 3;;
let (p_id:(identifier list)->identifier) = hyp_id 4;;
let (h_id:(identifier list)->identifier) = hyp_id 5;;
let (n_id:(identifier list)->identifier) = hyp_id 6;;
let (h'_id:(identifier list)->identifier) = hyp_id 7;;
let (ano_id:(identifier list)->identifier) = hyp_id 8;;
let (rec_res_id:(identifier list)->identifier) = hyp_id 10;;
let (hspec_id:(identifier list)->identifier) = hyp_id 11;;
let (heq_id:(identifier list)->identifier) = hyp_id 12;;
let (hrec_id:(identifier list)->identifier) = hyp_id 13;;
let (hex_id:(identifier list)->identifier) = hyp_id 14;;


let message s = if Flags.is_verbose () then msgnl(str s);;

let rec getMutCase env t =
  match kind_of_term t with
      Lambda(name, types, t') ->
	let id,env =
	  (match name with 
	       Anonymous -> 
		 error "don't know how to handle anonymous variables"
	     | Name id -> 
		 id, Environ.push_named (id, None, types) env ) in
	  (match getMutCase env (subst1 (mkVar id) t') with
	       (l,e,c) -> (id::l,e,c))
    | Case (b, c, a, d) -> ([], env , a)
    | _ -> Pp.pp(Printer.pr_lconstr t) ;
	error "Reste a traiter les autres formes, si c'est une application,
	 Si c'est un autre Case imbrique ou autre... "
;;

let def_of_const t =
  match (kind_of_term t) with
      Const sp -> 
	(try
	   let cb = Global.lookup_constant sp in
	   match Declarations.body_of_constant cb with
	       Some c -> Declarations.force c
	     | _ -> assert false
	 with _ -> assert false)
    |_ -> assert false
;;

(* replaces get_type *)
let arg_type t =
  match kind_of_term (def_of_const t) with
      Lambda(a,b,c) -> b
    | _ -> assert false;;

let result_type t =
  match destProd (arg_type t) with _, _, r -> r;;

let a_of_case t = 
  match (getMutCase (Global.env()) (def_of_const t)) with
      (identifier_list, env, a) -> a;;

let evaluable_reference t =
  match kind_of_term t with
      Const sp -> EvalConstRef sp
    | _ -> assert false;;

let evaluable_of_global_reference r =
  match r with 
      ConstRef sp -> EvalConstRef sp
    | VarRef id -> EvalVarRef id
    | _ -> assert false;;

let rec (find_call_occs: constr -> constr -> ((constr->constr)*constr)option) =
  fun f expr ->
    match (kind_of_term expr) with
	App (g, args) when g = f -> 
	  (* For now, we suppose that the function we work on 
	     takes only one argument. *)
	  Some ((fun x -> x), args.(0))
      | App (g, args) ->
	  let largs = Array.to_list args in
	  let rec find_aux = function
	      []    -> ((fun x -> []), None)
	    | a::tl -> match (find_call_occs f a) with
		  (Some (cf, args)) -> (fun x -> cf x::tl), (Some args)
		| None -> (match (find_aux tl) with
			       (cf, opt_args) -> ((fun x -> a::cf x), opt_args)) in
	    (match (find_aux largs) with
		 cf, None -> None
	       | cf, Some args -> Some ((fun x -> mkApp (g, Array.of_list (cf x))),
					args))
      | Rel(_) -> error "find_call_occs : Rel"
      | Var(id) -> None
      | Meta(_) -> error "find_call_occs : Meta"
      | Evar(_) -> error "find_call_occs : Evar"
      | Sort(_)  -> error "find_call_occs : Sort"
      | Cast(_,_,_) -> error "find_call_occs : cast"
      | Prod(_,_,_) -> error "find_call_occs : Prod"
      | Lambda(_,_,_) -> error "find_call_occs : Lambda"
      | LetIn(_,_,_,_) -> error "find_call_occs : let in"
      | Const(_) -> None
      | Ind(_) -> None
      | Construct (_, _) -> None
      | Case(i,t,a,r) -> (match find_call_occs f a with
			      Some (cf, args) -> 
				Some((fun x -> mkCase(i, t, (cf x), r)), args)
			    | None -> None)
      | Fix(_) -> error "find_call_occs : Fix"
      | CoFix(_) -> error "find_call_occs : CoFix";;

let coq_init_constant s =
  Coqlib.gen_constant_in_modules "RecursiveDefinition" 
    Coqlib.init_modules s;;

let coq_constant s =
  Coqlib.gen_constant_in_modules "RecursiveDefinition" 
    (Coqlib.init_modules @ Coqlib.arith_modules) s;;

let constant sl s =
  constr_of_reference
    (locate (make_qualid(Names.make_dirpath 
			   (List.map id_of_string (List.rev sl)))
	       (id_of_string s)));;

let find_reference sl s =
  (locate (make_qualid(Names.make_dirpath 
			 (List.map id_of_string (List.rev sl)))
	     (id_of_string s)));;

let ssplus_lt = lazy(constant ["Term_const"] "SSplus_lt")
let splus_lt = lazy(constant ["Term_const"] "Splus_lt")

let refl_equal = lazy(coq_init_constant "eq_refl")
let eq = lazy(coq_init_constant "eq")
let ex = lazy(coq_init_constant "ex")
let coq_sig_ref = lazy(find_reference ["Coq";"Init";"Specif"] "sig")
let coq_sig = lazy(coq_init_constant "sig")
let coq_O = lazy(coq_init_constant "O")
let coq_S = lazy(coq_init_constant "S")

let gt_irrefl = lazy(coq_constant "gt_irrefl")
let lt_n_O = lazy(coq_constant "lt_n_O")
let lt_n_Sn = lazy(coq_constant "lt_n_Sn")

let f_equal = lazy(coq_constant "f_equal")
let well_founded_induction = lazy(coq_constant "well_founded_induction")

let iter_ref = lazy(find_reference ["Term_const"] "iter")
let iter = lazy(constr_of_reference (Lazy.force iter_ref))
let coq_plus = lazy(coq_constant "plus")

(* These are specific to experiments in nat with lt as well_founded_relation,
   but this should be made more general. *)
let nat = lazy(coq_init_constant "nat")
let lt = lazy(coq_init_constant "lt")
let lt_wf = lazy(coq_constant "lt_wf")

let  mkCaseEq a =
  (fun g ->
     (* commentaire de Yves: on pourra avoir des problemes si
	a n'est pas bien type dans l'environnement du but *)
     let type_of_a = (type_of (pf_env g) Evd.empty a) in
       (tclTHEN (generalize [mkApp(Lazy.force refl_equal,
				   [| type_of_a; a|])])
	  (tclTHEN (fun g2 ->
		      change_in_concl None
			(pattern_occs [((true,[2]), a)] 
			   (pf_env g2)
			   Evd.empty (pf_concl g2)) g2)
	     (simplest_case a))) g);;

let rec  mk_intros_and_continue (extra_eqn:bool)
    cont_function rec_ids func (eqs:constr list) expr g =
  let ids = rec_ids@(ids_of_named_context (pf_hyps g)) in
    match (kind_of_term expr) with
	Lambda (n, _, b) -> 
     	  let n1 = (match n with
      			Name x -> x
                      | Anonymous -> ano_id hyp_ids ) in
     	  let new_n = next_ident_away n1 ids in
	    tclTHEN (intro_using new_n)
	      (mk_intros_and_continue extra_eqn cont_function
		 (new_n::rec_ids) func eqs 
		 (subst1 (mkVar new_n) b)) g
      | _ -> 
 	  if extra_eqn then
	    let teq = next_ident_away (id_of_string "teq") ids in
	      tclTHEN (intro_using teq)	
		(cont_function (teq::rec_ids) func (mkVar teq::eqs) expr) g
	  else
	    cont_function rec_ids func eqs expr g;;

let const_of_ref = function
    ConstRef kn -> kn
  | _ -> anomaly "ConstRef expected"

let simpl_iter () =
  reduce 
    (Lazy 
       {rBeta=true;rIota=true;rZeta= true; rDelta=false;
        rConst = [ EvalConstRef (const_of_ref (Lazy.force iter_ref))]})
    onConcl;;

let list_rewrite (rev:bool) (eqs: constr list) =
  tclREPEAT
    (List.fold_right
       (fun eq i -> tclORELSE (rewriteLR eq) i)
       (if rev then (List.rev eqs) else eqs) (tclFAIL 0 (mt())));;

let base_leaf (func:global_reference) eqs expr =
  (*  let _ = msgnl (str "entering base_leaf") in *)
  (fun g ->
     let ids = ids_of_named_context (pf_hyps g) in
     let k = next_ident_away (k_id hyp_ids) ids in
     let h = next_ident_away (h_id hyp_ids) (k::ids) in
     let _def = next_ident_away (def_id hyp_ids) (h::k::ids) in
       tclTHENLIST [split (ImplicitBindings [expr]);
		    split (ImplicitBindings [Lazy.force coq_O]);
		    intro_using k;
                    tclTHENS (simplest_case (mkVar k))
                      [(tclTHEN (intro_using h) 
		     	  (tclTHEN (simplest_elim 
				      (mkApp (Lazy.force gt_irrefl,
					      [| Lazy.force coq_O |])))
		             default_full_auto)); tclIDTAC];
                    intros;
		    simpl_iter();
		    unfold_constr func;
                    list_rewrite true eqs;
		    default_full_auto ] g);;

(* La fonction est donnee en premier argument a la 
   fonctionnelle suivie d'autres Lambdas et de Case ...
   Pour recuperer la fonction f a partir de la 
   fonctionnelle *)
let get_f foncl = 
  match (kind_of_term (def_of_const foncl)) with
      Lambda (Name f, _, _) -> f  
    |_ -> error "la fonctionnelle est mal definie";;

let rec_leaf hrec proofs result_type (func:global_reference) eqs expr =
  (*  let _ = msgnl(str "entering rec_leaf") in *)
  let fn, arg = 
    (match (find_call_occs (mkVar (get_f (constr_of_reference func))) expr) with
         Some (a, b) -> a,b
       | None -> failwith "rec_leaf called in a wrong context 
                                          (no recursive call)") in 
    (fun g ->
       let ids = ids_of_named_context (pf_hyps g) in
       let rec_res = next_ident_away (rec_res_id hyp_ids) ids in
       let hspec = next_ident_away (hspec_id hyp_ids) (rec_res::ids) in
       let p = next_ident_away (p_id hyp_ids) (hspec::rec_res::ids) in
       let heq = next_ident_away (id_of_string "heq") (p::hspec::rec_res::ids) in
       let s_p = mkApp(Lazy.force coq_S, [|mkVar p|]) in
       let k = next_ident_away (k_id hyp_ids) (heq::p::hspec::rec_res::ids) in
       let def = next_ident_away (def_id hyp_ids)
	 (k::heq::p::hspec::rec_res::ids) in
       let h' = next_ident_away (h'_id hyp_ids)
	 (def::k::heq::p::hspec::rec_res::ids) in
	 tclTHENS
	   (simplest_elim (mkApp(mkVar hrec, [|arg|])))
           [tclTHENLIST 
	      [intros_using [rec_res ; hspec]; 
	       split (ImplicitBindings [fn (mkVar rec_res)]);
               simplest_elim (mkVar hspec);             
               list_rewrite true eqs;
	       intros_using [p; heq]; split (ImplicitBindings [s_p]);
               intro_using k;
               tclTHENS
		 (simplest_case (mkVar k))
		 [tclTHENLIST
		    [intro_using h';
                     simplest_elim(mkApp(Lazy.force lt_n_O, [|s_p|]));
                     default_full_auto];
		  tclIDTAC];
               clear [k];
               intros_using [k; h'; def];
	       simpl_iter();
               unfold_in_concl[((true,[1]), evaluable_of_global_reference func)];
               list_rewrite true eqs; 
	       apply_with_bindings
		 (Lazy.force f_equal, 
		  ExplicitBindings[dummy_loc,NamedHyp (id_of_string "f"), 
				   mkLambda(Name (id_of_string "xx"), result_type,
					    fn (mkRel 1))]);
	       default_full_auto];
	    tclTHENLIST
	      [list_rewrite true eqs;
               List.fold_right
                 (fun proof tac ->
                    tclORELSE
                      (tclCOMPLETE
			 (tclTHENLIST
                            [h_simplest_eapply proof;
                             tclORELSE default_full_auto e_assumption]))
                      tac)
                 proofs
                 (fun g ->
                    (msgnl (str "complete proof failed for");
                     prgoal g; tclFAIL 0 (mt()) g))]] g);;

let rec (proveterminate:identifier -> (constr list) -> constr ->
	  (identifier list) -> global_reference -> (constr list) -> constr -> tactic) =
  fun (hrec:identifier) (preuves:constr list)  (f_constr:constr)
    (ids:identifier list) (func:global_reference) (eqs:constr list) (expr:constr) ->
      try
	(*  let _ = msgnl (str "entering proveterminate") in *)
	let v =
	  match (kind_of_term expr) with
	      Case (_, t, a, l) -> 
		(match (find_call_occs f_constr a) with
		     None ->
      		       tclTHENS (fun g ->
				   (*			   let _ = msgnl(str "entering mkCaseEq") in *)
				   let v = (mkCaseEq a) g in 
				     (*			   let _ = msgnl (str "exiting mkCaseEq") in *)
				     v
				)
   			 (List.map (mk_intros_and_continue true
				      (proveterminate hrec preuves f_constr)
				      ids func eqs) 
			    (Array.to_list l))
		   | Some _ -> (match (find_call_occs  f_constr expr) with
	     			    (* ici expr c'est la partie dte des regles
	     			       et donc c'est le b du mk_intros_and_continue*)
	     			    None -> 
				      (try 
					 base_leaf func eqs expr
				       with e -> (msgerrnl (str "failure in base case");raise e))
				  | Some x -> 
				      (try
					 rec_leaf hrec preuves
					   (result_type (constr_of_reference func)) func eqs expr
				       with e -> (msgerrnl (str "failure in recursive case");
						  raise e))))
	    | _ -> (match (find_call_occs  f_constr expr) with
	     		None -> 
			  (try 
			     base_leaf func eqs expr
			   with e -> (msgerrnl (str "failure in base case");raise e))
		      | Some x -> 
			  (try
			     rec_leaf hrec preuves
			       (result_type (constr_of_reference func)) func eqs expr
			   with e -> (msgerrnl (str "failure in recursive case");
				      raise e))) in
	  (*  let _ = msgnl(str "exiting proveterminate") in *)
	  v
      with e -> msgerrnl(str "failure in proveterminate"); raise e;;

let hyp_terminates fl = 
  let foncl = global_reference fl in 
  let _f = (get_f foncl) in
  let a_arrow_b = (arg_type foncl) in
  let (_,a,b) = destProd a_arrow_b in
  let left= mkApp (Lazy.force iter, [|a_arrow_b ;(mkRel 3); (foncl);
			     	      (mkRel 1); (mkRel 6)|]) in
  let right= (mkRel 5) in
  let equality = mkApp(Lazy.force eq, [|b; left; right|]) in
  let result = (mkProd ((Name (def_id hyp_ids)) , a_arrow_b, equality)) in
  let cond = mkApp(Lazy.force lt, [|(mkRel 2); (mkRel 1)|]) in
  let nb_iter =
    mkApp(Lazy.force ex,
	  [|Lazy.force nat;
	    (mkLambda 
	       (Name
		  (p_id hyp_ids),
		Lazy.force nat, 
		(mkProd (Name (k_id hyp_ids), Lazy.force nat, 
			 mkArrow cond result))))|])in
    
  let value = mkApp(Lazy.force coq_sig, 
		    [|b;
		      (mkLambda (Name (id_of_string "v"), b, nb_iter))|]) in
  let statement = mkProd ((Name (x_id hyp_ids)), a, value) in 
    (statement ) ;; 

let start n_name input_type relation wf_thm = 
  (fun g ->
     try
       let ids = ids_of_named_context (pf_hyps g) in
       let hrec = next_ident_away (hrec_id hyp_ids) (n_name::ids) in
       let wf_c = {elimindex = Some(-1);
                   elimbody = mkApp(Lazy.force well_founded_induction,
			[|input_type; relation; wf_thm|]),ImplicitBindings[]} in
       let x = next_ident_away (x_id hyp_ids) (hrec::n_name::ids) in
       let v =
	 (fun g ->
	    let v = 
	      tclTHENLIST
		[intro_using x;
		 general_elim false (mkVar x, ImplicitBindings[]) wf_c;
		 clear [x];
		 intros_using [n_name; hrec]] g in
	      v), hrec in 
	 v
     with e -> msgerrnl(str "error in start"); raise e);;

let rec instantiate_lambda t = function
  | [] -> t
  | a::l -> let (bound_name, _, body) = destLambda t in
      (match bound_name with
	   Name id -> instantiate_lambda (subst1 a body) l
	 | Anonymous -> body) ;;

let whole_start foncl input_type relation wf_thm preuves =  
  (fun g ->
     let v =
       let ids = ids_of_named_context (pf_hyps g) in
       let foncl_body = (def_of_const (constr_of_reference foncl)) in
       let (f_name, _, body1) = destLambda foncl_body in
       let f_id =
	 match f_name with  
	   | Name f_id -> next_ident_away f_id ids
	   | Anonymous -> assert false in
       let n_name, _, _ = destLambda body1 in
       let n_id =
	 match n_name with
	   | Name n_id -> next_ident_away n_id (f_id::ids)
	   | Anonymous -> assert false in
       let tac, hrec = (start n_id input_type relation wf_thm g) in
	 tclTHEN tac
	   (proveterminate hrec preuves (mkVar f_id)
	      (hrec::n_id::f_id::ids) foncl []
	      (instantiate_lambda foncl_body [mkVar f_id;mkVar n_id])) g in
       (*     let _ = msgnl(str "exiting whole start") in *)
       v);;

let com_terminate fl input_type relation_ast wf_thm_ast thm_name proofs =
  let (evmap, env) = Lemmas.get_current_context() in
  let (comparison:constr)= interp_constr evmap env relation_ast in
  let (wf_thm:constr) = interp_constr evmap env wf_thm_ast in
  let (proofs_constr:constr list) =
    List.map (fun x -> interp_constr evmap env x) proofs in
  let (foncl_constr:constr) = global_reference fl in 
    (start_proof thm_name
       (Global, Proof Lemma) (Environ.named_context_val env) (hyp_terminates fl)
       (fun _ _ -> ());
     by (whole_start (reference_of_constr foncl_constr)
	   input_type comparison wf_thm proofs_constr);
     Lemmas.save_named true);;

let ind_of_ref = function 
  | IndRef (ind,i) -> (ind,i)
  | _ -> anomaly "IndRef expected"

let (value_f:constr -> global_reference -> constr) =
  fun a fterm ->
    let d0 = dummy_loc in 
    let x_id = id_of_string "x" in
    let v_id = id_of_string "v" in
    let context = [Name x_id, None, a] in
    let env = Environ.push_rel_context context (Global.env ()) in
    let glob_body =
      GCases
	(d0,RegularStyle,None,
	 [GApp(d0, GRef(d0,fterm), [GVar(d0, x_id)]),(Anonymous,None)],
	 [d0, [v_id], [PatCstr(d0,(ind_of_ref
				     (Lazy.force coq_sig_ref),1),
			       [PatVar(d0, Name v_id);
				PatVar(d0, Anonymous)],
			       Anonymous)],
	  GVar(d0,v_id)])
    in
    let body = Default.understand Evd.empty env glob_body in
    it_mkLambda_or_LetIn body context

let (declare_fun : identifier -> logical_kind -> constr -> global_reference) =
  fun f_id kind value ->
    let ce = {const_entry_body = value;
	      const_entry_type = None;
	      const_entry_secctx = None;
	      const_entry_opaque = false} in
      ConstRef(declare_constant f_id (DefinitionEntry ce, kind));;

let (declare_f : identifier -> logical_kind -> constr -> global_reference -> global_reference) =
  fun f_id kind input_type fterm_ref ->
    declare_fun f_id kind (value_f input_type fterm_ref);;

let start_equation (f:global_reference) (term_f:global_reference) 
    (cont_tactic:identifier -> tactic) g =
  let ids = ids_of_named_context (pf_hyps g) in
  let x = next_ident_away (x_id hyp_ids) ids in
    tclTHENLIST [
      intro_using x;
      unfold_constr f;
      simplest_case (mkApp (constr_of_reference term_f, [| mkVar x|]));
      cont_tactic x] g;;

let base_leaf_eq func eqs f_id g =
  let ids = ids_of_named_context (pf_hyps g) in
  let k = next_ident_away (k_id hyp_ids) ids in
  let p = next_ident_away (p_id hyp_ids) (k::ids) in
  let v = next_ident_away (v_id hyp_ids) (p::k::ids) in
  let heq = next_ident_away (heq_id hyp_ids) (v::p::k::ids) in
  let heq1 = next_ident_away (heq_id hyp_ids) (heq::v::p::k::ids) in
  let hex = next_ident_away (hex_id hyp_ids) (heq1::heq::v::p::k::ids) in
    tclTHENLIST [
      intros_using [v; hex]; 
      simplest_elim (mkVar hex);
      intros_using [p;heq1];
      tclTRY
	(rewriteRL 
	   (mkApp(mkVar heq1, 
		  [|mkApp (Lazy.force coq_S, [|mkVar p|]);
		    mkApp(Lazy.force lt_n_Sn, [|mkVar p|]); f_id|])));
      simpl_iter();
      unfold_in_concl [((true,[1]), evaluable_of_global_reference func)];
      list_rewrite true eqs;
      apply (Lazy.force refl_equal)] g;;

let f_S t = mkApp(Lazy.force coq_S, [|t|]);;
let f_plus t1 t2 = mkApp(Lazy.force coq_plus, [|t1;t2|]);;

let rec_leaf_eq termine f ids functional eqs expr fn args =
  let k = next_ident_away (k_id hyp_ids) ids in
  let p = next_ident_away (p_id hyp_ids) (k::ids) in
  let v = next_ident_away (v_id hyp_ids) (p::k::ids) in
  let v' = next_ident_away (v_id hyp_ids) (v::p::k::ids) in
  let p' = next_ident_away (p_id hyp_ids) (v'::v::p::k::ids) in
  let heq = next_ident_away (heq_id hyp_ids) (p'::v'::v::p::k::ids) in
  let heq' = next_ident_away (heq_id hyp_ids) (heq::p'::v'::v::p::k::ids) in
  let hex = next_ident_away (hex_id hyp_ids) (heq'::heq::p'::v'::v::p::k::ids) in
  let hex' = next_ident_away (hex_id hyp_ids)
    (hex::heq'::heq::p'::v'::v::p::k::ids) in
  let heq1 = next_ident_away (heq_id hyp_ids)
    (hex'::hex::heq'::heq::p'::v'::v::p::k::ids) in
  let heq2 = next_ident_away (heq_id hyp_ids)
    (heq1::hex'::hex::heq'::heq::p'::v'::v::p::k::ids) in
  let heq3 = next_ident_away (heq_id hyp_ids)
    (heq2::heq1::hex'::hex::heq'::heq::p'::v'::v::p::k::ids) in
  let c_p = mkVar p in
  let c_p' = mkVar p' in
    tclTHENLIST
      [intros_using [v;hex];
       simplest_elim (mkVar hex);
       intros_using [p;heq1];
       mkCaseEq (mkApp(termine, [| args |]));
       intros_using [v';hex'];
       simplest_elim (mkVar hex');
       intros_using [p'];
       rewriteRL
	 (mkApp
	    (mkVar heq1,
	     [| f_S(f_S(f_plus c_p c_p'));
		mkApp(Lazy.force ssplus_lt, [|c_p;c_p'|]); f|]));
       simpl_iter();
       unfold_constr (reference_of_constr functional);
       list_rewrite true eqs;
       intros_using [heq2;heq3];
       tclTRY (rewriteLR (mkVar heq3));
       rewriteRL
	 (mkApp
	    (mkVar heq2,
	     [| f_S(f_plus c_p c_p');
		mkApp(Lazy.force splus_lt, [|c_p;c_p'|]); f|]));
       default_full_auto;
       (fun g-> prgoal g;tclIDTAC g)];;

let rec prove_eq (termine:constr) (f:constr)
    (ids:identifier list) (functional:constr)(eqs:constr list)
    (expr:constr) =
  match kind_of_term expr with
      Case(_,t,a,l) ->
	(match find_call_occs f a with
	     None -> 
	       tclTHENS(mkCaseEq a)(* (simplest_case a) *)
	  	 (List.map
		    (mk_intros_and_continue true
		       (prove_eq termine f) ids functional eqs)
		    (Array.to_list l))
	   | Some x ->
               (match find_call_occs f expr with
		    None -> base_leaf_eq (reference_of_constr functional) eqs f
		  | Some (fn,args) ->
		      rec_leaf_eq termine f ids functional eqs expr fn args))
    | _ -> 
	(match find_call_occs f expr with
	     None -> base_leaf_eq (reference_of_constr functional) eqs f
	   | Some (fn,args) ->
	       rec_leaf_eq termine f ids functional eqs expr fn args);;

let (com_eqn : identifier ->
      global_reference -> global_reference -> global_reference
      -> constr_expr -> unit) =
  fun eq_name functional_ref f_ref terminate_ref eq ->
    let (evmap, env) = Lemmas.get_current_context() in
    let eq_constr = interp_constr evmap env eq in
    let functional_constr = (constr_of_reference functional_ref) in
    let f_constr = (constr_of_reference f_ref) in
      (start_proof eq_name (Global, Proof Lemma)
	 (Environ.named_context_val env) eq_constr (fun _ _ -> ());
       by
	 (start_equation f_ref terminate_ref
	    (fun x ->
	       prove_eq (constr_of_reference terminate_ref) 
		 f_constr [x] functional_constr []
		 (instantiate_lambda 
		    (def_of_const functional_constr)
		    [f_constr; mkVar x])));
       Lemmas.save_named true);;

let recursive_definition f type_of_f r wf proofs eq =
  let function_type = interp_constr Evd.empty (Global.env()) type_of_f in
  let env = push_rel (Name f,None,function_type) (Global.env()) in
  let res = match kind_of_term (interp_constr Evd.empty env eq) with
      Prod(Name name_of_var,type_of_var,e) ->
	(match kind_of_term e with
	     App(e,[|type_e;gche;b|]) ->
	       mkLambda(Name f,function_type,
			mkLambda(Name name_of_var,type_of_var,b))
	   |_ -> failwith "Recursive Definition")
    |_ -> failwith "Recursive Definition" in
  let (_, input_type, _) = destProd function_type in
  let equation_id = add_suffix f "_equation" in
  let functional_id =  add_suffix f "_F" in
  let term_id = add_suffix f "_terminate" in
  let functional_ref = declare_fun functional_id (IsDefinition Definition) res in
  let _ = com_terminate functional_id input_type r wf term_id proofs in
  let term_ref = Nametab.locate (qualid_of_ident term_id) in
  let f_ref = declare_f f (IsProof Lemma) input_type term_ref in
  let _ = message "start second proof" in
    com_eqn equation_id functional_ref f_ref term_ref eq;;

VERNAC COMMAND EXTEND RecursiveDefinition
  [ "Recursive" "Definition" ident(f) constr(type_of_f) constr(r) constr(wf)
      constr(proof) constr(eq) ] ->
    [ recursive_definition f type_of_f r wf [proof] eq ]
  | [ "Recursive" "Definition" ident(f) constr(type_of_f) constr(r) constr(wf)
	"[" ne_constr_list(proof) "]" constr(eq) ] ->
      [ recursive_definition f type_of_f r wf proof eq ]

	END
	
