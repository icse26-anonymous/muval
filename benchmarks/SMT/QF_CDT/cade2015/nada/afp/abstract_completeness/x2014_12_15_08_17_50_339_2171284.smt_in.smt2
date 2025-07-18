;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort Rule$ 0 )
(declare-sort State$ 0 )
(declare-sort State_fset$ 0 )
(declare-sort State_fset_bool_fun$ 0 )
(declare-sort State_state_fset_option_fun$ 0 )
(declare-sort State_state_fset_bool_fun_fun$ 0 )
(declare-sort Rule_state_state_fset_option_fun_fun$ 0 )
(declare-sort Rule_state_state_fset_bool_fun_fun_fun$ 0 )
(declare-sort State_fset_option$ 0)
(declare-fun none$ ()State_fset_option$)
(declare-fun the$ (State_fset_option$)State_fset$)
(declare-fun some$ (State_fset$ )State_fset_option$)
(declare-fun r$ ()Rule$ )
(declare-fun s$ ()State$ )
(declare-fun uu$ ()State_fset_bool_fun$ )
(declare-fun eff$ ()Rule_state_state_fset_option_fun_fun$ )
(declare-fun eps$ (State_fset_bool_fun$ )State_fset$ )
(declare-fun uua$ (State_fset$ )State_fset_bool_fun$ )
(declare-fun uub$ (State_fset$ )State_fset_bool_fun$ )
(declare-fun eff$a (Rule_state_state_fset_option_fun_fun$ )Rule_state_state_fset_bool_fun_fun_fun$ )
(declare-fun fun_app$ (State_fset_bool_fun$ State_fset$ )Bool )
(declare-fun fun_app$a (State_state_fset_option_fun$ State$ )State_fset_option$ )
(declare-fun fun_app$b (Rule_state_state_fset_option_fun_fun$ Rule$ )State_state_fset_option_fun$ )
(declare-fun fun_app$c (State_state_fset_bool_fun_fun$ State$ )State_fset_bool_fun$ )
(declare-fun fun_app$d (Rule_state_state_fset_bool_fun_fun_fun$ Rule$ )State_state_fset_bool_fun_fun$ )
(assert (! (forall ((?v0 State_fset$ ))(! (= (fun_app$ uu$ ?v0 )(= (fun_app$a (fun_app$b eff$ r$ )s$ )(some$ ?v0 ))):pattern ((fun_app$ uu$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 State_fset$ )(?v1 State_fset$ ))(! (= (fun_app$ (uua$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$ (uua$ ?v0 )?v1 )))):named a1 ))
(assert (! (forall ((?v0 State_fset$ )(?v1 State_fset$ ))(! (= (fun_app$ (uub$ ?v0 )?v1 )(= ?v1 ?v0 )):pattern ((fun_app$ (uub$ ?v0 )?v1 )))):named a2 ))
(assert (! (not (= (ite (exists ((?v0 State_fset$ ))(= (fun_app$a (fun_app$b eff$ r$ )s$ )(some$ ?v0 )))(eps$ uu$ )(the$ none$ ))(the$ (fun_app$a (fun_app$b eff$ r$ )s$ )))):named a3 ))
(assert (! (forall ((?v0 Rule$ )(?v1 State$ )(?v2 State_fset$ ))(! (= (fun_app$ (fun_app$c (fun_app$d (eff$a eff$ )?v0 )?v1 )?v2 )(= (fun_app$a (fun_app$b eff$ ?v0 )?v1 )(some$ ?v2 ))):pattern ((fun_app$ (fun_app$c (fun_app$d (eff$a eff$ )?v0 )?v1 )?v2 )))):named a4 ))
(assert (! (forall ((?v0 State_fset_option$ ))(=> (not (= ?v0 none$ ))(= (some$ (the$ ?v0 ))?v0 ))):named a5 ))
(assert (! (forall ((?v0 State_fset_option$ ))(= (not (= ?v0 none$ ))(exists ((?v1 State_fset$ ))(= ?v0 (some$ ?v1 ))))):named a6 ))
(assert (! (forall ((?v0 State_fset_option$ ))(= (forall ((?v1 State_fset$ ))(not (= ?v0 (some$ ?v1 ))))(= ?v0 none$ ))):named a7 ))
(assert (! (forall ((?v0 State_fset$ ))(= (eps$ (uua$ ?v0 ))?v0 )):named a8 ))
(assert (! (forall ((?v0 State_fset$ ))(= (eps$ (uub$ ?v0 ))?v0 )):named a9 ))
(assert (! (forall ((?v0 State_fset_bool_fun$ )(?v1 State_fset$ ))(=> (and (fun_app$ ?v0 ?v1 )(forall ((?v2 State_fset$ ))(=> (fun_app$ ?v0 ?v2 )(= ?v2 ?v1 ))))(= (eps$ ?v0 )?v1 ))):named a10 ))
(assert (! (forall ((?v0 State_fset_option$ ))(=> (and (=> (= ?v0 none$ )false )(=> (= ?v0 (some$ (the$ ?v0 )))false ))false )):named a11 ))
(assert (! (forall ((?v0 State_fset$ )(?v1 State_fset$ ))(= (= (some$ ?v0 )(some$ ?v1 ))(= ?v0 ?v1 ))):named a12 ))
(assert (! (forall ((?v0 Rule_state_state_fset_option_fun_fun$ )(?v1 Rule$ )(?v2 State$ )(?v3 State_fset$ ))(! (= (fun_app$ (fun_app$c (fun_app$d (eff$a ?v0 )?v1 )?v2 )?v3 )(= (fun_app$a (fun_app$b ?v0 ?v1 )?v2 )(some$ ?v3 ))):pattern ((fun_app$ (fun_app$c (fun_app$d (eff$a ?v0 )?v1 )?v2 )?v3 )))):named a13 ))
(assert (! (forall ((?v0 State_fset$ ))(! (= (the$ (some$ ?v0 ))?v0 ):pattern ((some$ ?v0 )))):named a14 ))
(assert (! (forall ((?v0 State_fset_option$ )(?v1 State_fset_option$ ))(=> (and (= (= ?v0 none$ )(= ?v1 none$ ))(=> (and (not (= ?v0 none$ ))(not (= ?v1 none$ )))(= (the$ ?v0 )(the$ ?v1 ))))(= ?v0 ?v1 ))):named a15 ))
(assert (! (forall ((?v0 State_fset_bool_fun$ )(?v1 State_fset$ ))(=> (and (exists ((?v2 State_fset$ ))(fun_app$ ?v0 ?v2 ))(= ?v1 (eps$ ?v0 )))(fun_app$ ?v0 ?v1 ))):named a16 ))
(assert (! (forall ((?v0 State_fset_option$ ))(=> (and (=> (= ?v0 none$ )false )(=> (not (= ?v0 none$ ))false ))false )):named a17 ))
(assert (! (forall ((?v0 State_fset_bool_fun$ )(?v1 State_fset$ ))(=> (fun_app$ ?v0 ?v1 )(fun_app$ ?v0 (eps$ ?v0 )))):named a18 ))
(assert (! (forall ((?v0 State_fset_bool_fun$ )(?v1 State_fset$ ))(=> (fun_app$ ?v0 ?v1 )(fun_app$ ?v0 (eps$ ?v0 )))):named a19 ))
(assert (! (forall ((?v0 State_fset_bool_fun$ )(?v1 State_fset$ )(?v2 State_fset_bool_fun$ ))(=> (and (fun_app$ ?v0 ?v1 )(forall ((?v3 State_fset$ ))(=> (fun_app$ ?v0 ?v3 )(fun_app$ ?v2 ?v3 ))))(fun_app$ ?v2 (eps$ ?v0 )))):named a20 ))
(check-sat )
;(get-unsat-core )
