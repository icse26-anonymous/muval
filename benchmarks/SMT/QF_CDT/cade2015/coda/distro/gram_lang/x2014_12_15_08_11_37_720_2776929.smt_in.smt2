;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort N$ 0 )
(declare-sort N_dtree_fun$ 0 )
(declare-sort N_list_N_list_fun$ 0 )
(declare-sort N_list$ 0)
(declare-fun nil$ ()N_list$)
(declare-fun hd$ (N_list$)N$)
(declare-fun tl$ (N_list$)N_list$)
(declare-fun cons$ (N$ N_list$ )N_list$)
(declare-fun f$ ()N_dtree_fun$ )
(declare-fun nl1$ ()N_list$ )
(declare-fun nl2$ ()N_list$ )
(declare-fun path$ (N_dtree_fun$ N_list$ )Bool )
(declare-fun append$ (N_list$ )N_list_N_list_fun$ )
(declare-fun fun_app$ (N_list_N_list_fun$ N_list$ )N_list$ )
(assert (! (not (path$ f$ nl2$ )):named a0 ))
(assert (! (path$ f$ (fun_app$ (append$ nil$ )nl2$ )):named a1 ))
(assert (! (not (= nl2$ nil$ )):named a2 ))
(assert (! (not (= nl2$ nil$ )):named a3 ))
(assert (! (path$ f$ (fun_app$ (append$ nl1$ )nl2$ )):named a4 ))
(assert (! (forall ((?v0 N_dtree_fun$ )(?v1 N_list$ ))(=> (path$ ?v0 ?v1 )(not (= ?v1 nil$ )))):named a5 ))
(assert (! (forall ((?v0 N_list$ )(?v1 N_list$ ))(= (= (fun_app$ (append$ ?v0 )?v1 )?v1 )(= ?v0 nil$ ))):named a6 ))
(assert (! (forall ((?v0 N_list$ )(?v1 N_list$ ))(= (= (fun_app$ (append$ ?v0 )?v1 )?v0 )(= ?v1 nil$ ))):named a7 ))
(assert (! (forall ((?v0 N_list$ )(?v1 N_list$ ))(= (= ?v0 (fun_app$ (append$ ?v1 )?v0 ))(= ?v1 nil$ ))):named a8 ))
(assert (! (forall ((?v0 N_list$ )(?v1 N_list$ ))(= (= ?v0 (fun_app$ (append$ ?v0 )?v1 ))(= ?v1 nil$ ))):named a9 ))
(assert (! (forall ((?v0 N_list$ )(?v1 N_list$ ))(= (= nil$ (fun_app$ (append$ ?v0 )?v1 ))(and (= ?v0 nil$ )(= ?v1 nil$ )))):named a10 ))
(assert (! (forall ((?v0 N_list$ )(?v1 N_list$ ))(= (= (fun_app$ (append$ ?v0 )?v1 )nil$ )(and (= ?v0 nil$ )(= ?v1 nil$ )))):named a11 ))
(assert (! (forall ((?v0 N_list$ ))(! (= (fun_app$ (append$ ?v0 )nil$ )?v0 ):pattern ((append$ ?v0 )))):named a12 ))
(assert (! (forall ((?v0 N_list$ )(?v1 N_list$ )(?v2 N_list$ ))(= (= (fun_app$ (append$ ?v0 )?v1 )(fun_app$ (append$ ?v0 )?v2 ))(= ?v1 ?v2 ))):named a13 ))
(assert (! (forall ((?v0 N_list$ )(?v1 N_list$ )(?v2 N_list$ ))(= (= (fun_app$ (append$ ?v0 )?v1 )(fun_app$ (append$ ?v2 )?v1 ))(= ?v0 ?v2 ))):named a14 ))
(assert (! (forall ((?v0 N_list$ )(?v1 N_list$ )(?v2 N_list$ ))(= (fun_app$ (append$ (fun_app$ (append$ ?v0 )?v1 ))?v2 )(fun_app$ (append$ ?v0 )(fun_app$ (append$ ?v1 )?v2 )))):named a15 ))
(assert (! (forall ((?v0 N_list$ ))(! (= (fun_app$ (append$ nil$ )?v0 )?v0 ):pattern ((fun_app$ (append$ nil$ )?v0 )))):named a16 ))
(assert (! (forall ((?v0 N_list$ )(?v1 N_list$ ))(=> (= ?v0 ?v1 )(= ?v0 (fun_app$ (append$ nil$ )?v1 )))):named a17 ))
(assert (! (forall ((?v0 N_list$ ))(=> (and (=> (= ?v0 nil$ )false )(=> (not (= ?v0 nil$ ))false ))false )):named a18 ))
(assert (! (forall ((?v0 N_list$ )(?v1 N_list$ )(?v2 N_list$ )(?v3 N_list$ )(?v4 N_list$ ))(=> (and (= (fun_app$ (append$ ?v0 )?v1 )?v2 )(= ?v3 (fun_app$ (append$ ?v1 )?v4 )))(= (fun_app$ (append$ ?v0 )?v3 )(fun_app$ (append$ ?v2 )?v4 )))):named a19 ))
(check-sat )
;(get-unsat-core )
