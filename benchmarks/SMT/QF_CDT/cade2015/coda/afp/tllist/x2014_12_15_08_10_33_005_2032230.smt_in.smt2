;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort B_b_fun$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_b_tllist_bool_fun$ 0 )
(declare-sort A_a_b_tllist_bool_fun_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))(A_b_tllist$ (tNil$ (terminal$ B$ ))(tCons$ (thd$ A$ )(ttl$ A_b_tllist$ )))))
(declare-fun xs$ ()A_b_tllist$ )
(declare-fun tmap$ (A_a_fun$ B_b_fun$ A_b_tllist$ )A_b_tllist$ )
(declare-fun tset$ (A_b_tllist$ )A_set$ )
(declare-fun lnull$ (A_llist$ )Bool )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (A_a_fun$ A$ )A$ )
(declare-fun is_TNil$ (A_b_tllist$ )Bool )
(declare-fun fun_app$a (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$b (A_b_tllist_bool_fun$ A_b_tllist$ )Bool )
(declare-fun fun_app$c (A_a_b_tllist_bool_fun_fun$ A$ )A_b_tllist_bool_fun$ )
(declare-fun llist_of_tllist$ (A_b_tllist$ )A_llist$ )
(declare-fun tllist_of_llist$ (B$ A_llist$ )A_b_tllist$ )
(assert (! (not (= (lhd$ (llist_of_tllist$ xs$ ))(thd$ xs$ ))):named a0 ))
(assert (! (not (is_TNil$ xs$ )):named a1 ))
(assert (! (forall ((?v0 A_b_tllist$ ))(=> (and (=> (is_TNil$ ?v0 )false )(=> (not (is_TNil$ ?v0 ))false ))false )):named a2 ))
(assert (! (forall ((?v0 A_b_tllist$ ))(=> (and (=> (is_TNil$ ?v0 )false )(=> (not (is_TNil$ ?v0 ))false ))false )):named a3 ))
(assert (! (forall ((?v0 B$ )(?v1 A_llist$ ))(= (thd$ (tllist_of_llist$ ?v0 ?v1 ))(lhd$ ?v1 ))):named a4 ))
(assert (! (forall ((?v0 A_b_tllist$ )(?v1 A_a_fun$ )(?v2 B_b_fun$ ))(=> (not (is_TNil$ ?v0 ))(= (thd$ (tmap$ ?v1 ?v2 ?v0 ))(fun_app$ ?v1 (thd$ ?v0 ))))):named a5 ))
(assert (! (forall ((?v0 A_b_tllist$ ))(=> (not (is_TNil$ ?v0 ))(member$ (thd$ ?v0 )(tset$ ?v0 )))):named a6 ))
(assert (! (forall ((?v0 A_b_tllist$ ))(= (not (lnull$ (llist_of_tllist$ ?v0 )))(not (is_TNil$ ?v0 )))):named a7 ))
(assert (! (forall ((?v0 A_b_tllist$ ))(= (lnull$ (llist_of_tllist$ ?v0 ))(is_TNil$ ?v0 ))):named a8 ))
(assert (! (forall ((?v0 A_b_tllist$ ))(= (= (llist_of_tllist$ ?v0 )lNil$ )(is_TNil$ ?v0 ))):named a9 ))
(assert (! (forall ((?v0 A_b_tllist$ ))(! (=> (is_TNil$ ?v0 )(= (llist_of_tllist$ ?v0 )lNil$ )):pattern ((llist_of_tllist$ ?v0 )))):named a10 ))
(assert (! (forall ((?v0 A_b_tllist$ ))(=> (not (is_TNil$ ?v0 ))(not (lnull$ (llist_of_tllist$ ?v0 ))))):named a11 ))
(assert (! (forall ((?v0 A_b_tllist$ ))(=> (is_TNil$ ?v0 )(lnull$ (llist_of_tllist$ ?v0 )))):named a12 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 B_b_fun$ )(?v2 A_b_tllist$ ))(= (is_TNil$ (tmap$ ?v0 ?v1 ?v2 ))(is_TNil$ ?v2 ))):named a13 ))
(assert (! (forall ((?v0 B$ )(?v1 A_llist$ ))(= (is_TNil$ (tllist_of_llist$ ?v0 ?v1 ))(lnull$ ?v1 ))):named a14 ))
(assert (! (forall ((?v0 B$ )(?v1 A_llist$ ))(= (not (is_TNil$ (tllist_of_llist$ ?v0 ?v1 )))(not (lnull$ ?v1 )))):named a15 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (and (=> (lnull$ ?v0 )false )(=> (not (lnull$ ?v0 ))false ))false )):named a16 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 B$ ))(=> (lnull$ ?v0 )(is_TNil$ (tllist_of_llist$ ?v1 ?v0 )))):named a17 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 B$ ))(=> (not (lnull$ ?v0 ))(not (is_TNil$ (tllist_of_llist$ ?v1 ?v0 ))))):named a18 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_bool_fun$ ))(=> (and (=> (or (lnull$ ?v0 )(not (fun_app$a ?v1 (lhd$ ?v0 ))))false )(=> (and (not (lnull$ ?v0 ))(fun_app$a ?v1 (lhd$ ?v0 )))false ))false )):named a19 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (lnull$ ?v0 )(= ?v0 lNil$ )):pattern ((lnull$ ?v0 )))):named a20 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (= ?v0 lNil$ )(lnull$ ?v0 ))):named a21 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (lnull$ ?v0 )(= ?v0 lNil$ ))):named a22 ))
(assert (! (lnull$ lNil$ ):named a23 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ )(?v2 A_a_b_tllist_bool_fun_fun$ ))(=> (and (member$ ?v0 (tset$ ?v1 ))(and (forall ((?v3 A_b_tllist$ ))(=> (not (is_TNil$ ?v3 ))(fun_app$b (fun_app$c ?v2 (thd$ ?v3 ))?v3 )))(forall ((?v3 A_b_tllist$ )(?v4 A$ ))(=> (and (not (is_TNil$ ?v3 ))(and (member$ ?v4 (tset$ (ttl$ ?v3 )))(fun_app$b (fun_app$c ?v2 ?v4 )(ttl$ ?v3 ))))(fun_app$b (fun_app$c ?v2 ?v4 )?v3 )))))(fun_app$b (fun_app$c ?v2 ?v0 )?v1 ))):named a24 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 B$ ))(=> (lnull$ ?v0 )(= (terminal$ (tllist_of_llist$ ?v1 ?v0 ))?v1 ))):named a25 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (=> (or (lnull$ ?v0 )(lnull$ ?v1 ))false )(=> (and (not (lnull$ ?v0 ))(not (lnull$ ?v1 )))false ))false )):named a26 ))
(check-sat )
;(get-unsat-core )
