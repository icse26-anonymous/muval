;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort A_b_tllist_b_fun$ 0 )
(declare-codatatypes ()((A_b_tllist$ (tNil$ (terminal$ B$ ))(tCons$ (thd$ A$ )(ttl$ A_b_tllist$ )))(A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-fun b$ ()B$ )
(declare-fun uu$ ()A_b_tllist_b_fun$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun lnull$ (A_llist$ )Bool )
(declare-fun fun_app$ (A_b_tllist_b_fun$ A_b_tllist$ )B$ )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun terminal0$ ()A_b_tllist_b_fun$ )
(declare-fun lstrict_prefix$ (A_llist$ A_llist$ )Bool )
(declare-fun llist_of_tllist$ (A_b_tllist$ )A_llist$ )
(declare-fun tllist_of_llist$ (B$ A_llist$ )A_b_tllist$ )
(assert (! (forall ((?v0 A_b_tllist$ ))(! (= (fun_app$ uu$ ?v0 )(terminal$ ?v0 )):pattern ((fun_app$ uu$ ?v0 )))):named a0 ))
(assert (! (not (= (terminal$ (tllist_of_llist$ b$ xs$ ))b$ )):named a1 ))
(assert (! (lfinite$ xs$ ):named a2 ))
(assert (! (forall ((?v0 B$ )(?v1 A_llist$ )(?v2 B$ )(?v3 A_llist$ ))(= (= (tllist_of_llist$ ?v0 ?v1 )(tllist_of_llist$ ?v2 ?v3 ))(and (= ?v1 ?v3 )(=> (lfinite$ ?v3 )(= ?v0 ?v2 ))))):named a3 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 B$ )(?v3 B$ ))(=> (and (= ?v0 ?v1 )(=> (lfinite$ ?v1 )(= ?v2 ?v3 )))(= (tllist_of_llist$ ?v2 ?v0 )(tllist_of_llist$ ?v3 ?v1 )))):named a4 ))
(assert (! (= terminal0$ uu$ ):named a5 ))
(assert (! (forall ((?v0 A_b_tllist$ ))(= (tllist_of_llist$ (terminal$ ?v0 )(llist_of_tllist$ ?v0 ))?v0 )):named a6 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 B$ ))(=> (lnull$ ?v0 )(= (terminal$ (tllist_of_llist$ ?v1 ?v0 ))?v1 ))):named a7 ))
(assert (! (forall ((?v0 B$ )(?v1 A_llist$ ))(= (llist_of_tllist$ (tllist_of_llist$ ?v0 ?v1 ))?v1 )):named a8 ))
(assert (! (forall ((?v0 A_b_tllist$ ))(= (terminal$ (ttl$ ?v0 ))(terminal$ ?v0 ))):named a9 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ ))(! (= (terminal$ (tCons$ ?v0 ?v1 ))(terminal$ ?v1 )):pattern ((tCons$ ?v0 ?v1 )))):named a10 ))
(assert (! (forall ((?v0 B$ ))(! (= (terminal$ (tNil$ ?v0 ))?v0 ):pattern ((tNil$ ?v0 )))):named a11 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (lstrict_prefix$ ?v0 ?v1 )(lfinite$ ?v0 ))):named a12 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ ))(! (= (terminal$ (tCons$ ?v0 ?v1 ))(fun_app$ terminal0$ ?v1 )):pattern ((tCons$ ?v0 ?v1 )))):named a13 ))
(assert (! (= (lfinite$ lNil$ )true ):named a14 ))
(assert (! (forall ((?v0 B$ )(?v1 B$ ))(= (= (tNil$ ?v0 )(tNil$ ?v1 ))(= ?v0 ?v1 ))):named a15 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ )(?v2 A$ )(?v3 A_b_tllist$ ))(= (= (tCons$ ?v0 ?v1 )(tCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a16 ))
(assert (! (= (lstrict_prefix$ lNil$ lNil$ )false ):named a17 ))
(check-sat )
;(get-unsat-core )
