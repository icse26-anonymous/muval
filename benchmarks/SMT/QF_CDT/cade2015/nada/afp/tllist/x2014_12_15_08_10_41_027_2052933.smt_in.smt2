;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort A_llist_a_b_tllist_fun$ 0 )
(declare-sort A_b_tllist$ 0)
(declare-sort A_llist$ 0)
(declare-fun terminal$ (A_b_tllist$)B$)
(declare-fun tNil$ (B$ )A_b_tllist$)
(declare-fun thd$ (A_b_tllist$)A$)
(declare-fun ttl$ (A_b_tllist$)A_b_tllist$)
(declare-fun tCons$ (A$ A_b_tllist$ )A_b_tllist$)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-fun b$ ()B$ )
(declare-fun b$a ()B$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun xs$a ()A_llist$ )
(declare-fun lnull$ (A_llist$ )Bool )
(declare-fun fun_app$ (A_llist_a_b_tllist_fun$ A_llist$ )A_b_tllist$ )
(declare-fun is_TNil$ (A_b_tllist$ )Bool )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun tllist_of_llist$ (B$ )A_llist_a_b_tllist_fun$ )
(assert (! (not (= (fun_app$ (tllist_of_llist$ b$ )xs$ )(fun_app$ (tllist_of_llist$ b$a )xs$ ))):named a0 ))
(assert (! (= xs$a xs$ ):named a1 ))
(assert (! (=> (lfinite$ xs$ )(= b$ b$a )):named a2 ))
(assert (! (=> (lfinite$ xs$ )(= b$ b$a )):named a3 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 B$ ))(=> (lnull$ ?v0 )(= (terminal$ (fun_app$ (tllist_of_llist$ ?v1 )?v0 ))?v1 ))):named a4 ))
(assert (! (forall ((?v0 B$ )(?v1 A_llist$ ))(= (thd$ (fun_app$ (tllist_of_llist$ ?v0 )?v1 ))(lhd$ ?v1 ))):named a5 ))
(assert (! (forall ((?v0 B$ ))(! (= (fun_app$ (tllist_of_llist$ ?v0 )lNil$ )(tNil$ ?v0 )):pattern ((tllist_of_llist$ ?v0 )))):named a6 ))
(assert (! (forall ((?v0 B$ )(?v1 A$ )(?v2 A_llist$ ))(! (= (fun_app$ (tllist_of_llist$ ?v0 )(lCons$ ?v1 ?v2 ))(tCons$ ?v1 (fun_app$ (tllist_of_llist$ ?v0 )?v2 ))):pattern ((fun_app$ (tllist_of_llist$ ?v0 )(lCons$ ?v1 ?v2 ))))):named a7 ))
(assert (! (forall ((?v0 B$ )(?v1 A_llist$ ))(= (ttl$ (fun_app$ (tllist_of_llist$ ?v0 )?v1 ))(fun_app$ (tllist_of_llist$ ?v0 )(ltl$ ?v1 )))):named a8 ))
(assert (! (forall ((?v0 B$ )(?v1 A_llist$ ))(= (not (is_TNil$ (fun_app$ (tllist_of_llist$ ?v0 )?v1 )))(not (lnull$ ?v1 )))):named a9 ))
(assert (! (forall ((?v0 B$ )(?v1 A_llist$ ))(= (is_TNil$ (fun_app$ (tllist_of_llist$ ?v0 )?v1 ))(lnull$ ?v1 ))):named a10 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 B$ ))(=> (not (lnull$ ?v0 ))(not (is_TNil$ (fun_app$ (tllist_of_llist$ ?v1 )?v0 ))))):named a11 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 B$ ))(=> (lnull$ ?v0 )(is_TNil$ (fun_app$ (tllist_of_llist$ ?v1 )?v0 )))):named a12 ))
(assert (! (forall ((?v0 B$ )(?v1 B$ ))(= (= (tNil$ ?v0 )(tNil$ ?v1 ))(= ?v0 ?v1 ))):named a13 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ )(?v2 A$ )(?v3 A_b_tllist$ ))(= (= (tCons$ ?v0 ?v1 )(tCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a14 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ ))(! (= (terminal$ (tCons$ ?v0 ?v1 ))(terminal$ ?v1 )):pattern ((tCons$ ?v0 ?v1 )))):named a15 ))
(assert (! (forall ((?v0 A_b_tllist$ ))(= (terminal$ (ttl$ ?v0 ))(terminal$ ?v0 ))):named a16 ))
(assert (! (forall ((?v0 A_b_tllist$ ))(=> (is_TNil$ ?v0 )(= (tNil$ (terminal$ ?v0 ))?v0 ))):named a17 ))
(check-sat )
;(get-unsat-core )
