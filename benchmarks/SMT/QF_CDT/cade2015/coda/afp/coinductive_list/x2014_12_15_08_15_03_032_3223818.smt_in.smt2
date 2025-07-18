;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_a_llist_bool_fun_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
(declare-fun n$ ()Enat$ )
(declare-fun x$ ()A$ )
(declare-fun na$ ()Enat$ )
(declare-fun x$a ()A$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun xsa$ ()A_llist$ )
(declare-fun xsb$ ()A_llist$ )
(declare-fun lset$ (A_llist$ )A_set$ )
(declare-fun lsetp$ (A_llist$ A$ )Bool )
(declare-fun ltake$ (Enat$ A_llist$ )A_llist$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun lmember$ (A$ )A_llist_bool_fun$ )
(declare-fun fun_app$a (A_a_llist_bool_fun_fun$ A$ )A_llist_bool_fun$ )
(assert (! (not (member$ x$ (lset$ xsb$ ))):named a0 ))
(assert (! (not (= x$ x$a )):named a1 ))
(assert (! (member$ x$ (lset$ xsa$ )):named a2 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_llist$ ))(=> (= xsa$ (ltake$ ?v0 ?v1 ))(member$ x$ (lset$ ?v1 )))):named a3 ))
(assert (! (= (lCons$ x$a xsa$ )(ltake$ na$ xsb$ )):named a4 ))
(assert (! (member$ x$ (lset$ (ltake$ n$ xs$ ))):named a5 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A_a_llist_bool_fun_fun$ ))(=> (and (member$ ?v0 (lset$ ?v1 ))(and (forall ((?v3 A$ )(?v4 A_llist$ ))(fun_app$ (fun_app$a ?v2 ?v3 )(lCons$ ?v3 ?v4 )))(forall ((?v3 A$ )(?v4 A_llist$ )(?v5 A$ ))(=> (and (member$ ?v5 (lset$ ?v4 ))(fun_app$ (fun_app$a ?v2 ?v5 )?v4 ))(fun_app$ (fun_app$a ?v2 ?v5 )(lCons$ ?v3 ?v4 ))))))(fun_app$ (fun_app$a ?v2 ?v0 )?v1 ))):named a6 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(=> (and (member$ ?v0 (lset$ ?v1 ))(and (forall ((?v2 A_llist$ ))(=> (= ?v1 (lCons$ ?v0 ?v2 ))false ))(forall ((?v2 A$ )(?v3 A_llist$ ))(=> (and (= ?v1 (lCons$ ?v2 ?v3 ))(member$ ?v0 (lset$ ?v3 )))false ))))false )):named a7 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A_llist_bool_fun$ ))(=> (and (member$ ?v0 (lset$ ?v1 ))(and (forall ((?v3 A_llist$ ))(fun_app$ ?v2 (lCons$ ?v0 ?v3 )))(forall ((?v3 A$ )(?v4 A_llist$ ))(=> (and (member$ ?v0 (lset$ ?v4 ))(fun_app$ ?v2 ?v4 ))(fun_app$ ?v2 (lCons$ ?v3 ?v4 ))))))(fun_app$ ?v2 ?v1 ))):named a8 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A_llist_bool_fun$ ))(=> (and (member$ ?v0 (lset$ ?v1 ))(and (forall ((?v3 A_llist$ ))(fun_app$ ?v2 (lCons$ ?v0 ?v3 )))(forall ((?v3 A$ )(?v4 A_llist$ ))(=> (and (member$ ?v0 (lset$ ?v4 ))(and (not (= ?v0 ?v3 ))(fun_app$ ?v2 ?v4 )))(fun_app$ ?v2 (lCons$ ?v3 ?v4 ))))))(fun_app$ ?v2 ?v1 ))):named a9 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(=> (and (member$ ?v0 (lset$ ?v1 ))(and (forall ((?v2 A_llist$ ))(=> (= ?v1 (lCons$ ?v0 ?v2 ))false ))(forall ((?v2 A$ )(?v3 A_llist$ ))(=> (and (= ?v1 (lCons$ ?v2 ?v3 ))(member$ ?v0 (lset$ ?v3 )))false ))))false )):named a10 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ ))(=> (member$ ?v0 (lset$ ?v1 ))(member$ ?v0 (lset$ (lCons$ ?v2 ?v1 ))))):named a11 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ ))(=> (member$ ?v0 (lset$ ?v1 ))(member$ ?v0 (lset$ (lCons$ ?v2 ?v1 ))))):named a12 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(member$ ?v0 (lset$ (lCons$ ?v0 ?v1 )))):named a13 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(member$ ?v0 (lset$ (lCons$ ?v0 ?v1 )))):named a14 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(= (member$ ?v0 (lset$ ?v1 ))(fun_app$ (lmember$ ?v0 )?v1 ))):named a15 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a16 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(=> (member$ ?v0 (lset$ ?v1 ))(lsetp$ ?v1 ?v0 ))):named a17 ))
(check-sat )
;(get-unsat-core )
