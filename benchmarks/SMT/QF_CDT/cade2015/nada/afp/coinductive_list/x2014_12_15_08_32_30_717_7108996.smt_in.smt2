;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-sort A_llist_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-fun lNil$a ()A_llist_llist$)
(declare-fun lhd$a (A_llist_llist$)A_llist$)
(declare-fun ltl$a (A_llist_llist$)A_llist_llist$)
(declare-fun lCons$a (A_llist$ A_llist_llist$ )A_llist_llist$)
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
(declare-fun n$ ()Nat$ )
(declare-fun xss$ ()A_llist_llist$ )
(declare-fun enat$ (Nat$ )Enat$ )
(declare-fun less$ (Enat$ Enat$ )Bool )
(declare-fun xssa$ ()A_llist_llist$ )
(declare-fun zero$ ()Nat$ )
(declare-fun llast$ (A_llist$ )A$ )
(declare-fun lnull$ (A_llist$ )Bool )
(declare-fun lsetp$ (A_llist$ )A_bool_fun$ )
(declare-fun thesis$ ()Bool )
(declare-fun fun_app$ (A_bool_fun$ A$ )Bool )
(declare-fun lconcat$ (A_llist_llist$ )A_llist$ )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun lmember$ (A$ A_llist$ )Bool )
(declare-fun pred_llist$ (A_bool_fun$ A_llist$ )Bool )
(declare-fun lstrict_prefix$ (A_llist$ A_llist$ )Bool )
(assert (! (not thesis$ ):named a0 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(=> (= (lconcat$ xssa$ )(lCons$ ?v0 ?v1 ))thesis$ )):named a1 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a2 ))
(assert (! (not (lnull$ (lconcat$ xssa$ ))):named a3 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A$ )(?v2 A_llist$ ))(! (= (pred_llist$ ?v0 (lCons$ ?v1 ?v2 ))(and (fun_app$ ?v0 ?v1 )(pred_llist$ ?v0 ?v2 ))):pattern ((pred_llist$ ?v0 (lCons$ ?v1 ?v2 ))))):named a4 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A_llist$ ))(! (= (lmember$ ?v0 (lCons$ ?v1 ?v2 ))(or (= ?v0 ?v1 )(lmember$ ?v0 ?v2 ))):pattern ((lmember$ ?v0 (lCons$ ?v1 ?v2 ))))):named a5 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(! (= (lstrict_prefix$ (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(lstrict_prefix$ ?v1 ?v3 ))):pattern ((lstrict_prefix$ (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))))):named a6 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A$ ))(= (fun_app$ (lsetp$ ?v0 )?v1 )(or (exists ((?v2 A$ )(?v3 A_llist$ ))(and (= ?v0 (lCons$ ?v2 ?v3 ))(= ?v1 ?v2 )))(exists ((?v2 A_llist$ )(?v3 A$ )(?v4 A$ ))(and (= ?v0 (lCons$ ?v4 ?v2 ))(and (= ?v1 ?v3 )(fun_app$ (lsetp$ ?v2 )?v3 ))))))):named a7 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A$ ))(=> (and (fun_app$ (lsetp$ ?v0 )?v1 )(and (forall ((?v2 A$ )(?v3 A_llist$ ))(=> (and (= ?v0 (lCons$ ?v2 ?v3 ))(= ?v1 ?v2 ))false ))(forall ((?v2 A_llist$ )(?v3 A$ )(?v4 A$ ))(=> (and (= ?v0 (lCons$ ?v4 ?v2 ))(and (= ?v1 ?v3 )(fun_app$ (lsetp$ ?v2 )?v3 )))false ))))false )):named a8 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A$ )(?v2 A$ ))(=> (fun_app$ (lsetp$ ?v0 )?v1 )(fun_app$ (lsetp$ (lCons$ ?v2 ?v0 ))?v1 ))):named a9 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(fun_app$ (lsetp$ (lCons$ ?v0 ?v1 ))?v0 )):named a10 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A_llist$ ))(! (= (llast$ (lCons$ ?v0 (lCons$ ?v1 ?v2 )))(llast$ (lCons$ ?v1 ?v2 ))):pattern ((lCons$ ?v0 (lCons$ ?v1 ?v2 ))))):named a11 ))
(assert (! (less$ (enat$ zero$ )(llength$ (lconcat$ xssa$ ))):named a12 ))
(assert (! (less$ (enat$ n$ )(llength$ (lconcat$ xss$ ))):named a13 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (=> (or (lnull$ ?v0 )(lnull$ ?v1 ))false )(=> (and (not (lnull$ ?v0 ))(not (lnull$ ?v1 )))false ))false )):named a14 ))
(check-sat )
;(get-unsat-core )
