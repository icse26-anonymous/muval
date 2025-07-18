;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_llist_enat_fun$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-fun n$ ()Enat$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun min$ (Enat$ Enat$ )Enat$ )
(declare-fun lmap$ (A_a_fun$ A_llist$ )A_llist$ )
(declare-fun zero$ ()Enat$ )
(declare-fun epred$ (Enat$ )Enat$ )
(declare-fun ltake$ (Enat$ )A_llist_a_llist_fun$ )
(declare-fun zero$a ()Nat$ )
(declare-fun fun_app$ (A_llist_enat_fun$ A_llist$ )Enat$ )
(declare-fun llength$ ()A_llist_enat_fun$ )
(declare-fun fun_app$a (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun gen_llength$ (Nat$ )A_llist_enat_fun$ )
(assert (! (not (= (fun_app$ llength$ (fun_app$a (ltake$ n$ )xs$ ))(min$ n$ (fun_app$ llength$ xs$ )))):named a0 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ ))(= (min$ (min$ ?v0 ?v1 )?v1 )(min$ ?v0 ?v1 ))):named a1 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ ))(= (min$ ?v0 (min$ ?v0 ?v1 ))(min$ ?v0 ?v1 ))):named a2 ))
(assert (! (forall ((?v0 Enat$ ))(= (min$ ?v0 ?v0 )?v0 )):named a3 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ )(?v2 Enat$ ))(= (min$ (min$ ?v0 ?v1 )?v2 )(min$ ?v0 (min$ ?v1 ?v2 )))):named a4 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ )(?v2 Enat$ ))(= (min$ ?v0 (min$ ?v1 ?v2 ))(min$ ?v1 (min$ ?v0 ?v2 )))):named a5 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ ))(= (min$ ?v0 ?v1 )(min$ ?v1 ?v0 ))):named a6 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_llist$ ))(= (fun_app$ llength$ (lmap$ ?v0 ?v1 ))(fun_app$ llength$ ?v1 ))):named a7 ))
(assert (! (forall ((?v0 Enat$ ))(! (= (fun_app$a (ltake$ ?v0 )lNil$ )lNil$ ):pattern ((ltake$ ?v0 )))):named a8 ))
(assert (! (forall ((?v0 Enat$ ))(= (min$ ?v0 zero$ )zero$ )):named a9 ))
(assert (! (forall ((?v0 Enat$ ))(= (min$ zero$ ?v0 )zero$ )):named a10 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ ))(= (epred$ (min$ ?v0 ?v1 ))(min$ (epred$ ?v0 )(epred$ ?v1 )))):named a11 ))
(assert (! (= llength$ (gen_llength$ zero$a )):named a12 ))
(assert (! (= (fun_app$ llength$ lNil$ )zero$ ):named a13 ))
(assert (! (forall ((?v0 A_llist$ ))(= (fun_app$a (ltake$ zero$ )?v0 )lNil$ )):named a14 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_llist$ ))(= (= lNil$ (fun_app$a (ltake$ ?v0 )?v1 ))(or (= ?v1 lNil$ )(= ?v0 zero$ )))):named a15 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_llist$ ))(= (= (lmap$ ?v0 ?v1 )lNil$ )(= ?v1 lNil$ ))):named a16 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_llist$ ))(= (= lNil$ (lmap$ ?v0 ?v1 ))(= ?v1 lNil$ ))):named a17 ))
(check-sat )
;(get-unsat-core )
