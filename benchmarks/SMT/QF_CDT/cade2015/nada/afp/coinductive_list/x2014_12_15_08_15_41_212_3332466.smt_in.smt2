;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort Enat_bool_fun$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-sort Enat_enat_bool_fun_fun$ 0 )
(declare-sort Enat_a_llist_prod_bool_fun$ 0 )
(declare-sort A_llist_a_llist_bool_fun_fun$ 0 )
(declare-sort Enat_a_llist_a_llist_fun_fun$ 0 )
(declare-sort Enat_a_llist_prod_a_llist_fun$ 0 )
(declare-sort Enat_a_llist_prod_enat_a_llist_prod_bool_fun_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-sort Enat_a_llist_prod$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
(declare-fun fst$ (Enat_a_llist_prod$)Enat$)
(declare-fun snd$ (Enat_a_llist_prod$)A_llist$)
(declare-fun pair$ (Enat$ A_llist$ )Enat_a_llist_prod$)
(declare-fun uu$ ()Enat_enat_bool_fun_fun$ )
(declare-fun uua$ ()A_llist_a_llist_bool_fun_fun$ )
(declare-fun uub$ ()Enat_a_llist_prod_enat_a_llist_prod_bool_fun_fun$ )
(declare-fun ltake$ ()Enat_a_llist_a_llist_fun_fun$ )
(declare-fun fun_app$ (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun less_eq$ ()Enat_enat_bool_fun_fun$ )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun lprefix$ ()A_llist_a_llist_bool_fun_fun$ )
(declare-fun fun_app$a (A_llist_a_llist_bool_fun_fun$ A_llist$ )A_llist_bool_fun$ )
(declare-fun fun_app$b (Enat_a_llist_prod_bool_fun$ Enat_a_llist_prod$ )Bool )
(declare-fun fun_app$c (Enat_a_llist_prod_enat_a_llist_prod_bool_fun_fun$ Enat_a_llist_prod$ )Enat_a_llist_prod_bool_fun$ )
(declare-fun fun_app$d (Enat_bool_fun$ Enat$ )Bool )
(declare-fun fun_app$e (Enat_enat_bool_fun_fun$ Enat$ )Enat_bool_fun$ )
(declare-fun fun_app$f (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun fun_app$g (Enat_a_llist_a_llist_fun_fun$ Enat$ )A_llist_a_llist_fun$ )
(declare-fun fun_app$h (Enat_a_llist_prod_a_llist_fun$ Enat_a_llist_prod$ )A_llist$ )
(declare-fun monotone$ (Enat_a_llist_prod_enat_a_llist_prod_bool_fun_fun$ A_llist_a_llist_bool_fun_fun$ Enat_a_llist_prod_a_llist_fun$ )Bool )
(declare-fun rel_prod$ (Enat_enat_bool_fun_fun$ A_llist_a_llist_bool_fun_fun$ )Enat_a_llist_prod_enat_a_llist_prod_bool_fun_fun$ )
(declare-fun case_prod$ (Enat_a_llist_a_llist_fun_fun$ )Enat_a_llist_prod_a_llist_fun$ )
(declare-fun lstrict_prefix$ (A_llist$ A_llist$ )Bool )
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (= (fun_app$ (fun_app$a uua$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$ (fun_app$a uua$ ?v0 )?v1 )))):named a0 ))
(assert (! (forall ((?v0 Enat_a_llist_prod$ )(?v1 Enat_a_llist_prod$ ))(! (= (fun_app$b (fun_app$c uub$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$b (fun_app$c uub$ ?v0 )?v1 )))):named a1 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ ))(! (= (fun_app$d (fun_app$e uu$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$d (fun_app$e uu$ ?v0 )?v1 )))):named a2 ))
(assert (! (not (monotone$ (rel_prod$ less_eq$ lprefix$ )lprefix$ (case_prod$ ltake$ ))):named a3 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v0 )):named a4 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v0 )):named a5 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_llist$ ))(fun_app$ (fun_app$a lprefix$ (fun_app$f (fun_app$g ltake$ ?v0 )?v1 ))?v1 )):named a6 ))
(assert (! (forall ((?v0 Enat_enat_bool_fun_fun$ )(?v1 Enat$ )(?v2 Enat$ ))(=> (and (forall ((?v3 Enat$ )(?v4 Enat$ ))(=> (fun_app$d (fun_app$e less_eq$ ?v3 )?v4 )(fun_app$d (fun_app$e ?v0 ?v3 )?v4 )))(=> (fun_app$d (fun_app$e ?v0 ?v1 )?v2 )(fun_app$d (fun_app$e ?v0 ?v2 )?v1 )))(fun_app$d (fun_app$e ?v0 ?v2 )?v1 ))):named a7 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_llist$ )(?v2 A_llist$ )(?v3 Enat$ ))(=> (and (= (fun_app$f (fun_app$g ltake$ ?v0 )?v1 )(fun_app$f (fun_app$g ltake$ ?v0 )?v2 ))(fun_app$d (fun_app$e less_eq$ ?v3 )?v0 ))(= (fun_app$f (fun_app$g ltake$ ?v3 )?v1 )(fun_app$f (fun_app$g ltake$ ?v3 )?v2 )))):named a8 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a9 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a10 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v2 )?v1 ))(or (fun_app$ (fun_app$a lprefix$ ?v0 )?v2 )(fun_app$ (fun_app$a lprefix$ ?v2 )?v0 )))):named a11 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v2 ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v2 ))):named a12 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v2 ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v2 ))):named a13 ))
(assert (! (forall ((?v0 Enat$ ))(fun_app$d (fun_app$e less_eq$ ?v0 )?v0 )):named a14 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (= (lstrict_prefix$ ?v0 ?v1 )(and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(not (= ?v0 ?v1 )))):pattern ((lstrict_prefix$ ?v0 ?v1 )))):named a15 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_llist$ )(?v2 Enat$ ))(= (fun_app$ (fun_app$a lprefix$ (fun_app$f (fun_app$g ltake$ ?v0 )?v1 ))(fun_app$f (fun_app$g ltake$ ?v2 )?v1 ))(or (fun_app$d (fun_app$e less_eq$ ?v0 )?v2 )(fun_app$d (fun_app$e less_eq$ (llength$ ?v1 ))?v2 )))):named a16 ))
(assert (! (= (rel_prod$ uu$ uua$ )uub$ ):named a17 ))
(assert (! (forall ((?v0 Enat_a_llist_prod_enat_a_llist_prod_bool_fun_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ )(?v2 Enat_a_llist_prod_a_llist_fun$ ))(= (monotone$ ?v0 ?v1 ?v2 )(forall ((?v3 Enat_a_llist_prod$ )(?v4 Enat_a_llist_prod$ ))(=> (fun_app$b (fun_app$c ?v0 ?v3 )?v4 )(fun_app$ (fun_app$a ?v1 (fun_app$h ?v2 ?v3 ))(fun_app$h ?v2 ?v4 )))))):named a18 ))
(assert (! (forall ((?v0 Enat_a_llist_prod_enat_a_llist_prod_bool_fun_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ )(?v2 Enat_a_llist_prod_a_llist_fun$ ))(=> (forall ((?v3 Enat_a_llist_prod$ )(?v4 Enat_a_llist_prod$ ))(=> (fun_app$b (fun_app$c ?v0 ?v3 )?v4 )(fun_app$ (fun_app$a ?v1 (fun_app$h ?v2 ?v3 ))(fun_app$h ?v2 ?v4 ))))(monotone$ ?v0 ?v1 ?v2 ))):named a19 ))
(check-sat )
;(get-unsat-core )
