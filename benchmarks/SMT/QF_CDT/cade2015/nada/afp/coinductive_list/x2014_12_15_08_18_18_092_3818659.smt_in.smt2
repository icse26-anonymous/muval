;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort Nat_nat_fun$ 0 )
(declare-sort Enat_bool_fun$ 0 )
(declare-sort Enat_enat_bool_fun_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
(declare-fun uu$ ()Nat_nat_fun$ )
(declare-fun xsa$ ()A_llist$ )
(declare-fun enat$ (Nat$ )Enat$ )
(declare-fun lnth$ (A_llist$ Nat$ )A$ )
(declare-fun zero$ ()Nat$ )
(declare-fun minus$ (Nat$ )Nat_nat_fun$ )
(declare-fun fun_app$ (Nat_nat_fun$ Nat$ )Nat$ )
(declare-fun less_eq$ (Enat$ Enat$ )Bool )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun fun_app$a (Enat_bool_fun$ Enat$ )Bool )
(declare-fun fun_app$b (Enat_enat_bool_fun_fun$ Enat$ )Enat_bool_fun$ )
(declare-fun case_enat$ (Nat_nat_fun$ Nat$ Enat$ )Nat$ )
(declare-fun undefined$ (Nat$ )A$ )
(declare-fun undefined$a ()Nat$ )
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$ uu$ ?v0 )?v0 ):pattern ((fun_app$ uu$ ?v0 )))):named a0 ))
(assert (! (not (= (lnth$ xsa$ zero$ )(undefined$ (fun_app$ (minus$ zero$ )(case_enat$ uu$ undefined$a (llength$ xsa$ )))))):named a1 ))
(assert (! (less_eq$ (llength$ xsa$ )(enat$ zero$ )):named a2 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$ (minus$ ?v0 )?v0 )zero$ ):pattern ((minus$ ?v0 )))):named a3 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$ (minus$ zero$ )?v0 )zero$ ):pattern ((fun_app$ (minus$ zero$ )?v0 )))):named a4 ))
(assert (! (forall ((?v0 Nat$ ))(= (fun_app$ (minus$ ?v0 )zero$ )?v0 )):named a5 ))
(assert (! (forall ((?v0 Nat$ ))(= (fun_app$ (minus$ ?v0 )zero$ )?v0 )):named a6 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$ (minus$ ?v0 )?v0 )zero$ ):pattern ((minus$ ?v0 )))):named a7 ))
(assert (! (forall ((?v0 Nat$ ))(= (fun_app$ (minus$ zero$ )?v0 )zero$ )):named a8 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$ (minus$ ?v0 )zero$ )?v0 ):pattern ((minus$ ?v0 )))):named a9 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(=> (and (= (fun_app$ (minus$ ?v0 )?v1 )zero$ )(= (fun_app$ (minus$ ?v1 )?v0 )zero$ ))(= ?v0 ?v1 ))):named a10 ))
(assert (! (forall ((?v0 Enat_enat_bool_fun_fun$ )(?v1 Enat$ )(?v2 Enat$ ))(=> (and (forall ((?v3 Enat$ )(?v4 Enat$ ))(=> (less_eq$ ?v3 ?v4 )(fun_app$a (fun_app$b ?v0 ?v3 )?v4 )))(=> (fun_app$a (fun_app$b ?v0 ?v1 )?v2 )(fun_app$a (fun_app$b ?v0 ?v2 )?v1 )))(fun_app$a (fun_app$b ?v0 ?v2 )?v1 ))):named a11 ))
(check-sat )
;(get-unsat-core )
