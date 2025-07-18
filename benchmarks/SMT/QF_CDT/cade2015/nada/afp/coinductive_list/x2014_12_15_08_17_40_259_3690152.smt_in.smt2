;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort Nat_nat_fun$ 0 )
(declare-sort Enat_enat_fun$ 0 )
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
(declare-fun xsa$ ()A_llist$ )
(declare-fun enat$ (Nat$ )Enat$ )
(declare-fun zero$ ()Nat$ )
(declare-fun minus$ (Enat$ )Enat_enat_fun$ )
(declare-fun zero$a ()Enat$ )
(declare-fun ldropn$ (Nat$ A_llist$ )A_llist$ )
(declare-fun minus$a (Nat$ )Nat_nat_fun$ )
(declare-fun fun_app$ (Enat_enat_fun$ Enat$ )Enat$ )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun fun_app$a (Nat_nat_fun$ Nat$ )Nat$ )
(assert (! (not (= (llength$ (ldropn$ zero$ xsa$ ))(fun_app$ (minus$ (llength$ xsa$ ))(enat$ zero$ )))):named a0 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (ldropn$ zero$ ?v0 )?v0 ):pattern ((ldropn$ zero$ ?v0 )))):named a1 ))
(assert (! (forall ((?v0 Enat$ ))(! (= (fun_app$ (minus$ (enat$ zero$ ))?v0 )(enat$ zero$ )):pattern ((fun_app$ (minus$ (enat$ zero$ ))?v0 )))):named a2 ))
(assert (! (forall ((?v0 Enat$ ))(! (= (fun_app$ (minus$ ?v0 )(enat$ zero$ ))?v0 ):pattern ((minus$ ?v0 )))):named a3 ))
(assert (! (forall ((?v0 Nat$ ))(= (fun_app$a (minus$a ?v0 )zero$ )?v0 )):named a4 ))
(assert (! (forall ((?v0 Nat$ ))(= (fun_app$a (minus$a ?v0 )zero$ )?v0 )):named a5 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$a (minus$a ?v0 )?v0 )zero$ ):pattern ((minus$a ?v0 )))):named a6 ))
(assert (! (forall ((?v0 Nat$ ))(= (fun_app$a (minus$a zero$ )?v0 )zero$ )):named a7 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (enat$ ?v0 )(enat$ ?v1 ))(= ?v0 ?v1 ))):named a8 ))
(assert (! (forall ((?v0 Enat$ ))(= (fun_app$ (minus$ zero$a )?v0 )zero$a )):named a9 ))
(assert (! (forall ((?v0 Enat$ ))(= (fun_app$ (minus$ ?v0 )zero$a )?v0 )):named a10 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(! (= (fun_app$ (minus$ (enat$ ?v0 ))(enat$ ?v1 ))(enat$ (fun_app$a (minus$a ?v0 )?v1 ))):pattern ((fun_app$ (minus$ (enat$ ?v0 ))(enat$ ?v1 ))))):named a11 ))
(assert (! (= zero$a (enat$ zero$ )):named a12 ))
(check-sat )
;(get-unsat-core )
