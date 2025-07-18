;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort Nat$ 0 )
(declare-sort Nat_nat_fun$ 0 )
(declare-codatatypes ()((Nat_llist$ (lNil$ )(lCons$ (lhd$ Nat$ )(ltl$ Nat_llist$ )))))
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-sort Nat_list$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
(declare-fun nil$ ()Nat_list$)
(declare-fun hd$ (Nat_list$)Nat$)
(declare-fun tl$ (Nat_list$)Nat_list$)
(declare-fun cons$ (Nat$ Nat_list$ )Nat_list$)
(declare-fun m$ ()Nat$ )
(declare-fun n$ ()Nat$ )
(declare-fun suc$ ()Nat_nat_fun$ )
(declare-fun upt$ (Nat$ Nat$ )Nat_list$ )
(declare-fun enat$ (Nat$ )Enat$ )
(declare-fun plus$ (Nat$ Nat$ )Nat$ )
(declare-fun take$ (Nat$ Nat_list$ )Nat_list$ )
(declare-fun ltake$ (Enat$ Nat_llist$ )Nat_llist$ )
(declare-fun plus$a (Enat$ Enat$ )Enat$ )
(declare-fun fun_app$ (Nat_nat_fun$ Nat$ )Nat$ )
(declare-fun iterates$ (Nat_nat_fun$ Nat$ )Nat_llist$ )
(declare-fun llist_of$ (Nat_list$ )Nat_llist$ )
(assert (! (not (= (ltake$ (enat$ n$ )(iterates$ suc$ m$ ))(llist_of$ (upt$ m$ (plus$ n$ m$ ))))):named a0 ))
(assert (! (forall ((?v0 Nat_list$ )(?v1 Nat_list$ ))(= (= (llist_of$ ?v0 )(llist_of$ ?v1 ))(= ?v0 ?v1 ))):named a1 ))
(assert (! (forall ((?v0 Nat_llist$ )(?v1 Nat_llist$ ))(=> (forall ((?v2 Nat$ ))(= (ltake$ (enat$ ?v2 )?v0 )(ltake$ (enat$ ?v2 )?v1 )))(= ?v0 ?v1 ))):named a2 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(! (= (plus$ ?v0 (fun_app$ suc$ ?v1 ))(fun_app$ suc$ (plus$ ?v0 ?v1 ))):pattern ((plus$ ?v0 (fun_app$ suc$ ?v1 ))))):named a3 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (enat$ ?v0 )(enat$ ?v1 ))(= ?v0 ?v1 ))):named a4 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (fun_app$ suc$ ?v0 )(fun_app$ suc$ ?v1 ))(= ?v0 ?v1 ))):named a5 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (fun_app$ suc$ ?v0 )(fun_app$ suc$ ?v1 ))(= ?v0 ?v1 ))):named a6 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (= (plus$ ?v0 ?v1 )(plus$ ?v2 ?v1 ))(= ?v0 ?v2 ))):named a7 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (= (plus$ ?v0 ?v1 )(plus$ ?v0 ?v2 ))(= ?v1 ?v2 ))):named a8 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(! (= (plus$ (fun_app$ suc$ ?v0 )?v1 )(plus$ ?v0 (fun_app$ suc$ ?v1 ))):pattern ((plus$ (fun_app$ suc$ ?v0 )?v1 )))):named a9 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(! (= (plus$ (fun_app$ suc$ ?v0 )?v1 )(fun_app$ suc$ (plus$ ?v0 ?v1 ))):pattern ((plus$ (fun_app$ suc$ ?v0 )?v1 )))):named a10 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat_list$ ))(= (ltake$ (enat$ ?v0 )(llist_of$ ?v1 ))(llist_of$ (take$ ?v0 ?v1 )))):named a11 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (= (plus$ ?v0 ?v1 )(plus$ ?v2 ?v1 ))(= ?v0 ?v2 ))):named a12 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (= (plus$ ?v0 ?v1 )(plus$ ?v0 ?v2 ))(= ?v1 ?v2 ))):named a13 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(! (= (plus$a (enat$ ?v0 )(enat$ ?v1 ))(enat$ (plus$ ?v0 ?v1 ))):pattern ((plus$a (enat$ ?v0 )(enat$ ?v1 ))))):named a14 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ )(?v3 Nat$ ))(=> (and (= ?v0 ?v1 )(= ?v2 ?v3 ))(= (plus$ ?v0 ?v2 )(plus$ ?v1 ?v3 )))):named a15 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ )(?v2 Enat$ )(?v3 Enat$ ))(=> (and (= ?v0 ?v1 )(= ?v2 ?v3 ))(= (plus$a ?v0 ?v2 )(plus$a ?v1 ?v3 )))):named a16 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(=> (= (plus$ ?v0 ?v1 )(plus$ ?v0 ?v2 ))(= ?v1 ?v2 ))):named a17 ))
(check-sat )
;(get-unsat-core )
