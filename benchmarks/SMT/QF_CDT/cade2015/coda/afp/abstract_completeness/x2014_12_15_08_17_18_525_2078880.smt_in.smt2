;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort Nat$ 0 )
(declare-sort Rule$ 0 )
(declare-sort State$ 0 )
(declare-sort State_set$ 0 )
(declare-sort State_fset$ 0 )
(declare-sort Nat_nat_fun$ 0 )
(declare-sort State_fset_bool_fun$ 0 )
(declare-sort State_state_fset_bool_fun_fun$ 0 )
(declare-sort Rule_state_state_fset_bool_fun_fun_fun$ 0 )
(declare-codatatypes ()((Rule_stream$ (sCons$ (shd$ Rule$ )(stl$ Rule_stream$ )))))
(declare-fun r$ ()Rule$ )
(declare-fun s$ ()State_set$ )
(declare-fun s$a ()State$ )
(declare-fun s$b ()State$ )
(declare-fun sa$ ()State$ )
(declare-fun eff$ ()Rule_state_state_fset_bool_fun_fun_fun$ )
(declare-fun pos$ (Rule_stream$ Rule$ )Nat$ )
(declare-fun rsa$ ()Rule_stream$ )
(declare-fun suc$ (Nat$ )Nat$ )
(declare-fun less$ (Nat$ Nat$ )Bool )
(declare-fun minus$ (Nat$ )Nat_nat_fun$ )
(declare-fun member$ (State$ State_set$ )Bool )
(declare-fun enabled$ (Rule_state_state_fset_bool_fun_fun_fun$ Rule$ State$ )Bool )
(declare-fun fun_app$ (Nat_nat_fun$ Nat$ )Nat$ )
(declare-fun less_eq$ (Nat$ Nat$ )Bool )
(declare-fun minWait$ (Rule_state_state_fset_bool_fun_fun_fun$ Rule_stream$ State$ )Nat$ )
(declare-fun fun_app$a (State_fset_bool_fun$ State_fset$ )Bool )
(declare-fun fun_app$b (State_state_fset_bool_fun_fun$ State$ )State_fset_bool_fun$ )
(declare-fun fun_app$c (Rule_state_state_fset_bool_fun_fun_fun$ Rule$ )State_state_fset_bool_fun_fun$ )
(assert (! (not (less_eq$ (suc$ (fun_app$ (minus$ (pos$ rsa$ r$ ))(suc$ (minWait$ eff$ rsa$ sa$ ))))(pos$ rsa$ r$ ))):named a0 ))
(assert (! (less$ (minWait$ eff$ rsa$ sa$ )(pos$ rsa$ r$ )):named a1 ))
(assert (! (not (= (pos$ rsa$ r$ )(minWait$ eff$ rsa$ sa$ ))):named a2 ))
(assert (! (member$ sa$ s$ ):named a3 ))
(assert (! (enabled$ eff$ r$ sa$ ):named a4 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(=> (less_eq$ ?v0 ?v1 )(= (fun_app$ (minus$ ?v1 )(fun_app$ (minus$ ?v1 )?v0 ))?v0 ))):named a5 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (fun_app$ (minus$ (fun_app$ (minus$ (suc$ ?v0 ))?v1 ))(suc$ ?v2 ))(fun_app$ (minus$ (fun_app$ (minus$ ?v0 )?v1 ))?v2 ))):named a6 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(! (= (fun_app$ (minus$ (suc$ ?v0 ))(suc$ ?v1 ))(fun_app$ (minus$ ?v0 )?v1 )):pattern ((fun_app$ (minus$ (suc$ ?v0 ))(suc$ ?v1 ))))):named a7 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(! (= (less_eq$ (suc$ ?v0 )(suc$ ?v1 ))(less_eq$ ?v0 ?v1 )):pattern ((less_eq$ (suc$ ?v0 )(suc$ ?v1 ))))):named a8 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(! (=> (less_eq$ ?v0 ?v1 )(= (fun_app$ (minus$ (suc$ ?v1 ))?v0 )(suc$ (fun_app$ (minus$ ?v1 )?v0 )))):pattern ((fun_app$ (minus$ (suc$ ?v1 ))?v0 )))):named a9 ))
(assert (! (forall ((?v0 Nat_nat_fun$ )(?v1 Nat$ )(?v2 Nat$ ))(=> (and (forall ((?v3 Nat$ ))(less_eq$ (fun_app$ ?v0 (suc$ ?v3 ))(fun_app$ ?v0 ?v3 )))(less_eq$ ?v1 ?v2 ))(less_eq$ (fun_app$ ?v0 ?v2 )(fun_app$ ?v0 ?v1 )))):named a10 ))
(assert (! (forall ((?v0 Nat_nat_fun$ )(?v1 Nat$ )(?v2 Nat$ ))(=> (and (forall ((?v3 Nat$ ))(less_eq$ (fun_app$ ?v0 ?v3 )(fun_app$ ?v0 (suc$ ?v3 ))))(less_eq$ ?v1 ?v2 ))(less_eq$ (fun_app$ ?v0 ?v1 )(fun_app$ ?v0 ?v2 )))):named a11 ))
(assert (! (forall ((?v0 Rule$ )(?v1 State$ ))(! (= (enabled$ eff$ ?v0 ?v1 )(exists ((?v2 State_fset$ ))(fun_app$a (fun_app$b (fun_app$c eff$ ?v0 )?v1 )?v2 ))):pattern ((enabled$ eff$ ?v0 ?v1 )))):named a12 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (suc$ ?v0 )(suc$ ?v1 ))(= ?v0 ?v1 ))):named a13 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (suc$ ?v0 )(suc$ ?v1 ))(= ?v0 ?v1 ))):named a14 ))
(assert (! (member$ s$a s$ ):named a15 ))
(assert (! (member$ s$b s$ ):named a16 ))
(check-sat )
;(get-unsat-core )
