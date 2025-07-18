;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort Nat$ 0 )
(declare-sort Rule$ 0 )
(declare-sort State$ 0 )
(declare-sort Rule_set$ 0 )
(declare-sort State_set$ 0 )
(declare-sort State_fset$ 0 )
(declare-sort State_fset_bool_fun$ 0 )
(declare-sort State_rule_prod_tree$ 0 )
(declare-sort State_rule_prod_bool_fun$ 0 )
(declare-sort State_state_fset_bool_fun_fun$ 0 )
(declare-sort State_rule_prod_stream_bool_fun$ 0 )
(declare-sort Rule_state_state_fset_bool_fun_fun_fun$ 0 )
(declare-sort State_rule_prod$ 0)
(declare-fun fst$ (State_rule_prod$)State$)
(declare-fun snd$ (State_rule_prod$)Rule$)
(declare-fun pair$ (State$ Rule$ )State_rule_prod$)
(declare-codatatypes ()((Rule_stream$ (sCons$ (shd$ Rule$ )(stl$ Rule_stream$ )))(State_rule_prod_stream$ (sCons$a (shd$a State_rule_prod$ )(stl$a State_rule_prod_stream$ )))))
(declare-fun r$ ()Rule$ )
(declare-fun s$ ()State_set$ )
(declare-fun rs$ ()Rule_stream$ )
(declare-fun s$a ()State$ )
(declare-fun s$b ()State$ )
(declare-fun sa$ ()State$ )
(declare-fun uu$ ()State_rule_prod_bool_fun$ )
(declare-fun alw$ (State_rule_prod_stream_bool_fun$ State_rule_prod_stream$ )Bool )
(declare-fun eff$ ()Rule_state_state_fset_bool_fun_fun_fun$ )
(declare-fun pos$ (Rule_stream$ Rule$ )Nat$ )
(declare-fun rsa$ ()Rule_stream$ )
(declare-fun root$ (State_rule_prod_tree$ )State_rule_prod$ )
(declare-fun sset$ (Rule_stream$ )Rule_set$ )
(declare-fun trim$ (Rule_state_state_fset_bool_fun_fun_fun$ Rule_stream$ State$ )Rule_stream$ )
(declare-fun holds$ (State_rule_prod_bool_fun$ )State_rule_prod_stream_bool_fun$ )
(declare-fun ipath$ (State_rule_prod_tree$ State_rule_prod_stream$ )Bool )
(declare-fun rules$ ()Rule_stream$ )
(declare-fun sdrop$ (Nat$ Rule_stream$ )Rule_stream$ )
(declare-fun steps$ ()State_rule_prod_stream$ )
(declare-fun member$ (State$ State_set$ )Bool )
(declare-fun mkTree$ (Rule_state_state_fset_bool_fun_fun_fun$ Rule_stream$ State$ )State_rule_prod_tree$ )
(declare-fun stepsa$ ()State_rule_prod_stream$ )
(declare-fun enabled$ (Rule_state_state_fset_bool_fun_fun_fun$ Rule$ State$ )Bool )
(declare-fun fun_app$ (State_rule_prod_bool_fun$ State_rule_prod$ )Bool )
(declare-fun less_eq$ (Nat$ Nat$ )Bool )
(declare-fun member$a (Rule$ Rule_set$ )Bool )
(declare-fun minWait$ (Rule_state_state_fset_bool_fun_fun_fun$ Rule_stream$ State$ )Nat$ )
(declare-fun pickEff$ (Rule_state_state_fset_bool_fun_fun_fun$ Rule$ State$ )State_fset$ )
(declare-fun fun_app$a (State_fset_bool_fun$ State_fset$ )Bool )
(declare-fun fun_app$b (State_state_fset_bool_fun_fun$ State$ )State_fset_bool_fun$ )
(declare-fun fun_app$c (Rule_state_state_fset_bool_fun_fun_fun$ Rule$ )State_state_fset_bool_fun_fun$ )
(assert (! (forall ((?v0 State_rule_prod$ ))(! (= (fun_app$ uu$ ?v0 )(enabled$ eff$ r$ (fst$ ?v0 ))):pattern ((fun_app$ uu$ ?v0 )))):named a0 ))
(assert (! (not (enabled$ eff$ r$ sa$ )):named a1 ))
(assert (! (forall ((?v0 Rule$ )(?v1 State$ ))(! (= (enabled$ eff$ ?v0 ?v1 )(exists ((?v2 State_fset$ ))(fun_app$a (fun_app$b (fun_app$c eff$ ?v0 )?v1 )?v2 ))):pattern ((enabled$ eff$ ?v0 ?v1 )))):named a2 ))
(assert (! (= (root$ (mkTree$ eff$ rsa$ sa$ ))(shd$a stepsa$ )):named a3 ))
(assert (! (member$ sa$ s$ ):named a4 ))
(assert (! (forall ((?v0 Rule$ )(?v1 State$ ))(=> (enabled$ eff$ ?v0 ?v1 )(fun_app$a (fun_app$b (fun_app$c eff$ ?v0 )?v1 )(pickEff$ eff$ ?v0 ?v1 )))):named a5 ))
(assert (! (forall ((?v0 Rule_state_state_fset_bool_fun_fun_fun$ )(?v1 Rule$ )(?v2 State$ ))(! (= (enabled$ ?v0 ?v1 ?v2 )(exists ((?v3 State_fset$ ))(fun_app$a (fun_app$b (fun_app$c ?v0 ?v1 )?v2 )?v3 ))):pattern ((enabled$ ?v0 ?v1 ?v2 )))):named a6 ))
(assert (! (ipath$ (mkTree$ eff$ rsa$ sa$ )stepsa$ ):named a7 ))
(assert (! (not (= (pos$ rsa$ r$ )(minWait$ eff$ rsa$ sa$ ))):named a8 ))
(assert (! (alw$ (holds$ uu$ )stepsa$ ):named a9 ))
(assert (! (forall ((?v0 Rule_state_state_fset_bool_fun_fun_fun$ )(?v1 Rule$ )(?v2 State$ ))(=> (enabled$ ?v0 ?v1 ?v2 )(fun_app$a (fun_app$b (fun_app$c ?v0 ?v1 )?v2 )(pickEff$ ?v0 ?v1 ?v2 )))):named a10 ))
(assert (! (alw$ (holds$ uu$ )steps$ ):named a11 ))
(assert (! (ipath$ (mkTree$ eff$ rs$ s$a )steps$ ):named a12 ))
(assert (! (= (trim$ eff$ rsa$ sa$ )(sdrop$ (minWait$ eff$ rsa$ sa$ )rsa$ )):named a13 ))
(assert (! (member$a r$ (sset$ rules$ )):named a14 ))
(assert (! (member$ s$a s$ ):named a15 ))
(assert (! (member$ s$b s$ ):named a16 ))
(assert (! (ipath$ (mkTree$ eff$ (stl$ (trim$ eff$ rsa$ sa$ ))s$b )(stl$a stepsa$ )):named a17 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Rule_stream$ )(?v2 State$ ))(=> (enabled$ eff$ (shd$ (sdrop$ ?v0 ?v1 ))?v2 )(less_eq$ (minWait$ eff$ ?v1 ?v2 )?v0 ))):named a18 ))
(check-sat )
;(get-unsat-core )
