;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort Nat$ 0 )
(declare-sort Rule$ 0 )
(declare-sort State$ 0 )
(declare-sort Rule_set$ 0 )
(declare-sort Rule_fset$ 0 )
(declare-sort State_set$ 0 )
(declare-sort State_fset$ 0 )
(declare-sort Rule_fset_bool_fun$ 0 )
(declare-sort State_fset_bool_fun$ 0 )
(declare-sort State_rule_prod_tree$ 0 )
(declare-sort Rule_rule_fset_bool_fun_fun$ 0 )
(declare-sort State_state_fset_bool_fun_fun$ 0 )
(declare-sort Rule_rule_rule_fset_bool_fun_fun_fun$ 0 )
(declare-sort State_rule_rule_fset_bool_fun_fun_fun$ 0 )
(declare-sort Rule_state_state_fset_bool_fun_fun_fun$ 0 )
(declare-sort State_state_state_fset_bool_fun_fun_fun$ 0 )
(declare-codatatypes ()((Rule_stream$ (sCons$ (shd$ Rule$ )(stl$ Rule_stream$ )))))
(declare-sort State_rule_prod$ 0)
(declare-fun fst$ (State_rule_prod$)State$)
(declare-fun snd$ (State_rule_prod$)Rule$)
(declare-fun pair$ (State$ Rule$ )State_rule_prod$)
(declare-codatatypes ()((State_rule_prod_stream$ (sCons$a (shd$a State_rule_prod$ )(stl$a State_rule_prod_stream$ )))(State_stream$ (sCons$b (shd$b State$ )(stl$b State_stream$ )))))
(declare-fun s$ ()State$ )
(declare-fun rs$ ()Rule_stream$ )
(declare-fun s$a ()State_set$ )
(declare-fun wf$ (Rule_state_state_fset_bool_fun_fun_fun$ Rule_stream$ State_rule_prod_tree$ )Bool )
(declare-fun bot$ ()Rule_set$ )
(declare-fun eff$ ()Rule_state_state_fset_bool_fun_fun_fun$ )
(declare-fun fair$ (Rule_stream$ Rule_stream$ )Bool )
(declare-fun sset$ (Rule_stream$ )Rule_set$ )
(declare-fun epath$ (Rule_state_state_fset_bool_fun_fun_fun$ Rule_stream$ State_rule_prod_stream$ )Bool )
(declare-fun fenum$ (Rule_stream$ )Rule_stream$ )
(declare-fun ipath$ (State_rule_prod_tree$ State_rule_prod_stream$ )Bool )
(declare-fun rules$ ()Rule_stream$ )
(declare-fun sdrop$ (Nat$ Rule_stream$ )Rule_stream$ )
(declare-fun sset$a (State_stream$ )State_set$ )
(declare-fun fenum$a (State_stream$ )State_stream$ )
(declare-fun member$ (Rule$ Rule_set$ )Bool )
(declare-fun thesis$ ()Bool )
(declare-fun enabled$ (Rule_state_state_fset_bool_fun_fun_fun$ Rule$ State$ )Bool )
(declare-fun fmember$ (State$ State_fset$ )Bool )
(declare-fun fun_app$ (State_fset_bool_fun$ State_fset$ )Bool )
(declare-fun member$a (State$ State_set$ )Bool )
(declare-fun pickEff$ (Rule_state_state_fset_bool_fun_fun_fun$ Rule$ State$ )State_fset$ )
(declare-fun fun_app$a (State_state_fset_bool_fun_fun$ State$ )State_fset_bool_fun$ )
(declare-fun fun_app$b (Rule_state_state_fset_bool_fun_fun_fun$ Rule$ )State_state_fset_bool_fun_fun$ )
(declare-fun fun_app$c (Rule_fset_bool_fun$ Rule_fset$ )Bool )
(declare-fun fun_app$d (Rule_rule_fset_bool_fun_fun$ Rule$ )Rule_fset_bool_fun$ )
(declare-fun fun_app$e (State_rule_rule_fset_bool_fun_fun_fun$ State$ )Rule_rule_fset_bool_fun_fun$ )
(declare-fun fun_app$f (State_state_state_fset_bool_fun_fun_fun$ State$ )State_state_fset_bool_fun_fun$ )
(declare-fun fun_app$g (Rule_rule_rule_fset_bool_fun_fun_fun$ Rule$ )Rule_rule_fset_bool_fun_fun$ )
(declare-fun countable$ (Rule_set$ )Bool )
(declare-fun saturated$ (Rule_state_state_fset_bool_fun_fun_fun$ Rule_stream$ State_rule_prod_stream$ )Bool )
(declare-fun ruleSystem$ (State_rule_rule_fset_bool_fun_fun_fun$ State_stream$ Rule_set$ )Bool )
(declare-fun saturated$a (Rule_state_state_fset_bool_fun_fun_fun$ Rule$ State_rule_prod_stream$ )Bool )
(declare-fun ruleSystem$a (State_state_state_fset_bool_fun_fun_fun$ State_stream$ State_set$ )Bool )
(declare-fun ruleSystem$b (Rule_rule_rule_fset_bool_fun_fun_fun$ Rule_stream$ Rule_set$ )Bool )
(declare-fun ruleSystem$c (Rule_state_state_fset_bool_fun_fun_fun$ Rule_stream$ State_set$ )Bool )
(assert (! (not thesis$ ):named a0 ))
(assert (! (forall ((?v0 Rule$ )(?v1 State_fset$ ))(=> (and (member$ ?v0 (sset$ rules$ ))(fun_app$ (fun_app$a (fun_app$b eff$ ?v0 )s$ )?v1 ))thesis$ )):named a1 ))
(assert (! (exists ((?v0 Rule$ ))(and (member$ ?v0 (sset$ rules$ ))(exists ((?v1 State_fset$ ))(fun_app$ (fun_app$a (fun_app$b eff$ ?v0 )s$ )?v1 )))):named a2 ))
(assert (! (member$a s$ s$a ):named a3 ))
(assert (! (fair$ rules$ rs$ ):named a4 ))
(assert (! (= (sset$ (fenum$ rules$ ))(sset$ rules$ )):named a5 ))
(assert (! (forall ((?v0 State$ ))(=> (member$a ?v0 s$a )(exists ((?v1 Rule$ ))(and (member$ ?v1 (sset$ rules$ ))(exists ((?v2 State_fset$ ))(fun_app$ (fun_app$a (fun_app$b eff$ ?v1 )?v0 )?v2 )))))):named a6 ))
(assert (! (forall ((?v0 State_rule_prod_stream$ ))(= (saturated$ eff$ rules$ ?v0 )(forall ((?v1 Rule$ ))(=> (member$ ?v1 (sset$ rules$ ))(saturated$a eff$ ?v1 ?v0 ))))):named a7 ))
(assert (! (forall ((?v0 Rule$ )(?v1 State$ ))(! (= (enabled$ eff$ ?v0 ?v1 )(exists ((?v2 State_fset$ ))(fun_app$ (fun_app$a (fun_app$b eff$ ?v0 )?v1 )?v2 ))):pattern ((enabled$ eff$ ?v0 ?v1 )))):named a8 ))
(assert (! (not (= (sset$ rules$ )bot$ )):named a9 ))
(assert (! (countable$ (sset$ rules$ )):named a10 ))
(assert (! (forall ((?v0 State$ )(?v1 Rule$ )(?v2 State_fset$ )(?v3 State$ ))(=> (and (member$a ?v0 s$a )(and (member$ ?v1 (sset$ rules$ ))(and (fun_app$ (fun_app$a (fun_app$b eff$ ?v1 )?v0 )?v2 )(fmember$ ?v3 ?v2 ))))(member$a ?v3 s$a ))):named a11 ))
(assert (! (forall ((?v0 State_stream$ ))(= (sset$a (fenum$a ?v0 ))(sset$a ?v0 ))):named a12 ))
(assert (! (forall ((?v0 Rule_stream$ ))(= (sset$ (fenum$ ?v0 ))(sset$ ?v0 ))):named a13 ))
(assert (! (fair$ rules$ (fenum$ rules$ )):named a14 ))
(assert (! (forall ((?v0 State_rule_rule_fset_bool_fun_fun_fun$ )(?v1 State_stream$ )(?v2 Rule_set$ )(?v3 Rule$ ))(=> (and (ruleSystem$ ?v0 ?v1 ?v2 )(member$ ?v3 ?v2 ))(exists ((?v4 State$ ))(and (member$a ?v4 (sset$a ?v1 ))(exists ((?v5 Rule_fset$ ))(fun_app$c (fun_app$d (fun_app$e ?v0 ?v4 )?v3 )?v5 )))))):named a15 ))
(assert (! (forall ((?v0 State_state_state_fset_bool_fun_fun_fun$ )(?v1 State_stream$ )(?v2 State_set$ )(?v3 State$ ))(=> (and (ruleSystem$a ?v0 ?v1 ?v2 )(member$a ?v3 ?v2 ))(exists ((?v4 State$ ))(and (member$a ?v4 (sset$a ?v1 ))(exists ((?v5 State_fset$ ))(fun_app$ (fun_app$a (fun_app$f ?v0 ?v4 )?v3 )?v5 )))))):named a16 ))
(assert (! (forall ((?v0 Rule_rule_rule_fset_bool_fun_fun_fun$ )(?v1 Rule_stream$ )(?v2 Rule_set$ )(?v3 Rule$ ))(=> (and (ruleSystem$b ?v0 ?v1 ?v2 )(member$ ?v3 ?v2 ))(exists ((?v4 Rule$ ))(and (member$ ?v4 (sset$ ?v1 ))(exists ((?v5 Rule_fset$ ))(fun_app$c (fun_app$d (fun_app$g ?v0 ?v4 )?v3 )?v5 )))))):named a17 ))
(assert (! (forall ((?v0 Rule_state_state_fset_bool_fun_fun_fun$ )(?v1 Rule_stream$ )(?v2 State_set$ )(?v3 State$ ))(=> (and (ruleSystem$c ?v0 ?v1 ?v2 )(member$a ?v3 ?v2 ))(exists ((?v4 Rule$ ))(and (member$ ?v4 (sset$ ?v1 ))(exists ((?v5 State_fset$ ))(fun_app$ (fun_app$a (fun_app$b ?v0 ?v4 )?v3 )?v5 )))))):named a18 ))
(assert (! (forall ((?v0 Rule_state_state_fset_bool_fun_fun_fun$ )(?v1 Rule_stream$ )(?v2 State_rule_prod_stream$ ))(= (saturated$ ?v0 ?v1 ?v2 )(forall ((?v3 Rule$ ))(=> (member$ ?v3 (sset$ ?v1 ))(saturated$a ?v0 ?v3 ?v2 ))))):named a19 ))
(assert (! (forall ((?v0 Rule$ )(?v1 State$ ))(=> (enabled$ eff$ ?v0 ?v1 )(fun_app$ (fun_app$a (fun_app$b eff$ ?v0 )?v1 )(pickEff$ eff$ ?v0 ?v1 )))):named a20 ))
(assert (! (forall ((?v0 State_rule_prod_tree$ )(?v1 State_rule_prod_stream$ ))(=> (and (wf$ eff$ rules$ ?v0 )(ipath$ ?v0 ?v1 ))(epath$ eff$ rules$ ?v1 ))):named a21 ))
(assert (! (forall ((?v0 Rule_stream$ )(?v1 Nat$ ))(=> (fair$ rules$ ?v0 )(fair$ rules$ (sdrop$ ?v1 ?v0 )))):named a22 ))
(check-sat )
;(get-unsat-core )
