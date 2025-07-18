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
(declare-sort State_state_fset_bool_fun_fun$ 0 )
(declare-sort Rule_state_state_fset_bool_fun_fun_fun$ 0 )
(declare-sort Rule_stream$ 0)
(declare-fun shd$ (Rule_stream$)Rule$)
(declare-fun stl$ (Rule_stream$)Rule_stream$)
(declare-fun sCons$ (Rule$ Rule_stream$ )Rule_stream$)
(declare-sort State_rule_prod$ 0)
(declare-fun fst$ (State_rule_prod$)State$)
(declare-fun snd$ (State_rule_prod$)Rule$)
(declare-fun pair$ (State$ Rule$ )State_rule_prod$)
(declare-sort State_rule_prod_stream$ 0)
(declare-fun shd$a (State_rule_prod_stream$)State_rule_prod$)
(declare-fun stl$a (State_rule_prod_stream$)State_rule_prod_stream$)
(declare-fun sCons$a (State_rule_prod$ State_rule_prod_stream$ )State_rule_prod_stream$)
(declare-fun s$ ()State$ )
(declare-fun rs$ ()Rule_stream$ )
(declare-fun s$a ()State_set$ )
(declare-fun wf$ (Rule_state_state_fset_bool_fun_fun_fun$ Rule_stream$ State_rule_prod_tree$ )Bool )
(declare-fun eff$ ()Rule_state_state_fset_bool_fun_fun_fun$ )
(declare-fun fair$ (Rule_stream$ Rule_stream$ )Bool )
(declare-fun sset$ (Rule_stream$ )Rule_set$ )
(declare-fun trim$ (Rule_state_state_fset_bool_fun_fun_fun$ Rule_stream$ State$ )Rule_stream$ )
(declare-fun epath$ (Rule_state_state_fset_bool_fun_fun_fun$ Rule_stream$ State_rule_prod_stream$ )Bool )
(declare-fun fenum$ (Rule_stream$ )Rule_stream$ )
(declare-fun ipath$ (State_rule_prod_tree$ State_rule_prod_stream$ )Bool )
(declare-fun rules$ ()Rule_stream$ )
(declare-fun sdrop$ (Nat$ Rule_stream$ )Rule_stream$ )
(declare-fun member$ (State$ State_set$ )Bool )
(declare-fun mkTree$ (Rule_state_state_fset_bool_fun_fun_fun$ Rule_stream$ State$ )State_rule_prod_tree$ )
(declare-fun sdrop$a (Nat$ State_rule_prod_stream$ )State_rule_prod_stream$ )
(declare-fun enabled$ (Rule_state_state_fset_bool_fun_fun_fun$ Rule$ State$ )Bool )
(declare-fun fmember$ (State$ State_fset$ )Bool )
(declare-fun fun_app$ (State_fset_bool_fun$ State_fset$ )Bool )
(declare-fun member$a (Rule$ Rule_set$ )Bool )
(declare-fun minWait$ (Rule_state_state_fset_bool_fun_fun_fun$ Rule_stream$ State$ )Nat$ )
(declare-fun pickEff$ (Rule_state_state_fset_bool_fun_fun_fun$ Rule$ State$ )State_fset$ )
(declare-fun fun_app$a (State_state_fset_bool_fun_fun$ State$ )State_fset_bool_fun$ )
(declare-fun fun_app$b (Rule_state_state_fset_bool_fun_fun_fun$ Rule$ )State_state_fset_bool_fun_fun$ )
(declare-fun saturated$ (Rule_state_state_fset_bool_fun_fun_fun$ Rule_stream$ State_rule_prod_stream$ )Bool )
(declare-fun saturated$a (Rule_state_state_fset_bool_fun_fun_fun$ Rule$ State_rule_prod_stream$ )Bool )
(assert (! (not (wf$ eff$ rules$ (mkTree$ eff$ rs$ s$ ))):named a0 ))
(assert (! (member$ s$ s$a ):named a1 ))
(assert (! (fair$ rules$ rs$ ):named a2 ))
(assert (! (fair$ rules$ (fenum$ rules$ )):named a3 ))
(assert (! (forall ((?v0 Rule$ )(?v1 State$ ))(! (= (enabled$ eff$ ?v0 ?v1 )(exists ((?v2 State_fset$ ))(fun_app$ (fun_app$a (fun_app$b eff$ ?v0 )?v1 )?v2 ))):pattern ((enabled$ eff$ ?v0 ?v1 )))):named a4 ))
(assert (! (forall ((?v0 State_rule_prod_tree$ )(?v1 State_rule_prod_stream$ ))(=> (and (wf$ eff$ rules$ ?v0 )(ipath$ ?v0 ?v1 ))(epath$ eff$ rules$ ?v1 ))):named a5 ))
(assert (! (forall ((?v0 State$ )(?v1 Rule_stream$ ))(=> (and (member$ ?v0 s$a )(fair$ rules$ ?v1 ))(fair$ rules$ (trim$ eff$ ?v1 ?v0 )))):named a6 ))
(assert (! (forall ((?v0 State$ ))(=> (member$ ?v0 s$a )(exists ((?v1 Rule$ ))(and (member$a ?v1 (sset$ rules$ ))(exists ((?v2 State_fset$ ))(fun_app$ (fun_app$a (fun_app$b eff$ ?v1 )?v0 )?v2 )))))):named a7 ))
(assert (! (forall ((?v0 Rule_stream$ )(?v1 Nat$ ))(=> (fair$ rules$ ?v0 )(fair$ rules$ (sdrop$ ?v1 ?v0 )))):named a8 ))
(assert (! (forall ((?v0 State_rule_prod_stream$ ))(= (saturated$ eff$ rules$ ?v0 )(forall ((?v1 Rule$ ))(=> (member$a ?v1 (sset$ rules$ ))(saturated$a eff$ ?v1 ?v0 ))))):named a9 ))
(assert (! (forall ((?v0 Rule_stream$ ))(=> (fair$ rules$ ?v0 )(fair$ rules$ (stl$ ?v0 )))):named a10 ))
(assert (! (forall ((?v0 Rule$ )(?v1 State$ ))(=> (enabled$ eff$ ?v0 ?v1 )(fun_app$ (fun_app$a (fun_app$b eff$ ?v0 )?v1 )(pickEff$ eff$ ?v0 ?v1 )))):named a11 ))
(assert (! (= (sset$ (fenum$ rules$ ))(sset$ rules$ )):named a12 ))
(assert (! (forall ((?v0 State$ )(?v1 Rule_stream$ )(?v2 State_rule_prod_stream$ )(?v3 Nat$ ))(=> (and (member$ ?v0 s$a )(and (fair$ rules$ ?v1 )(ipath$ (mkTree$ eff$ ?v1 ?v0 )?v2 )))(exists ((?v4 Nat$ )(?v5 State$ ))(and (member$ ?v5 s$a )(ipath$ (mkTree$ eff$ (sdrop$ ?v4 ?v1 )?v5 )(sdrop$a ?v3 ?v2 )))))):named a13 ))
(assert (! (forall ((?v0 State$ )(?v1 Rule$ )(?v2 State_fset$ )(?v3 State$ ))(=> (and (member$ ?v0 s$a )(and (member$a ?v1 (sset$ rules$ ))(and (fun_app$ (fun_app$a (fun_app$b eff$ ?v1 )?v0 )?v2 )(fmember$ ?v3 ?v2 ))))(member$ ?v3 s$a ))):named a14 ))
(assert (! (forall ((?v0 State$ )(?v1 Rule_stream$ ))(! (=> (and (member$ ?v0 s$a )(fair$ rules$ ?v1 ))(= (trim$ eff$ ?v1 ?v0 )(sdrop$ (minWait$ eff$ ?v1 ?v0 )?v1 ))):pattern ((trim$ eff$ ?v1 ?v0 )))):named a15 ))
(assert (! (forall ((?v0 Rule_state_state_fset_bool_fun_fun_fun$ )(?v1 Rule_stream$ )(?v2 State_rule_prod_stream$ ))(= (saturated$ ?v0 ?v1 ?v2 )(forall ((?v3 Rule$ ))(=> (member$a ?v3 (sset$ ?v1 ))(saturated$a ?v0 ?v3 ?v2 ))))):named a16 ))
(assert (! (forall ((?v0 Rule_stream$ ))(= (sset$ (fenum$ ?v0 ))(sset$ ?v0 ))):named a17 ))
(check-sat )
;(get-unsat-core )
