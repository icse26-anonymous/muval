;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort Rule$ 0 )
(declare-sort State$ 0 )
(declare-sort Rule_set$ 0 )
(declare-sort State_set$ 0 )
(declare-sort State_fset$ 0 )
(declare-sort State_fset_bool_fun$ 0 )
(declare-sort State_rule_prod_tree$ 0 )
(declare-sort State_rule_prod_state_fun$ 0 )
(declare-sort State_rule_prod_tree_fset$ 0 )
(declare-sort State_rule_prod_tree_bool_fun$ 0 )
(declare-sort State_state_fset_bool_fun_fun$ 0 )
(declare-sort State_rule_prod_tree_state_fun$ 0 )
(declare-sort Rule_state_state_fset_bool_fun_fun_fun$ 0 )
(declare-sort State_rule_prod_tree_state_rule_prod_fun$ 0 )
(declare-sort Rule_stream_state_rule_prod_tree_bool_fun_fun$ 0 )
(declare-codatatypes ()((Rule_stream$ (sCons$ (shd$ Rule$ )(stl$ Rule_stream$ )))))
(declare-sort State_rule_prod$ 0)
(declare-fun fst$ (State_rule_prod$)State$)
(declare-fun snd$ (State_rule_prod$)Rule$)
(declare-fun pair$ (State$ Rule$ )State_rule_prod$)
(declare-fun s$ ()State_set$ )
(declare-fun rs$ ()Rule_stream$ )
(declare-fun s$a ()State$ )
(declare-fun sa$ ()State$ )
(declare-fun uu$ ()State_rule_prod_state_fun$ )
(declare-fun wf$ (Rule_state_state_fset_bool_fun_fun_fun$ )Rule_stream_state_rule_prod_tree_bool_fun_fun$ )
(declare-fun eff$ ()Rule_state_state_fset_bool_fun_fun_fun$ )
(declare-fun rsa$ ()Rule_stream$ )
(declare-fun comp$ (State_rule_prod_state_fun$ State_rule_prod_tree_state_rule_prod_fun$ )State_rule_prod_tree_state_fun$ )
(declare-fun cont$ (State_rule_prod_tree$ )State_rule_prod_tree_fset$ )
(declare-fun fair$ (Rule_stream$ Rule_stream$ )Bool )
(declare-fun root$ ()State_rule_prod_tree_state_rule_prod_fun$ )
(declare-fun sset$ (Rule_stream$ )Rule_set$ )
(declare-fun fenum$ (Rule_stream$ )Rule_stream$ )
(declare-fun rules$ ()Rule_stream$ )
(declare-fun fimage$ (State_rule_prod_tree_state_fun$ State_rule_prod_tree_fset$ )State_fset$ )
(declare-fun member$ (Rule$ Rule_set$ )Bool )
(declare-fun mkTree$ (Rule_state_state_fset_bool_fun_fun_fun$ Rule_stream$ State$ )State_rule_prod_tree$ )
(declare-fun fmember$ (State_rule_prod_tree$ State_rule_prod_tree_fset$ )Bool )
(declare-fun fun_app$ (State_rule_prod_state_fun$ State_rule_prod$ )State$ )
(declare-fun member$a (State$ State_set$ )Bool )
(declare-fun fun_app$a (State_rule_prod_tree_state_rule_prod_fun$ State_rule_prod_tree$ )State_rule_prod$ )
(declare-fun fun_app$b (State_fset_bool_fun$ State_fset$ )Bool )
(declare-fun fun_app$c (State_state_fset_bool_fun_fun$ State$ )State_fset_bool_fun$ )
(declare-fun fun_app$d (Rule_state_state_fset_bool_fun_fun_fun$ Rule$ )State_state_fset_bool_fun_fun$ )
(declare-fun fun_app$e (State_rule_prod_tree_bool_fun$ State_rule_prod_tree$ )Bool )
(declare-fun fun_app$f (Rule_stream_state_rule_prod_tree_bool_fun_fun$ Rule_stream$ )State_rule_prod_tree_bool_fun$ )
(assert (! (forall ((?v0 State_rule_prod$ ))(! (= (fun_app$ uu$ ?v0 )(fst$ ?v0 )):pattern ((fun_app$ uu$ ?v0 )))):named a0 ))
(assert (! (not (exists ((?v0 State_rule_prod_tree$ ))(and (= (mkTree$ eff$ rsa$ sa$ )?v0 )(and (member$ (snd$ (fun_app$a root$ ?v0 ))(sset$ rules$ ))(and (fun_app$b (fun_app$c (fun_app$d eff$ (snd$ (fun_app$a root$ ?v0 )))(fst$ (fun_app$a root$ ?v0 )))(fimage$ (comp$ uu$ root$ )(cont$ ?v0 )))(forall ((?v1 State_rule_prod_tree$ ))(=> (fmember$ ?v1 (cont$ ?v0 ))(or (exists ((?v2 Rule_stream$ )(?v3 State$ ))(and (= ?v1 (mkTree$ eff$ ?v2 ?v3 ))(and (member$a ?v3 s$ )(fair$ rules$ ?v2 ))))(fun_app$e (fun_app$f (wf$ eff$ )rules$ )?v1 ))))))))):named a1 ))
(assert (! (member$a s$a s$ ):named a2 ))
(assert (! (fair$ rules$ rs$ ):named a3 ))
(assert (! (member$a sa$ s$ ):named a4 ))
(assert (! (fair$ rules$ rsa$ ):named a5 ))
(assert (! (member$ (snd$ (fun_app$a root$ (mkTree$ eff$ rsa$ sa$ )))(sset$ rules$ )):named a6 ))
(assert (! (fun_app$b (fun_app$c (fun_app$d eff$ (snd$ (fun_app$a root$ (mkTree$ eff$ rsa$ sa$ ))))(fst$ (fun_app$a root$ (mkTree$ eff$ rsa$ sa$ ))))(fimage$ (comp$ uu$ root$ )(cont$ (mkTree$ eff$ rsa$ sa$ )))):named a7 ))
(assert (! (forall ((?v0 State$ ))(=> (member$a ?v0 s$ )(exists ((?v1 Rule$ ))(and (member$ ?v1 (sset$ rules$ ))(exists ((?v2 State_fset$ ))(fun_app$b (fun_app$c (fun_app$d eff$ ?v1 )?v0 )?v2 )))))):named a8 ))
(assert (! (= (sset$ (fenum$ rules$ ))(sset$ rules$ )):named a9 ))
(assert (! (fair$ rules$ (fenum$ rules$ )):named a10 ))
(assert (! (forall ((?v0 State_rule_prod_tree$ ))(= (fun_app$e (fun_app$f (wf$ eff$ )rules$ )?v0 )(exists ((?v1 State_rule_prod_tree$ ))(and (= ?v0 ?v1 )(and (member$ (snd$ (fun_app$a root$ ?v1 ))(sset$ rules$ ))(and (fun_app$b (fun_app$c (fun_app$d eff$ (snd$ (fun_app$a root$ ?v1 )))(fst$ (fun_app$a root$ ?v1 )))(fimage$ (comp$ uu$ root$ )(cont$ ?v1 )))(forall ((?v2 State_rule_prod_tree$ ))(=> (fmember$ ?v2 (cont$ ?v1 ))(fun_app$e (fun_app$f (wf$ eff$ )rules$ )?v2 ))))))))):named a11 ))
(assert (! (forall ((?v0 State_rule_prod_tree$ ))(=> (and (fun_app$e (fun_app$f (wf$ eff$ )rules$ )?v0 )(forall ((?v1 State_rule_prod_tree$ ))(=> (and (= ?v0 ?v1 )(and (member$ (snd$ (fun_app$a root$ ?v1 ))(sset$ rules$ ))(and (fun_app$b (fun_app$c (fun_app$d eff$ (snd$ (fun_app$a root$ ?v1 )))(fst$ (fun_app$a root$ ?v1 )))(fimage$ (comp$ uu$ root$ )(cont$ ?v1 )))(forall ((?v2 State_rule_prod_tree$ ))(=> (fmember$ ?v2 (cont$ ?v1 ))(fun_app$e (fun_app$f (wf$ eff$ )rules$ )?v2 ))))))false )))false )):named a12 ))
(assert (! (forall ((?v0 State_rule_prod_tree$ ))(=> (and (member$ (snd$ (fun_app$a root$ ?v0 ))(sset$ rules$ ))(and (fun_app$b (fun_app$c (fun_app$d eff$ (snd$ (fun_app$a root$ ?v0 )))(fst$ (fun_app$a root$ ?v0 )))(fimage$ (comp$ uu$ root$ )(cont$ ?v0 )))(forall ((?v1 State_rule_prod_tree$ ))(=> (fmember$ ?v1 (cont$ ?v0 ))(fun_app$e (fun_app$f (wf$ eff$ )rules$ )?v1 )))))(fun_app$e (fun_app$f (wf$ eff$ )rules$ )?v0 ))):named a13 ))
(assert (! (forall ((?v0 State_rule_prod_tree_bool_fun$ )(?v1 State_rule_prod_tree$ ))(=> (and (fun_app$e ?v0 ?v1 )(forall ((?v2 State_rule_prod_tree$ ))(=> (fun_app$e ?v0 ?v2 )(exists ((?v3 State_rule_prod_tree$ ))(and (= ?v2 ?v3 )(and (member$ (snd$ (fun_app$a root$ ?v3 ))(sset$ rules$ ))(and (fun_app$b (fun_app$c (fun_app$d eff$ (snd$ (fun_app$a root$ ?v3 )))(fst$ (fun_app$a root$ ?v3 )))(fimage$ (comp$ uu$ root$ )(cont$ ?v3 )))(forall ((?v4 State_rule_prod_tree$ ))(=> (fmember$ ?v4 (cont$ ?v3 ))(or (fun_app$e ?v0 ?v4 )(fun_app$e (fun_app$f (wf$ eff$ )rules$ )?v4 )))))))))))(fun_app$e (fun_app$f (wf$ eff$ )rules$ )?v1 ))):named a14 ))
(assert (! (forall ((?v0 Rule_state_state_fset_bool_fun_fun_fun$ )(?v1 Rule_stream$ )(?v2 State_rule_prod_tree$ ))(= (fun_app$e (fun_app$f (wf$ ?v0 )?v1 )?v2 )(exists ((?v3 State_rule_prod_tree$ ))(and (= ?v2 ?v3 )(and (member$ (snd$ (fun_app$a root$ ?v3 ))(sset$ ?v1 ))(and (fun_app$b (fun_app$c (fun_app$d ?v0 (snd$ (fun_app$a root$ ?v3 )))(fst$ (fun_app$a root$ ?v3 )))(fimage$ (comp$ uu$ root$ )(cont$ ?v3 )))(forall ((?v4 State_rule_prod_tree$ ))(=> (fmember$ ?v4 (cont$ ?v3 ))(fun_app$e (fun_app$f (wf$ ?v0 )?v1 )?v4 ))))))))):named a15 ))
(assert (! (forall ((?v0 Rule_state_state_fset_bool_fun_fun_fun$ )(?v1 Rule_stream$ )(?v2 State_rule_prod_tree$ ))(=> (and (fun_app$e (fun_app$f (wf$ ?v0 )?v1 )?v2 )(forall ((?v3 State_rule_prod_tree$ ))(=> (and (= ?v2 ?v3 )(and (member$ (snd$ (fun_app$a root$ ?v3 ))(sset$ ?v1 ))(and (fun_app$b (fun_app$c (fun_app$d ?v0 (snd$ (fun_app$a root$ ?v3 )))(fst$ (fun_app$a root$ ?v3 )))(fimage$ (comp$ uu$ root$ )(cont$ ?v3 )))(forall ((?v4 State_rule_prod_tree$ ))(=> (fmember$ ?v4 (cont$ ?v3 ))(fun_app$e (fun_app$f (wf$ ?v0 )?v1 )?v4 ))))))false )))false )):named a16 ))
(assert (! (forall ((?v0 State_rule_prod_tree$ )(?v1 State_rule_prod_tree$ ))(=> (and (= (fun_app$a root$ ?v0 )(fun_app$a root$ ?v1 ))(= (cont$ ?v0 )(cont$ ?v1 )))(= ?v0 ?v1 ))):named a17 ))
(assert (! (forall ((?v0 State_rule_prod_tree$ )(?v1 Rule_stream$ )(?v2 Rule_state_state_fset_bool_fun_fun_fun$ ))(=> (and (member$ (snd$ (fun_app$a root$ ?v0 ))(sset$ ?v1 ))(and (fun_app$b (fun_app$c (fun_app$d ?v2 (snd$ (fun_app$a root$ ?v0 )))(fst$ (fun_app$a root$ ?v0 )))(fimage$ (comp$ uu$ root$ )(cont$ ?v0 )))(forall ((?v3 State_rule_prod_tree$ ))(=> (fmember$ ?v3 (cont$ ?v0 ))(fun_app$e (fun_app$f (wf$ ?v2 )?v1 )?v3 )))))(fun_app$e (fun_app$f (wf$ ?v2 )?v1 )?v0 ))):named a18 ))
(check-sat )
;(get-unsat-core )
