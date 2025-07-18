;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort Rule$ 0 )
(declare-sort State$ 0 )
(declare-sort Rule_set$ 0 )
(declare-sort State_set$ 0 )
(declare-sort State_fset$ 0 )
(declare-sort State_fset_bool_fun$ 0 )
(declare-sort State_state_fset_bool_fun_fun$ 0 )
(declare-sort State_rule_prod_stream_bool_fun$ 0 )
(declare-sort Rule_state_state_fset_bool_fun_fun_fun$ 0 )
(declare-sort Rule_stream_state_rule_prod_stream_bool_fun_fun$ 0 )
(declare-sort State_rule_prod_stream_state_rule_prod_stream_bool_fun_fun$ 0 )
(declare-datatypes ()((State_rule_prod$ (pair$ (fst$ State$ )(snd$ Rule$ )))))
(declare-sort State_rule_prod_stream$ 0)
(declare-sort Rule_stream$ 0)
(declare-fun shd$ (State_rule_prod_stream$)State_rule_prod$)
(declare-fun stl$ (State_rule_prod_stream$)State_rule_prod_stream$)
(declare-fun sCons$ (State_rule_prod$ State_rule_prod_stream$ )State_rule_prod_stream$)
(declare-fun shd$a (Rule_stream$)Rule$)
(declare-fun stl$a (Rule_stream$)Rule_stream$)
(declare-fun sCons$a (Rule$ Rule_stream$ )Rule_stream$)
(declare-fun r$ ()Rule$ )
(declare-fun s$ ()State_set$ )
(declare-fun eff$ ()Rule_state_state_fset_bool_fun_fun_fun$ )
(declare-fun per$ (Rule_state_state_fset_bool_fun_fun_fun$ Rule_stream$ State_set$ Rule$ )Bool )
(declare-fun sset$ (Rule_stream$ )Rule_set$ )
(declare-fun epath$ (Rule_state_state_fset_bool_fun_fun_fun$ )Rule_stream_state_rule_prod_stream_bool_fun_fun$ )
(declare-fun rules$ ()Rule_stream$ )
(declare-fun steps$ ()State_rule_prod_stream$ )
(declare-fun member$ (State$ State_set$ )Bool )
(declare-fun stepsa$ ()State_rule_prod_stream$ )
(declare-fun thesis$ ()Bool )
(declare-fun enabled$ (Rule_state_state_fset_bool_fun_fun_fun$ Rule$ State$ )Bool )
(declare-fun fmember$ (State$ State_fset$ )Bool )
(declare-fun fun_app$ (State_fset_bool_fun$ State_fset$ )Bool )
(declare-fun member$a (Rule$ Rule_set$ )Bool )
(declare-fun fun_app$a (State_state_fset_bool_fun_fun$ State$ )State_fset_bool_fun$ )
(declare-fun fun_app$b (Rule_state_state_fset_bool_fun_fun_fun$ Rule$ )State_state_fset_bool_fun_fun$ )
(declare-fun fun_app$c (State_rule_prod_stream_bool_fun$ State_rule_prod_stream$ )Bool )
(declare-fun fun_app$d (Rule_stream_state_rule_prod_stream_bool_fun_fun$ Rule_stream$ )State_rule_prod_stream_bool_fun$ )
(declare-fun fun_app$e (State_rule_prod_stream_state_rule_prod_stream_bool_fun_fun$ State_rule_prod_stream$ )State_rule_prod_stream_bool_fun$ )
(assert (! (not thesis$ ):named a0 ))
(assert (! (forall ((?v0 State_fset$ ))(=> (and (fun_app$ (fun_app$a (fun_app$b eff$ (snd$ (shd$ stepsa$ )))(fst$ (shd$ stepsa$ )))?v0 )(fmember$ (fst$ (shd$ (stl$ stepsa$ )))?v0 ))thesis$ )):named a1 ))
(assert (! (member$ (fst$ (shd$ stepsa$ ))s$ ):named a2 ))
(assert (! (not (= (snd$ (shd$ stepsa$ ))r$ )):named a3 ))
(assert (! (and (fun_app$c (fun_app$d (epath$ eff$ )rules$ )steps$ )(member$ (fst$ (shd$ steps$ ))s$ )):named a4 ))
(assert (! (enabled$ eff$ r$ (fst$ (shd$ stepsa$ ))):named a5 ))
(assert (! (forall ((?v0 Rule$ )(?v1 State$ ))(! (= (enabled$ eff$ ?v0 ?v1 )(exists ((?v2 State_fset$ ))(fun_app$ (fun_app$a (fun_app$b eff$ ?v0 )?v1 )?v2 ))):pattern ((enabled$ eff$ ?v0 ?v1 )))):named a6 ))
(assert (! (forall ((?v0 State_rule_prod_stream$ ))(= (fun_app$c (fun_app$d (epath$ eff$ )rules$ )?v0 )(exists ((?v1 State_rule_prod_stream$ )(?v2 State_fset$ ))(and (= ?v0 ?v1 )(and (member$a (snd$ (shd$ ?v1 ))(sset$ rules$ ))(and (fmember$ (fst$ (shd$ (stl$ ?v1 )))?v2 )(and (fun_app$ (fun_app$a (fun_app$b eff$ (snd$ (shd$ ?v1 )))(fst$ (shd$ ?v1 )))?v2 )(fun_app$c (fun_app$d (epath$ eff$ )rules$ )(stl$ ?v1 ))))))))):named a7 ))
(assert (! (forall ((?v0 State_rule_prod_stream$ ))(=> (and (fun_app$c (fun_app$d (epath$ eff$ )rules$ )?v0 )(forall ((?v1 State_rule_prod_stream$ )(?v2 State_fset$ ))(=> (and (= ?v0 ?v1 )(and (member$a (snd$ (shd$ ?v1 ))(sset$ rules$ ))(and (fmember$ (fst$ (shd$ (stl$ ?v1 )))?v2 )(and (fun_app$ (fun_app$a (fun_app$b eff$ (snd$ (shd$ ?v1 )))(fst$ (shd$ ?v1 )))?v2 )(fun_app$c (fun_app$d (epath$ eff$ )rules$ )(stl$ ?v1 ))))))false )))false )):named a8 ))
(assert (! (forall ((?v0 State_rule_prod_stream$ )(?v1 State_fset$ ))(=> (and (member$a (snd$ (shd$ ?v0 ))(sset$ rules$ ))(and (fmember$ (fst$ (shd$ (stl$ ?v0 )))?v1 )(and (fun_app$ (fun_app$a (fun_app$b eff$ (snd$ (shd$ ?v0 )))(fst$ (shd$ ?v0 )))?v1 )(fun_app$c (fun_app$d (epath$ eff$ )rules$ )(stl$ ?v0 )))))(fun_app$c (fun_app$d (epath$ eff$ )rules$ )?v0 ))):named a9 ))
(assert (! (forall ((?v0 State_rule_prod_stream_bool_fun$ )(?v1 State_rule_prod_stream$ ))(=> (and (fun_app$c ?v0 ?v1 )(forall ((?v2 State_rule_prod_stream$ ))(=> (fun_app$c ?v0 ?v2 )(exists ((?v3 State_rule_prod_stream$ )(?v4 State_fset$ ))(and (= ?v2 ?v3 )(and (member$a (snd$ (shd$ ?v3 ))(sset$ rules$ ))(and (fmember$ (fst$ (shd$ (stl$ ?v3 )))?v4 )(and (fun_app$ (fun_app$a (fun_app$b eff$ (snd$ (shd$ ?v3 )))(fst$ (shd$ ?v3 )))?v4 )(or (fun_app$c ?v0 (stl$ ?v3 ))(fun_app$c (fun_app$d (epath$ eff$ )rules$ )(stl$ ?v3 )))))))))))(fun_app$c (fun_app$d (epath$ eff$ )rules$ )?v1 ))):named a10 ))
(assert (! (forall ((?v0 State_rule_prod_stream$ )(?v1 State_rule_prod_stream$ ))(=> (and (= (shd$ ?v0 )(shd$ ?v1 ))(= (stl$ ?v0 )(stl$ ?v1 )))(= ?v0 ?v1 ))):named a11 ))
(assert (! (forall ((?v0 State_rule_prod_stream_state_rule_prod_stream_bool_fun_fun$ )(?v1 State_rule_prod_stream$ )(?v2 State_rule_prod_stream$ ))(=> (and (fun_app$c (fun_app$e ?v0 ?v1 )?v2 )(forall ((?v3 State_rule_prod_stream$ )(?v4 State_rule_prod_stream$ ))(=> (fun_app$c (fun_app$e ?v0 ?v3 )?v4 )(and (= (shd$ ?v3 )(shd$ ?v4 ))(or (fun_app$c (fun_app$e ?v0 (stl$ ?v3 ))(stl$ ?v4 ))(= (stl$ ?v3 )(stl$ ?v4 )))))))(= ?v1 ?v2 ))):named a12 ))
(assert (! (forall ((?v0 State_rule_prod_stream_state_rule_prod_stream_bool_fun_fun$ )(?v1 State_rule_prod_stream$ )(?v2 State_rule_prod_stream$ ))(=> (and (fun_app$c (fun_app$e ?v0 ?v1 )?v2 )(forall ((?v3 State_rule_prod_stream$ )(?v4 State_rule_prod_stream$ ))(=> (fun_app$c (fun_app$e ?v0 ?v3 )?v4 )(and (= (shd$ ?v3 )(shd$ ?v4 ))(fun_app$c (fun_app$e ?v0 (stl$ ?v3 ))(stl$ ?v4 ))))))(= ?v1 ?v2 ))):named a13 ))
(assert (! (forall ((?v0 State_rule_prod$ )(?v1 State_rule_prod$ ))(= (= ?v0 ?v1 )(and (= (fst$ ?v0 )(fst$ ?v1 ))(= (snd$ ?v0 )(snd$ ?v1 ))))):named a14 ))
(assert (! (forall ((?v0 State_rule_prod$ )(?v1 State_rule_prod$ ))(=> (and (= (fst$ ?v0 )(fst$ ?v1 ))(= (snd$ ?v0 )(snd$ ?v1 )))(= ?v0 ?v1 ))):named a15 ))
(assert (! (per$ eff$ rules$ s$ r$ ):named a16 ))
(assert (! (forall ((?v0 State$ ))(=> (member$ ?v0 s$ )(exists ((?v1 Rule$ ))(and (member$a ?v1 (sset$ rules$ ))(exists ((?v2 State_fset$ ))(fun_app$ (fun_app$a (fun_app$b eff$ ?v1 )?v0 )?v2 )))))):named a17 ))
(assert (! (member$a (snd$ (shd$ stepsa$ ))(sset$ rules$ )):named a18 ))
(check-sat )
;(get-unsat-core )
