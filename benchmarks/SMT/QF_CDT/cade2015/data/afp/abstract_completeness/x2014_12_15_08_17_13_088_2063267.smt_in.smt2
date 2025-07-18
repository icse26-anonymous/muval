;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort Rule$ 0 )
(declare-sort State$ 0 )
(declare-sort Rule_set$ 0 )
(declare-sort State_fset$ 0 )
(declare-sort Rule_bool_fun$ 0 )
(declare-sort State_fset_bool_fun$ 0 )
(declare-sort State_rule_prod_set$ 0 )
(declare-sort Rule_stream_bool_fun$ 0 )
(declare-sort State_rule_prod_bool_fun$ 0 )
(declare-sort State_state_fset_bool_fun_fun$ 0 )
(declare-sort Rule_bool_fun_rule_bool_fun_fun$ 0 )
(declare-sort State_rule_prod_stream_bool_fun$ 0 )
(declare-sort Rule_state_rule_prod_bool_fun_fun$ 0 )
(declare-sort Rule_state_state_fset_bool_fun_fun_fun$ 0 )
(declare-sort Rule_state_rule_prod_stream_bool_fun_fun$ 0 )
(declare-sort Rule_stream_bool_fun_rule_stream_bool_fun_fun$ 0 )
(declare-sort Rule_stream_state_rule_prod_stream_bool_fun_fun$ 0 )
(declare-sort State_rule_prod_bool_fun_state_rule_prod_bool_fun_fun$ 0 )
(declare-sort State_rule_prod_stream_bool_fun_state_rule_prod_stream_bool_fun_fun$ 0 )
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
(declare-fun ev$ (State_rule_prod_stream_bool_fun$ )State_rule_prod_stream_bool_fun$ )
(declare-fun uu$ ()State_rule_prod_bool_fun$ )
(declare-fun alw$ (State_rule_prod_stream_bool_fun$ )State_rule_prod_stream_bool_fun$ )
(declare-fun eff$ ()Rule_state_state_fset_bool_fun_fun_fun$ )
(declare-fun ev$a (Rule_stream_bool_fun$ )Rule_stream_bool_fun$ )
(declare-fun hld$ (Rule_set$ )Rule_stream_bool_fun$ )
(declare-fun uua$ (Rule_bool_fun$ )Rule_bool_fun_rule_bool_fun_fun$ )
(declare-fun uub$ (State_rule_prod_bool_fun$ )State_rule_prod_bool_fun_state_rule_prod_bool_fun_fun$ )
(declare-fun uuc$ (Rule_stream_bool_fun$ )Rule_stream_bool_fun_rule_stream_bool_fun_fun$ )
(declare-fun uud$ (State_rule_prod_stream_bool_fun$ )State_rule_prod_stream_bool_fun_state_rule_prod_stream_bool_fun_fun$ )
(declare-fun uue$ ()Rule_stream_bool_fun$ )
(declare-fun uuf$ ()State_rule_prod_stream_bool_fun$ )
(declare-fun uug$ ()State_rule_prod_bool_fun$ )
(declare-fun uuh$ (Rule_state_state_fset_bool_fun_fun_fun$ )Rule_state_rule_prod_bool_fun_fun$ )
(declare-fun uui$ (Rule$ )State_rule_prod_bool_fun$ )
(declare-fun uuj$ (Rule_state_state_fset_bool_fun_fun_fun$ )Rule_state_rule_prod_stream_bool_fun_fun$ )
(declare-fun uuk$ (Rule_set$ )Rule_bool_fun$ )
(declare-fun uul$ (State_rule_prod_set$ )State_rule_prod_bool_fun$ )
(declare-fun uum$ (Rule_stream_bool_fun$ )Rule_stream_bool_fun$ )
(declare-fun uun$ (Rule_stream_bool_fun$ )Rule_stream_bool_fun$ )
(declare-fun uuo$ (State_rule_prod_stream_bool_fun$ )State_rule_prod_stream_bool_fun$ )
(declare-fun uup$ (State_rule_prod_stream_bool_fun$ )State_rule_prod_stream_bool_fun$ )
(declare-fun alw$a (Rule_stream_bool_fun$ )Rule_stream_bool_fun$ )
(declare-fun hld$a (State_rule_prod_set$ )State_rule_prod_stream_bool_fun$ )
(declare-fun sset$ (Rule_stream$ )Rule_set$ )
(declare-fun holds$ (State_rule_prod_bool_fun$ )State_rule_prod_stream_bool_fun$ )
(declare-fun rules$ ()Rule_stream$ )
(declare-fun sset$a (State_rule_prod_stream$ )State_rule_prod_set$ )
(declare-fun steps$ ()State_rule_prod_stream$ )
(declare-fun holds$a (Rule_bool_fun$ )Rule_stream_bool_fun$ )
(declare-fun member$ (State_rule_prod$ State_rule_prod_set$ )Bool )
(declare-fun stepsa$ ()State_rule_prod_stream$ )
(declare-fun enabled$ (Rule_state_state_fset_bool_fun_fun_fun$ Rule$ State$ )Bool )
(declare-fun fun_app$ (State_rule_prod_bool_fun$ State_rule_prod$ )Bool )
(declare-fun member$a (Rule$ Rule_set$ )Bool )
(declare-fun fun_app$a (Rule_bool_fun$ Rule$ )Bool )
(declare-fun fun_app$b (State_rule_prod_stream_bool_fun$ State_rule_prod_stream$ )Bool )
(declare-fun fun_app$c (Rule_stream_bool_fun$ Rule_stream$ )Bool )
(declare-fun fun_app$d (Rule_state_rule_prod_bool_fun_fun$ Rule$ )State_rule_prod_bool_fun$ )
(declare-fun fun_app$e (Rule_state_rule_prod_stream_bool_fun_fun$ Rule$ )State_rule_prod_stream_bool_fun$ )
(declare-fun fun_app$f (State_rule_prod_stream_bool_fun_state_rule_prod_stream_bool_fun_fun$ State_rule_prod_stream_bool_fun$ )State_rule_prod_stream_bool_fun$ )
(declare-fun fun_app$g (Rule_stream_bool_fun_rule_stream_bool_fun_fun$ Rule_stream_bool_fun$ )Rule_stream_bool_fun$ )
(declare-fun fun_app$h (State_rule_prod_bool_fun_state_rule_prod_bool_fun_fun$ State_rule_prod_bool_fun$ )State_rule_prod_bool_fun$ )
(declare-fun fun_app$i (Rule_bool_fun_rule_bool_fun_fun$ Rule_bool_fun$ )Rule_bool_fun$ )
(declare-fun fun_app$j (State_fset_bool_fun$ State_fset$ )Bool )
(declare-fun fun_app$k (State_state_fset_bool_fun_fun$ State$ )State_fset_bool_fun$ )
(declare-fun fun_app$l (Rule_state_state_fset_bool_fun_fun_fun$ Rule$ )State_state_fset_bool_fun_fun$ )
(declare-fun fun_app$m (Rule_stream_state_rule_prod_stream_bool_fun_fun$ Rule_stream$ )State_rule_prod_stream_bool_fun$ )
(declare-fun saturated$ (Rule_state_state_fset_bool_fun_fun_fun$ )Rule_state_rule_prod_stream_bool_fun_fun$ )
(declare-fun saturated$a (Rule_state_state_fset_bool_fun_fun_fun$ )Rule_stream_state_rule_prod_stream_bool_fun_fun$ )
(assert (! (forall ((?v0 State_rule_prod$ ))(! (= (fun_app$ uug$ ?v0 )(enabled$ eff$ r$ (fst$ ?v0 ))):pattern ((fun_app$ uug$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 State_rule_prod$ ))(! (= (fun_app$ uu$ ?v0 )(= (snd$ ?v0 )r$ )):pattern ((fun_app$ uu$ ?v0 )))):named a1 ))
(assert (! (forall ((?v0 Rule$ )(?v1 State_rule_prod$ ))(! (= (fun_app$ (uui$ ?v0 )?v1 )(= (snd$ ?v1 )?v0 )):pattern ((fun_app$ (uui$ ?v0 )?v1 )))):named a2 ))
(assert (! (forall ((?v0 State_rule_prod_set$ )(?v1 State_rule_prod$ ))(! (= (fun_app$ (uul$ ?v0 )?v1 )(member$ ?v1 ?v0 )):pattern ((fun_app$ (uul$ ?v0 )?v1 )))):named a3 ))
(assert (! (forall ((?v0 Rule_set$ )(?v1 Rule$ ))(! (= (fun_app$a (uuk$ ?v0 )?v1 )(member$a ?v1 ?v0 )):pattern ((fun_app$a (uuk$ ?v0 )?v1 )))):named a4 ))
(assert (! (forall ((?v0 State_rule_prod_stream_bool_fun$ )(?v1 State_rule_prod_stream$ ))(! (= (fun_app$b (uup$ ?v0 )?v1 )(not (fun_app$b (ev$ (uuo$ ?v0 ))?v1 ))):pattern ((fun_app$b (uup$ ?v0 )?v1 )))):named a5 ))
(assert (! (forall ((?v0 Rule_stream_bool_fun$ )(?v1 Rule_stream$ ))(! (= (fun_app$c (uun$ ?v0 )?v1 )(not (fun_app$c (ev$a (uum$ ?v0 ))?v1 ))):pattern ((fun_app$c (uun$ ?v0 )?v1 )))):named a6 ))
(assert (! (forall ((?v0 State_rule_prod_stream_bool_fun$ )(?v1 State_rule_prod_stream$ ))(! (= (fun_app$b (uuo$ ?v0 )?v1 )(not (fun_app$b ?v0 ?v1 ))):pattern ((fun_app$b (uuo$ ?v0 )?v1 )))):named a7 ))
(assert (! (forall ((?v0 Rule_stream_bool_fun$ )(?v1 Rule_stream$ ))(! (= (fun_app$c (uum$ ?v0 )?v1 )(not (fun_app$c ?v0 ?v1 ))):pattern ((fun_app$c (uum$ ?v0 )?v1 )))):named a8 ))
(assert (! (forall ((?v0 Rule_state_state_fset_bool_fun_fun_fun$ )(?v1 Rule$ )(?v2 State_rule_prod$ ))(! (= (fun_app$ (fun_app$d (uuh$ ?v0 )?v1 )?v2 )(enabled$ ?v0 ?v1 (fst$ ?v2 ))):pattern ((fun_app$ (fun_app$d (uuh$ ?v0 )?v1 )?v2 )))):named a9 ))
(assert (! (forall ((?v0 Rule_state_state_fset_bool_fun_fun_fun$ )(?v1 Rule$ )(?v2 State_rule_prod_stream$ ))(! (= (fun_app$b (fun_app$e (uuj$ ?v0 )?v1 )?v2 )(=> (fun_app$b (holds$ (fun_app$d (uuh$ ?v0 )?v1 ))?v2 )(fun_app$b (ev$ (holds$ (uui$ ?v1 )))?v2 ))):pattern ((fun_app$b (fun_app$e (uuj$ ?v0 )?v1 )?v2 )))):named a10 ))
(assert (! (forall ((?v0 State_rule_prod_stream_bool_fun$ )(?v1 State_rule_prod_stream_bool_fun$ )(?v2 State_rule_prod_stream$ ))(! (= (fun_app$b (fun_app$f (uud$ ?v0 )?v1 )?v2 )(or (fun_app$b ?v0 ?v2 )(fun_app$b ?v1 ?v2 ))):pattern ((fun_app$b (fun_app$f (uud$ ?v0 )?v1 )?v2 )))):named a11 ))
(assert (! (forall ((?v0 Rule_stream_bool_fun$ )(?v1 Rule_stream_bool_fun$ )(?v2 Rule_stream$ ))(! (= (fun_app$c (fun_app$g (uuc$ ?v0 )?v1 )?v2 )(or (fun_app$c ?v0 ?v2 )(fun_app$c ?v1 ?v2 ))):pattern ((fun_app$c (fun_app$g (uuc$ ?v0 )?v1 )?v2 )))):named a12 ))
(assert (! (forall ((?v0 State_rule_prod_bool_fun$ )(?v1 State_rule_prod_bool_fun$ )(?v2 State_rule_prod$ ))(! (= (fun_app$ (fun_app$h (uub$ ?v0 )?v1 )?v2 )(and (fun_app$ ?v0 ?v2 )(fun_app$ ?v1 ?v2 ))):pattern ((fun_app$ (fun_app$h (uub$ ?v0 )?v1 )?v2 )))):named a13 ))
(assert (! (forall ((?v0 Rule_bool_fun$ )(?v1 Rule_bool_fun$ )(?v2 Rule$ ))(! (= (fun_app$a (fun_app$i (uua$ ?v0 )?v1 )?v2 )(and (fun_app$a ?v0 ?v2 )(fun_app$a ?v1 ?v2 ))):pattern ((fun_app$a (fun_app$i (uua$ ?v0 )?v1 )?v2 )))):named a14 ))
(assert (! (forall ((?v0 State_rule_prod_stream$ ))(! (= (fun_app$b uuf$ ?v0 )false ):pattern ((fun_app$b uuf$ ?v0 )))):named a15 ))
(assert (! (forall ((?v0 Rule_stream$ ))(! (= (fun_app$c uue$ ?v0 )false ):pattern ((fun_app$c uue$ ?v0 )))):named a16 ))
(assert (! (not (fun_app$b (ev$ (holds$ uu$ ))stepsa$ )):named a17 ))
(assert (! (forall ((?v0 Rule_stream_bool_fun$ ))(= (ev$a (ev$a ?v0 ))(ev$a ?v0 ))):named a18 ))
(assert (! (forall ((?v0 State_rule_prod_stream_bool_fun$ ))(= (ev$ (ev$ ?v0 ))(ev$ ?v0 ))):named a19 ))
(assert (! (forall ((?v0 Rule_bool_fun$ )(?v1 Rule_stream$ )(?v2 Rule_bool_fun$ ))(= (and (fun_app$c (holds$a ?v0 )?v1 )(fun_app$c (holds$a ?v2 )?v1 ))(fun_app$c (holds$a (fun_app$i (uua$ ?v0 )?v2 ))?v1 ))):named a20 ))
(assert (! (forall ((?v0 State_rule_prod_bool_fun$ )(?v1 State_rule_prod_stream$ )(?v2 State_rule_prod_bool_fun$ ))(= (and (fun_app$b (holds$ ?v0 )?v1 )(fun_app$b (holds$ ?v2 )?v1 ))(fun_app$b (holds$ (fun_app$h (uub$ ?v0 )?v2 ))?v1 ))):named a21 ))
(assert (! (forall ((?v0 Rule_stream_bool_fun$ )(?v1 Rule_stream_bool_fun$ )(?v2 Rule_stream$ ))(= (fun_app$c (ev$a (fun_app$g (uuc$ ?v0 )?v1 ))?v2 )(or (fun_app$c (ev$a ?v0 )?v2 )(fun_app$c (ev$a ?v1 )?v2 )))):named a22 ))
(assert (! (forall ((?v0 State_rule_prod_stream_bool_fun$ )(?v1 State_rule_prod_stream_bool_fun$ )(?v2 State_rule_prod_stream$ ))(= (fun_app$b (ev$ (fun_app$f (uud$ ?v0 )?v1 ))?v2 )(or (fun_app$b (ev$ ?v0 )?v2 )(fun_app$b (ev$ ?v1 )?v2 )))):named a23 ))
(assert (! (forall ((?v0 Rule_stream$ ))(= (fun_app$c (ev$a uue$ )?v0 )false )):named a24 ))
(assert (! (forall ((?v0 State_rule_prod_stream$ ))(= (fun_app$b (ev$ uuf$ )?v0 )false )):named a25 ))
(assert (! (forall ((?v0 Rule_bool_fun$ )(?v1 Rule_stream$ )(?v2 Rule_bool_fun$ ))(=> (and (fun_app$c (holds$a ?v0 )?v1 )(forall ((?v3 Rule$ ))(=> (fun_app$a ?v0 ?v3 )(fun_app$a ?v2 ?v3 ))))(fun_app$c (holds$a ?v2 )?v1 ))):named a26 ))
(assert (! (forall ((?v0 State_rule_prod_bool_fun$ )(?v1 State_rule_prod_stream$ )(?v2 State_rule_prod_bool_fun$ ))(=> (and (fun_app$b (holds$ ?v0 )?v1 )(forall ((?v3 State_rule_prod$ ))(=> (fun_app$ ?v0 ?v3 )(fun_app$ ?v2 ?v3 ))))(fun_app$b (holds$ ?v2 )?v1 ))):named a27 ))
(assert (! (forall ((?v0 Rule_stream_bool_fun$ )(?v1 Rule_stream$ )(?v2 Rule_stream_bool_fun$ ))(=> (and (fun_app$c (ev$a ?v0 )?v1 )(forall ((?v3 Rule_stream$ ))(=> (fun_app$c ?v0 ?v3 )(fun_app$c ?v2 ?v3 ))))(fun_app$c (ev$a ?v2 )?v1 ))):named a28 ))
(assert (! (forall ((?v0 State_rule_prod_stream_bool_fun$ )(?v1 State_rule_prod_stream$ )(?v2 State_rule_prod_stream_bool_fun$ ))(=> (and (fun_app$b (ev$ ?v0 )?v1 )(forall ((?v3 State_rule_prod_stream$ ))(=> (fun_app$b ?v0 ?v3 )(fun_app$b ?v2 ?v3 ))))(fun_app$b (ev$ ?v2 )?v1 ))):named a29 ))
(assert (! (forall ((?v0 Rule_stream_bool_fun$ )(?v1 Rule_stream$ ))(=> (fun_app$c ?v0 ?v1 )(fun_app$c (ev$a ?v0 )?v1 ))):named a30 ))
(assert (! (forall ((?v0 State_rule_prod_stream_bool_fun$ )(?v1 State_rule_prod_stream$ ))(=> (fun_app$b ?v0 ?v1 )(fun_app$b (ev$ ?v0 )?v1 ))):named a31 ))
(assert (! (fun_app$b (alw$ (holds$ uug$ ))stepsa$ ):named a32 ))
(assert (! (member$a r$ (sset$ rules$ )):named a33 ))
(assert (! (forall ((?v0 Rule_bool_fun$ )(?v1 Rule_stream$ ))(= (fun_app$c (ev$a (holds$a ?v0 ))?v1 )(exists ((?v2 Rule$ ))(and (member$a ?v2 (sset$ ?v1 ))(fun_app$a ?v0 ?v2 ))))):named a34 ))
(assert (! (forall ((?v0 State_rule_prod_bool_fun$ )(?v1 State_rule_prod_stream$ ))(= (fun_app$b (ev$ (holds$ ?v0 ))?v1 )(exists ((?v2 State_rule_prod$ ))(and (member$ ?v2 (sset$a ?v1 ))(fun_app$ ?v0 ?v2 ))))):named a35 ))
(assert (! (forall ((?v0 Rule_state_state_fset_bool_fun_fun_fun$ )(?v1 Rule$ ))(= (fun_app$e (saturated$ ?v0 )?v1 )(alw$ (fun_app$e (uuj$ ?v0 )?v1 )))):named a36 ))
(assert (! (forall ((?v0 Rule_set$ ))(= (hld$ ?v0 )(holds$a (uuk$ ?v0 )))):named a37 ))
(assert (! (forall ((?v0 State_rule_prod_set$ ))(= (hld$a ?v0 )(holds$ (uul$ ?v0 )))):named a38 ))
(assert (! (forall ((?v0 Rule$ )(?v1 State$ ))(! (= (enabled$ eff$ ?v0 ?v1 )(exists ((?v2 State_fset$ ))(fun_app$j (fun_app$k (fun_app$l eff$ ?v0 )?v1 )?v2 ))):pattern ((enabled$ eff$ ?v0 ?v1 )))):named a39 ))
(assert (! (forall ((?v0 Rule_stream_bool_fun$ ))(= (alw$a (alw$a ?v0 ))(alw$a ?v0 ))):named a40 ))
(assert (! (forall ((?v0 State_rule_prod_stream_bool_fun$ ))(= (alw$ (alw$ ?v0 ))(alw$ ?v0 ))):named a41 ))
(assert (! (fun_app$b (alw$ (holds$ uug$ ))steps$ ):named a42 ))
(assert (! (forall ((?v0 State_rule_prod_stream$ ))(= (fun_app$b (fun_app$m (saturated$a eff$ )rules$ )?v0 )(forall ((?v1 Rule$ ))(=> (member$a ?v1 (sset$ rules$ ))(fun_app$b (fun_app$e (saturated$ eff$ )?v1 )?v0 ))))):named a43 ))
(assert (! (forall ((?v0 Rule_stream_bool_fun$ ))(= (uun$ ?v0 )(alw$a ?v0 ))):named a44 ))
(assert (! (forall ((?v0 State_rule_prod_stream_bool_fun$ ))(= (uup$ ?v0 )(alw$ ?v0 ))):named a45 ))
(check-sat )
;(get-unsat-core )
