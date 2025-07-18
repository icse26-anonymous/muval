;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort A_set$ 0 )
(declare-sort B_b_fun$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_llist_set$ 0 )
(declare-sort A_llist_b_fun$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_llist_set$ 0 )
(declare-sort A_llist_b_b_fun_fun$ 0 )
(declare-sort A_llist_llist_bool_fun$ 0 )
(declare-sort A_llist_llist_llist_set$ 0 )
(declare-sort A_llist_a_llist_prod_set$ 0 )
(declare-sort A_a_llist_b_b_fun_fun_fun$ 0 )
(declare-sort A_llist_llist_llist_bool_fun$ 0 )
(declare-sort A_llist_a_llist_prod_bool_fun$ 0 )
(declare-sort A_llist_llist_llist_llist_set$ 0 )
(declare-sort A_llist_a_llist_prod_llist_set$ 0 )
(declare-sort A_llist_llist_llist_llist_bool_fun$ 0 )
(declare-sort A_llist_a_llist_prod_llist_bool_fun$ 0 )
(declare-sort A_llist_a_llist_prod_llist_llist_set$ 0 )
(declare-sort A_llist_llist_a_llist_llist_prod_set$ 0 )
(declare-sort A_llist_a_llist_prod_llist_llist_bool_fun$ 0 )
(declare-sort A_llist_llist_a_llist_llist_prod_llist_set$ 0 )
(declare-sort A_a_llist_b_b_fun_fun_fun_a_llist_b_fun_fun$ 0 )
(declare-sort A_llist_llist_a_llist_llist_prod_llist_bool_fun$ 0 )
(declare-sort A_llist_llist_llist_a_llist_llist_llist_prod_set$ 0 )
(declare-sort A_llist_a_llist_prod_llist_a_llist_a_llist_prod_llist_prod_set$ 0 )
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-datatypes ()((A_llist_a_llist_prod$ (pair$ (fst$ A_llist$ )(snd$ A_llist$ )))))
(declare-sort A_llist_a_llist_prod_llist$ 0)
(declare-sort A_llist_a_llist_prod_llist_llist$ 0)
(declare-sort A_llist_llist$ 0)
(declare-sort A_llist_llist_llist$ 0)
(declare-sort A_llist_llist_llist_llist$ 0)
(declare-fun lNil$a ()A_llist_a_llist_prod_llist$)
(declare-fun lhd$a (A_llist_a_llist_prod_llist$)A_llist_a_llist_prod$)
(declare-fun ltl$a (A_llist_a_llist_prod_llist$)A_llist_a_llist_prod_llist$)
(declare-fun lCons$a (A_llist_a_llist_prod$ A_llist_a_llist_prod_llist$ )A_llist_a_llist_prod_llist$)
(declare-fun lNil$b ()A_llist_a_llist_prod_llist_llist$)
(declare-fun lhd$b (A_llist_a_llist_prod_llist_llist$)A_llist_a_llist_prod_llist$)
(declare-fun ltl$b (A_llist_a_llist_prod_llist_llist$)A_llist_a_llist_prod_llist_llist$)
(declare-fun lCons$b (A_llist_a_llist_prod_llist$ A_llist_a_llist_prod_llist_llist$ )A_llist_a_llist_prod_llist_llist$)
(declare-fun lNil$c ()A_llist_llist$)
(declare-fun lhd$c (A_llist_llist$)A_llist$)
(declare-fun ltl$c (A_llist_llist$)A_llist_llist$)
(declare-fun lCons$c (A_llist$ A_llist_llist$ )A_llist_llist$)
(declare-fun lNil$d ()A_llist_llist_llist$)
(declare-fun lhd$d (A_llist_llist_llist$)A_llist_llist$)
(declare-fun ltl$d (A_llist_llist_llist$)A_llist_llist_llist$)
(declare-fun lCons$d (A_llist_llist$ A_llist_llist_llist$ )A_llist_llist_llist$)
(declare-fun lNil$e ()A_llist_llist_llist_llist$)
(declare-fun lhd$e (A_llist_llist_llist_llist$)A_llist_llist_llist$)
(declare-fun ltl$e (A_llist_llist_llist_llist$)A_llist_llist_llist_llist$)
(declare-fun lCons$e (A_llist_llist_llist$ A_llist_llist_llist_llist$ )A_llist_llist_llist_llist$)
(declare-datatypes ()((A_llist_llist_a_llist_llist_prod$ (pair$a (fst$a A_llist_llist$ )(snd$a A_llist_llist$ )))))
(declare-sort A_llist_llist_a_llist_llist_prod_llist$ 0)
(declare-fun lNil$f ()A_llist_llist_a_llist_llist_prod_llist$)
(declare-fun lhd$f (A_llist_llist_a_llist_llist_prod_llist$)A_llist_llist_a_llist_llist_prod$)
(declare-fun ltl$f (A_llist_llist_a_llist_llist_prod_llist$)A_llist_llist_a_llist_llist_prod_llist$)
(declare-fun lCons$f (A_llist_llist_a_llist_llist_prod$ A_llist_llist_a_llist_llist_prod_llist$ )A_llist_llist_a_llist_llist_prod_llist$)
(declare-datatypes ()((A_llist_a_llist_prod_llist_a_llist_a_llist_prod_llist_prod$ (pair$b (fst$b A_llist_a_llist_prod_llist$ )(snd$b A_llist_a_llist_prod_llist$ )))(A_llist_llist_llist_a_llist_llist_llist_prod$ (pair$c (fst$c A_llist_llist_llist$ )(snd$c A_llist_llist_llist$ )))))
(declare-fun a$ ()A$ )
(declare-fun c$ ()B$ )
(declare-fun d$ ()A_a_llist_b_b_fun_fun_fun$ )
(declare-fun f$ ()A_llist_b_fun$ )
(declare-fun r$ ()A_llist$ )
(declare-fun a$a ()A_set$ )
(declare-fun member$ (A_llist$ A_llist_set$ )Bool )
(declare-fun alllsts$ (A_llist_a_llist_prod_llist_set$ )A_llist_a_llist_prod_llist_llist_set$ )
(declare-fun finlsts$ (A_set$ )A_llist_set$ )
(declare-fun fun_app$ (A_llist_b_fun$ A_llist$ )B$ )
(declare-fun member$a (A_llist_a_llist_prod_llist_llist$ A_llist_a_llist_prod_llist_llist_set$ )Bool )
(declare-fun member$b (A_llist_a_llist_prod_llist$ A_llist_a_llist_prod_llist_set$ )Bool )
(declare-fun member$c (A_llist_llist_llist_llist$ A_llist_llist_llist_llist_set$ )Bool )
(declare-fun member$d (A_llist_llist_llist$ A_llist_llist_llist_set$ )Bool )
(declare-fun member$e (A_llist_llist_a_llist_llist_prod_llist$ A_llist_llist_a_llist_llist_prod_llist_set$ )Bool )
(declare-fun member$f (A_llist_llist_a_llist_llist_prod$ A_llist_llist_a_llist_llist_prod_set$ )Bool )
(declare-fun member$g (A_llist_llist$ A_llist_llist_set$ )Bool )
(declare-fun member$h (A_llist_a_llist_prod$ A_llist_a_llist_prod_set$ )Bool )
(declare-fun member$i (A$ A_set$ )Bool )
(declare-fun member$j (A_llist_a_llist_prod_llist_a_llist_a_llist_prod_llist_prod$ A_llist_a_llist_prod_llist_a_llist_a_llist_prod_llist_prod_set$ )Bool )
(declare-fun member$k (A_llist_llist_llist_a_llist_llist_llist_prod$ A_llist_llist_llist_a_llist_llist_llist_prod_set$ )Bool )
(declare-fun alllsts$a (A_llist_llist_llist_set$ )A_llist_llist_llist_llist_set$ )
(declare-fun alllsts$b (A_llist_llist_a_llist_llist_prod_set$ )A_llist_llist_a_llist_llist_prod_llist_set$ )
(declare-fun alllsts$c (A_llist_llist_set$ )A_llist_llist_llist_set$ )
(declare-fun alllsts$d (A_llist_a_llist_prod_set$ )A_llist_a_llist_prod_llist_set$ )
(declare-fun alllsts$e (A_llist_set$ )A_llist_llist_set$ )
(declare-fun alllsts$f (A_set$ )A_llist_set$ )
(declare-fun alllstsp$ (A_llist_a_llist_prod_bool_fun$ )A_llist_a_llist_prod_llist_bool_fun$ )
(declare-fun finlsts$a (A_llist_a_llist_prod_llist_set$ )A_llist_a_llist_prod_llist_llist_set$ )
(declare-fun finlsts$b (A_llist_llist_llist_set$ )A_llist_llist_llist_llist_set$ )
(declare-fun finlsts$c (A_llist_llist_a_llist_llist_prod_set$ )A_llist_llist_a_llist_llist_prod_llist_set$ )
(declare-fun finlsts$d (A_llist_llist_set$ )A_llist_llist_llist_set$ )
(declare-fun finlsts$e (A_llist_a_llist_prod_set$ )A_llist_a_llist_prod_llist_set$ )
(declare-fun finlsts$f (A_llist_set$ )A_llist_llist_set$ )
(declare-fun finlstsp$ (A_llist_a_llist_prod_bool_fun$ )A_llist_a_llist_prod_llist_bool_fun$ )
(declare-fun fun_app$a (B_b_fun$ B$ )B$ )
(declare-fun fun_app$b (A_llist_b_b_fun_fun$ A_llist$ )B_b_fun$ )
(declare-fun fun_app$c (A_a_llist_b_b_fun_fun_fun$ A$ )A_llist_b_b_fun_fun$ )
(declare-fun fun_app$d (A_a_llist_b_b_fun_fun_fun_a_llist_b_fun_fun$ A_a_llist_b_b_fun_fun_fun$ )A_llist_b_fun$ )
(declare-fun fun_app$e (A_llist_a_llist_prod_llist_llist_bool_fun$ A_llist_a_llist_prod_llist_llist$ )Bool )
(declare-fun fun_app$f (A_llist_llist_llist_llist_bool_fun$ A_llist_llist_llist_llist$ )Bool )
(declare-fun fun_app$g (A_llist_llist_a_llist_llist_prod_llist_bool_fun$ A_llist_llist_a_llist_llist_prod_llist$ )Bool )
(declare-fun fun_app$h (A_llist_llist_llist_bool_fun$ A_llist_llist_llist$ )Bool )
(declare-fun fun_app$i (A_llist_a_llist_prod_llist_bool_fun$ A_llist_a_llist_prod_llist$ )Bool )
(declare-fun fun_app$j (A_llist_llist_bool_fun$ A_llist_llist$ )Bool )
(declare-fun fun_app$k (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun fun_app$l (A_llist_a_llist_prod_bool_fun$ A_llist_a_llist_prod$ )Bool )
(declare-fun fun_app$m (A_bool_fun$ A$ )Bool )
(declare-fun alllstsp$a (A_llist_llist_bool_fun$ )A_llist_llist_llist_bool_fun$ )
(declare-fun alllstsp$b (A_llist_bool_fun$ )A_llist_llist_bool_fun$ )
(declare-fun alllstsp$c (A_bool_fun$ )A_llist_bool_fun$ )
(declare-fun finlstsp$a (A_llist_llist_bool_fun$ )A_llist_llist_llist_bool_fun$ )
(declare-fun finlstsp$b (A_llist_bool_fun$ )A_llist_llist_bool_fun$ )
(declare-fun finlstsp$c (A_bool_fun$ )A_llist_bool_fun$ )
(declare-fun finlsts_rec$ (B$ )A_a_llist_b_b_fun_fun_fun_a_llist_b_fun_fun$ )
(declare-fun finlsts_pred$ ()A_llist_a_llist_prod_llist_a_llist_a_llist_prod_llist_prod_set$ )
(declare-fun finlsts_pred$a ()A_llist_llist_llist_a_llist_llist_llist_prod_set$ )
(declare-fun finlsts_pred$b ()A_llist_llist_a_llist_llist_prod_set$ )
(declare-fun finlsts_pred$c ()A_llist_a_llist_prod_set$ )
(assert (! (not (= (fun_app$ f$ (lCons$ a$ r$ ))(fun_app$a (fun_app$b (fun_app$c d$ a$ )r$ )(fun_app$ f$ r$ )))):named a0 ))
(assert (! (= f$ (fun_app$d (finlsts_rec$ c$ )d$ )):named a1 ))
(assert (! (member$ r$ (finlsts$ a$a )):named a2 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_llist_llist$ )(?v1 A_llist_a_llist_prod_llist_set$ )(?v2 A_llist_a_llist_prod_llist$ ))(=> (and (member$a ?v0 (finlsts$a ?v1 ))(member$b ?v2 ?v1 ))(member$a (lCons$b ?v2 ?v0 )(finlsts$a ?v1 )))):named a3 ))
(assert (! (forall ((?v0 A_llist_llist_llist_llist$ )(?v1 A_llist_llist_llist_set$ )(?v2 A_llist_llist_llist$ ))(=> (and (member$c ?v0 (finlsts$b ?v1 ))(member$d ?v2 ?v1 ))(member$c (lCons$e ?v2 ?v0 )(finlsts$b ?v1 )))):named a4 ))
(assert (! (forall ((?v0 A_llist_llist_a_llist_llist_prod_llist$ )(?v1 A_llist_llist_a_llist_llist_prod_set$ )(?v2 A_llist_llist_a_llist_llist_prod$ ))(=> (and (member$e ?v0 (finlsts$c ?v1 ))(member$f ?v2 ?v1 ))(member$e (lCons$f ?v2 ?v0 )(finlsts$c ?v1 )))):named a5 ))
(assert (! (forall ((?v0 A_llist_llist_llist$ )(?v1 A_llist_llist_set$ )(?v2 A_llist_llist$ ))(=> (and (member$d ?v0 (finlsts$d ?v1 ))(member$g ?v2 ?v1 ))(member$d (lCons$d ?v2 ?v0 )(finlsts$d ?v1 )))):named a6 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_llist$ )(?v1 A_llist_a_llist_prod_set$ )(?v2 A_llist_a_llist_prod$ ))(=> (and (member$b ?v0 (finlsts$e ?v1 ))(member$h ?v2 ?v1 ))(member$b (lCons$a ?v2 ?v0 )(finlsts$e ?v1 )))):named a7 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_set$ )(?v2 A_llist$ ))(=> (and (member$g ?v0 (finlsts$f ?v1 ))(member$ ?v2 ?v1 ))(member$g (lCons$c ?v2 ?v0 )(finlsts$f ?v1 )))):named a8 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set$ )(?v2 A$ ))(=> (and (member$ ?v0 (finlsts$ ?v1 ))(member$i ?v2 ?v1 ))(member$ (lCons$ ?v2 ?v0 )(finlsts$ ?v1 )))):named a9 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set$ )(?v2 B$ )(?v3 A_a_llist_b_b_fun_fun_fun$ )(?v4 A$ ))(=> (member$ ?v0 (finlsts$ ?v1 ))(= (fun_app$ (fun_app$d (finlsts_rec$ ?v2 )?v3 )(lCons$ ?v4 ?v0 ))(fun_app$a (fun_app$b (fun_app$c ?v3 ?v4 )?v0 )(fun_app$ (fun_app$d (finlsts_rec$ ?v2 )?v3 )?v0 ))))):named a10 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod$ )(?v1 A_llist_a_llist_prod_llist$ )(?v2 A_llist_a_llist_prod$ )(?v3 A_llist_a_llist_prod_llist$ ))(= (= (lCons$a ?v0 ?v1 )(lCons$a ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a11 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_llist_llist$ )(?v2 A_llist_llist$ )(?v3 A_llist_llist_llist$ ))(= (= (lCons$d ?v0 ?v1 )(lCons$d ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a12 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist_llist$ )(?v2 A_llist$ )(?v3 A_llist_llist$ ))(= (= (lCons$c ?v0 ?v1 )(lCons$c ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a13 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a14 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_llist_llist$ )(?v1 A_llist_a_llist_prod_llist_set$ ))(= (member$a ?v0 (finlsts$a ?v1 ))(or (= ?v0 lNil$b )(exists ((?v2 A_llist_a_llist_prod_llist_llist$ )(?v3 A_llist_a_llist_prod_llist$ ))(and (= ?v0 (lCons$b ?v3 ?v2 ))(and (member$a ?v2 (finlsts$a ?v1 ))(member$b ?v3 ?v1 ))))))):named a15 ))
(assert (! (forall ((?v0 A_llist_llist_llist_llist$ )(?v1 A_llist_llist_llist_set$ ))(= (member$c ?v0 (finlsts$b ?v1 ))(or (= ?v0 lNil$e )(exists ((?v2 A_llist_llist_llist_llist$ )(?v3 A_llist_llist_llist$ ))(and (= ?v0 (lCons$e ?v3 ?v2 ))(and (member$c ?v2 (finlsts$b ?v1 ))(member$d ?v3 ?v1 ))))))):named a16 ))
(assert (! (forall ((?v0 A_llist_llist_a_llist_llist_prod_llist$ )(?v1 A_llist_llist_a_llist_llist_prod_set$ ))(= (member$e ?v0 (finlsts$c ?v1 ))(or (= ?v0 lNil$f )(exists ((?v2 A_llist_llist_a_llist_llist_prod_llist$ )(?v3 A_llist_llist_a_llist_llist_prod$ ))(and (= ?v0 (lCons$f ?v3 ?v2 ))(and (member$e ?v2 (finlsts$c ?v1 ))(member$f ?v3 ?v1 ))))))):named a17 ))
(assert (! (forall ((?v0 A_llist_llist_llist$ )(?v1 A_llist_llist_set$ ))(= (member$d ?v0 (finlsts$d ?v1 ))(or (= ?v0 lNil$d )(exists ((?v2 A_llist_llist_llist$ )(?v3 A_llist_llist$ ))(and (= ?v0 (lCons$d ?v3 ?v2 ))(and (member$d ?v2 (finlsts$d ?v1 ))(member$g ?v3 ?v1 ))))))):named a18 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_llist$ )(?v1 A_llist_a_llist_prod_set$ ))(= (member$b ?v0 (finlsts$e ?v1 ))(or (= ?v0 lNil$a )(exists ((?v2 A_llist_a_llist_prod_llist$ )(?v3 A_llist_a_llist_prod$ ))(and (= ?v0 (lCons$a ?v3 ?v2 ))(and (member$b ?v2 (finlsts$e ?v1 ))(member$h ?v3 ?v1 ))))))):named a19 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_set$ ))(= (member$g ?v0 (finlsts$f ?v1 ))(or (= ?v0 lNil$c )(exists ((?v2 A_llist_llist$ )(?v3 A_llist$ ))(and (= ?v0 (lCons$c ?v3 ?v2 ))(and (member$g ?v2 (finlsts$f ?v1 ))(member$ ?v3 ?v1 ))))))):named a20 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set$ ))(= (member$ ?v0 (finlsts$ ?v1 ))(or (= ?v0 lNil$ )(exists ((?v2 A_llist$ )(?v3 A$ ))(and (= ?v0 (lCons$ ?v3 ?v2 ))(and (member$ ?v2 (finlsts$ ?v1 ))(member$i ?v3 ?v1 ))))))):named a21 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_llist_llist$ )(?v1 A_llist_a_llist_prod_llist_set$ ))(=> (and (member$a ?v0 (finlsts$a ?v1 ))(and (=> (= ?v0 lNil$b )false )(forall ((?v2 A_llist_a_llist_prod_llist_llist$ )(?v3 A_llist_a_llist_prod_llist$ ))(=> (and (= ?v0 (lCons$b ?v3 ?v2 ))(and (member$a ?v2 (finlsts$a ?v1 ))(member$b ?v3 ?v1 )))false ))))false )):named a22 ))
(assert (! (forall ((?v0 A_llist_llist_llist_llist$ )(?v1 A_llist_llist_llist_set$ ))(=> (and (member$c ?v0 (finlsts$b ?v1 ))(and (=> (= ?v0 lNil$e )false )(forall ((?v2 A_llist_llist_llist_llist$ )(?v3 A_llist_llist_llist$ ))(=> (and (= ?v0 (lCons$e ?v3 ?v2 ))(and (member$c ?v2 (finlsts$b ?v1 ))(member$d ?v3 ?v1 )))false ))))false )):named a23 ))
(assert (! (forall ((?v0 A_llist_llist_a_llist_llist_prod_llist$ )(?v1 A_llist_llist_a_llist_llist_prod_set$ ))(=> (and (member$e ?v0 (finlsts$c ?v1 ))(and (=> (= ?v0 lNil$f )false )(forall ((?v2 A_llist_llist_a_llist_llist_prod_llist$ )(?v3 A_llist_llist_a_llist_llist_prod$ ))(=> (and (= ?v0 (lCons$f ?v3 ?v2 ))(and (member$e ?v2 (finlsts$c ?v1 ))(member$f ?v3 ?v1 )))false ))))false )):named a24 ))
(assert (! (forall ((?v0 A_llist_llist_llist$ )(?v1 A_llist_llist_set$ ))(=> (and (member$d ?v0 (finlsts$d ?v1 ))(and (=> (= ?v0 lNil$d )false )(forall ((?v2 A_llist_llist_llist$ )(?v3 A_llist_llist$ ))(=> (and (= ?v0 (lCons$d ?v3 ?v2 ))(and (member$d ?v2 (finlsts$d ?v1 ))(member$g ?v3 ?v1 )))false ))))false )):named a25 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_llist$ )(?v1 A_llist_a_llist_prod_set$ ))(=> (and (member$b ?v0 (finlsts$e ?v1 ))(and (=> (= ?v0 lNil$a )false )(forall ((?v2 A_llist_a_llist_prod_llist$ )(?v3 A_llist_a_llist_prod$ ))(=> (and (= ?v0 (lCons$a ?v3 ?v2 ))(and (member$b ?v2 (finlsts$e ?v1 ))(member$h ?v3 ?v1 )))false ))))false )):named a26 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_set$ ))(=> (and (member$g ?v0 (finlsts$f ?v1 ))(and (=> (= ?v0 lNil$c )false )(forall ((?v2 A_llist_llist$ )(?v3 A_llist$ ))(=> (and (= ?v0 (lCons$c ?v3 ?v2 ))(and (member$g ?v2 (finlsts$f ?v1 ))(member$ ?v3 ?v1 )))false ))))false )):named a27 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set$ ))(=> (and (member$ ?v0 (finlsts$ ?v1 ))(and (=> (= ?v0 lNil$ )false )(forall ((?v2 A_llist$ )(?v3 A$ ))(=> (and (= ?v0 (lCons$ ?v3 ?v2 ))(and (member$ ?v2 (finlsts$ ?v1 ))(member$i ?v3 ?v1 )))false ))))false )):named a28 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_llist_llist$ )(?v1 A_llist_a_llist_prod_llist_set$ )(?v2 A_llist_a_llist_prod_llist_llist_bool_fun$ ))(=> (and (member$a ?v0 (finlsts$a ?v1 ))(and (forall ((?v3 A_llist_a_llist_prod_llist_llist$ ))(=> (= ?v3 lNil$b )(fun_app$e ?v2 ?v3 )))(forall ((?v3 A_llist_a_llist_prod_llist$ )(?v4 A_llist_a_llist_prod_llist_llist$ ))(=> (and (member$a ?v4 (finlsts$a ?v1 ))(and (fun_app$e ?v2 ?v4 )(member$b ?v3 ?v1 )))(fun_app$e ?v2 (lCons$b ?v3 ?v4 ))))))(fun_app$e ?v2 ?v0 ))):named a29 ))
(assert (! (forall ((?v0 A_llist_llist_llist_llist$ )(?v1 A_llist_llist_llist_set$ )(?v2 A_llist_llist_llist_llist_bool_fun$ ))(=> (and (member$c ?v0 (finlsts$b ?v1 ))(and (forall ((?v3 A_llist_llist_llist_llist$ ))(=> (= ?v3 lNil$e )(fun_app$f ?v2 ?v3 )))(forall ((?v3 A_llist_llist_llist$ )(?v4 A_llist_llist_llist_llist$ ))(=> (and (member$c ?v4 (finlsts$b ?v1 ))(and (fun_app$f ?v2 ?v4 )(member$d ?v3 ?v1 )))(fun_app$f ?v2 (lCons$e ?v3 ?v4 ))))))(fun_app$f ?v2 ?v0 ))):named a30 ))
(assert (! (forall ((?v0 A_llist_llist_a_llist_llist_prod_llist$ )(?v1 A_llist_llist_a_llist_llist_prod_set$ )(?v2 A_llist_llist_a_llist_llist_prod_llist_bool_fun$ ))(=> (and (member$e ?v0 (finlsts$c ?v1 ))(and (forall ((?v3 A_llist_llist_a_llist_llist_prod_llist$ ))(=> (= ?v3 lNil$f )(fun_app$g ?v2 ?v3 )))(forall ((?v3 A_llist_llist_a_llist_llist_prod$ )(?v4 A_llist_llist_a_llist_llist_prod_llist$ ))(=> (and (member$e ?v4 (finlsts$c ?v1 ))(and (fun_app$g ?v2 ?v4 )(member$f ?v3 ?v1 )))(fun_app$g ?v2 (lCons$f ?v3 ?v4 ))))))(fun_app$g ?v2 ?v0 ))):named a31 ))
(assert (! (forall ((?v0 A_llist_llist_llist$ )(?v1 A_llist_llist_set$ )(?v2 A_llist_llist_llist_bool_fun$ ))(=> (and (member$d ?v0 (finlsts$d ?v1 ))(and (forall ((?v3 A_llist_llist_llist$ ))(=> (= ?v3 lNil$d )(fun_app$h ?v2 ?v3 )))(forall ((?v3 A_llist_llist$ )(?v4 A_llist_llist_llist$ ))(=> (and (member$d ?v4 (finlsts$d ?v1 ))(and (fun_app$h ?v2 ?v4 )(member$g ?v3 ?v1 )))(fun_app$h ?v2 (lCons$d ?v3 ?v4 ))))))(fun_app$h ?v2 ?v0 ))):named a32 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_llist$ )(?v1 A_llist_a_llist_prod_set$ )(?v2 A_llist_a_llist_prod_llist_bool_fun$ ))(=> (and (member$b ?v0 (finlsts$e ?v1 ))(and (forall ((?v3 A_llist_a_llist_prod_llist$ ))(=> (= ?v3 lNil$a )(fun_app$i ?v2 ?v3 )))(forall ((?v3 A_llist_a_llist_prod$ )(?v4 A_llist_a_llist_prod_llist$ ))(=> (and (member$b ?v4 (finlsts$e ?v1 ))(and (fun_app$i ?v2 ?v4 )(member$h ?v3 ?v1 )))(fun_app$i ?v2 (lCons$a ?v3 ?v4 ))))))(fun_app$i ?v2 ?v0 ))):named a33 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_set$ )(?v2 A_llist_llist_bool_fun$ ))(=> (and (member$g ?v0 (finlsts$f ?v1 ))(and (forall ((?v3 A_llist_llist$ ))(=> (= ?v3 lNil$c )(fun_app$j ?v2 ?v3 )))(forall ((?v3 A_llist$ )(?v4 A_llist_llist$ ))(=> (and (member$g ?v4 (finlsts$f ?v1 ))(and (fun_app$j ?v2 ?v4 )(member$ ?v3 ?v1 )))(fun_app$j ?v2 (lCons$c ?v3 ?v4 ))))))(fun_app$j ?v2 ?v0 ))):named a34 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set$ )(?v2 A_llist_bool_fun$ ))(=> (and (member$ ?v0 (finlsts$ ?v1 ))(and (forall ((?v3 A_llist$ ))(=> (= ?v3 lNil$ )(fun_app$k ?v2 ?v3 )))(forall ((?v3 A$ )(?v4 A_llist$ ))(=> (and (member$ ?v4 (finlsts$ ?v1 ))(and (fun_app$k ?v2 ?v4 )(member$i ?v3 ?v1 )))(fun_app$k ?v2 (lCons$ ?v3 ?v4 ))))))(fun_app$k ?v2 ?v0 ))):named a35 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_llist$ )(?v1 A_llist_a_llist_prod_llist_llist$ )(?v2 A_llist_a_llist_prod_llist_set$ ))(= (member$a (lCons$b ?v0 ?v1 )(alllsts$ ?v2 ))(and (member$b ?v0 ?v2 )(member$a ?v1 (alllsts$ ?v2 ))))):named a36 ))
(assert (! (forall ((?v0 A_llist_llist_llist$ )(?v1 A_llist_llist_llist_llist$ )(?v2 A_llist_llist_llist_set$ ))(= (member$c (lCons$e ?v0 ?v1 )(alllsts$a ?v2 ))(and (member$d ?v0 ?v2 )(member$c ?v1 (alllsts$a ?v2 ))))):named a37 ))
(assert (! (forall ((?v0 A_llist_llist_a_llist_llist_prod$ )(?v1 A_llist_llist_a_llist_llist_prod_llist$ )(?v2 A_llist_llist_a_llist_llist_prod_set$ ))(= (member$e (lCons$f ?v0 ?v1 )(alllsts$b ?v2 ))(and (member$f ?v0 ?v2 )(member$e ?v1 (alllsts$b ?v2 ))))):named a38 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_llist_llist$ )(?v2 A_llist_llist_set$ ))(= (member$d (lCons$d ?v0 ?v1 )(alllsts$c ?v2 ))(and (member$g ?v0 ?v2 )(member$d ?v1 (alllsts$c ?v2 ))))):named a39 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod$ )(?v1 A_llist_a_llist_prod_llist$ )(?v2 A_llist_a_llist_prod_set$ ))(= (member$b (lCons$a ?v0 ?v1 )(alllsts$d ?v2 ))(and (member$h ?v0 ?v2 )(member$b ?v1 (alllsts$d ?v2 ))))):named a40 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist_llist$ )(?v2 A_llist_set$ ))(= (member$g (lCons$c ?v0 ?v1 )(alllsts$e ?v2 ))(and (member$ ?v0 ?v2 )(member$g ?v1 (alllsts$e ?v2 ))))):named a41 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A_set$ ))(= (member$ (lCons$ ?v0 ?v1 )(alllsts$f ?v2 ))(and (member$i ?v0 ?v2 )(member$ ?v1 (alllsts$f ?v2 ))))):named a42 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_bool_fun$ )(?v1 A_llist_a_llist_prod_llist$ )(?v2 A_llist_a_llist_prod$ ))(=> (and (fun_app$i (finlstsp$ ?v0 )?v1 )(fun_app$l ?v0 ?v2 ))(fun_app$i (finlstsp$ ?v0 )(lCons$a ?v2 ?v1 )))):named a43 ))
(assert (! (forall ((?v0 A_llist_llist_bool_fun$ )(?v1 A_llist_llist_llist$ )(?v2 A_llist_llist$ ))(=> (and (fun_app$h (finlstsp$a ?v0 )?v1 )(fun_app$j ?v0 ?v2 ))(fun_app$h (finlstsp$a ?v0 )(lCons$d ?v2 ?v1 )))):named a44 ))
(assert (! (forall ((?v0 A_llist_bool_fun$ )(?v1 A_llist_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$j (finlstsp$b ?v0 )?v1 )(fun_app$k ?v0 ?v2 ))(fun_app$j (finlstsp$b ?v0 )(lCons$c ?v2 ?v1 )))):named a45 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_llist$ )(?v2 A$ ))(=> (and (fun_app$k (finlstsp$c ?v0 )?v1 )(fun_app$m ?v0 ?v2 ))(fun_app$k (finlstsp$c ?v0 )(lCons$ ?v2 ?v1 )))):named a46 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_bool_fun$ )(?v1 A_llist_a_llist_prod_llist$ )(?v2 A_llist_a_llist_prod$ ))(=> (and (fun_app$i (alllstsp$ ?v0 )?v1 )(fun_app$l ?v0 ?v2 ))(fun_app$i (alllstsp$ ?v0 )(lCons$a ?v2 ?v1 )))):named a47 ))
(assert (! (forall ((?v0 A_llist_llist_bool_fun$ )(?v1 A_llist_llist_llist$ )(?v2 A_llist_llist$ ))(=> (and (fun_app$h (alllstsp$a ?v0 )?v1 )(fun_app$j ?v0 ?v2 ))(fun_app$h (alllstsp$a ?v0 )(lCons$d ?v2 ?v1 )))):named a48 ))
(assert (! (forall ((?v0 A_llist_bool_fun$ )(?v1 A_llist_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$j (alllstsp$b ?v0 )?v1 )(fun_app$k ?v0 ?v2 ))(fun_app$j (alllstsp$b ?v0 )(lCons$c ?v2 ?v1 )))):named a49 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_llist$ )(?v2 A$ ))(=> (and (fun_app$k (alllstsp$c ?v0 )?v1 )(fun_app$m ?v0 ?v2 ))(fun_app$k (alllstsp$c ?v0 )(lCons$ ?v2 ?v1 )))):named a50 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_llist$ )(?v1 A_llist_a_llist_prod_set$ )(?v2 A_llist_a_llist_prod_set$ ))(=> (and (member$b ?v0 (finlsts$e ?v1 ))(member$b ?v0 (alllsts$d ?v2 )))(member$b ?v0 (finlsts$e ?v2 )))):named a51 ))
(assert (! (forall ((?v0 A_llist_llist_llist$ )(?v1 A_llist_llist_set$ )(?v2 A_llist_llist_set$ ))(=> (and (member$d ?v0 (finlsts$d ?v1 ))(member$d ?v0 (alllsts$c ?v2 )))(member$d ?v0 (finlsts$d ?v2 )))):named a52 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_set$ )(?v2 A_llist_set$ ))(=> (and (member$g ?v0 (finlsts$f ?v1 ))(member$g ?v0 (alllsts$e ?v2 )))(member$g ?v0 (finlsts$f ?v2 )))):named a53 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set$ )(?v2 A_set$ ))(=> (and (member$ ?v0 (finlsts$ ?v1 ))(member$ ?v0 (alllsts$f ?v2 )))(member$ ?v0 (finlsts$ ?v2 )))):named a54 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_llist$ )(?v1 A_llist_a_llist_prod_set$ ))(=> (member$b ?v0 (finlsts$e ?v1 ))(member$b ?v0 (alllsts$d ?v1 )))):named a55 ))
(assert (! (forall ((?v0 A_llist_llist_llist$ )(?v1 A_llist_llist_set$ ))(=> (member$d ?v0 (finlsts$d ?v1 ))(member$d ?v0 (alllsts$c ?v1 )))):named a56 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_set$ ))(=> (member$g ?v0 (finlsts$f ?v1 ))(member$g ?v0 (alllsts$e ?v1 )))):named a57 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set$ ))(=> (member$ ?v0 (finlsts$ ?v1 ))(member$ ?v0 (alllsts$f ?v1 )))):named a58 ))
(assert (! (forall ((?v0 B$ )(?v1 A_a_llist_b_b_fun_fun_fun$ ))(! (= (fun_app$ (fun_app$d (finlsts_rec$ ?v0 )?v1 )lNil$ )?v0 ):pattern ((fun_app$d (finlsts_rec$ ?v0 )?v1 )))):named a59 ))
(assert (! (forall ((?v0 A_llist_b_fun$ )(?v1 B$ )(?v2 A_a_llist_b_b_fun_fun_fun$ ))(=> (= ?v0 (fun_app$d (finlsts_rec$ ?v1 )?v2 ))(= (fun_app$ ?v0 lNil$ )?v1 ))):named a60 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_llist$ )(?v1 A_llist_a_llist_prod_set$ )(?v2 A_llist_a_llist_prod$ ))(=> (member$b ?v0 (finlsts$e ?v1 ))(member$j (pair$b ?v0 (lCons$a ?v2 ?v0 ))finlsts_pred$ ))):named a61 ))
(assert (! (forall ((?v0 A_llist_llist_llist$ )(?v1 A_llist_llist_set$ )(?v2 A_llist_llist$ ))(=> (member$d ?v0 (finlsts$d ?v1 ))(member$k (pair$c ?v0 (lCons$d ?v2 ?v0 ))finlsts_pred$a ))):named a62 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_set$ )(?v2 A_llist$ ))(=> (member$g ?v0 (finlsts$f ?v1 ))(member$f (pair$a ?v0 (lCons$c ?v2 ?v0 ))finlsts_pred$b ))):named a63 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set$ )(?v2 A$ ))(=> (member$ ?v0 (finlsts$ ?v1 ))(member$h (pair$ ?v0 (lCons$ ?v2 ?v0 ))finlsts_pred$c ))):named a64 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_set$ ))(member$b lNil$a (alllsts$d ?v0 ))):named a65 ))
(assert (! (forall ((?v0 A_llist_llist_set$ ))(member$d lNil$d (alllsts$c ?v0 ))):named a66 ))
(assert (! (forall ((?v0 A_llist_set$ ))(member$g lNil$c (alllsts$e ?v0 ))):named a67 ))
(assert (! (forall ((?v0 A_set$ ))(member$ lNil$ (alllsts$f ?v0 ))):named a68 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_bool_fun$ ))(fun_app$i (alllstsp$ ?v0 )lNil$a )):named a69 ))
(assert (! (forall ((?v0 A_llist_llist_bool_fun$ ))(fun_app$h (alllstsp$a ?v0 )lNil$d )):named a70 ))
(assert (! (forall ((?v0 A_llist_bool_fun$ ))(fun_app$j (alllstsp$b ?v0 )lNil$c )):named a71 ))
(assert (! (forall ((?v0 A_bool_fun$ ))(fun_app$k (alllstsp$c ?v0 )lNil$ )):named a72 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_bool_fun$ ))(fun_app$i (finlstsp$ ?v0 )lNil$a )):named a73 ))
(assert (! (forall ((?v0 A_llist_llist_bool_fun$ ))(fun_app$h (finlstsp$a ?v0 )lNil$d )):named a74 ))
(assert (! (forall ((?v0 A_llist_bool_fun$ ))(fun_app$j (finlstsp$b ?v0 )lNil$c )):named a75 ))
(assert (! (forall ((?v0 A_bool_fun$ ))(fun_app$k (finlstsp$c ?v0 )lNil$ )):named a76 ))
(check-sat )
;(get-unsat-core )
