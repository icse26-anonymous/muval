;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_llist_set$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_llist_set$ 0 )
(declare-sort A_llist_llist_llist_set$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))(A_llist_llist$ (lNil$a )(lCons$a (lhd$a A_llist$ )(ltl$a A_llist_llist$ )))(A_llist_llist_llist$ (lNil$b )(lCons$b (lhd$b A_llist_llist$ )(ltl$b A_llist_llist_llist$ )))))
(declare-fun a$ ()A$ )
(declare-fun a$a ()A_set$ )
(declare-fun lconst$ (A$ )A_llist$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun alllsts$ (A_llist_llist_set$ )A_llist_llist_llist_set$ )
(declare-fun fun_app$ (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun inflsts$ (A_llist_llist_set$ )A_llist_llist_llist_set$ )
(declare-fun lconst$a (A_llist$ )A_llist_llist$ )
(declare-fun lmember$ (A_llist$ A_llist_llist$ )Bool )
(declare-fun member$a (A_llist_llist_llist$ A_llist_llist_llist_set$ )Bool )
(declare-fun member$b (A_llist_llist$ A_llist_llist_set$ )Bool )
(declare-fun member$c (A_llist$ A_llist_set$ )Bool )
(declare-fun alllsts$a (A_llist_set$ )A_llist_llist_set$ )
(declare-fun alllsts$b (A_set$ )A_llist_set$ )
(declare-fun alllstsp$ (A_llist_bool_fun$ A_llist_llist$ )Bool )
(declare-fun finlstsp$ (A_llist_bool_fun$ A_llist_llist$ )Bool )
(declare-fun fun_app$a (A_bool_fun$ A$ )Bool )
(declare-fun inflsts$a (A_llist_set$ )A_llist_llist_set$ )
(declare-fun inflsts$b (A_set$ )A_llist_set$ )
(declare-fun lmember$a (A$ )A_llist_bool_fun$ )
(declare-fun alllstsp$a (A_bool_fun$ )A_llist_bool_fun$ )
(declare-fun finlstsp$a (A_bool_fun$ )A_llist_bool_fun$ )
(declare-fun pred_llist$ (A_llist_bool_fun$ A_llist_llist$ )Bool )
(declare-fun pred_llist$a (A_bool_fun$ )A_llist_bool_fun$ )
(declare-fun lstrict_prefix$ (A_llist_llist$ A_llist_llist$ )Bool )
(declare-fun lstrict_prefix$a (A_llist$ )A_llist_bool_fun$ )
(assert (! (not (= (lconst$ a$ )(lCons$ a$ (lconst$ a$ )))):named a0 ))
(assert (! (member$ a$ a$a ):named a1 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (lconst$a ?v0 )(lCons$a ?v0 (lconst$a ?v0 ))):pattern ((lconst$a ?v0 )))):named a2 ))
(assert (! (forall ((?v0 A$ ))(! (= (lconst$ ?v0 )(lCons$ ?v0 (lconst$ ?v0 ))):pattern ((lconst$ ?v0 )))):named a3 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist_llist$ )(?v2 A_llist$ )(?v3 A_llist_llist$ ))(= (= (lCons$a ?v0 ?v1 )(lCons$a ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a4 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a5 ))
(assert (! (forall ((?v0 A_llist_bool_fun$ )(?v1 A_llist_llist$ )(?v2 A_llist$ ))(=> (and (finlstsp$ ?v0 ?v1 )(fun_app$ ?v0 ?v2 ))(finlstsp$ ?v0 (lCons$a ?v2 ?v1 )))):named a6 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_llist$ )(?v2 A$ ))(=> (and (fun_app$ (finlstsp$a ?v0 )?v1 )(fun_app$a ?v0 ?v2 ))(fun_app$ (finlstsp$a ?v0 )(lCons$ ?v2 ?v1 )))):named a7 ))
(assert (! (forall ((?v0 A_llist_bool_fun$ )(?v1 A_llist_llist$ )(?v2 A_llist$ ))(=> (and (alllstsp$ ?v0 ?v1 )(fun_app$ ?v0 ?v2 ))(alllstsp$ ?v0 (lCons$a ?v2 ?v1 )))):named a8 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_llist$ )(?v2 A$ ))(=> (and (fun_app$ (alllstsp$a ?v0 )?v1 )(fun_app$a ?v0 ?v2 ))(fun_app$ (alllstsp$a ?v0 )(lCons$ ?v2 ?v1 )))):named a9 ))
(assert (! (forall ((?v0 A$ ))(not (= (lconst$ ?v0 )lNil$ ))):named a10 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_llist_llist$ )(?v2 A_llist_llist_set$ ))(= (member$a (lCons$b ?v0 ?v1 )(alllsts$ ?v2 ))(and (member$b ?v0 ?v2 )(member$a ?v1 (alllsts$ ?v2 ))))):named a11 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist_llist$ )(?v2 A_llist_set$ ))(= (member$b (lCons$a ?v0 ?v1 )(alllsts$a ?v2 ))(and (member$c ?v0 ?v2 )(member$b ?v1 (alllsts$a ?v2 ))))):named a12 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A_set$ ))(= (member$c (lCons$ ?v0 ?v1 )(alllsts$b ?v2 ))(and (member$ ?v0 ?v2 )(member$c ?v1 (alllsts$b ?v2 ))))):named a13 ))
(assert (! (forall ((?v0 A_llist_llist_llist$ )(?v1 A_llist_llist_set$ )(?v2 A_llist_llist$ ))(=> (and (member$a ?v0 (alllsts$ ?v1 ))(member$b ?v2 ?v1 ))(member$a (lCons$b ?v2 ?v0 )(alllsts$ ?v1 )))):named a14 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_set$ )(?v2 A_llist$ ))(=> (and (member$b ?v0 (alllsts$a ?v1 ))(member$c ?v2 ?v1 ))(member$b (lCons$a ?v2 ?v0 )(alllsts$a ?v1 )))):named a15 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set$ )(?v2 A$ ))(=> (and (member$c ?v0 (alllsts$b ?v1 ))(member$ ?v2 ?v1 ))(member$c (lCons$ ?v2 ?v0 )(alllsts$b ?v1 )))):named a16 ))
(assert (! (forall ((?v0 A_llist_llist_llist$ )(?v1 A_llist_llist_set$ ))(=> (and (member$a ?v0 (inflsts$ ?v1 ))(forall ((?v2 A_llist_llist$ )(?v3 A_llist_llist_llist$ ))(=> (and (member$a ?v3 (inflsts$ ?v1 ))(and (member$b ?v2 ?v1 )(= ?v0 (lCons$b ?v2 ?v3 ))))false )))false )):named a17 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_set$ ))(=> (and (member$b ?v0 (inflsts$a ?v1 ))(forall ((?v2 A_llist$ )(?v3 A_llist_llist$ ))(=> (and (member$b ?v3 (inflsts$a ?v1 ))(and (member$c ?v2 ?v1 )(= ?v0 (lCons$a ?v2 ?v3 ))))false )))false )):named a18 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set$ ))(=> (and (member$c ?v0 (inflsts$b ?v1 ))(forall ((?v2 A$ )(?v3 A_llist$ ))(=> (and (member$c ?v3 (inflsts$b ?v1 ))(and (member$ ?v2 ?v1 )(= ?v0 (lCons$ ?v2 ?v3 ))))false )))false )):named a19 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_llist_set$ )(?v2 A_llist_llist_llist$ ))(=> (and (member$b ?v0 ?v1 )(member$a ?v2 (inflsts$ ?v1 )))(member$a (lCons$b ?v0 ?v2 )(inflsts$ ?v1 )))):named a20 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist_set$ )(?v2 A_llist_llist$ ))(=> (and (member$c ?v0 ?v1 )(member$b ?v2 (inflsts$a ?v1 )))(member$b (lCons$a ?v0 ?v2 )(inflsts$a ?v1 )))):named a21 ))
(assert (! (forall ((?v0 A$ )(?v1 A_set$ )(?v2 A_llist$ ))(=> (and (member$ ?v0 ?v1 )(member$c ?v2 (inflsts$b ?v1 )))(member$c (lCons$ ?v0 ?v2 )(inflsts$b ?v1 )))):named a22 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist_llist$ ))(! (= (lmember$ ?v0 (lCons$a ?v1 ?v2 ))(or (= ?v0 ?v1 )(lmember$ ?v0 ?v2 ))):pattern ((lmember$ ?v0 (lCons$a ?v1 ?v2 ))))):named a23 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A_llist$ ))(! (= (fun_app$ (lmember$a ?v0 )(lCons$ ?v1 ?v2 ))(or (= ?v0 ?v1 )(fun_app$ (lmember$a ?v0 )?v2 ))):pattern ((fun_app$ (lmember$a ?v0 )(lCons$ ?v1 ?v2 ))))):named a24 ))
(assert (! (forall ((?v0 A_llist_bool_fun$ )(?v1 A_llist$ )(?v2 A_llist_llist$ ))(! (= (pred_llist$ ?v0 (lCons$a ?v1 ?v2 ))(and (fun_app$ ?v0 ?v1 )(pred_llist$ ?v0 ?v2 ))):pattern ((pred_llist$ ?v0 (lCons$a ?v1 ?v2 ))))):named a25 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A$ )(?v2 A_llist$ ))(! (= (fun_app$ (pred_llist$a ?v0 )(lCons$ ?v1 ?v2 ))(and (fun_app$a ?v0 ?v1 )(fun_app$ (pred_llist$a ?v0 )?v2 ))):pattern ((fun_app$ (pred_llist$a ?v0 )(lCons$ ?v1 ?v2 ))))):named a26 ))
(assert (! (forall ((?v0 A_llist_llist$ ))(=> (and (=> (= ?v0 lNil$a )false )(forall ((?v1 A_llist$ )(?v2 A_llist_llist$ ))(=> (= ?v0 (lCons$a ?v1 ?v2 ))false )))false )):named a27 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (and (=> (= ?v0 lNil$ )false )(forall ((?v1 A$ )(?v2 A_llist$ ))(=> (= ?v0 (lCons$ ?v1 ?v2 ))false )))false )):named a28 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist_llist$ )(?v2 A_llist$ )(?v3 A_llist_llist$ ))(! (= (lstrict_prefix$ (lCons$a ?v0 ?v1 )(lCons$a ?v2 ?v3 ))(and (= ?v0 ?v2 )(lstrict_prefix$ ?v1 ?v3 ))):pattern ((lstrict_prefix$ (lCons$a ?v0 ?v1 )(lCons$a ?v2 ?v3 ))))):named a29 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(! (= (fun_app$ (lstrict_prefix$a (lCons$ ?v0 ?v1 ))(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(fun_app$ (lstrict_prefix$a ?v1 )?v3 ))):pattern ((fun_app$ (lstrict_prefix$a (lCons$ ?v0 ?v1 ))(lCons$ ?v2 ?v3 ))))):named a30 ))
(assert (! (= (fun_app$ (lstrict_prefix$a lNil$ )lNil$ )false ):named a31 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist_llist$ ))(! (= (lstrict_prefix$ (lCons$a ?v0 ?v1 )lNil$a )false ):pattern ((lCons$a ?v0 ?v1 )))):named a32 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (fun_app$ (lstrict_prefix$a (lCons$ ?v0 ?v1 ))lNil$ )false ):pattern ((lCons$ ?v0 ?v1 )))):named a33 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist_llist$ ))(! (= (lstrict_prefix$ lNil$a (lCons$a ?v0 ?v1 ))true ):pattern ((lCons$a ?v0 ?v1 )))):named a34 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (fun_app$ (lstrict_prefix$a lNil$ )(lCons$ ?v0 ?v1 ))true ):pattern ((lCons$ ?v0 ?v1 )))):named a35 ))
(check-sat )
;(get-unsat-core )
