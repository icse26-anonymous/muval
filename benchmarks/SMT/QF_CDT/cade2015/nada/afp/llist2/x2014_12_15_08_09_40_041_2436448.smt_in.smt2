;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_llist_set$ 0 )
(declare-sort Nat_a_option_fun$ 0 )
(declare-sort A_option_bool_fun$ 0 )
(declare-sort A_option$ 0)
(declare-fun none$ ()A_option$)
(declare-fun the$ (A_option$)A$)
(declare-fun some$ (A$ )A_option$)
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-fun i$ ()Nat$ )
(declare-fun j$ ()Nat$ )
(declare-fun q$ ()Bool )
(declare-fun t$ ()A_llist$ )
(declare-fun x$ ()A$ )
(declare-fun ran$ (Nat_a_option_fun$ )A_set$ )
(declare-fun suc$ (Nat$ )Nat$ )
(declare-fun ll2f$ (A_llist$ )Nat_a_option_fun$ )
(declare-fun lset$ (A_llist$ )A_set$ )
(declare-fun member$ (A_llist$ A_llist_set$ )Bool )
(declare-fun finlsts$ (A_set$ )A_llist_set$ )
(declare-fun fun_app$ (Nat_a_option_fun$ Nat$ )A_option$ )
(declare-fun less_eq$ (Nat$ Nat$ )Bool )
(declare-fun llength$ (A_llist$ )Nat$ )
(declare-fun fun_app$a (A_option_bool_fun$ A_option$ )Bool )
(assert (! (not (= (fun_app$ (ll2f$ t$ )j$ )none$ )):named a0 ))
(assert (! (not (exists ((?v0 A$ ))(= (fun_app$ (ll2f$ t$ )j$ )(some$ ?v0 )))):named a1 ))
(assert (! (= (fun_app$ (ll2f$ t$ )i$ )(some$ x$ )):named a2 ))
(assert (! (forall ((?v0 A$ ))(=> (= (fun_app$ (ll2f$ t$ )j$ )(some$ ?v0 ))q$ )):named a3 ))
(assert (! (less_eq$ j$ i$ ):named a4 ))
(assert (! (forall ((?v0 A_option$ ))(=> (and (=> (= ?v0 none$ )false )(=> (not (= ?v0 none$ ))false ))false )):named a5 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$ (ll2f$ lNil$ )?v0 )none$ ):pattern ((fun_app$ (ll2f$ lNil$ )?v0 )))):named a6 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 Nat$ )(?v2 Nat$ ))(=> (and (= (fun_app$ (ll2f$ ?v0 )?v1 )none$ )(less_eq$ ?v1 ?v2 ))(= (fun_app$ (ll2f$ ?v0 )?v2 )none$ ))):named a7 ))
(assert (! (forall ((?v0 A_option$ ))(= (not (= ?v0 none$ ))(exists ((?v1 A$ ))(= ?v0 (some$ ?v1 ))))):named a8 ))
(assert (! (forall ((?v0 A_option$ ))(= (forall ((?v1 A$ ))(not (= ?v0 (some$ ?v1 ))))(= ?v0 none$ ))):named a9 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 Nat$ ))(! (=> (= (fun_app$ (ll2f$ ?v0 )?v1 )none$ )(= (fun_app$ (ll2f$ ?v0 )(suc$ ?v1 ))none$ )):pattern ((fun_app$ (ll2f$ ?v0 )(suc$ ?v1 ))))):named a10 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (lset$ ?v0 )(ran$ (ll2f$ ?v0 ))):pattern ((lset$ ?v0 )))):named a11 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set$ ))(=> (member$ ?v0 (finlsts$ ?v1 ))(= (fun_app$ (ll2f$ ?v0 )(llength$ ?v0 ))none$ ))):named a12 ))
(assert (! (forall ((?v0 A_option_bool_fun$ ))(= (exists ((?v1 A_option$ ))(fun_app$a ?v0 ?v1 ))(or (fun_app$a ?v0 none$ )(exists ((?v1 A$ ))(fun_app$a ?v0 (some$ ?v1 )))))):named a13 ))
(assert (! (forall ((?v0 A_option_bool_fun$ ))(= (forall ((?v1 A_option$ ))(fun_app$a ?v0 ?v1 ))(and (fun_app$a ?v0 none$ )(forall ((?v1 A$ ))(fun_app$a ?v0 (some$ ?v1 )))))):named a14 ))
(assert (! (forall ((?v0 A_option$ ))(=> (and (=> (= ?v0 none$ )false )(forall ((?v1 A$ ))(=> (= ?v0 (some$ ?v1 ))false )))false )):named a15 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(= (= (some$ ?v0 )(some$ ?v1 ))(= ?v0 ?v1 ))):named a16 ))
(assert (! (forall ((?v0 A_set$ ))(member$ lNil$ (finlsts$ ?v0 ))):named a17 ))
(check-sat )
;(get-unsat-core )
