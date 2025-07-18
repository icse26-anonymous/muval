;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_nat_fun$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_a_nat_fun_fun$ 0 )
(declare-sort Nat_a_nat_fun_fun$ 0 )
(declare-sort A_set_a_nat_fun_fun$ 0 )
(declare-sort A_nat_fun_a_nat_fun_fun$ 0 )
(declare-sort A_nat_fun_a_a_nat_fun_fun_fun$ 0 )
(declare-sort A_nat_fun_a_set_a_nat_fun_fun_fun$ 0 )
(declare-sort A_tree$ 0)
(declare-fun select$ (A_tree$)Nat$)
(declare-fun selecta$ (A_tree$)A$)
(declare-fun leaf$ (Nat$ A$ )A_tree$)
(declare-fun selectb$ (A_tree$)Nat$)
(declare-fun selectc$ (A_tree$)A_tree$)
(declare-fun selectd$ (A_tree$)A_tree$)
(declare-fun innerNode$ (Nat$ A_tree$ A_tree$ )A_tree$)
(declare-fun uu$ ()A_nat_fun$ )
(declare-fun x1$ ()Nat$ )
(declare-fun x2$ ()A$ )
(declare-fun uua$ (Nat$ )A_nat_fun_a_nat_fun_fun$ )
(declare-fun uub$ (A_nat_fun$ )A_nat_fun_a_a_nat_fun_fun_fun$ )
(declare-fun uuc$ (A_nat_fun$ )A_nat_fun_a_set_a_nat_fun_fun_fun$ )
(declare-fun uud$ (A_nat_fun$ )Nat_a_nat_fun_fun$ )
(declare-fun uue$ (A_a_nat_fun_fun$ )A_set_a_nat_fun_fun$ )
(declare-fun uuf$ (A_a_nat_fun_fun$ )A_a_nat_fun_fun$ )
(declare-fun uug$ (A_a_nat_fun_fun$ )A_set_a_nat_fun_fun$ )
(declare-fun uuh$ ()A_nat_fun$ )
(declare-fun cost$ (A_tree$ )Nat$ )
(declare-fun freq$ (A_tree$ )A_nat_fun$ )
(declare-fun zero$ ()Nat$ )
(declare-fun depth$ (A_tree$ )A_nat_fun$ )
(declare-fun times$ (Nat$ Nat$ )Nat$ )
(declare-fun height$ (A_tree$ )Nat$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun setsum$ (A_nat_fun$ A_set$ )Nat$ )
(declare-fun weight$ (A_tree$ )Nat$ )
(declare-fun fun_app$ (A_nat_fun$ A$ )Nat$ )
(declare-fun alphabet$ (A_tree$ )A_set$ )
(declare-fun fun_app$a (A_a_nat_fun_fun$ A$ )A_nat_fun$ )
(declare-fun fun_app$b (A_set_a_nat_fun_fun$ A_set$ )A_nat_fun$ )
(declare-fun fun_app$c (Nat_a_nat_fun_fun$ Nat$ )A_nat_fun$ )
(declare-fun fun_app$d (A_nat_fun_a_nat_fun_fun$ A_nat_fun$ )A_nat_fun$ )
(declare-fun fun_app$e (A_nat_fun_a_set_a_nat_fun_fun_fun$ A_nat_fun$ )A_set_a_nat_fun_fun$ )
(declare-fun fun_app$f (A_nat_fun_a_a_nat_fun_fun_fun$ A_nat_fun$ )A_a_nat_fun_fun$ )
(declare-fun fun_app$g (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$h (A_a_fun$ A$ )A$ )
(declare-fun pred_tree$ (A_bool_fun$ A_tree$ )Bool )
(declare-fun consistent$ (A_tree$ )Bool )
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$ uu$ ?v0 )(times$ (fun_app$ (freq$ (leaf$ x1$ x2$ ))?v0 )(fun_app$ (depth$ (leaf$ x1$ x2$ ))?v0 ))):pattern ((fun_app$ uu$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 A_a_nat_fun_fun$ )(?v1 A$ )(?v2 A$ ))(! (= (fun_app$ (fun_app$a (uuf$ ?v0 )?v1 )?v2 )(fun_app$ (fun_app$a ?v0 ?v2 )?v1 )):pattern ((fun_app$ (fun_app$a (uuf$ ?v0 )?v1 )?v2 )))):named a1 ))
(assert (! (forall ((?v0 A_a_nat_fun_fun$ )(?v1 A_set$ )(?v2 A$ ))(! (= (fun_app$ (fun_app$b (uug$ ?v0 )?v1 )?v2 )(setsum$ (fun_app$a (uuf$ ?v0 )?v2 )?v1 )):pattern ((fun_app$ (fun_app$b (uug$ ?v0 )?v1 )?v2 )))):named a2 ))
(assert (! (forall ((?v0 A_a_nat_fun_fun$ )(?v1 A_set$ )(?v2 A$ ))(! (= (fun_app$ (fun_app$b (uue$ ?v0 )?v1 )?v2 )(setsum$ (fun_app$a ?v0 ?v2 )?v1 )):pattern ((fun_app$ (fun_app$b (uue$ ?v0 )?v1 )?v2 )))):named a3 ))
(assert (! (forall ((?v0 A_nat_fun$ )(?v1 Nat$ )(?v2 A$ ))(! (= (fun_app$ (fun_app$c (uud$ ?v0 )?v1 )?v2 )(times$ (fun_app$ ?v0 ?v2 )?v1 )):pattern ((fun_app$ (fun_app$c (uud$ ?v0 )?v1 )?v2 )))):named a4 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_nat_fun$ )(?v2 A$ ))(! (= (fun_app$ (fun_app$d (uua$ ?v0 )?v1 )?v2 )(times$ ?v0 (fun_app$ ?v1 ?v2 ))):pattern ((fun_app$ (fun_app$d (uua$ ?v0 )?v1 )?v2 )))):named a5 ))
(assert (! (forall ((?v0 A_nat_fun$ )(?v1 A_nat_fun$ )(?v2 A_set$ )(?v3 A$ ))(! (= (fun_app$ (fun_app$b (fun_app$e (uuc$ ?v0 )?v1 )?v2 )?v3 )(setsum$ (fun_app$a (fun_app$f (uub$ ?v0 )?v1 )?v3 )?v2 )):pattern ((fun_app$ (fun_app$b (fun_app$e (uuc$ ?v0 )?v1 )?v2 )?v3 )))):named a6 ))
(assert (! (forall ((?v0 A_nat_fun$ )(?v1 A_nat_fun$ )(?v2 A$ )(?v3 A$ ))(! (= (fun_app$ (fun_app$a (fun_app$f (uub$ ?v0 )?v1 )?v2 )?v3 )(times$ (fun_app$ ?v0 ?v2 )(fun_app$ ?v1 ?v3 ))):pattern ((fun_app$ (fun_app$a (fun_app$f (uub$ ?v0 )?v1 )?v2 )?v3 )))):named a7 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$ uuh$ ?v0 )zero$ ):pattern ((fun_app$ uuh$ ?v0 )))):named a8 ))
(assert (! (not (= (cost$ (leaf$ x1$ x2$ ))(setsum$ uu$ (alphabet$ (leaf$ x1$ x2$ ))))):named a9 ))
(assert (! (consistent$ (leaf$ x1$ x2$ )):named a10 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A$ )(?v2 Nat$ )(?v3 A$ ))(= (= (leaf$ ?v0 ?v1 )(leaf$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a11 ))
(assert (! (forall ((?v0 A_tree$ ))(exists ((?v1 A$ ))(member$ ?v1 (alphabet$ ?v0 )))):named a12 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A$ ))(! (= (consistent$ (leaf$ ?v0 ?v1 ))true ):pattern ((leaf$ ?v0 ?v1 )))):named a13 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_nat_fun$ )(?v2 A_set$ ))(= (times$ ?v0 (setsum$ ?v1 ?v2 ))(setsum$ (fun_app$d (uua$ ?v0 )?v1 )?v2 ))):named a14 ))
(assert (! (forall ((?v0 A_nat_fun$ )(?v1 A_set$ )(?v2 A_nat_fun$ )(?v3 A_set$ ))(= (times$ (setsum$ ?v0 ?v1 )(setsum$ ?v2 ?v3 ))(setsum$ (fun_app$b (fun_app$e (uuc$ ?v0 )?v2 )?v3 )?v1 ))):named a15 ))
(assert (! (forall ((?v0 A_nat_fun$ )(?v1 A_set$ )(?v2 Nat$ ))(= (times$ (setsum$ ?v0 ?v1 )?v2 )(setsum$ (fun_app$c (uud$ ?v0 )?v2 )?v1 ))):named a16 ))
(assert (! (forall ((?v0 A_tree$ ))(! (=> (consistent$ ?v0 )(= (weight$ ?v0 )(setsum$ (freq$ ?v0 )(alphabet$ ?v0 )))):pattern ((weight$ ?v0 )))):named a17 ))
(assert (! (forall ((?v0 A_a_nat_fun_fun$ )(?v1 A_set$ )(?v2 A_set$ ))(= (setsum$ (fun_app$b (uue$ ?v0 )?v1 )?v2 )(setsum$ (fun_app$b (uug$ ?v0 )?v2 )?v1 ))):named a18 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 Nat$ )(?v2 A$ ))(! (= (pred_tree$ ?v0 (leaf$ ?v1 ?v2 ))(fun_app$g ?v0 ?v2 )):pattern ((pred_tree$ ?v0 (leaf$ ?v1 ?v2 ))))):named a19 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ ))(! (=> (not (member$ ?v0 (alphabet$ ?v1 )))(= (fun_app$ (freq$ ?v1 )?v0 )zero$ )):pattern ((fun_app$ (freq$ ?v1 )?v0 )))):named a20 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_a_fun$ )(?v2 A_a_fun$ )(?v3 A_set$ )(?v4 A_nat_fun$ )(?v5 A_nat_fun$ ))(=> (and (forall ((?v6 A$ ))(=> (member$ ?v6 ?v0 )(= (fun_app$h ?v1 (fun_app$h ?v2 ?v6 ))?v6 )))(and (forall ((?v6 A$ ))(=> (member$ ?v6 ?v0 )(member$ (fun_app$h ?v2 ?v6 )?v3 )))(and (forall ((?v6 A$ ))(=> (member$ ?v6 ?v3 )(= (fun_app$h ?v2 (fun_app$h ?v1 ?v6 ))?v6 )))(and (forall ((?v6 A$ ))(=> (member$ ?v6 ?v3 )(member$ (fun_app$h ?v1 ?v6 )?v0 )))(forall ((?v6 A$ ))(=> (member$ ?v6 ?v0 )(= (fun_app$ ?v4 (fun_app$h ?v2 ?v6 ))(fun_app$ ?v5 ?v6 ))))))))(= (setsum$ ?v5 ?v0 )(setsum$ ?v4 ?v3 )))):named a21 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ )(?v2 A_nat_fun$ )(?v3 A_nat_fun$ ))(=> (and (= ?v0 ?v1 )(forall ((?v4 A$ ))(=> (member$ ?v4 ?v1 )(= (fun_app$ ?v2 ?v4 )(fun_app$ ?v3 ?v4 )))))(= (setsum$ ?v2 ?v0 )(setsum$ ?v3 ?v1 )))):named a22 ))
(assert (! (forall ((?v0 A_tree$ ))(=> (consistent$ ?v0 )(exists ((?v1 A$ ))(and (member$ ?v1 (alphabet$ ?v0 ))(= (fun_app$ (depth$ ?v0 )?v1 )(height$ ?v0 )))))):named a23 ))
(assert (! (forall ((?v0 A_set$ ))(= (setsum$ uuh$ ?v0 )zero$ )):named a24 ))
(assert (! (forall ((?v0 A_nat_fun$ )(?v1 A_set$ ))(=> (and (not (= (setsum$ ?v0 ?v1 )zero$ ))(forall ((?v2 A$ ))(=> (and (member$ ?v2 ?v1 )(not (= (fun_app$ ?v0 ?v2 )zero$ )))false )))false )):named a25 ))
(check-sat )
;(get-unsat-core )
