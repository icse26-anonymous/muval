;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_tree$ 0)
(declare-sort B_tree$ 0)
(declare-fun select$ (A_tree$)Nat$)
(declare-fun selecta$ (A_tree$)A$)
(declare-fun leaf$ (Nat$ A$ )A_tree$)
(declare-fun selectb$ (A_tree$)Nat$)
(declare-fun selectc$ (A_tree$)A_tree$)
(declare-fun selectd$ (A_tree$)A_tree$)
(declare-fun innerNode$ (Nat$ A_tree$ A_tree$ )A_tree$)
(declare-fun selecte$ (B_tree$)Nat$)
(declare-fun selectf$ (B_tree$)B$)
(declare-fun leaf$a (Nat$ B$ )B_tree$)
(declare-fun selectg$ (B_tree$)Nat$)
(declare-fun selecth$ (B_tree$)B_tree$)
(declare-fun selecti$ (B_tree$)B_tree$)
(declare-fun innerNode$a (Nat$ B_tree$ B_tree$ )B_tree$)
(declare-fun a$ ()A$ )
(declare-fun p$ ()Bool )
(declare-fun max$ (Nat$ Nat$ )Nat$ )
(declare-fun t_1$ ()A_tree$ )
(declare-fun t_2$ ()B_tree$ )
(declare-fun depth$ (A_tree$ A$ )Nat$ )
(declare-fun depth$a (B_tree$ B$ )Nat$ )
(declare-fun height$ (A_tree$ )Nat$ )
(declare-fun height$a (B_tree$ )Nat$ )
(declare-fun less_eq$ (Nat$ Nat$ )Bool )
(assert (! (not p$ ):named a0 ))
(assert (! (= (depth$ t_1$ a$ )(max$ (height$ t_1$ )(height$a t_2$ ))):named a1 ))
(assert (! (=> (and (= (depth$ t_1$ a$ )(height$ t_1$ ))(less_eq$ (height$a t_2$ )(height$ t_1$ )))p$ ):named a2 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A$ ))(less_eq$ (depth$ ?v0 ?v1 )(height$ ?v0 ))):named a3 ))
(assert (! (forall ((?v0 B_tree$ )(?v1 B$ ))(less_eq$ (depth$a ?v0 ?v1 )(height$a ?v0 ))):named a4 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (less_eq$ (max$ ?v0 ?v1 )?v2 )(and (less_eq$ ?v0 ?v2 )(less_eq$ ?v1 ?v2 )))):named a5 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(=> (less_eq$ ?v0 ?v1 )(= (max$ ?v0 ?v1 )?v1 ))):named a6 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(=> (less_eq$ ?v0 ?v1 )(= (max$ ?v1 ?v0 )?v1 ))):named a7 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (max$ (max$ ?v0 ?v1 )?v1 )(max$ ?v0 ?v1 ))):named a8 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (max$ ?v0 (max$ ?v0 ?v1 ))(max$ ?v0 ?v1 ))):named a9 ))
(assert (! (forall ((?v0 Nat$ ))(= (max$ ?v0 ?v0 )?v0 )):named a10 ))
(assert (! (forall ((?v0 Nat$ ))(less_eq$ ?v0 ?v0 )):named a11 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (max$ ?v0 ?v1 )(ite (less_eq$ ?v0 ?v1 )?v1 ?v0 ))):named a12 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (less_eq$ ?v0 (max$ ?v1 ?v2 ))(or (less_eq$ ?v0 ?v1 )(less_eq$ ?v0 ?v2 )))):named a13 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(! (= (less_eq$ ?v0 ?v1 )(= (max$ ?v0 ?v1 )?v1 )):pattern ((less_eq$ ?v0 ?v1 )))):named a14 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(! (= (less_eq$ ?v0 ?v1 )(= (max$ ?v1 ?v0 )?v1 )):pattern ((less_eq$ ?v0 ?v1 )))):named a15 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(! (= (less_eq$ ?v0 ?v1 )(= ?v1 (max$ ?v1 ?v0 ))):pattern ((less_eq$ ?v0 ?v1 )))):named a16 ))
(assert (! (forall ((?v0 Nat$ ))(less_eq$ ?v0 ?v0 )):named a17 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(or (less_eq$ ?v0 ?v1 )(less_eq$ ?v1 ?v0 ))):named a18 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(! (=> (less_eq$ ?v0 ?v1 )(= (less_eq$ ?v1 ?v0 )(= ?v1 ?v0 ))):pattern ((less_eq$ ?v1 ?v0 )))):named a19 ))
(check-sat )
;(get-unsat-core )
