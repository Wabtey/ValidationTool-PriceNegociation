theory pc
imports Main
begin

(* ATTENTION les fonctions et lemmes introduits dans ce fichier ne sont pas 
   forcément utiles pour prouver le tp89. L'objectif, ici, est d'illustrer l'utilisation de 
   certaines commandes de preuve Isabelle et de voir leur effet *)

(* PREMIERE partie *)
(* <<prefer i>>, pour choisir de traiter le sous-but i en premier *)

(* <<case_tac>>, pour:
  - faire une preuve par cas sur une variable de type inductif définie par "datatype"
  - déplier la définition d'une variable définie par "type_synonym"
  - faire une preuve par cas sur une propriété
  - ajouter une hypothèse (démontrable) supplémentaire pendant une preuve
*)

(* <<rename_tac>>, pour renommer une variable dont le nom a été généré par isabelle/hol, pour:
  - avoir des identifiants plus lisibles
  - avoir des preuves plus robustes (d'une version à l'autre le nommage de ces variables peut changer)
*)

(* <<metis>>, pour: 
  - résoudre une propriété que simp ne sait pas faire seul (si elle nécessite d'instancier
    des quantificateurs par exemple)
  - appliquer des lemmes résolvant explicitement le but courant
*)

type_synonym transid= "nat*nat*nat"

datatype message= 
  Pay transid nat  
| Ack transid nat
| Cancel transid

fun f::"message \<Rightarrow> nat"
where
"f (Pay _ 0) = 10" |
"f (Pay _ m) = m" |
"f (Ack _ _) = 1" |
"f (Cancel _) = 2" 

(* case_tac sur data_types + prefer i + rename_tac *)
lemma "((f mess)>0)"
apply simp
apply auto           (* N'ont pas d'effet, car (f mess) ne peut être réécrit. Pour pouvoir appliquer la définition
                        de f, on doit connaitre la forme de mess *)
apply (case_tac mess)(* on fait une preuve par cas sur la forme de mess: soit Pay, soit Ack, soit Cancel *)
prefer 2             (* on peut traiter en premier le cas Ack ...*)
apply simp           (* simplement en appliquant la définition de f *)
prefer 2             (* on peut traiter le cas Cancel ...*)
apply simp           (* simplement en appliquant la définition de f *)
apply simp           (* Le cas Pay ne peut être réécrit par la définition de f, car il y a deux cas possibles:
                        le cas (Pay _ 0) et le cas (Pay _ m) *)
apply (rename_tac tid montant) (* On renomme les identifiants générés par la preuve par cas, pour en choisir des plus 
                                    lisibles *)
apply (case_tac montant) (* on fait une preuve par cas sur la variable nommée montant: soit nat=0 soit nat=Suc y *)
apply auto               (* les deux cas se démontrent facilement *)
done

(* case_tac sur type_synonym/tuples etc. + application à plusieurs sous-buts *)
lemma "((f mess)>0)"
apply (case_tac mess)
apply (case_tac x11) (* Dans une preuve si on a une variable qui est définie comme un doublet, triplet etc, 
                         on peut aussi déplier sa définition par case_tac *)
apply (case_tac [2] x21)  (* On peut appliquer un case_tac un sous-but particulier *)
apply (rename_tac [3] tid)
apply (case_tac [3] tid) 
                          (* On peut appliquer un case_tac à un ensemble de sous buts (si cette variable apparaît)
                                avec le même nom dans tous les sous-buts *)
apply (case_tac [1-] a)
sorry


fun member:: "'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
"member _ [] = False" |
"member x (y#r) = (if x=y then True else (member x r))"

fun nth:: "nat \<Rightarrow> 'a list \<Rightarrow> 'a"
where
"nth 0 (y#_) = y" |
"nth i (y#r) = (nth (i - 1) r)"

(* Un lemme intermédiaire pour la preuve du dessous, sa preuve n'est pas intéressante, 
    on peut la sauter *)
lemma temp: "((member e l) \<and> (nth i l = e)) \<longrightarrow> (\<exists>i. nth i (a#l) = e)"
apply (induct l arbitrary: i e)
apply auto
apply (metis One_nat_def diff_Suc_Suc diff_zero pc.nth.simps(2))
apply (metis One_nat_def diff_Suc_Suc diff_zero pc.nth.simps(2))
done


(* case_tac pour: faire une preuve par cas sur une propriété et 
                  ajouter (en la démontrant) une hypothèse supplémentaire pendant une preuve *)

(* Si un élément e est dans une liste, il existe un index i pour e dans la liste *)
lemma "(member e l) \<longrightarrow> (\<exists> i. (nth i l) = e)" 
apply (induct l)
apply simp           (* par induction, soit la liste est [] soit elle est (a#l) *)
                            (* Sledgehammer démontre aussi les autres sous-buts 
                               mais détaillons un peu une autre façon de faire la preuve *)
apply (case_tac "a=e")      (* On fait une preuve par cas. Soit l'élément que l'on cherche: "e" 
                                est égal à "a" soit il est différent *)
apply simp                  (* pour le cas a=e, avec simp on applique le remplacement de a par e *)
                            (* dans ce cas la preuve est simple: (\<exists>i. pc.nth i (e # l) = e) est 
                               vrai si on choisit i=0, car (nth 0 (e#l)) = e *)
(* point (a) *)
                            (* Démontrons d'abord la propriété (hypothèse supplémentaire) que 
                               (nth 0 (e#l)) = e. Pour ce faire on fait un case_tac sur sa 
                               négation. *)
apply (case_tac "\<not>((nth 0 (e#l)) = e)") (* Comme la propriété est vraie, sa négation (pc.nth 0 (e # l) \<noteq> e)
                                           apparaît comme hypothèse du premier sous but.
                                           Cette hypothèse est trivialement fausse et simp permet 
                                           de le montrer *)
apply simp                              

(* Notre premier sous-but revient à celui que l'on avait au point (a) mais mais avec notre 
   hypothèse supplémentaire: (\<not> pc.nth 0 (e # l) \<noteq> e) *)
apply metis                             (* Cette hypothèse permet de montrer (\<exists>i. pc.nth i (e # l) = e)
                                           on utilise metis qui s'occupe d'instancier le "i" avec la valeur 0 *)

(* Il ne reste plus qu'un sous-but pour le cas a\<noteq>e.*)
                              (* Dans ce cas, les hypothèses (member e (a#l)) et (e\<noteq>a) font
                                 que l'on obtient l'hypothèse (member e l) en appliquant 
                                 la définition de member avec simp. *)
apply simp                   
                              (* Avec (member e l), on doit pouvoir utiliser l'hypothèse d'induction
                                 (member e l \<longrightarrow> (\<exists>i. pc.nth i l = e)) et obtenir (\<exists>i. pc.nth i l = e)
                              *)
apply (case_tac "\<not>(\<exists>i. pc.nth i l = e)")
apply simp
  by (meson temp)
                              (* Comme tout à l'heure on a le même but avec une hypothèse supplémentaire
                                 Or celle-ci n'est pas équivalente au but:  (\<exists>i. pc.nth i (a # l) = e)
                                 Cependant, en se servant du lemme "temp", on peut conclure. *)

  


(* SECONDE partie *)

(* <<unfolding>>: pour appliquer la réécriture sur UNE fonction choisie *)

(* <<induct rule: f.inducts>>, pour choisir un principe d'induction respectant la définition de f*)

(* <<induct arbitrary: x y>>, pour appliquer le principe d'induction en généralisant les variables x et y*)

(* <<sledgehammer [options] (del: th1 th2 add: th3 th4)>>, pour guider sledgehammer dans sa recherche de preuve *)

fun h::"nat \<Rightarrow> nat"
where
"h x= x+1"

fun k::"nat \<Rightarrow> nat"
where
"k 0 = 0" |
"k x = x - 1"

fun head::"'a list \<Rightarrow> 'a"
where
"head (x#_) = x"

(* On utilise ce lemme intermédiaire en dessous *)
lemma temp2: "h(k(x))\<ge> x"
apply (induct x)
apply auto
done

(* On tente de prouver ce lemme *)
lemma "(head [h(k(x))]) \<ge> x"
apply simp     (* en appliquant la simplification on réécrit head (voulu) mais aussi (h) pas voulu *)
apply (metis temp2)  (* du coup le lemme temp2 ne peut plus être appliqué -syntaxiquement- *)
sorry

(* Recommençons *)
(* unfolding: pour appliquer la réécriture sur UNE fonction choisie *)
lemma "(head [h(k(x))]) \<ge> x"
unfolding head.simps  (* On ne réécrit que la fonction head à l'aide de sa définition *)
apply (metis temp2)  (* le lemme temp2 peut être appliqué -syntaxiquement- *)
done


fun g::"message list \<Rightarrow> bool"
where 
"g [] = True"|
"g ((Pay _ 0)#_) = False"|
"g ((Pay _ _)#r) = g r"|
"g ((Ack _ _)#r) = g r"|
"g ((Cancel _)#r) = g r"

lemma "((member (Pay tid 0) l)) \<longrightarrow> \<not>(g l)"
apply (induct l)  (* Le principe d'induction par défaut utilise la structure du type de la variable *)
                  (* Ici, on se retrouve avec 2 sous-buts un pour le cas où la liste est [] et 
                     un pour le cas où elle est (a#l) *)
apply auto        (* le premier sous-buts (cas []) est démontré automatiquement mais il reste à
                     faire la preuve pour le cas (a#l) *)

                  (* C'est faisable mais il faut détailler par des case_tac toutes les formes 
                     que peut prendre le message a *)
apply (case_tac a)
                  (* Dans le cas du Pay il faut aussi voir si le montant est 0 ou pas (car c'est 
                     utilisé dans la définition de g *)
apply (case_tac x12)
apply auto
done

(* Recommençons *)
(* On peut faire plus simple (et plus rapide) en appliquant un principe d'induction qui
   respecte la définition de g. Il utilise la définition de la fonction (qui termine) plutôt
   que la structure du type *)

(* induct rule: g.induct: pour appliquer l'induction selon la définition de g.
   Si la définition de g est inductive sur plusieurs paramètre x, y, z on peut aussi faire
   (induct x y z rule: g.induct *)

lemma "((member (Pay tid 0) l)) \<longrightarrow> \<not>(g l)"
apply (induct l rule: g.induct)
apply auto
done


(* On redéfinit \<le> pour les naturels: leq (lesser or equal) et =< le nouveau symbole *)
fun leq::"nat \<Rightarrow> nat \<Rightarrow> bool"   (infix "=<" 65)
where 
"leq 0 _ = True" |
"leq (Suc _) 0 = False" |
"leq (Suc x) (Suc y) = leq x y"

(* On veut prouver le lemme suivant *)
lemma sym: "((x=<y) \<and> (y=<x)) \<longrightarrow> (x=y)"
apply (induct x)  
prefer 2  (* on tente de prouver le second cas (le cas inductif) *)

(* Dans ce but:

    \<And>x. x =< y \<and> y =< x \<longrightarrow> x = y \<Longrightarrow> Suc x =< y \<and> y =< Suc x \<longrightarrow> Suc x = y

 le **même** y apparaît dans 
  
 l'hypothèse d'induction 
    (a) \<And>x. x =< y \<and> y =< x \<longrightarrow> x = y

 et dans la conclusion:

    (b) Suc x =< y \<and> y =< Suc x \<longrightarrow> Suc x = y

 Or, prouver (b) à l'aide de (a) est difficile! Voyons celà. *)

(* pour se servir de l'hypothèse d'induction on doit se ramener à 
   des inégalités entre x et y. Or pour l'instant, on a des (Suc x). Pour les 
   faire disparaître on peut utiliser la définition de leq, or pour l'appliquer 
   on doit avoir, à la place de y, soit 0 soit (Suc ...). On fait une preuve par
   cas sur y *)

apply (case_tac y) 
apply simp          (* le premier cas se simplifie *)
apply simp          (* le deuxième aussi mais on voit bien que l'on n'est pas beaucoup plus
                       avancés, car même si notre conclusion est maintenant de la bonne forme:
                       x =< nat \<and> nat =< x \<longrightarrow> x = nat
    
                       C'est l'hypothèse qui a souffert de la preuve par cas, elle est devenue:
                       x =< Suc nat \<and> Suc nat =< x \<longrightarrow> x = Suc nat
                       
                       Le problème ici est que le y de l'hypothèse et de la conclusion n'ont
                       aucune raison d'être reliés (ils l'ont été par le apply (induct x) du début *)
apply simp
oops

(* Recommençons *)

lemma sym: "((x=<y) \<and> (y=< x)) \<longrightarrow> (x=y)"
apply (induct x arbitrary:y) (* On utilise un principe d'induction dans lequel "y" sera arbitraire
                                ... ou quantifié universellement. *)
prefer 2  (* Si l'on compare le cas inductif avec la version précédente:

Avant:      \<And>x. x =< y \<and> y =< x \<longrightarrow> x = y \<Longrightarrow> Suc x =< y \<and> y =< Suc x \<longrightarrow> Suc x = y

Maintenant: \<And>x y. (\<And>y. x =< y \<and> y =< x \<longrightarrow> x = y) \<Longrightarrow> Suc x =< y \<and> y =< Suc x \<longrightarrow> Suc x = y

La conclusion est la même mais l'hypothèse est strictement plus forte. 

Avant l'hypothèse était pour un y (le même que dans la conclusion) x =< y \<and> y =< x \<longrightarrow> x = y
Maintenant c'est: pour tout y x =< y \<and> y =< x \<longrightarrow> x = y 
*)

apply (case_tac y)
apply simp
apply simp
apply (case_tac y)
apply simp
apply simp
done

(* <<sledgehammer [options] (del: th1 th2 add: th3 th4)>>: pour guider sledgehammer *)
lemma "(member e l) \<longrightarrow> (\<exists> i. (nth i l) = e)"  
apply (induct l arbitrary: e)
apply (metis pc.member.simps(1))


(* En utilisant slegehammer comme une commande de preuve, si nécessaire on peut:
   - choisir les provers utilisés par sledgehammer (avec provers=...)
   - choisir un timeout plus important (quand il devrait VRAIMENT trouver la preuve mais ne 
     la trouve pas avec le timeout par défaut). A utiliser avec parcimonie, le timeout par défaut
     de 30s est celui qui offre le meilleur compromis temps passé/nb de preuves trouvées
   - ajouter des lemmes à considérer pour sa recherche de preuve (add: ...)
   - supprimer des lemmes à considérer (s'ils peuvent l'emmener dans une mauvaise direction) avec 
     (del: ...)
 *)
sledgehammer [provers=e cvc4 spass z3 remote_vampire,timeout=120] (del: pc.member.simps(2) add:temp)
  by (metis list.sel(3) member.elims(2) pc.nth.simps(1) temp)


end
